#!/usr/bin/env bash
# Run the parallel k-plex enumerator (Main) on every DIMACS graph in datasets/,
# each capped at 2 hours or 1 GB of captured output.
# Results (quasi-cliques / models + stats) are written to outputs/<graphname>.txt
# Progress log is written to outputs/run.log

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BINARY="$SCRIPT_DIR/mdsusat"          # or wherever Main.cc compiles to
DATASETS_DIR="$SCRIPT_DIR/../datasets"
OUTPUT_DIR="$SCRIPT_DIR/../output"
LOG_FILE="$OUTPUT_DIR/run.log"

# ---- Solver parameters (MiniSat-style) ----
K=2                 # k-plex value (k=1 for cliques)  -> passed as --k
MIN_SIZE=2          # minimum k-plex size             -> passed as --min-size
NCORES=1            # number of OpenMP threads        -> passed as --ncores
VERB=3              # verbosity (0..4)                -> passed as --verb
LIMIT_EX=10         # max clause-exchange size        -> passed as --limitEx
CTRL=0              # dynamic control mode (0..2)     -> passed as --ctrl

TIMEOUT_SECS=7200   # 2 hours in seconds
SIZE_LIMIT=$((1 * 1024 * 1024 * 1024))  # 1 GB in bytes (captured stdout+result file)

mkdir -p "$OUTPUT_DIR"

if [[ ! -x "$BINARY" ]]; then
    echo "ERROR: binary not found at $BINARY" >&2
    echo "Build Main.cc first (e.g. 'cmake --build build')." >&2
    exit 1
fi

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*" | tee -a "$LOG_FILE"
}

log "Starting run on all graphs — k=$K, min_size=$MIN_SIZE, ncores=$NCORES, timeout=2h, size_limit=1GB"
log "Results will be saved to $OUTPUT_DIR"

# Main expects DIMACS files. Adjust the glob if your instances are named differently
# (e.g. *.cnf, *.dimacs, *.graph, or gzipped *.cnf.gz).
shopt -s nullglob
GRAPHS=("$DATASETS_DIR"/*.cnf "$DATASETS_DIR"/*.dimacs "$DATASETS_DIR"/*.graph "$DATASETS_DIR"/*.cnf.gz)
shopt -u nullglob

if [[ ${#GRAPHS[@]} -eq 0 ]]; then
    log "No datasets found in $DATASETS_DIR (looked for *.cnf, *.dimacs, *.graph, *.cnf.gz)"
    exit 0
fi

for GRAPH in "${GRAPHS[@]}"; do
    NAME=$(basename "$GRAPH")
    # strip known extensions for a clean output name
    NAME="${NAME%.gz}"
    NAME="${NAME%.cnf}"
    NAME="${NAME%.dimacs}"
    NAME="${NAME%.graph}"

    OUTFILE="$OUTPUT_DIR/${NAME}.txt"
    TMPDIR="$OUTPUT_DIR/.tmp_${NAME}"

    if [[ -f "$OUTFILE" ]]; then
        log "SKIPPING: $NAME  (output already exists: $OUTFILE)"
        continue
    fi

    log "--- Starting: $NAME ---"
    mkdir -p "$TMPDIR"

    # Main writes the "SAT" model to the 2nd positional arg if given, and
    # stats/models to stdout. We capture both separately.
    RESULT_FILE="$TMPDIR/result.out"
    STDOUT_FILE="$TMPDIR/stdout.txt"
    TIME_FILE="$TMPDIR/time.txt"
    START_EPOCH=$(date +%s)

    if [[ -x /usr/bin/time ]]; then
        /usr/bin/time -v -o "$TIME_FILE" \
            "$BINARY" \
            -k="$K" \
            -min-size="$MIN_SIZE" \
            -ncores="$NCORES" \
            -verb="$VERB" \
            -limitEx="$LIMIT_EX" \
            -ctrl="$CTRL" \
            "$GRAPH" "$RESULT_FILE" \
            > "$STDOUT_FILE" 2>>"$LOG_FILE" &
    else
        "$BINARY" \
            -k="$K" \
            -min-size="$MIN_SIZE" \
            -ncores="$NCORES" \
            -verb="$VERB" \
            -limitEx="$LIMIT_EX" \
            -ctrl="$CTRL" \
            "$GRAPH" "$RESULT_FILE" \
            > "$STDOUT_FILE" 2>>"$LOG_FILE" &
    fi
    BIN_PID=$!

    # Monitor: kill on timeout (2h) or combined output exceeding 1 GB
    EXIT_CODE=0
    STOP_REASON=""
    DEADLINE=$(( $(date +%s) + TIMEOUT_SECS ))

    while kill -0 "$BIN_PID" 2>/dev/null; do
        if [[ $(date +%s) -ge $DEADLINE ]]; then
            kill "$BIN_PID" 2>/dev/null || true
            EXIT_CODE=124
            STOP_REASON="TIMED_OUT"
            break
        fi

        SIZE_OUT=$(stat -c%s "$STDOUT_FILE" 2>/dev/null || echo 0)
        SIZE_RES=$(stat -c%s "$RESULT_FILE" 2>/dev/null || echo 0)
        TOTAL_SIZE=$(( SIZE_OUT + SIZE_RES ))
        if [[ $TOTAL_SIZE -ge $SIZE_LIMIT ]]; then
            kill "$BIN_PID" 2>/dev/null || true
            EXIT_CODE=125
            STOP_REASON="SIZE_EXCEEDED"
            break
        fi
        sleep 5
    done

    # Collect exit code when process finishes normally (no kill)
    if [[ -z "$STOP_REASON" ]]; then
        wait "$BIN_PID" || EXIT_CODE=$?
    else
        wait "$BIN_PID" 2>/dev/null || true
    fi

    # Try to count solutions. Main prints "SATISFIABLE"/"UNSATISFIABLE"/"INDETERMINATE"
    # and a per-thread table "thread | detected substructures | conflicts | runtime (s)".
    # We extract the total line if present; otherwise fall back to line count of the
    # result file (which contains a single model for the current implementation).
    NB_MODELS=0
    if [[ -f "$STDOUT_FILE" ]]; then
        TOTAL_LINE=$(grep -E '^\s*total\s*\|' "$STDOUT_FILE" | head -n1 || true)
        if [[ -n "$TOTAL_LINE" ]]; then
            NB_MODELS=$(echo "$TOTAL_LINE" | awk -F'|' '{gsub(/ /,"",$2); print $2}')
        fi
    fi
    if [[ -z "$NB_MODELS" || "$NB_MODELS" == "0" ]]; then
        # fallback: count non-header lines in result file
        if [[ -f "$RESULT_FILE" && -s "$RESULT_FILE" ]]; then
            NB_MODELS=$(wc -l < "$RESULT_FILE" 2>/dev/null || echo 0)
        fi
    fi

    END_EPOCH=$(date +%s)
    RUNTIME_SECS=$((END_EPOCH - START_EPOCH))

    # Read peak RSS if available from /usr/bin/time -v output.
    PEAK_RSS_KB="N/A"
    if [[ -f "$TIME_FILE" ]]; then
        RSS_LINE=$(grep -E '^\s*Maximum resident set size \(kbytes\):' "$TIME_FILE" | tail -n1 || true)
        if [[ -n "$RSS_LINE" ]]; then
            PEAK_RSS_KB=$(echo "$RSS_LINE" | awk -F':' '{gsub(/^[ \t]+/,"",$2); print $2}')
        fi
    fi

    # Determine solver status from stdout
    STATUS_LINE=$(grep -E '^(SATISFIABLE|UNSATISFIABLE|INDETERMINATE)$' "$STDOUT_FILE" | tail -n1 || true)
    [[ -z "$STATUS_LINE" ]] && STATUS_LINE="UNKNOWN"

    # Build the final output
    {
        echo "# Graph:      $NAME"
        echo "# k-plex (k): $K"
        echo "# Min size:   $MIN_SIZE"
        echo "# ncores:     $NCORES"
        echo "# Timeout:    2h"
        echo "# Runtime:    ${RUNTIME_SECS}s"
        echo "# Peak RSS:   ${PEAK_RSS_KB} kB"
        if [[ "$STOP_REASON" == "SIZE_EXCEEDED" ]]; then
            echo "# Status:     STOPPED — output exceeded 1 GB (partial results)"
        elif [[ $EXIT_CODE -eq 124 ]]; then
            echo "# Status:     TIMED OUT after 2h (partial results)"
        elif [[ $EXIT_CODE -eq 137 ]]; then
            echo "# Status:     KILLED (exit 137 / SIGKILL; likely OOM or external kill)"
        elif [[ $EXIT_CODE -eq 0 ]]; then
            echo "# Status:     COMPLETED ($STATUS_LINE)"
        else
            echo "# Status:     ERROR (exit code $EXIT_CODE)"
        fi
        echo "# Detected substructures: $NB_MODELS"
        echo ""
        echo "# --- Result file (SAT model / UNSAT) ---"
        if [[ -f "$RESULT_FILE" && -s "$RESULT_FILE" ]]; then
            cat "$RESULT_FILE"
            echo ""
        fi
        echo "# --- Solver stdout (stats, per-thread table, detected substructures) ---"
        if [[ -f "$STDOUT_FILE" && -s "$STDOUT_FILE" ]]; then
            cat "$STDOUT_FILE"
        fi
    } > "$OUTFILE"

    rm -rf "$TMPDIR"

    if [[ "$STOP_REASON" == "SIZE_EXCEEDED" ]]; then
        log "SIZE LIMIT: $NAME  (output exceeded 1 GB, $NB_MODELS models so far, partial results in $OUTFILE)"
    elif [[ $EXIT_CODE -eq 124 ]]; then
        log "TIMED OUT after 2h: $NAME  ($NB_MODELS models so far, partial results in $OUTFILE)"
    elif [[ $EXIT_CODE -eq 137 ]]; then
        log "KILLED (SIGKILL/137): $NAME  (peak_rss_kb=$PEAK_RSS_KB, likely OOM or external kill, results in $OUTFILE)"
    elif [[ $EXIT_CODE -eq 0 ]]; then
        log "COMPLETED: $NAME  ($NB_MODELS models, status=$STATUS_LINE, results in $OUTFILE)"
    else
        log "ERROR (exit $EXIT_CODE): $NAME"
    fi
done

log "All graphs done."