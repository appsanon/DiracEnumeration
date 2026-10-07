 BEGIN{
}

{
    for(i = 1; i <= NF; i++)
	printf("%d ", $i+1);
    printf("0\n");
}


END{

}
