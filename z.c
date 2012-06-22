#include <stdio.h>
#include <stdlib.h>

void fail(const char *err) {
	fputs(err, stderr);
	fputc('\n', stderr);
	exit(1);
}
