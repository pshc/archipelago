#include <stdio.h>

int main(void) {
	int ptrsize = (int) sizeof(void *);
	printf("PTRSIZE = %d\n", ptrsize);
	return 0;
}
