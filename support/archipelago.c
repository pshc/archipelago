#include "archipelago.h"
#include <stdarg.h>
#include <stdlib.h>

tuple_t *tuple(unsigned int len, ...) {
	va_list ap;
	unsigned int i;
	tuple_t *t;
	if (!len)
		return NULL;
       	t = malloc(sizeof t[0] * len);
	if (!t)
		return NULL;
	va_start(ap, len);
	for (i = 0; i < len; i++)
		t[i] = va_arg(ap, void *);
	va_end(ap);
	return t;
}
