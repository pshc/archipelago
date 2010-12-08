#include "archipelago.h"
#include "bedrock.h"
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

struct List *list(unsigned int len, ...) {
	va_list ap;
	unsigned int i;
	struct List *ls;
	void **temp;
	if (!len)
		return Nil();
	/* Wow, this sucks. */
	temp = malloc(sizeof temp[0] * len);
	if (!temp)
		return NULL;
	va_start(ap, len);
	for (i = 0; i < len; i++)
		temp[i] = va_arg(ap, void *);
	va_end(ap);
	ls = Nil();
	while (i > 0)
		ls = Cons(temp[--i], ls);
	free(temp);
	return ls;
}
