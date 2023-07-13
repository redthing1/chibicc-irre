
#ifndef _CODEGEN_H_
#define _CODEGEN_H_

void codegen(Obj *prog, FILE *out);
int align_to(int n, int align);

extern bool opt_emit_debug;

#endif // _CODEGEN_H_