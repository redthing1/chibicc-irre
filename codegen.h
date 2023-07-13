
#ifndef _CODEGEN_H_
#define _CODEGEN_H_

void codegen(Obj *prog, FILE *out);
int align_to(int n, int align);

#endif // _CODEGEN_H_