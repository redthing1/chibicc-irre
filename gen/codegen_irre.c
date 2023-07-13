#include "../chibicc.h"
#include "../backend.h"
#include <math.h>

int ptr_size_irre = 4;

#define GP_MAX 8
#define FP_MAX 8

const char *R_ARG[] = {"r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7"};
const char *R_SAVED = "r8";
const char *R_TMP[] = {"r9", "r10"};
const char *R_SCRATCH[] = {"r11", "r12", "r13", "r14",
                           "r15", "r16", "r17", "r18"};

static FILE *output_file;
static int depth;
static Obj *current_fn;

static void gen_expr(Node *node);
static void gen_stmt(Node *node);

static void println(char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(output_file, fmt, ap);
  va_end(ap);
  fprintf(output_file, "\n");
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to_irre(5, 8) returns 8 and align_to_irre(11, 8) returns 16.
int align_to_irre(int n, int align) { return (n + align - 1) / align * align; }

static int count(void) {
  static int i = 1;
  return i++;
}

static void push(int reg) {
  // lower the stack pointer by 4 bytes
  println("\tsbi\tsp\tsp\t#4");
  // store the value of r1 to the stack
  // println("\tstw\tr1\tsp\t#0");
  println("\tstw\t%s\tsp\t#0", R_ARG[reg]);
  depth++;
}

static void pop(int reg) {
  // println("  ld a%d,0(sp)", reg);
  // println("  addi sp,sp,8");
  // load the value of the reg from the stack
  // println("\tldw\tr%d\tsp\t#0", reg);
  println("\tldw\t%s\tsp\t#0", R_ARG[reg]);
  depth--;
}

static void pushf(void) {
  println("  addi sp,sp,-8");
  println("  fsd fa0,0(sp)");
  depth++;
}

static void popf(int reg) {
  println("  fld fa%d,0(sp)", reg);
  println("  addi sp,sp,8");
  depth--;
}

// Compute the absolute address of a given node.
// It's an error if a given node does not reside in memory.
static void gen_addr(Node *node) {
  switch (node->kind) {
  case ND_VAR:
    // Local variable
    if (node->var->is_local) {
      // println("  li r9,%d", node->var->offset - node->var->ty->size);
      // println("  add r1,r8,r9");
      println("\tset\tat\t#%d", -(node->var->offset - node->var->ty->size));
      println("\tsub\tr1\tr8\tat");
      return;
    }

    // Function
    if (node->ty->kind == TY_FUNC) {
      int c = count();
      println("_L_b1_%d:", c);
      // println("  auipc r1,%%pcrel_hi(%s)", node->var->name);
      // println("  addi r1,r1,%%pcrel_lo(_L_b1_%d)", c);
      println("\tset\tat\t::%s", node->var->name);
      return;
    }

    // Global variable
    println("  lui r1,%%hi(%s)", node->var->name);
    println("  addi r1,r1,%%lo(%s)", node->var->name);
    return;
  case ND_DEREF:
    gen_expr(node->lhs);
    return;
  case ND_COMMA:
    gen_expr(node->lhs);
    gen_addr(node->rhs);
    return;
  case ND_MEMBER:
    gen_addr(node->lhs);
    println("  addi r1,r1,%d", node->member->offset);
    return;
  default:
    break;
  }

  error_tok(node->tok, "not an lvalue");
}

// Load a value from where r1 is pointing to.
static void load(Type *ty) {
  switch (ty->kind) {
  case TY_ARRAY:
  case TY_STRUCT:
  case TY_UNION:
  case TY_FUNC:
    // If it is an array, do not attempt to load a value to the
    // register because in general we can't load an entire array to a
    // register. As a result, the result of an evaluation of an array
    // becomes not the array itself but the address of the array.
    // This is where "array is automatically converted to a pointer to
    // the first element of the array in C" occurs.
    return;
  case TY_FLOAT:
    println("  flw fa0,0(r1)");
    return;
  case TY_DOUBLE:
    println("  fld fa0,0(r1)");
    return;
  default:
    break;
  }

  // char *suffix = ty->is_unsigned ? "u" : "";

  // When we load a char or a short value to a register, we always
  // extend them to the size of int, so we can assume the lower half of
  // a register always contains a valid value. The upper half of a
  // register for char, short and int may contain garbage. When we load
  // a long value to a register, it simply occupies the entire register.
  if (ty->size == 1) {
    // println("  lb%s r1,0(r1)", suffix);
    println("\tldb\tr1\tr1\t#0");
  } else if (ty->size == 2) {
    // println("  lh%s r1,0(r1)", suffix);
    println("\tldh\tr1\tr1\t#0");
  } else if (ty->size == 4) {
    // println("  lw r1,0(r1)", suffix);
    println("\tldw\tr1\tr1\t#0");
  } else {
    // println("  ld r1,0(r1)");
    println("\tldd\tr1\tr1\t#0");
  }
}

// Store r1 to an address that the stack top is pointing to.
static void store(Type *ty) {
  pop(1);

  switch (ty->kind) {
  case TY_STRUCT:
  case TY_UNION:
    for (int i = 0; i < ty->size; i++) {
      println("  lb a4,%d(r1)", i);
      println("  sb a4,%d(r2)", i);
    }
    return;
  case TY_FLOAT:
    println("  fsw fa0,0(r2)");
    return;
  case TY_DOUBLE:
    println("  fsd fa0,0(r2)");
    return;
  default:
    break;
  }

  if (ty->size == 1) {
    // println("  sb r1,0(r2)");
    println("\tstb\tr1\tr2\t#0");
  } else if (ty->size == 2) {
    println("  sh r1,0(r2)");
  } else if (ty->size == 4) {
    // println("  sw r1,0(r2)");
    println("\tstw\tr1\tr2\t#0");
  } else {
    // println("  sd r1,0(r2)");
    // to store a dword, we have to do two stw
    // println("\t%%error\tstd\tr1\tr2\t#0");
    println("\t%%error\tstd\tr1\tr2\t#0\t; %d", ty->kind);
  }
}

static void cmp_zero(Type *ty) {
  switch (ty->kind) {
  case TY_FLOAT:
    println("  fmv.w.x fa1,zero");
    println("  feq.s r1,fa0,fa1");
    return;
  case TY_DOUBLE:
    println("  fmv.d.x fa1,zero");
    println("  feq.d r1,fa0,fa1");
    return;
  default:
    break;
  }

  // println("  seqz r1,r1");
  println("\ttcu\tr1\tr1\tr1");
  println("\tadi\tr1\tr1\t#1");
  println("\tset\tat\t#1");
  println("\tand\tr1\tr1\tat");
}

enum { I8, I16, I32, I64, U8, U16, U32, U64, F32, F64 };

static int getTypeId(Type *ty) {
  switch (ty->kind) {
  case TY_CHAR:
    return ty->is_unsigned ? U8 : I8;
  case TY_SHORT:
    return ty->is_unsigned ? U16 : I16;
  case TY_INT:
    return ty->is_unsigned ? U32 : I32;
  case TY_LONG:
    return ty->is_unsigned ? U64 : I64;
  case TY_FLOAT:
    return F32;
  case TY_DOUBLE:
    return F64;
  default:
    return U64;
    ;
  }
}

// The table for type casts
static char i32i8[] = "  slliw r1,r1,24\n  sraiw r1,r1,24";
static char i32u8[] = "  andi r1,r1,0xff";
static char i32i16[] = "  slliw r1,r1,16\n  sraiw r1,r1,16";
static char i32u16[] = "  slli r1,r1,48\n  srli r1,r1,48";

static char u64i32[] = "  slli r1,r1,32\n  srli r1,r1,32";

static char i32f32[] = "  fcvt.s.w fa0,r1";
static char i32f64[] = "  fcvt.d.w fa0,r1";

static char u32f32[] = "  fcvt.s.wu fa0,r1";
static char u32f64[] = "  fcvt.d.wu fa0,r1";

static char i64f32[] = "  fcvt.s.l fa0,r1";
static char i64f64[] = "  fcvt.d.l fa0,r1";

static char u64f32[] = "  fcvt.s.lu fa0,r1";
static char u64f64[] = "  fcvt.d.lu fa0,r1";

static char f32i8[] = "  fcvt.w.s r1,fa0,rtz\n  andi r1,r1,0xff";
static char f32u8[] = "  fcvt.wu.s r1,fa0,rtz\n  andi r1,r1,0xff";
static char f32i16[] = "  fcvt.w.s r1,fa0,rtz\n"
                       "  slliw r1,r1,16\n"
                       "  sraiw r1,r1,16\n";
static char f32u16[] = "  fcvt.wu.s r1,fa0,rtz\n"
                       "  slli r1,r1,48\n"
                       "  srli r1,r1,48\n";
static char f32i32[] = "  fcvt.w.s r1,fa0,rtz";
static char f32u32[] = "  fcvt.wu.s r1,fa0,rtz";
static char f32i64[] = "  fcvt.l.s r1,fa0,rtz";
static char f32u64[] = "  fcvt.lu.s r1,fa0,rtz";
static char f32f64[] = "  fcvt.d.s fa0,fa0";

static char f64i8[] = "  fcvt.w.d r1,fa0,rtz\n  andi r1,r1,0xff";
static char f64u8[] = "  fcvt.wu.d r1,fa0,rtz\n  andi r1,r1,0xff";
static char f64i16[] = "  fcvt.w.d r1,fa0,rtz\n"
                       "  slliw r1,r1,16\n"
                       "  sraiw r1,r1,16\n";
static char f64u16[] = "  fcvt.wu.d r1,fa0,rtz\n"
                       "  slli r1,r1,48\n"
                       "  srli r1,r1,48\n";
static char f64i32[] = "  fcvt.w.d r1,fa0,rtz";
static char f64u32[] = "  fcvt.wu.d r1,fa0,rtz";
static char f64f32[] = "  fcvt.s.d fa0,fa0";
static char f64i64[] = "  fcvt.l.d r1,fa0,rtz";
static char f64u64[] = "  fcvt.lu.d r1,fa0,rtz";

static char *cast_table[][10] = {
    // i8   i16     i32     i64     u8     u16     u32     u64     f32     f64
    {NULL, NULL, NULL, NULL, i32u8, i32u16, NULL, NULL, i32f32, i32f64},  // i8
    {i32i8, NULL, NULL, NULL, i32u8, i32u16, NULL, NULL, i32f32, i32f64}, // i16
    {i32i8, i32i16, NULL, NULL, i32u8, i32u16, NULL, NULL, i32f32,
     i32f64}, // i32
    {i32i8, i32i16, u64i32, NULL, i32u8, i32u16, u64i32, NULL, i64f32,
     i64f64}, // i64

    {i32i8, NULL, NULL, NULL, NULL, NULL, NULL, NULL, i32f32, i32f64},    // u8
    {i32i8, i32i16, NULL, NULL, i32u8, NULL, NULL, NULL, i32f32, i32f64}, // u16
    {i32i8, i32i16, NULL, NULL, i32u8, i32u16, NULL, NULL, u32f32,
     u32f64}, // u32
    {i32i8, i32i16, u64i32, NULL, i32u8, i32u16, u64i32, NULL, u64f32,
     u64f64}, // u64

    {f32i8, f32i16, f32i32, f32i64, f32u8, f32u16, f32u32, f32u64, NULL,
     f32f64}, // f32
    {f64i8, f64i16, f64i32, f64i64, f64u8, f64u16, f64u32, f64u64, f64f32,
     NULL}, // f64
};

static void cast(Type *from, Type *to) {
  if (to->kind == TY_VOID) {
    return;
  }

  if (to->kind == TY_BOOL) {
    println("  snez r1,r1");
    return;
  }

  int t1 = getTypeId(from);
  int t2 = getTypeId(to);
  if (cast_table[t1][t2]) {
    println(cast_table[t1][t2]);
  }
}

static bool has_flonum(Type *ty, int lo, int hi, int offset) {
  if (ty->kind == TY_STRUCT || ty->kind == TY_UNION) {
    for (Member *mem = ty->members; mem; mem = mem->next) {
      if (!has_flonum(mem->ty, lo, hi, offset + mem->offset)) {
        return false;
      }
    }
    return true;
  }

  if (ty->kind == TY_ARRAY) {
    for (int i = 0; i < ty->array_len; i++) {
      if (!has_flonum(ty->base, lo, hi, offset + ty->base->size * i)) {
        return false;
      }
    }
    return true;
  }

  return offset < lo || hi <= offset || is_flonum(ty);
}

static bool has_flonum1(Type *ty) { return has_flonum(ty, 0, 8, 0); }

static bool has_flonum2(Type *ty) { return has_flonum(ty, 8, 16, 0); }

static void push_struct(Type *ty) {
  int sz = align_to_irre(ty->size, 8);
  println("  addi sp,sp,%d", -sz);
  depth += sz / 8;

  for (int i = 0; i < ty->size; i++) {
    println("  lb t3,%d(r1)", i);
    println("  sb t3,%d(sp)", i);
  }
}

static void push_args2(Node *args, bool first_pass) {
  if (!args) {
    return;
  }

  push_args2(args->next, first_pass);

  if ((first_pass && !args->pass_by_stack) ||
      (!first_pass && args->pass_by_stack)) {
    return;
  }

  gen_expr(args);
  switch (args->ty->kind) {
  case TY_STRUCT:
  case TY_UNION:
    push_struct(args->ty);
    break;
  case TY_FLOAT:
  case TY_DOUBLE:
    pushf();
    break;
  default:
    push(0);
  }
}

static int push_args(Node *args) {
  int stack = 0, gp = 0, fp = 0;

  for (Node *arg = args; arg; arg = arg->next) {
    Type *ty = arg->ty;

    switch (ty->kind) {
    case TY_STRUCT:
    case TY_UNION:
      if (ty->size > 16) {
        arg->pass_by_stack = true;
        stack += align_to_irre(ty->size, 8) / 8;
      } else {
        bool fp1 = has_flonum1(ty);
        bool fp2 = has_flonum2(ty);

        if (fp + fp1 + fp2 < FP_MAX && gp + !fp1 + !fp2 < GP_MAX) {
          fp = fp + fp1 + fp2;
          gp = gp + !fp1 + !fp2;
        } else {
          arg->pass_by_stack = true;
          stack += align_to_irre(ty->size, 8) / 8;
        }
      }
      break;
    case TY_FLOAT:
    case TY_DOUBLE:
      if (fp >= FP_MAX && gp > GP_MAX) {
        arg->pass_by_stack = true;
        stack++;
      } else if (fp < FP_MAX) {
        fp++;
      } else {
        gp++;
      }
      break;
    default:
      if (gp++ >= GP_MAX) {
        arg->pass_by_stack = true;
        stack++;
      }
    }
  }

  push_args2(args, true);
  push_args2(args, false);

  return stack;
}

// Generate code for a given node.
static void gen_expr(Node *node) {
  if (opt_emit_debug) {
    println("\t; .loc %d %d", node->tok->file->file_no, node->tok->line_no);
  }

  switch (node->kind) {
  case ND_NULL_EXPR:
    return;
  case ND_NUM: {
    union {
      float f32;
      double f64;
      uint32_t u32;
      uint64_t u64;
    } u;

    switch (node->ty->kind) {
    case TY_FLOAT:
      u.f32 = node->fval;
      println("  li r1,%u  # float %f", u.u32, node->fval);
      println("  fmv.w.x fa0,r1");
      return;
    case TY_DOUBLE:
      u.f64 = node->fval;
      println("  li r1,%lu  # float %f", u.u64, node->fval);
      println("  fmv.d.x fa0,r1");
      return;
    default:
      break;
    }

    // println("  li r1,%ld", node->val);
    println("\tset\tr1\t#%ld", node->val);
    return;
  }
  case ND_NEG:
    gen_expr(node->lhs);

    switch (node->ty->kind) {
    case TY_FLOAT:
      println("  fneg.s fa0,fa0");
      return;
    case TY_DOUBLE:
      println("  fneg.d fa0,fa0");
      return;
    default:
      break;
    }

    println("  neg r1,r1");
    return;
  case ND_VAR:
  case ND_MEMBER:
    gen_addr(node);
    load(node->ty);
    return;
  case ND_DEREF:
    gen_expr(node->lhs);
    load(node->ty);
    return;
  case ND_ADDR:
    gen_addr(node->lhs);
    return;
  case ND_ASSIGN:
    gen_addr(node->lhs);
    push(0);
    gen_expr(node->rhs);
    store(node->ty);
    return;
  case ND_STMT_EXPR:
    for (Node *n = node->body; n; n = n->next) {
      gen_stmt(n);
    }
    return;
  case ND_COMMA:
    gen_expr(node->lhs);
    gen_expr(node->rhs);
    return;
  case ND_CAST:
    gen_expr(node->lhs);
    cast(node->lhs->ty, node->ty);
    return;
  case ND_MEMZERO: {
    int offset = node->var->offset;
    for (int i = 0; i < node->var->ty->size; i++) {
      offset -= sizeof(char);
      // println("  li r9,%d", offset);
      // println("  add r9,r9,%s", R_SAVED);
      // println("  sb zero,0(r9)", offset);
      // println("\tset\tat\t#%d", offset);
      // println("\tadd\tat\tat\t%s", R_SAVED);
      if (offset >= 0) {
        println("\tset\tat\t#%d", offset);
        println("\tadd\tat\tat\t%s", R_SAVED);
      } else {
        println("\tset\tat\t#%d", -offset);
        println("\tsub\tat\t%s\tat", R_SAVED);
      }
      println("\tset\tad\t#0");
      println("\tstw\tad\tat\t#0");
    }
    return;
  }
  case ND_COND: {
    int c = count();
    gen_expr(node->cond);
    cmp_zero(node->cond->ty);
    // println("  bne r1,zero,_L_else_%d", c);
    println("\tset\tat\t::_L_else_%d", c);
    println("\tbvn\tat\tr1\t#1");
    gen_expr(node->then);
    println("  j _L_end_%d", c);
    println("_L_else_%d:", c);
    gen_expr(node->els);
    println("_L_end_%d:", c);
    return;
  }
  case ND_NOT:
    gen_expr(node->lhs);
    cmp_zero(node->lhs->ty);
    return;
  case ND_BITNOT:
    gen_expr(node->lhs);
    println("  not r1,r1");
    return;
  case ND_LOGAND: {
    int c = count();
    gen_expr(node->lhs);
    cmp_zero(node->lhs->ty);
    // println("  bne r1,zero,_L_false_%d", c);
    println("\tset\tat\t::_L_false_%d", c);
    println("\tbvn\tat\tr1\t#1");
    gen_expr(node->rhs);
    cmp_zero(node->rhs->ty);
    // println("  bne r1,zero,_L_false_%d", c);
    println("\tset\tat\t::_L_false_%d", c);
    println("\tbvn\tat\tr1\t#1");
    println("  li r1,1");
    println("  j _L_end_%d", c);
    println("_L_false_%d:", c);
    println("  li r1,0");
    println("_L_end_%d:", c);
    return;
  }
  case ND_LOGOR: {
    int c = count();
    gen_expr(node->lhs);
    cmp_zero(node->lhs->ty);
    // println("  beqz r1,_L_true_%d", c);
    println("\tset\tat\t::_L_true_%d", c);
    println("\tbve\tat\tr1\t#1");
    gen_expr(node->rhs);
    cmp_zero(node->rhs->ty);
    // println("  beqz r1,_L_true_%d", c);
    println("\tset\tat\t::_L_true_%d", c);
    println("\tbve\tat\tr1\t#1");
    println("  li r1,0");
    println("  j _L_end_%d", c);
    println("_L_true_%d:", c);
    println("  li r1,1");
    println("_L_end_%d:", c);
    return;
  }
  case ND_FUNCALL: {
    int stack_args = push_args(node->args);
    gen_expr(node->lhs);
    // println("  mv r10,r1");

    int fp = 0, gp = 0;
    Type *cur_param = node->func_ty->params;
    for (Node *arg = node->args; arg; arg = arg->next) {
      if (node->func_ty->is_variadic && cur_param == NULL) {
        if (gp < GP_MAX) {
          pop(gp++);
        }
        continue;
      }
      cur_param = cur_param->next;
      Type *ty = arg->ty;

      switch (ty->kind) {
      case TY_STRUCT:
      case TY_UNION:
        if (ty->size > 16) {
          continue;
        }

        bool fp1 = has_flonum1(ty);
        bool fp2 = has_flonum2(ty);

        if (fp + fp1 + fp2 < FP_MAX && gp + !fp1 + !fp2 < GP_MAX) {
          if (fp1) {
            popf(fp++);
          } else {
            pop(gp++);
          }

          if (ty->size > 8) {
            if (fp2) {
              popf(fp++);
            } else {
              pop(gp++);
            }
          }
        }
        break;
      case TY_FLOAT:
      case TY_DOUBLE:
        if (fp < FP_MAX) {
          popf(fp++);
        } else if (gp < GP_MAX) {
          pop(gp++);
        }
        break;
      default:
        if (gp < GP_MAX) {
          pop(gp++);
        }
      }
    }

    // println("  jalr at");
    println("\tcal\tat");

    if (stack_args) {
      depth -= stack_args;
      println("  addi sp,sp,%d", stack_args * 8);
    }

    // It looks like the most significant 48 or 56 bits in r1 may
    // contain garbage if a function return type is short or bool/char,
    // respectively. We clear the upper bits here.
    switch (node->ty->kind) {
    case TY_BOOL:
      println("  andi r1,r1,0xff");
    case TY_CHAR:
      if (node->ty->is_unsigned) {
        println("  andi r1,r1,0xff");
      } else {
        println("  slliw r1,r1,24");
        println("  sraiw r1,r1,24");
      }
      return;
    case TY_SHORT:
      if (node->ty->is_unsigned) {
        println("  slli r1,r1,48");
        println("  srli r1,r1,48");
      } else {
        println("  slliw r1,r1,16");
        println("  sraiw r1,r1,16");
      }
      return;
    default:
      break;
    }
    return;
  default:
    break;
  }
  }

  if (is_flonum(node->lhs->ty)) {
    gen_expr(node->rhs);
    pushf();
    gen_expr(node->lhs);
    popf(1);

    char *suffix = (node->lhs->ty->kind == TY_FLOAT) ? "s" : "d";

    switch (node->kind) {
    case ND_ADD:
      println("  fadd.%s fa0,fa0,fa1", suffix);
      return;
    case ND_SUB:
      println("  fsub.%s fa0,fa0,fa1", suffix);
      return;
    case ND_MUL:
      println("  fmul.%s fa0,fa0,fa1", suffix);
      return;
    case ND_DIV:
      println("  fdiv.%s fa0,fa0,fa1", suffix);
      return;
    case ND_EQ:
      println("  feq.%s r1,fa0,fa1", suffix);
      return;
    case ND_NE:
      println("  feq.%s r1,fa0,fa1", suffix);
      println("  seqz r1,r1");
      return;
    case ND_LT:
      println("  flt.%s r1,fa0,fa1", suffix);
      return;
    case ND_LE:
      println("  fle.%s r1,fa0,fa1", suffix);
      return;
    default:
      break;
    }

    error_tok(node->tok, "invalid expression");
  }

  // put rhs into r1
  gen_expr(node->rhs);
  // push r1 onto the stack
  push(0);
  // put lhs into r1
  gen_expr(node->lhs);
  // grab the rhs from the stack and put it into r2
  pop(1);

  // char *suffix =
  //     node->lhs->ty->kind == TY_LONG || node->lhs->ty->base ? "" : "w";
  switch (node->kind) {
  case ND_ADD:
    // println("  add%s r1,r1,r2", suffix);
    println("\tadd\tr1\tr1\tr2");
    return;
  case ND_SUB:
    // println("  sub%s r1,r1,r2", suffix);
    println("\tsub\tr1\tr1\tr2");
    return;
  case ND_MUL:
    // println("  mul%s r1,r1,r2", suffix);
    println("\tmul\tr1\tr1\tr2");
    return;
  case ND_DIV:
    // if (node->ty->is_unsigned) {
    //   println("  divu%s r1,r1,r2", suffix);
    // } else {
    //   println("  div%s r1,r1,r2", suffix);
    // }
    println("\tdiv\tr1\tr1\tr2");
    return;
  case ND_MOD:
    // if (node->ty->is_unsigned) {
    //   println("  remu%s r1,r1,r2", suffix);
    // } else {
    //   println("  rem%s r1,r1,r2", suffix);
    // }
    println("\tmod\tr1\tr1\tr2");
    return;
  case ND_BITAND:
    // println("  and r1,r1,r2");
    println("\tand\tr1\tr1\tr2");
    return;
  case ND_BITOR:
    // println("  or r1,r1,r2");
    println("\torr\t\tr1\tr1\tr2");
    return;
  case ND_BITXOR:
    // println("  xor r1,r1,r2");
    println("\txor\tr1\tr1\tr2");
    return;
  case ND_EQ:
    // we want to check if r1 == r2 with irre
    // we have available tcu, which will be -1, 0, or 1
    // if tcu outputs 0, set r1 to 1, otherwise set r1 to 0
    println("\ttcu\tr1\tr1\tr2"); // r1 = -1,0,1
    println("\tadi\tr1\tr1\t#1"); // r1 = 0,1,2 (0b00, 0b01, 0b10)
    println("\tset\tat\t#1");     // at = 0b01
    println("\tand\tr1\tr1\tat"); // if the least significant bit is 1, r1 = 1
    return;
  case ND_NE:
    println("\ttcu\tr1\tr1\tr2"); // r1 = -1,0,1
    println("\tadi\tr1\tr1\t#1"); // r1 = 0,1,2 (0b00, 0b01, 0b10)
    println("\tset\tat\t#1");     // at = 0b01
    println("\txor\tr1\tr1\tat"); // if the least significant bit is 1, r1 = 0
    return;
  case ND_LT:
    // if (node->lhs->ty->is_unsigned) {
    //   println("  sltu r1,r1,r2");
    // } else {
    //   println("  slt r1,r1,r2");
    // }
    println("\ttcu\tr1\tr1\tr2"); // r1 = -1,0,1
    println("\tadi\tr1\tr1\t#1"); // r1 = 0,1,2 (0b00, 0b01, 0b10)
    // set r1 to 1 if neither of the two bits are set
    println("\tset\tat\t#1");
    println("\tlsh\tr1\tr1\tat"); // vacate 0b00
    println("\txor\tr1\tr1\tat"); // xor with 0b1 to flip the bit
    return;
  case ND_LE:
    // if (node->lhs->ty->is_unsigned) {
    //   println("  sgtu r1,r1,r2");
    // } else {
    //   println("  sgt r1,r1,r2");
    // }
    // println("  xori r1,r1,1");
    println("\ttcu\tr1\tr1\tr2"); // r1 = -1,0,1
    println("\tadi\tr1\tr1\t#1"); // r1 = 0,1,2 (0b00, 0b01, 0b10)
    // set r1 to 1 if 0b00 (less) or 0b01 (equal)
    println("\tset\tat\t#-1");
    println("\tlsh\tr1\tr1\tat"); // shift right so we have either 0b1 or 0b0
    println("\tset\tat\t#1");
    println("\txor\tr1\tr1\tat"); // xor with 0b1 to flip the bit
    return;
  case ND_SHL:
    // println("  sll%s r1,r1,r2", suffix);
    println("\tlsh\tr1\tr1\tr2");
    return;
  case ND_SHR:
    // negate the shift amount r2 (to shift right)
    println("\tset\tat\t#0");
    println("\tsub\tr2\tat\tr2");
    if (node->lhs->ty->is_unsigned) {
      // println("  srl%s r1,r1,r2", suffix);
      println("\tlsh\tr1\tr1\tr2");
    } else {
      // println("  sra%s r1,r1,r2", suffix);
      println("\tash\tr1\tr1\tr2");
    }
    return;
  default:
    break;
  }

  error_tok(node->tok, "invalid expression");
}

static void gen_stmt(Node *node) {
  if (opt_emit_debug) {
    println("\t; .loc %d %d", node->tok->file->file_no, node->tok->line_no);
  }

  switch (node->kind) {
  case ND_IF: {
    int c = count();
    gen_expr(node->cond);
    cmp_zero(node->cond->ty);
    // println("  bne r1,zero,_L_else_%d", c);
    println("\tset\tat\t::_L_else_%d", c);
    println("\tbve\tat\tr1\t#1");
    gen_stmt(node->then);
    // println("  j _L_end_%d", c);
    println("\tjmi\t::_L_end_%d", c);
    println("_L_else_%d:", c);
    if (node->els) {
      gen_stmt(node->els);
    }
    println("_L_end_%d:", c);
    return;
  }
  case ND_FOR: {
    int c = count();
    if (node->init) {
      gen_stmt(node->init);
    }
    println("_L_begin_%d:", c);
    if (node->cond) {
      gen_expr(node->cond);
      cmp_zero(node->cond->ty);
      // println("  bne r1,zero,%s", node->brk_label);
      println("\tset\tat\t::%s", node->brk_label);
      println("\tbvn\tat\tr1\t#1");
    }
    gen_stmt(node->then);
    println("%s:", node->cont_label);
    if (node->inc) {
      gen_expr(node->inc);
    }
    // println("  j _L_begin_%d", c);
    println("\tjmi\t::_L_begin_%d", c);
    println("%s:", node->brk_label);
    return;
  }
  case ND_DO: {
    int c = count();
    println("_L_begin_%d:", c);
    gen_stmt(node->then);
    println("%s:", node->cont_label);
    gen_expr(node->cond);
    cmp_zero(node->cond->ty);
    // println("  beqz r1,_L_begin_%d", c);
    println("\tset\tat\t::_L_begin_%d", c);
    println("\tbve\tat\tr1\t#1");
    println("%s:", node->brk_label);
    return;
  }
  case ND_SWITCH:
    gen_expr(node->cond);

    for (Node *n = node->case_next; n; n = n->case_next) {
      // println("  li a4,%ld", n->val);
      // println("  beq r1,a4,%s", n->label);
      println("\tset\tat\t#%ld", n->val);
      println("\tbve\tat\tr1\t#1");
    }

    if (node->default_case) {
      // println("  j %s", node->default_case->label);
      println("\tjmi\t::%s", node->default_case->label);
    }

    // println("  j %s", node->brk_label);
    println("\tjmi\t::%s", node->brk_label);
    gen_stmt(node->then);
    println("%s:", node->brk_label);
    return;
  case ND_CASE:
    println("%s:", node->label);
    gen_stmt(node->lhs);
    return;
  case ND_BLOCK:
    for (Node *n = node->body; n; n = n->next) {
      gen_stmt(n);
    }
    return;
  case ND_GOTO:
    // println("  j %s", node->unique_label);
    println("\tjmi\t::%s", node->unique_label);
    return;
  case ND_LABEL:
    println("%s:", node->unique_label);
    gen_stmt(node->lhs);
    return;
  case ND_RETURN:
    if (node->lhs) {
      gen_expr(node->lhs);
    }
    // println("  j _L_return_%s", current_fn->name);
    println("\tjmi\t::_L_return_%s", current_fn->name);
    return;
  case ND_EXPR_STMT:
    gen_expr(node->lhs);
    return;
  case ND_ASM:
    println("  %s", node->asm_str);
    return;
  default:
    break;
  }

  error_tok(node->tok, "invalid statement");
}

// Assign offsets to local variables.
static void assign_lvar_offsets(Obj *prog) {
  for (Obj *fn = prog; fn; fn = fn->next) {
    if (!fn->is_function) {
      continue;
    }

    int top = 16;
    int bottom = 0;

    int gp = 0, fp = 0;

    // Assign offsets to pass-by-stack parameters.
    for (Obj *var = fn->params; var; var = var->next) {
      if (is_flonum(var->ty)) {
        if (fp < FP_MAX) {
          fp++;
          continue;
        } else if (gp < GP_MAX) {
          gp++;
          continue;
        }
      } else {
        if (gp++ < GP_MAX) {
          continue;
        }
      }

      top = align_to_irre(top, 8);
      var->offset = top + var->ty->size;
      top += var->ty->size;
    }

    // Assign offsets to pass-by-register parameters and local variables.
    for (Obj *var = fn->locals; var; var = var->next) {
      if (var->offset) {
        continue;
      }

      bottom = align_to_irre(bottom, var->align);
      var->offset = -bottom;
      bottom += var->ty->size;
    }

    fn->stack_size = align_to_irre(bottom, 16);
  }
}

static void emit_data(Obj *prog) {
  println("%%section data");

  for (Obj *var = prog; var; var = var->next) {
    if (var->is_function || !var->is_definition) {
      continue;
    }

    // if (var->is_static)
    //   println("  .local %s", var->name);
    // else
    //   println("  .globl %s", var->name);
    // irre doesn't support local
    if (var->is_static) {
      println("; .local %s", var->name);
    } else {
      println("%%global %s", var->name);
    }

    println("\t; .align %d", (int)log2(var->align));

    if (var->init_data) {
      // println("  .data");
      println("%s:", var->name);

      Relocation *rel = var->rel;
      int pos = 0;
      while (pos < var->ty->size) {
        if (rel && rel->offset == pos) {
          println("  .quad %s%+ld", rel->label, rel->addend);
          rel = rel->next;
          pos += 8;
        } else {
          // println("  .byte %d", var->init_data[pos++]);
          println("\t%%d\t\\x\t$%02x", var->init_data[pos++]);
        }
      }
      continue;
    }

    println("%%section bss");
    println("%s:", var->name);
    // println("  .zero %d", var->ty->size);
    println("\t%%d\t\\z\t#%d", var->ty->size);
  }
}

static void store_fp(int r, int offset, int sz) {
  println("  li r9,%d", offset - sz);
  println("  add r9,r9,r8");
  switch (sz) {
  case 4:
    println("  fsw fa%d, 0(r9)", r, offset);
    return;
  case 8:
    println("  fsd fa%d, 0(r9)", r, offset);
    return;
  }
  unreachable();
}

static void store_gp(int r, int offset, int sz) {
  if (opt_emit_debug) {
    println("\t; store_gp(%d, %d, %d)", r, offset, sz);
  }
  // println("  li r9,%d", offset - sz);
  // println("  add r9,r9,r8");
  const char *r_name = R_ARG[r];
  println("\tset\tat\t#%d", offset - sz);
  println("\tadd\tat\tat\t%s", R_SAVED);
  switch (sz) {
  case 1:
    // println("  sb a%d,0(r9)", r);
    println("\tstb\t%s\tat\t#0", r_name);
    return;
  case 2:
    // println("  sh a%d,0(r9)", r);
    // we have to do two stb to store 2 bytes: first stb to store lower 8 bits,
    // then shift 8 bits and stb again
    println("\tstb\t%s\tat\t#0", r_name);
    println("\tset\tad\t#8");
    println("\tlsh\tad\t%s\tad", r_name);
    println("\tstb\tad\tat\t#1");
    return;
  case 4:
    // println("  sw a%d,0(r9)", r);
    println("\tstw\t%s\tat\t#0", r_name);
    return;
  case 8:
    // println("  sd a%d,0(r9)", r);
    println("<unsupported> store_gp(%d, %d, %d)", r, offset, sz);
    return;
  }
  printf("WTF %d\n", sz);
  unreachable();
}

static void emit_text(Obj *prog) {
  println("%%section text");

  for (Obj *fn = prog; fn; fn = fn->next) {
    if (!fn->is_function || !fn->is_definition) {
      continue;
    }

    // if (fn->is_static) {
    //   println("\t; %%local %s", fn->name);
    // }
    // else {
    //   println("%%global %s", fn->name);
    // }
    // irre doesn't support local
    if (fn->is_static) {
      println("; .local %s", fn->name);
    } else {
      println("%%global %s", fn->name);
    }

    // println("  .text");
    println("%s:", fn->name);
    current_fn = fn;

    // Prologue
    // println("  sd ra,-8(sp)");
    // println("  sd r8,-16(sp)");
    // println("  addi r8,sp,-16");
    // println("  li r9,-%d", fn->stack_size + 16);
    // println("  add sp,sp,r9");

    // lower stack pointer to save lr and fp
    if (opt_emit_debug) {
      println("\t; prologue");
    }
    println("\tsbi\tsp\t#8");
    println("\tstw\tlr\tsp\t#4");
    println("\tstw\t%s\tsp\t#0", R_SAVED);
    // lower stack for function body
    println("\tsbi\tsp\t#%d", fn->stack_size + 16);

    // Save passed-by-register arguments to the stack
    int fp = 0, gp = 0;
    for (Obj *var = fn->params; var; var = var->next) {
      if (var->offset > 0) {
        continue;
      }

      // __va_area__
      if (var->ty->kind == TY_ARRAY) {
        int offset = var->offset - var->ty->size;
        while (gp < GP_MAX) {
          offset += 8;
          store_gp(gp++, offset, 8);
        }
      } else if (is_flonum(var->ty)) {
        if (fp < FP_MAX) {
          store_fp(fp++, var->offset, var->ty->size);
        } else {
          store_gp(gp++, var->offset, var->ty->size);
        }
      } else {
        store_gp(gp++, var->offset, var->ty->size);
      }
    }

    // Emit code
    gen_stmt(fn->body);
    assert(depth == 0);

    // Epilogue
    println("_L_return_%s:", fn->name);
    // println("  li r9,%d", fn->stack_size + 16);
    // println("  add sp,sp,r9");
    // println("  ld ra,-8(sp)");
    // println("  ld r8,-16(sp)");
    // println("  ret");

    if (opt_emit_debug) {
      println("\t; epilogue");
    }
    // raise stack pointer for function body
    println("\tadi\tsp\tsp\t#%d", fn->stack_size + 16);
    // restore lr and fp
    println("\tldw\t%s\tsp\t#0", R_SAVED);
    println("\tldw\tlr\tsp\t#4");
    // raise stack pointer after restore lr and fp
    println("\tadi\tsp\tsp\t#8");
  }
}

void codegen_irre(Obj *prog, FILE *out) {
  output_file = out;

  File **files = get_input_files();
  for (int i = 0; files[i]; i++) {
    println("; .file %d \"%s\"", files[i]->file_no, files[i]->name);
  }

  assign_lvar_offsets(prog);
  emit_text(prog);
  emit_data(prog);
}
