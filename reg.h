#ifndef REG_H
#define REG_H

#define UNKNOWN_COND_FLAGS 0xffffffff

/*** REGISTER MODELING FRAMEWORK ***/
#define DERI_LEN 128   // length of register derivation tree
#define VALUE_UNDEF     0
#define VALUE_CONST     1
#define VALUE_PARA      2   /*unknown parameter*/
#define VALUE_EXPR      3
#define VALUE_BIV       4
#define VALUE_UNPRED    VALUE_PARA /*unpredictable value*/

typedef struct linear_expr *   expr_p;
typedef struct BIV *         biv_p;

//NOTE: avoid using dynamic allocation, the source of all errors
typedef struct {
  char      name[4];
  char      t;       // value type: expression, const, induction, parameter
  long       val;
  expr_p    expr;
  biv_p     biv;
  char      para[3];
  int       flag;
} reg_t;

typedef enum {
    OPR_MIN,
    OPR_ADD,
    OPR_SUB,
    OPR_MUL,
    OPR_NOT,
    OPR_AND,
    OPR_ORR,
    OPR_XOR,
    OPR_RSF,
    OPR_LSF,
    OPR_MAX  
} operation_t;

int     initRegSet(reg_t *regList);
int     clearRegList(reg_t *regList);

void    setInt(reg_t *reg, long k);
void    initReg(reg_t *reg);
void    clrReg(reg_t *reg);
void    regUnknown(reg_t *reg);
int     regEq( reg_t reg1, reg_t reg2 );
int     cpyReg( reg_t *dst, reg_t src);

void    printReg(FILE *fp, reg_t reg);
int     findReg(reg_t *regList, char regName[] );

/*** EXPRESSION VALUE OPERATION ***
 *  Expression value is a polynomial expression C*v
 *  C = coefficient constant, v = parameter / constant
 */
#define MAX_EXPR_LEN 2 /* max length: c1:v1 + .. + c4:v4 + K:1 */
struct linear_expr {
    reg_t   value[MAX_EXPR_LEN];  //restrict to CONST / INDUCTION / PARA
    int     coef[MAX_EXPR_LEN];
    int     added[MAX_EXPR_LEN];  //added=0: not processed, added=1: added
    long    k;
    int     varNum;
};

typedef struct linear_expr    expr_s;

void    printExpr(FILE* fp, expr_p expr);
int     computeExpr(operation_t op, expr_p exprD, expr_p expr1, expr_p expr2);
int     cpyExpr(expr_p exprDst, expr_p exprSrc);
void    reg2expr(reg_t *r);
void    setExpr(expr_p expr, reg_t r);
void    clrExpr(expr_p expr);
int     exprEq(expr_p expr1, expr_p expr2);
void    initExpr(expr_p expr);
int     compute_cond_flags(long res);

/*** ABSTRACT INTERPRETATION OF REG_VALUE ***/
int     mergeReg(reg_t *dstReg,reg_t srcReg,int isBackEdge);//merge abs.reg value
int     regOpr(operation_t op, reg_t *rD, reg_t r1, reg_t r2); //abs.opr on r.values

#endif
