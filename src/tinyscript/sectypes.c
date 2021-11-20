#include "tinyscript/sectypes.h"
#include <stdbool.h>
#include <stdlib.h>


sec_label* fillLabel(sec_lattice *L,char* ident) {
    sec_label* tmp = NULL;
     for(size_t i = 0; i < ubarray_size(L->uba);i++) {
        tmp = ((sec_label*)*(ubarray_elem(L->uba, i)));
        if(strcmp(tmp->name,ident) == 0) {
            return tmp;
        }
    }

    return tmp;
}

bool sec_lessthan(sec_lattice *L, sec_label *l1, sec_label *l2) {
    // should implement the partial order relation to return true
    // if and only if l1 is less than l2
    // in the lattice defined by L, and false otherwise
   
    // replace the following (incorrect) line with your code

    //Do appropriate pub and admin checks
    //printf("comparing: %s and %s \n",l1->name,l2->name);
    if(strcmp(l1->name,"pub") == 0 || strcmp(l2->name,"admin") == 0) {
        return true;

    } else if(strcmp(l2->name,"pub") == 0) {

        return !strcmp(l1->name,"pub");

    } else if(strcmp(l1->name,"admin") == 0) {

        return !strcmp(l2->name,"admin");

    } 
    //printf("I think that both of the above were users \n");

    //Should only get here if both l1 and l2 are user types
    return strcmp(l1->name,l2->name) == 0;
}

sec_label *sec_lub(sec_lattice *L, sec_label *l1, sec_label *l2) {
    // should implement the least-upper-bound operation to return
    // the smallest element of L that is at least as large as both
    // l1 and l2
    // replace the following (incorrect) line with your code
    sec_label* tmp_label = NULL;

    if(strcmp(l1->name,"admin") == 0 || strcmp(l2->name,"pub") == 0) {
        return l1;
    }else if(strcmp(l2->name,"admin") == 0 || strcmp(l1->name,"pub") == 0) {
        return l2;
    } else if(strcmp(l1->name,l2->name) == 0) {
        return l1;
    }
    
    tmp_label = fillLabel(L,"admin");

    return tmp_label;
}

sec_label *type_aexp(sec_ctxt *G, sec_lattice *L, aexp *a) {
    // should implement type inference using rules for arithmetic
    // expressions to return a label reflecting the greatest label
    // of information that the given expression could carry under context G
    
    int *ind = malloc(sizeof(int));
    sec_label *l_val;
    sec_label *r_val;
    int index = 0;
    sec_label* label= NULL;

    switch(a->optype) {
        case CONST:
        printf("CONSTANT \n");
            label = fillLabel(L,"pub");
            break;
        case IDENT:
            if(hash_table_find(G->ht,a->value.id,ind)) {
                index = *ind;
                label = (sec_label*)(*ubarray_elem(L->uba,index));
            } else {
                //Case where we haven't declared the variable yet. According to the writeup this should be the user's
                hash_table_insert(G->ht,a->value.id,2);
                return L->user_label;
            }
            break;
        case APAREN:
            label = type_aexp(G,L,a->op1);
            break;
        case PLUS:
        case MINUS:
        case TIMES:
            l_val = type_aexp(G,L,a->op1);
            r_val = type_aexp(G,L,a->op2);
            label = sec_lub(L,l_val,r_val);
            break;
        default:
            label = fillLabel(label,"admin");
    }

    //free(l_val);
    //free(r_val);
    free(ind);
    return label;
}

sec_label *type_bexp(sec_ctxt *G, sec_lattice *L, bexp *b) {
    // should implement type inference using rules for boolean
    // expressions to return a label reflecting the greatest label of
    // information that the given expression could carry under context G
    /*
        struct bexp {
	int optype;			// operation type (CTRUE, CFALSE, NOT, AND, OR, EQ, LEQ, HASDEF)
	union {
		struct aexp *a;	// use when optype is EQ, LEQ, HASDEF
		struct bexp *b; // use when optype is AND, OR, NOT
	} op1;				// first operand
	union {
		struct aexp *a;	// use when optype is EQ, LEQ
		struct bexp *b;	// use when optype is AND, OR
	} op2;				// second operand
};
    */
    int *ind = malloc(sizeof(int));
    sec_label *l_val;
    sec_label *r_val;
    int index = 0;
    sec_label* label= NULL;
    switch(b->optype) {
        case CTRUE:
        case CFALSE:
            label = fillLabel(L,"pub");
            break;
        case HASDEF:
            label = type_aexp(G,L,b->op1.a);
            break;
        case NOT:
        case BPAREN:
            label = type_bexp(G,L,b->op1.b);
            break;
        case AND:
        case OR:
            label = sec_lub(L,type_bexp(G,L,b->op1.b),type_bexp(G,L,b->op2.b));
            break;
        case EQ:
        case LEQ:
            label = sec_lub(L,type_aexp(G,L,b->op1.a),type_aexp(G,L,b->op2.a));
            break;
        default:
            label = fillLabel(L,"admin");
            break;
    }
    return label;    
}

bool typecheck_com(sec_ctxt *G, sec_lattice *L, sec_label *lu, com *c) {
    // should implement type checking for commands to verify that
    // the script will not leak information to label lu in violation
    // of the lattice policy L in type context G

    int index = 0;
    sec_label* alpha = NULL;
    sec_label* tmp = NULL;
    sec_label* var = NULL;
    sec_label* Q = NULL;
    sec_label* cur_user = NULL;
    int* ind = (int*)malloc(sizeof(int));
    bool typechecks = false;

    switch (c->comtype) {
   
    case SKIP:
        typechecks = true;
        break;
    case ASGN:
    printf("ASSGN \n");
        if(hash_table_find(G->ht,c->data.asgn->var,ind)) {
            printf("FOUND IT: %s \n",c->data.asgn->var);
            index = *ind;
            var = (sec_label*)(*ubarray_elem(L->uba,index));
            if(sec_lessthan(L,sec_lub(L,var,G->pc),lu)) {
                typechecks = true;
            } else {
                typechecks =  false;
            }
        } else {
            //Case where we haven't declared the variable yet.  Shouldn't ever happen if we populate context correctly
            //Insert the new variabel for adppending to label
            printf("TO ASSIGN: %s \n",c->data.asgn->var);
            hash_table_insert(G->ht,c->data.asgn->var,2);
            typechecks =  true;
        }
        break;
    case COMP:
        typechecks =  typecheck_com(G,L,lu,c->data.compose->c1) && typecheck_com(G,L,lu,c->data.compose->c2);
        break;
    case COND:
        Q = type_bexp(G,L,c->data.conditional->b);
        tmp = sec_lub(L,Q,G->pc);
        cur_user = G->pc;
        G->pc = tmp;
        typechecks = typecheck_com(G,L,lu,c->data.conditional->c1) && typecheck_com(G,L,lu,c->data.conditional->c2);
        G->pc = cur_user;
        break;
    case WHILE:
        Q = type_bexp(G,L,c->data.whilec->b);
        tmp = sec_lub(L,Q,G->pc);
        cur_user = G->pc;
        G->pc = tmp;
        typechecks = typecheck_com(G,L,lu,c->data.whilec->c);
        G->pc = cur_user;
        break;
    case UNDEF:
        if(hash_table_find(G->ht,c->data.undef->var,ind)) {
            index = *ind;
            var = (sec_label*)(*ubarray_elem(L->uba,index));
            if(sec_lessthan(L,sec_lub(L,var,G->pc),lu)) {
                typechecks = true;
            } else {
                typechecks =  false;
            }
        } else {
            //Case where we haven't declared the variable yet.  Shouldn't ever happen if we populate context correctly
            //Assignment will error so it is allowed
            typechecks =  true;
        }
        break;
    case OUTP:
        printf("OUTPUT \n");
        typechecks = sec_lessthan(L,sec_lub(L,type_aexp(G,L,c->data.output->a),G->pc),lu); 
        break;
    default:
        break;
  }

    free(ind);
    return typechecks;    
}


