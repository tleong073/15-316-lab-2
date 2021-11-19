#include "tinyscript/sectypes.h"
#include <stdbool.h>
#include <stdlib.h>


sec_label* fillLabel(sec_lattice *L,char* ident) {
    sec_label* tmp = NULL;
     for(size_t i = 0; i < ubarray_size(L->uba);i++) {
        tmp = (sec_label*)(*(ubarray_elem(L->uba, i)));
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
    sec_label *l_val =malloc(sizeof(sec_label));
    sec_label *r_val =malloc(sizeof(sec_label));
    int index = 0;
    sec_label* label= NULL;

    switch(a->optype) {
        case CONST:
            label = fillLabel(L,"pub");
            break;
        case IDENT:
            if(hash_table_find(G->ht,a->value.id,ind)) {
                index = *ind;
                label = (sec_label*)(*ubarray_elem(L->uba,index));
            } else {
                //Case where we haven't declared variable yet. Should never get here
                return fillLabel(L,"admin");
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
    //free(ind);
    return label;
}

sec_label *type_bexp(sec_ctxt *G, sec_lattice *L, bexp *b) {
    // should implement type inference using rules for boolean
    // expressions to return a label reflecting the greatest label of
    // information that the given expression could carry under context G

    // replace the following (incorrect) line with your code
    return (sec_label *)NULL;    
}

bool typecheck_com(sec_ctxt *G, sec_lattice *L, sec_label *lu, com *c) {
    // should implement type checking for commands to verify that
    // the script will not leak information to label lu in violation
    // of the lattice policy L in type context G

    // replace the following (incorrect) line with your code
    return false;    
}


