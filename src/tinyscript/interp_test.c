#include "tinyscript/sectypes.h"
#include <assert.h>
#include "tinyscript/ast.h"

sec_label * make_label(char* ident) {
    sec_label* tmp =  malloc(sizeof(sec_label));
    tmp->name = ident;
    return tmp;
}

int main (int argc , char * argv []) {
    ubarray * uba = ubarray_new(3) ;
    hash_table_t * state = hash_table_new();

    // create a minimal set of users
    // you need to provide a make_label helper
    sec_label* pub = make_label("pub");
    sec_label* admin = make_label("admin");
    sec_label* user = make_label("user");
    sec_label* user2 = make_label("user2");

    ubarray_push_back ( uba, pub );
    ubarray_push_back ( uba, admin );
    ubarray_push_back ( uba, user);
    ubarray_push_back ( uba, user2);

    //printf("String: %x %x \n", *((sec_label*)ubarray_elem(uba,0)),pub);
    // populate the context with a single variable owned by " user "
    //aexp * var_x = new_ident (( char *)"x") ;
    

    //printf("sanity check 1 \n");

    // construct a lattice and security context
    sec_lattice* L = malloc(sizeof(sec_lattice));
    L->user_label = user;
    L->uba = uba;
    sec_ctxt* G = malloc(sizeof(sec_ctxt));
    G->pc = user;
    G->ht = state;

    //printf("sanity check 2 \n");

    // test type_aexp
    //sec_label * l_infer = type_aexp (G , L , var_x ) ;
    //assert (! strcmp ( l_infer->name , user->name ) ) ;
    /*
        LESSTHAN tests
    */

    bool lt_admin_admin = sec_lessthan(L,admin,admin);
    bool lt_pub_pub = sec_lessthan(L,pub,pub);
    bool lt_user_user = sec_lessthan(L,user,user);

    bool lt_pub_admin = sec_lessthan(L,pub,admin);
    bool lt_admin_pub = sec_lessthan(L,admin,pub);

    bool lt_user_pub = sec_lessthan(L,user,pub);
    bool lt_pub_user = sec_lessthan(L,pub,user);

    bool lt_user_admin= sec_lessthan(L,user,admin);
    bool lt_admin_user = sec_lessthan(L,admin,user);

    bool lt_user1_user2 = sec_lessthan(L,user,user2);


    //pub-admin tests
    assert(lt_pub_admin);
    assert(!lt_admin_pub);
    assert(lt_admin_admin);
    assert(lt_pub_pub);
    assert(lt_user_user);

    //user-pub tests
    assert(!lt_user_pub);
    assert(lt_pub_user);

    //user-admin tests
    assert(lt_user_admin);
    assert(!lt_admin_user);

    //user-user test
    assert(!lt_user1_user2);
    /*
        Least Upper bound tests
    */

    sec_label* lub_pub_admin = sec_lub(L,pub,admin);
    sec_label* lub_admin_pub = sec_lub(L,admin,pub);

    sec_label* lub_admin_user = sec_lub(L,admin,user);
    sec_label* lub_user_admin = sec_lub(L,user,admin);

    sec_label* lub_pub_user = sec_lub(L,pub,user);
    sec_label* lub_user_pub = sec_lub(L,user,pub);

    sec_label* lub_user_user = sec_lub(L,user,user);
    sec_label* lub_user_user2 = sec_lub(L,user,user2);




    //admin tests
    assert(strcmp(lub_pub_admin->name,"admin") == 0);
    assert(strcmp(lub_admin_pub->name,"admin") == 0);
    assert(strcmp(lub_admin_user->name,"admin") == 0);
    assert(strcmp(lub_user_admin->name,"admin") == 0);
    printf("sanity check1 \n");

    //pub tests
    assert(strcmp(lub_pub_user->name,"user") == 0);
    assert(strcmp(lub_user_pub->name,"user") == 0);
    printf("sanity check 2\n");

    //user-user tests
    assert(strcmp(lub_user_user->name,"user") == 0);
    assert(strcmp(lub_user_user2->name,"admin") == 0);

    // --------------------------------------------------------------------------------------

    // a-expression tests
    /*
        aexp *new_const(int val);
        aexp *new_ident(char *id);
        aexp *new_plus(aexp *op1, aexp *op2);
        aexp *new_minus(aexp *op1, aexp *op2);
        aexp *new_times(aexp *op1, aexp *op2);
        aexp *new_aparen(aexp *op);
    */


    aexp * constant1 = new_const (5);
    aexp * constant2 = new_const (6);

    aexp * var_x = new_ident((char*)"x1");
    aexp * var_y = new_ident((char*)"x2");

    hash_table_insert (state, var_x->value.id, 2); // 2 is the index of " user " in uba
    hash_table_insert (state, var_y->value.id, 3) ;

    aexp * plus_const_const = new_plus(constant1,constant2);
    aexp * plus_const_user = new_plus(constant1,var_x);
    aexp * plus_user_user = new_plus(var_x,var_x);
    aexp * plus_user_user2 = new_plus(var_x,var_y);

    aexp * paren_plus =  new_aparen(plus_const_const);

    sec_label* a_const = type_aexp(G,L,constant1);
    sec_label* a_var = type_aexp(G,L,var_x);
    sec_label* a_const_const = type_aexp(G,L,plus_const_const);
    sec_label* a_const_user = type_aexp(G,L,plus_const_user);
    sec_label* a_user_user = type_aexp(G,L,plus_user_user);
    sec_label* a_user_user2 = type_aexp(G,L,plus_user_user2);
    sec_label* a_paren_plus = type_aexp(G,L,paren_plus);
    

    //Constant
    assert(strcmp(a_const->name,"pub") == 0);
    //Variables
    assert(strcmp(a_var->name,"user") == 0);
    //BinOps
    assert(strcmp(a_const_const->name,"pub") == 0);
    assert(strcmp(a_const_user->name,"user") == 0);
    assert(strcmp(a_user_user->name,"user") == 0);
    assert(strcmp(a_user_user2->name,"admin") == 0);
    assert(strcmp(a_paren_plus->name,"pub") == 0);

// --------------------------------------------------------------------------------------

    // b-expression tests

    

}