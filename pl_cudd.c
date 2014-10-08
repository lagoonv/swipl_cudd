
#include "pl_cudd.h"
#define PTR_SIZE sizeof(DdNode *)
#define CNT_SIZE sizeof(int)
#define BDD_ATOM_PREFIX "$bdd"
#define BDD_PREFIX_LEN 4
#define BUF_SIZE BDD_PREFIX_LEN+PTR_SIZE+CNT_SIZE

static DdManager *mng;

static PL_agc_hook_t old_hook;

static char bdd_atom_string[BUF_SIZE] = BDD_ATOM_PREFIX;

static int uniq_cnt = 0;

static int f_cnt = 0;

//-----------------------------------------------------------------------------
static int atom_finalizer(atom_t bdd)
{
    char *atom_chars = (char *)PL_atom_chars(bdd);
    
    if (!memcmp(atom_chars,BDD_ATOM_PREFIX,BDD_PREFIX_LEN)) {
#ifdef DEBUG_GC
	Sdprintf(".");
#endif
	DdNode *n = *((DdNode **)(atom_chars+BDD_PREFIX_LEN));
	Cudd_RecursiveDeref(mng,n);
	f_cnt--;
    }
    
    if (old_hook) return old_hook(bdd);
    else return TRUE;
}


//=============================================================================
// Wrapping and unwrapping of SWI-Prolog BDDs

inline term_t wrap(DdNode *n)
{
    term_t result = PL_new_term_ref();
    Cudd_Ref(n);		// every node being wrapped is presumed new
    *((DdNode **)(bdd_atom_string+BDD_PREFIX_LEN)) = n;
    *((int *)(bdd_atom_string+BDD_PREFIX_LEN+PTR_SIZE)) = uniq_cnt++;
    PL_put_atom_nchars(result,BUF_SIZE,bdd_atom_string);
    f_cnt++;
    return result;
}

//-----------------------------------------------------------------------------
inline DdNode *unwrap(term_t bdd)
{
    char *atom_chars;
    int _unused = PL_get_atom_chars(bdd,&atom_chars);


    if (memcmp(atom_chars,BDD_ATOM_PREFIX,BDD_PREFIX_LEN)) {

	term_t except = PL_new_term_ref();
	
	int _unused = PL_unify_term(except,
				    PL_FUNCTOR_CHARS, "type_error", 2,
				    PL_CHARS, "bdd",
				    PL_TERM, bdd);
	
	PL_raise_exception(except);
	PL_action(PL_ACTION_ABORT);
    }
    
    return *((DdNode **)(atom_chars+BDD_PREFIX_LEN));
};


//=============================================================================
foreign_t bdd_init()
{
    if(mng) Cudd_Quit(mng);
    mng = Cudd_Init(0,
		    0,
		    CUDD_UNIQUE_SLOTS,
		    CUDD_CACHE_SLOTS,
		    0);
    if (mng) PL_succeed;
    else     PL_fail;
}


foreign_t bdd_quit()
{
    if(mng) Cudd_Quit(mng);
    mng = NULL;
    PL_succeed;
}
//=============================================================================
foreign_t bdd(term_t f)
{
    char *atom_chars;
    if (!PL_is_atom(f)) PL_fail;
    int _unused = PL_get_atom_chars(f,&atom_chars);
    
    if (!memcmp(atom_chars,BDD_ATOM_PREFIX,BDD_PREFIX_LEN))
	PL_succeed;
    else
	PL_fail;
}

//-----------------------------------------------------------------------------
foreign_t bdd_var(term_t f)
{
    return PL_unify(f,wrap(Cudd_bddNewVar(mng)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_var0(term_t f)
{
    return PL_unify(f,wrap(Cudd_bddNewVarAtLevel(mng,0)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_zero(term_t zero)
{
    return PL_unify(zero,wrap(Cudd_ReadLogicZero(mng)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_one(term_t one)
{
    return PL_unify(one,wrap(Cudd_ReadOne(mng)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_and(term_t f1, term_t f2, term_t f3)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    return PL_unify(f3,wrap(Cudd_bddAnd(mng,n1,n2)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_or(term_t f1, term_t f2, term_t f3)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    return PL_unify(f3,wrap(Cudd_bddOr(mng,n1,n2)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_xor(term_t f1, term_t f2, term_t f3)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    return PL_unify(f3,wrap(Cudd_bddXor(mng,n1,n2)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_not(term_t f, term_t not_f)
{
    DdNode *n = unwrap(f);
    return PL_unify(not_f,wrap(Cudd_Not(n)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_ite(term_t f1, term_t f2, term_t f3, term_t f4)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    DdNode *n3 = unwrap(f3);
    return PL_unify(f4,wrap(Cudd_bddIte(mng,n1,n2,n3)));
}

//-----------------------------------------------------------------------------
foreign_t bdd_iff(term_t f1, term_t f2, term_t f3)
{
    foreign_t succ;
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    DdNode *not_n2 = Cudd_Not(n2);
    Cudd_Ref(not_n2);
    succ = PL_unify(f3,wrap(Cudd_bddIte(mng,n1,n2,not_n2)));
    Cudd_RecursiveDeref(mng,not_n2);
    return succ;
}

//-----------------------------------------------------------------------------
foreign_t bdd_cube(term_t l, term_t cube)
{
    term_t head = PL_new_term_ref();      /* variable for the elements */
    term_t list = PL_copy_term_ref(l);    /* copy as we need to write */

    foreign_t status;
    
    DdNode *cb = Cudd_ReadOne(mng); Cudd_Ref(cb);
    while( PL_get_list(list, head, list) ) {
	DdNode *tmp =
	    Cudd_bddAnd(mng,
			cb,
			Cudd_bddIthVar(mng,
				       Cudd_NodeReadIndex(unwrap(head))));
	Cudd_Ref(tmp);
	Cudd_RecursiveDeref(mng,cb);
	cb = tmp;
    }

    if (PL_get_nil(list)) {	/* must be a proper list */
	status = PL_unify(cube,wrap(cb));
	Cudd_RecursiveDeref(mng,cb);
	return status;
    }
    else PL_fail;
}

foreign_t bdd_and_abstract(term_t cube, term_t f, term_t g, term_t res)
{
    DdNode *cube_dd = unwrap(cube);
    DdNode *f_dd = unwrap(f);
    DdNode *g_dd = unwrap(g);
    return PL_unify(res,wrap(Cudd_bddAndAbstract(mng,f_dd,g_dd,cube_dd)));
}

foreign_t bdd_exist(term_t cube, term_t f, term_t res)
{
    DdNode *cube_dd = unwrap(cube);
    DdNode *f_dd = unwrap(f);
    return PL_unify(res,wrap(Cudd_bddExistAbstract(mng,f_dd,cube_dd)));    
}

foreign_t bdd_forall(term_t cube, term_t f, term_t res)
{
    DdNode *cube_dd = unwrap(cube);
    DdNode *f_dd = unwrap(f);
    return PL_unify(res,wrap(Cudd_bddUnivAbstract(mng,f_dd,cube_dd)));    
}

//-----------------------------------------------------------------------------
foreign_t bdd_constrain(term_t f1, term_t f2, term_t f3)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    return PL_unify(f3,wrap(Cudd_bddConstrain(mng,n1,n2)));
}


foreign_t bdd_restrict(term_t f1, term_t f2, term_t f3)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    return PL_unify(f3,wrap(Cudd_bddRestrict(mng,n1,n2)));
}

foreign_t bdd_cofactor(term_t f1, term_t f2, term_t f3)
{
    DdNode *n1 = unwrap(f1);
    DdNode *n2 = unwrap(f2);
    return PL_unify(f3,wrap(Cudd_Cofactor(mng,n1,n2)));
}


//-----------------------------------------------------------------------------
foreign_t bdd_rename(term_t f1, term_t l1, term_t l2, term_t f2)
{
    term_t head1 = PL_new_term_ref();      /* variable for the elements */
    term_t list1 = PL_copy_term_ref(l1);    /* copy as we need to write */
    term_t head2 = PL_new_term_ref();      /* variable for the elements */
    term_t list2 = PL_copy_term_ref(l2);    /* copy as we need to write */
    int sz = Cudd_ReadSize(mng);
    foreign_t status;
    int i;

    int *perm = (int *)malloc(sz*sizeof(int)); assert(perm);
    for (i=0; i<sz; i++) perm[i]=i;
    
    while( PL_get_list(list1, head1, list1) &&
	   PL_get_list(list2, head2, list2) ) {
	
	int n1_id = Cudd_NodeReadIndex(unwrap(head1));
	int n2_id = Cudd_NodeReadIndex(unwrap(head2));
	perm[n1_id] = n2_id;
    }

    if (PL_get_nil(list1) && PL_get_nil(list2))  /* must be proper lists
						    of the same length */
	status = PL_unify(f2,wrap(Cudd_bddPermute(mng,unwrap(f1),perm)));
    else
	status = FALSE;
    free(perm);
    return status;
}

//-----------------------------------------------------------------------------
foreign_t bdd_is_zero(term_t t)
{
    if (unwrap(t) == Cudd_ReadLogicZero(mng)) PL_succeed;
    else PL_fail;
}

//-----------------------------------------------------------------------------
foreign_t bdd_is_one(term_t t)
{
    if (unwrap(t) == Cudd_ReadOne(mng)) PL_succeed;
    else PL_fail;
}


//-----------------------------------------------------------------------------
foreign_t bdd_eq(term_t t1, term_t t2)
{
    if (unwrap(t1) == unwrap(t2)) PL_succeed;
    else PL_fail;
}

//-----------------------------------------------------------------------------
foreign_t bdd_le(term_t t1, term_t t2)
{
    if (Cudd_bddLeq(mng,unwrap(t1),unwrap(t2))) PL_succeed;
    else PL_fail;
}


//-----------------------------------------------------------------------------
foreign_t bdd_print(term_t t)
{
    Cudd_PrintMinterm(mng,unwrap(t));
}


//=============================================================================
foreign_t bdd_count_paths(term_t f, term_t paths)
{
    DdNode *n = unwrap(f);
    term_t cnt = PL_new_term_ref();
    int _unused = PL_put_float(cnt,Cudd_CountPath(n));
    return PL_unify(paths,cnt);
}
//=============================================================================
foreign_t bdd_count_paths_to_zero(term_t f, term_t paths)
{
    DdNode *n = unwrap(f);
    term_t cnt = PL_new_term_ref();
    int _unused = PL_put_float(cnt,Cudd_CountPath(n) -
			       Cudd_CountPathsToNonZero(n));
    return PL_unify(paths,cnt);
}

//Cudd_CountPathsToNonZero
//=============================================================================
foreign_t bdd_count_paths_to_one(term_t f, term_t paths)
{
    DdNode *n = unwrap(f);
    term_t cnt = PL_new_term_ref();
    int _unused = PL_put_float(cnt,Cudd_CountPathsToNonZero(n));
    return PL_unify(paths,cnt);
}

//=============================================================================
foreign_t bdd_count_nodes(term_t f, term_t nodes)
{
    DdNode *n = unwrap(f);
    term_t cnt = PL_new_term_ref();
    int _unused = PL_put_integer(cnt,Cudd_DagSize(n));
    return PL_unify(nodes,cnt);
}



//=============================================================================
foreign_t bdd_gc_internal()
{
    cuddGarbageCollect(mng,1);
    Cudd_ReduceHeap(mng,CUDD_REORDER_SIFT_CONVERGE,0);
    PL_succeed;
}

foreign_t bdd_enable_reordering(term_t method)
{
    int m;
    int _unused = PL_get_integer(method,&m);
    Cudd_AutodynEnable(mng,m);
    PL_succeed;
}

foreign_t bdd_disable_reordering()
{
    Cudd_AutodynDisable(mng);
    PL_succeed;
}

//-----------------------------------------------------------------------------
foreign_t bdd_id(term_t f,term_t id)
{    
    DdNode *n = unwrap(f);
    term_t res = PL_new_term_ref();
    int _unused = PL_put_integer(res,Cudd_NodeReadIndex(n));
    return PL_unify(id,res);
}

foreign_t bdd_ptr(term_t f,term_t ptr)
{    
    DdNode *n = unwrap(f);
    term_t res = PL_new_term_ref();
    int _unused = PL_put_integer(res,(unsigned int)n);
    return PL_unify(ptr,res);
}

foreign_t bdd_level(term_t f,term_t level)
{    
    DdNode *n = unwrap(f);
    term_t res = PL_new_term_ref();
    int _unused = PL_put_integer(res,
				 Cudd_ReadPerm(mng,Cudd_NodeReadIndex(n)));
    return PL_unify(level,res);
}


foreign_t bdd_if(term_t f, term_t top)
{            
    DdNode *one = Cudd_ReadOne(mng);
    DdNode *zero = Cudd_ReadLogicZero(mng);
    DdNode *n = unwrap(f);
    DdNode *res;
    
    if (n == one) res=one;
    else if (n == zero) res=zero;
    else res = Cudd_ReadVars(mng,Cudd_NodeReadIndex(n));
    return PL_unify(top,wrap(res));    
}

foreign_t bdd_then(term_t f, term_t then)
{
    DdNode *n = unwrap(f);
    DdNode *t = Cudd_T(n);
    return PL_unify(then,wrap((Cudd_IsComplement(n)) ? Cudd_Not(t) : t));
}

foreign_t bdd_else(term_t f, term_t els)
{
    DdNode *n = unwrap(f);
    DdNode *e = Cudd_E(n);
    return PL_unify(els,wrap((Cudd_IsComplement(n)) ? Cudd_Not(e) : e));
}

foreign_t bdd_essential(term_t f, term_t ess)
{
    DdNode *n = unwrap(f);
    return PL_unify(ess,wrap(Cudd_FindEssential(mng,n)));
}

//=============================================================================
typedef struct                  /* define a context structure */
{
    DdGen *gen;
    int *cube;
} context;

foreign_t bdd_satisfy(term_t f, term_t sol, control_t handle)
{
    context *ctxt;
    CUDD_VALUE_TYPE unused;
    
    switch( PL_foreign_control(handle) ) {
    case PL_FIRST_CALL:
	ctxt = malloc(sizeof(context)); assert(ctxt);
	ctxt->gen = Cudd_FirstCube(mng,unwrap(f),&(ctxt->cube),&unused);
	break;
    case PL_REDO:
	ctxt = PL_foreign_context_address(handle);
	break;
    case PL_CUTTED:
	ctxt = PL_foreign_context_address(handle);
	Cudd_GenFree(ctxt->gen);
	free(ctxt);
	PL_succeed;
    }

    // common code for PL_FIRST_CALL and PL_REDO
    if (!Cudd_IsGenEmpty(ctxt->gen)
	&& PL_unify(sol,wrap(Cudd_CubeArrayToBdd(mng,ctxt->cube)))) {
	Cudd_NextCube(ctxt->gen,&(ctxt->cube),&unused);
	PL_retry_address(ctxt);
    }
    else {
	Cudd_GenFree(ctxt->gen);
	free(ctxt);
	PL_fail;
    }
}

//=============================================================================
// bdd_mem(-VarsInUse, -BDDsInUse, -NodesInUse, -PeakNodes, -MemInUse)
foreign_t bdd_mem(term_t vs, term_t fs, term_t ns, term_t pk, term_t mem)
{
    term_t vs_cnt = PL_new_term_ref();
    term_t fs_cnt = PL_new_term_ref();
    term_t ns_cnt = PL_new_term_ref();
    term_t pk_cnt = PL_new_term_ref();
    term_t mem_cnt = PL_new_term_ref();
    int _unused;
    _unused = PL_put_integer(mem_cnt,Cudd_ReadMemoryInUse(mng));
    _unused = PL_put_integer(vs_cnt,Cudd_ReadSize(mng));
    _unused = PL_put_integer(ns_cnt,Cudd_ReadNodeCount(mng));
    _unused = PL_put_integer(pk_cnt,Cudd_ReadPeakNodeCount(mng));
    _unused = PL_put_integer(fs_cnt,f_cnt);
    return (PL_unify(vs,vs_cnt) &&
	    PL_unify(ns,ns_cnt) &&
	    PL_unify(pk,pk_cnt) &&
	    PL_unify(fs,fs_cnt) &&
	    PL_unify(mem,mem_cnt));
}

//=============================================================================

foreign_t bdd_dump_dot(term_t fname, term_t f)
{
    char *name;
    //char *dotname = "wakeup";
    if (PL_get_file_name(fname,&name,PL_FILE_ABSOLUTE)) {
	FILE *file = fopen(name,"w");
	DdNode *n = unwrap(f);
	assert(f);
	Cudd_DumpDot(mng,1,&n,NULL,NULL,//&dotname,
		     file);
	fclose(file);
	PL_succeed;
    }
    else PL_fail;
}
		       
//=============================================================================
static const PL_extension predicates[] =
    {
        //
        //  { "name", arity, function, PL_FA_<flags> },
        //

        { "bdd",              1, bdd,              0 },
        { "bdd_init",         0, bdd_init,         0 },
        { "bdd_quit",         0, bdd_quit,         0 },
        { "bdd_var",          1, bdd_var,          0 },
        { "bdd_var0",         1, bdd_var0,         0 },
	{ "bdd_zero",         1, bdd_zero,         0 },
	{ "bdd_one",          1, bdd_one,          0 },
	{ "bdd_and",          3, bdd_and,          0 },
	{ "bdd_or",           3, bdd_or,           0 },
	{ "bdd_xor",          3, bdd_xor,          0 },
	{ "bdd_not",          2, bdd_not,          0 },
	{ "bdd_ite",          4, bdd_ite,          0 },
	{ "bdd_iff",          3, bdd_iff,          0 },
	{ "bdd_constrain",    3, bdd_constrain,    0 },
	{ "bdd_restrict",     3, bdd_restrict,     0 },
	{ "bdd_cofactor",     3, bdd_cofactor,     0 },
	{ "bdd_is_zero",      1, bdd_is_zero,      0 },
	{ "bdd_is_one",       1, bdd_is_one,       0 },
	{ "bdd_eq",           2, bdd_eq,           0 },
	{ "bdd_le",           2, bdd_le,           0 },
			             	   	   
	{ "bdd_cube",         2, bdd_cube,         0 },
	{ "bdd_forall",       3, bdd_forall,       0 },
	{ "bdd_exist",        3, bdd_exist,        0 },

	{ "bdd_and_abstract", 4, bdd_and_abstract, 0 },
	
	{ "bdd_satisfy",      2, bdd_satisfy,      PL_FA_NONDETERMINISTIC },
			      
	{ "bdd_count_paths",          2, bdd_count_paths,  0 },
	{ "bdd_count_paths_to_zero",  2, bdd_count_paths_to_zero,  0 },
	{ "bdd_count_paths_to_one",   2, bdd_count_paths_to_one,  0 },
	{ "bdd_count_nodes",          2, bdd_count_nodes,  0 },

	{ "bdd_id",           2, bdd_id,           0 },
	{ "bdd_level",        2, bdd_level,        0 },
	{ "bdd_ptr",          2, bdd_ptr,          0 },
	{ "bdd_if",           2, bdd_if,           0 },
	{ "bdd_then",         2, bdd_then,         0 },
	{ "bdd_else",         2, bdd_else,         0 },
	{ "bdd_rename",       4, bdd_rename,       0 },
	{ "bdd_essential",    2, bdd_essential,    0 },

	{ "bdd_print",        1, bdd_print,        0 },
	{ "bdd_dump_dot",     2, bdd_dump_dot,     0 },

	{ "bdd_mem",          5, bdd_mem,          0 },
	{ "bdd_gc_internal",  0, bdd_gc_internal,  0 },

	{ "bdd_enable_reordering",  1, bdd_enable_reordering,  0 },
	{ "bdd_disable_reordering", 0, bdd_disable_reordering, 0 },
	
	
        { NULL,               0, NULL,             0 }    // terminating line
    };

//-----------------------------------------------------------------------------
install_t install()
{
#ifndef NDEBUG
    Sdprintf("%%  CUDD library API, build of "
	     __DATE__", "__TIME__"\n");
#endif
    PL_license("lgpl","pl_cudd: PL interface to CUDD (http://vlsi.colorado.edu/~fabio/CUDD/)");
    mng = Cudd_Init(0,
		    0,
		    CUDD_UNIQUE_SLOTS,
		    CUDD_CACHE_SLOTS,
		    0);
    
    PL_register_extensions(predicates);
    old_hook = PL_agc_hook(atom_finalizer); /* install new atom hook */
}

