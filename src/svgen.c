#include "phase.h"
#include "util.h"
#include "hash.h"
#include "common.h"
#include "rt/netdb.h"

#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdlib.h>

typedef tree_t (*get_fn_t)(tree_t, unsigned);

//static void dump_op(FILE* fh, tree_t t);
static void dump_expr(FILE* fh, tree_t t);
static void dump_stmt(FILE* fh, tree_t t);
static void dump_port(FILE* fh, tree_t t);
//static void dump_ports(FILE* fh, tree_t t);
//static void dump_type(FILE* fh, type_t t);
static void dump_decl(FILE* fh, tree_t t);
static void dump_decls(FILE* fh, tree_t t);
//static void dump_block(FILE* fh, tree_t t);
//static void dump_params(FILE* fh, tree_t t, get_fn_t get, int n, const char *prefix);

#define TAB_SIZE (4)
static int g_tab;
static int g_comb;

static void dump_tab(FILE* fh)
{
    int indent = g_tab * TAB_SIZE;
    while (indent--) fputc(' ', fh);
}

static void dump_params(FILE* fh, tree_t t, get_fn_t get, int n, const char *prefix)
{
    if (n > 0)
    {
        if (prefix != NULL)
        {
            fprintf(fh, prefix, "");
            fprintf(fh, " ");
        }
        fprintf(fh, " (");
        for (int i = 0; i < n; i++)
        {
            if (i > 0) fprintf(fh, ", ");
            tree_t p = (*get)(t, i);
            switch (tree_subkind(p))
            {
                case P_POS:
                    break;
                case P_NAMED:
                    dump_expr(fh, tree_name(p));
                    fprintf(fh, " => ");
                    break;
            }
            dump_expr(fh, tree_value(p));
        }
        fprintf(fh, ")");
    }
}

static void dump_range(FILE* fh, range_t r)
{
    dump_expr(fh, r.left);
    switch (r.kind)
    {
        case RANGE_TO:     fprintf(fh, ":");                break;
        case RANGE_DOWNTO: fprintf(fh, ":");                break;
        case RANGE_DYN:    fprintf(fh, " #dynamic ");         break;
        case RANGE_RDYN:   fprintf(fh, " #reverse_dynamic "); break;
        case RANGE_EXPR:   fprintf(fh, " #expr ");            break;
    }
    dump_expr(fh, r.right);
}

static void dump_expr(FILE* fh, tree_t t)
{
    switch (tree_kind(t))
    {
        // i.e : operator, function
        case T_FCALL:
        {
            const char *func = istr(tree_ident(tree_ref(t)));
            const char *op = strstr(func, "\"");
            size_t i;
            
            if (op)
            {
                // operator
                static const char *vhd_op[] =
                {
                    "\"**\"",
                    "\"*\"",
                    "\"/\"",
                    "\"mod\"",
                    "\"rem\"",
                    "\"+\"",
                    "\"-\"",
                    "\"&\"",
                    "\"sll\"",
                    "\"srl\"",
                    "\"sla\"",
                    "\"sra\"",
                    "\"rol\"",
                    "\"ror\"",
                    "\"and\"",
                    "\"or\"",
                    "\"xor\"",
                    "\"nand\"",
                    "\"nor\"",
                    "\"xnor\"",
                    "\"not\"",
                    "\"=\"",
                    "\"/=\"",
                    "\"<\"",
                    "\"<=\"",
                    "\">\"",
                    "\">=\""
                };
                static const char *sv_op[] =
                {
                    "**",
                    " * ",
                    " / ",
                    " % ",
                    " % ",
                    " + ",
                    " - ",
                    "\"&\"",
                    " << ",
                    " >> ",
                    " <<< ",
                    " >>> ",
                    "\"rol\"",
                    "\"ror\"",
                    " & ",
                    " | ",
                    " ^ ",
                    " ~& ",
                    " ~| ",
                    " ~^ ",
                    " ~",
                    " == ",
                    " != ",
                    " < ",
                    " <= ",
                    " > ",
                    " >= "
                };
                
                for (i = 0; i < ARRAY_LEN(vhd_op); i++)
                {
                    if (strcmp(op, vhd_op[i]) == 0)
                    {
                        op = sv_op[i];
                        break;
                    }
                }
                
                int n = tree_params(t);
                // unary operators
                if (n == 1)
                {
                    tree_t p = tree_param(t, 0);
                    fprintf(fh, "%s(", op);
                    dump_expr(fh, tree_value(p));
                    fprintf(fh, ")");
                }
                // operators
                else if (n == 2)
                {
                    tree_t p;
                    fprintf(fh, "(");
                    p = tree_param(t, 0);
                    dump_expr(fh, tree_value(p));
                    fprintf(fh, "%s", op);
                    p = tree_param(t, 1);
                    dump_expr(fh, tree_value(p));
                    fprintf(fh, ")");
                }
                // ???
                else
                {
                    fprintf(fh, "op ??? %s", op);
                    dump_params(fh, t, tree_param, tree_params(t), NULL);
                }
            }
            else
            {
                // function call
                static const char *vhd_fn[] =
                {
                    "IEEE.STD_LOGIC_1164.RISING_EDGE",
                    "IEEE.STD_LOGIC_1164.FALLING_EDGE",
                    "IEEE.STD_LOGIC_1164.STD_LOGIC_VECTOR",
                    "IEEE.STD_LOGIC_UNSIGNED.CONV_INTEGER",
                    "IEEE.NUMERIC_STD.TO_INTEGER",
                    "IEEE.NUMERIC_STD.UNSIGNED"
                };
                static const char *sv_fn[] =
                {
                    "posedge",
                    "negedge",
                    "std_logic_vector",
                    "conv_integer",
                    "to_integer",
                    "unsigned"
                };
                for (i = 0; i < ARRAY_LEN(vhd_fn); i++)
                {
                    if (strcmp(func, vhd_fn[i]) == 0)
                    {
                        op = sv_fn[i];
                        break;
                    }
                }
                if (op)
                {
                    if (i < 2)
                    {
                        fprintf(fh, "1'b1 /* @ %s", op);
                        dump_params(fh, t, tree_param, tree_params(t), NULL);
                        fprintf(fh, "*/");
                    }
                    else
                    {
                        fprintf(fh, "/* %s */", op);
                        dump_params(fh, t, tree_param, tree_params(t), NULL);
                    }
                }
                else
                {
                    fprintf(fh, "%s", func);
                    dump_params(fh, t, tree_param, tree_params(t), NULL);
                }
            }
            break;
        }
        
        case T_LITERAL:
        {
            switch (tree_subkind(t))
            {
                // i.e : bit number, vector range
                case L_INT:
                {
                    fprintf(fh, "%"PRIi64, tree_ival(t));
                    break;
                }
                case L_REAL:
                {
                    fprintf(fh, "r%lf", tree_dval(t));
                    break;
                }
                case L_NULL:
                {
                    fprintf(fh, "#null");
                    break;
                }
                // i.e : vector value
                case L_STRING:
                {
                    const int nchars = tree_chars(t);
                    fprintf(fh, "%d'b", nchars);
                    for (int i = 0; i < nchars; i++)
                    {
                        fprintf(fh, "%c", ident_char(tree_ident(tree_char(t, i)), 1));
                    }
                    break;
                }
                default:
                {
                    assert(false);
                }
            }
            break;
        }
        
        case T_NEW:
        {
            fprintf(fh, "new ");
            dump_expr(fh, tree_value(t));
            break;
        }
        
        case T_ALL:
        {
            dump_expr(fh, tree_value(t));
            fprintf(fh, ".all");
            break;
        }
        
        case T_AGGREGATE:
        {
            fprintf(fh, "(");
            for (unsigned i = 0; i < tree_assocs(t); i++)
            {
                if (i > 0) fprintf(fh, ", ");
                tree_t a = tree_assoc(t, i);
                tree_t value = tree_value(a);
                switch (tree_subkind(a))
                {
                    case A_POS:
                    {
                        dump_expr(fh, value);
                        break;
                    }
                    case A_NAMED:
                    {
                        dump_expr(fh, tree_name(a));
                        fprintf(fh, " => ");
                        dump_expr(fh, value);
                        break;
                    }
                    case A_OTHERS:
                    {
                        if ((tree_kind(value) == T_REF) && tree_has_ref(value))
                        {
                            const char *ref = istr(tree_ident(tree_ref(value)));
                            
                            if (strcmp(ref,"'0'") == 0)
                            {
                                fprintf (fh, "-'b0");
                            }
                            else if (strcmp(ref,"'1'") == 0)
                            {
                                fprintf (fh, "-'b1");
                            }
                            else if (strcmp(ref,"'Z'") == 0)
                            {
                                fprintf (fh, "-'bZ");
                            }
                            else if (strcmp(ref,"'U'") == 0)
                            {
                                fprintf (fh, "-'bX");
                            }
                            else
                            {
                                fprintf(fh, "others => %s", ref);
                            }
                        }
                        else
                        {
                            fprintf(fh, "others => ");
                            dump_expr(fh, value);
                        }
                        break;
                    }
                    case A_RANGE:
                    {
                        dump_range(fh, tree_range(a, 0));
                        fprintf(fh, " => ");
                        dump_expr(fh, value);
                        break;
                    }
                    default:
                    {
                        assert(false);
                    }
                }
            }
            fprintf(fh, ")");
            break;
        }
        
        case T_REF:
        {
            const char *ref;
            
            if (tree_has_ref(t))
                // i.e : signal, bit value
                ref = istr(tree_ident(tree_ref(t)));
            else
                ref = istr(tree_ident(t));
            
            if ((strcmp(ref,"'0'") == 0) || (strcmp(ref,"FALSE") == 0))
            {
                fprintf (fh, "1'b0");
            }
            else if ((strcmp(ref,"'1'") == 0) || (strcmp(ref,"TRUE") == 0))
            {
                fprintf (fh, "1'b1");
            }
            else if (strcmp(ref,"'Z'") == 0)
            {
                fprintf (fh, "1'bZ");
            }
            else if (strcmp(ref,"'U'") == 0)
            {
                fprintf (fh, "1'bX");
            }
            else
            {
                fprintf(fh, "%s", ref);
            }
            break;
        }
        
        case T_ATTR_REF:
        {
            dump_expr(fh, tree_name(t));
            fprintf(fh, "'%s", istr(tree_ident(t)));
            break;
        }
        
        // i.e vector bit
        case T_ARRAY_REF:
        {
            int n = tree_params(t);
            
            dump_expr(fh, tree_value(t));
            if (n == 1)
            {
                tree_t p = tree_param(t, 0);
                fprintf(fh, "[");
                dump_expr(fh, tree_value(p));
                fprintf(fh, "]");
            }
            else
            {
                dump_params(fh, t, tree_param, n, NULL);
            }
            break;
        }
        
        // i.e vector range
        case T_ARRAY_SLICE:
        {
            dump_expr(fh, tree_value(t));
            fprintf(fh, "[");
            dump_range(fh, tree_range(t, 0));
            fprintf(fh, "]");
            break;
        }
        
        case T_RECORD_REF:
        {
            dump_expr(fh, tree_value(t));
            fprintf(fh, ".%s", istr(tree_ident(t)));
            break;
        }
        
        case T_TYPE_CONV:
        {
            fprintf(fh, "%s(", istr(tree_ident(tree_ref(t))));
            dump_expr(fh, tree_value(tree_param(t, 0)));
            fprintf(fh, ")");
            break;
        }
        
        case T_CONCAT:
        {
            const int nparams = tree_params(t);
            fprintf(fh, "{ ");
            for (int i = 0; i < nparams; i++)
            {
                if (i > 0) fprintf(fh, ", ");
                dump_expr(fh, tree_value(tree_param(t, i)));
            }
            fprintf(fh, " }");
            break;
        }
        
        case T_QUALIFIED:
        {
            fprintf(fh, "%s'(", istr(type_ident(tree_type(t))));
            dump_expr(fh, tree_value(t));
            fprintf(fh, ")");
            break;
        }
        
        case T_OPEN:
        {
            // Not connected pin
            fprintf(fh, "/* open */");
            break;
        }
        
        default:
        {
            //cannot_dump(t, "expr");
        }
    }
    fflush(fh);
}

static const char *dump_minify_type(const char *name)
{
    static const char *vhd_known[] =
    {
        "STD.STANDARD.BIT",
        "STD.STANDARD.BIT_VECTOR",
        "STD.STANDARD.BOOLEAN",
        "STD.STANDARD.CHARACTER",
        "STD.STANDARD.INTEGER",
        "STD.STANDARD.NATURAL",
        "STD.STANDARD.POSITIVE",
        "STD.STANDARD.STRING",
        "IEEE.NUMERIC_STD.SIGNED",
        "IEEE.NUMERIC_STD.UNSIGNED",
        "IEEE.STD_LOGIC_1164.STD_LOGIC",
        "IEEE.STD_LOGIC_1164.STD_LOGIC_VECTOR",
        "IEEE.STD_LOGIC_1164.STD_ULOGIC",
        "IEEE.STD_LOGIC_1164.STD_ULOGIC_VECTOR"
    };
    
    static const char *sv_known[] =
    {
        "bit           %s",
        "bit           %s",
        "bit           %s",
        "byte unsigned %s",
        "int           %s",
        "int unsigned  %s",
        "int unsigned  %s",
        "string        %s",
        "logic signed  %s",
        "logic         %s",
        "logic         %s",
        "logic         %s",
        "logic         %s",
        "logic         %s"
    };
    
    for (size_t i = 0; i < ARRAY_LEN(vhd_known); i++)
    {
        const size_t len = strlen(vhd_known[i]);
        if (strncmp(name, vhd_known[i], len) == 0)
        {
            return sv_known[i];
        }
    }
    
    return name;
}

static void dump_type(FILE* fh, type_t type)
{
    if (type_kind(type) == T_SUBTYPE && type_has_ident(type))
    {
        fprintf(fh, type_pp_minify(type, dump_minify_type), " ");
    }
    else if (type_is_array(type) && !type_is_unconstrained(type))
    {
        fprintf(fh, type_pp_minify(type, dump_minify_type), " [");
        const int ndims = array_dimension(type);
        for (int i = 0; i < ndims; i++)
        {
            range_t r = range_of(type, i);
            dump_expr(fh, r.left);
            switch (r.kind)
            {
                case RANGE_TO:
                    fprintf(fh, ":");
                    dump_expr(fh, r.right);
                    break;
                case RANGE_DOWNTO:
                    fprintf(fh, ":");
                    dump_expr(fh, r.right);
                    break;
                case RANGE_DYN:
                    fprintf(fh, " dynamic ");
                    dump_expr(fh, r.right);
                    break;
                case RANGE_RDYN:
                    fprintf(fh, " reverse_dynamic ");
                    dump_expr(fh, r.right);
                    break;
                case RANGE_EXPR:
                    break;
            }
        }
        fprintf(fh, "] ");
    }
    else
    {
        fprintf(fh, type_pp_minify(type, dump_minify_type), " ");
    }
}

/*
static void dump_op(FILE* fh, tree_t t)
{
    fprintf(fh, "-- predefined %s [", istr(tree_ident(t)));

    const int nports = tree_ports(t);
    for (int i = 0; i < nports; i++)
    {
        if (i > 0) fprintf(fh, ", ");
        dump_type(fh, tree_type(tree_port(t, i)));
    }

    fprintf(fh, "]");

    if (tree_kind(t) == T_FUNC_DECL)
    {
        fprintf(fh, " return ");
        dump_type(fh, type_result(tree_type(t)));
    }

    fprintf(fh, "\n");
}
*/

static void dump_always(FILE* fh, tree_t t, int n, tree_t sl, int s)
{
    int clk = 0;
    int rst = 0;
    
    const char *sig_0 = NULL; // Clock signal
    const char *sig_1 = NULL; // Reset signal
        
    if (s == 0)
    {
        // No clock : combinatorial
    }
    else if (s == 1) // Maybe one clock ?
    {
        // Potential clock signal
        sig_0 = istr(tree_ident(tree_ref(tree_trigger(sl, 0))));
        
        // Check for :
        // if rising_edge(clk) then ... -> clk = +1
        // if falling_edge(clk) then ... -> clk = -1
        if (tree_kind(tree_stmt(t, 0)) == T_IF)
        {
            tree_t if_exp = tree_value(tree_stmt(t, 0));
            
            if ((tree_kind(if_exp) == T_FCALL) && (tree_params(if_exp) == 1))
            {
                const char *func = istr(tree_ident(tree_ref(if_exp)));
                const char *par_0 = NULL;
                
                if (tree_kind(tree_value(tree_param(if_exp, 0))) == T_REF)
                {
                    par_0 = istr(tree_ident(tree_ref(tree_value(tree_param(if_exp, 0)))));
                }
                
                if (par_0)
                {
                    if ((strcmp(func,"IEEE.STD_LOGIC_1164.RISING_EDGE") == 0) &&
                        (strcmp(sig_0, par_0) == 0)) clk = 1;
                        
                    if ((strcmp(func,"IEEE.STD_LOGIC_1164.FALLING_EDGE") == 0) &&
                        (strcmp(sig_0, par_0) == 0)) clk = -1;
                }
                    
                //fprintf(fh, "1 : %s %s %s\n", func, sig_0, par_0);
                //fflush(fh);
            }
        }
        
    }
    else // Maybe one reset and one clock ?
    {
        // Potential clock and reset signals
        sig_0 = istr(tree_ident(tree_ref(tree_trigger(sl, 0))));
        sig_1 = istr(tree_ident(tree_ref(tree_trigger(sl, 1))));
        
        // Check for :
        // if (rst = '1') then ... -> rst = +1
        // if (rst = '0') then ... -> rst = -1
        if (tree_kind(tree_stmt(t, 0)) == T_IF)
        {
            tree_t if_exp = tree_value(tree_stmt(t, 0));
            
            if ((tree_kind(if_exp) == T_FCALL) && (tree_params(if_exp) == 2))
            {
                const char *func = istr(tree_ident(tree_ref(if_exp)));
                const char *par_0 = NULL;
                const char *par_1 = NULL;
                
                if (tree_kind(tree_value(tree_param(if_exp, 0))) == T_REF)
                {
                    par_0 = istr(tree_ident(tree_ref(tree_value(tree_param(if_exp, 0)))));
                }
                
                if (tree_kind(tree_value(tree_param(if_exp, 1))) == T_REF)
                {
                    par_1 = istr(tree_ident(tree_ref(tree_value(tree_param(if_exp, 1)))));
                }
                
                if ((par_0) && (par_0))
                {
                    if ((strcmp(func,"\"=\"") == 0) &&
                        (strcmp(sig_1, par_0) == 0) &&
                        (strcmp("'1'", par_1) == 0)) rst = 1;
                        
                    if ((strcmp(func,"\"=\"") == 0) &&
                        (strcmp(sig_1, par_0) == 0) &&
                        (strcmp("'0'", par_1) == 0)) rst = -1;
                    
                    if ((strcmp(func,"\"=\"") == 0) &&
                        (strcmp(sig_0, par_0) == 0) &&
                        (strcmp("'1'", par_1) == 0))
                    {
                        const char *tmp = sig_0;
                        sig_0 = sig_1;
                        sig_1 = tmp;
                        rst = 1;
                    }
                        
                    if ((strcmp(func,"\"=\"") == 0) &&
                        (strcmp(sig_0, par_0) == 0) &&
                        (strcmp("'0'", par_1) == 0))
                    {
                        const char *tmp = sig_0;
                        sig_0 = sig_1;
                        sig_1 = tmp;
                        rst = -1;
                    }
                }
                
                //fprintf(fh, "2 : %s %s %s %s %s %d\n", func, sig_0, sig_1, par_0, par_1, rst);
                //fflush(fh);
            }
            
            // Check for :
            // ... else if rising_edge(clk) then ... -> clk = +1
            // ... else if falling_edge(clk) then ... -> clk = -1
            if (tree_else_stmts(tree_stmt(t, 0)) > 0)
            {
                if (tree_kind(tree_else_stmt(tree_stmt(t, 0), 0)) == T_IF)
                {
                    tree_t if2_exp = tree_value(tree_else_stmt(tree_stmt(t, 0), 0));
                    
                    if ((tree_kind(if2_exp) == T_FCALL) && (tree_params(if2_exp) == 1))
                    {
                        const char *func = istr(tree_ident(tree_ref(if2_exp)));
                        const char *par_0 = NULL;
                        
                        if (tree_kind(tree_value(tree_param(if2_exp, 0))) == T_REF)
                        {
                            par_0 = istr(tree_ident(tree_ref(tree_value(tree_param(if2_exp, 0)))));
                        }
                        
                        if (par_0)
                        {
                            if ((strcmp(func,"IEEE.STD_LOGIC_1164.RISING_EDGE") == 0) &&
                                (strcmp(sig_0, par_0) == 0)) clk = 1;
                                
                            if ((strcmp(func,"IEEE.STD_LOGIC_1164.FALLING_EDGE") == 0) &&
                                (strcmp(sig_0, par_0) == 0)) clk = -1;
                        }
                        
                        //fprintf(fh, "1 : %s %s %s %d %d\n", func, sig_0, par_0, rst, clk);
                        //fflush(fh);
                    }
                }
            }
        }
        
    }
    
    dump_tab(fh);
    if (clk == 0)
    {
        fprintf(fh, "always_comb");
        g_comb = 1;
    }
    else
    {
        fprintf(fh, "always_ff @(");
        g_comb = 0;
        
        if (rst > 0)
        {
            fprintf(fh, "posedge %s or ", sig_1);
        }
        else if (rst < 0)
        {
            fprintf(fh, "negedge %s or ", sig_1);
        }
        
        if (clk > 0)
        {
            fprintf(fh, "posedge %s)", sig_0);
        }
        else
        {
            fprintf(fh, "negedge %s)", sig_0);
        }
    }
    if (tree_has_ident(t))
    {
        fprintf(fh, " begin : %s\n", istr(tree_ident(t)));
    }
    else
    {
        fprintf(fh, " begin\n");
    }
    fflush(fh);
}

static void dump_ports(FILE* fh, tree_t t)
{
    const int nports = tree_ports(t);
    if (nports > 0)
    {
        if (nports > 1)
        {
            fprintf(fh, " (\n");
        }
        else
        {
            fprintf(fh, " (");
        }
        for (int i = 0; i < nports; i++)
        {
            if (i > 0) fprintf(fh, ";\n");
            dump_port(fh, tree_port(t, i));
        }
        fprintf(fh, " )");
    }
}

static void dump_block(FILE* fh, tree_t t)
{
    const int ndecls = tree_decls(t);
    for (unsigned i = 0; i < ndecls; i++)
    {
        dump_decl(fh, tree_decl(t, i));
    }
    const int nstmts = tree_stmts(t);
    for (int i = 0; i < nstmts; i++)
    {
        dump_stmt(fh, tree_stmt(t, i));
    }
}

static void dump_decl(FILE* fh, tree_t t)
{
    switch (tree_kind(t))
    {
        case T_SIGNAL_DECL:
        case T_VAR_DECL:
            dump_tab(fh);
            dump_type(fh, tree_type(t));
            fprintf(fh, "%s;\n", istr(tree_ident(t)));
            return;
        
        case T_CONST_DECL:
            dump_tab(fh);
            fprintf(fh, "const ");
            dump_type(fh, tree_type(t));
            fprintf(fh, istr(tree_ident(t)));
            if (tree_has_value(t))
            {
                fprintf(fh, " = ");
                dump_expr(fh, tree_value(t));
            }
            fprintf(fh, ";\n");
            return;
        
        case T_TYPE_DECL:
        {
            int i;
            
            type_t type = tree_type(t);
            type_kind_t kind = type_kind(type);
            bool is_subtype = (kind == T_SUBTYPE);
        
            dump_tab(fh);
            fprintf(fh, "typedef ");
        
            if (is_subtype)
            {
                fprintf(fh, "%s ", istr(type_ident(type_base(type))));
            }
        
            if (type_is_integer(type) || type_is_real(type))
            {
                fprintf(fh, "range ");
                dump_range(fh, type_dim(type, 0));
            }
            else if (type_is_physical(type))
            {
                fprintf(fh, "range ");
                dump_range(fh, type_dim(type, 0));
                fprintf(fh, "\n");
                fprintf(fh, "units\n");
                {
                    const int nunits = type_units(type);
                    for (i = 0; i < nunits; i++)
                    {
                        tree_t u = type_unit(type, i);
                        fprintf(fh, "%s = ", istr(tree_ident(u)));
                        dump_expr(fh, tree_value(u));
                        fprintf(fh, ";\n");
                    }
                }
                fprintf(fh, "end units\n");
            }
            else if (type_is_array(type))
            {
                if (!is_subtype)
                {
                    dump_type(fh, type_elem(type));
                }
                fprintf(fh, "%s [", istr(tree_ident(t)));
                if (kind == T_UARRAY)
                {
                    const int nindex = type_index_constrs(type);
                    for (i = 0; i < nindex; i++)
                    {
                        if (i > 0) fprintf(fh, ", ");
                        dump_type(fh, type_index_constr(type, i));
                        fprintf(fh, " range <>");
                    }
                }
                else if (kind == T_SUBTYPE)
                {
                    tree_t constraint = type_constraint(type);
                    const int nranges = tree_ranges(constraint);
                    for (i = 0; i < nranges; i++)
                    {
                        if (i > 0) fprintf(fh, ", ");
                        dump_range(fh, tree_range(constraint, i));
                    }
                }
                else
                {
                    const int ndims = type_dims(type);
                    for (i = 0; i < ndims; i++)
                    {
                       if (i > 0) fprintf(fh, ", ");
                       dump_range(fh, type_dim(type, i));
                    }
                }
                fprintf(fh, "];\n");
            }
            else if (type_is_protected(type))
            {
                fprintf(fh, "protected\n");
                for (i = 0; i < type_decls(type); i++)
                {
                    dump_decl(fh, type_decl(type, i));
                }
                fprintf(fh, "end protected");
            }
            else if (kind == T_ENUM)
            {
                fprintf(fh, "enum {\n");
                g_tab++;
                for (i = 0; i < type_enum_literals(type); i++)
                {
                    if (i > 0) fprintf(fh, ",\n");
                    dump_tab(fh);
                    fprintf(fh, "%s", istr(tree_ident(type_enum_literal(type, i))));
                }
                fprintf(fh, "\n");
                g_tab--;
                dump_tab(fh);
                fprintf(fh, "}");
                fprintf(fh, " %s;\n", istr(tree_ident(t)));
            }
            else
            {
                dump_type(fh, type);
            }
            
            /*
            const int nops = tree_ops(t);
            for (int i = 0; i < nops; i++)
            {
                dump_op(fh, tree_op(t, i));
            }
            */
            return;
        }
        
        case T_SPEC:
        {
            fprintf(fh, "#for %s\n", istr(tree_ident(t)));
            fprintf(fh, "#end #for;\n");
            return;
        }
        
        case T_BLOCK_CONFIG:
        {
            fprintf(fh, "#for %s\n", istr(tree_ident(t)));
            dump_decls(fh, t);
            fprintf(fh, "#end #for;\n");
            return;
        }
        
        case T_ALIAS:
        {
            dump_tab(fh);
            fprintf(fh, "alias %s = ", istr(tree_ident(t)));
            dump_expr(fh, tree_value(t));
            fprintf(fh, ";\n");
            return;
        }
        
        case T_ATTR_SPEC:
        {
            fprintf(fh, "// attribute %s #of %s : #%s #is ", istr(tree_ident(t)),
                   istr(tree_ident2(t)), class_str(tree_class(t)));
            dump_expr(fh, tree_value(t));
            fprintf(fh, ";\n");
            return;
        }
        
        case T_ATTR_DECL:
        {
            fprintf(fh, "// attribute %s : ", istr(tree_ident(t)));
            dump_type(fh, tree_type(t));
            fprintf(fh, ";\n");
            return;
        }
        
        case T_GENVAR:
        {
            dump_tab(fh);
            fprintf(fh, "genvar %s;\n", istr(tree_ident(t)));
            //dump_type(fh, tree_type(t));
            return;
        }
        
        case T_FUNC_DECL:
        {
            fprintf(fh, "#function %s", istr(tree_ident(t)));
            dump_ports(fh, t);
            fprintf(fh, " #return %s;\n", type_pp(type_result(tree_type(t))));
            return;
        }
        
        case T_FUNC_BODY:
        {
            fprintf(fh, "#function %s", istr(tree_ident(t)));
            dump_ports(fh, t);
            fprintf(fh, " #return %s #is\n", type_pp(type_result(tree_type(t))));
            dump_block(fh, t);
            fprintf(fh, "#end #function;\n\n");
            return;
        }
        
        case T_PROC_DECL:
        {
            fprintf(fh, "#procedure %s", istr(tree_ident(t)));
            dump_ports(fh, t);
            fprintf(fh, ";");
            //dump_wait_level(t);
            fprintf(fh, "\n");
            return;
        }
        
        case T_PROC_BODY:
        {
            fprintf(fh, "#procedure %s", istr(tree_ident(t)));
            dump_ports(fh, t);
            fprintf(fh, " #is");
            //dump_wait_level(t);
            fprintf(fh, "\n");
            dump_block(fh, t);
            fprintf(fh, "#end #procedure;\n\n");
            return;
        }
        
        case T_HIER:
           fprintf(fh, "-- Enter scope %s\n", istr(tree_ident(t)));
           return;
        
        case T_COMPONENT:
        {
            int i, n;
            
            
            fprintf(fh, "/*\nmodule %s", istr(tree_ident(t)));
            
            n = tree_generics(t);
            if (n > 0)
            {
                fprintf(fh, "\n#(\n");
                for (i = 0; i < n; i++)
                {
                    if (i > 0) fprintf(fh, ",\n");
                    dump_port(fh, tree_generic(t, i));
                }
                fprintf(fh, "\n)");
            }
            
            n = tree_ports(t);
            if (n > 0)
            {
                fprintf(fh, "\n(\n");
                for (i = 0; i < n; i++)
                {
                    if (i > 0) fprintf(fh, ",\n");
                    dump_port(fh, tree_port(t, i));
                }
                fprintf(fh, "\n)");
            }
            fprintf(fh, ";\n*/\n");
            return;
        }
        
        case T_PROT_BODY:
        {
            fprintf(fh, "type %s #is #protected #body\n", istr(tree_ident(t)));
            for (unsigned i = 0; i < tree_decls(t); i++)
            {
                dump_decl(fh, tree_decl(t, i));
            }
            fprintf(fh, "#end #protected #body;\n");
            return;
        }
        
        case T_FILE_DECL:
        {
            fprintf(fh, "#file %s : ", istr(tree_ident(t)));
            dump_type(fh, tree_type(t));
            if (tree_has_value(t))
            {
                fprintf(fh, " #open ");
                dump_expr(fh, tree_file_mode(t));
                fprintf(fh, " #is ");
                dump_expr(fh, tree_value(t));
            }
            fprintf(fh, ";\n");
            return;
        }
        
        case T_USE:
        {
            fprintf(fh, "#use %s", istr(tree_ident(t)));
            if (tree_has_ident2(t))
               fprintf(fh, ".%s", istr(tree_ident2(t)));
            fprintf(fh, ";\n");
            return;
        }
        
        default:
        {
            //cannot_dump(t, "decl");
        }
    }
    
    dump_type(fh, tree_type(t));
    
    if (tree_has_value(t))
    {
        fprintf(fh, " = ");
        dump_expr(fh, tree_value(t));
    }
    fprintf(fh, ";");
    
    if (tree_attr_int(t, ident_new("returned"), 0))
    {
        fprintf(fh, " -- returned");
    }
    
    fprintf(fh, "\n");
    fflush(fh);
}

static void dump_stmt(FILE* fh, tree_t t)
{
    int i;
    
    if (tree_kind(t) == T_PRAGMA)
    {
        fprintf(fh, "%s\n", tree_text(t));
        return;
    }

    //if (tree_has_ident(t))
    //{
    //    fprintf(fh, "%s: ", istr(tree_ident(t)));
    //}

    switch (tree_kind(t))
    {
        case T_PROCESS:
        {
            int s, n;
            tree_t sl;
            
            // Number of statements
            n = tree_stmts(t);
            // Sensitivity list
            sl = tree_stmt(t, n - 1);
            // Number of signals
            s = tree_triggers(sl);
            
            // Start of process
            dump_always(fh, t, n, sl, s);
            g_tab++;
            
            // Variables declaration
            dump_decls(fh, t);
            fprintf(fh, "\n");
            
            // Statements
            for (i = 0; i < (n - 1); i++)
            {
                dump_stmt(fh, tree_stmt(t, i));
            }
            
            // End of process
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "end\n\n");
            g_comb = 0;
            return;
        }
        
        case T_SIGNAL_ASSIGN:
        {
            dump_tab(fh);
            dump_expr(fh, tree_target(t));
            fprintf(fh, (g_comb) ? " = " : " <= ");
            //fprintf(fh, " <= #reject ");
            //if (tree_has_reject(t))
            //    dump_expr(fh, tree_reject(t));
            //else
            //    fprintf(fh, "0 ps");
            //fprintf(fh, " #inertial ");
            for (i = 0; i < tree_waveforms(t); i++)
            {
                if (i > 0) fprintf(fh, ", ");
                tree_t w = tree_waveform(t, i);
                dump_expr(fh, tree_value(w));
                //if (tree_has_delay(w))
                //{
                //    fprintf(fh, " #after ");
                //    dump_expr(fh, tree_delay(w));
                //}
            }
            break;
        }
        
        case T_VAR_ASSIGN:
        {
            dump_tab(fh);
            dump_expr(fh, tree_target(t));
            fprintf(fh, " = ");
            dump_expr(fh, tree_value(t));
            break;
        }
        
        case T_WAIT:
        {
            fprintf(fh, "#wait");
            if (tree_triggers(t) > 0)
            {
                fprintf(fh, " #on ");
                for (unsigned i = 0; i < tree_triggers(t); i++)
                {
                    if (i > 0) fprintf(fh, ", ");
                    dump_expr(fh, tree_trigger(t, i));
                }
            }
            if (tree_has_delay(t)) {
               fprintf(fh, " #for ");
               dump_expr(fh, tree_delay(t));
            }
            fprintf(fh, ";");
            if (tree_attr_int(t, ident_new("static"), 0))
               fprintf(fh, "   -- static");
            fprintf(fh, "\n");
            return;
        }
        
        case T_BLOCK:
        {
            dump_tab(fh);
            fprintf(fh, "begin\n");
            g_tab++;
            dump_block(fh, t);
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "end\n");
            fflush(fh);
            return;
        }
        
        case T_ASSERT:
        {
            if (tree_has_value(t))
            {
               fprintf(fh, "#assert ");
               dump_expr(fh, tree_value(t));
            }
            if (tree_has_message(t))
            {
               fprintf(fh, " #report ");
               dump_expr(fh, tree_message(t));
            }
            fprintf(fh, " #severity ");
            dump_expr(fh, tree_severity(t));
            break;
        }
        
        case T_WHILE:
        {
            if (tree_has_value(t))
            {
                fprintf(fh, "#while ");
                dump_expr(fh, tree_value(t));
                fprintf(fh, " ");
            }
            fprintf(fh, "#loop\n");
            for (i = 0; i < tree_stmts(t); i++)
            {
                dump_stmt(fh, tree_stmt(t, i));
            }
            fprintf(fh, "#end #loop");
            break;
        }
        
        case T_IF:
        {
            dump_tab(fh);
            fprintf(fh, "if (");
            dump_expr(fh, tree_value(t));
            fprintf(fh, ") begin\n");
            g_tab++;
            for (i = 0; i < tree_stmts(t); i++)
            {
                dump_stmt(fh, tree_stmt(t, i));
            }
            if (tree_else_stmts(t) > 0)
            {
                g_tab--;
                dump_tab(fh);
                fprintf(fh, "end else begin\n");
                g_tab++;
                for (i = 0; i < tree_else_stmts(t); i++)
                {
                    dump_stmt(fh, tree_else_stmt(t, i));
                }
            }
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "end\n");
            fflush(fh);
            return;
        }
        
        case T_EXIT:
        {
            fprintf(fh, "#exit %s", istr(tree_ident2(t)));
            if (tree_has_value(t))
            {
              fprintf(fh, " #when ");
              dump_expr(fh, tree_value(t));
            }
            break;
        }
        
        case T_CASE:
        {
            dump_tab(fh);
            fprintf(fh, "case (");
            dump_expr(fh, tree_value(t));
            fprintf(fh, ")\n");
            g_tab++;
            for (i = 0; i < tree_assocs(t); i++)
            {
                tree_t a = tree_assoc(t, i);
                switch (tree_subkind(a))
                {
                    case A_NAMED:
                    {
                        dump_tab(fh);
                        dump_expr(fh, tree_name(a));
                        fprintf(fh, ":\n");
                        break;
                    }
                    case A_RANGE:
                    {
                        dump_tab(fh);
                        fprintf(fh, "[");
                        dump_range(fh, tree_range(a, 0));
                        fprintf(fh, "]:\n");
                        break;
                    }
                    case A_OTHERS:
                    {
                        dump_tab(fh);
                        fprintf(fh, "default:\n");
                        break;
                    }
                    default:
                    {
                        printf("case subkind = %d\n", tree_subkind(a));
                        assert(false);
                    }
                }
                dump_stmt(fh, tree_value(a));
            }
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "endcase\n");
            fflush(fh);
            return;
        }
        
        case T_RETURN:
        {
            fprintf(fh, "#return");
            if (tree_has_value(t))
            {
                fprintf(fh, " ");
                dump_expr(fh, tree_value(t));
            }
            break;
        }
        
        case T_FOR:
        {
            const char *v = istr(tree_ident2(t));
            range_t r = tree_range(t, 0);
            
            dump_tab(fh);
            fprintf(fh, "for (%s = ", v);
            dump_expr(fh, r.left);
            fprintf(fh, "; %s <= ", v);
            dump_expr(fh, r.right);
            if (r.kind == RANGE_TO)
            {
                fprintf(fh, "; %s = %s + 1) begin\n", v, v);
            }
            else if (r.kind == RANGE_DOWNTO)
            {
                fprintf(fh, "; %s = %s - 1) begin\n", v, v);
            }
            else
            {
                fprintf(fh, "; /* r.kind = %d ??? */) begin\n", r.kind);
            }
            
            g_tab++;
            for (i = 0; i < tree_stmts(t); i++)
            {
                dump_stmt(fh, tree_stmt(t, i));
            }
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "end\n");
            fflush(fh);
            return;
        }
        
        case T_PCALL:
        {
            fprintf(fh, "%s", istr(tree_ident(tree_ref(t))));
            dump_params(fh, t, tree_param, tree_params(t), NULL);
            break;
        }
        
        case T_FOR_GENERATE:
        {
            const char *v = istr(tree_ident2(t));
            range_t r = tree_range(t, 0);
            
            dump_tab(fh);
            fprintf(fh, "generate\n");
            dump_tab(fh);
            fprintf(fh, "for (%s = ", v);
            dump_expr(fh, r.left);
            fprintf(fh, "; %s <= ", v);
            dump_expr(fh, r.right);
            if (r.kind == RANGE_TO)
            {
                fprintf(fh, "; %s = %s + 1) begin\n", v, v);
            }
            else if (r.kind == RANGE_DOWNTO)
            {
                fprintf(fh, "; %s = %s - 1) begin\n", v, v);
            }
            else
            {
                fprintf(fh, "; /* r.kind = %d ??? */) begin\n", r.kind);
            }
            g_tab++;
            for (i = 0; i < tree_decls(t); i++)
            {
                dump_decl(fh, tree_decl(t, i));
            }
            for (i = 0; i < tree_stmts(t); i++)
            {
                dump_stmt(fh, tree_stmt(t, i));
            }
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "end\n");
            dump_tab(fh);
            fprintf(fh, "endgenerate\n");
            fflush(fh);
            return;
        }
        
        case T_IF_GENERATE:
        {
            dump_tab(fh);
            fprintf(fh, "generate\n");
            dump_tab(fh);
            fprintf(fh, "if ");
            dump_expr(fh, tree_value(t));
            fprintf(fh, " begin\n");
            g_tab++;
            for (i = 0; i < tree_decls(t); i++)
            {
                dump_decl(fh, tree_decl(t, i));
            }
            for (i = 0; i < tree_stmts(t); i++)
            {
                dump_stmt(fh, tree_stmt(t, i));
            }
            g_tab--;
            dump_tab(fh);
            fprintf(fh, "end\n");
            dump_tab(fh);
            fprintf(fh, "endgenerate\n");
            fflush(fh);
            return;
        }
        
        case T_INSTANCE:
        {
            /*
            switch (tree_class(t))
            {
                case C_ENTITY:    fprintf(fh, "#entity ");    break;
                case C_COMPONENT: fprintf(fh, "#component "); break;
                default:          assert(false);
            }
            fprintf(fh, "%s : %s", istr(tree_ident(t)), istr(tree_ident2(t)));
            if (tree_has_spec(t))
            {
                tree_t bind = tree_value(tree_spec(t));
                fprintf(fh, " -- bound to %s", istr(tree_ident(bind)));
                if (tree_has_ident2(bind))
                {
                    fprintf(fh, "(%s)", istr(tree_ident2(bind)));
                }
            }
            fprintf(fh, "\n");
            if (tree_genmaps(t) > 0)
            {
                dump_params(fh, t, tree_genmap, tree_genmaps(t), "#generic #map");
                fprintf(fh, "\n");
            }
            if (tree_params(t) > 0)
            {
                dump_params(fh, t, tree_param, tree_params(t), "#port #map");
            }
            fprintf(fh, ";\n\n");
            */
            int n;
            
            dump_tab(fh);
            fprintf(fh, "%s", istr(tree_ident2(t)));
            n = tree_genmaps(t);
            if (n > 0)
            {
                fprintf(fh, "\n");
                dump_tab(fh);
                fprintf(fh, "#(\n");
                g_tab++;
                for (i = 0; i < n; i++)
                {
                    tree_t p = tree_genmap(t, i);
                    
                    if (i > 0) fprintf(fh, ",\n");
                    dump_tab(fh);
                    fprintf(fh, ".");
                    if (tree_subkind(p) == P_NAMED)
                    {
                        dump_expr(fh, tree_name(p));
                    }
                    fprintf(fh, " (");
                    dump_expr(fh, tree_value(p));
                    fprintf(fh, ")");
                }
                g_tab--;
                fprintf(fh, "\n");
                dump_tab(fh);
                fprintf(fh, ")\n");
                dump_tab(fh);
            }
            else
            {
                fprintf(fh, " ");
            }
            fprintf(fh, "%s", istr(tree_ident(t)));
            n = tree_params(t);
            if (n > 0)
            {
                fprintf(fh, "\n");
                dump_tab(fh);
                fprintf(fh, "(\n");
                g_tab++;
                for (i = 0; i < n; i++)
                {
                    tree_t p = tree_param(t, i);
                    
                    if (i > 0) fprintf(fh, ",\n");
                    dump_tab(fh);
                    fprintf(fh, ".");
                    if (tree_subkind(p) == P_NAMED)
                    {
                        dump_expr(fh, tree_name(p));
                    }
                    fprintf(fh, " (");
                    dump_expr(fh, tree_value(p));
                    fprintf(fh, ")");
                }
                g_tab--;
                fprintf(fh, "\n");
                dump_tab(fh);
                fprintf(fh, ");\n\n");
            }
            fflush(fh);
            return;
        }
        
        case T_NEXT:
        {
            fprintf(fh, "#next");
            if (tree_has_value(t))
            {
                fprintf(fh, " #when ");
                dump_expr(fh, tree_value(t));
            }
            break;
        }
        
        default:
        {
            //cannot_dump(t, "stmt");
        }
    }
    fprintf(fh, ";\n");
    fflush(fh);
}

static void dump_port(FILE* fh, tree_t t)
{
    const char *dir = NULL;
    switch (tree_class(t))
    {
        case C_SIGNAL:
        case C_VARIABLE:
        case C_DEFAULT:
        {
            switch (tree_subkind(t))
            {
                case PORT_IN:      dir = "input";  break;
                case PORT_OUT:     dir = "output"; break;
                case PORT_INOUT:   dir = "inout";  break;
                case PORT_BUFFER:  dir = "output"; break;
                case PORT_INVALID: dir = "??";     break;
            }
            break;
        }
        case C_CONSTANT:
        {
            dir = "parameter"; break;
            break;
        }
        case C_FILE:
        {
            dir = "file";
            break;
        }
        default:
        {
            assert(false);
        }
    }
    dump_tab(fh);
    fprintf(fh, "%-10s", dir);
    dump_type(fh, tree_type(t));
    fprintf(fh, " %s", istr(tree_ident(t)));
}

static void dump_context(FILE* fh, tree_t t)
{
    const int nctx = tree_contexts(t);
    for (int i = 0; i < nctx; i++)
    {
        tree_t c = tree_context(t, i);
        switch (tree_kind(c))
        {
            case T_LIBRARY:
            {
                if (tree_ident(c) != std_i && tree_ident(c) != work_i)
                {
                    fprintf(fh, "// VHDL : library %s;\n", istr(tree_ident(c)));
                }
                break;
            }
            
            case T_USE:
            {
                fprintf(fh, "// VHDL : use %s", istr(tree_ident(c)));
                if (tree_has_ident2(c))
                {
                    fprintf(fh, ".%s", istr(tree_ident2(c)));
                }
                fprintf(fh, ";\n");
                break;
            }
            
            case T_PRAGMA:
            {
                fprintf(fh, "%s\n", tree_text(t));
                break;
            }
            
            default:
            {
                //
            }
        }
    }
    
    if (nctx > 0) fprintf(fh, "\n");
}

static void dump_entity(FILE* fh, tree_t t)
{
    int i, n;
    char c = 0;
    const char *mod;
    
    dump_context(fh, t);
    mod = strstr(istr(tree_ident(t)), ".");
    fprintf(fh, "module %s", mod + 1);
    
    n = tree_generics(t);
    if (n > 0)
    {
        // VHDL "generic" -> SystemVerilog "parameter"
        fprintf(fh, "\n#(\n");
        for (i = 0; i < n; i++)
        {
            tree_t p = tree_generic(t, i);
            if (i > 0) fprintf(fh, ",\n");
            dump_port(fh, p);
            if (tree_has_value(p))
            {
                fprintf(fh, " = ");
                dump_expr(fh, tree_value(p));
            }
        }
        fprintf(fh, "\n)");
        c = ';';
    }
    
    n = tree_ports(t);
    if (n > 0)
    {
        // VHDL "port" -> SystemVerilog "port"
        fprintf(fh, "\n(\n");
        for (i = 0; i < n; i++)
        {
            if (i > 0) fprintf(fh, ",\n");
            dump_port(fh, tree_port(t, i));
        }
        fprintf(fh, "\n)");
        c = ';';
    }
    fprintf(fh, "%c\n", c);
    
    n = tree_stmts(t);
    if (n > 0)
    {
        for (i = 0; i < n; i++)
        {
            dump_stmt(fh, tree_stmt(t, i));
        }
    }
}

static void dump_decls(FILE* fh, tree_t t)
{
    const int ndecls = tree_decls(t);
    
    for (unsigned i = 0; i < ndecls; i++)
    {
        dump_decl(fh, tree_decl(t, i));
    }
}

static void dump_arch(FILE* fh, tree_t t)
{
    int i;
    
    dump_context(fh, t);
    
    for (i = 0; i < tree_decls(t); i++)
    {
        dump_decl(fh, tree_decl(t, i));
    }
    
    fprintf(fh, "\n// VHDL : architecture %s of %s is\n\n",
            istr(tree_ident(t)), istr(tree_ident2(t)));
    
    for (i = 0; i < tree_stmts(t); i++)
    {
        dump_stmt(fh, tree_stmt(t, i));
    }
    fprintf(fh, "endmodule\n");
}

static void trees_to_sv(FILE* fh, tree_t *elements, unsigned int n_elements)
{
    int i;
    
    for(i = 0; i < n_elements; i++)
    {
        tree_t t = elements[i];
        switch (tree_kind(t))
        {
            case T_ENTITY:
            {
                dump_entity(fh, t);
                fflush(fh);
                break;
            }
            case T_ARCH:
            {
                dump_arch(fh, t);
                fflush(fh);
                break;
            }
            case T_FCALL:
            case T_LITERAL:
            case T_AGGREGATE:
            case T_REF:
            case T_ARRAY_REF:
            case T_ARRAY_SLICE:
            case T_TYPE_CONV:
            case T_CONCAT:
            case T_RECORD_REF:
            {
                dump_expr(fh, t);
                fflush(fh);
                fprintf(fh, "\n");
                break;                
            }
            case T_FOR_GENERATE:
            case T_BLOCK:
            case T_PROCESS:
            case T_CASE:
            case T_FOR:
            {
                dump_stmt(fh, t);
                fflush(fh);
                break;
            }
            case T_CONST_DECL:
            case T_VAR_DECL:
            case T_SIGNAL_DECL:
            {
                dump_decl(fh, t);
                fflush(fh);
                break;
            }
            default:
            {
                //
            }
        }
    }
}

void dump_sv(tree_t *elements, unsigned int n_elements, const char *filename)
{
    FILE* dump_file = fopen(filename, "w");
    if (!dump_file)
    {
        fatal_errno("Failed to open SystemVerilog file %s", filename);
        return;
    }
    
    g_tab  = 1;
    g_comb = 0;
    trees_to_sv(dump_file, elements, n_elements);
    
    fclose(dump_file);
}
