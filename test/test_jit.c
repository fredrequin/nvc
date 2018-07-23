#include "test_util.h"
#include "jit/jit.h"

#define check_result(expr, expect) \
   __check_result(#expr, expr, expect)

static vcode_unit_t context = NULL;
static vcode_type_t vint32 = VCODE_INVALID_TYPE;

static void setup(void)
{
   context = emit_context(ident_new("unit_test"));
   vint32 = vtype_int(INT32_MIN, INT32_MAX);
}

static void teardown(void)
{
   vcode_unit_unref(context);
}

static void __check_result(const char *expr, int32_t have, int32_t expect)
{
   if (have != expect)
      fail("expected result of %s to be %d but have %d", expr, expect, have);
}

START_TEST(test_ret42)
{
   vcode_unit_t unit = emit_thunk(ident_new("ret42"), context, vint32);
   emit_return(emit_const(vint32, 42));
   vcode_opt();

   uint32_t (*fn)(void) = jit_vcode_unit(unit);
   fail_if(fn == NULL);

   uint32_t result = (*fn)();
   fail_unless(result == 42);

   jit_free(fn);
}
END_TEST

START_TEST(test_add1)
{
   vcode_unit_t unit = emit_function(ident_new("add1"), context, vint32);
   vcode_reg_t p1 = emit_param(vint32, vint32, ident_new("p1"));
   vcode_reg_t r = emit_add(p1, emit_const(vint32, 1));
   emit_return(r);
   vcode_opt();

   uint32_t (*fn)(int) = jit_vcode_unit(unit);
   fail_if(fn == NULL);

   fail_unless((*fn)(5) == 6);
   fail_unless((*fn)(-1) == 0);
   fail_unless((*fn)(127) == 128);

   jit_free(fn);
}
END_TEST

START_TEST(test_load_store)
{
   vcode_unit_t unit =
      emit_function(ident_new("load_store"), context, vint32);
   vcode_reg_t p1 = emit_param(vint32, vint32, ident_new("p1"));
   vcode_reg_t mem = emit_alloca(vint32, vint32, VCODE_INVALID_REG);
   emit_store_indirect(p1, mem);
   vcode_reg_t result = emit_load_indirect(mem);
   emit_return(result);

   vcode_opt();

   uint32_t (*fn)(int) = jit_vcode_unit(unit);
   fail_if(fn == NULL);

   fail_unless((*fn)(1) == 1);
   fail_unless((*fn)(INT32_MAX) == INT32_MAX);

   jit_free(fn);
}
END_TEST

START_TEST(test_variables)
{
   vcode_unit_t unit =
      emit_function(ident_new("variables"), context, vint32);
   vcode_reg_t p1 = emit_param(vint32, vint32, ident_new("p1"));
   vcode_var_t var = emit_var(vint32, vint32, ident_new("v"), false);
   emit_store(p1, var);

   vcode_block_t bb = emit_block();
   emit_jump(bb);

   vcode_select_block(bb);

   vcode_reg_t result = emit_load(var);
   emit_return(result);

   vcode_opt();

   uint32_t (*fn)(int) = jit_vcode_unit(unit);
   fail_if(fn == NULL);

   fail_unless((*fn)(1) == 1);
   fail_unless((*fn)(INT32_MAX) == INT32_MAX);

   jit_free(fn);
}
END_TEST

START_TEST(test_loop)
{
   vcode_unit_t unit = emit_function(ident_new("fact"), context, vint32);
   vcode_reg_t p1 = emit_param(vint32, vint32, ident_new("p1"));
   vcode_reg_t ctr = emit_alloca(vint32, vint32, VCODE_INVALID_REG);
   vcode_reg_t result = emit_alloca(vint32, vint32, VCODE_INVALID_REG);
   emit_store_indirect(emit_const(vint32, 1), ctr);
   emit_store_indirect(emit_const(vint32, 1), result);

   vcode_block_t testbb = emit_block();
   vcode_block_t exitbb = emit_block();
   vcode_block_t bodybb = emit_block();
   emit_jump(testbb);

   vcode_select_block(testbb);
   vcode_reg_t loaded = emit_load_indirect(ctr);
   vcode_reg_t test = emit_cmp(VCODE_CMP_GT, loaded, p1);
   emit_cond(test, exitbb, bodybb);

   vcode_select_block(bodybb);

   vcode_reg_t tmp = emit_load_indirect(result);
   vcode_reg_t result_next = emit_mul(tmp, loaded);
   emit_store_indirect(result_next, result);
   vcode_reg_t ctr_next = emit_add(loaded, emit_const(vint32, 1));
   emit_store_indirect(ctr_next, ctr);
   emit_jump(testbb);

   vcode_select_block(exitbb);
   emit_return(emit_load_indirect(result));

   vcode_opt();

   uint32_t (*fn)(int) = jit_vcode_unit(unit);
   fail_if(fn == NULL);

   check_result((*fn)(1), 1);
   check_result((*fn)(2), 2);
   check_result((*fn)(3), 6);
   check_result((*fn)(4), 24);

   jit_free(fn);
}
END_TEST

Suite *get_jit_tests(void)
{
   Suite *s = suite_create("jit");

   TCase *tc = nvc_unit_test();
   tcase_add_test(tc, test_ret42);
   tcase_add_test(tc, test_add1);
   tcase_add_test(tc, test_load_store);
   tcase_add_test(tc, test_loop);
   tcase_add_test(tc, test_variables);
   tcase_add_checked_fixture(tc, setup, teardown);
   suite_add_tcase(s, tc);

   return s;
}
