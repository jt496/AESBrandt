// Lean compiler output
// Module: AESBrandt.CompletePartite
// Imports: Init Mathlib.Order.Partition.Finpartition Mathlib.Combinatorics.SimpleGraph.Maps Mathlib.Combinatorics.SimpleGraph.Partition
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_setoid(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Finpartition_part___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_finpartition(lean_object*);
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__7___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_card(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at_SimpleGraph_IsCompletePartite_finpartition___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_SimpleGraph_IsCompletePartite_finpartition___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Finset_image___at_SimpleGraph_IsCompletePartite_finpartition___spec__5___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4(lean_object*);
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9(lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_instDecidableRelR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_partition___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__8___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_partition___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_card___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
uint8_t l_List_isPerm___at_List_decidablePerm___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring(lean_object*);
uint8_t l_List_decidableBAll___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Finset_image___at_SimpleGraph_IsCompletePartite_finpartition___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_finpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_instDecidableRelR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_partition(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_SimpleGraph_IsCompletePartite_finpartition___spec__6___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_setoid___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at_SimpleGraph_IsCompletePartite_finpartition___spec__10___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_setoid(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_setoid___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_SimpleGraph_IsCompletePartite_setoid(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_partition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_partition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_partition___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_partition___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_SimpleGraph_IsCompletePartite_partition___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_instDecidableNot___rarg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_instDecidableRelR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_instDecidableRelR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_SimpleGraph_IsCompletePartite_instDecidableRelR(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg(x_3, x_5, x_10);
if (x_12 == 0)
{
lean_free_object(x_6);
lean_dec(x_10);
x_2 = lean_box(0);
x_6 = x_11;
goto _start;
}
else
{
lean_ctor_set(x_6, 1, x_7);
{
lean_object* _tmp_1 = lean_box(0);
lean_object* _tmp_5 = x_11;
lean_object* _tmp_6 = x_6;
x_2 = _tmp_1;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_inc(x_15);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l_SimpleGraph_IsCompletePartite_instDecidableRelR___rarg(x_3, x_5, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
x_2 = lean_box(0);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_7);
x_2 = lean_box(0);
x_6 = x_16;
x_7 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; 
x_4 = l_List_isPerm___at_List_decidablePerm___spec__1___rarg(x_1, x_2, x_3);
x_5 = l_instDecidableNot___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_inc(x_5);
x_11 = l_List_decidableBAll___rarg(x_10, x_5);
if (x_11 == 0)
{
lean_dec(x_9);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_5);
x_3 = x_8;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_inc(x_5);
x_11 = l_List_decidableBAll___rarg(x_10, x_5);
if (x_11 == 0)
{
lean_dec(x_9);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_5);
x_3 = x_8;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_SimpleGraph_IsCompletePartite_finpartition___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_mk(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_le(x_5, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg(x_1, x_4, x_9, x_10, x_2);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_5);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg(x_1, x_4, x_14, x_15, x_2);
lean_dec(x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at_SimpleGraph_IsCompletePartite_finpartition___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldrTR___at_SimpleGraph_IsCompletePartite_finpartition___spec__10___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldrTR___at_SimpleGraph_IsCompletePartite_finpartition___spec__10___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__8___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Multiset_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Multiset_dedup___at_SimpleGraph_IsCompletePartite_finpartition___spec__7___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_SimpleGraph_IsCompletePartite_finpartition___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_toFinset___at_SimpleGraph_IsCompletePartite_finpartition___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Multiset_toFinset___at_SimpleGraph_IsCompletePartite_finpartition___spec__6___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finset_image___at_SimpleGraph_IsCompletePartite_finpartition___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Multiset_map___rarg(x_2, x_3);
x_5 = l_List_pwFilter___at_SimpleGraph_IsCompletePartite_finpartition___spec__9___rarg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Finset_image___at_SimpleGraph_IsCompletePartite_finpartition___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finset_image___at_SimpleGraph_IsCompletePartite_finpartition___spec__5___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg(x_1, lean_box(0), x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_3);
x_8 = l_Finset_image___at_SimpleGraph_IsCompletePartite_finpartition___spec__5___rarg(x_4, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_finpartition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_finpartition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_finpartition___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_filterTR_loop___at_SimpleGraph_IsCompletePartite_finpartition___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Multiset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Finset_filter___at_SimpleGraph_IsCompletePartite_finpartition___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__11___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_SimpleGraph_IsCompletePartite_finpartition___spec__12___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Finpartition_ofSetoid___at_SimpleGraph_IsCompletePartite_finpartition___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_card___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_SimpleGraph_IsCompletePartite_finpartition___rarg(x_1, lean_box(0), x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthTRAux___rarg(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_card(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_card___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_SimpleGraph_IsCompletePartite_finpartition___rarg(x_1, lean_box(0), x_3, x_4, x_5);
x_8 = l_Finpartition_part___rarg(x_4, x_3, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_coloring___elambda__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_coloring___elambda__1___rarg), 6, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
lean_closure_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SimpleGraph_IsCompletePartite_coloring(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SimpleGraph_IsCompletePartite_coloring___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Order_Partition_Finpartition(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Combinatorics_SimpleGraph_Maps(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Combinatorics_SimpleGraph_Partition(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_AESBrandt_CompletePartite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_Partition_Finpartition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Combinatorics_SimpleGraph_Maps(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Combinatorics_SimpleGraph_Partition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
