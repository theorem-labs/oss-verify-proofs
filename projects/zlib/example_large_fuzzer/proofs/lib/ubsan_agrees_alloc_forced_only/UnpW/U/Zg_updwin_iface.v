(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_updwin_pure Z_updwin.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition updwin_have_stmt : Prop :=
  forall (L : ilay) (s : inflate_state) (c : icall) (src : arr) (put copy E lo : Z) (b : ZProg.blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk usegs m lo (bv_unsigned sp) -> izs m L c ->
  isA m L s -> is_window_blk s = Some b -> iwin m L s -> arr_len (is_window s) = 32768 ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < 2^32 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < il_Aw L -> il_Aw L + 32768 <= lo -> apart (il_As L) 7176 (il_Aw L) 32768 ->
  0 < E - copy -> E <= lo -> (E <= il_Aw L \/ il_Aw L + 32768 <= E - copy) -> (E <= il_As L \/ il_As L + 7176 <= E - copy) ->
  mem_inv usegs m ->
  il_S L mod 8 = 0 -> il_As L mod 16 = 0 ->      (* [comment removed for export] *)
  evt usegs (updwin_post L (updw_core s src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                         [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (il_Aw L, il_Aw L + 32768)] m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) (wz E) (wz copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_UPDATEWINDOW) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition updwin_ret_block_stmt : Prop :=
  forall (fj : list byte) (L : ilay) (s : inflate_state) (src : arr) (put copy E lo A : Z) (wb : ZProg.blk) (junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells usegs m (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (bv_unsigned sp + -64) ->
  isA m L s -> is_window_blk s = None -> rw_cells usegs m A [CB (Z.to_nat 32768) junk] ->
  bytes_at usegs m (E - copy) (map (Z_to_bv 8) (arr_slice src (put - copy) copy)) ->
  is_wbits s = 15 -> 0 <= copy < 2^32 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  lo <= bv_unsigned sp - 64 -> 0x5f000 <= lo -> bv_unsigned sp < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo -> 0 < A -> A + 32768 <= lo -> apart (il_As L) 7176 A 32768 ->
  0 < E - copy -> E <= lo -> (E <= A \/ A + 32768 <= E - copy) -> (E <= il_As L \/ il_As L + 7176 <= E - copy) ->
  mem_inv usegs m ->
  evt usegs (updwin_post (il_setw L A) (updw_core (s_fresh s wb junk) src put copy) 0 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                         [(lo, bv_unsigned sp); (il_As L, il_As L + 168); (A, A + 32768)] m)
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz E) (wz copy) (wz A) a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz (il_As L)) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_RET) fc None m (seg_rom usegs)).
