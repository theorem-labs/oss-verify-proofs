(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_kit
  Z_defl_path Z_defl_entry Z_defl_arms Z_defl_pend Z_defl_hdr Z_defl_blocks Z_defl_fin.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition deflate_in_stmt : Prop :=
  forall (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> dout m L rest0 (ds_strm d) -> mem_inv usegs m -> relro_clean m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DEFLATE_IN_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  defl_path inp flush (deflate_core d flush) d ->
  (length (cs_out_rev (ds_strm (fst (deflate_core d flush)))) <= length rest0)%nat ->
  a0 = wz (dl_S L) -> a1 = wz flush ->
  evt usegs (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst (deflate_core d flush)) (snd (deflate_core d flush)) inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE_PC) fc None m (seg_rom usegs)).

Section ASM.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HSLOW : deflate_slow_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = 0 \/ flush = 4.
Variables (R : deflate_state * Z) (Q : machine_state -> Prop).
Hypothesis EXIT : forall X rc, R = (X, rc) -> DKE L rest0 lo r F fc me Q (wz rc) X.
Hypothesis ROOMR : (length (cs_out_rev (ds_strm (fst R))) <= length rest0)%nat.

End ASM.

Section DEFL.
Hypothesis HSLOW : deflate_slow_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

End DEFL.
