(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_C0_stmt ECH_C2_stmt ECH_C6_stmt ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_LibMid ECH_KitSeg ECH_Iface ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C5_stmt ECH_C7_stmt ECH_C13_stmt ECH_C14_stmt ECH_C15_stmt ECH_UbKit ECH_C1_dup ECH_C1_freeopt ECH_C4 ECH_C7_newmembuf ECH_C15_parse.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FZ_R1 : Z := 0xe2814.   (* [comment removed for export] *)
Definition FZ_R2 : Z := 0xe2838.
Definition FZ_R3 : Z := 0xe28c4.
Definition FZ_R4 : Z := 0xe28e0.
Definition FZ_R5 : Z := 0xe28e4.
Definition A_FZ_FILE : Z := 0x33a47.
Definition fz_frame (junk : list byte) (s1 s0 ra : word) : list cell := [CB 8 junk; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma f_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (D N lo : Z),
      a1 = Z_to_bv 64 N -> 0 <= N < 2^31 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 junk,
          ms' = MS (mkR (Z_to_bv 64 FZ_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 (Z_to_bv 64 D) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_parse_one) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells usegs m1 (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_FUZZ_ENTRY) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros A1 NR ST CEIL LO MI. subst a1.
    unfold P_FUZZ_ENTRY, P_LLVMFuzzerTestOneInput, P_parse_one, FZ_R1.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. carve_frame 32%nat ST.
    do 3 st1. step. step.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota| symmetry; rewrite (unsigned_lit N) by lia; rewrite Z.shiftr_div_pow2, Z.div_small by lia; vm_compute; reflexivity] end.
    step. step. step. finish. unfold fz_frame. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma f_seg2a :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (N : Z),
      32 <= N < 1500 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0,
          ms' = MS (mkR (Z_to_bv 64 FZ_R2) sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 s1 (Z_to_bv 64 N) (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 68) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom usegs) /\ u0 = t0)
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_R1) fc None m (seg_rom usegs)).
  Proof.
    intros until N. intros NR MI. unfold FZ_R1, FZ_R2, P_CRYPTO_memdup, A_FZ_FILE.
    step. step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 5 step. step. apply evt_done. exists t0. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma f_seg2b :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (N : Z),
      0 <= N < 2^31 -> (N < 32 \/ 1500 <= N) -> mem_inv usegs m ->
      evt usegs (fun ms' => exists u0,
          ms' = MS (mkR (Z_to_bv 64 FZ_R4) sp gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 80) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs) /\ u0 = t0)
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_R1) fc None m (seg_rom usegs)).
  Proof.
    intros until N. intros NR NC MI. unfold FZ_R1, FZ_R4, P_CRYPTO_free, A_FZ_FILE.
    step. step. step. try (if_cases K0; zify_cond K0; [| kill K0]; clear K0).
    do 5 step. step. apply evt_done. exists t0. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma f_seg3 :
    forall (rax sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (N A : Z) (bs : list byte),
      32 <= N < 1500 -> 0 < A -> A + N <= hceil -> zlength bs = N -> rw_cells usegs m A [CB (length bs) bs] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (c2 c3 c4 c5 : word) m1 bs',
          ms' = MS (mkR (Z_to_bv 64 FZ_R3) sp gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 N) c2 c3 c4 c5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_parse_one) fc None m1 (seg_rom usegs)
          /\ munch [(A, A + 6)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ bytes_at usegs m1 A bs' /\ zlength bs' = N)
        (MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 N) s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_R2) fc None m (seg_rom usegs)).
  Proof.
    intros until bs. intros NR AP AH LEN BLK MI. unfold FZ_R2, FZ_R3, P_parse_one. unfold zlength in LEN.
    hcb.
    pose proof (munch_refl [(A, A + 6)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    destruct (rw_cells_CB_split _ _ _ _ 6 _ BLK ltac:(lia)) as [HD TL]. clear BLK.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    (* [comment removed for export] *)
    step.                                  (* [comment removed for export] *)
    step. step. ub_dead.                   (* [comment removed for export] *)
    step. step. step.                      (* [comment removed for export] *)
    st1.                                   (* [comment removed for export] *)
    step. ub_dead.                         (* [comment removed for export] *)
    step. st1.                             (* [comment removed for export] *)
    step. ub_dead.                         (* [comment removed for export] *)
    step. step. step. ub_dead.             (* [comment removed for export] *)
    step. step. st1.                       (* [comment removed for export] *)
    step. ub_dead.                         (* [comment removed for export] *)
    step. step. st1.                       (* [comment removed for export] *)
    step. ub_dead.                         (* [comment removed for export] *)
    step. step. step. ub_dead.             (* [comment removed for export] *)
    step. step. step. st1.                 (* [comment removed for export] *)
    step. ub_dead.                         (* [comment removed for export] *)
    st1.                                   (* [comment removed for export] *)
    step. step. step.                      (* [comment removed for export] *)
    apply evt_done. eexists _, _, _, _, _. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    pose proof (rw_cells_bytes_at _ _ _ _ HD) as B1. pose proof (rw_cells_bytes_at _ _ _ _ TL) as B2.
    cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B2.
    lazymatch type of B1 with bytes_at _ _ _ ?hd =>
      instantiate (1 := hd ++ skipn 6 bs);
      split; [apply (proj2 (bytes_at_app _ _ _ hd (skipn 6 bs))); split; [exact B1| cbn [length]; exact B2]
            | unfold zlength; rewrite length_app, length_skipn; cbn [length]; lia] end.
  Qed.

  (* [comment removed for export] *)
  Lemma f_seg4 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => exists u0,
          ms' = MS (mkR (Z_to_bv 64 FZ_R4) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 80) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs) /\ u0 = t0)
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_R3) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold FZ_R3, FZ_R4, P_CRYPTO_free, A_FZ_FILE.
    step. step. step. step. step. step. apply evt_done. exists t0. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma f_seg5 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FZ_R5) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_clear_error) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_R4) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold FZ_R4, FZ_R5, P_ERR_clear_error.
    step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma f_seg6 :
    forall (rax sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word) (junk : list byte)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells usegs m (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra) ->
      stk usegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_R5) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI RAE. unfold FZ_R5. unfold fz_frame in FR.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. do 3 step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma parse_stack_max {HCEIL : HeapCeil} : forall M, PARSE_STACK M <= 12256.   (* [comment removed for export] *)
Proof. intros [f [|x] [|c] E v]; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma errclear_stack_max {HCEIL : HeapCeil} : forall eph, ERRCLEAR_STACK eph <= 9376.   (* [comment removed for export] *)
Proof. intros [|c]; apply Z.leb_le; vm_compute; reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bud_nonneg : forall M, 0 <= mid_bytes M /\ 0 <= mid_cnt M /\ 0 <= mid_big M.
Proof.
  intros M. unfold mid_bytes, mid_cnt, mid_big. pose proof (ctxph_nonneg (mid_ctx M)) as (A1 & A2 & A3 & _). pose proof (errph_nonneg (mid_err M)) as (B1 & B2 & B3). lia.
Qed.
(* [comment removed for export] *)
Lemma newlib_bounds : forall M M' LBN, mid_step M M' -> mid_newlib_ok M M' LBN ->
  lb_bytes LBN + mid_bytes M' <= mid_bytes M /\ Z.of_nat (length LBN) + mid_cnt M' <= mid_cnt M /\ lb_big LBN + mid_big M' <= mid_big M
  /\ lb_big LBN <= 2 /\ Z.of_nat (length LBN) <= CTXINIT_CNT + ERRINIT_CNT /\ lb_bytes LBN <= CTXINIT_BYTES + ERRINIT_BYTES.
Proof.
  intros [f cph eph E v] [f' cph' eph' E' v'] LBN ST NW. unfold mid_step, mid_newlib_ok, mid_bytes, mid_cnt, mid_big in *.
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. destruct ST as (_ & SC & SE & _). destruct NW as (LA & LE & P & C & R).
  rewrite (lb_bytes_perm _ _ P), (lb_big_perm _ _ P), (Permutation_length P), lb_bytes_app, lb_big_app, length_app, Nat2Z.inj_add.
  assert (KA : lb_bytes LA + ctxph_bytes cph' <= ctxph_bytes cph /\ Z.of_nat (length LA) + ctxph_cnt cph' <= ctxph_cnt cph
               /\ lb_big LA + ctxph_big cph' <= ctxph_big cph /\ lb_big LA <= 1 /\ Z.of_nat (length LA) <= CTXINIT_CNT /\ lb_bytes LA <= CTXINIT_BYTES).
  { destruct cph as [|b].
    - destruct cph' as [|b']; cbn [ctxph_delta ctxph_bytes ctxph_cnt ctxph_big] in C |- *.
      + subst LA. cbn. unfold CTXINIT_BYTES, CTXINIT_CNT, CTXINIT_BIG. lia.
      + unfold CTXINIT_BIG. lia.
    - cbn in C. subst LA. rewrite (SC b eq_refl). cbn. unfold CTXINIT_CNT, CTXINIT_BYTES. lia. }
  assert (KE : lb_bytes LE + errph_bytes eph' <= errph_bytes eph /\ Z.of_nat (length LE) + errph_cnt eph' <= errph_cnt eph
               /\ lb_big LE + errph_big eph' <= errph_big eph /\ lb_big LE <= 1 /\ Z.of_nat (length LE) <= ERRINIT_CNT /\ lb_bytes LE <= ERRINIT_BYTES).
  { destruct eph as [|c].
    - destruct eph' as [|c']; cbn [errph_delta errph_bytes errph_cnt errph_big] in R |- *.
      + subst LE. cbn. unfold ERRINIT_BYTES, ERRINIT_CNT, ERRINIT_BIG. lia.
      + unfold ERRINIT_BIG. lia.
    - cbn in R. subst LE. rewrite (SE c eq_refl). cbn. unfold ERRINIT_CNT, ERRINIT_BYTES. lia. }
  lia.
Qed.
Lemma newlib_nil : forall M M' LBN x c, mid_ctx M = CtxReady x -> mid_err M = ErrReady c -> mid_newlib_ok M M' LBN -> LBN = [].
Proof.
  intros [f cph eph E v] M' LBN x c HC HE NW. unfold mid_newlib_ok in NW. cbn [mid_ctx mid_err] in *. subst cph eph.
  destruct NW as (LA & LE & P & -> & ->). apply Permutation_nil. apply Permutation_sym. exact P.
Qed.
Lemma mid_step_trans : forall M0 M1 M2, mid_step M0 M1 -> mid_step M1 M2 -> mid_step M0 M2.
Proof.
  intros M0 M1 M2 (F1 & C1 & E1 & V1) (F2 & C2 & E2 & V2). unfold mid_step.
  split; [exact F2|]. split; [intros b Hb; exact (C2 b (C1 b Hb))|]. split; [intros c Hc; exact (E2 c (E1 c Hc))| intros Hv; exact (V2 (V1 Hv))].
Qed.
Lemma errph_below_of_mid {HCEIL : HeapCeil} : forall LIB m x eph lo,
  ERRPH_mid LIB m (CtxReady x) eph -> (forall b, In b LIB -> blk_addr b + blk_size b <= lo) -> errph_below eph lo.
Proof.
  intros LIB m x [|c] lo P HB; cbn [ERRPH_mid ERRPH errph_below] in *; [exact I|].
  destruct P as [_ CH]. unfold ERR_chain, chain_blocks in CH. destruct CH as (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & I6 & Z6 & RR).
  pose proof (HB _ I2) as K2. pose proof (HB _ I3) as K3. pose proof (HB _ I4) as K4. pose proof (HB _ I5) as K5.
  rewrite Z2 in K2. rewrite Z3 in K3. rewrite Z4 in K4. rewrite Z5 in K5.
  pose proof (Forall_inv RR) as (R2 & _). pose proof (Forall_inv (Forall_inv_tail RR)) as (R3 & _).
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as (R4 & _). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as (R5 & _).
  unfold chain_below. lia.
Qed.
(* [comment removed for export] *)
Lemma XF_libx : forall a, rin_ivs (memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X) a -> rin_ivs LIBX a.
Proof.
  intros a Ha. apply (proj1 (in_ivs_b_spec LIBX a)).
  unfold memflag_foot, CTX_X, ERR_X, VDSO_X in Ha. cbn [rin_ivs fst snd app] in Ha.
  unfold LIBX, LIBX0, A_mem_inited, A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_in_init_config_key, A_load_strings_once, A_optsdone_lock,
    A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_err_string_once, A_optsdone, A_td_tsd_used, A_tsd_main, A_vdso_func in *.
  cbn [in_ivs_b fst snd].
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
    repeat (rewrite Bool.orb_true_iff; first [left; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia | right]).
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  (* [comment removed for export] *)
  Hypothesis CERTA : getdefctx_fresh_stmt H.
  (* [comment removed for export] *)
  Hypothesis CERTO3 : egs_fresh_stmt H.
  (* [comment removed for export] *)
  Hypothesis RCFG : readcfg_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  (* [comment removed for export] *)
  Definition fz_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (junk : list byte)
      (LIB LB0 LBc : list block) (M0 : libmid) (D N lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (M' : libmid) (LBN : list block) (P : Z) (o : oblk),
      cfg_ms k = MS (mkR (Z_to_bv 64 FZ_R4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 P)
                       (Z_to_bv 64 A_FZ_FILE) (Z_to_bv 64 80) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_CRYPTO_free) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -32) /\ rw_cells usegs m' RERRNO [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ match o with None => P = 0 | Some (id, n) => In (id, P, n) (mid_errblocks M' ++ blocks_of P o ++ LBN ++ LB0) end
      /\ hs_RHEAP H s' (mid_errblocks M' ++ blocks_of P o ++ LBN ++ LB0) m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M0 M' /\ mid_newlib_ok M0 M' LBN /\ (exists b, mid_ctx M' = CtxReady b)
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
      /\ lb_bytes (blocks_of P o) <= 1500 /\ lb_big (blocks_of P o) = 0
      /\ rw_cells usegs m' (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra)
      /\ xpres LBc (bv_unsigned sp) LIBX m m'.

  (* [comment removed for export] *)
  Lemma LIBMID_mf_same : forall LIB Lall SP m m' M,
    LIBMID LIB m M -> mid_flag M = 1 -> xpres Lall SP memflag_foot m m' -> (forall b, In b LIB -> In b Lall) -> MEMFLAG m' 1 -> LIBMID LIB m' M.
  Proof.
    intros LIB Lall SP m m' [f cph eph E v] LM F1 XP SUB MF'. cbn [mid_flag] in F1. subst f.
    exact (LIBMID_mf LIB Lall SP m m' _ LM XP SUB MF').
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_client : forall (LBc L : list block) SP X m m' D N ds s0 L0 m0,
    hs_RHEAP H s0 L0 m0 -> (forall b, In b LBc -> In b L0) ->
    (N = 0 \/ exists pD, In (pD, D, N) LBc /\ rblock_range D N) -> Z.of_nat (length ds) = N ->
    xpres L SP X m m' -> bytes_at usegs m D ds -> (forall b, In b LBc -> In b L) ->
    Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) X -> bytes_at usegs m' D ds.
  Proof.
    intros LBc L SP X m m' D N ds s0 L0 m0 HP0 SUBC DCASE DSL XP BA SUB FX. destruct DCASE as [N0|(pD & PIN & PR)].
    - destruct ds; [| cbn in DSL; lia]. destruct BA as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros i Hi. cbn in Hi. lia.
    - eapply xpres_bytes_at; [exact XP| exact BA|]. split.
      + right; right. exists (pD, D, N). split; [apply SUB; exact PIN| cbn; lia].
      + eapply Forall_impl; [| exact FX]. intros [lo' hi'] K. cbn in K |- *. destruct PR as (_ & _ & _ & _ & PO). unfold IMG_LO, IMG_HI in K. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_top : forall (LBc Lx Lh Lall : list block) mx cph eph sh mh SPx (sp : word) mA mB X,
    ERRPH_mid Lx mx cph eph -> hs_RHEAP H sh Lh mh -> (forall b, In b Lx -> In b Lh) -> (forall b, In b LBc -> In b Lh) -> idsdisj Lx LBc ->
    hceil <= bv_unsigned sp ->
    xpres Lall SPx X mA mB -> (forall a, rin_ivs X a -> rin_ivs (memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X) a \/ rin_ivs (errph_foot eph) a) ->
    (forall b, In b LBc -> In b Lall) -> SPx <= bv_unsigned sp ->
    xpres LBc (bv_unsigned sp) LIBX mA mB.
  Proof.
    intros LBc Lx Lh Lall mx cph eph sh mh SPx sp mA mB X EPm HPh SUBx SUBc DJ CE XP XSUB SUB LE.
    eapply (xpres_drop_nonclient _ _ LIBX (errph_foot eph)).
    - eapply xpres_weaken; [exact XP| exact LE| exact SUB|]. intros a Ha. destruct (XSUB a Ha) as [K|K].
      + apply rin_ivs_app. left. apply XF_libx. exact K.
      + apply rin_ivs_app. right. exact K.
    - intros a Ha [HC _]. destruct eph as [|c]; cbn [errph_foot rin_ivs fst snd] in Ha; [exact Ha|]. destruct Ha as [Ha|[]].
      destruct cph as [|x]; cbn [ERRPH_mid ERRPH] in EPm; [destruct EPm|]. destruct EPm as [_ CH].
      pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
      pose proof (client_outside_block H HH _ _ _ (ec_es c) LBc (bv_unsigned sp) a HPh (SUBx _ I5) SUBc
                    ltac:(intros b b' Hb Hb'; destruct Hb as [<-|[]]; apply DJ; [exact I5| exact Hb']) CE HC) as K.
      rewrite Z5 in K. unfold ERRST_SIZE in *. lia.
  Qed.

  Lemma fuzz_spec : fuzz_stmt H.
  Proof.
    unfold fuzz_stmt. intros until errv.
    intros A0 A1 DS DSL NR D16 DIN DEMPTY HP KREL LST BUD BUDC BUDB AUX SPB BHI SPA ST CEIL LO ERR MI RL TP RAE.
    unfold fuzz_live, fuzz_cnt, fuzz_big, FUZZ_LIVE, TRANS_CNT, TRANS_BIG, LIB_CNT_MAX, LIB_BYTES_MAX, LIB_BIG_MAX, FUZZ_STACK in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp a0 a1. rewrite errno_RATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ DS) as [DSB1 DSB2]. rewrite DSL in DSB2.
    assert (N0 : 0 <= N) by lia.
    set (LB0 := LIB ++ LBc) in *.
    assert (SUBL : forall b, In b LIB -> In b LB0) by (intros b Hb; unfold LB0; apply in_or_app; left; exact Hb).
    assert (SUBC : forall b, In b LBc -> In b LB0) by (intros b Hb; unfold LB0; apply in_or_app; right; exact Hb).
    assert (HB := HH_blocks_below H HH _ _ _ HP). assert (ND0 := HH_RHEAP_blocks_nodup H HH _ _ _ HP).
    pose proof (nd_app LIB LBc ND0) as [DJLC _].
    assert (DCASE : N = 0 \/ exists pD, In (pD, D, N) LBc /\ rblock_range D N).
    { destruct (Z.eq_dec N 0) as [N00|N00]; [left; exact N00| right]. destruct (DIN ltac:(lia)) as [pD PIN].
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBC _ PIN)) as R. exists pD. split; [exact PIN| exact R]. }
    assert (DPH : 0 < D /\ D + N <= hceil).
    { destruct DCASE as [N00|(pD & PIN & (R1 & R2 & R3 & R4 & R5))]; [| lia]. rewrite (DEMPTY N00), N00. unfold P_FUZZ_EMPTY. lia. }
    destruct DPH as [DP DH].
    (* [comment removed for export] *)
    assert (INIT : exists M0, LIBMID LIB m M0 /\ errst_canonical (mid_E M0)
                   /\ mid_bytes M0 <= (if is_fresh st then 2^17 else 0) /\ mid_cnt M0 <= (if is_fresh st then 1800 else 0)
                   /\ mid_big M0 + 6 <= (if is_fresh st then 2 else 0) + 8             (* [comment removed for export] *)
                   /\ (is_fresh st = false -> (exists x, mid_ctx M0 = CtxReady x) /\ (exists c, mid_err M0 = ErrReady c) /\ lib_fits LIB)
                   /\ (is_fresh st = true -> LIB = [])).
    { destruct st as [|i].
      - destruct (LIBMID_fresh LIB m LST RL) as [-> LM]. exists (mkMID 0 CtxFresh ErrFresh errst_zero false).
        unfold mid_bytes, mid_cnt, mid_big. cbn [mid_E mid_ctx mid_err is_fresh ctxph_bytes errph_bytes ctxph_cnt errph_cnt ctxph_big errph_big].
        unfold CTXINIT_BYTES, ERRINIT_BYTES, CTXINIT_CNT, ERRINIT_CNT, CTXINIT_BIG, ERRINIT_BIG.
        split; [exact LM|]. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; discriminate| reflexivity].
      - destruct (LIBMID_inited LIB m i LST RL) as (E & CE & SZ & LM). exists (mkMID 1 (CtxReady (li_ctx i)) (ErrReady (li_chain i)) E (li_vdso_done i)).
        unfold mid_bytes, mid_cnt, mid_big. cbn [mid_E mid_ctx mid_err is_fresh ctxph_bytes errph_bytes ctxph_cnt errph_cnt ctxph_big errph_big].
        split; [exact LM|]. split; [exact CE|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros _; split; [eexists; reflexivity| split; [eexists; reflexivity| exact SZ]]| intros; discriminate]. }
    destruct INIT as (M0 & LM0 & CE0 & MB0 & MC0 & MG0 & INITED & FRESH).
    assert (E00 : mid_errblocks M0 = []) by (unfold mid_errblocks; apply blocks_ERRST_canonical; exact CE0).
    pose proof (bud_nonneg M0) as (NB0a & NB0b & NB0c). pose proof (parse_stack_max M0) as PS0.
    pose proof LM0 as (_ & _ & _ & EPm0 & _).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply f_seg1 with (lo := lo) (N := N); [reflexivity| lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & junk & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB0 (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (HP1 : hs_RHEAP H s LB0 m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM0 XP1 SUBL) as LM1.
    assert (DS1 : bytes_at usegs m1 D ds) by (eapply (bytes_at_client LBc); [exact HP| exact SUBC| exact DCASE| exact DSL| exact XP1| exact DS| exact SUBC| apply Forall_nil]).
    assert (XC1 : xpres LBc (bv_unsigned sp) LIBX m m1).
    { eapply xpres_weaken; [exact XP1| lia| exact SUBC| intros q Hq; destruct Hq]. }
    (* [comment removed for export] *)
    pose proof (parse_one_spec H HX CERTA RCFG) as P1. unfold parse_one_stmt in P1.
    eapply (sr_seq H HH).
    { eapply P1 with (lo := lo) (B := B) (LIB := LIB) (LB := LB0) (M := M0) (D := D) (N := N) (ds := ds) (s := s); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact DS1| exact DEMPTY| exact LM1| exact SUBL| exact KREL| exact AUX1| exact BHI| exact ST1| exact CEIL| exact MI1].
      all: lazymatch goal with
           | |- zlength _ = _ => try (exact DSL)
           | |- 1 <= _ -> _ => try (intros K; destruct (DIN K) as [pD PIN]; exists pD; split; [apply SUBC; exact PIN| intros b Hb; exact (DJLC _ _ Hb PIN)])
           | |- hs_RHEAP _ _ _ _ => try (rewrite E00; cbn [app]; exact HP1)
           | |- lb_bytes _ + _ + _ <= _ => try (rewrite E00; cbn [app]; unfold PARSE_BYTES, DECODE_BYTES, ERRSTR_BYTES; clear - BUD MB0 NB0a; destruct (is_fresh st); lia)
           | |- Z.of_nat (length _) + _ + _ <= _ => try (rewrite E00; cbn [app]; unfold PARSE_CNT, DECODE_CNT, ERRSTR_CNT; clear - BUDC MC0 NB0b; destruct (is_fresh st); lia)
           | |- lb_big _ + _ + _ <= _ => try (rewrite E00; cbn [app]; unfold PARSE_BIG, DECODE_BIG; clear - BUDB MG0 NB0c; destruct (is_fresh st); lia)
           | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR1)
           | |- _ mod 16 = 0 => try (clear - SPA SPR LO; lia)
           | |- _ <= _ - PARSE_STACK _ => try (clear - LO PS0; lia)
           | |- _ mod 2 = 0 => try (unfold FZ_R1; rewrite unsigned_lit by lia; reflexivity)
           | |- _ => try lia
           end. }
    clear P1. intros [ms2 mo2] PO. unfold parse_one_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & M1 & LBN1 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HP2 & LM2 & STEP1 & NEW1 & CTX1 & EC1 & EB1 & EG1 & DS2 & XP2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
    replace (ret_pc (Z_to_bv 64 FZ_R1)) with (Z_to_bv 64 FZ_R1) by (symmetry; apply ret_pc_even; [unfold FZ_R1; lia| reflexivity]).
    pose proof (newlib_bounds _ _ _ STEP1 NEW1) as (NL1 & NL2 & NL3 & NL4 & NL5 & NL6).
    pose proof (bud_nonneg M1) as (NB1a & NB1b & NB1c). pose proof (parse_stack_max M1) as PS1.
    set (E1 := mid_errblocks M1) in *.
    assert (HB2 := HH_blocks_below H HH _ _ _ HP2). assert (ND2 := HH_RHEAP_blocks_nodup H HH _ _ _ HP2).
    pose proof LM2 as (IM2 & MF2 & _ & EPm2 & _ & _ & _ & _ & GM2 & _). rewrite (proj1 STEP1) in MF2.
    assert (SUBA2 : forall b, In b (LBN1 ++ LIB) -> In b (E1 ++ LBN1 ++ LB0)).
    { intros b Hb. apply in_or_app. right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (SUBC2 : forall b, In b LBc -> In b (E1 ++ LBN1 ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; apply SUBC; exact Hb).
    pose proof (nd_app E1 (LBN1 ++ LB0) ND2) as [DJ2E ND2a]. pose proof (nd_app LBN1 LB0 ND2a) as [DJ2N _].
    assert (DJX2 : idsdisj (LBN1 ++ LIB) LBc).
    { intros b b' Hb Hb'. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply DJ2N; [exact Hb| apply SUBC; exact Hb']| apply DJLC; assumption]. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact FR1| left; cbn; lia|].
      assert (XB : Forall (fun iv : Z * Z => snd iv <= hceil) (memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M0))).
      { repeat (apply Forall_app; split); try (eapply Forall_impl; [| first [apply img_memflag| apply img_CTX_X| apply img_ERR_X| apply img_VDSO_X]]; intros [u v] K0; cbn in K0 |- *; unfold IMG_HI in K0; lia).
        eapply errph_foot_below; [exact EPm0| intros b Hb; exact (HB _ (SUBL _ Hb))]. }
      eapply Forall_impl; [| exact XB]. intros [u v] K. cbn in K |- *. lia. }
    assert (XC2 : xpres LBc (bv_unsigned sp) LIBX m m2).
    { eapply xpres_trans; [exact XC1|]. eapply (xpres_top LBc LIB LB0); [exact EPm0| exact HP| exact SUBL| exact SUBC| exact DJLC| lia| exact XP2| | exact SUBC| lia].
      intros q Hq. rewrite !app_assoc in Hq. apply rin_ivs_app in Hq. rewrite <- !app_assoc in Hq. exact Hq. }
    (* [comment removed for export] *)
    assert (MID : hs_SR H (fz_mid ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc junk LIB LB0 LBc M0 D N lo B m mo)
             (mkCfg (MS (mkR (Z_to_bv 64 FZ_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) u0 u1 u2 (Z_to_bv 64 N) (Z_to_bv 64 D)
                           b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 FZ_R1) fc None m2 (seg_rom usegs)) mo2)).
    { assert (CASES : (32 <= N < 1500) \/ (N < 32 \/ 1500 <= N)) by lia. destruct CASES as [GATE|GATE].
      - (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL2| eapply f_seg2a; [exact GATE| exact MI2]|]. intros ms3 (u7 & -> & _).
        destruct DCASE as [N00|(pD & PIN & PR)]; [lia|]. pose proof PR as (PR1 & _ & _ & PR4 & PR5).
        pose proof (cmemdup_spec H HH) as MD. unfold cmemdup_stmt in MD.
        eapply (sr_seq H HH).
        { eapply MD with (lo := lo) (B := B) (LB := E1 ++ LBN1 ++ LB0) (s := s2') (D := D) (bs := ds) (v := 1); unfold zlength; rewrite ?DSL; rewrite ?unsigned_lit by lia; try reflexivity.
          all: try first [exact DS2| exact HP2| exact KREL2| exact AUX2| exact ST2| exact CEIL| exact MI2| exact MF2| exact IM2| exact GM2].
          all: lazymatch goal with
               | |- xclient_range _ _ _ _ _ => try (split; [right; right; exists (pD, D, N); split; [apply SUBC2; exact PIN| cbn; lia]| apply avoid_of_img; [apply img_memflag| unfold IMG_LO, IMG_HI; lia]])
               | |- lb_bytes _ + _ <= _ => try (unfold LB0 in BUD |- *; repeat rewrite lb_bytes_app in BUD; repeat rewrite lb_bytes_app; clear - BUD MB0 NB1a NL1 EB1 GATE; unfold ERRSTR_BYTES in EB1; destruct (is_fresh st); lia)
               | |- Z.of_nat (length _) + _ <= _ => try (unfold LB0 in BUDC |- *; repeat rewrite length_app in BUDC; repeat rewrite length_app; rewrite ?Nat2Z.inj_add in BUDC; rewrite ?Nat2Z.inj_add; clear - BUDC MC0 NB1b NL2 EC1; unfold ERRSTR_CNT in EC1; destruct (is_fresh st); lia)
               | |- lb_big _ + _ <= _ => try (unfold LB0 in BUDB |- *; repeat rewrite lb_big_app in BUDB; repeat rewrite lb_big_app; rewrite big1_small by (unfold BIGB; lia); clear - BUDB MG0 NB1c NL3 EG1; destruct (is_fresh st); lia)
               | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR2)
               | |- _ <= _ - CMEMDUP_STACK => try (clear - LO; unfold CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, RMALLOC_STACK; lia)
               | |- _ => try lia
               end. }
        clear MD. intros [ms4 mo4] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & A & p & s3' &
                        -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & XP3 & BR3 & HP3 & BLK3 & MF3 & IM3 & GM3).
        unfold zlength in BR3, HP3. rewrite DSL in BR3, HP3.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST3, XP3 by lia. rewrite errno_RATP in ERR3.
        replace (ret_pc (Z_to_bv 64 FZ_R2)) with (Z_to_bv 64 FZ_R2) by (symmetry; apply ret_pc_even; [unfold FZ_R2; lia| reflexivity]).
        pose proof BR3 as (AP & _ & _ & AH & AOFF).
        pose proof (LIBMID_mf_same _ _ _ _ _ _ LM2 (proj1 STEP1) XP3 SUBA2 MF3) as LM3.
        assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra)).
        { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP3); [exact FR2| left; cbn; lia|]. apply avoid_of_img; [apply img_memflag| unfold IMG_HI; cbn; lia]. }
        assert (XC3 : xpres LBc (bv_unsigned sp) LIBX m m3).
        { eapply xpres_trans; [exact XC2|]. eapply xpres_weaken; [exact XP3| lia| exact SUBC2|]. intros q Hq. apply XF_libx. apply rin_ivs_app. left. exact Hq. }
        (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL3| eapply f_seg3 with (bs := ds); [exact GATE| exact AP| exact AH| exact DSL| exact BLK3| exact MI3]|].
        intros ms5 (c8 & c9 & c10 & c11 & m4 & bs' & -> & MU4 & WM4 & MI4 & DS4 & LEN4).
        assert (HP4 : hs_RHEAP H s3' ((p, A, N) :: E1 ++ LBN1 ++ LB0) m4).
        { eapply (HH_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4|]. apply Forall_cons; [| apply Forall_nil].
          right; right. exists (p, A, N). split; [left; reflexivity| cbn; lia]. }
        assert (AUX4 : hs_rauxv_ok H m4 B).
        { eapply (HH_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        apply (rw_cells_transport usegs _ m3 m4 _ _ ERR3) in MU4 as ERR4; [| exact WM4| unfold RERRNO; cbn; lia].
        apply (rw_cells_transport usegs _ m3 m4 _ _ FR3) in MU4 as FR4; [| exact WM4| cbn; lia].
        apply (stk_transport_disjoint usegs _ m3 m4 _ _ ST3) in MU4 as ST4; [| exact WM4| cbn; lia].
        assert (XP4 : xpres (E1 ++ LBN1 ++ LB0) (bv_unsigned sp) [] m3 m4).
        { eapply (xpres_of_munch_fresh H HH); [exact HP3| lia| exact MU4| exact WM4|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
        pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM3 XP4 SUBA2) as LM4.
        assert (XC4 : xpres LBc (bv_unsigned sp) LIBX m m4).
        { eapply xpres_trans; [exact XC3|]. eapply xpres_weaken; [exact XP4| lia| exact SUBC2| intros q Hq; destruct Hq]. }
        (* [comment removed for export] *)
        subst E1.
        pose proof (parse_one_spec H HX CERTA RCFG) as P2. unfold parse_one_stmt in P2.
        eapply (sr_seq H HH).
        { eapply P2 with (lo := lo) (B := B) (LIB := LBN1 ++ LIB) (LB := (p, A, N) :: LBN1 ++ LB0) (M := M1) (D := A) (N := N) (ds := bs') (s := s3');
            rewrite ?unsigned_lit by lia; try reflexivity.
          all: try first [exact DS4| exact LEN4| exact LM4| exact KREL3| exact AUX4| exact BHI| exact ST4| exact CEIL| exact MI4].
          all: lazymatch goal with
               | |- 1 <= _ -> _ => try (intros _; exists p; split; [left; reflexivity| intros b Hb; apply not_eq_sym; apply (nodup_ids_cons_ne (p, A, N) _ b (HH_RHEAP_blocks_nodup H HH _ _ _ HP4)); apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; unfold LB0; apply in_or_app; left; exact Hb]])
               | |- _ = 0 -> _ => try (intros K; exfalso; clear - K GATE; lia)
               | |- forall b, In b _ -> In b _ => try (intros b Hb; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb])
               | |- hs_RHEAP _ _ _ _ => try (eapply PERM; [exact HP4| apply Permutation_middle])
               | |- lb_bytes _ + _ + _ <= _ => try (unfold LB0 in BUD |- *; repeat rewrite lb_bytes_app in BUD; rewrite lb_bytes_app, lb_bytes_cons; repeat rewrite lb_bytes_app; cbn [blk_size snd]; unfold PARSE_BYTES, DECODE_BYTES, ERRSTR_BYTES in *;
                                                   clear - BUD MB0 NB1a NL1 EB1 GATE; destruct (is_fresh st); lia)
               | |- Z.of_nat (length _) + _ + _ <= _ => try (unfold LB0 in BUDC |- *; repeat rewrite length_app in BUDC; rewrite length_app; cbn [length]; repeat rewrite length_app; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ, ?Nat2Z.inj_add in BUDC |- *;
                                                             unfold PARSE_CNT, DECODE_CNT, ERRSTR_CNT in *; clear - BUDC MC0 NB1b NL2 EC1; destruct (is_fresh st); lia)
               | |- lb_big _ + _ + _ <= _ => try (unfold LB0 in BUDB |- *; repeat rewrite lb_big_app in BUDB; rewrite lb_big_app, lb_big_cons; repeat rewrite lb_big_app; cbn [blk_size snd]; rewrite big1_small by (unfold BIGB; lia);
                                                 unfold PARSE_BIG, DECODE_BIG in *; clear - BUDB MG0 NB1c NL3 EG1; destruct (is_fresh st); lia)
               | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR4)
               | |- _ mod 16 = 0 => try (clear - SPA SPR LO; lia)
               | |- _ <= _ - PARSE_STACK _ => try (clear - LO PS1; lia)
               | |- _ mod 2 = 0 => try (unfold FZ_R3; rewrite unsigned_lit by lia; reflexivity)
               | |- _ => try lia
               end. }
        clear P2. intros [ms6 mo6] PO. unfold parse_one_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m5 & errv5 & s5' & M2 & LBN2 &
                        -> & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5 & HP5 & LM5 & STEP2 & NEW2 & CTX2 & EC2 & EB2 & EG2 & DS5 & XP5).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia. rewrite errno_RATP in ERR5.
        replace (ret_pc (Z_to_bv 64 FZ_R3)) with (Z_to_bv 64 FZ_R3) by (symmetry; apply ret_pc_even; [unfold FZ_R3; lia| reflexivity]).
        pose proof LM4 as (_ & _ & _ & EPm4 & _).
        assert (HB4 := HH_blocks_below H HH _ _ _ HP4). assert (ND4 := HH_RHEAP_blocks_nodup H HH _ _ _ HP4).
        assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra)).
        { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP5); [exact FR4| left; cbn; lia|].
          assert (XB : Forall (fun iv : Z * Z => snd iv <= hceil) (memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M1))).
          { repeat (apply Forall_app; split); try (eapply Forall_impl; [| first [apply img_memflag| apply img_CTX_X| apply img_ERR_X| apply img_VDSO_X]]; intros [u v] K0; cbn in K0 |- *; unfold IMG_HI in K0; lia).
            eapply errph_foot_below; [exact EPm4| intros b Hb; apply HB4; right; exact (SUBA2 _ Hb)]. }
          eapply Forall_impl; [| exact XB]. intros [u v] K. cbn in K |- *. lia. }
        assert (XC5 : xpres LBc (bv_unsigned sp) LIBX m m5).
        { eapply xpres_trans; [exact XC4|].
          eapply (xpres_top LBc (LBN1 ++ LIB) ((p, A, N) :: mid_errblocks M1 ++ LBN1 ++ LB0)); [exact EPm4| exact HP4| intros b Hb; right; exact (SUBA2 _ Hb)| intros b Hb; right; exact (SUBC2 _ Hb)| exact DJX2| lia| exact XP5| | intros b Hb; right; apply in_or_app; right; apply SUBC; exact Hb| lia].
          intros q Hq. rewrite !app_assoc in Hq. apply rin_ivs_app in Hq. rewrite <- !app_assoc in Hq. exact Hq. }
        (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL5| eapply f_seg4; exact MI5|]. intros ms7 (u8 & -> & _).
        apply (sr_done H HH). unfold fz_mid. cbn [cfg_ms cfg_model].
        exists x0, x1, x2, e3, e4, e5, e6, e7, x3, x4, x5, x6, m5, errv5, s5', M2, (LBN2 ++ LBN1), A, (Some (p, N)).
        split; [reflexivity|]. split; [exact KREL5|].
        split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP3| exact MP5]]|].
        split; [exact MI5|]. split; [exact ST5|]. split; [exact ERR5|]. split; [exact AUX5|].
        split; [cbn [blocks_of]; apply in_or_app; right; left; reflexivity|].
        split. { eapply PERM; [exact HP5|]. cbn [blocks_of]. apply Permutation_app_head. rewrite <- !app_assoc. change ((p, A, N) :: LBN1 ++ LB0) with ([(p, A, N)] ++ LBN1 ++ LB0).
                 apply (Permutation_app_swap_app LBN2 [(p, A, N)]). }
        split; [rewrite <- app_assoc; exact LM5|].
        split; [eapply mid_step_trans; [exact STEP1| exact STEP2]|].
        split; [eapply mid_newlib_ok_trans; [exact STEP1| exact NEW1| exact STEP2| exact NEW2]|].
        split; [exact CTX2|]. split; [exact EC2|]. split; [exact EB2|]. split; [exact EG2|].
        split; [cbn; lia|]. split; [cbn [blocks_of lb_big fold_right blk_size snd]; rewrite big1_small by (unfold BIGB; lia); reflexivity|].
        split; [exact FR5| exact XC5].
      - (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL2| eapply f_seg2b; [lia| exact GATE| exact MI2]|]. intros ms3 (u7 & -> & _).
        apply (sr_done H HH). unfold fz_mid. cbn [cfg_ms cfg_model].
        exists u0, u1, u2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, s2', M1, LBN1, 0, None.
        split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|].
        split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
        split; [reflexivity|].
        split; [cbn [blocks_of app]; exact HP2|].
        split; [exact LM2|]. split; [exact STEP1|]. split; [exact NEW1|]. split; [exact CTX1|]. split; [exact EC1|]. split; [exact EB1|]. split; [exact EG1|].
        split; [cbn; lia|]. split; [reflexivity|]. split; [exact FR2| exact XC2]. }
    (* [comment removed for export] *)
    clear XC2 FR2 DS2 XP2 HP2 LM2 EPm2 SUBA2 SUBC2 DJ2E DJ2N DJX2 IM2 MF2 GM2 HB2 ND2 ST2 ERR2 AUX2 MI2 KREL2.
    eapply (sr_seq H HH); [exact MID|]. clear MID. intros [ms8 mo8] PO. unfold fz_mid in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & errv6 & s6' & M2 & LBN & P & o &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & OIN & HP6 & LM6 & STEP6 & NEW6 & (bx & CTX6) & EC6 & EB6 & EG6 & PB & PG & FR6 & XC6).
    set (E2 := mid_errblocks M2) in *. set (BO := blocks_of P o) in *. set (L6 := E2 ++ BO ++ LBN ++ LB0) in *.
    pose proof LM6 as (IM6 & MF6 & CP6 & EPm6 & EX6 & _ & _ & FIT6 & GM6 & _ & _ & _ & _ & _ & RL6). rewrite (proj1 STEP6) in MF6. rewrite CTX6 in CP6, EPm6.
    pose proof (newlib_bounds _ _ _ STEP6 NEW6) as (ML1 & ML2 & ML3 & ML4 & ML5 & ML6).
    pose proof (bud_nonneg M2) as (NB2a & NB2b & NB2c).
    assert (HB6 := HH_blocks_below H HH _ _ _ HP6). assert (ND6 := HH_RHEAP_blocks_nodup H HH _ _ _ HP6).
    pose proof (nd_app E2 (BO ++ LBN ++ LB0) ND6) as [DJ6E ND6a]. pose proof (nd_app BO (LBN ++ LB0) ND6a) as [DJ6B ND6b]. pose proof (nd_app LBN LB0 ND6b) as [DJ6N _].
    assert (SUBA6 : forall b, In b (LBN ++ LIB) -> In b (LBN ++ LB0)).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply SUBL; exact Hb]. }
    assert (DJX6 : idsdisj (LBN ++ LIB) LBc).
    { intros b b' Hb Hb'. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply DJ6N; [exact Hb| apply SUBC; exact Hb']| apply DJLC; assumption]. }
    (* [comment removed for export] *)
    pose proof (cfree_opt_spec H HH) as CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := L6) (s := s6') (P := P) (o := o) (errv := errv6); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP6| exact KREL6| exact AUX6| exact ST6| exact CEIL| exact MI6| exact IM6| exact GM6].
      all: lazymatch goal with
           | |- match _ with _ => _ end => try (unfold L6, BO; exact OIN)
           | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR6)
           | |- _ <= _ - CFREE_STACK => try (clear - LO; unfold CFREE_STACK, RFREE_STACK; lia)
           | |- _ => try lia
           end. }
    clear CF. intros [ms9 mo9] PO. unfold cfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m7 & s7' & LB7 &
                    -> & KREL7 & MP7 & MI7 & ST7 & ERR7 & AUX7 & PERM7 & SUB7 & XP7 & HP7 & IM7 & GM7).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST7, XP7 by lia. rewrite errno_RATP in ERR7.
    replace (ret_pc (Z_to_bv 64 FZ_R4)) with (Z_to_bv 64 FZ_R4) by (symmetry; apply ret_pc_even; [unfold FZ_R4; lia| reflexivity]).
    assert (P7 : Permutation LB7 (E2 ++ LBN ++ LB0)).
    { apply (Permutation_app_inv_l BO). transitivity L6; [exact PERM7|]. unfold L6. apply Permutation_app_swap_app. }
    assert (KEEP7 : forall b, In b (E2 ++ LBN ++ LB0) -> In b LB7).
    { intros b Hb. eapply perm_in_rest; [exact PERM7| unfold L6; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb]|].
      intros K. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - exact (DJ6E _ _ Hb ltac:(apply in_or_app; left; exact K) eq_refl).
      - exact (DJ6B _ _ K Hb eq_refl). }
    assert (HB7 := HH_blocks_below H HH _ _ _ HP7).
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM6 XP7 ltac:(intros b Hb; apply KEEP7; apply in_or_app; right; exact (SUBA6 _ Hb))) as LM7.
    pose proof LM7 as (_ & MF7 & CP7 & EPm7 & EX7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & RL7). rewrite (proj1 STEP6) in MF7. rewrite CTX6 in CP7, EPm7.
    assert (FR7 : rw_cells usegs m7 (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP7); [exact FR6| left; cbn; lia| apply Forall_nil]. }
    assert (XC7 : xpres LBc (bv_unsigned sp) LIBX m m7).
    { eapply xpres_trans; [exact XC6|]. eapply xpres_weaken; [exact XP7| lia| intros b Hb; apply KEEP7; apply in_or_app; right; apply in_or_app; right; apply SUBC; exact Hb| intros q Hq; destruct Hq]. }
    assert (HP7' : hs_RHEAP H s7' (blocks_ERRST (mid_E M2) ++ LBN ++ LB0) m7) by (eapply PERM; [exact HP7| exact P7]).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL7| eapply f_seg5; exact MI7|]. intros ms10 ->.
    (* [comment removed for export] *)
    pose proof (C4_spec H HX CERTO3) as C4S. destruct C4S as (_ & _ & _ & _ & _ & EC). unfold errclear_stmt in EC.
    eapply (sr_seq H HH).
    { eapply EC with (lo := lo) (B := B) (LB := LBN ++ LB0) (s := s7') (ph := mid_err M2) (E := mid_E M2) (x := bx) (errv := errv6); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP7'| exact KREL7| exact AUX7| exact ST7| exact CEIL| exact MI7| exact MF7| exact IM7| exact GM7| exact RL7| exact EX7| exact CP7].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => try (change (blocks_ERRST (mid_E M2)) with E2; unfold LB0 in BUD |- *; repeat rewrite lb_bytes_app in BUD; repeat rewrite lb_bytes_app; unfold mid_bytes in ML1, MB0; rewrite CTX6 in ML1; cbn [ctxph_bytes] in ML1;
                                           unfold ERRSTR_BYTES in EB6; clear - BUD MB0 ML1 EB6 NB0a; pose proof (ctxph_nonneg (mid_ctx M0)) as (? & _); destruct (is_fresh st); lia)
           | |- Z.of_nat (length _) + _ <= _ => try (change (blocks_ERRST (mid_E M2)) with E2; unfold LB0 in BUDC |- *; repeat rewrite length_app in BUDC; repeat rewrite length_app; rewrite ?Nat2Z.inj_add in BUDC; rewrite ?Nat2Z.inj_add; unfold mid_cnt in ML2, MC0; rewrite CTX6 in ML2; cbn [ctxph_cnt] in ML2;
                                                     unfold ERRSTR_CNT in EC6; clear - BUDC MC0 ML2 EC6; pose proof (ctxph_nonneg (mid_ctx M0)) as (_ & ? & _); destruct (is_fresh st); lia)
           | |- lb_big _ + _ <= _ => try (change (blocks_ERRST (mid_E M2)) with E2; unfold LB0 in BUDB |- *; repeat rewrite lb_big_app in BUDB; repeat rewrite lb_big_app; unfold mid_big in ML3, MG0; rewrite CTX6 in ML3; cbn [ctxph_big] in ML3;
                                         clear - BUDB MG0 ML3 EG6; pose proof (ctxph_nonneg (mid_ctx M0)) as (_ & _ & ? & _); destruct (is_fresh st); lia)
           | |- rw_cells _ _ _ [C4 _] => try (rewrite errno_RATP; exact ERR7)
           | |- _ mod 16 = 0 => try (clear - SPA SPR LO; lia)
           | |- _ <= _ - ERRCLEAR_STACK _ => try (pose proof (errclear_stack_max (mid_err M2)) as K; clear - LO K; lia)
           | |- _ <= _ - ERRCLEAR_STACK _ - 64 => try (pose proof (errclear_stack_max (mid_err M2)) as K; clear - LO K; lia)   (* [comment removed for export] *)
           | |- ERRPH _ _ _ => try (eapply ERRPH_mono; [exact EPm7| exact SUBA6])
           | |- errph_below _ _ => try (eapply errph_below_of_mid; [exact EPm7| intros b Hb; pose proof (HB7 _ (KEEP7 _ (in_or_app _ _ _ (or_intror (SUBA6 _ Hb))))); lia])
           | |- CTXPH _ _ _ => try (eapply ECH_LibMid.CTXPH_mono; [exact CP7| exact SUBA6])
           | |- _ mod 2 = 0 => try (unfold FZ_R5; rewrite unsigned_lit by lia; reflexivity)
           | |- _ => try lia
           end. }
    clear EC. intros [ms11 mo11] PO. unfold errclear_post, c4_frame in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m8 & errv8 & s8' & LBN3 & c &
                    -> & MP8 & (KREL8 & MI8 & ST8 & AUX8 & HP8 & MF8 & IM8 & GM8 & RL8) & ERR8 & ED8 & EP8 & CP8 & ES8 & XP8).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST8, XP8 by lia. rewrite errno_RATP in ERR8.
    replace (ret_pc (Z_to_bv 64 FZ_R5)) with (Z_to_bv 64 FZ_R5) by (symmetry; apply ret_pc_even; [unfold FZ_R5; lia| reflexivity]).
    set (M3 := mkMID 1 (CtxReady bx) (ErrReady c) errst_cleared (mid_vdso M2)).
    assert (LM8 : LIBMID (LBN3 ++ LBN ++ LIB) m8 M3).
    { eapply LIBMID_errcall; [exact LM7| exact CTX6| exact XP8| exact SUBA6| exact CP8| exact EP8| exact ED8| rewrite blocks_ERRST_cleared; exact ES8| exact errst_fits_cleared| exact MF8]. }
    assert (FR8 : rw_cells usegs m8 (bv_unsigned sp + -32) (fz_frame junk s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact FR7| left; cbn; lia|].
      apply Forall_app. split; [apply avoid_of_img; [apply img_ERR_X| unfold IMG_HI; cbn; lia]|].
      eapply Forall_impl; [| eapply errph_foot_below; [exact EPm7| intros b Hb; exact (HB7 _ (KEEP7 _ (in_or_app _ _ _ (or_intror (SUBA6 _ Hb)))))]].
      intros [u v] K. cbn in K |- *. lia. }
    assert (XC8 : xpres LBc (bv_unsigned sp) LIBX m m8).
    { eapply xpres_trans; [exact XC7|].
      eapply (xpres_top LBc (LBN ++ LIB) LB7); [exact EPm7| exact HP7| intros b Hb; apply KEEP7; apply in_or_app; right; exact (SUBA6 _ Hb)| intros b Hb; apply KEEP7; apply in_or_app; right; apply in_or_app; right; apply SUBC; exact Hb| exact DJX6| lia| exact XP8| | intros b Hb; apply in_or_app; right; apply SUBC; exact Hb| lia].
      intros q Hq. apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [left| right; exact Hq]. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; left. exact Hq. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL8| eapply f_seg6 with (lo := lo); [exact FR8| exact ST8| exact CEIL| lia| exact MI8| exact RAE]|].
    intros ms12 [-> ST8r].
    (* [comment removed for export] *)
    assert (STEP3 : mid_step M2 M3).
    { unfold mid_step, M3. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; rewrite CTX6 in Hb; exact Hb|].
      split; [| intros Hv; exact Hv]. intros c0 Hc. rewrite Hc in ED8. cbn [errph_delta] in ED8. destruct ED8 as [-> _]. reflexivity. }
    assert (NEW3 : mid_newlib_ok M2 M3 LBN3).
    { unfold mid_newlib_ok, M3. cbn [mid_ctx mid_err]. rewrite CTX6. exists [], LBN3. split; [apply Permutation_refl|]. split; [reflexivity|].
      destruct (mid_err M2) as [|c0]; [exact ED8|]. cbn [errph_delta] in ED8. destruct ED8 as [_ E3]. exact E3. }
    pose proof (mid_step_trans _ _ _ STEP6 STEP3) as STEPT. pose proof (mid_newlib_ok_trans _ _ _ _ _ STEP6 NEW6 STEP3 NEW3) as NEWT.
    pose proof (newlib_bounds _ _ _ STEPT NEWT) as (_ & _ & _ & TB4 & TB5 & TB6).
    assert (FITS : lib_fits ((LBN3 ++ LBN) ++ LIB) /\ (is_fresh st = false -> (LBN3 ++ LBN) ++ LIB = LIB)).
    { destruct (is_fresh st) eqn:FS.
      - rewrite (FRESH eq_refl). rewrite app_nil_r. split; [| intros; discriminate].
        unfold lib_fits. unfold CTXINIT_CNT, ERRINIT_CNT, CTXINIT_BYTES, ERRINIT_BYTES in TB5, TB6. lia.
      - destruct (INITED eq_refl) as ((x0 & CX0) & (c0 & CE0') & SZ). rewrite (newlib_nil _ _ _ _ _ CX0 CE0' NEWT). cbn [app]. split; [exact SZ| reflexivity]. }
    destruct FITS as [FITS LIBEQ].
    apply (sr_done H HH). unfold fuzz_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, h1, h2, h3, h4, h5, h6, h7, z3, z4, z5, z6, m8, errv8, s8', ((LBN3 ++ LBN) ++ LIB), LBc, (Inited (mkLI bx c (mid_vdso M2))).
    split; [reflexivity|]. split; [exact KREL8|].
    split; [eapply (mpres_trans H HH); [exact MP6| eapply (mpres_trans H HH); [exact MP7| exact MP8]]|].
    split; [exact MI8|]. split; [exact RL8|]. split; [exact ST8r|]. split; [rewrite errno_RATP; exact ERR8|]. split; [exact AUX8|].
    split; [unfold LB0 in HP8; rewrite <- !app_assoc; exact HP8|].
    split; [apply Permutation_refl|].
    split; [eapply LIBST_of_mid; [rewrite <- app_assoc; exact LM8| right; reflexivity| exact FITS]|].
    split; [reflexivity|].
    unfold lib_fits in FITS. unfold LIB_CNT_MAX, LIB_BYTES_MAX, LIB_BIG_MAX. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact LIBEQ| exact XC8].
  Qed.
End W.
