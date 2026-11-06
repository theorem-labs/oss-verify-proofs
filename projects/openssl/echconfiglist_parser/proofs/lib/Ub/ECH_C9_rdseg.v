(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_B64 ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C6_acc ECH_C7_read ECH_C7_rd2 ECH_C9_ctrl ECH_C9_rdfacts ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RD_RA_READ : Z := 0x2b4860.    (* [comment removed for export] *)
Definition RD_RA_TF1 : Z := 0x2b48f4.     (* [comment removed for export] *)
Definition RD_RA_DU : Z := 0x2b4ad4.      (* [comment removed for export] *)
Definition RD_RA_MC : Z := 0x2b4b08.      (* [comment removed for export] *)
Definition RD_RA_TF2 : Z := 0x2b4884.     (* [comment removed for export] *)
Definition RD_RA_DF : Z := 0x2b48a4.      (* [comment removed for export] *)
Definition RD_RA_DI2 : Z := 0x2b48b8.     (* [comment removed for export] *)
Definition RD_RA_CNR : Z := 0x2b4b8c.     (* [comment removed for export] *)
Definition RD_HEAD : Z := 0x2b481c.
Definition RD_EXIT : Z := 0x2b4b80.

(* [comment removed for export] *)
Definition rdframe (ctx mb a vout voutl vret vrc : Z) (j0 j8 : list byte) (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 voutl); C8 (Z_to_bv 64 vret); C8 (Z_to_bv 64 vout); C8 (Z_to_bv 64 vrc); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 mb);
   C8 (Z_to_bv 64 (ctx + 40)); C8 (Z_to_bv 64 (18446744073709551615 - (ctx + 1542))); C8 (Z_to_bv 64 (ctx + 1542)); CB 8 j8;
   C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].
(* [comment removed for export] *)
Definition rdhdr (bl bo tl c enc : Z) : list cell :=
  [C4 (wz bl); C4 (wz bo); C4 (wz tl); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz enc)].

(* [comment removed for export] *)
Lemma unsigned_neg64 : forall c, - 2^64 <= c < 0 -> bv_unsigned (Z_to_bv 64 c) = c + 2^64.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  replace c with ((c + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma shiftr32_small : forall z, 0 <= z < 2^32 -> Z.shiftr z 32 = 0.
Proof. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_mod64 : forall x, bv_swrap 32 (x mod 2^64) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap. f_equal. unfold bv_wrap.
  change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_eq x (2^64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64) + bv_half_modulus 32) with ((x + bv_half_modulus 32) + (- (4294967296 * (x / 2 ^ 64))) * 4294967296) by lia.
  apply Z.mod_add. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_lw_C8 : forall m A cs k z,
  rw_cells usegs m A cs -> nth_error cs k = Some (C8 (Z_to_bv 64 z)) -> 0 <= z < 2^32 ->
  ov_read_bytes usegs m (Z_to_bv 64 (A + Z.of_nat (cells_size (firstn k cs)))) 4 = Some (le4 (Z_to_bv 64 z)).
Proof.
  intros m A cs k z H N R.
  destruct (nth_error_split cs k _ N) as (l1 & l2 & E & L).
  rewrite E in H. rewrite E, <- L, firstn_app_exact.
  apply (rw_cells_C8_C4C4 usegs m A l1 z l2) in H; [| lia]. rewrite (shiftr32_small z) in H by lia.
  apply rw_cells_app in H. destruct H as [_ H].
  pose proof (rw_cells_read_at usegs m _ _ 0%nat (C4 (wz z)) 4 _ H eq_refl eq_refl eq_refl) as RD.
  cbn [cbytes] in RD. rewrite <- RD. unfold wa, wz. f_equal. f_equal. lia.
Qed.
Ltac lwslot FR k z :=
  let HR := fresh "HR" in
  pose proof (rw_cells_lw_C8 _ _ _ k z FR eq_refl ltac:(lia)) as HR;
  cbn [firstn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HR.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac killb K :=
    first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; apply Z.ltb_lt in K'; exfalso; revert K K'; rewrite ?unsigned_lit, ?signed_lit by lia; lia
          | exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia ].
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].

  (* [comment removed for export] *)
  Lemma rd_head :
    forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl vout voutl vret vrc bl bo c enc lo : Z) (j0 j8 : list byte),
      0 < c < 2^31 -> 0 <= out < 2^64 -> 0 <= outl < 2^64 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a vout voutl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 RD_RA_READ) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 mb)
                       (Z_to_bv 64 mb) (Z_to_bv 64 (ctx + 1542)) (Z_to_bv 64 1024) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 out) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 out) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_HEAD) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros C OUT OUTL CP CL FR HD ST LO MI. hcb.
    unfold RD_HEAD, RD_RA_READ, P_BIO_read, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    st1. st1.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit c) by lia. step. if_cases Kb; zify_cond Kb; [killb Kb|]; try clear Kb.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 0) by lia. step. step. if_lit.
    st1. step. fbr.
    (* [comment removed for export] *)
    st1. step. step. step.
    st1. step. step. step.
    replace (Z_to_bv 64 (ctx + 1542 + 0)) with (Z_to_bv 64 (ctx + 1542)) by (f_equal; lia).
    finish.
    all: match goal with |- ?G => idtac "HEAD-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_head_exit :
    forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl vout voutl vret vrc bl bo c enc lo : Z) (j0 j8 : list byte),
      - 2^31 <= c <= 0 -> 0 <= out < 2^64 -> 0 <= outl < 2^64 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a vout voutl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 a0',
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1
                       a0' a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 out) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RD_EXIT) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 out) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_HEAD) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros C OUT OUTL CP CL FR HD ST LO MI. hcb.
    unfold RD_HEAD, RD_EXIT, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    st1. st1.
    st1. step. if_cases Kb; zify_cond Kb.
    2:{ exfalso. rewrite (sx32_wz_small c) in * by lia. destruct (Z.eq_dec c 0) as [E0|NZ].
        - rewrite E0 in *. rewrite unsigned_lit in * by lia. lia.
        - rewrite (unsigned_neg64 c) in * by lia. lia. }
    clear Kb.
    finish.
    all: match goal with |- ?G => idtac "HEADX-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_data1 :
    forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (B : biorep) (ctx mb a out outl vret vrc n bl bo c enc lo : Z) (j0 j8 : list byte),
      0 < n <= 1024 -> 0 < a -> a + BIO_SIZE <= lo -> a mod 8 = 0 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo -> (a + BIO_SIZE <= ctx \/ ctx + B64CTX_SIZE <= a) ->
      0 <= bio_flags B < 2^31 -> Z.land (bio_flags B) BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL ->
      rw_cells usegs m a (bio_cells B) ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> hceil <= lo -> lo <= bv_unsigned sp + -192 - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 t0' t1' t2' a5' a6' a7' t3' t4' t5' t6',
          ms' = MS (mkR (Z_to_bv 64 RD_RA_DU) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0' t1' t2' sp (Z_to_bv 64 n)
                       (Z_to_bv 64 enc) (Z_to_bv 64 (ctx + 40)) (Z_to_bv 64 ctx) (Z_to_bv 64 (ctx + 1542)) (Z_to_bv 64 n) a5' a6' a7'
                       (Z_to_bv 64 ctx) (Z_to_bv 64 0) (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 n) (Z_to_bv 64 n) s11
                       t3' t4' t5' t6')
                   F (Z_to_bv 64 P_EVP_DecodeUpdate) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192 - 16, bv_unsigned sp + -192); (ctx, ctx + 40)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 a (bio_cells B)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 out) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_READ) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros N AP AL AAL CP CL AC FLR NONL BC FR HD ST CEIL LO MI. hcb.
    unfold RD_RA_READ, RD_RA_DU, P_EVP_DecodeUpdate, B64CTX_SIZE, BIO_SIZE, BIO_FLAGS_BASE64_NO_NL in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192 - 16, bv_unsigned sp + -192); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    unfold bio_cells, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    (* [comment removed for export] *)
    step. step. if_cases Kb; zify_cond Kb; [killb Kb|]; try clear Kb.
    st1. rewrite ?(sx32_lit 0) by lia. step. step.
    (* [comment removed for export] *)
    zstep. rewrite ?Z.add_0_r. rewrite (swrap32_small n) by lia.
    zstep. rewrite ?Z.add_0_r.
    step. fbr.
    st1. rewrite ?(sx32_lit 1) by lia. st1. step. if_lit.
    (* [comment removed for export] *)
    step. st1. step. step.
    carve_frame 16%nat ST. st1. st1. do 2 st1.
    (* [comment removed for export] *)
    step. fbr. step. ubal_by AAL. step. if_lit.
    st1. rewrite ?sx32_lit by lia.
    zstep. rewrite ?(unsigned_lit (bio_flags B)) by lia. rewrite land_ones64 by lia.
    do 4 step. release_frame FR0 ST (bv_unsigned sp + -192).
    (* [comment removed for export] *)
    zstep. rewrite NONL. step. if_cases Kb; zify_cond Kb; [| killb Kb]; try clear Kb.
    (* [comment removed for export] *)
    st1. st1. st1. step. st1. step. step.
    finish.
    all: match goal with |- ?G => idtac "D1-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_du_neg :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl vret vrc k bl bo c enc lo : Z) (j0 j8 : list byte),
      - 2^31 <= k < 0 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 RD_RA_DU) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RD_EXIT) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret 0 j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr 0 0 0 k enc))
        (MS (mkR (Z_to_bv 64 RD_RA_DU) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_DU) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros K CP CL FR HD ST LO MI. hcb.
    unfold RD_RA_DU, RD_EXIT, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    st1. st1. st1.
    step. if_cases KK; zify_cond KK.
    2:{ exfalso. revert KK. rewrite ?(unsigned_neg64 k) by lia. lia. }
    clear KK.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 1) by lia. step. step. zstep.
    change (Z.land _ (k mod 18446744073709551616)) with 0.
    st1. st1.
    finish.
    all: match goal with |- ?G => idtac "DUN-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_du_pos :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl vret vrc k bl bo c enc lo : Z) (j0 j8 : list byte),
      0 <= k < 2^31 -> 0 <= bl < 2^31 -> 0 < outl < 2^31 -> 0 <= out < 2^64 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 RD_RA_MC) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 bl)
                       (Z_to_bv 64 out) (Z_to_bv 64 (ctx + 40)) (Z_to_bv 64 (Z.min bl outl)) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 (Z.min bl outl)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_memcpy) fc None m1 (seg_rom usegs)
          /\ munch [(ctx, ctx + 40)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl 0 0 k enc))
        (MS (mkR (Z_to_bv 64 RD_RA_DU) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_DU) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros K BL OUTL OUT CP CL FR HD ST LO MI. hcb.
    unfold RD_RA_DU, RD_RA_MC, P_memcpy, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(ctx, ctx + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    st1. st1. st1.
    step. if_cases KK; zify_cond KK; [killb KK|]; try clear KK.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit bl) by lia.
    lwslot FR 1%nat outl. st1. clear HR. rewrite ?(sx32_lit outl) by lia.
    step. step. if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - (* [comment removed for export] *) replace (Z.min bl outl) with bl by lia.
      st1. st1. step. step. finish.
    - (* [comment removed for export] *) step. replace (Z.min bl outl) with outl by lia.
      st1. st1. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_mc_loop :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl ret vrc bl k enc lo : Z) (j0 j8 : list byte),
      0 <= bl < outl -> outl < 2^31 -> 0 <= ret -> ret + outl < 2^31 -> 0 < out -> out + outl < 2^64 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl ret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl 0 0 k enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 a0' a1',
          ms' = MS (mkR (Z_to_bv 64 RD_RA_MC) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 bl)
                       a0' a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) s3 (Z_to_bv 64 (outl - bl)) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 (out + bl)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RD_HEAD) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl (ret + bl) vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr 0 0 0 k enc))
        (MS (mkR (Z_to_bv 64 RD_RA_MC) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 bl)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 bl) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_MC) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros BL OUTL RET RETO OUT OUTO CP CL FR HD ST LO MI. hcb.
    unfold RD_RA_MC, RD_HEAD, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    lwslot FR 2%nat ret. st1. clear HR. rewrite ?(sx32_lit ret) by lia.
    zstep. zstep. rewrite (swrap32_small (ret + bl)) by lia.
    st1. step. fbr.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit bl) by lia. st1.
    step. if_cases KK; zify_cond KK; [killb KK|]; try clear KK.
    apply (rw_cells_merge usegs _ ctx [] [C4 (Z_to_bv 64 bl); C4 (Z_to_bv 64 bl)]) in HD. cbn [app cells_size csize cells_bytes cbytes Nat.add] in HD.
    st1.
    match goal with H : rw_cells usegs _ ctx _ |- _ => apply (rw_cells_C8_C4C4 usegs _ ctx [] 0) in H; [cbn [app Z.shiftr] in H| lia] end.
    (* [comment removed for export] *)
    lwslot FR 1%nat outl. st1. clear HR. rewrite ?(sx32_lit outl) by lia.
    zstep. rewrite (swrap32_small (outl - bl)) by lia. zstep. step. fbr.
    (* [comment removed for export] *)
    st1. zstep. replace (bl + out) with (out + bl) by lia. step. fbr.
    st1. zstep. zstep. zstep. zstep. ub_b2z. change (Z.lxor (Z.lxor 0 0) 1) with 1. step. if_lit.
    (* [comment removed for export] *)
    step. if_cases KK; zify_cond KK; [| killb KK]; try clear KK.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_mc_done :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl ret vrc bl k enc lo : Z) (j0 j8 : list byte),
      0 < outl <= bl -> bl < 2^31 -> 0 <= ret -> ret + outl < 2^31 -> 0 < out -> out + outl < 2^64 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl ret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl 0 0 k enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 a0' a1',
          ms' = MS (mkR (Z_to_bv 64 RD_RA_MC) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 bl)
                       a0' a1' a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) s3 (Z_to_bv 64 0) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 (out + outl)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RD_EXIT) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl (ret + outl) vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr (if bl =? outl then 0 else bl) (if bl =? outl then 0 else outl) 0 k enc))
        (MS (mkR (Z_to_bv 64 RD_RA_MC) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 bl)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 outl) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_MC) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros BL BLH RET RETO OUT OUTO CP CL FR HD ST LO MI. hcb.
    unfold RD_RA_MC, RD_EXIT, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    lwslot FR 2%nat ret. st1. clear HR. rewrite ?(sx32_lit ret) by lia.
    zstep. zstep. rewrite (swrap32_small (ret + outl)) by lia.
    st1. step. fbr.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit bl) by lia. st1.
    step. if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - (* [comment removed for export] *)
      replace (bl =? outl) with false by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      lwslot FR 1%nat outl. st1. clear HR. rewrite ?(sx32_lit outl) by lia.
      zstep. rewrite (swrap32_small (outl - outl)) by lia. zstep. step. fbr.
      st1. zstep. replace (outl + out) with (out + outl) by lia. step. fbr.
      st1. zstep. zstep. zstep. zstep. ub_b2z. change (Z.lxor (Z.lxor 0 0) 1) with 1. step. if_lit.
      replace (outl - outl) with 0 by lia.
      step. if_cases KK2; zify_cond KK2; [killb KK2|]; try clear KK2. step.
      finish.
    - (* [comment removed for export] *)
      replace (bl =? outl) with true by (symmetry; apply Z.eqb_eq; lia).
      apply (rw_cells_merge usegs _ ctx [] [C4 (Z_to_bv 64 bl); C4 (Z_to_bv 64 outl)]) in HD. cbn [app cells_size csize cells_bytes cbytes Nat.add] in HD.
      st1.
      match goal with H : rw_cells usegs _ ctx _ |- _ => apply (rw_cells_C8_C4C4 usegs _ ctx [] 0) in H; [cbn [app Z.shiftr] in H| lia] end.
      lwslot FR 1%nat outl. st1. clear HR. rewrite ?(sx32_lit outl) by lia.
      zstep. rewrite (swrap32_small (outl - outl)) by lia. zstep. step. fbr.
      st1. zstep. replace (outl + out) with (out + outl) by lia. step. fbr.
      st1. zstep. zstep. zstep. zstep. ub_b2z. change (Z.lxor (Z.lxor 0 0) 1) with 1. step. if_lit.
      replace (outl - outl) with 0 by lia.
      step. if_cases KK2; zify_cond KK2; [killb KK2|]; try clear KK2. step.
      finish.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_eof1 :
    forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (NB : biorep) (ctx mb a out outl vret vrc bl bo c enc lo : Z) (j0 j8 : list byte),
      0 < mb -> mb + BIO_SIZE <= lo -> mb mod 8 = 0 -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      0 <= bio_flags NB < 2^31 -> Z.land (bio_flags NB) 8 = 0 ->
      rw_cells usegs m mb (bio_cells NB) ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> hceil <= lo -> lo <= bv_unsigned sp + -192 - 16 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 a3',
          ms' = MS (mkR (Z_to_bv 64 RD_RA_DF) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
                       (Z_to_bv 64 enc) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -108)) a3' a4 a5 a6 a7
                       (Z_to_bv 64 ctx) (Z_to_bv 64 0) (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192 - 16, bv_unsigned sp + -192)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 mb (bio_cells NB)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 mb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_READ) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros MP ML MAL CP CL FLR FL8 NC FR HD ST CEIL LO MI. hcb.
    unfold RD_RA_READ, RD_RA_DF, P_EVP_DecodeFinal, B64CTX_SIZE, BIO_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192 - 16, bv_unsigned sp + -192)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    unfold bio_cells, wz in NC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in NC.
    (* [comment removed for export] *)
    step. step. if_cases KK; zify_cond KK; [| killb KK]; try clear KK.
    step. step. step. step.
    carve_frame 16%nat ST. st1. st1. do 2 st1.
    step. fbr. step. ubal_by MAL. step. if_lit.
    st1. rewrite ?sx32_lit by lia.
    zstep. rewrite ?(unsigned_lit (bio_flags NB)) by lia. rewrite FL8.
    do 4 step. release_frame FR0 ST (bv_unsigned sp + -192).
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 0) by lia. step. step. if_lit. step. if_lit.
    st1. step. step. step.
    finish.
    all: match goal with |- ?G => idtac "EOF1-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_eof2 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl vret vrc rv bl bo c enc lo : Z) (j0 j8a : list byte),
      (rv = -1 \/ rv = 1) -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8a q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 RD_RA_DI2) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (if rv <? 0 then -1 else 0))
                       (Z_to_bv 64 enc) (Z_to_bv 64 enc) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) (Z_to_bv 64 0) (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_DecodeInit) fc None m1 (seg_rom usegs)
          /\ munch [] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8a q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl bo 0 c enc))
        (MS (mkR (Z_to_bv 64 RD_RA_DF) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
                 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) (Z_to_bv 64 0) (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_DF) fc None m (seg_rom usegs)).
  Proof.
    intros until j8a. intros RV CP CL FR HD ST LO MI. hcb.
    unfold RD_RA_DF, RD_RA_DI2, P_EVP_DecodeInit, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD.
    (* [comment removed for export] *)
    st1.
    destruct RV as [-> | ->].
    - zstep. zstep. step. step. replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity). finish.
    - zstep. zstep. step. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_eof3 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx mb a out outl vret vrc rc bl bo c enc lo : Z) (j0 j8 : list byte),
      (rc = -1 \/ rc = 0) -> 0 < ctx -> ctx + B64CTX_SIZE <= lo ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret vrc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      rw_cells usegs m ctx (rdhdr bl bo 0 c enc) ->
      stk usegs m lo (bv_unsigned sp + -192) -> lo <= bv_unsigned sp + -192 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 RD_RA_DI2) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 rc)
                       a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ctx) (Z_to_bv 64 0) (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 RD_EXIT) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -192)
          /\ rw_cells usegs m1 (bv_unsigned sp + -192) (rdframe ctx mb a out outl vret rc j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
          /\ rw_cells usegs m1 ctx (rdhdr bl bo 0 rc enc))
        (MS (mkR (Z_to_bv 64 RD_RA_DI2) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 rc)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ctx) s3 (Z_to_bv 64 outl) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_RA_DI2) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros RC CP CL FR HD ST LO MI. hcb.
    unfold RD_RA_DI2, RD_EXIT, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp); (ctx, ctx + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR. unfold rdhdr, wz in HD |- *.
    (* [comment removed for export] *)
    st1. rewrite ?(sx32_lit 0) by lia. st1. st1. step. if_lit.
    finish.
    all: match goal with |- ?G => idtac "EOF3-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
  Definition bio_copy_retry (B NB : biorep) : biorep :=
    mkBIO (bio_method B) (bio_init B) (bio_shutdown B) (Z.lor (bio_flags B) ((bio_flags NB) mod 16)) (bio_retry NB) (bio_numf B)
          (bio_ptr B) (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
  Lemma rd_exit :
    forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (B NB : biorep) (ctx mb a vout voutl retf rcf lo : Z) (j0 j8 : list byte),
      0 <= retf < 2^31 -> - 2^31 <= rcf < 2^31 -> 0 < a -> a + BIO_SIZE <= lo -> a mod 8 = 0 -> 0 < mb -> mb + BIO_SIZE <= lo -> mb mod 8 = 0 ->
      (a + BIO_SIZE <= mb \/ mb + BIO_SIZE <= a) ->
      bio_next B = mb -> 0 <= bio_flags B < 2^31 -> 0 <= bio_flags NB < 2^32 -> 0 <= bio_retry NB < 2^31 ->
      rw_cells usegs m a (bio_cells B) -> rw_cells usegs m mb (bio_cells NB) ->
      rw_cells usegs m (bv_unsigned sp + -192) (rdframe ctx mb a vout voutl retf rcf j0 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
      stk usegs m lo (bv_unsigned sp + -192) -> hceil <= lo -> lo <= bv_unsigned sp + -192 - 16 -> mem_inv usegs m -> bv_unsigned qra mod 2 = 0 ->
      evt usegs (fun ms' => exists m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
          ms' = MS (mkR qra sp gp tp t0' t1' t2' q0 q1
                       (Z_to_bv 64 (if retf =? 0 then rcf else retf)) a1' a2' a3' a4' a5' a6' a7'
                       q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 t3' t4' t5' t6')
                   F (ret_pc qra) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -192 - 16, bv_unsigned sp); (a, a + BIO_SIZE)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp)
          /\ rw_cells usegs m1 a (bio_cells (bio_copy_retry B NB)) /\ rw_cells usegs m1 mb (bio_cells NB))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RD_EXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until j8. intros RETF RCF AP AL AAL MP ML MAL AMB NXT FLB FLN RTN BC NC FR ST CEIL LO MI RAE. hcb.
    unfold RD_EXIT, BIO_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -192 - 16, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rdframe in FR.
    unfold bio_cells, bio_copy_retry, wz in BC |- *. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC |- *.
    unfold bio_cells, wz in NC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in NC.
    rewrite NXT in BC.
    assert (M16 : 0 <= bio_flags NB mod 16 < 16) by (apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    st1. step. step.
    carve_frame 16%nat ST. st1. st1. st1. st1.
    (* [comment removed for export] *)
    step. fbr. step. ubal_by AAL. step. if_lit.
    st1. step. fbr. step. ubal_by MAL. step. if_lit.
    (* [comment removed for export] *)
    st1. rewrite ?zx32_lit by lia. st1. rewrite ?(sx32_lit (bio_flags B)) by lia. st1. rewrite ?(sx32_lit (bio_retry NB)) by lia.
    zstep. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
    zstep. rewrite ?unsigned_lit by lia. rewrite ?(Z.mod_small (bio_flags NB) (2^32)) by lia.
    st1. st1.
    do 3 step. release_frame FR0 ST (bv_unsigned sp + -192). step.
    (* [comment removed for export] *)
    st1. zstep. rewrite ?Z.add_0_r. rewrite (bv_swrap_small 32 retf) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
    st1.
    step. if_cases KK; zify_cond KK; rewrite ?unsigned_lit, ?signed_lit in KK by lia.
    - replace (retf =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      zstep. rewrite ?Z.add_0_r, ?swrap32_mod64. rewrite (bv_swrap_small 32 rcf) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      do 13 st1. step. release_frame FR ST (bv_unsigned sp). step.
      replace (Z_to_bv 64 (bv_unsigned sp + -192 + 192)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      finish. all: rewrite ?NXT; assumption.
    - replace (retf =? 0) with false by (symmetry; apply Z.eqb_neq; lia). step.
      zstep. rewrite ?Z.add_0_r. rewrite (bv_swrap_small 32 retf) by (change (bv_half_modulus 32) with 2147483648%Z; lia).
      do 13 st1. step. release_frame FR ST (bv_unsigned sp). step.
      replace (Z_to_bv 64 (bv_unsigned sp + -192 + 192)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      finish. all: rewrite ?NXT; assumption.
  Qed.
End S.
