(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge RzCPS Arr FP Frame Cells Step Mem Bytes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog PrintfModel PrintfModelX ApFmt CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs GDesc I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA BnIfaceA AsStruct RtCallA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeFmtPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_C17_A : Z := 0x76c60.      (* [comment removed for export] *)

Lemma fmt_C17_roA : ro_bytes ctasegs A_C17_A (zb FMT_C17). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma vfmtA_C17 : forall t : tm6, tm_valid t ->
  vfmtA_ok A_C17_A FMT_C17 [PA_i (t_year t); PA_i (t_mon t); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t)] (gen15 t).
Proof.
  intros t TV. pose proof TV as (Y & MO & MD & HH & MI' & SS).
  pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  destruct (printf_piecesx_C17 (t_year t) (t_mon t) (t_mday t) (t_hour t) (t_min t) (t_sec t)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (ps & P & CC).
  pose proof (printf_piecesx_count _ _ _ _ P) as L. rewrite (ct_gentime_gen15 t TV) in CC.
  split; [exact fmt_C17_roA|]. split; [exact fmt_bytes_C17|].
  split; [unfold A_C17_A; clear; lia|]. split; [unfold A_C17_A, STATIC_SPLIT; change (zlength FMT_C17) with 26; clear; lia|].
  split. { intros AR' Σ' OW' LB' m' H. change (zlength FMT_C17) with 26.
           eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x76c60, 26, 64)); [exact (@AH_art AR' _ _ _ _ H)| vm_compute; reflexivity| unfold A_C17_A; cbn; clear; lia| unfold A_C17_A; cbn; clear; lia]. }
  split; [exact pass1x_ok_C17|].
  split. { rewrite <- CC. rewrite L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold SN_CAP, OssFuzzTheorems.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. pose proof (gen15_zlength t). rewrite <- CC in *. rewrite L in *. clear - H. lia. }
  split; [apply fp_callsx_nog; repeat constructor|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ints_args (l : list Z) : list parg := match l with [] => [] | i :: l' => PA_i i :: ints_args l' end.

Fixpoint int_slots_ok (slots : list word) (l : list Z) : Prop :=
  match l with
  | [] => True
  | i :: l' => match slots with [] => False | w :: slots' => (-2^31 <= i < 2^31 /\ bv_unsigned w mod 2^32 = i mod 2^32) /\ int_slots_ok slots' l' end
  end.

Lemma int_slots_vargs : forall RT (Σ : rts RT) m sp lo D n slots l covs,
  int_slots_ok slots l -> vargs_okx RT Σ m sp lo D n slots (ints_args l) covs.
Proof.
  intros RT Σ m sp lo D n slots l. revert slots. induction l as [|i l IH]; intros slots covs H; cbn [ints_args vargs_okx]; [destruct slots; exact I|].
  destruct slots as [|w slots']; [exact H|]. destruct H as [H1 H2]. split; [exact H1| apply IH; exact H2].
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition snp_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo D : Z) (o : list Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength o)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (D <= a < D + (zlength o + 1))) m m'
    /\ bytes_at ctasegs m' D (zb o ++ [Z_to_bv 8 0]).

Section WithPFC.
Hypothesis PFC : printf_contracts RT.

(* [comment removed for export] *)
Lemma snprintf_ints_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo D nD A : Z) (bd : block)
    (fmt : list Z) (stkw : list word) (ints : list Z) (o : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 8 * zlength stkw <= USTACK_TOP - 16 -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= D -> D + nD <= blk_addr bd + blk_size bd ->
  vfmtA_ok A fmt (ints_args ints) o -> zlength o <= nD - 1 -> 1 <= nD -> nD < 2^31 ->
  va_area m (bv_unsigned sp) stkw -> int_slots_ok ([a3; a4; a5; a6; a7] ++ stkw) ints ->
  a0 = wz D -> a1 = wz nD -> a2 = wz A ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_snprintf) fc None m (seg_rom ctasegs))))
      (ASTA RT Σ PMc (snp_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo D o m)).
Proof.
  intros until o. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 VF OLEN N1 N2 VAA INTS -> -> ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & BDI).
  assert (ZS : 0 <= zlength stkw) by (unfold zlength; clear; lia).
  pose proof (blk_checked_dst Σ OW LB m sp bd D nD HEAP IND D1 D2 ltac:(lia)) as CD.
  eapply cps_conseq; [ eapply (rc_snprintf _ PFC Σ PMc) with (D := D) (n := nD) (A := A) (fmt := fmt) (stk := stkw) (args := ints_args ints) (o := o) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact (vfmtA_vfmt AR Σ OW LB m A fmt (ints_args ints) o VF HEAP MI).
  - exact VAA.
  - unfold USTACK_TOP. lia.
  - right; left. unfold BnHeapA.ACEIL, RT_STACK in *. lia.
  - apply int_slots_vargs. exact INTS.
  - exact N1.
  - exact N2.
  - exact OLEN.
  - lia.
  - unfold BnHeapA.ACEIL, USTACK_TOP in *. lia.
  - unfold SEGTOP_A. unfold BnHeapA.ACEIL in *. lia.
  - exact CD.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold snp_postA, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split; [exact (AH_same' _ _ _ _ _ _ _ _ bd HEAP ART2 WM2 PRES IND D1 ltac:(lia))|].
    split; [exact WM2|].
    split; [pose proof (AH_frames _ _ _ _ HEAP) as HF; eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP); rewrite <- HF; exact PRES |].
    exact BZ.
Qed.
End WithPFC.
End WithRT.
