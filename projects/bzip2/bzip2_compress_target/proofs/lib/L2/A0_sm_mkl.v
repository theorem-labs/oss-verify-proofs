(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCHuff BzArrD CmpMem CmpHmKit AsanKit AsanCut A0_cmp_smK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section SMK.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis HBM : hbMakeCodeLengths_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
(* [comment removed for export] *)
Variables (lo P usp sp0 FB SHF : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (Wc : list (Z * Z)) (mi : mem).
Hypothesis G : act_geom RT lo P usp sp0 true 2 FB SHF 256 32 fr live0 Wc.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
Hypothesis FRSZ : P + 1600 <= usp.                          (* [comment removed for export] *)
Hypothesis ROOM : lo + RT_STACK + 240 <= P.                 (* [comment removed for export] *)
Hypothesis FRB : (length fr + 1 < FRAMES_MAX)%nat.         (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wc mi).
Notation SOK Σ := (sig_ok RT sp0 true 2 FB fr live0 Σ).
(* [comment removed for export] *)
Variables (E qE : Z) (Jl Jf : list byte) (A nG : Z) (rfe : zarr) (len : nat -> zarr) (gp tp : word).   (* [comment removed for export] *)
Hypothesis ELIV : In (E, 55768) live0.
Hypothesis E4 : E = 4 * qE.
Hypothesis TP : tp = Z_to_bv 64 0x5fc0d8.
Hypothesis HA : 3 <= A <= 258. Hypothesis HNG : 1 <= nG <= 6.
Hypothesis WCE : forall x, E + 37708 <= x < E + 39256 -> ~ outside Wc x.
Hypothesis RFF : forall tt v, 0 <= tt < nG -> 0 <= v < A -> zdef rfe (258 * tt + v) = true /\ 0 <= zget rfe (258 * tt + v) < 8388608.
Hypothesis LENS : forall t : nat, Z.of_nat t < nG ->
  hm_facts (len t) rfe (258 * Z.of_nat t) (258 * Z.of_nat t) A /\
  len (S t) = hs_len (hm_rounds 40 A 17 (258 * Z.of_nat t) (hp_rs (len t) rfe (258 * Z.of_nat t) (258 * Z.of_nat t) A 0)).
Notation Wmkl := [(E + 37708, E + 39256)].

(* [comment removed for export] *)
Notation LR pc ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 :=
  (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 A) s8 s9 s10 s11 t3 t4 t5 t6).

Lemma sm_mkl_cps : forall (n t : nat) (Σ0 Σ : rts RT) (m0 m : mem) (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  Z.of_nat t + Z.of_nat n = nG -> (1 <= n)%nat ->
  SOK Σ -> rt_live RT Σ = rt_live RT Σ0 -> rt_frames RT Σ = rt_frames RT Σ0 -> Z.of_nat n <= rt_credit RT Σ ->
  ART RT Σ m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  u8arr a0segs m (E + 37708) (ovb (len t) Jl 1548) -> u32arr a0segs m (E + 45448) (ovw rfe Jf 1548) ->
  rw_cells a0segs m (P + 1408) [C8 (Z_to_bv 64 (E + 45448 + 1032 * nG))] ->
  rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wmkl m0 m ->
  cps asegs (ASTA RT Σ PMc (eq (MS (LR 0x8f1a8 ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 37708 + 258 * Z.of_nat t)) (Z_to_bv 64 (E + 45448 + 1032 * Z.of_nat t))
                                       s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x8f1a8) fc None m (seg_rom a0segs))))
    (fun c => exists (Σ' : rts RT) (m' : mem) (ra' t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
       ASTA RT Σ' PMc (eq (MS (LR 0x8f1cc ra' t0 t1 t2 s0 a0 a1 (Z_to_bv 64 (E + 45448 + 1032 * nG)) a3 a4 a5 a6 a7
                                  (Z_to_bv 64 (E + 37708 + 258 * nG)) (Z_to_bv 64 (E + 45448 + 1032 * nG)) s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6)
                              F' (Z_to_bv 64 0x8f1cc) fc' None m' (seg_rom a0segs))) c
       /\ SOK Σ' /\ rt_live RT Σ' = rt_live RT Σ0 /\ rt_frames RT Σ' = rt_frames RT Σ0 /\ rt_credit RT Σ' = rt_credit RT Σ - Z.of_nat n
       /\ ART RT Σ' m' /\ KMem.mem_inv asegs m' /\ stk asegs m' lo P /\ PRESI m'
       /\ u8arr a0segs m' (E + 37708) (ovb (len (t + n)) Jl 1548) /\ u32arr a0segs m' (E + 45448) (ovw rfe Jf 1548)
       /\ rw_cells a0segs m' (P + 1408) [C8 (Z_to_bv 64 (E + 45448 + 1032 * nG))]
       /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wmkl m0 m').
Proof.
  induction n as [|n IH]. { intros; lia. }
  intros t Σ0 Σ m0 m ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc Ht Hn SK LVE FRE CRED ART0 MI0 ST0 PR0 LEN RFQ SL ACC.
  intros T c Hc Hk.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. pose proof SK as (FRM & SP0E & LIVS).
  pose proof (P_unsigned G) as PU. pose proof ROOM as ROOM'. unfold RT_STACK in GLOR, ROOM'.
  pose proof (af_live_range RT AF Σ m E 55768 ART0 (LIVS _ ELIV)) as (EL0 & EL1 & _). rewrite SP0E in EL1.
  destruct (LENS t ltac:(lia)) as [HMF EML].
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro E (CLive E 55768)) as KE.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc). eapply A0_sm_mklA. apply evt_done. clear Hc. intros c1 Hc1.
  (* [comment removed for export] *)
  set (X := HE (Z_to_bv 64 0x8f1bc) (Z_to_bv 64 P) gp tp s0 (Z_to_bv 64 P) (Z_to_bv 64 (E + 37708 + 258 * Z.of_nat t)) (Z_to_bv 64 (E + 45448 + 1032 * Z.of_nat t))
                s4 s5 s6 (Z_to_bv 64 A) s8 s9 s10 s11 F fc (E + 37708) (E + 45448) (258 * Z.of_nat t) (258 * Z.of_nat t) A 1548 1548 lo (P / 16) (qE + 11362)
                (len t) rfe Jl Jf (Z_to_bv 64 0) m).
  assert (XOK : hmenv_ok X).
  { unfold hmenv_ok, X, CEILh. cbn [he_sp he_lb he_A he_NL he_fb he_NF he_El he_Ef he_qf he_lo he_qsp he_freq]. rewrite PU, ACE. unfold RT_STACK, USTACK_TOP in *.
    repeat split; try lia;
      match goal with H : 0 <= ?v < A |- _ => destruct (RFF (Z.of_nat t) v ltac:(lia) H) as [D R] end; [exact D| lia| lia]. }
  pose proof (HBM Σ PMc X m E 55768 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6) as HB. cbv zeta in HB.
  cbn [X he_ra he_sp he_gp he_tp he_s0 he_s1 he_s2 he_s3 he_s4 he_s5 he_s6 he_s7 he_s8 he_s9 he_s10 he_s11 he_F he_fc he_El he_Ef he_lb he_fb he_A he_NL he_NF he_lo he_len he_freq he_Jl he_Jf] in HB.
  rewrite PU in HB.
  refine (cps_realizes asegs _ _ T c1 (HB FDO MST XOK TP ltac:(rewrite SP0E; exact ACE) LEN RFQ (LIVS _ ELIV) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
            ltac:(rewrite FRM; cbn [length app]; lia) ltac:(lia) ART0 MI0 ST0 ltac:(rewrite SP0E; exact GLOW) ROOM ltac:(lia) HMF) _ _).
  { replace (E + 37708 + 258 * Z.of_nat t) with (E + 37708 + 258 * Z.of_nat t) by reflexivity.
    replace (E + 45448 + 4 * (258 * Z.of_nat t)) with (E + 45448 + 1032 * Z.of_nat t) by lia. exact Hc1. }
  clear Hc1 HB. intros c2 (Σ' & Hq & LV' & FR' & SP' & CR').
  destruct (ASTA_unpack RT Σ' _ _ c2 Hq) as (ms2 & (m' & q0 & q1 & q2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & q3 & q4 & q5 & q6 & F' & fc' & -> & ART' & MI' & ST' & LEN' & STEP) & Hc2).
  clear Hq. rewrite <- EML in LEN'.
  cbn [X he_ra he_sp he_gp he_tp he_s0 he_s1 he_s2 he_s3 he_s4 he_s5 he_s6 he_s7 he_s8 he_s9 he_s10 he_s11] in Hc2.
  cbn [X he_sp he_El he_Ef he_lb he_fb he_A he_NL he_NF he_lo he_len he_freq he_Jl he_Jf] in ART', MI', ST', LEN', STEP. rewrite ?PU in ST', STEP.
  rewrite (ret_pc_even 0x8f1bc ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  destruct (after_call G Σ Σ' _ m m' SK LV' FR' SP' PR0 STEP ltac:(per_interval; right; apply WCE; lia)) as (SK' & PR').
  clear LEN. xfer_rtf G SK STEP m m'.
  assert (ACC' : rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wmkl m0 m').
  { apply (pfp_trans _ _ _ _ m0 m m' ACC). rewrite <- LVE, <- FRE. apply (pfp_weaken _ _ _ _ Wmkl m m' STEP). per_interval. cbn [KFrame.outside]. lia. }
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ' PMc _ T c2 MST Hc2).
  eapply (A0_sm_mklB _ m' P (E + 37708 + 258 * Z.of_nat t) (E + 45448 + 1032 * Z.of_nat t) (E + 45448 + 1032 * nG)); [exact SL| lia| unfold USTACK_TOP, STACK_WIN in *; lia| unfold USTACK_TOP, STACK_WIN in *; lia| |].
  - (* [comment removed for export] *)
    intros NE. apply evt_done. intros c3 Hc3.
    refine (cps_realizes asegs _ _ T c3 (IH (S t) Σ0 Σ' m0 m' _ _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s8 s9 s10 s11 _ _ _ _ F' fc' ltac:(lia) ltac:(lia) SK'
              ltac:(rewrite LV'; exact LVE) ltac:(rewrite FR'; exact FRE) ltac:(lia) ART' MI' ST' PR' LEN' RFQ SL ACC') _ _).
    + replace (E + 37708 + 258 * Z.of_nat (S t)) with (E + 37708 + 258 * Z.of_nat t + 258) by lia.
      replace (E + 45448 + 1032 * Z.of_nat (S t)) with (E + 45448 + 1032 * Z.of_nat t + 1032) by lia. exact Hc3.
    + intros c4 (Σ4 & m4 & ra4 & x0 & x1 & x2 & y0 & y1 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F4 & fc4 & Hc4 & S4 & LV4 & FR4 & CR4 & REST).
      apply Hk. exists Σ4, m4, ra4, x0, x1, x2, y0, y1, y3, y4, y5, y6, y7, x3, x4, x5, x6, F4, fc4.
      split; [exact Hc4|]. split; [exact S4|]. split; [exact LV4|]. split; [exact FR4|]. split; [lia|].
      replace (t + S n)%nat with (S t + n)%nat by lia. exact REST.
  - (* [comment removed for export] *)
    intros EQ. apply evt_done. intros c3 Hc3. assert (n = 0)%nat by lia. subst n.
    apply Hk. eexists Σ', m', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F', fc'.
    split; [| split; [exact SK'| split; [rewrite LV'; exact LVE| split; [rewrite FR'; exact FRE| split; [lia|]]]]].
    + replace (E + 37708 + 258 * nG) with (E + 37708 + 258 * Z.of_nat t + 258) by lia.
      replace (E + 45448 + 1032 * nG) with (E + 45448 + 1032 * Z.of_nat t + 1032) at 2 by lia. exact Hc3.
    + replace (t + 1)%nat with (S t) by lia.
      split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PR'|]. split; [exact LEN'|]. split; [exact RFQ|]. split; [exact SL| exact ACC'].
Qed.
End SMK.
