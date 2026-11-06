(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section ArmKit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma arm_post_out : forall (W : Z -> rts RT -> mem -> Prop) (a : Z) (X : lfA) (E : aenvA) (Σ : rts RT) (sel idx : Z) (jr jos t : list byte) (m m' : mem) (fc' : bv 32) (jr' : list byte),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m ->
  arm_memA X E a sel idx jr jos t m ->
  ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' (lf_lo X) (lf_S1 X) -> frm0 fc' ->
  (forall ad : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) (bv_unsigned ad) -> ~ (lf_S1 X + 128 <= bv_unsigned ad < lf_S1 X + 152) -> m' ad = m ad) ->
  rw_cells bsegs m' (lf_S1 X + 128) [CB 24 jr'] ->
  arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E)) = 0 ->
  arm_postA RT W a false (rt_credit RT Σ) X E sel idx t Σ Σ m m' fc'.
Proof using AF.
  intros W a X E Σ sel idx jr jos t m m' fc' jr' LK OKE LE AL FRS ARTg AM ART' MI' ST' FRM' AGm OUT' COST.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  assert (STAT : forall x, client_static x -> x < sp' - 208) by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO LOR SPR; ul).
  assert (SLO : shad f + 128 <= sp' - 208) by (clear - SHT LOR SPR; ul).
  assert (FLO0 : f + 1024 <= sp' - 208) by (clear - FLO LOR SPR; ul).
  assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' + 128 <= x < sp' + 152)) -> agree_on P m m').
  { intros P HP ad Ha. destruct (HP _ Ha) as [H N]. exact (AGm ad H N). }
  assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; clear - Hx SPT; ul).
  assert (INF : forall x, f <= x < f + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; left. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
  assert (INSH : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; right. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]. }
  unfold arm_postA, artxA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [split; [exact ART'| reflexivity]|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite COST; lia|].
  split; [intros ad Ha Ho; apply (AGm ad Ha); unfold arm_WA in Ho; cbn [outside app lf_usp lf_S1 lf_F lf_lo] in Ho; clear - Ho; lia|].
  split; [| intros XX; discriminate XX].
  exists jr', jos. unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [eapply rw_cells_agree_nw; [exact C16|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INS; lia| lia]|].
  split; [eapply rw_cells_agree_nw; [exact C100|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INS; lia| lia]|].
  split; [exact OUT'|].
  split; [eapply rw_cells_agree_nw; [exact CE|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INF; lia| lia]|].
  split; [eapply rw_cells_agree_nw; [exact CO|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply INF; lia| lia]|].
  split; [eapply rw_cells_agree_nw; [exact CS|]; apply AG; intros x Hx; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; split; [apply INSH; lia| clear - Hx SLO; lia]|].
  split; [apply (AINV_A_agree E m m' AI); apply AG; intros x Hx; split; [exact (ainv_rng_aclient RT Σ E sp' x AL OKE Hx)| pose proof (ainv_rng_lo E x OKE Hx); clear - H ELO LOR SPR; ul]|].
  split; [apply (el_libA_agree m m' LIB); apply AG; intros x Hx; pose proof (el_lib_rng_static x Hx) as [CSx _]; split; [right; left; exact CSx| pose proof (STAT _ CSx); lia]|].
  split; [apply (libc_nl_agree m m' NL); apply AG; intros x Hx; pose proof (libc_nl_static _ Hx) as CSx; split; [right; left; exact CSx| pose proof (STAT _ CSx); lia]|].
  destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σ m' ART'))|]. apply (ro_cells_agree bsegs m m' _ _ G2). apply AG. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply client_static_intro; lia| clear - Hx LLO LOR SPR; ul].
Qed.

Lemma arm_nbelow : forall (X : lfA) (E : aenvA) (Σ : rts RT) (m : mem) (k : Z),
  lfA_ok X -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m -> 0 <= k -> lf_lo X + 16 <= lf_S1 X - k ->
  forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) x -> ~ (lf_S1 X - k <= x < lf_S1 X).
Proof using AF.
  intros X E Σ m k LK LE AL FRS ARTg K0 KLO.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI. destruct AL as (_ & _ & _ & _ & WLO).
  intros x [H|[H|[H|[H|H]]]] Hin.
  - clear - H Hin. lia.
  - pose proof (client_static_range _ H). clear - H0 Hin LLO KLO. ul.
  - destruct H as (p & kk & Hp & Hr). pose proof (af_live_range RT AF Σ m p kk ARTg Hp) as (_ & Y & _). clear - Hr Y WLO Hin ELO KLO. ul.
  - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-. change (fs_size 4) with 1024 in Hr. clear - Hr Hin FLO KLO. lia.
  - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-.
    replace (shad (f + fs_size 4)) with (shad f + 128) in Hr by (change (fs_size 4) with 1024; unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
    clear - Hr Hin SHT KLO. lia.
Qed.
End ArmKit2.
