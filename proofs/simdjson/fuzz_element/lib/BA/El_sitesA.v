(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition EL_SITE_END_B : Z := 0xb3170.
Definition el_site_pcsB (a : Z) : list Z :=
  if a =? 22 then [0xb272c; 0xb27f8; 0xb29e8; 0xb2ac4; 0xb2b84; 0xb2c64; 0xb2cc0; 0xb2d2c]
  else if a =? 23 then [0xb2fb4] else if a =? 24 then [EL_SITE_END_B] else [].

Definition site_fszB (pcs : Z) : Z :=
  if (pcs =? EL_SITE_END_B) || (pcs =? 0xb2fb4) then 32 else 48.

Definition site_frameB (pcs : Z) (X : lfA) (j : list byte) (cv : Z) : list cell :=
  if pcs =? EL_SITE_END_B then [CB 8 j; C8 (wz (lf_S1 X)); C8 (wz (lf_usp X)); C8 (wz 0xb1c78)]
  else if pcs =? 0xb2fb4 then [CB 8 j; C8 (wz (lf_S1 X)); C8 (wz (lf_usp X)); C8 (wz 0xb1c18)]
  else [CB 8 j; C8 (wz (shad (lf_F X))); C8 (wz (lf_F X)); C8 (wz (lf_S1 X)); C8 (wz (lf_usp X)); C8 (wz 0xb1c40)].

Definition site_jlenB (pcs : Z) : nat := 8%nat.
Definition site_cvB (pcs : Z) (cv : Z) : Prop := True.

Definition site_regsB (pcs u : Z) (s0 s2 s3 s1 s4 s8 : word) (f : Z) : Prop :=
  if (pcs =? EL_SITE_END_B) || (pcs =? 0xb2fb4) then s1 = wz SHB /\ s2 = wz f /\ s3 = wz (shad f) /\ s4 = wz (f + 32) /\ s8 = wz f
  else s1 = wz SHB /\ s4 = wz (f + 32) /\ s8 = wz f.

Lemma site_frameB_size : forall pcs X j cv, length j = site_jlenB pcs -> Z.of_nat (cells_size (site_frameB pcs X j cv)) = site_fszB pcs.
Proof.
  intros pcs X j cv L. unfold site_frameB, site_fszB.
  destruct (pcs =? EL_SITE_END_B), (pcs =? 0xb2fb4); cbn [orb cells_size csize Nat.add]; lia.
Qed.

Section Sites.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition throw_siteB (W : Z -> rts RT -> mem -> Prop) (a : Z) (pcs : Z) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (X : lfA) (E : aenvA) (sel idx : Z) (jr jos t j : list byte) (cv : Z)
         (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  In pcs (el_site_pcsB a) ->
  fdfs_only PMc -> mat_stable PMc ->
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> 0 <= sel < 8 -> 0 <= idx < 2^64 ->
  a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> lposA (rt_live RT Σ) ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost EXC_SIZE + 16 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m (lf_lo X) (lf_S1 X - site_fszB pcs) -> lf_lo X + EL_THROW_STACK_A <= lf_S1 X ->
  arm_memA X E a sel idx jr jos t m -> frm0 fc ->
  el_xdataA m -> el_auxvA (lf_usp X) m -> lf_usp X <= rt_sp0 RT Σ <= lf_usp X + FUZZ_SP0GAP ->
  length j = site_jlenB pcs -> site_cvB pcs cv ->
  rw_cells asegs m (lf_S1 X - site_fszB pcs) (site_frameB pcs X j cv) ->
  site_regsB pcs (lf_S1 X - site_fszB pcs) s0 s2 s3 s1 s4 s8 (lf_F X) ->
  (forall (c : Z) (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word)
          (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
     lret_postA RT W a c X E sel idx t Σ Σ' m m' fc' ->
     aevt RT PMc Σ' K (lf_st X EL_LRET_A ra' gp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' (wz (lf_F X)) s9' s10' s11' t3' t4' t5' t6' F' fc' m')) ->
  aevt RT PMc Σ K (MS (mkR ra (wz (lf_S1 X - site_fszB pcs)) gp (wz TPV_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 (wz (lf_F X + 96)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz pcs) fc None m (seg_rom asegs)).
End Sites.

Section PostLe.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma arm_post_below_le : forall (W : Z -> rts RT -> mem -> Prop) (a : Z) (X : lfA) (E : aenvA) (Σ : rts RT) (sel idx : Z) (jr jos t : list byte) (m m1 : mem) (fc1 : bv 32) (k : Z),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m ->
  arm_memA X E a sel idx jr jos t m -> 0 <= k -> lf_lo X + 16 <= lf_S1 X - k ->
  munch [(lf_S1 X - k, lf_S1 X)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (lf_lo X) (lf_S1 X) -> frm0 fc1 ->
  0 <= arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E)) ->
  arm_postA RT W a false (rt_credit RT Σ) X E sel idx t Σ Σ m m1 fc1.
Proof using AF.
  intros W a X E Σ sel idx jr jos t m m1 fc1 k LK OKE LE AL FRS ARTg AM K0 KLO MU1 WM1 MI1 ST1 FRM1 COST.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R.
  assert (FLO16 : f + 1024 <= sp' - k) by (clear - FLO KLO; lia).
  assert (SLO : shad f + 128 <= sp' - k) by (clear - SHT KLO; lia).
  assert (AG : forall P : Z -> Prop, (forall x, P x -> x < sp' - k \/ sp' <= x) -> agree_on P m m1).
  { intros P HP a' Ha. apply MU1. cbn [outside]. split; [pose proof (HP _ Ha); lia| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (sp' - k) ARTg ltac:(clear - SP0R LLO LOR SPR ELO AL KLO; destruct AL as (_ & _ & _ & _ & WLO); ul)); [| exact WM1].
    intros a' Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin SPT SPR. ul. }
  assert (STAT : forall x, client_static x -> x < sp' - k) by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO KLO; ul).
  unfold arm_postA, artxA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [split; [exact ART1| reflexivity]|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FRM1|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split.
  { intros a' Ha _. apply MU1. cbn [outside]. split; [| exact I]. intros Hin.
    destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H Hin. lia.
    - pose proof (STAT _ H). clear - H0 Hin. lia.
    - destruct H as (p & kk & Hp & Hr). pose proof (af_live_range RT AF Σ m p kk ARTg Hp) as (_ & Y & _). destruct AL as (_ & _ & _ & _ & WLO). clear - Hr Y WLO Hin ELO KLO. ul.
    - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-. change (fs_size 4) with 1024 in Hr. clear - Hr Hin FLO16. lia.
    - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-.
      replace (shad (f + fs_size 4)) with (shad f + 128) in Hr by (change (fs_size 4) with 1024; unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
      clear - Hr Hin SLO. lia. }
  split; [| intros X; discriminate X].
  exists jr, jos. unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo].
  split; [eapply rw_cells_agree_nw; [exact C16|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; lia|].
  split; [eapply rw_cells_agree_nw; [exact C100|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; lia|].
  split; [eapply rw_cells_agree_nw; [exact C128|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; lia|].
  split; [eapply rw_cells_agree_nw; [exact CE|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia|].
  split; [eapply rw_cells_agree_nw; [exact CO|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia|].
  split; [eapply rw_cells_agree_nw; [exact CS|]; apply AG; intros x Hx; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; left; lia|].
  split; [apply (AINV_A_agree E m m1 AI); apply AG; intros x Hx; left; pose proof (ainv_rng_lo E x OKE Hx); clear - H ELO KLO; subst; lia|].
  split; [apply (el_libA_agree m m1 LIB); apply AG; intros x Hx; left; exact (STAT _ (proj1 (el_lib_rng_static x Hx)))|].
  split; [apply (libc_nl_agree m m1 NL); apply AG; intros x Hx; left; exact (STAT _ (libc_nl_static _ Hx))|].
  destruct IOS as (g & G1 & G2). exists g. split; [apply (ro_cells_agree asegs m m1 _ _ G1)| apply (ro_cells_agree asegs m m1 _ _ G2)]; apply AG; intros x Hx;
    cbn [cells_size csize Nat.add] in Hx; left; clear - Hx LLO KLO; ul.
Qed.

Lemma arm_mem_agree : forall (X : lfA) (E : aenvA) (Σ : rts RT) (a sel idx : Z) (jr jos t : list byte) (m m0 : mem),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m0 ->
  arm_memA X E a sel idx jr jos t m -> el_xdataA m -> el_auxvA (lf_usp X) m ->
  (forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) x) -> agree_on P m m0) ->
  arm_memA X E a sel idx jr jos t m0 /\ el_xdataA m0 /\ el_auxvA (lf_usp X) m0.
Proof using AF.
  intros X E Σ a sel idx jr jos t m m0 LK OKE LE AL FRS ART1 AM XD AUX AG.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  assert (INS : forall x, sp' <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) by (intros x Hx; left; clear - Hx SPT; ul).
  assert (INF : forall x, f <= x < f + 1016 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; left. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; lia]. }
  assert (INSH : forall x, shad f <= x < shad f + 128 -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros x Hx. right; right; right; right. exists f, 4%nat. rewrite FRS. split; [left; reflexivity| change (fs_size 4) with 1024; unfold shad in *; Z.div_mod_to_equations; lia]. }
  split.
  { unfold arm_memA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [eapply rw_cells_agree_nw; [exact C16|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INS; lia|].
    split; [eapply rw_cells_agree_nw; [exact C100|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INS; lia|].
    split; [eapply rw_cells_agree_nw; [exact C128|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INS; lia|].
    split; [eapply rw_cells_agree_nw; [exact CE|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INF; lia|].
    split; [eapply rw_cells_agree_nw; [exact CO|]; apply AG; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INF; lia|].
    split; [eapply rw_cells_agree_nw; [exact CS|]; apply AG; intros x Hx; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; apply INSH; lia|].
    split; [apply (AINV_A_agree E m m0 AI); apply AG; intros x Hx; exact (ainv_rng_aclient RT Σ E sp' x AL OKE Hx)|].
    split; [apply (el_libA_agree m m0 LIB); apply AG; intros x Hx; pose proof (el_lib_rng_static x Hx) as [CSx _]; right; left; exact CSx|].
    split; [apply (libc_nl_agree m m0 NL); apply AG; intros x Hx; pose proof (libc_nl_static _ Hx) as CSx; right; left; exact CSx|].
    destruct IOS as (g & G1 & G2). exists g. split; [exact (proj1 (af_got_lib RT AF Σ m0 ART1))|]. apply (ro_cells_agree asegs m m0 _ _ G2). apply AG. intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. right; left; apply client_static_intro; lia. }
  split; [apply (el_xdata_agree m m0 XD); apply AG; intros x Hx; right; left; apply client_static_intro; clear - Hx; lia|].
  apply (el_auxv_agree usp m m0 AUX); apply AG; intros x Hx; [right; left; exact (auxc_client_static _ Hx)| left; clear - Hx SPR; lia].
Qed.

Lemma arm_ctx_below : forall (X : lfA) (E : aenvA) (Σ : rts RT) (a sel idx : Z) (jr jos t : list byte) (m m0 : mem) (k : Z),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m ->
  arm_memA X E a sel idx jr jos t m -> 0 <= k -> lf_lo X + 16 <= lf_S1 X - k ->
  el_xdataA m -> el_auxvA (lf_usp X) m ->
  munch [(lf_S1 X - k, lf_S1 X)] m m0 -> wmono asegs m m0 ->
  ART RT Σ m0 /\ arm_memA X E a sel idx jr jos t m0 /\ el_xdataA m0 /\ el_auxvA (lf_usp X) m0
  /\ (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) x -> ~ (lf_S1 X - k <= x < lf_S1 X))
  /\ (forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) x) -> agree_on P m m0).
Proof using AF.
  intros X E Σ a sel idx jr jos t m m0 k LK OKE LE AL FRS ARTg AM K0 KLO XD AUX MU1 WM1.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R.
  assert (FLO16 : f + 1024 <= sp' - k) by (clear - FLO KLO; lia).
  assert (SLO : shad f + 128 <= sp' - k) by (clear - SHT KLO; lia).
  assert (STAT : forall x, client_static x -> x < sp' - k) by (intros x Hx; pose proof (client_static_range _ Hx); clear - H LLO KLO; ul).
  assert (NBELOW : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x -> ~ (sp' - k <= x < sp')).
  { intros x [H|[H|[H|[H|H]]]] Hin.
    - clear - H Hin. lia.
    - pose proof (STAT _ H). clear - H0 Hin. lia.
    - destruct H as (p & kk & Hp & Hr). pose proof (af_live_range RT AF Σ m p kk ARTg Hp) as (_ & Y & _). destruct AL as (_ & _ & _ & _ & WLO). clear - Hr Y WLO Hin ELO KLO. ul.
    - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-. change (fs_size 4) with 1024 in Hr. clear - Hr Hin FLO16. lia.
    - destruct H as (f' & k' & Hf & Hr). rewrite FRS in Hf. destruct Hf as [Hf|[]]. injection Hf as <- <-.
      replace (shad (f + fs_size 4)) with (shad f + 128) in Hr by (change (fs_size 4) with 1024; unfold shad; clear - F64 FPOS; Z.div_mod_to_equations; lia).
      clear - Hr Hin SLO. lia. }
  assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) -> agree_on P m m0).
  { intros P HP a' Ha. apply MU1. cbn [outside]. split; [exact (NBELOW _ (HP _ Ha))| exact I]. }
  assert (ART1 : ART RT Σ m0).
  { apply (art_client_write RT AF Σ m m0 (sp' - k) ARTg ltac:(clear - SP0R LLO LOR SPR ELO AL KLO; destruct AL as (_ & _ & _ & _ & WLO); ul)); [| exact WM1].
    intros a' Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin SPT SPR. ul. }
  destruct (arm_mem_agree (mkLF usp sp' f lo) E Σ a sel idx jr jos t m m0 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM XD AUX AG) as (AM0 & XD0 & AUX0).
  cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0.
  split; [exact ART1|]. split; [exact AM0|]. split; [exact XD0|]. split; [exact AUX0|]. split; [exact NBELOW| exact AG].
Qed.

Lemma arm_post_agree : forall (W : Z -> rts RT -> mem -> Prop) (a : Z) (X : lfA) (E : aenvA) (Σ : rts RT) (sel idx : Z) (jr jos t : list byte) (m m1 : mem) (fc1 : bv 32),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m1 ->
  arm_memA X E a sel idx jr jos t m -> el_xdataA m -> el_auxvA (lf_usp X) m ->
  (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) (bv_unsigned x) -> m1 x = m x) ->
  mem_inv asegs m1 -> stk asegs m1 (lf_lo X) (lf_S1 X) -> frm0 fc1 ->
  0 <= arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E)) ->
  arm_postA RT W a false (rt_credit RT Σ) X E sel idx t Σ Σ m m1 fc1.
Proof using AF.
  intros W a X E Σ sel idx jr jos t m m1 fc1 LK OKE LE AL FRS ART1 AM XD AUX PRES MI1 ST1 FRM1 COST.
  assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (lf_S1 X) x) -> agree_on P m m1).
  { intros P HP x Px. exact (PRES x (HP _ Px)). }
  destruct (arm_mem_agree X E Σ a sel idx jr jos t m m1 LK OKE LE AL FRS ART1 AM XD AUX AG) as (AM1 & _ & _).
  unfold arm_postA, artxA.
  split; [split; [exact ART1| reflexivity]|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FRM1|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [intros x Hx _; exact (PRES x Hx)|].
  split; [exists jr, jos; exact AM1| intros Y; discriminate Y].
Qed.
End PostLe.
