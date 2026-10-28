(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma ael_root_elem : forall E, aenvA_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any TAPE_MAX_DEPTH 1 (ae_n E - 1) /\ 2 < ae_n E < 2^32.
Proof. intros E OK. apply tape_wf_root. exact (ok_wf E OK). Qed.

Lemma ael_elem_cases : forall E d i j, aenvA_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j ->
  let w := ae_T E i in
  (j = i + 1 /\ (w = tword t_true 0 \/ w = tword t_false 0 \/ w = tword t_null 0))
  \/ (j = i + 2 /\ (w = tword t_i64 0 \/ w = tword t_u64 0 \/ w = tword t_dbl 0))
  \/ (j = i + 1 /\ is_str (ae_T E) (ae_S E) (ae_sn E) i /\ exists o, w = tword t_str o /\ 0 <= o < 2^56)
  \/ (exists e cv, i < e /\ e + 1 = j /\ 0 <= cv <= CNT_MAX /\ (w = cword t_arr (e + 1) cv \/ w = cword t_obj (e + 1) cv)).
Proof.
  intros E d i j OK EL. cbv zeta.
  pose proof (ok_wf E OK) as WF. destruct WF as (NR & SN & _ & _ & _).
  assert (SCAL : scalar (ae_T E) (ae_S E) (ae_sn E) i j ->
     (j = i + 1 /\ (ae_T E i = tword t_true 0 \/ ae_T E i = tword t_false 0 \/ ae_T E i = tword t_null 0))
  \/ (j = i + 2 /\ (ae_T E i = tword t_i64 0 \/ ae_T E i = tword t_u64 0 \/ ae_T E i = tword t_dbl 0))
  \/ (j = i + 1 /\ is_str (ae_T E) (ae_S E) (ae_sn E) i /\ exists o, ae_T E i = tword t_str o /\ 0 <= o < 2^56)
  \/ (exists e cv, i < e /\ e + 1 = j /\ 0 <= cv <= CNT_MAX /\ (ae_T E i = cword t_arr (e + 1) cv \/ ae_T E i = cword t_obj (e + 1) cv))).
  { intros [[-> H]|[[-> H]|[-> H]]]; [left; auto| right; left; auto| right; right; left].
    split; [reflexivity|]. split; [exact H|]. destruct H as (o & l & Hw & Hs). exists o. split; [exact Hw|].
    pose proof (str_at_bounds (ae_S E) (ae_sn E) ltac:(lia) o l Hs). lia. }
  destruct d as [|d']; cbn [elem] in EL.
  - destruct EL as [SC|[]]. exact (SCAL SC).
  - destruct EL as [SC|CO]; [exact (SCAL SC)|].
    right; right; right. destruct CO as (e & c & cv & -> & CK & HC).
    exists e, cv. unfold ck_any in CK.
    destruct HC as [(H1 & H2 & HT)|(H1 & H2 & HT)].
    + pose proof (tiles_le _ (elem_lt (ae_T E) (ae_S E) (ae_sn E) ck_any d') _ _ _ HT). split; [lia|]. split; [lia|]. split; [lia|]. left; exact H1.
    + pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt (ae_T E) (ae_S E) (ae_sn E) ck_any d')) _ _ _ HT). split; [lia|]. split; [lia|]. split; [lia|]. right; exact H1.
Qed.

Lemma ael_word_eq : forall E d i j t, aenvA_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j < 2^32 ->
  ae_T E i = tword t 0 -> (t = t_i64 \/ t = t_u64 \/ t = t_dbl) -> j = i + 2.
Proof.
  intros E d i j t OK EL Hi Hj HK Ht. pose proof (ok_wf E OK) as WF. destruct WF as (NR & SN & _ & _ & _).
  pose proof (ael_elem_cases E _ _ _ OK EL) as CASES. cbv zeta in CASES. rewrite HK in CASES.
  unfold tword, cword, tword, t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj, CNT_MAX in *.
  destruct CASES as [[E1 [H|[H|H]]]|[[E1 [H|[H|H]]]|[(E1 & _ & o & H & Ho)|(e & cv & He & Hj' & Hcv & [H|H])]]]; lia.
Qed.

Section ArmKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma arm_entry_kit : forall (X : lfA) (E : aenvA) (Σ : rts RT) (a sel idx : Z) (jr jos t : list byte) (m : mem) (k : Z),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m ->
  arm_memA X E a sel idx jr jos t m -> 0 <= k -> lf_lo X + 16 <= lf_S1 X - k ->
  (forall m', munch [(lf_S1 X - k, lf_S1 X)] m m' -> wmono asegs m m' -> ART RT Σ m')
  /\ (forall m', munch [(lf_S1 X - k, lf_S1 X)] m m' -> wmono asegs m m' -> shz m' (lf_F X + 208) 16)
  /\ (forall m', munch [(lf_S1 X - k, lf_S1 X)] m m' -> AINV_A E m')
  /\ (forall m', munch [(lf_S1 X - k, lf_S1 X)] m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16)
  /\ (forall m', munch [(lf_S1 X - k, lf_S1 X)] m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E))
  /\ (forall m', munch [(lf_S1 X - k, lf_S1 X)] m m' -> wmono asegs m m' -> shb_cells m').
Proof using AF.
  intros X E Σ a sel idx jr jos t m k LK OKE LE AL FRS ARTg AM K0 KLO.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  assert (SLO : shad f + 128 <= sp' - k) by (clear - SHT KLO; lia).
  assert (ARTM : forall m', munch [(sp' - k, sp')] m m' -> wmono asegs m m' -> ART RT Σ m').
  { intros m' MU WM. apply (lvl_art_munch RT AF E Σ [(sp' - k, sp')] m m' ARTg AL); [| exact MU| exact WM].
    apply (fp_client_stack1 RT E Σ); [rewrite ELO; clear - KLO; lia| clear - SPT SPR; ul]. }
  split; [exact ARTM|]. split.
  { intros m' MU WM. apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)). apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64].
    eapply rw_cells_agree_nw; [exact CS|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. unfold el_shadow_armA in Hx. rewrite el_shadowA_size in Hx. cbn [outside].
    clear - Hx SLO. split; [lia| exact I]. }
  assert (AIM : forall m', munch [(sp' - k, sp')] m m' -> AINV_A E m').
  { intros m' MU. apply (AINV_A_agree E m m' AI). apply (agree_of_munch _ _ _ _ MU). intros x Hx. pose proof (ainv_rng_lo E x OKE Hx) as R. cbn [outside].
    clear - R ELO KLO. split; [lia| exact I]. }
  split; [exact AIM|]. split; [intros m' MU WM; exact (lvl_shz_doc E OKE m' (AIM m' MU))|].
  split; [intros m' MU WM; exact (lvl_shz_tape RT AF E OKE Σ m' (ARTM m' MU WM) AL)|].
  intros m' MU WM. exact (shb_cells_of_art RT AF Σ m' (ARTM m' MU WM)).
Qed.

Lemma arm_post_below : forall (W : Z -> rts RT -> mem -> Prop) (a : Z) (X : lfA) (E : aenvA) (Σ : rts RT) (sel idx : Z) (jr jos t : list byte) (m m1 : mem) (fc1 : bv 32) (k : Z),
  lfA_ok X -> aenvA_ok E -> lf_envA X E -> a_live RT Σ E -> rt_frames RT Σ = [(lf_F X, 4%nat)] -> ART RT Σ m ->
  arm_memA X E a sel idx jr jos t m -> 0 <= k -> lf_lo X + 16 <= lf_S1 X - k ->
  munch [(lf_S1 X - k, lf_S1 X)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (lf_lo X) (lf_S1 X) -> frm0 fc1 ->
  arm_costA a (ae_n E) (ae_sn E) (zlength (ae_p1 E)) = 0 ->
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
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite COST; lia|].
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

Lemma arm_exit_okA : forall (PMc : Model -> Prop) W a, el_arm_pcA a = EL_EXIT_A -> (forall n sn L, arm_costA a n sn L = 0) ->
  arm_cpsA RT PMc W a.
Proof.
  intros PMc W a PC COST Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  rewrite PC. apply (POST false (rt_credit RT Σ) Σ m fc F).
  unfold arm_postA, artxA. rewrite COST.
  split; [split; [exact ARTg| reflexivity]|]. split; [exact MIg|]. split; [exact STg|]. split; [exact FRM|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  split; [intros a' _ _; reflexivity|].
  split; [exists jr, jos; exact AM| intros H; discriminate H].
Qed.
End ArmKit.
