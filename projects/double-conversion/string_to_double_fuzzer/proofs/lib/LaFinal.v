(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk LibIface Hoare.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxOrder LxOrderWf.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib MemsetLib AsanMemset_code AsanMemset LaState LaMem LaStep LaCheck LaSem LaWf LaSoundVal LaSoundAlu LaSoundMem LaSoundMem2 LaSoundStep LaSoundMatch LaSoundExplore LaGlue LaSumMalloc LaSumMemset LaSumCbd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LAS LAM LAI LAC LASEM LAWF LASV LASM LASM2.
Open Scope Z_scope.

Module LAF.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_eta : forall ms : machine_state,
  ms_svc_pending ms = None -> ms_resv ms = None ->
  ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [regs fregs pc svc resv fcsr mem rom] Hs Hr. cbn in *. subst. reflexivity. Qed.

Lemma w64_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma w64_succ : forall a, (w64 a + 1)%bv = w64 (a + 1).
Proof.
  intros a. apply bv_eq. unfold w64. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_wrap 64 1) with 1.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_ext : forall segs (m m' : word -> option byte) n a,
  (forall i, 0 <= i < Z.of_nat n -> m' (w64 (a + i)) = m (w64 (a + i))) ->
  rdn segs m' (w64 a) n = rdn segs m (w64 a) n.
Proof.
  intros segs m m' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn]. pose proof (Hag 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
  rewrite w64_succ. rewrite (IH (a + 1)) by (intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hag; lia).
  reflexivity.
Qed.

Lemma havoc_regs_get : forall rs i j,
  list_get (havoc_regs rs i) j Top = if existsb (Nat.eqb (i + j)%nat) keep_regs then list_get rs j Top else Top.
Proof.
  induction rs as [|v r IH]; intros i j; cbn [havoc_regs list_get].
  - destruct (existsb _ _); reflexivity.
  - destruct j as [|j]; [rewrite Nat.add_0_r; reflexivity|].
    rewrite IH. replace (S i + j)%nat with (i + S j)%nat by lia. reflexivity.
Qed.

Lemma list_get_below : forall rs n r, forallb (fun v => aval_below v n) rs = true -> aval_below (list_get rs r Top) n = true.
Proof.
  induction rs as [|v l IH]; intros n r H; [destruct r; reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. destruct r; cbn [list_get]; [exact H1 | apply IH; exact H2].
Qed.

Lemma keep_cs : forall k : nat, existsb (Nat.eqb k) keep_regs = true -> In (Z.of_nat k) cs_regs.
Proof.
  intros k H. apply existsb_exists in H as (k' & Hin & E). apply Nat.eqb_eq in E. subst k'.
  unfold keep_regs in Hin. unfold cs_regs. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn; tauto|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_rom : forall segs ms w ms',
  drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms w ms' H. unfold decode_exec_accesses in H.
  destruct (is_ecall w); [cbn in H; injection H as <-; reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
  match type of H with context [interp_eff_accesses ?a ?b ?c] => destruct (interp_eff_accesses a b c) as [rep| |] end; try discriminate.
  destruct rep as [[c m] acc]. cbn in H. injection H as <-. reflexivity.
Qed.

Lemma step_rom : forall segs ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms ms' H. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  unfold fetch_failure in H. destruct (negb _); [discriminate|].
  match type of H with context [if ?t then MachineFault else MachineUnmodeled] => destruct t; discriminate end.
Qed.

Lemma msteps_rom : forall segs ms ms', msteps segs ms ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; [reflexivity|].
  rewrite IH. eapply step_rom. exact Hstep.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pairs_subb (L M : list (Z * Z)) : bool :=
  forallb (fun ab : Z * Z => match bm_get M (fst ab) with Some b => Z.eqb b (snd ab) | None => false end) L.
Definition envA_okb (U : uenv) : bool :=
  pairs_subb RT_A (ue_rt U) &&& pairs_subb GSH_A (ue_gsh U)
  &&& Z.eqb (ue_memset U) ms_base
  &&& forallb (fun pk : Z * Z => Z.eqb (fst pk) (MALLOC_A (snd pk))) (ue_malloc U).

Lemma pairs_subb_sound : forall L M a b, pairs_subb L M = true -> In (a, b) L -> bm_get M a = Some b.
Proof.
  intros L M a b H Hin. unfold pairs_subb in H. rewrite forallb_forall in H. specialize (H _ Hin). cbn [fst snd] in H.
  destruct (bm_get M a) as [b'|]; [|discriminate]. apply Z.eqb_eq in H. subst. reflexivity.
Qed.
Lemma mallocs_at_In : forall ms pc k, LAC.mallocs_at ms pc = Some k -> In (pc, k) ms.
Proof.
  induction ms as [|[p k'] r IH]; intros pc k H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec p pc); [injection H; intros <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unit_obligation (s32 : Z) (abs0 : list (Z * Z)) (Un : unitT) : Prop :=
  LAG.uenv_okb (un_env Un) = true /\ LAG.glue_okb (un_env Un) LIBR_HULL_A LIBR_A SNAP_A = true /\ envA_okb (un_env Un) = true
  /\ ue_sp32 (un_env Un) = s32 /\ ue_segs (un_env Un) = SEGS_A /\ ue_ro (un_env Un) = RO_A
  /\ un_snap Un = SNAP_A /\ check_unit Un = true /\ un_total Un = true
  /\ In (entry_cut ENTRY_A NMAX_A s32 TP_A abs0) (un_cuts Un)
  /\ ue_scells (un_env Un) = [(CANARY_A, SYM_SC0)].                  (* [comment removed for export] *)

Theorem lxa_lib_stmt :
  (forall s32 abs0, s32 = 0 \/ s32 = 16 -> abs0 = [] \/ abs0 = SNAP_A -> exists Un, unit_obligation s32 abs0 Un) ->
  (forall k, (k = 1 \/ k = 4 \/ k = 5) -> malloc_stmt k) -> cbd_stmt_A ->
  lib_stmt_A.
Proof.
  intros HUN HMALLOC HCBD.
  unfold lib_stmt_A.
  intros fx regs mem rom ret sp data n FS Hx1 Hret4 Hx2 Hx10 Hx11 Hx4 Hn Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 Hdisj Himg Hnoseg Hpay Hst Hro [c Hc] [Hstat Hhull]
         Hrt Hgsh Hshstk Hshpay Hfs Hctx Hap Hfrm.
  (* [comment removed for export] *)
  set (s32 := bv_unsigned sp mod 32).
  assert (H32 : s32 = 0 \/ s32 = 16).
  { subst s32. pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)) as B.
    pose proof (Z.div_mod (bv_unsigned sp) 32 ltac:(lia)) as D32. pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as D16. rewrite Hs1 in D16. lia. }
  (* [comment removed for export] *)
  assert (UNIT : exists abs0, (abs0 = [] \/ abs0 = SNAP_A) /\ ((abs0 = [] /\ statics_pristine LIBR_A mem) \/ (abs0 = SNAP_A /\ statics_snap SNAP_A mem))).
  { destruct Hstat as [HP|HS]; [exists []; split; [left; reflexivity | left; split; [reflexivity | exact HP]] | exists SNAP_A; split; [right; reflexivity | right; split; [reflexivity | exact HS]]]. }
  destruct UNIT as (abs0 & Habs0 & HABS).
  destruct (HUN s32 abs0 H32 Habs0) as (Un & HUOK & HGOK & HENV & ESP32 & ESEGS & ERO & SU & CHK & TOT & HIN & HSC).
  set (U := un_env Un) in *.
  pose proof (LAG.uenv_okb_sound U HUOK) as UOK. pose proof (LAG.glue_okb_sound U _ _ _ HGOK) as GOK.
  unfold envA_okb in HENV. apply andb_prop in HENV as [HENV HMAL]. apply andb_prop in HENV as [HENV HMS]. apply andb_prop in HENV as [HRT HGSH].
  apply Z.eqb_eq in HMS.
  assert (RTCOV : forall a b, In (a, b) RT_A -> bm_get (ue_rt U) a = Some b) by (intros a b; apply pairs_subb_sound; exact HRT).
  assert (GSHCOV : forall a b, In (a, b) GSH_A -> bm_get (ue_gsh U) a = Some b) by (intros a b; apply pairs_subb_sound; exact HGSH).
  assert (MALLOCS : forall pc k, LAC.mallocs_at (ue_malloc U) pc = Some k -> pc = MALLOC_A k).
  { intros pc k H. apply mallocs_at_In in H. rewrite forallb_forall in HMAL. specialize (HMAL _ H). cbn [fst snd] in HMAL. apply Z.eqb_eq in HMAL. exact HMAL. }
  (* [comment removed for export] *)
  assert (G2 : LAG.greg regs 2 = bv_unsigned sp) by (unfold LAG.greg; rewrite Hx2; reflexivity).
  assert (G10 : LAG.greg regs 10 = bv_unsigned data) by (unfold LAG.greg; rewrite Hx10; reflexivity).
  assert (G1 : LAG.greg regs 1 = bv_unsigned ret) by (unfold LAG.greg; rewrite Hx1; reflexivity).
  (* [comment removed for export] *)
  pose proof (LAG.entry_scells U UOK regs n c mem
                ltac:(intros a x Hin; rewrite HSC in Hin; destruct Hin as [Hin|[]]; injection Hin; intros _ <-; rewrite ESEGS; exact Hc)) as SCOK.
  pose proof (LAG.entry_R U LIBR_HULL_A LIBR_A SNAP_A UOK GOK ESEGS fx regs mem rom n (bv_unsigned c) FS ENTRY_A NMAX_A abs0) as ER.
  cbv zeta in ER. rewrite G2, G10, G1 in ER. rewrite ESEGS in ER.
  specialize (ER Hx11 Hx4 Hn Hret4 Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 ltac:(rewrite ESP32; reflexivity) Hdisj Hnoseg Hpay Hst ltac:(rewrite ERO; exact Hro) HABS Hhull
                 Hrt Hgsh Hshstk Hshpay Hfs Hctx Hap Hfrm).
  (* [comment removed for export] *)
  assert (SUM : forall sk rho S S' ms, wf_state S = true -> R U (LAG.rho_entry U regs n (bv_unsigned c)) FS mem rho S ms -> LASE.apply_sum Un sk S = Some S' ->
            exists ms' rho', msteps (ue_segs U) ms ms' /\ R U (LAG.rho_entry U regs n (bv_unsigned c)) FS mem rho' S' ms' /\ agree (s_next S) rho rho' /\ (s_next S <= s_next S')%nat).
  { intros sk rho S S' ms Hwf HR Hsum. unfold LASE.apply_sum in Hsum. change (un_env Un) with U in Hsum. destruct sk as [| |k| |]; try discriminate.
    - eapply LASUMC.apply_cbd_sound; try eassumption; try exact (LAG.go_tp _ _ _ _ GOK); try exact (LAG.go_cbd_pc _ _ _ _ GOK); try exact (LAG.go_cbd_fr _ _ _ _ GOK).
    - eapply LASUMM.apply_malloc_sound; try eassumption; try exact (LAG.go_tp _ _ _ _ GOK).
    - eapply LASUMS.apply_memset_sound; try eassumption; try exact (LAG.go_tp _ _ _ _ GOK). }
  (* [comment removed for export] *)
  destruct (LASE.unit_sound Un (LAG.rho_entry U regs n (bv_unsigned c)) mem FS UOK SCOK SUM
              CHK TOT (LAG.rho_entry U regs n (bv_unsigned c)) (@mkst fx regs (Z_to_bv 64 ENTRY_A) mem rom)) as (ms' & S & rho' & MS & EXIT & HR').
  { exists (entry_cut ENTRY_A NMAX_A s32 TP_A abs0). split; [exact HIN|]. change (un_env Un) with U. rewrite ESP32, (LAG.go_tp _ _ _ _ GOK) in ER. exact ER. }
  change (un_env Un) with U in MS. change (un_env Un) with U in HR'.
  (* [comment removed for export] *)
  destruct (LAG.exit_post U LIBR_HULL_A LIBR_A SNAP_A UOK GOK ESEGS (LAG.rho_entry U regs n (bv_unsigned c)) mem FS fx regs mem n (bv_unsigned c) Un S rho' ms'
              eq_refl eq_refl eq_refl SU Hx4 Hhull EXIT HR') as (fx' & regs' & mem' & Ems' & KEEP & A0 & FRAME & STAT & FSI & FRM').
  exists fx', regs', mem'.
  rewrite Ems' in MS. pose proof (msteps_rom _ _ _ MS) as ROM. cbn [ms_rom mkst] in ROM. rewrite ROM in MS.
  rewrite Hx1 in MS. change (ue_segs U) with (ue_segs (un_env Un)) in ESEGS. change (ue_segs U) with (ue_segs (un_env Un)) in MS.
  rewrite ?ESEGS in MS. rewrite G2 in FRAME.
  split; [exact MS|]. split; [exact KEEP|]. split; [exact A0|]. split; [exact FRAME|]. split; [exact STAT|]. split; [exact FSI | exact FRM'].
Qed.

(* [comment removed for export] *)
Corollary lxa_lib_stmt4 : forall U16p U16s U0p U0s : unitT,
  unit_obligation 16 [] U16p -> unit_obligation 16 SNAP_A U16s -> unit_obligation 0 [] U0p -> unit_obligation 0 SNAP_A U0s ->
  (forall k, (k = 1 \/ k = 4 \/ k = 5) -> malloc_stmt k) -> cbd_stmt_A ->
  lib_stmt_A.
Proof.
  intros U16p U16s U0p U0s H1 H2 H3 H4 HM HC. apply lxa_lib_stmt; [|exact HM|exact HC].
  intros s32 abs0 [-> | ->] [-> | ->]; eexists; eassumption.
Qed.

End LAF.
