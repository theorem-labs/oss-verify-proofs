(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface LibIface L5Defs L5Core.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmLibSanity_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopKitX_u5 TopSpecs_u5 HarnessXStretch_u5.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module HNXT.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma lor7_bounds : forall x, 0 <= x -> x <= Z.lor x 7 <= x + 7.
Proof.
  intros x Hx. pose proof (Z.add_lor_land x 7) as H. assert (L : Z.land x 7 = x mod 8).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
  rewrite L in H. assert (H0 : 0 <= x mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  set (a := Z.lor x 7) in *. set (m := x mod 8) in *. clearbody a m. clear L. lia.
Qed.
Lemma str_cap_bounds : forall n, 0 <= n -> n < PML.str_cap n <= n + 10.
Proof. intros n Hn. unfold PML.str_cap. pose proof (lor7_bounds n Hn). destruct (Z.eqb_spec (Z.lor n 7) 23); lia. Qed.
Lemma copy_cap_bounds : forall n, 0 <= n -> 0 < PML.copy_cap n <= n + 52.
Proof. intros n Hn. unfold PML.copy_cap. pose proof (lor7_bounds (Z.max n 44) ltac:(lia)). lia. Qed.

Lemma al8 : forall sp k, sp mod 16 = 0 -> k mod 8 = 0 -> (sp - k) mod 8 = 0.
Proof.
  intros sp k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r.
  - apply Z.divide_trans with 16; [exists 2; reflexivity | apply Z.mod_divide; [lia | exact H1]].
  - apply Z.mod_divide; [lia | exact H2].
Qed.
Ltac oos Hal := unfold PML.obj_on_stack; split; [lia|]; split; [lia|]; apply (al8 _ _ Hal); reflexivity.

Lemma not_outside : forall F a, ~ L5.outside F a -> exists w, In w F /\ L5.in_rng w a.
Proof.
  induction F as [|w F IH]; intros a H; [exfalso; apply H; intros w []|].
  destruct (classic (L5.in_rng w a)) as [Y|N]; [exists w; split; [left; reflexivity | exact Y]|].
  destruct (IH a) as (w' & Hw' & Hin); [|exists w'; split; [right; exact Hw' | exact Hin]].
  intros Ho. apply H. intros w0 [<-|Hw0]; [exact N | exact (Ho w0 Hw0)].
Qed.
Lemma frame_but_nil0 : forall (M M' : mem) a, L5.frame_but [(a, 0)] M M' -> M' = M.
Proof.
  intros M M' a H. apply FunctionalExtensionality.functional_extensionality. intros x. apply H. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
Qed.
Lemma land1_even : forall k, Z.land (2 * k) 1 = 0.
Proof. intros k. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Z.mul_comm. apply Z.mod_mul. discriminate. Qed.
Lemma land1_odd_low : forall w, Z.testbit w 0 = true -> Z.land (w mod 256) 1 = 1.
Proof.
  intros w H. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite <- Z.bit0_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite H. reflexivity.
Qed.
Lemma reg_of_u : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Definition in_footx (a : Z) : Prop := exists iv, In iv PML.ll_footx_xsrc /\ fst iv <= a < snd iv.
Lemma in_footx_iv : forall lo hi a, In (lo, hi) PML.ll_footx_xsrc -> lo <= a < hi -> in_footx a.
Proof. intros lo hi a Hin Ha. exists (lo, hi). split; [exact Hin | exact Ha]. Qed.
Lemma in_foot11_footx : forall a, PML.in_foot11 a -> in_footx a.
Proof. intros a (iv & Hiv & Hr). exists iv. split; [|exact Hr]. unfold PML.ll_footx_xsrc. apply in_or_app. left. exact Hiv. Qed.

Ltac ow := unfold L5.outside; let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w Hw Hin; unfold PML.ll_foot_xsrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia|]); destruct Hw.
Ltac cov_stack := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; split; [ow | left; lia].
Ltac wsi := let w := fresh "w" in let Hw := fresh "Hw" in intros w Hw; unfold PML.ll_foot_xsrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; lia|]); destruct Hw.
Ltac foot_in := first [ apply (in_footx_iv 0xdb5c0 0xdb5c2); [cbn; tauto | lia] | apply (in_footx_iv 0xdb840 0xdb842); [cbn; tauto | lia]
                      | apply (in_footx_iv 0xdb850 0xdba48); [cbn; tauto | lia] | apply (in_footx_iv 0xdbaf8 0xdbf78); [cbn; tauto | lia]
                      | apply (in_footx_iv 0xdc6a8 0xdc708); [cbn; tauto | lia] | apply (in_footx_iv 0xfd058 0xfd278); [cbn; tauto | lia]
                      | apply (in_footx_iv 0xdb5c8 0xdb610); [cbn; tauto | lia] ].
Ltac wfoot := let w := fresh "w" in let a := fresh "a" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w a Hw Hin; unfold PML.ll_foot_xsrc in Hw; cbn [In map fst snd] in Hw;
  repeat (destruct Hw as [<-|Hw]; [unfold L5.in_rng in Hin; cbn [fst snd] in Hin; first [left; lia | right; foot_in]|]); destruct Hw.
Ltac st_cov := apply TK2.statics_cov_keepH; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  assert (a < 0xfe000) by (destruct Ha as [(iv & Hiv & Hr)|Hr]; [unfold PML.ll_foot_xsrc in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]); destruct Hiv | unfold PML.IMG_RO_HI in Hr; lia]); ow.
Ltac lit_cov := apply TKX.lits_cov_keepH; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold PML.LIT_LO, PML.LIT_HI in Ha; ow.

(* [comment removed for export] *)
Lemma CS2 : In (bv_unsigned (2%bv : reg)) callee_saved_idx. Proof. cbn; tauto. Qed.
Lemma CS4 : In (bv_unsigned (4%bv : reg)) callee_saved_idx. Proof. cbn; tauto. Qed.
Lemma CS8 : In (bv_unsigned (8%bv : reg)) callee_saved_idx. Proof. cbn; tauto. Qed.
Lemma K8_4 : In (ridx (4%bv : reg)) HSX.KS8. Proof. cbn; tauto. Qed.
Lemma K8_8 : In (ridx (8%bv : reg)) HSX.KS8. Proof. cbn; tauto. Qed.
Lemma KS_4 : In (ridx (4%bv : reg)) TK.KS. Proof. cbn; tauto. Qed.
Ltac kin := first [exact CS2 | exact CS4 | exact CS8 | exact K8_4 | exact K8_8 | exact KS_4].
Lemma KS_in_KS8 : forall q, In q TK.KS -> In q HSX.KS8.
Proof. intros q Hq. cbn in Hq |- *. intuition lia. Qed.
Lemma KS_csaved : forall r : reg, In (ridx r) TK.KS -> In (bv_unsigned r) callee_saved_idx.
Proof. intros r Hr. unfold ridx in Hr. pose proof (bv_unsigned_in_range _ r) as X. cbn in Hr |- *. intuition lia. Qed.
Lemma KSP : forall Ra Rb, regs_preserved Ra Rb -> TK.keepsR HSX.KS8 Ra Rb.
Proof. intros Ra Rb HRP. apply TK.keepsR_preserved; [exact HRP | intros q Hq; cbn in Hq; cbn; intuition lia]. Qed.
Lemma KSc : forall R Ra Rb, TK.keepsR HSX.KS8 Ra Rb -> TK.keepsR TK.KS R Ra -> TK.keepsR TK.KS R Rb.
Proof. intros R Ra Rb H1 H2 r Hr. rewrite (H1 r (KS_in_KS8 _ Hr)). exact (H2 r Hr). Qed.

(* [comment removed for export] *)
Lemma nodup_mid : forall (A B C : list (Z * Z)) (x : Z * Z), base.NoDup (map fst (A ++ x :: B ++ C)) -> forall b, In b B -> fst b <> fst x.
Proof.
  induction A as [|a A IH]; intros B C x ND b Hb.
  - cbn [app map] in ND. inversion ND as [|y l N1 N2]; subst. intros X. apply N1. apply stdpp.base.list_elem_of_In. rewrite <- X. apply in_map. apply in_or_app. left. exact Hb.
  - cbn [app map] in ND. inversion ND as [|y l N1 N2]; subst. exact (IH B C x N2 b Hb).
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPDELS : PMS.opdel_sized_spec L HI.
Hypothesis LOCDTOR : PMS.locale_dtor_spec L.
Hypothesis ISTRDTOR : TPS.istream_dtor_spec L.
Hypothesis IOSBDTOR : TPS.iosb_dtor_spec L.

Lemma mk_entry : forall R M spc r scr, getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  L5C.stk (hl_sptop L) M spc scr -> PML.entry L R M spc r scr.
Proof. intros R M spc r scr H1 Hra H2 H4 Hs. split; [exact H1|]. split; [exact Hra|]. split; [exact H2|]. split; [exact H4 | exact Hs]. Qed.

(* [comment removed for export] *)
Lemma mk_stk : forall LB0 sp SS (foot : Z -> Prop) M0 M spc scr, TK2.FR L LB0 sp SS foot M0 M -> sp mod 16 = 0 -> spc = sp - 1376 -> 0 <= scr -> 1376 + scr <= SS ->
  hl_ceil L + SS <= sp -> sp <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> L5C.stk (hl_sptop L) M spc scr.
Proof.
  intros LB0 sp SS foot M0 M spc scr [_ F2] Hal -> Hscr HSS Hc Hs Htop. unfold hl_ceil in Hc.
  split; [rewrite <- Z.add_opp_r, Z.add_mod, Hal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Htop|].
  intros i Hi. apply F2. lia.
Qed.

Lemma ra_ok_lit : forall r, 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> L5.ra_ok r.
Proof. intros r H1 H2. split; assumption. Qed.

Lemma csaved_cases : forall r : reg, In (bv_unsigned r) callee_saved_idx -> r = 2%bv \/ r = 8%bv \/ In (ridx r) TK.KS.
Proof.
  intros r H. unfold callee_saved_idx in H. cbn [In] in H.
  destruct H as [H|[H|[H|[H|H]]]]; [left; apply bv_eq; rewrite <- H; reflexivity | right; right; unfold ridx; rewrite <- H; cbn; tauto | right; right; unfold ridx; rewrite <- H; cbn; tauto
                                   | right; left; apply bv_eq; rewrite <- H; reflexivity |].
  right; right. unfold ridx. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H.
Qed.

(* [comment removed for export] *)
Section Run.
Variable Lay : lib_layout.
Hypothesis LH : ll_heap Lay = L.
Hypothesis LF : ll_foot Lay = PML.ll_footx_xsrc.
Hypothesis LC : forall n, ll_credit Lay n = PMX.pm_creditx L n.
Let SS := ll_stack Lay.
Hypothesis HSS : 1376 + 9568 <= SS.
Variables (LB : list (Z * Z)) (cr : credit) (sp ra : Z) (payload : list byte) (R : bvmap 5 word) (M : mem) (model : Model) (K : ShapeAlg.TSet).
Let n := Z.of_nat (length payload).
Hypothesis Psp : getr R 2%bv = Z_to_bv 64 sp.
Hypothesis Ptp : getr R 4%bv = Z_to_bv 64 PML.TP.
Hypothesis Plen : 0 <= n < 2 ^ 26.
Hypothesis Prok : L5.ra_ok ra.
Hypothesis SPOK : HSX.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis BOK0 : TK2.blocks_ok L LB.
Hypothesis HK0 : K [].
Hypothesis CONT : forall (fx' : FPState) (g' : PML.ls_state) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit),
  PML.fp_ok fx' -> lib_post Lay PMX.pm_staticsx g' LB cr sp payload R M R' M' cr' -> hi_heap HI LB cr' M' (m_vmmaps model') -> model_but_vm model model' ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' ra M' model') K.

(* [comment removed for export] *)
Definition pers (reps : PML.srep) (Mk : mem) : Prop :=
  L5.u64_at RSEGS Mk (sp - 8) ra /\ L5.u64_at RSEGS Mk (sp - 16) (bv_unsigned (getr R 8%bv)) /\ PML.str_at_w Mk (sp - 40) reps.
Lemma pers_x : forall (Kc : Z -> Prop) M1 M2 reps, TK.samem Kc M1 M2 -> TK2.cov Kc (sp - 40) 40 -> TK2.str_cov Kc (sp - 40) reps -> pers reps M1 -> pers reps M2.
Proof.
  intros Kc M1 M2 reps AG HC HS (A & B & C). destruct SPOK as [S1 S2].
  split; [apply (TK2.u64_x Kc M1 M2 AG); [lia | eapply TK2.cov_sub; [exact HC | lia | lia] | exact A]|].
  split; [apply (TK2.u64_x Kc M1 M2 AG); [lia | eapply TK2.cov_sub; [exact HC | lia | lia] | exact B]|].
  apply (TK2.str_at_w_x Kc M1 M2 AG); [lia | exact HS | exact C].
Qed.

(* [comment removed for export] *)
Lemma tail2 : forall (fxk : FPState) Rk Mk modelk crk gk,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1376) -> TK.keepsR TK.KS R Rk -> L5.u64_at RSEGS Mk (sp - 8) ra -> L5.u64_at RSEGS Mk (sp - 16) (bv_unsigned (getr R 8%bv)) ->
  TK2.FR L LB sp SS in_footx M Mk -> model_but_vm model modelk -> PML.model_ok modelk -> hi_heap HI LB crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> gk <> PML.LS0 -> PML.lits_ok Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk 0x3a758 Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk Hfp Rsp KSk Cra Cs0 FRk BVk (Hh & Hl & Hmat) HHk LSk Gk LITk CRk.
  apply (HSX.s_r_opdel2 FPM fxk Rk Mk modelk K sp ra (bv_unsigned (getr R 8%bv)) Hh Hl Hfp Rsp SPOK Cra Cs0 Prok).
  { pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as X. change (bv_modulus 64) with (2 ^ 64) in X. lia. }
  intros fx' R' Hfp' R'sp R'a0 R's0 KS'.
  apply (CONT fx' gk R' Mk modelk crk Hfp'); [| exact HHk | exact BVk].
  constructor.
  - exact R'a0.
  - intros r Hr. destruct (csaved_cases r Hr) as [->|[->|Hin]].
    + rewrite R'sp, Psp. reflexivity.
    + rewrite R's0. apply Z_to_bv_bv_unsigned.
    + rewrite (KS' r Hin). exact (KSk r Hin).
  - exact CRk.
  - intros a Ha HC HF HE. rewrite LH in HC, HE. apply (proj1 FRk a Ha HC); [|exact HE]. intros X. apply HF. unfold in_foot. rewrite LF. exact X.
  - intros a Ha. apply (proj2 FRk). exact Ha.
  - split; [exact LSk|]. destruct gk; [exfalso; exact (Gk eq_refl) | exact LITk | exact LITk].
Qed.

(* [comment removed for export] *)
Lemma step_out : forall F reps gk M1 M2 crk modelk,
  TK.samem (L5.outside F) M1 M2 -> mem_grows M1 M2 ->
  (forall w, In w F -> (sp - SS <= fst w /\ fst w + snd w <= sp - 40 /\ 0 <= snd w)) ->
  pers reps M1 -> PML.ls_ok gk M1 -> PML.lits_ok M1 -> TK2.FR L LB sp SS in_footx M M1 -> hi_heap HI (PML.srep_blocks reps ++ LB) crk M1 (m_vmmaps modelk) ->
  pers reps M2 /\ PML.ls_ok gk M2 /\ PML.lits_ok M2 /\ TK2.FR L LB sp SS in_footx M M2 /\ hi_heap HI (PML.srep_blocks reps ++ LB) crk M2 (m_vmmaps modelk).
Proof.
  intros F reps gk M1 M2 crk modelk AG MG HF PE LSk LITk FRk HHk. destruct SPOK as [S1 S2].
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HHk) as BOK.
  assert (WSI : TK2.w_si L F) by (intros w Hw; left; destruct (HF w Hw); lia).
  assert (OUT : forall a, ~ (sp - SS <= a < sp - 40) -> L5.outside F a) by (intros a Ha w Hw Hin; unfold L5.in_rng in Hin; destruct (HF w Hw); lia).
  split; [|split; [|split; [|split]]].
  - apply (pers_x _ M1 M2 reps AG); [intros i Hi; apply OUT; lia | | exact PE].
    apply (TK2.str_cov_out L LAY); [lia | intros i Hi; apply OUT; lia | exact WSI | intros b Hb; apply BOK; apply in_or_app; left; exact Hb].
  - apply (TK2.ls_ok_x _ M1 M2 AG); [|exact LSk]. apply (TK2.statics_cov_out L); [intros w Hw; destruct (HF w Hw); lia | lia].
  - apply (TKX.lits_ok_x _ M1 M2 AG); [|exact LITk]. intros a Ha. apply OUT. unfold PML.LIT_LO, PML.LIT_HI in Ha. unfold hl_ceil in Hceil. lia.
  - apply (TK2.FR_grows L LAY LB sp SS _ M M1 M2 _ FRk AG MG BOK0 Hceil ltac:(lia)). intros a Ha. left. destruct (not_outside F a Ha) as (w & Hw & Hin).
    unfold L5.in_rng in Hin. destruct (HF w Hw). lia.
  - apply (TK2.heap_stack_write L HI HIok LAY _ _ M1 M2 _ (sp - SS) sp HHk); [lia | lia | lia | | exact MG].
    apply (TK.samem_weaken _ _ _ _ AG). intros a Ha. apply OUT. lia.
Qed.

(* [comment removed for export] *)
Lemma tail1 : forall (fxk : FPState) Rk Mk modelk crk gk reps rd,
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1376) -> getr Rk 8%bv = Z_to_bv 64 HSX.VTT_ISS -> TK.keepsR TK.KS R Rk ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) ->
  TK2.FR L LB sp SS in_footx M Mk -> model_but_vm model modelk -> PML.model_ok modelk -> hi_heap HI (PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> gk <> PML.LS0 -> PML.lits_ok Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  L5.u64_at RSEGS Mk (sp - 288) PML.CLASSIC_IMP -> PML.iosb_at Mk (sp - 192) rd (sp - 296) ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk 0x3a710 Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rd Hfp Rsp Rs0 KSk PE BLs FRk BVk MOK HHk LSk Gk LITk CRk LOCc IOSB.
  destruct MOK as (Hh & Hl & Hmat). pose proof SPOK as [S1 S2].
  pose proof KS_in_KS8 as KS8in.
  (* [comment removed for export] *)
  apply (HSX.s_r_opdel1 FPM fxk Rk Mk modelk K sp Hh Hl Hfp Rsp SPOK (proj1 LSk)).
  { intros i Hi. apply (proj2 FRk). lia. }
  intros fx1 R1 M1 Hfp1 R1sp R1ra R1a0 KS1 _ AG1 MG1.
  assert (AG1o : TK.samem (L5.outside [(sp - 296, 8)]) Mk M1).
  { apply (TK.samem_weaken _ _ _ _ AG1). intros a Ho Hin. apply (Ho (sp - 296, 8) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. lia. }
  destruct (step_out _ reps gk Mk M1 crk modelk AG1o MG1 ltac:(intros w [<-|[]]; cbn [fst snd]; lia) PE LSk LITk FRk HHk) as (PE1 & LS1 & LIT1 & FR1 & HH1).
  assert (LOC1 : L5.u64_at RSEGS M1 (sp - 288) PML.CLASSIC_IMP) by (apply (TK2.u64_x _ Mk M1 AG1o); [lia | intros i Hi; ow | exact LOCc]).
  assert (IOSB1 : PML.iosb_at M1 (sp - 192) rd (sp - 296)) by (apply (TK2.iosb_at_x _ Mk M1 AG1o); [lia | intros i Hi; ow | exact IOSB]).
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS1 4%bv ltac:(kin)), (KSk 4%bv ltac:(kin)); exact Ptp).
  assert (STKg : forall Mx scr, TK2.FR L LB sp SS in_footx M Mx -> 0 <= scr -> 1376 + scr <= SS -> L5C.stk (hl_sptop L) Mx (sp - 1376) scr).
  { intros Mx scr FRx H1 H2. apply (mk_stk LB sp SS _ M Mx _ _ FRx S2 eq_refl H1 H2 Hceil Hsptop Htop). }
  apply (LOCDTOR (sp - 288) (sp - 1376) 0x3a728 fx1 R1 M1 modelk K Hh Hl HK0 Hfp1).
  { split; [apply mk_entry; [exact R1ra | apply ra_ok_lit; [lia | reflexivity] | exact R1sp | exact TP1 | apply STKg; [exact FR1 | lia | lia]]|]. split; [exact R1a0 | split; [lia | exact LOC1]]. }
  intros fx2 R2 M2 Hfp2 _ RP2 FB2 _. rewrite (frame_but_nil0 M1 M2 _ FB2). clear FB2 M2.
  assert (R2sp : getr R2 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP2 2%bv ltac:(kin)); exact R1sp).
  assert (R2s0 : getr R2 8%bv = Z_to_bv 64 HSX.VTT_ISS) by (rewrite (RP2 8%bv ltac:(kin)), (KS1 8%bv ltac:(kin)); exact Rs0).
  (* [comment removed for export] *)
  apply (HSX.s_r_locdtor FPM fx2 R2 M1 modelk K sp HSX.VTT_ISS Hh Hl Hfp2 R2sp SPOK R2s0 ltac:(unfold HSX.VTT_ISS; lia)).
  intros fx3 R3 Hfp3 R3sp R3ra _ _ KS3.
  assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS3 4%bv ltac:(kin)), (RP2 4%bv ltac:(kin)); exact TP1).
  apply (ISTRDTOR (sp - 1376) 0x3a734 fx3 R3 M1 modelk K Hh Hl HK0 Hfp3).
  { apply mk_entry; [exact R3ra | apply ra_ok_lit; [lia | reflexivity] | exact R3sp | exact TP3 | apply STKg; [exact FR1 | lia | lia]]. }
  intros fx4 R4 M4 Hfp4 _ RP4 FB4 _. rewrite (frame_but_nil0 M1 M4 _ FB4). clear FB4 M4.
  assert (R4sp : getr R4 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP4 2%bv ltac:(kin)); exact R3sp).
  (* [comment removed for export] *)
  apply (HSX.s_r_istrdtor FPM fx4 R4 M1 modelk K sp Hh Hl Hfp4 R4sp SPOK).
  intros fx5 R5 Hfp5 R5sp R5ra R5a0 KS5.
  assert (TP5 : getr R5 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS5 4%bv ltac:(kin)), (RP4 4%bv ltac:(kin)); exact TP3).
  apply (IOSBDTOR (sp - 192) rd (sp - 296) (sp - 1376) 0x3a73c fx5 R5 M1 modelk K Hh Hl HK0 Hfp5).
  { split; [apply mk_entry; [exact R5ra | apply ra_ok_lit; [lia | reflexivity] | exact R5sp | exact TP5 | apply STKg; [exact FR1 | unfold TPS.IOSB_SCR; lia | unfold TPS.IOSB_SCR; lia]]|].
    split; [exact R5a0|]. split; [exact IOSB1 | oos S2]. }
  intros fx6 R6 M6 Hfp6 _ RP6 FB6 MG6. unfold TPS.IOSB_SCR in FB6. pose proof (TK2.frame_but_samem _ _ _ FB6) as AG6.
  destruct (step_out _ reps gk M1 M6 crk modelk AG6 MG6 ltac:(intros w [<-|[<-|[]]]; cbn [fst snd]; lia) PE1 LS1 LIT1 FR1 HH1) as (PE6 & LS6 & LIT6 & FR6 & HH6).
  assert (R6sp : getr R6 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP6 2%bv ltac:(kin)); exact R5sp).
  assert (KS6 : TK.keepsR TK.KS R R6).
  { intros r Hr. pose proof (KS_csaved r Hr) as Hc.
    rewrite (RP6 r Hc), (KS5 r (KS8in _ Hr)), (RP4 r Hc), (KS3 r (KS8in _ Hr)), (RP2 r Hc), (KS1 r (KS8in _ Hr)). exact (KSk r Hr). }
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH6) as BOK6.
  pose proof PE6 as (Cra6 & Cs06 & STR6).
  (* [comment removed for export] *)
  destruct reps as [s | cap p s]; cbn [PML.str_at_w] in STR6.
  - destruct STR6 as (Sl & Sb0 & _).
    apply (HSX.s_r_iosbdtor FPM fx6 R6 M6 modelk K sp (2 * Z.of_nat (length s)) Hh Hl Hfp6 R6sp SPOK Sb0 ltac:(lia)).
    intros fx7 R7 Hfp7 R7sp R7a0 KS7. rewrite land1_even in R7a0. apply reg_of_u in R7a0.
    apply (HSX.s_b2_short FPM fx7 R7 M6 modelk K sp Hh Hl Hfp7 R7sp SPOK R7a0).
    intros fx8 R8 Hfp8 R8sp KS8.
    apply (tail2 fx8 R8 M6 modelk crk gk Hfp8 R8sp); [| exact Cra6 | exact Cs06 | exact FR6 | exact BVk | exact (conj Hh (conj Hl Hmat)) | exact HH6 | exact LS6 | exact Gk | exact LIT6 | exact CRk].
    intros r Hr. rewrite (KS8 r (KS8in _ Hr)), (KS7 r (KS8in _ Hr)). exact (KS6 r Hr).
  - destruct STR6 as ((Sbit & Sw0 & Sw8 & Sw16 & _) & _).
    destruct (BOK6 (p, cap) (or_introl eq_refl)) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in *.
    pose proof (BLs (p, cap) (or_introl eq_refl)) as BC. cbn [snd] in BC.
    pose proof (TK2.u64_u8_low M6 (sp - 40) (cap + 1) ltac:(lia) ltac:(lia) Sw0) as Sb0.
    apply (HSX.s_r_iosbdtor FPM fx6 R6 M6 modelk K sp ((cap + 1) mod 256) Hh Hl Hfp6 R6sp SPOK Sb0).
    { pose proof (Z.mod_pos_bound (cap + 1) 256 ltac:(lia)). lia. }
    intros fx7 R7 Hfp7 R7sp R7a0 KS7. rewrite (land1_odd_low _ Sbit) in R7a0. apply reg_of_u in R7a0.
    replace (sp - 40 + 16) with (sp - 24) in Sw16 by lia.
    apply (HSX.s_b2_long FPM fx7 R7 M6 modelk K sp (cap + 1) p Hh Hl Hfp7 R7sp SPOK R7a0 Sw0 Sw16 ltac:(lia) ltac:(lia)).
    intros fx8 R8 Hfp8 R8sp R8ra R8a0 KS8.
    assert (TP8 : getr R8 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS8 4%bv ltac:(kin)), (KS7 4%bv ltac:(kin)), (KS6 4%bv ltac:(kin)); exact Ptp).
    apply (OPDELS ([(p, cap)] ++ LB) crk p cap (sp - 1376) 0x3a758 fx8 R8 M6 modelk K HH6 (conj Hh (conj Hl Hmat)) HK0 Hfp8).
    { split; [apply mk_entry; [exact R8ra | apply ra_ok_lit; [lia | reflexivity] | exact R8sp | exact TP8 | apply STKg; [exact FR6 | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia]]|].
      split; [exact R8a0 | left; reflexivity]. }
    intros fx9 R9 M9 model9 LB9 cr9 LBk9 W9 Hfp9 (-> & -> & -> & ->) RP9 HP9 BV9 HH9.
    cbn [app lb_remove fst] in HH9, HP9. rewrite Z.eqb_refl in HH9, HP9.
    assert (STK6 : L5C.stk (hl_sptop L) M6 (sp - 1376) PMS.OPDEL_SCR) by (apply STKg; [exact FR6 | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia]).
    pose proof (TK2.hpres_samem L LAY LB (sp - 1376) _ _ M6 M9 HP9 BOK0 STK6 ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia)) as AG9.
    assert (R9sp : getr R9 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP9 2%bv ltac:(kin)); exact R8sp).
    apply (tail2 fx9 R9 M9 model9 crk gk Hfp9 R9sp).
    + intros r Hr. pose proof (KS_csaved r Hr) as Hc.
      rewrite (RP9 r Hc), (KS8 r (KS8in _ Hr)), (KS7 r (KS8in _ Hr)). exact (KS6 r Hr).
    + apply (TK2.u64_x _ M6 M9 AG9); [lia | cov_stack | exact Cra6].
    + apply (TK2.u64_x _ M6 M9 AG9); [lia | cov_stack | exact Cs06].
    + apply (TK2.FR_hpres L LAY LB sp SS _ M M6 M9 LB (sp - 1376) _ _ FR6 HP9 BOK0 (incl_refl _) Hceil ltac:(lia) ltac:(lia)); [unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | intros w a []].
    + exact (L5C.model_but_vm_trans _ _ _ BVk BV9).
    + split; [rewrite (L5C.halted_but_vm _ _ BV9); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV9); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV9); exact Hmat]].
    + exact HH9.
    + apply (TK2.ls_ok_x _ M6 M9 AG9); [st_cov | exact LS6].
    + exact Gk.
    + apply (TKX.lits_ok_x _ M6 M9 AG9); [lit_cov | exact LIT6].
    + exact CRk.
Qed.

Ltac mok BV Hh Hl Hmat := split; [rewrite (L5C.halted_but_vm _ _ BV); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV); exact Hmat]].

(* [comment removed for export] *)
Definition w_ok (W : list L5.range) : Prop :=
  forall w, In w W -> (sp - 1376 <= fst w /\ fst w + snd w <= sp - 40) \/ (0x10000 <= fst w /\ fst w + snd w <= 0xfe000 /\ forall a, L5.in_rng w a -> in_footx a).
Lemma step_heap : forall reps M1 M2 LBk scr W,
  L5C.hpres L LBk (sp - 1376) scr W M1 M2 -> TK2.blocks_ok L LBk -> incl (PML.srep_blocks reps ++ LB) LBk -> 0 <= scr -> 1376 + scr <= SS -> w_ok W ->
  pers reps M1 -> TK2.FR L LB sp SS in_footx M M1 ->
  pers reps M2 /\ TK2.FR L LB sp SS in_footx M M2 /\ TK.samem (TK2.keepH L LBk W (sp - 1376) scr) M1 M2 /\ TK2.w_si L W.
Proof.
  intros reps M1 M2 LBk scr W HP BOK Hincl Hscr Hs HW PE FRk. destruct SPOK as [S1 S2].
  assert (STK : L5C.stk (hl_sptop L) M1 (sp - 1376) scr) by (apply (mk_stk LB sp SS _ M M1 _ _ FRk S2 eq_refl Hscr Hs Hceil Hsptop Htop)).
  pose proof (TK2.hpres_samem L LAY LBk (sp - 1376) scr W M1 M2 HP BOK STK Hscr) as AG.
  assert (WSI : TK2.w_si L W) by (intros w Hw; destruct (HW w Hw) as [X|X]; [left; lia | right; lia]).
  assert (OUT : forall a, sp - 40 <= a -> L5.outside W a) by (intros a Ha w Hw Hi; unfold L5.in_rng in Hi; destruct (HW w Hw) as [X|X]; lia).
  split; [|split; [|split]].
  - apply (pers_x _ M1 M2 reps AG); [intros i Hi; split; [apply OUT; lia | left; lia] | | exact PE].
    apply (TK2.str_cov_keepH L LAY); [lia | intros i Hi; split; [apply OUT; lia | left; lia] | exact WSI |].
    intros b Hb. assert (Hb' : In b LBk) by (apply Hincl; apply in_or_app; left; exact Hb). split; [exact Hb' | exact (BOK b Hb')].
  - apply (TK2.FR_hpres L LAY LB sp SS _ M M1 M2 LBk (sp - 1376) scr W FRk HP BOK0); [intros b Hb; apply Hincl; apply in_or_app; right; exact Hb | exact Hceil | lia | lia | lia | lia | exact Hscr |].
    intros w a Hw Hi. destruct (HW w Hw) as [X|(_ & _ & X)]; [left; unfold L5.in_rng in Hi; lia | right; exact (X a Hi)].
  - exact AG.
  - exact WSI.
Qed.

(* [comment removed for export] *)
Lemma tail0 : forall (fxk : FPState) Rk Mk modelk crk gk reps rep gp' rdst',
  PML.fp_ok fxk -> getr Rk 2%bv = Z_to_bv 64 (sp - 1376) -> TK.keepsR TK.KS R Rk ->
  pers reps Mk -> (forall b, In b (PML.srep_blocks reps) -> 0 <= snd b <= n + 10) -> (forall b, In b (PML.srep_blocks rep) -> 0 <= snd b <= n + 52) ->
  TK2.FR L LB sp SS in_footx M Mk -> model_but_vm model modelk -> PML.model_ok modelk ->
  hi_heap HI (PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) crk Mk (m_vmmaps modelk) ->
  PML.ls_ok gk Mk -> gk <> PML.LS0 -> PML.lits_ok Mk -> credit_le (credit_sub cr (ll_credit Lay n)) crk ->
  PML.isrc_at Mk (sp - 312) rep gp' rdst' ->
  srealizes RSEGS SCFG (@PML.cfg fxk Rk 0x3a6c0 Mk modelk) K.
Proof.
  intros fxk Rk Mk modelk crk gk reps rep gp' rdst' Hfp14 R14sp KS14 PE14 BLs CAPr FR14 BV14' MOK14 HH14 LS14 Gk LIT14 CR10 ISRC14.
  destruct MOK14 as (Hh14 & Hl14 & Hmat14). pose proof SPOK as [S1 S2]. pose proof KS_in_KS8 as KS8in.
  set (LB4 := PML.srep_blocks rep ++ PML.srep_blocks reps ++ LB) in *.
  assert (INs : forall b, In b (PML.srep_blocks reps) -> In b LB4) by (intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (INr : forall b, In b (PML.srep_blocks rep) -> In b LB4) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH14) as BOK5.
  assert (STKg : forall Mx scr, TK2.FR L LB sp SS in_footx M Mx -> 0 <= scr -> 1376 + scr <= SS -> L5C.stk (hl_sptop L) Mx (sp - 1376) scr).
  { intros Mx scr FRx H1 H2. apply (mk_stk LB sp SS _ M Mx _ _ FRx S2 eq_refl H1 H2 Hceil Hsptop Htop). }
  (* [comment removed for export] *)
  pose proof ISRC14 as ISX. unfold PML.isrc_at in ISX. cbv zeta in ISX.
  destruct ISX as (_ & _ & A24 & _ & _ & _ & _ & _ & _ & _ & As & _ & _ & _ & Aio & _ & Adef).
  replace (sp - 312 + 80) with (sp - 232) in As by lia. replace (sp - 312 + 24) with (sp - 288) in A24 by lia.
  replace (sp - 312 + 120) with (sp - 192) in Aio by lia. replace (sp - 312 + 16) with (sp - 296) in Aio by lia.
  assert (BX : exists b, L5.u8_at RSEGS Mk (sp - 232) b /\ 0 <= b <= 255 /\
                ((Z.land b 1 = 0 /\ PML.srep_blocks rep = []) \/
                 (Z.land b 1 = 1 /\ exists cap1 p1 s1, rep = PML.SLong cap1 p1 s1 /\ L5.u64_at RSEGS Mk (sp - 232) (cap1 + 1) /\ L5.u64_at RSEGS Mk (sp - 216) p1))).
  { destruct rep as [s1 | cap1 p1 s1]; cbn [PML.str_at] in As.
    - destruct As as (Sl & Sb0 & _). exists (2 * Z.of_nat (length s1)). split; [exact Sb0|]. split; [lia|]. left. split; [apply land1_even | reflexivity].
    - destruct As as ((Sbit & Sw0 & Sw8 & Sw16 & _) & _). pose proof (CAPr (p1, cap1) (or_introl eq_refl)) as BC. cbn [snd] in BC.
      exists ((cap1 + 1) mod 256). split; [apply (TK2.u64_u8_low Mk (sp - 232) (cap1 + 1)); [lia | lia | exact Sw0]|].
      split; [pose proof (Z.mod_pos_bound (cap1 + 1) 256 ltac:(lia)); lia|]. right. split; [exact (land1_odd_low _ Sbit)|].
      exists cap1, p1, s1. split; [reflexivity|]. split; [exact Sw0|]. replace (sp - 216) with (sp - 232 + 16) by lia. exact Sw16. }
  destruct BX as (b0 & Bu8 & Brng & BC).
  apply (HSX.s_r_opdel0 FPM fxk Rk Mk modelk K sp b0 Hh14 Hl14 Hfp14 R14sp SPOK (proj1 LS14)); [apply (L5.defined_sub _ _ _ _ _ Adef); lia | apply (L5.defined_sub _ _ _ _ _ Adef); lia | apply (L5.defined_sub _ _ _ _ _ Adef); lia | exact Bu8 | exact Brng |].
  intros fx16 R16 M16 Hfp16 R16sp R16s0 R16a1 KS16 _ _ _ AG16 MG16.
  assert (AG16o : TK.samem (L5.outside [(sp - 312, 8); (sp - 296, 8); (sp - 192, 8)]) Mk M16).
  { apply (TK.samem_weaken _ _ _ _ AG16). intros a Ho. repeat split; intros Hin; [apply (Ho (sp - 312, 8)) | apply (Ho (sp - 296, 8)) | apply (Ho (sp - 192, 8))]; try (cbn; tauto); unfold L5.in_rng; cbn [fst snd]; lia. }
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH14) as BOK.
  assert (WSI16 : TK2.w_si L [(sp - 312, 8); (sp - 296, 8); (sp - 192, 8)]) by (intros w [<-|[<-|[<-|[]]]]; cbn [fst snd]; left; unfold hl_ceil in Hceil; lia).
  assert (OUT16 : forall a, ~ (sp - SS <= a < sp - 40) -> L5.outside [(sp - 312, 8); (sp - 296, 8); (sp - 192, 8)] a).
  { intros a Ha w [<-|[<-|[<-|[]]]] Hi; unfold L5.in_rng in Hi; cbn [fst snd] in Hi; lia. }
  assert (PE16 : pers reps M16).
  { apply (pers_x _ Mk M16 reps AG16o); [intros i Hi; apply OUT16; lia | | exact PE14].
    apply (TK2.str_cov_out L LAY); [lia | intros i Hi; apply OUT16; lia | exact WSI16 | intros b Hb; apply BOK; apply INs; exact Hb]. }
  assert (FR16 : TK2.FR L LB sp SS in_footx M M16).
  { apply (TK2.FR_grows L LAY LB sp SS _ M Mk M16 _ FR14 AG16o MG16 BOK0 Hceil ltac:(lia)). intros a Ha. left. destruct (not_outside _ a Ha) as (w & Hw & Hin).
    destruct Hw as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
  assert (HH16 : hi_heap HI LB4 crk M16 (m_vmmaps modelk)).
  { apply (TK2.heap_stack_write L HI HIok LAY _ _ Mk M16 _ (sp - SS) sp HH14); [lia | lia | lia | | exact MG16]. apply (TK.samem_weaken _ _ _ _ AG16o). intros a Ha. apply OUT16. lia. }
  assert (SC16 : TK2.statics_cov (L5.outside [(sp - 312, 8); (sp - 296, 8); (sp - 192, 8)])) by (apply (TK2.statics_cov_out L); [intros w [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold hl_ceil in Hceil; lia | lia]).
  pose proof (TK2.ls_ok_x _ Mk M16 AG16o SC16 gk LS14) as LS16.
  assert (LIT16 : PML.lits_ok M16) by (apply (TKX.lits_ok_x _ Mk M16 AG16o); [intros a Ha; apply OUT16; unfold PML.LIT_LO, PML.LIT_HI in Ha; unfold hl_ceil in Hceil; lia | exact LIT14]).
  assert (LOC16 : L5.u64_at RSEGS M16 (sp - 288) PML.CLASSIC_IMP) by (apply (TK2.u64_x _ Mk M16 AG16o); [lia | intros i Hi; ow | exact A24]).
  assert (IOSB16 : PML.iosb_at M16 (sp - 192) rdst' (sp - 296)) by (apply (TK2.iosb_at_xg _ Mk M16 AG16o); [lia | intros i Hi; ow | exact MG16 | exact Aio]).
  assert (KS16' : TK.keepsR TK.KS R R16) by (intros r Hr; rewrite (KS16 r Hr); exact (KS14 r Hr)).
  destruct BC as [(BL0 & NOB) | (BL1 & cap1 & p1 & s1 & -> & Cw0 & Cp)].
  - (* [comment removed for export] *)
    rewrite BL0 in R16a1. apply reg_of_u in R16a1.
    apply (HSX.s_b1_short FPM fx16 R16 M16 modelk K sp Hh14 Hl14 Hfp16 R16sp SPOK R16a1).
    intros fx17 R17 Hfp17 R17sp KS17.
    unfold LB4 in HH16. rewrite NOB in HH16. cbn [app] in HH16.
    apply (tail1 fx17 R17 M16 modelk crk gk reps rdst' Hfp17 R17sp); [rewrite (KS17 8%bv ltac:(kin)); exact R16s0 | exact (KSc _ _ _ KS17 KS16') | exact PE16 | exact BLs | exact FR16 | exact BV14' | exact (conj Hh14 (conj Hl14 Hmat14)) | exact HH16 | exact LS16 | exact Gk | exact LIT16 | exact CR10 | exact LOC16 | exact IOSB16].
  - (* [comment removed for export] *)
    rewrite BL1 in R16a1. apply reg_of_u in R16a1.
    pose proof (CAPr (p1, cap1) (or_introl eq_refl)) as BCp. cbn [snd] in BCp.
    destruct (BOK5 (p1, cap1) (INr _ (or_introl eq_refl))) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in B0, B1, B2, B3, B4.
    assert (Cw0' : L5.u64_at RSEGS M16 (sp - 232) (cap1 + 1)) by (apply (TK2.u64_x _ Mk M16 AG16o); [lia | intros i Hi; ow | exact Cw0]).
    assert (Cp' : L5.u64_at RSEGS M16 (sp - 216) p1) by (apply (TK2.u64_x _ Mk M16 AG16o); [lia | intros i Hi; ow | exact Cp]).
    apply (HSX.s_b1_long FPM fx16 R16 M16 modelk K sp (cap1 + 1) p1 Hh14 Hl14 Hfp16 R16sp SPOK R16a1 Cw0' Cp' ltac:(lia) ltac:(lia)).
    intros fx17 R17 Hfp17 R17sp R17ra R17a0 KS17.
    assert (TP17 : getr R17 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS17 4%bv ltac:(kin)), (KS16' 4%bv ltac:(kin)); exact Ptp).
    apply (OPDELS LB4 crk p1 cap1 (sp - 1376) 0x3a710 fx17 R17 M16 modelk K HH16 (conj Hh14 (conj Hl14 Hmat14)) HK0 Hfp17).
    { split; [apply mk_entry; [exact R17ra | apply ra_ok_lit; [lia | reflexivity] | exact R17sp | exact TP17 | apply STKg; [exact FR16 | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia | unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia]]|].
      split; [exact R17a0 | left; reflexivity]. }
    intros fx18 R18 M18 model18 LB18 cr18 LBk18 W18 Hfp18 (-> & -> & -> & ->) RP18 HP18 BV18 HH18.
    unfold LB4 in HP18, HH18. cbn [PML.srep_blocks app lb_remove fst] in HP18, HH18. rewrite Z.eqb_refl in HP18, HH18.
    assert (MOK18 : PML.model_ok model18) by (mok BV18 Hh14 Hl14 Hmat14).
    destruct (step_heap reps M16 M18 _ _ _ HP18 (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH18) (incl_refl _) ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia) ltac:(unfold PMS.OPDEL_SCR, PML.HEAP_STACK; lia) ltac:(intros w []) PE16 FR16) as (PE18 & FR18 & AG18 & WSI18).
    assert (R18sp : getr R18 2%bv = Z_to_bv 64 (sp - 1376)) by (rewrite (RP18 2%bv ltac:(kin)); exact R17sp).
    apply (tail1 fx18 R18 M18 model18 crk gk reps rdst' Hfp18 R18sp).
    + rewrite (RP18 8%bv ltac:(kin)), (KS17 8%bv ltac:(kin)). exact R16s0.
    + exact (KSc _ _ _ (KSP _ _ RP18) (KSc _ _ _ KS17 KS16')).
    + exact PE18. + exact BLs. + exact FR18. + exact (L5C.model_but_vm_trans _ _ _ BV14' BV18). + exact MOK18. + exact HH18.
    + apply (TK2.ls_ok_x _ M16 M18 AG18); [st_cov | exact LS16].
    + exact Gk.
    + apply (TKX.lits_ok_x _ M16 M18 AG18); [lit_cov | exact LIT16].
    + exact CR10.
    + apply (TK2.u64_x _ M16 M18 AG18); [lia | cov_stack | exact LOC16].
    + apply (TK2.iosb_at_x _ M16 M18 AG18); [lia | cov_stack | exact IOSB16].
Qed.
End Run.
End H.
End HNXT.
