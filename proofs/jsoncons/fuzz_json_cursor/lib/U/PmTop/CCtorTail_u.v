(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u PmCurSpecs_u PmLibSanity_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u TopSpecs2_u ReadKit_u ChunkKit_u CCtorStretch_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CCTL.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition box (X : Prop) : Prop := X.

Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z X. apply andb_prop in X as [X Y3]. apply andb_prop in X as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. apply Z.eqb_eq in Y3. split; [lia | exact Y3]. Qed.

Lemma u64_of_defined : forall (M : mem) a, L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS M a v.
Proof.
  intros M a Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn RSEGS M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl | lia].
Qed.
Lemma samem_tr : forall (K1 K2 : Z -> Prop) (M1 M2 M3 : mem), TK.samem K1 M1 M2 -> TK.samem K2 M2 M3 -> TK.samem (fun a => K1 a /\ K2 a) M1 M3.
Proof. intros K1 K2 M1 M2 M3 A B a Ha [X Y]. rewrite (B a Ha Y). exact (A a Ha X). Qed.
Lemma regJ_idem : forall g, PML.regJ (PML.regJ g) = PML.regJ g. Proof. intros []; reflexivity. Qed.
Lemma regJ_ne : forall g, PML.regJ g <> PML.LS0. Proof. intros []; discriminate. Qed.
Lemma not_outside : forall F a, ~ L5.outside F a -> exists w, In w F /\ L5.in_rng w a.
Proof.
  induction F as [|w F IH]; intros a H; [exfalso; apply H; intros w []|].
  destruct (classic (L5.in_rng w a)) as [Y|N]; [exists w; split; [left; reflexivity | exact Y]|].
  destruct (IH a) as (w' & Hw' & Hi'); [intros X; apply H; intros w0 [<-|Hw0]; [exact N | exact (X w0 Hw0)] | exists w'; split; [right; exact Hw' | exact Hi']].
Qed.

Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> CCS.same_s05 R0 R' -> getr R' 22%bv = getr R0 22%bv -> TK.keepsR CCS.KO7 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18 & Q19 & Q20 & Q21) Q22 HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) CCS.KO7 -> getr R' q = getr R0 q) by (apply HK). unfold CCS.KO7 in HK'. cbn [In] in HK'.
  repeat (destruct Hq as [Hq|Hq]; [first [apply HK'; tauto | rewrite (QQ _ Hq); assumption]|]). destruct Hq.
Qed.

Lemma ko7_of_ko8 : forall R R' : bvmap 5 word, TK.keepsR CCS.KO8 R R' -> getr R' 23%bv = getr R 23%bv -> TK.keepsR CCS.KO7 R R'.
Proof.
  intros R R' HK H23 q Hq. unfold CCS.KO7 in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) CCS.KO8 -> getr R' q = getr R q) by (apply HK). unfold CCS.KO8 in HK'. cbn [In] in HK'.
  repeat (destruct Hq as [Hq|Hq]; [first [apply HK'; tauto | rewrite (QQ _ Hq); assumption]|]). destruct Hq.
Qed.
Definition CS15 : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma ko_rp : forall qs R R', regs_preserved R R' -> forallb (fun q => existsb (Nat.eqb q) CS15) qs = true -> TK.keepsR qs R R'.
Proof.
  intros qs R R' RP Hqs. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. rewrite forallb_forall in Hqs. specialize (Hqs _ Hq). apply existsb_exists in Hqs as (x & Hx & E).
  apply Nat.eqb_eq in E. subst x. unfold callee_saved_idx, CS15 in *. cbn [In] in *. intuition (subst; cbn; tauto).
Qed.
Lemma sub_ko7 : forall qs R R', TK.keepsR qs R R' -> forallb (fun q => existsb (Nat.eqb q) qs) CCS.KO7 = true -> TK.keepsR CCS.KO7 R R'.
Proof. intros qs R R' H Hq. apply (CK.keepsR_sub _ _ _ _ H). intros q Hin. rewrite forallb_forall in Hq. specialize (Hq _ Hin). apply existsb_exists in Hq as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx. Qed.

Lemma ev_at_x : forall (K : Z -> Prop) (M M' : mem) V e, TK.samem K M M' -> 0 <= V < 2 ^ 60 -> TK2.cov K (V + 8) 40 -> PMCUR.ev_at RSEGS M V e -> PMCUR.ev_at RSEGS M' V e.
Proof.
  intros K M M' V e AG HV HK H. unfold PMCUR.ev_at in *. destruct H as (D & H).
  split; [apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact D]|].
  assert (X64 : forall off v, 8 <= off -> off + 8 <= 48 -> L5.u64_at RSEGS M (V + off) v -> L5.u64_at RSEGS M' (V + off) v).
  { intros off v H1 H2 Hv. apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact Hv]. }
  assert (X8 : forall off v, 8 <= off < 48 -> L5.u8_at RSEGS M (V + off) v -> L5.u8_at RSEGS M' (V + off) v).
  { intros off v H1 Hv. apply (TK.u8_samem K M M' _ _ AG); [lia | apply HK; lia | exact Hv]. }
  destruct e; simpl in H |- *;
    repeat match goal with X : _ /\ _ |- _ => destruct X end;
    repeat (match goal with |- _ /\ _ => split end);
    first [apply X64; [lia | lia | assumption] | apply X8; [lia | assumption]].
Qed.
Lemma evc_x : forall (K : Z -> Prop) (M M' : mem) V lv0 LBo ps', TK.samem K M M' -> mem_grows M M' -> 0 <= V < 2 ^ 60 -> TK2.cov K (V + 8) 40 ->
  PMCS.evc M V lv0 LBo ps' -> PMCS.evc M' V lv0 LBo ps'.
Proof.
  intros K M M' V lv0 LBo ps' AG MG HV HK (w0 & Hw & e & He & Hr). exists w0. split.
  - destruct w0 as [[p0 e0]|]; [|exact I]. destruct Hw as (b & Hb & H1 & H2 & Hd). exists b. split; [exact Hb|]. split; [exact H1|]. split; [exact H2|]. exact (L5.defined_grows _ _ _ _ MG Hd).
  - exists e. split; [exact (ev_at_x K M M' V e AG HV HK He) | exact Hr].
Qed.
Lemma win_ok_x : forall (M M' : mem) LBo ps, mem_grows M M' -> PML.win_ok M LBo ps -> PML.win_ok M' LBo ps.
Proof.
  intros M M' LBo ps MG H. unfold PML.win_ok in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact I].
  destruct H as (c & H1 & H2 & H3 & H4). exists c. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exact (L5.defined_grows _ _ _ _ MG H4).
Qed.
Lemma ps_cov_low : forall L (K : Z -> Prop) ps, (forall b, In b (PML.ps_blocks ps) -> block_range L (fst b) (snd b)) -> hl_sptop L <= 2 ^ 47 ->
  (forall a, 0 <= a < hl_ceil L -> (a < hl_img_lo L \/ hl_img_hi L <= a) -> K a) -> TK2.ps_cov K ps.
Proof.
  intros L K ps HB Hc HK. pose proof (HB (PML.ps_bptr ps, PML.ps_bcap ps) (or_introl eq_refl)) as (B0 & B1 & B2 & B3 & B4).
  pose proof (HB (PML.ps_sb ps, PML.ps_scap ps) (or_intror (or_introl eq_refl))) as (C0 & C1 & C2 & C3 & C4). cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. split; [intros i Hi; apply HK; lia|]. split; [lia|]. split; [lia|]. intros i Hi; apply HK; lia.
Qed.
Lemma str_cov_low : forall L (K : Z -> Prop) o r, (forall b, In b (PML.srep_blocks r) -> block_range L (fst b) (snd b)) -> hl_sptop L <= 2 ^ 47 ->
  (forall a, 0 <= a < hl_ceil L -> (a < hl_img_lo L \/ hl_img_hi L <= a) -> K a) -> TK2.cov K o 24 -> TK2.str_cov K o r.
Proof.
  intros L K o r HB Hc HK Ho. split; [exact Ho|]. destruct r as [s|cap p s]; [exact I|].
  pose proof (HB (p, cap) (or_introl eq_refl)) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in *. split; [lia|]. split; [lia|]. intros i Hi; apply HK; lia.
Qed.

Lemma cursor_at_x : forall (K : Z -> Prop) (M M' : mem) C IS ch bof dn ps, TK.samem K M M' -> 0 <= C < 2 ^ 59 -> TK2.cov K C 656 -> TK2.ps_cov K ps -> mem_grows M M' ->
  PMCS.cursor_at M C IS ch bof dn ps -> PMCS.cursor_at M' C IS ch bof dn ps.
Proof.
  intros K M M' C IS ch bof dn ps AG HC HK HP MG ((S240 & S248 & S264 & S272 & (de & S280 & Hde) & S288 & S296 & (st0 & IOSB) & S32) & PA & VA & DN & DEF).
  split; [|split; [|split; [|split]]].
  - split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S240]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S248]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S264]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S272]|].
    split; [exists de; split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S280] | exact Hde]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S288]|].
    split; [apply (TK2.u8_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S296]|].
    split; [exists st0; apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact IOSB]|].
    apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S32].
  - apply (TK2.parser_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact HP | exact PA].
  - apply (TK2.vis_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact VA].
  - apply (TK2.u8_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact DN].
  - exact (L5.defined_grows _ _ _ _ MG DEF).
Qed.

Lemma cursor_at_dn : forall (K : Z -> Prop) (M M' : mem) C IS ch bof dn dn' ps, TK.samem K M M' -> 0 <= C < 2 ^ 59 -> TK2.cov K C 640 -> TK2.ps_cov K ps -> mem_grows M M' ->
  PML.u8 M' (C + 640) (PML.b2z dn') -> PMCS.cursor_at M C IS ch bof dn ps -> PMCS.cursor_at M' C IS ch bof dn' ps.
Proof.
  intros K M M' C IS ch bof dn dn' ps AG HC HK HP MG DN' ((S240 & S248 & S264 & S272 & (de & S280 & Hde) & S288 & S296 & (st0 & IOSB) & S32) & PA & VA & DN & DEF).
  split; [|split; [|split; [|split]]].
  - split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S240]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S248]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S264]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S272]|].
    split; [exists de; split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S280] | exact Hde]|].
    split; [apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S288]|].
    split; [apply (TK2.u8_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S296]|].
    split; [exists st0; apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact IOSB]|].
    apply (TK2.u64_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact S32].
  - apply (TK2.parser_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact HP | exact PA].
  - apply (TK2.vis_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact VA].
  - exact DN'.
  - exact (L5.defined_grows _ _ _ _ MG DEF).
Qed.
Lemma FR_weaken : forall L LB0 sp0 SCR (foot foot' : Z -> Prop) (M0 M : mem), TK2.FR L LB0 sp0 SCR foot M0 M -> (forall a, foot a -> foot' a) -> TK2.FR L LB0 sp0 SCR foot' M0 M.
Proof. intros L LB0 sp0 SCR foot foot' M0 M [F1 F2] H. split; [intros a Ha HC Hf HE; apply F1; [exact Ha | exact HC | intros X; exact (Hf (H a X)) | exact HE] | exact F2]. Qed.

Definition foot6 (C IS E a : Z) : Prop :=
  C <= a < C + 656 \/ IS <= a < IS + 272 \/ E <= a < E + 16 \/ 0xd4df8 <= a < 0xd4dfa \/ 0xf6848 <= a < 0xf6a68 \/ 0xd5030 <= a < 0xd5032.
Lemma foot6_out : forall C IS E a, L5.outside [(C, PMCS.CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544); (0xd5030, 2)] a -> ~ foot6 C IS E a.
Proof.
  intros C IS E a HO X. unfold foot6 in X. unfold PMCS.CURSOR_SIZE in HO.
  destruct X as [X|[X|[X|[X|[X|X]]]]]; [apply (HO (C, 656)) | apply (HO (IS, 272)) | apply (HO (E, 16)) | apply (HO (0xd4df8, 2)) | apply (HO (0xf6848, 544)) | apply (HO (0xd5030, 2))];
    try (cbn [In]; tauto); unfold L5.in_rng; cbn [fst snd]; lia.
Qed.
Lemma foot6_in : forall C IS E a, foot6 C IS E a -> ~ L5.outside [(C, PMCS.CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544); (0xd5030, 2)] a.
Proof.
  intros C IS E a X HO. unfold foot6 in X. unfold PMCS.CURSOR_SIZE in HO.
  destruct X as [X|[X|[X|[X|[X|X]]]]]; [apply (HO (C, 656)) | apply (HO (IS, 272)) | apply (HO (E, 16)) | apply (HO (0xd4df8, 2)) | apply (HO (0xf6848, 544)) | apply (HO (0xd5030, 2))];
    try (cbn [In]; tauto); unfold L5.in_rng; cbn [fst snd]; lia.
Qed.

Section T.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Variable STRTOD_SCR : Z.
Hypothesis RNEXT : PMCS.read_next_spec L HI STRTOD_SCR.
Hypothesis SETEC2 : PMCS.set_ec2_spec L.

Variables (LB : list (Z * Z)) (cr : credit) (C IS E sp r kx bx : Z) (rep : PML.srep) (g : PML.ls_state).
Variables (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : ShapeAlg.TSet).
Variables (ch b p : Z) (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model).
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
  PML.fp_ok fx' ->
  (exists (ch : Z) (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (bof' dn' : bool),
     PMCS.cursor_at M' C IS ch bof' dn' ps' /\ PML.isrc_at M' IS rep gp' rdst' /\ PMCS.rn_bound ps' IS rep gp' (Z.of_nat (length (PML.srep_chars rep))) /\ PML.ec_at M' E code /\
     PML.ls_ok g' M' /\ (g' = g \/ g' = PML.regJ g) /\ PMCUR.wf_c ps' /\ PML.win_ok M' ((ch, 16384) :: LB) ps' /\ PML.u8 M' 0xd5030 1 /\
     LB' = PML.ps_blocks ps' ++ (ch, 16384) :: LB /\ LBk = LB /\ PML.pcredit_x L cr' ps' kx bx /\
     W = [(C, PMCS.CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544); (0xd5030, 2)] /\
     (code = 0 -> dn' = false -> PML.ps_more ps' = false /\
        ((PML.ps_done ps' = true /\ PML.ps_st ps' = PML.ST_DONE) \/ (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ PMCS.evc M' (C + 592) 0 ((ch, 16384) :: LB) ps')))) ->
  regs_preserved R0 R' -> L5C.hpres L LBk sp (PMCS.CCTOR_SCR STRTOD_SCR) W M0 M' -> model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Hypothesis Hmo : PML.model_ok model.
Hypothesis BV0 : model_but_vm model0 model.
Hypothesis HK0 : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis H2 : getr R 2%bv = Z_to_bv 64 (sp - 400).
Hypothesis H1 : getr R 1%bv = Z_to_bv 64 CCT.R_RN.
Hypothesis H4 : getr R 4%bv = Z_to_bv 64 PML.TP.
Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 C.
Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 (C + 592).
Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 (sp - 384).
Hypothesis H8 : getr R 8%bv = Z_to_bv 64 E.
Hypothesis H9 : getr R 9%bv = Z_to_bv 64 C.
Hypothesis KOR : TK.keepsR CCS.KO7 R0 R.
Hypothesis H2R0 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis HH : hi_heap HI (PML.ps_blocks (PMS.ps_init b p) ++ (ch, 16384) :: LB) (debit L (debit L (debit L cr 16384) 264) 66) M (m_vmmaps model).
Hypothesis CUR : PMCS.cursor_at M C IS ch true false (PMS.ps_init b p).
Hypothesis ISRC : PML.isrc_at M IS rep (PML.srep_data (IS + 80) rep) 0.
Hypothesis ECL : PML.ec_at M (sp - 384) 0.
Hypothesis CHF : forall b0, In b0 (PML.srep_blocks rep) -> In b0 ((ch, 16384) :: LB) /\ fst b0 <> ch.
Hypothesis NLEN : Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26.
Hypothesis LSg : PML.ls_ok g M.
Hypothesis HG : g <> PML.LS0.
Hypothesis PC : PML.pcredit_x L (debit L (debit L (debit L cr 16384) 264) 66) (PMS.ps_init b p) kx bx.
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 sp (PMCS.CCTOR_SCR STRTOD_SCR).
Hypothesis Hrok : L5.ra_ok r.
Hypothesis OC : PML.obj_on_stack L sp C 656.
Hypothesis OI : PML.obj_on_stack L sp IS 272.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis APCI : box (C + 656 <= IS \/ IS + 272 <= C).
Hypothesis APCE : box (C + 656 <= E \/ E + 16 <= C).
Hypothesis APIE : box (IS + 272 <= E \/ E + 16 <= IS).
Hypothesis WF : CCS.cells64 M (CCS.wframe sp r R0).
Hypothesis CF : CCS.cells64 M (CCS.cframe sp C IS E (bv_unsigned (getr R0 22%bv))).
Hypothesis O16 : L5.u64_at RSEGS M (sp - 288) PML.VT_FUNC.
Hypothesis O48 : L5.u64_at RSEGS M (sp - 256) (sp - 288).
Hypothesis OZ : CCS.zeros M (sp - 224) 144.
Hypothesis RO : PML.img_ro M.
Hypothesis SG : PML.u8 M 0xd5030 1.
Hypothesis EC0 : PML.ec_at M E 0.
Hypothesis FR : TK2.FR L LB sp (PMCS.CCTOR_SCR STRTOD_SCR) (fun a => C <= a < C + 656 \/ 0xd5030 <= a < 0xd5032) M0 M.
Hypothesis DW : forall a, 0 <= a < 2 ^ 64 -> ~ L5.outside [(C, 656); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544); (0xd5030, 2)] a ->
  M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None.
Hypothesis BOK : TK2.blocks_ok L LB.

Lemma tail_ok : srealizes RSEGS SCFG (@PML.cfg fx R PMCS.PC_READ_NEXT_C M model) K.
Proof.
  pose proof STK0 as (S1 & S2 & S3 & S4 & S5).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as ERR.
  set (SCR := PMCS.CCTOR_SCR STRTOD_SCR) in *.
  assert (HSCR : SCR = 400 + PMCS.RN_SCR STRTOD_SCR /\ 9520 <= PMCS.RN_SCR STRTOD_SCR).
  { unfold SCR, PMCS.CCTOR_SCR, PMCS.CCTOR_MAIN_SCR, PMCS.RN_SCR, PMS.READNEXT_SCR, PMS.PSOME_SCR, PMS.PF_SCR, PMS.CTOR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK. lia. }
  destruct HSCR as (HSCR & HRN2).
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  pose proof OC as (OC1 & OC2 & OC3). pose proof OI as (OI1 & OI2 & OI3). pose proof OE as (OE1 & OE2 & OE3).
  destruct Hmo as (Hh & Hl & Hmat).
  assert (STKrn : L5C.stk (hl_sptop L) M (sp - 400) (PMCS.RN_SCR STRTOD_SCR)).
  { split; [apply CK.al16; [exact S1 | reflexivity]|]. split; [lia|]. split; [lia|]. split; [exact S4|]. intros i Hi. apply (proj2 FR). lia. }
  assert (Hs6 : 0 <= bv_unsigned (getr R0 22%bv) < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (getr R0 22%bv)) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
  assert (ECK : forall i, E <= i < E + 16 -> ~ (C <= i < C + 656) /\ ~ (IS <= i < IS + 272)) by (unfold box in APCE, APIE; intros i Hi; lia).
  assert (ISK : forall i, IS <= i < IS + 272 -> ~ (C <= i < C + 656) /\ ~ (E <= i < E + 16)) by (unfold box in APCI, APIE; intros i Hi; lia).
  assert (CEK : forall i, C <= i < C + 656 -> ~ (E <= i < E + 16)) by (unfold box in APCE; intros i Hi; lia).

  apply (RNEXT ((ch, 16384) :: LB) (debit L (debit L (debit L cr 16384) 264) 66) (sp - 400) CCT.R_RN C IS (sp - 384) ch (PML.srep_data (IS + 80) rep) 0
           (Z.of_nat (length (PML.srep_chars rep))) kx bx rep g true (PMS.ps_init b p) fx R M model K HH (conj Hh (conj Hl Hmat)) HK0 Hfp).
  { split; [exact (CK.mk_entry L R M (sp - 400) _ _ H1 (ra_ok_lit CCT.R_RN eq_refl) H2 H4 STKrn)|].
    split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|]. split; [exact CUR|].
    split; [split; [exact (wf_ps_init b p) | unfold PMCUR.lvl_ok, PMS.ps_init; cbn [PML.ps_more PML.ps_st PML.ps_stack PML.ps_level PMCUR.ps_set_more];
                                             intros _ [X|(x & X & Y)]; [unfold PMCUR.ICS in X; cbn [In] in X; unfold PML.ST_START, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in X; lia
                                                                           | destruct X as [<-|[]]; unfold PMCUR.ICS in Y; cbn [In] in Y; unfold PML.ST_ROOT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Y; lia]]|].
    split; [unfold PML.win_ok, PMS.ps_init; cbn [PML.ps_win]; exact I|].
    split; [exact ISRC|].
    split; [unfold PMCS.rn_bound, PMCS.undelivered; change (PML.winlen (PMCUR.ps_set_more (PMS.ps_init b p) true)) with 0;
            change (PML.buf_need (PMCUR.ps_set_more (PMS.ps_init b p) true)) with 0; change (PML.ps_buf (PMCUR.ps_set_more (PMS.ps_init b p) true)) with (@nil Z); cbn [length Z.of_nat]; lia|].
    split; [exact ECL|]. split; [left; reflexivity|]. split; [exact CHF|]. split; [exact NLEN|]. split; [exact LSg|]. split; [exact HG|]. split; [exact PC|].
    unfold PMCS.CURSOR_SIZE, PML.obj_on_stack, PML.apart.
    split; [split; [lia | split; [lia | exact OC3]]|]. split; [split; [lia | split; [lia | exact OI3]]|].
    split; [split; [lia | split; [lia | clear - S1; apply Z.mod_divide; [lia|]; apply Z.mod_divide in S1; [|lia]; destruct S1 as (q & ->); exists (2 * q - 48); lia]]|].
    unfold box in APCI. split; [exact APCI|]. split; [lia | lia]. }
  intros fx1 R1 M1 model1 LB1 cr1 LBk1 W1 Hfp1 (ps' & code & gp' & rdst' & g' & bof' & dn' & CUR1 & ISRC1 & RNB1 & EC1 & LS1 & HG1 & WF1 & WIN1 & -> & -> & PC1 & -> & RNR1) RP1 HP1 BV1 HH1.
  cbn [lb_remove fst] in HP1. rewrite Z.eqb_refl in HP1.
  assert (Hh1 : m_halted model1 = None) by (rewrite (L5C.halted_but_vm _ _ BV1); exact Hh).
  assert (Hl1 : m_vm_lazy model1 = []) by (rewrite (L5C.lazy_but_vm _ _ BV1); exact Hl).
  pose proof (TK2.hpres_samem L LAY _ _ _ _ M M1 HP1 BOK STKrn ltac:(lia)) as AG1.
  assert (KH1 : forall a, sp - 368 <= a < hl_sptop L -> ~ (C <= a < C + 656) -> ~ (IS <= a < IS + 272) ->
            TK2.keepH L LB [(C, PMCS.CURSOR_SIZE); (IS, 272); (sp - 384, 16); (0xd4df8, 2); (0xf6848, 544)] (sp - 400) (PMCS.RN_SCR STRTOD_SCR) a).
  { intros a Ha X1 X2. split; [|left; lia]. intros w Hw Hin. unfold L5.in_rng in Hin. unfold PMCS.CURSOR_SIZE in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hin; lia. }
  assert (KS1 : forall a, 0x10000 <= a < 0xf8000 -> ~ (0xd4df8 <= a < 0xd4dfa) -> ~ (0xf6848 <= a < 0xf6a68) -> ~ (0xf6c08 <= a < 0xf6fb0) -> ~ (0xd675c <= a < 0xd6760) ->
            TK2.keepH L LB [(C, PMCS.CURSOR_SIZE); (IS, 272); (sp - 384, 16); (0xd4df8, 2); (0xf6848, 544)] (sp - 400) (PMCS.RN_SCR STRTOD_SCR) a).
  { intros a Ha X1 X2 X3 X4. split; [|right; right; right; lia]. intros w Hw Hin. unfold L5.in_rng in Hin. unfold PMCS.CURSOR_SIZE in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hin; lia. }
  assert (WF1' : CCS.cells64 M1 (CCS.wframe sp r R0)).
  { apply (CCS.cells64_x _ M M1 _ AG1); [|exact WF]. intros av Hin. unfold CCS.wframe in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst]; split; [lia | intros i Hi; apply KH1; lia]|]). destruct Hin. }
  assert (CF1' : CCS.cells64 M1 (CCS.cframe sp C IS E (bv_unsigned (getr R0 22%bv)))).
  { apply (CCS.cells64_x _ M M1 _ AG1); [|exact CF]. intros av Hin. unfold CCS.cframe in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst]; split; [lia | intros i Hi; apply KH1; lia]|]). destruct Hin. }
  assert (O16_1 : L5.u64_at RSEGS M1 (sp - 288) PML.VT_FUNC) by (apply (TK2.u64_x _ M M1 AG1); [lia | intros i Hi; apply KH1; lia | exact O16]).
  assert (O48_1 : L5.u64_at RSEGS M1 (sp - 256) (sp - 288)) by (apply (TK2.u64_x _ M M1 AG1); [lia | intros i Hi; apply KH1; lia | exact O48]).
  assert (OZ1 : CCS.zeros M1 (sp - 224) 144) by (apply (CCS.zeros_samem _ M M1 _ _ AG1); [lia | lia | intros i Hi; apply KH1; lia | exact OZ]).
  assert (D400_1 : L5.defined M1 (sp - 400) 400).
  { intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - 400 + i) HP1); [lia | right; left; split; [lia | lia] | unfold in_errno; rewrite ERR; lia | apply (proj2 FR); lia]. }
  assert (EC_1 : PML.ec_at M1 E 0) by (apply (TK2.ec_at_x _ M M1 AG1); [lia | intros i Hi; destruct (ECK i Hi); apply KH1; [lia | assumption | assumption] | exact EC0]).
  assert (SG1 : PML.u8 M1 0xd5030 1) by (apply (TK2.u8_x _ M M1 AG1); [lia | intros i Hi; apply KS1; lia | exact SG]).
  destruct EC1 as (EC1a & EC1d & EC1c).
  assert (Hcode : 0 <= code < 2 ^ 31) by (destruct EC1c as [X|(X & _)]; lia).

  assert (HB1 : forall b0, In b0 (PML.ps_blocks ps' ++ (ch, 16384) :: LB) -> block_range L (fst b0) (snd b0)) by (exact (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH1)).
  assert (PSC : forall K0 : Z -> Prop, (forall a, 0 <= a < hl_ceil L -> (a < hl_img_lo L \/ hl_img_hi L <= a) -> K0 a) -> TK2.ps_cov K0 ps').
  { intros K0 HK'. apply (ps_cov_low L); [intros b0 Hb0; apply HB1; apply in_or_app; left; exact Hb0 | lia | exact HK']. }
  assert (STC : forall K0 : Z -> Prop, (forall a, 0 <= a < hl_ceil L -> (a < hl_img_lo L \/ hl_img_hi L <= a) -> K0 a) -> TK2.cov K0 (IS + 80) 24 -> TK2.str_cov K0 (IS + 80) rep).
  { intros K0 HK' Ho. apply (str_cov_low L); [intros b0 Hb0; apply HB1; apply in_or_app; right; exact (proj1 (CHF b0 Hb0)) | lia | exact HK' | exact Ho]. }
  assert (CL1 : forall a, foot6 C IS E a -> client_addr L LB (sp - 400) (PMCS.RN_SCR STRTOD_SCR) a).
  { intros a X. unfold foot6 in X. unfold client_addr. rewrite ILO, IHI.
    destruct X as [X|[X|[X|X]]]; [right; left; lia | right; left; lia | right; left; lia | right; right; split; [lia | intros Z0; apply (PmLayout.ly_static L LAY) in Z0; lia]]. }
  assert (FR1 : TK2.FR L LB sp SCR (foot6 C IS E) M0 M1).
  { apply (TK2.FR_hpres L LAY LB sp SCR (foot6 C IS E) M0 M M1 LB (sp - 400) (PMCS.RN_SCR STRTOD_SCR) _ (FR_weaken L LB sp SCR _ (foot6 C IS E) M0 M FR ltac:(intros a X; cbv beta in X; unfold foot6; lia)) HP1 BOK (incl_refl _));
      [lia | lia | lia | lia | lia | lia |].
    intros w a Hw Hin. unfold L5.in_rng in Hin. unfold PMCS.CURSOR_SIZE in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hin; [right; unfold foot6; lia | right; unfold foot6; lia | left; lia | right; unfold foot6; lia | right; unfold foot6; lia]. }
  assert (FR2of : forall M2 : mem, TK.samem (CCS.KE8 sp) M1 M2 -> mem_grows M1 M2 -> TK2.FR L LB sp SCR (foot6 C IS E) M0 M2).
  { intros M2 AG2 MG2. apply (TK2.FR_grows L LAY LB sp SCR _ M0 M1 M2 _ FR1 AG2 MG2 BOK ltac:(lia) ltac:(lia)). intros a Ha. left. unfold CCS.KE8 in Ha. lia. }
  assert (HH2of : forall M2 : mem, TK.samem (CCS.KE8 sp) M1 M2 -> mem_grows M1 M2 -> hi_heap HI (PML.ps_blocks ps' ++ (ch, 16384) :: LB) cr1 M2 (m_vmmaps model1)).
  { intros M2 AG2 MG2. apply (TK2.heap_stack_write L HI HIok LAY _ _ M1 M2 _ (sp - 320) sp HH1 ltac:(lia) ltac:(lia) ltac:(lia)); [|exact MG2].
    apply (TK.samem_weaken _ _ _ _ AG2). intros a Ha. unfold CCS.KE8. lia. }
  assert (FIN : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) code' g'' dn'',
    PML.fp_ok fx' -> regs_preserved R0 R' -> TK2.FR L LB sp SCR (foot6 C IS E) M0 M' -> mem_grows M1 M' -> hi_heap HI (PML.ps_blocks ps' ++ (ch, 16384) :: LB) cr1 M' (m_vmmaps model1) ->
    PMCS.cursor_at M' C IS ch bof' dn'' ps' -> PML.isrc_at M' IS rep gp' rdst' -> PML.ec_at M' E code' -> PML.ls_ok g'' M' -> (g'' = g \/ g'' = PML.regJ g) -> PML.u8 M' 0xd5030 1 ->
    (code' = 0 -> dn'' = false -> PML.ps_more ps' = false /\
        ((PML.ps_done ps' = true /\ PML.ps_st ps' = PML.ST_DONE) \/ (PMCUR.wf_c (PMCUR.ps_set_more ps' true) /\ PMCS.evc M' (C + 592) 0 ((ch, 16384) :: LB) ps'))) ->
    srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model1) K).
  { intros fx' R' M' code' g'' dn'' Hfp' RP' FR' MG' HH' CUR' ISRC' EC' LS' HG'' SG' EVT.
    apply (Hcont fx' R' M' model1 (PML.ps_blocks ps' ++ (ch, 16384) :: LB) cr1 LB [(C, PMCS.CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544); (0xd5030, 2)] Hfp').
    - exists ch, ps', code', gp', rdst', g'', bof', dn''.
      split; [exact CUR'|]. split; [exact ISRC'|]. split; [exact RNB1|]. split; [exact EC'|]. split; [exact LS'|]. split; [exact HG''|].
      split; [exact WF1|]. split; [exact (win_ok_x M1 M' _ _ MG' WIN1)|]. split; [exact SG'|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact PC1|]. split; [reflexivity | exact EVT].
    - exact RP'.
    - apply L5C.hpres_intro.
      + intros a (Ha & HC & HE & HO). exact (proj1 FR' a Ha HC (foot6_out C IS E a HO) HE).
      + intros i Hi. apply (proj2 FR'). lia.
      + intros a Ha HC HE Hd. destruct (classic (foot6 C IS E a)) as [Y|N]; [|rewrite (proj1 FR' a Ha HC N HE); exact Hd].
        apply MG'. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP1 Ha); [apply CL1; exact Y | unfold in_errno; rewrite ERR; unfold foot6 in Y; lia | exact (DW a Ha (foot6_in C IS E a Y) Hd)].
    - exact (L5C.model_but_vm_trans _ _ _ BV0 BV1).
    - exact HH'. }

  apply (CCS.s_r_rn FPM fx1 R1 M1 model1 K sp r R0 C IS E (bv_unsigned (getr R0 22%bv)) code Hh1 Hl1 Hfp1
           ltac:(rewrite (RP1 2%bv ltac:(ck_in)); exact H2) SPOK Hrok ltac:(lia) ltac:(lia) ltac:(lia) Hs6 Hcode EC1a WF1' CF1' O16_1 O48_1 OZ1 (proj1 LS1) D400_1).
  -
    intros Hc0 fx2 R2 M2 Hfp2 H2r SS2 S6r KO2 AG2 MG2.
    assert (K8 : forall a, ~ (sp - 400 <= a < sp) -> CCS.KE8 sp a) by (intros a Ha; unfold CCS.KE8; lia).
    apply (FIN fx2 R2 M2 0 g' dn' Hfp2).
    + apply rp_final; [rewrite H2r, H2R0; reflexivity | exact SS2 | rewrite S6r, Z_to_bv_bv_unsigned; reflexivity |].
      exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KOR (ko_rp CCS.KO7 _ _ RP1 eq_refl)) KO2).
    + exact (FR2of M2 AG2 MG2).
    + exact MG2.
    + exact (HH2of M2 AG2 MG2).
    + exact (cursor_at_x (CCS.KE8 sp) M1 M2 C IS ch bof' dn' ps' AG2 ltac:(lia) ltac:(intros i Hi; apply K8; lia) (PSC (CCS.KE8 sp) ltac:(intros a Ha Hb; apply K8; lia)) MG2 CUR1).
    + apply (TK2.isrc_at_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | apply STC; [intros a Ha Hb; apply K8; lia | intros i Hi; apply K8; lia] | exact ISRC1].
    + apply (TK2.ec_at_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | exact EC_1].
    + apply (TK2.ls_ok_x _ M1 M2 AG2); [apply TK2.statics_cov_lo; intros a Ha; apply K8; lia | exact LS1].
    + destruct HG1 as [X|(X & _)]; [left | right]; exact X.
    + apply (TK2.u8_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | exact SG1].
    + intros _ Hdn. destruct RNR1 as (_ & RN2). destruct (RN2 Hc0 Hdn) as (Hmore & [Hdone | (Hwf & Hevc)]); (split; [exact Hmore|]); [left; exact Hdone | right; split; [exact Hwf|]].
      change (PML.ps_level (PMS.ps_init b p)) with 0 in Hevc.
      apply (evc_x (CCS.KE8 sp) M1 M2 _ _ _ _ AG2 MG2); [lia | intros i Hi; apply K8; lia | exact Hevc].
  -
    intros Hc0 fx2 R2 M2 Hfp2 H2r H1r H10r H11r KS2 AG2 MG2 C312 C320.
    assert (K8 : forall a, ~ (sp - 320 <= a < sp - 296) -> ~ (sp - 240 <= a < sp - 232) -> CCS.KE8 sp a) by (intros a X1 X2; split; assumption).
    assert (Hcnz : 1 <= code <= 31) by (destruct EC1c as [X|(X & _)]; [exfalso; exact (Hc0 X) | exact X]).

    assert (WF2 : CCS.cells64 M2 (CCS.wframe sp r R0)).
    { apply (CCS.cells64_x _ M1 M2 _ AG2); [|exact WF1']. intros av Hin. unfold CCS.wframe in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst]; split; [lia | intros i Hi; apply K8; lia]|]). destruct Hin. }
    assert (CF2 : CCS.cells64 M2 (CCS.cframe sp C IS E (bv_unsigned (getr R0 22%bv)))).
    { pose proof CF1' as CFx. unfold CCS.cframe in CFx |- *. cbn [CCS.cells64] in CFx |- *. destruct CFx as (_ & _ & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      split; [exact C312|]. split; [exact C320|].
      repeat (split; [apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | assumption]|]). exact I. }
    assert (O16_2 : L5.u64_at RSEGS M2 (sp - 288) PML.VT_FUNC) by (apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | exact O16_1]).
    assert (O48_2 : L5.u64_at RSEGS M2 (sp - 256) (sp - 288)) by (apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | exact O48_1]).
    assert (OZ2 : CCS.zeros M2 (sp - 224) 144) by (apply (CCS.zeros_samem _ M1 M2 _ _ AG2); [lia | lia | intros i Hi; apply K8; lia | exact OZ1]).

    destruct (u64_of_defined M1 (sp - 384) ltac:(eapply L5.defined_sub; [exact EC1d | lia | lia])) as (v64 & Hv64 & Lv64).
    assert (Lcat1 : L5.u64_at RSEGS M1 (sp - 376) PML.OBJ_JSON_CATEGORY).
    { destruct EC1c as [X|(_ & X)]; [exfalso; exact (Hc0 X)|]. replace (sp - 376) with (sp - 384 + 8) by lia. exact X. }
    pose proof (CCS.u64_u32_lo M1 (sp - 384) v64 code Hv64 ltac:(lia) Lv64 EC1a) as Hm.
    assert (Lv64_2 : L5.u64_at RSEGS M2 (sp - 384) v64) by (apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | exact Lv64]).
    assert (Lcat2 : L5.u64_at RSEGS M2 (sp - 376) PML.OBJ_JSON_CATEGORY) by (apply (TK2.u64_x _ M1 M2 AG2); [lia | intros i Hi; apply K8; lia | exact Lcat1]).

    assert (TP2 : getr R2 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KS2 4%bv ltac:(ck_in)), (RP1 4%bv ltac:(ck_in)); exact H4).
    assert (LS2 : PML.ls_ok g' M2) by (apply (TK2.ls_ok_x _ M1 M2 AG2); [apply TK2.statics_cov_lo; intros a Ha; apply K8; lia | exact LS1]).
    assert (HG2 : g' <> PML.LS0) by (destruct HG1 as [->|(-> & _)]; [exact HG | apply regJ_ne]).
    assert (D400_2 : L5.defined M2 (sp - 400) 400) by exact (L5.defined_grows _ _ _ _ MG2 D400_1).
    assert (STK2 : L5C.stk (hl_sptop L) M2 (sp - 400) PMS.SETEC_SCR).
    { unfold PMS.SETEC_SCR. split; [apply CK.al16; [exact S1 | reflexivity]|]. split; [lia|]. split; [lia|]. split; [exact S4|].
      intros i Hi. apply MG2. pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP1 (PMCS.RN_SCR STRTOD_SCR - 256 + i) ltac:(lia)) as X.
      replace (sp - 400 - PMCS.RN_SCR STRTOD_SCR + (PMCS.RN_SCR STRTOD_SCR - 256 + i)) with (sp - 400 - 256 + i) in X by lia. exact X. }
    apply (SETEC2 (sp - 400) 1 (sp - 400) CCT.R_SETEC2 g' fx2 R2 M2 model1 K Hh1 Hl1 HK0 Hfp2).
    { split; [exact (CK.mk_entry L R2 M2 (sp - 400) _ _ H1r (ra_ok_lit CCT.R_SETEC2 eq_refl) H2r TP2 STK2)|].
      split; [exact H10r|]. split; [exact H11r|]. split; [lia|]. split; [eapply L5.defined_sub; [exact D400_2 | lia | lia]|].
      split; [unfold PML.obj_on_stack; split; [lia | split; [lia | clear - S1; apply Z.mod_divide; [lia|]; apply Z.mod_divide in S1; [|lia]; destruct S1 as (q & ->); exists (2 * q - 50); lia]]|].
      split; [exact LS2 | exact HG2]. }
    intros fx3 R3 M3 Hfp3 (ECT & LST) RP3 FB3 MG3. pose proof (TK2.frame_but_samem _ _ _ FB3) as AG3.
    assert (K3 : forall a, sp - 384 <= a -> L5.outside [(sp - 400 - PMS.SETEC_SCR, PMS.SETEC_SCR); (sp - 400, 16); (0xd4df8, 2); (0xf6848, 544)] a).
    { intros a Ha w Hw Hin. unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; lia. }
    pose proof (samem_tr _ _ M1 M2 M3 AG2 AG3) as AG13.
    assert (K13 : forall a, (sp - 384 <= a /\ ~ (sp - 320 <= a < sp - 296) /\ ~ (sp - 240 <= a < sp - 232)) \/ (0 <= a < hl_ceil L /\ (a < 0x10000 \/ 0xf8000 <= a)) \/
                    (0x10000 <= a < 0xd4df8 \/ 0xd4dfa <= a < 0xf6848 \/ 0xf6a68 <= a < 0xf8000) ->
                    CCS.KE8 sp a /\ L5.outside [(sp - 400 - PMS.SETEC_SCR, PMS.SETEC_SCR); (sp - 400, 16); (0xd4df8, 2); (0xf6848, 544)] a).
    { intros a Ha. split; [unfold CCS.KE8; lia|]. intros w Hw Hin. unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; lia. }
    assert (WF3 : CCS.cells64 M3 (CCS.wframe sp r R0)).
    { apply (CCS.cells64_x _ M2 M3 _ AG3); [|exact WF2]. intros av Hin. unfold CCS.wframe in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst]; split; [lia | intros i Hi; apply K3; lia]|]). destruct Hin. }
    assert (CF3 : CCS.cells64 M3 (CCS.cframe sp C IS E (bv_unsigned (getr R0 22%bv)))).
    { apply (CCS.cells64_x _ M2 M3 _ AG3); [|exact CF2]. intros av Hin. unfold CCS.cframe in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst]; split; [lia | intros i Hi; apply K3; lia]|]). destruct Hin. }
    assert (O16_3 : L5.u64_at RSEGS M3 (sp - 288) PML.VT_FUNC) by (apply (TK2.u64_x _ M2 M3 AG3); [lia | intros i Hi; apply K3; lia | exact O16_2]).
    assert (O48_3 : L5.u64_at RSEGS M3 (sp - 256) (sp - 288)) by (apply (TK2.u64_x _ M2 M3 AG3); [lia | intros i Hi; apply K3; lia | exact O48_2]).
    assert (OZ3 : CCS.zeros M3 (sp - 224) 144) by (apply (CCS.zeros_samem _ M2 M3 _ _ AG3); [lia | lia | intros i Hi; apply K3; lia | exact OZ2]).
    assert (Lv64_3 : L5.u64_at RSEGS M3 (sp - 384) v64) by (apply (TK2.u64_x _ M2 M3 AG3); [lia | intros i Hi; apply K3; lia | exact Lv64_2]).
    assert (Lcat3 : L5.u64_at RSEGS M3 (sp - 376) PML.OBJ_JSON_CATEGORY) by (apply (TK2.u64_x _ M2 M3 AG3); [lia | intros i Hi; apply K3; lia | exact Lcat2]).
    destruct ECT as (ET1 & ET2 & ET3).
    destruct (u64_of_defined M3 (sp - 400) ltac:(eapply L5.defined_sub; [exact ET2 | lia | lia])) as (tv64 & Htv & Ltv).
    pose proof (CCS.u64_u32_lo M3 (sp - 400) tv64 1 Htv ltac:(lia) Ltv ET1) as Htm.
    assert (Ltcat : L5.u64_at RSEGS M3 (sp - 392) PML.OBJ_JSON_CATEGORY) by (destruct ET3 as [X|(_ & X)]; [discriminate X | replace (sp - 392) with (sp - 400 + 8) by lia; exact X]).
    pose proof CUR1 as (_ & _ & _ & DN1 & DC1).
    assert (DN3 : PML.u8 M3 (C + 640) (PML.b2z dn')) by (apply (TK2.u8_x _ M1 M3 AG13); [lia | intros i Hi; apply K13; lia | exact DN1]).
    assert (EC_3 : PML.ec_at M3 E 0) by (apply (TK2.ec_at_x _ M1 M3 AG13); [lia | intros i Hi; apply K13; lia | exact EC_1]).
    pose proof EC_3 as (E3a & E3d & _).
    destruct (u64_of_defined M3 E ltac:(eapply L5.defined_sub; [exact E3d | lia | lia])) as (e0 & He0 & E0_3).
    destruct (u64_of_defined M3 (E + 8) ltac:(eapply L5.defined_sub; [exact E3d | lia | lia])) as (e8 & He8 & E8_3).
    assert (H2_3 : getr R3 2%bv = Z_to_bv 64 (sp - 400)) by (rewrite (RP3 2%bv ltac:(ck_in)); exact H2r).
    assert (H8_3 : getr R3 8%bv = Z_to_bv 64 E) by (rewrite (RP3 8%bv ltac:(ck_in)), (KS2 8%bv ltac:(ck_in)), (RP1 8%bv ltac:(ck_in)); exact H8).
    assert (H9_3 : getr R3 9%bv = Z_to_bv 64 C) by (rewrite (RP3 9%bv ltac:(ck_in)), (KS2 9%bv ltac:(ck_in)), (RP1 9%bv ltac:(ck_in)); exact H9).
    assert (D400_3 : L5.defined M3 (sp - 400) 400) by exact (L5.defined_grows _ _ _ _ MG3 D400_2).
    assert (DC3 : L5.defined M3 C 656) by exact (L5.defined_grows _ _ _ _ MG3 (L5.defined_grows _ _ _ _ MG2 DC1)).
    assert (Hdnb : 0 <= PML.b2z dn' < 256) by (destruct dn'; cbn; lia).
    assert (FR3 : TK2.FR L LB sp SCR (foot6 C IS E) M0 M3).
    { apply (TK2.FR_grows L LAY LB sp SCR _ M0 M2 M3 _ (FR2of M2 AG2 MG2) AG3 MG3 BOK ltac:(lia) ltac:(lia)). intros a Ha. destruct (not_outside _ a Ha) as (w & Hw & Hin).
      unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [left; lia | left; lia | right; unfold foot6; lia | right; unfold foot6; lia]. }
    assert (HH3 : hi_heap HI (PML.ps_blocks ps' ++ (ch, 16384) :: LB) cr1 M3 (m_vmmaps model1)).
    { apply (TK2.heap_pure_write L HI HIok LAY _ _ M2 M3 _ _ (HH2of M2 AG2 MG2) ltac:(lia) AG3 MG3). intros a Hz Ha. destruct (not_outside _ a Ha) as (w & Hw & Hin).
      unfold L5.in_rng in Hin. unfold PMS.SETEC_SCR in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [left; lia | left; lia | right; lia | right; lia]. }
    pose proof (fun z Hz => MG3 z (MG2 z Hz)) as MG13.

    assert (FIN4 : forall (fx4 : FPState) (R4 : bvmap 5 word) (M4 : mem) code' dn'', PML.fp_ok fx4 -> getr R4 2%bv = Z_to_bv 64 sp -> CCS.same_s05 R0 R4 ->
              getr R4 22%bv = Z_to_bv 64 (bv_unsigned (getr R0 22%bv)) -> TK.keepsR CCS.KO7 R3 R4 -> TK.samem (CCS.KE9 sp C E) M3 M4 -> mem_grows M3 M4 ->
              PML.u8 M4 (C + 640) (PML.b2z dn'') -> PML.ec_at M4 E code' -> (code' <> 0 \/ dn'' = true) -> srealizes RSEGS SCFG (@PML.cfg fx4 R4 r M4 model1) K).
    { intros fx4 R4 M4 code' dn'' Hfp4 H2d SSd S6d KOd AG4 MG4 D640' EC4 NZ.
      pose proof (samem_tr _ _ M1 M3 M4 AG13 AG4) as AG14.
      assert (K14 : forall a, (sp <= a /\ ~ (C + 640 <= a < C + 641) /\ ~ (E <= a < E + 16)) \/ (0 <= a < hl_ceil L /\ (a < 0x10000 \/ 0xf8000 <= a)) \/
                      (0x10000 <= a < 0xd4df8 \/ 0xd4dfa <= a < 0xf6848 \/ 0xf6a68 <= a < 0xf8000) ->
                      (CCS.KE8 sp a /\ L5.outside [(sp - 400 - PMS.SETEC_SCR, PMS.SETEC_SCR); (sp - 400, 16); (0xd4df8, 2); (0xf6848, 544)] a) /\ CCS.KE9 sp C E a).
      { intros a Ha. split; [apply K13; lia | unfold CCS.KE9; lia]. }
      pose proof (fun z Hz => MG4 z (MG13 z Hz)) as MG14.
      apply (FIN fx4 R4 M4 code' (PML.regJ g') dn'' Hfp4).
      - apply rp_final; [rewrite H2d, H2R0; reflexivity | exact SSd | rewrite S6d, Z_to_bv_bv_unsigned; reflexivity |].
        exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KOR (ko_rp CCS.KO7 _ _ RP1 eq_refl)) (sub_ko7 _ _ _ KS2 eq_refl))
                 (ko_rp CCS.KO7 _ _ RP3 eq_refl)) KOd).
      - apply (TK2.FR_grows L LAY LB sp SCR _ M0 M3 M4 _ FR3 AG4 MG4 BOK ltac:(lia) ltac:(lia)). intros a Ha. unfold CCS.KE9 in Ha. unfold foot6. lia.
      - exact MG14.
      - apply (TK2.heap_stack_write L HI HIok LAY _ _ M3 M4 _ (sp - 400) (hl_sptop L) HH3 ltac:(lia) ltac:(lia) ltac:(lia)); [|exact MG4].
        apply (TK.samem_weaken _ _ _ _ AG4). intros a Ha. unfold CCS.KE9. lia.
      - apply (cursor_at_dn _ M1 M4 C IS ch bof' dn' dn'' ps' AG14 ltac:(lia)); [intros i Hi; apply K14; left; pose proof (CEK i ltac:(lia)); lia | apply PSC; intros a Ha Hb; apply K14; right; left; lia
                                                                          | exact MG14 | exact D640' | exact CUR1].
      - apply (TK2.isrc_at_x _ M1 M4 AG14); [lia | intros i Hi; apply K14; left; destruct (ISK i Hi) as (X1 & X2); lia
                                           | apply STC; [intros a Ha Hb; apply K14; right; left; lia | intros i Hi; apply K14; left; destruct (ISK i ltac:(lia)) as (X1 & X2); lia] | exact ISRC1].
      - exact EC4.
      - apply (TK2.ls_ok_x _ M3 M4 AG4); [apply TK2.statics_cov_lo; intros a Ha; unfold CCS.KE9; lia | exact LST].
      - destruct HG1 as [->|(-> & _)]; right; [reflexivity | apply regJ_idem].
      - apply (TK2.u8_x _ M1 M4 AG14); [lia | intros i Hi; apply K14; right; right; lia | exact SG1].
      - intros X Y. destruct NZ as [N|T]; [exfalso; exact (N X) | rewrite T in Y; discriminate Y]. }
    apply (CCS.s_r_setec2 FPM fx3 R3 M3 model1 K sp r R0 C IS E (bv_unsigned (getr R0 22%bv)) v64 PML.OBJ_JSON_CATEGORY tv64 PML.OBJ_JSON_CATEGORY code 1 (PML.b2z dn') e0 e8
             Hh1 Hl1 Hfp3 H2_3 H8_3 H9_3 SPOK Hrok ltac:(lia) ltac:(lia) OC1 OE1 ltac:(unfold box in APCE; exact APCE) ltac:(lia) Hs6 Hv64 ltac:(unfold PML.OBJ_JSON_CATEGORY; lia) Htv
             ltac:(unfold PML.OBJ_JSON_CATEGORY; lia) Hdnb He0 He8 Hm Hcode Htm ltac:(lia)
             ltac:(unfold PML.OBJ_JSON_CATEGORY; lia) ltac:(unfold PML.OBJ_JSON_CATEGORY; reflexivity) ltac:(unfold PML.OBJ_JSON_CATEGORY; lia) ltac:(unfold PML.OBJ_JSON_CATEGORY; reflexivity)
             Lv64_3 Lcat3 Ltv Ltcat DN3 E0_3 E8_3 WF3 CF3 O16_3 O48_3 OZ3 (proj1 LST) D400_3 DC3 E3d).
    +
      intros _ fx4 R4 M4 Hfp4 H2d SSd S6d KOd D640d E0d E8d AG4 MG4.
      apply (FIN4 fx4 R4 M4 0 true Hfp4 H2d SSd S6d KOd AG4 MG4 D640d); [|right; reflexivity].
      split; [|split; [exact (L5.defined_grows _ _ _ _ MG4 E3d) | left; reflexivity]].
      pose proof (CCS.u64_u32_lo M3 E e0 0 He0 ltac:(lia) E0_3 E3a) as X. pose proof (CCS.u32_of_u64 M4 E e0 He0 E0d) as Y. rewrite X in Y. exact Y.
    +
      intros _ fx4 R4 M4 Hfp4 H2d SSd S6d KOd Ev64 Ecat D640c AG4 MG4.
      apply (FIN4 fx4 R4 M4 code dn' Hfp4 H2d SSd S6d KOd AG4 MG4 D640c); [|left; exact Hc0].
      split; [pose proof (CCS.u32_of_u64 M4 E v64 Hv64 Ev64) as Y; rewrite Hm in Y; exact Y | split; [exact (L5.defined_grows _ _ _ _ MG4 E3d) | right; split; [exact Hcnz | exact Ecat]]].
Qed.
End T.
End CCTL.
