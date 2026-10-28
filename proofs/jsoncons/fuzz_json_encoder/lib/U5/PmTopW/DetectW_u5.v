(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefRead_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import TopSpecsW_u5 DetectKW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_detect_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module DTW.
Definition DJ_RET : Z := 0x478b4.      (* [comment removed for export] *)
Definition DEPTH : Z := 48.            (* [comment removed for export] *)
End DTW.

Module DJW.
Module G := Cut_detect_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_dj : CL.is_ret_at RSEGS DTW.DJ_RET. Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Definition off_of (e : expr) : option Z :=
  match e with
  | EVar v => if Nat.eqb v 42 then Some 0 else None
  | EAlu ALU_ADD (EVar v) (ELit c) => if (Nat.eqb v 42 && (0 <=? c) && (c <=? 4))%bool then Some c else None
  | EAlu ALU_ADD (EVar v) (EAlu ALU_AND _ (ELit 3)) => if Nat.eqb v 42 then Some 3 else None
  | _ => None
  end.
Fixpoint klo (l : list kentry) : Z :=
  match l with
  | [] => 0
  | KRange (EVar v) lo _ :: r => if Nat.eqb v 43 then Z.max lo (klo r) else klo r
  | _ :: r => klo r
  end.
Definition KEPT : list nat := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition leaf_good (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) DTW.DJ_RET && CL.ps_reg_is ps 2 (EVar 2) && TK.keeps_hv ps KEPT &&
   match TK.ps_reg ps 10, TK.ps_reg ps 11 with Some a0e, Some a1e => DKW.leaf_chk (SR.ps_cells ps) a0e a1e | _, _ => false end)%bool.   (* [comment removed for export] *)
Definition GC : list (expr * Z * Z) := DKW.dedup (flat_map (fun ps => DKW.gcons (SR.ps_cells ps)) (CC.cp_PSS G.cp0)).
Lemma all_good : forallb leaf_good (CC.cp_PSS G.cp0) && forallb DKW.inv_ok GC = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma gc_in : forall ps c, In ps (CC.cp_PSS G.cp0) -> In c (DKW.gcons (SR.ps_cells ps)) -> In c GC.
Proof. intros ps c Hps Hc. unfold GC. apply DKW.dedup_in. apply in_flat_map. exists ps. split; [exact Hps | exact Hc]. Qed.

Lemma klo_sound : forall E (M : mem) l, (forall K, In K l -> kentry_ok RSEGS E M K) -> klo l <= bv_unsigned (ev E 43).
Proof.
  intros E M l. induction l as [|K r IH]; intros H.
  - cbn [klo]. pose proof (bv_unsigned_in_range _ (ev E 43)). lia.
  - assert (Hr : klo r <= bv_unsigned (ev E 43)) by (apply IH; intros K' HK'; apply H; right; exact HK').
    destruct K as [| | | | |e lo hi| | | |]; cbn [klo]; try exact Hr. destruct e as [|v| | | | | |]; try exact Hr.
    destruct (Nat.eqb_spec v 43) as [->|_]; [|exact Hr].
    pose proof (H _ (or_introl eq_refl)) as HK. cbn [kentry_ok edenot] in HK. lia.
Qed.
Lemma land3 : forall y, 0 <= y -> 0 <= Z.land y 3 <= 3.
Proof. intros y Hy. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound y (2 ^ 2) ltac:(lia)). change (Z.ones 2) with 3. change (2 ^ 2) with 4 in *. lia. Qed.
Lemma off_sound : forall E e c p, off_of e = Some c -> bv_unsigned (ev E 42) = p -> p + 4 < 2 ^ 64 ->
  exists c', 0 <= c' <= c /\ c' <= 4 /\ edenot E e = Z_to_bv 64 (p + c').
Proof.
  intros E e c p H Hp Hp4. pose proof (bv_unsigned_in_range _ (ev E 42)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. rewrite Hp in Hr.
  destruct e as [|v|op e1 e2| | | | |]; cbn [off_of] in H; try discriminate H.
  - destruct (Nat.eqb_spec v 42) as [->|]; [|discriminate H]. injection H as <-. exists 0. split; [lia|]. split; [lia|]. cbn [edenot]. rewrite Z.add_0_r. apply RK.w_of_u. exact Hp.
  - destruct op; try discriminate H. destruct e1 as [|v| | | | | |]; try discriminate H. destruct e2 as [c0| |op2 x y| | | | |]; try discriminate H.
    + destruct (Nat.eqb v 42 && (0 <=? c0) && (c0 <=? 4))%bool eqn:B; [|discriminate H]. injection H as <-.
      apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2]. apply Nat.eqb_eq in B1. subst v. apply Z.leb_le in B2, B3.
      exists c0. split; [lia|]. split; [lia|]. cbn [edenot]. rewrite (RK.w_of_u _ _ Hp). apply TK.add_lit; lia.
    + destruct op2; try discriminate H. destruct y as [c3| | | | | | |]; try discriminate H.
      destruct c3 as [|c3|]; try discriminate H. destruct c3 as [c3|c3|]; try discriminate H. destruct c3; try discriminate H.
      destruct (Nat.eqb_spec v 42) as [->|]; [|discriminate H]. injection H as <-.
      set (w := edenot E x). pose proof (bv_unsigned_in_range _ w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
      exists (Z.land (bv_unsigned w) 3). pose proof (land3 (bv_unsigned w) ltac:(lia)) as L3. split; [lia|]. split; [lia|].
      cbn [edenot]. fold w. rewrite (RK.w_of_u _ _ Hp). rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. rewrite RK.and_lit by lia. apply TK.add_lit; lia.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem detect_json_okw : TPSW.detect_json_specw L.
Proof.
  intros sp r p k bs fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & Hk & BR & DD & RO & Bbs & LS & FALL) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). destruct BR as (B1 & B2 & B3 & B4 & B5).
  unfold TPS.DETECT_SCR in *. unfold hl_ceil in *. unfold PML.a0, PML.a1 in A0, A1.
  assert (Lbs : length bs = Z.to_nat k) by lia.
  assert (Hrav : 0 <= r < 2 ^ 64) by (destruct Hrok; lia).
  change PML.PC_DETECT_JSON with (CC.cp_pc G.cp0).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun id : nat => if Nat.eqb id 0 then map (Z_to_bv 8) bs else @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1.
    + eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | eapply L5.defined_sub; [exact S5 | lia | lia]].
    + eapply CL5.kwr_intro; [ev_start | ev_len | lia | lia | lia | eapply L5.defined_sub; [exact S5 | lia | lia]].
    + e_range. + e_range.
    + eapply CL5.kblob_intro with (A := p) (bs := bs); [ev_start | rewrite Lbs, Z2Nat.id by lia; unfold elenZ; cbn [edenot]; rw_atoms; reflexivity | lia | rewrite Lbs, Z2Nat.id by lia; lia | lia | reflexivity | exact Bbs | rewrite Lbs, Z2Nat.id by lia; exact DD].
    + tk_kimg RO.
    + e_disj.
  - intros fx' E' R' M' j ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1.
    ck_leaf Hag E'.
    pose proof all_good as GOOD. apply andb_prop in GOOD as [GOOD GINV]. rewrite forallb_forall in GOOD. specialize (GOOD ps (nth_error_In _ _ Hnth)). unfold leaf_good in GOOD.
    apply andb_prop in GOOD as [GOOD Ga0]. apply andb_prop in GOOD as [GOOD Gk]. apply andb_prop in GOOD as [Gpc Gsp]. apply Z.eqb_eq in Gpc.
    destruct (TK.ps_reg ps 10) as [a0e|] eqn:Er; [|discriminate Ga0]. destruct (TK.ps_reg ps 11) as [a1e|] eqn:Er1; [|discriminate Ga0].
    assert (EB' : eb E' 0%nat = map (Z_to_bv 8) bs) by (rewrite <- (proj2 Hag); subst E; reflexivity).
    destruct (DKW.leaf_sound (SR.ps_cells ps) a0e a1e GC E' M' bs k p Ga0 GINV (fun c Hc => gc_in ps c (nth_error_In _ _ Hnth) Hc) (CC.lf_cells _ _ _ _ _ _ _ HLF) EB' FALL LS ltac:(lia)
                ltac:(assumption) ltac:(assumption) ltac:(lia)) as (c' & kind & Hc4 & Hc' & Ee & Hkind & DET).
    assert (R10 : getr R' 10%bv = Z_to_bv 64 (p + c')) by (rewrite (TK.ps_reg_r _ _ _ _ _ _ 10%bv a0e HLF Er); exact Ee).
    assert (R11 : getr R' 11%bv = Z_to_bv 64 kind) by (rewrite (TK.ps_reg_r _ _ _ _ _ _ 11%bv a1e HLF Er1); apply RK.w_of_u; exact Hkind).
    assert (R1 : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ KEPT 1%bv HLF Gk Hag64 ltac:(ck_in)); exact Hra).
    assert (R2 : getr R' 2%bv = getr R 2%bv).
    { rewrite <- (ridx_roundtrip 2%bv) at 1. etransitivity; [exact (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF Gsp)|]. cbn [edenot]. rewrite Hsp. apply RK.w_of_u. assumption. }
    rewrite Gpc. apply (CK.ret_leaf fx' R' _ M' model K r ret_dj Hh Hl R1 Hrok).
    apply (Hcont fx' R' M' Hfp').
    + exists (p + c'). split; [exact R10|]. split; [lia|]. split; [lia|]. exists kind. split; [exact R11|].
      destruct (PMR.detect bs) as [j0|]; [destruct DET as [-> ->]; split; [lia | reflexivity] | exact DET].
    + apply CK.rp_of_keeps; [exact R2|]. intros q Hq. apply (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ KEPT q HLF Gk Hag64). unfold CK.CSR in Hq. unfold KEPT. cbn [In] in *. tauto.
    + apply (CK.samem_frame_but (fun a => ~ (sp - DTW.DEPTH <= a < sp))).
      * unfold DTW.DEPTH. ck_frame HLF.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X. unfold L5.in_rng, DTW.DEPTH in *. cbn [fst snd] in X. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.
End S.
End DJW.
