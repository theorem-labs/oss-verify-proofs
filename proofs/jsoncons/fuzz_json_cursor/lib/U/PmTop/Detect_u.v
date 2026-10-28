(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_detect_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module DT.
Definition DJ_RET : Z := 0x3c278.
Definition DEPTH : Z := 48.
End DT.

Module DJ.
Module G := Cut_detect_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_dj : CL.is_ret_at RSEGS DT.DJ_RET. Proof. CL.solve_is_ret. Qed.

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
  (Z.eqb (SR.ps_pc ps) DT.DJ_RET && CL.ps_reg_is ps 2 (EVar 2) && TK.keeps_hv ps KEPT &&
   match TK.ps_reg ps 10 with Some e => match off_of e with Some c => c <=? klo (SR.ps_cells ps) | None => false end | None => false end)%bool.
Lemma all_good : forallb leaf_good (CC.cp_PSS G.cp0) = true.
Proof. vmc_refl. Qed.

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

Theorem detect_json_ok : TPS.detect_json_spec L.
Proof.
  intros sp r p k fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & Hk & BR & DD & RO) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). destruct BR as (B1 & B2 & B3 & B4 & B5).
  unfold TPS.DETECT_SCR in *. unfold hl_ceil in *. unfold PML.a0, PML.a1 in A0, A1.
  destruct (CK.bytes_of_defined M (Z.to_nat k) p ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; exact DD)) as (bs & Lbs & Bbs).
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
    pose proof all_good as GOOD. rewrite forallb_forall in GOOD. specialize (GOOD ps (nth_error_In _ _ Hnth)). unfold leaf_good in GOOD.
    apply andb_prop in GOOD as [GOOD Ga0]. apply andb_prop in GOOD as [GOOD Gk]. apply andb_prop in GOOD as [Gpc Gsp]. apply Z.eqb_eq in Gpc.
    destruct (TK.ps_reg ps 10) as [e|] eqn:Er; [|discriminate Ga0]. destruct (off_of e) as [c|] eqn:Eo; [|discriminate Ga0]. apply Z.leb_le in Ga0.
    pose proof (klo_sound E' M' _ (CC.lf_cells _ _ _ _ _ _ _ HLF)) as KLO. match goal with U : bv_unsigned (ev E' 43) = _ |- _ => rewrite U in KLO end.
    destruct (off_sound E' e c p Eo ltac:(assumption) ltac:(lia)) as (c' & Hc' & Hc4 & Ee).
    assert (R10 : getr R' 10%bv = Z_to_bv 64 (p + c')) by (rewrite (TK.ps_reg_r _ _ _ _ _ _ 10%bv e HLF Er); exact Ee).
    assert (R1 : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ KEPT 1%bv HLF Gk Hag64 ltac:(ck_in)); exact Hra).
    assert (R2 : getr R' 2%bv = getr R 2%bv).
    { rewrite <- (ridx_roundtrip 2%bv) at 1. etransitivity; [exact (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF Gsp)|]. cbn [edenot]. rewrite Hsp. apply RK.w_of_u. assumption. }
    rewrite Gpc. apply (CK.ret_leaf fx' R' _ M' model K r ret_dj Hh Hl R1 Hrok).
    apply (Hcont fx' R' M' Hfp').
    + exists (p + c'). split; [exact R10 | lia].
    + apply CK.rp_of_keeps; [exact R2|]. intros q Hq. apply (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ KEPT q HLF Gk Hag64). unfold CK.CSR in Hq. unfold KEPT. cbn [In] in *. tauto.
    + apply (CK.samem_frame_but (fun a => ~ (sp - DT.DEPTH <= a < sp))).
      * unfold DT.DEPTH. ck_frame HLF.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X. unfold L5.in_rng, DT.DEPTH in *. cbn [fst snd] in X. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.
End S.
End DJ.
