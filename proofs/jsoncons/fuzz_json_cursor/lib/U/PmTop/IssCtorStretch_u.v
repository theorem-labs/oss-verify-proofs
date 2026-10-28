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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_issctor_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ICT.
Definition R_INIT : Z := 0x39a60.      Definition R_SBUF : Z := 0x39a94.      Definition RET : Z := 0x39abc.
Definition FRAME : Z := 80.
End ICT.

Module ICS.
Module G := Cut_issctor_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_ic : CL.is_ret_at RSEGS ICT.RET. Proof. CL.solve_is_ret. Qed.

Definition KO8 : list nat := [3; 4; 24; 25; 26; 27]%nat.

Definition ic_live (R : bvmap 5 word) (IS so : Z) : Prop :=
  getr R 8%bv = Z_to_bv 64 IS /\ getr R 9%bv = Z_to_bv 64 so /\ getr R 18%bv = Z_to_bv 64 8 /\ getr R 19%bv = Z_to_bv 64 (IS + 16) /\ getr R 20%bv = Z_to_bv 64 (IS + 120) /\
  getr R 22%bv = Z_to_bv 64 PML.VT_ISS_IOS /\ getr R 23%bv = Z_to_bv 64 (PML.VT_ISS - 24).
Definition SV : list nat := [8; 9; 18; 19; 20; 21; 22; 23]%nat.
Definition same_s07 (R0 R' : bvmap 5 word) : Prop :=
  getr R' 8%bv = getr R0 8%bv /\ getr R' 9%bv = getr R0 9%bv /\ getr R' 18%bv = getr R0 18%bv /\ getr R' 19%bv = getr R0 19%bv /\ getr R' 20%bv = getr R0 20%bv /\
  getr R' 21%bv = getr R0 21%bv /\ getr R' 22%bv = getr R0 22%bv /\ getr R' 23%bv = getr R0 23%bv.
Definition ic_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)) /\ L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 22%bv)) /\ L5.u64_at RSEGS M (sp1 - 72) (bv_unsigned (getr R0 23%bv)).
Lemma ic_frame_x : forall (K : Z -> Prop) (M M' : mem) sp1 rav R0, TK.samem K M M' -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> (forall i, sp1 - 80 <= i < sp1 -> K i) -> ic_frame M sp1 rav R0 -> ic_frame M' sp1 rav R0.
Proof. intros K M M' sp1 rav R0 AG Hsp HK (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). repeat split; (eapply (TK.u64_samem K M M'); [exact AG | lia | intros i Hi; apply HK; lia | assumption]). Qed.
Lemma sv_rp : forall R R', regs_preserved R R' -> forall q : reg, In (ridx q) SV -> getr R' q = getr R q.
Proof. intros R R' RP. apply (TK.keepsR_preserved SV R R' RP). intros q Hq. unfold SV in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma ic_live_keep : forall R R' IS so, (forall q : reg, In (ridx q) SV -> getr R' q = getr R q) -> ic_live R IS so -> ic_live R' IS so.
Proof.
  intros R R' IS so HK (H8 & H9 & H18 & H19 & H20 & H22 & H23). unfold ic_live.
  rewrite (HK 8%bv ltac:(ck_in)), (HK 9%bv ltac:(ck_in)), (HK 18%bv ltac:(ck_in)), (HK 19%bv ltac:(ck_in)), (HK 20%bv ltac:(ck_in)), (HK 22%bv ltac:(ck_in)), (HK 23%bv ltac:(ck_in)). repeat split; assumption.
Qed.
Lemma rp_final : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> same_s07 R0 R' -> TK.keepsR KO8 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23) HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) KO8 -> getr R' q = getr R0 q) by (apply HK). unfold KO8 in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]]]];
    [apply HK'; tauto | apply HK'; tauto | rewrite (QQ _ Hq); exact Q8 | rewrite (QQ _ Hq); exact Q9 | rewrite (QQ _ Hq); exact Q18 | rewrite (QQ _ Hq); exact Q19 | rewrite (QQ _ Hq); exact Q20
    | rewrite (QQ _ Hq); exact Q21 | rewrite (QQ _ Hq); exact Q22 | rewrite (QQ _ Hq); exact Q23 | apply HK'; tauto].
Qed.
Lemma ko8_rp : forall R R', regs_preserved R R' -> TK.keepsR KO8 R R'.
Proof. intros R R' RP. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. unfold KO8 in Hq. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto). Qed.
Lemma sp_rp : forall (R R' : bvmap 5 word), regs_preserved R R' -> getr R' 2%bv = getr R 2%bv.
Proof. intros R R' RP. apply RP. ck_in. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition KE1 (sp1 IS : Z) (a : Z) : Prop := ~ (sp1 - 80 <= a < sp1) /\ ~ (IS <= a < IS + 16) /\ ~ (IS + 120 <= a < IS + 128) /\ ~ (IS + 168 <= a < IS + 176).
Definition KE2 (IS : Z) (a : Z) : Prop := ~ (IS + 256 <= a < IS + 268) /\ ~ (IS <= a < IS + 8) /\ ~ (IS + 120 <= a < IS + 128).

Lemma s_ic_entry : forall (fx : FPState) R M model K sp1 IS so rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 10%bv = Z_to_bv 64 IS -> getr R 11%bv = Z_to_bv 64 so -> getr R 12%bv = Z_to_bv 64 8 ->
  2 ^ 40 <= IS <= 2 ^ 47 - 272 -> 0 <= so < 2 ^ 64 -> PML.img_ro M -> L5.defined M (sp1 - 80) 80 -> L5.defined M IS 272 -> sp1 <= IS ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 ICT.R_INIT -> getr R' 10%bv = Z_to_bv 64 (IS + 120) -> getr R' 11%bv = Z_to_bv 64 (IS + 16) ->
      ic_live R' IS so -> ic_frame M' sp1 rav R -> TK.keepsR KO8 R R' -> TK.samem (KE1 sp1 IS) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_IOSB_INIT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_ISS_CTOR M model) K.
Proof.
  intros fx R M model K sp1 IS so rav Hh Hl Hfp H2 [Hsp Hal] H1 Hra H10 H11 H12 HIS Hso RO DF DI J1 Kinit.
  change PML.PC_ISS_CTOR with (CC.cp_pc G.cp0).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) [(12%nat, 8)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (10%bv : reg) H10.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + tk_kimg RO. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11. ck_reg E (1%bv : reg) H1.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE1 sp1 IS) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3 & Hk4); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kinit fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold ICT.R_INIT; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | | | ck_keeps HLF Hag64 KO8 | exact FRM | exact MG].
    + unfold ic_live, PML.VT_ISS_IOS, PML.VT_ISS. repeat split; [tk_lin HLF (8%bv : reg) | tk_lin HLF (9%bv : reg) | tk_lin HLF (18%bv : reg) | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
    + unfold ic_frame. repeat split; [ck_cell64 HLF (EVar 2) (-8) (EVar 33); ck_atom | ck_saved HLF Hag64 (-16) 40%nat (8%bv : reg) | ck_saved HLF Hag64 (-24) 41%nat (9%bv : reg) | ck_saved HLF Hag64 (-32) 50%nat (18%bv : reg)
        | ck_saved HLF Hag64 (-40) 51%nat (19%bv : reg) | ck_saved HLF Hag64 (-48) 52%nat (20%bv : reg) | ck_saved HLF Hag64 (-56) 53%nat (21%bv : reg) | ck_saved HLF Hag64 (-64) 54%nat (22%bv : reg)
        | ck_saved HLF Hag64 (-72) 55%nat (23%bv : reg)].
Qed.

Lemma s_ic_r_init : forall (fx : FPState) R M model K sp1 IS so,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> ic_live R IS so ->
  2 ^ 40 <= IS <= 2 ^ 47 - 272 -> 0 <= so < 2 ^ 64 -> L5.defined M IS 272 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 ICT.R_SBUF -> getr R' 10%bv = Z_to_bv 64 (IS + 16) -> getr R' 11%bv = Z_to_bv 64 so ->
      getr R' 12%bv = Z_to_bv 64 8 -> TK.keepsR KO8 R R' -> L5.u64_at RSEGS M' IS PML.VT_ISS -> L5.u64_at RSEGS M' (IS + 120) PML.VT_ISS_IOS -> TK.samem (KE2 IS) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SBUF_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R ICT.R_INIT M model) K.
Proof.
  intros fx R M model K sp1 IS so Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18 & H19 & H20 & H22 & H23) HIS Hso DI Ksb.
  change ICT.R_INIT with (CC.cp_pc G.cp1). unfold PML.VT_ISS_IOS, PML.VT_ISS in H22, H23.
  ck_open FPM G.cp1 (G.plans 1%nat _ eq_refl) (-80) (@nil Z) (fun _ : nat => @nil byte) [(18%nat, 8)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (20%bv : reg) H20.
    unfold know_ok, G.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (19%bv : reg) H19. ck_reg E (20%bv : reg) H20. ck_reg E (22%bv : reg) H22. ck_reg E (23%bv : reg) H23.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KE2 IS) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2 & Hk3); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Ksb fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold ICT.R_SBUF; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | tk_lin HLF (12%bv : reg) | ck_keeps HLF Hag64 KO8 | | | exact FRM | exact MG].
    + unfold PML.VT_ISS. ck_cell64 HLF (EVar 40) 0 (EAlu ALU_ADD (EVar 55) (ELit 24)). ck_vlin.
    + unfold PML.VT_ISS_IOS. ck_cell64 HLF (EVar 40) 120 (EVar 54). ck_atom.
Qed.

Lemma s_ic_r_sbuf : forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> ic_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s07 R0 R' -> TK.keepsR KO8 R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R ICT.R_SBUF M model) K.
Proof.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) Hra Kret.
  change ICT.R_SBUF with (CC.cp_pc G.cp2).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22. pose proof (RG 23%bv) as G23.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 21%bv);
              bv_unsigned (getr R0 22%bv); bv_unsigned (getr R0 23%bv)]).
  ck_open FPM G.cp2 (G.plans 2%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)).
    ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)). ck_gh E 7%nat (bv_unsigned (getr R0 22%bv)). ck_gh E 8%nat (bv_unsigned (getr R0 23%bv)).
    unfold know_ok, G.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3.
    + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4. + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + ck_kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 9)%nat) by (change 9%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx G.cp2) with 73%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
    apply (CK.ret_leaf fx' R' _ M model K rav ret_ic Hh Hl R1 Hra).
    apply (Kret fx' R' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO8].
    unfold same_s07. repeat split.
    + tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (20%bv : reg). etransitivity; [exact (GH 5%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (21%bv : reg). etransitivity; [exact (GH 6%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (22%bv : reg). etransitivity; [exact (GH 7%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
    + tk_reg HLF (23%bv : reg). etransitivity; [exact (GH 8%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
Qed.
End S.
End ICS.
