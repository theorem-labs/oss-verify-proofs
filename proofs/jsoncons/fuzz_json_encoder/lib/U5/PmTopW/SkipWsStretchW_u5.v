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
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_skipws_a_xsrc_u5 Cut_skipws_b_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import SkipWsStretch_u5 PcdStretch_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import PcdStretchW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmRef_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module SWSW.
Import SWS.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_sw_loopw : forall (fx : FPState) R M model K sp1 P e p b st v160 v168 v176 v200 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 80) -> CK.spok sp1 -> sw_live R P e -> getr R 10%bv = Z_to_bv 64 p ->
  2 ^ 40 <= P <= 2 ^ 47 - 272 -> 2 ^ 12 <= p <= 2 ^ 47 -> 0 <= e < 2 ^ 64 -> 0 <= b <= 255 -> 0 <= st <= 255 ->
  0 <= v160 < 2 ^ 64 -> 0 <= v168 < 2 ^ 64 -> 0 <= v176 < 2 ^ 64 -> 0 <= v200 < 2 ^ 64 ->
  L5.u8_at RSEGS M p b -> L5.u8_at RSEGS M (P + 208) st -> L5.u64_at RSEGS M (P + 160) v160 -> L5.u64_at RSEGS M (P + 168) v168 -> L5.u64_at RSEGS M (P + 176) v176 -> L5.u64_at RSEGS M (P + 200) v200 ->
  L5.defined M (P + 160) 24 -> L5.defined M (P + 200) 8 -> sw_frame M sp1 rav R0 -> L5.ra_ok rav -> sp1 <= P -> p + 1 <= sp1 - 80 ->
  (st = 28 -> forall q' (fx' : FPState) R' M', (q' = p + 1 /\ b = 10) \/ (q' = v200 /\ b <> 10) -> PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 SWT.R_POP -> getr R' 10%bv = Z_to_bv 64 P ->
      sw_live R' P e -> TK.keepsR KO7 R R' -> L5.u64_at RSEGS M' (P + 200) q' -> TK.samem (KF P) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_POP_STATE M' model) K) ->
  (st <> 28 -> In b [9; 10; 13; 32] -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 80) -> getr R' 1%bv = Z_to_bv 64 SWT.R_SPACE ->
      getr R' 10%bv = Z_to_bv 64 P -> getr R' 11%bv = Z_to_bv 64 (P + 200) ->
      sw_live R' P e -> TK.keepsR KO7 R R' -> L5.u64_at RSEGS M' (P + 200) v200 -> TK.samem (KF P) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_SPACE M' model) K) ->
  (st <> 28 -> PMR.is_ws b = false -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s06 R0 R' -> TK.keepsR KO7 R R' ->
      L5.u64_at RSEGS M' (P + 200) v200 -> TK.samem (KF P) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R SWT.LOOP M model) K.
Proof.
  intros fx R M model K sp1 P e p b st v160 v168 v176 v200 rav R0 Hh Hl Hfp H2 [Hsp Hal] (H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23) H10 HP Hp He Hb Hst Hv160 Hv168 Hv176 Hv200
         Cb C208 C160 C168 C176 C200 D160 D200 (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) Hra J1 J2 Kpop Kspace Kret.
  change SWT.LOOP with (CC.cp_pc GB.cp0). unfold SWT.MASK in H23.
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19. pose proof (RG 20%bv) as G20. pose proof (RG 21%bv) as G21. pose proof (RG 22%bv) as G22.
  pose proof (RG 23%bv) as G23.
  set (gl := ghf rav R0 [b; st; v160; v168; v176; v200; bv_unsigned (getr R0 23%bv)]).
  ck_open FPM GB.cp0 (GB.plans 0%nat _ eq_refl) (-80) gl (fun _ : nat => @nil byte) [(19%nat, 28); (20%nat, 10); (21%nat, -1); (22%nat, 32); (23%nat, 4294977024)] sp1 R M fx model K Hh Hl Hfp H2 ck_pins.
  - ck_reg E (8%bv : reg) H8. ck_reg E (10%bv : reg) H10. ck_gh E 0%nat rav. ck_gh E 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E 2%nat (bv_unsigned (getr R0 9%bv)).
    ck_gh E 3%nat (bv_unsigned (getr R0 18%bv)). ck_gh E 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E 5%nat (bv_unsigned (getr R0 20%bv)). ck_gh E 6%nat (bv_unsigned (getr R0 21%bv)).
    ck_gh E 7%nat (bv_unsigned (getr R0 22%bv)). ck_gh E 8%nat b. ck_gh E 9%nat st. ck_gh E 10%nat v160. ck_gh E 11%nat v168. ck_gh E 12%nat v176. ck_gh E 13%nat v200.
    ck_gh E 14%nat (bv_unsigned (getr R0 23%bv)).
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + ck_kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6. + ck_kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7.
    + ck_kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8. + ck_kw64 (sp1 - 72) (bv_unsigned (getr R0 23%bv)) F9.
    + e_range. + e_range. + ck_kw8 p b Cb. + e_range. + ck_kw8 (P + 208) st C208. + e_range.
    + ck_kw64 (P + 160) v160 C160. + ck_kw64 (P + 168) v168 C168. + ck_kw64 (P + 176) v176 C176. + ck_kw64 (P + 200) v200 C200.
    + e_wr. + e_wr. + e_disj. + e_disj. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (8%bv : reg) H8. ck_reg E (9%bv : reg) H9. ck_reg E (18%bv : reg) H18. ck_reg E (10%bv : reg) H10. ck_gh E 8%nat b. ck_gh E 9%nat st. ck_gh E 13%nat v200.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 15)%nat) by (change 15%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GB.cp0) with 79%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KF P) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside. }
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (LIVE : (forall r : reg, In (ridx r) [8; 9; 18]%nat -> getr R' r = getr R r) -> getr R' 19%bv = Z_to_bv 64 28 -> getr R' 20%bv = Z_to_bv 64 10 -> getr R' 21%bv = Z_to_bv 64 (-1) ->
                   getr R' 22%bv = Z_to_bv 64 32 -> getr R' 23%bv = Z_to_bv 64 4294977024 -> sw_live R' P e).
    { intros HK X19 X20 X21 X22 X23. unfold sw_live, SWT.MASK. rewrite (HK 8%bv ltac:(ck_in)), (HK 9%bv ltac:(ck_in)), (HK 18%bv ltac:(ck_in)). repeat split; assumption. }
    assert (GB72 : ev E' 72%nat = Z_to_bv 64 b) by (match goal with U : bv_unsigned (ev E' 72%nat) = b |- _ => exact (RK.w_of_u _ _ U) end).
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]]]]]; ck_probes HLF PF.
    + (* [comment removed for export] *)
      destruct PF as (PB & PF & _). rewrite GB72 in PB. apply RK.w_inj in PB; [|lia|lia]. ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      apply (Kpop PF (p + 1) fx' R' M' (or_introl (conj eq_refl PB)) Hfp'); [tk_lin HLF (2%bv : reg) | unfold SWT.R_POP; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply LIVE; [ck_keeps HLF Hag64 [8; 9; 18]%nat | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * ck_cell64 HLF (EVar 40) 200 (EAlu ALU_ADD (EVar 42) (ELit 1)). ck_vlin.
    + (* [comment removed for export] *)
      destruct PF as (PB & PF & _). rewrite GB72 in PB. assert (NB : b <> 10) by (intros X; apply PB; rewrite X; reflexivity). ck_w2z PF. apply RK.w_inj in PF; [|lia|lia].
      apply (Kpop PF v200 fx' R' M' (or_intror (conj eq_refl NB)) Hfp'); [tk_lin HLF (2%bv : reg) | unfold SWT.R_POP; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply LIVE; [ck_keeps HLF Hag64 [8; 9; 18]%nat | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
    + (* [comment removed for export] *)
      destruct PF as (PF & _). ck_w2z PF. assert (NE : st <> 28) by (intros X; apply PF; rewrite X; reflexivity).
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 72) 33 255) HLF ltac:(vm_compute; reflexivity)) as BR. cbn [kentry_ok edenot] in BR. rewrite GB72, u64_of_Z in BR by lia.
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret NE (PSW.nws_big b ltac:(lia)) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply (same_of_gh R0 R' (fun j => ev E' (64 + j)) 14%nat); [tk_reg HLF (8%bv : reg); reflexivity | tk_reg HLF (9%bv : reg); reflexivity | tk_reg HLF (18%bv : reg); reflexivity | tk_reg HLF (19%bv : reg); reflexivity
          | tk_reg HLF (20%bv : reg); reflexivity | tk_reg HLF (21%bv : reg); reflexivity | tk_reg HLF (22%bv : reg); reflexivity | tk_reg HLF (23%bv : reg); reflexivity
          | exact (GH 1%nat _ eq_refl) | exact (GH 2%nat _ eq_refl) | exact (GH 3%nat _ eq_refl) | exact (GH 4%nat _ eq_refl) | exact (GH 5%nat _ eq_refl) | exact (GH 6%nat _ eq_refl) | exact (GH 7%nat _ eq_refl) | exact (GH 14%nat _ eq_refl)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
    + (* [comment removed for export] *)
      destruct PF as (PM & PF & _). rewrite GB72 in PM. ck_w2z PF. assert (NE : st <> 28) by (intros X; apply PF; rewrite X; reflexivity).
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 72) 0 32) HLF ltac:(vm_compute; reflexivity)) as BR. cbn [kentry_ok edenot] in BR. rewrite GB72, u64_of_Z in BR by lia.
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_sw Hh Hl R1 Hra).
      apply (Kret NE (PSW.ws_mask0 b BR PM) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply (same_of_gh R0 R' (fun j => ev E' (64 + j)) 14%nat); [tk_reg HLF (8%bv : reg); reflexivity | tk_reg HLF (9%bv : reg); reflexivity | tk_reg HLF (18%bv : reg); reflexivity | tk_reg HLF (19%bv : reg); reflexivity
          | tk_reg HLF (20%bv : reg); reflexivity | tk_reg HLF (21%bv : reg); reflexivity | tk_reg HLF (22%bv : reg); reflexivity | tk_reg HLF (23%bv : reg); reflexivity
          | exact (GH 1%nat _ eq_refl) | exact (GH 2%nat _ eq_refl) | exact (GH 3%nat _ eq_refl) | exact (GH 4%nat _ eq_refl) | exact (GH 5%nat _ eq_refl) | exact (GH 6%nat _ eq_refl) | exact (GH 7%nat _ eq_refl) | exact (GH 14%nat _ eq_refl)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
    + (* [comment removed for export] *)
      destruct PF as (PW & PF & _). ck_w2z PF. assert (NE : st <> 28) by (intros X; apply PF; rewrite X; reflexivity).
      ck_paths HLF RF. destruct RF as (_ & _ & RB & _). ck_rlin RB.
      assert (B32 : 0 <= b <= 32) by lia. ck_w2z PW.
      apply (Kspace NE (ws_class b B32 PW) fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | unfold SWT.R_SPACE; tk_lin HLF (1%bv : reg) | tk_lin HLF (10%bv : reg) | tk_lin HLF (11%bv : reg) | | ck_keeps HLF Hag64 KO7 | | exact FRM | exact MG].
      * apply LIVE; [ck_keeps HLF Hag64 [8; 9; 18]%nat | tk_lin HLF (19%bv : reg) | tk_lin HLF (20%bv : reg) | sw_reg HLF (21%bv : reg) | tk_lin HLF (22%bv : reg) | tk_lin HLF (23%bv : reg)].
      * ck_cell64 HLF (EVar 40) 200 (EVar 77). ck_atom.
Qed.

End S.
End SWSW.
