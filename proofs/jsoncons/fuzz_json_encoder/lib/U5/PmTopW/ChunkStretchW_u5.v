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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5 ChunkStretch_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_chunk_a_xsrc_u5 Cut_chunk_b_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CSW.
Import CS.
Module GA := Cut_chunk_a_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Definition KIND_EXPR : expr := EAlu ALU_SLTU (EAlu ALU_SUB (EMd M_MUL (ELit 2) (EAluw ALU_SRL (EVar 43) (ELit 1))) (ELit 0)) (ELit 1).
Definition EK (kind : Z) : env := Env (fun v => if Nat.eqb v 43 then Z_to_bv 64 kind else Z_to_bv 64 0) (fun _ => []).
Definition kind_test (kind : Z) : Z := bv_unsigned (edenot (EK kind) KIND_EXPR).
Example kind_test_1 : kind_test 1 = 1. Proof. vm_compute. reflexivity. Qed.
Example kind_test_2 : kind_test 2 = 0. Proof. vm_compute. reflexivity. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Lemma s_rc_r_detectw : forall (fx : FPState) R M model K sp1 Rr E k0 p p' kind bofb rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 (sp1 - 48) -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 kind -> rc_live2 R Rr E k0 p ->
  2 ^ 40 <= Rr <= 2 ^ 47 -> 0 <= E < 2 ^ 64 -> 0 <= k0 <= 16384 -> 0 <= p -> p <= p' <= p + k0 -> p + k0 < 2 ^ 63 -> 0 <= kind < 2 ^ 64 ->
  rc_frame M sp1 rav R0 -> L5.ra_ok rav -> L5.u8_at RSEGS M (Rr + 296) bofb -> 0 <= bofb <= 1 -> L5.defined M (Rr + 296) 1 -> sp1 <= Rr ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 10%bv = Z_to_bv 64 p' -> getr R' 11%bv = Z_to_bv 64 (k0 + p - p') ->
      same_s03 R0 R' -> TK.keepsR KO R R' -> L5.u8_at RSEGS M' (Rr + 296) 0 -> TK.samem (fun a => ~ (Rr + 296 <= a < Rr + 297)) M M' -> mem_grows M M' ->
      kind_test kind = 1 (* [comment removed for export] *) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 48) -> getr R' 1%bv = Z_to_bv 64 CKT.RC_R_SETEC ->
      getr R' 10%bv = Z_to_bv 64 E -> getr R' 11%bv = Z_to_bv 64 30 -> TK.keepsR KO R R' -> L5.u8_at RSEGS M' (Rr + 296) bofb -> TK.samem (fun a => ~ (Rr + 296 <= a < Rr + 297)) M M' -> mem_grows M M' ->
      2 <= kind (* [comment removed for export] *) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R CKT.RC_R_DETECT M model) K.
Proof.
  intros fx R M model K sp1 Rr E k0 p p' kind bofb rav R0 Hh Hl Hfp H2 [Hsp Hal] H10 H11 ((H18 & H19) & H8 & H9) HRr HE Hk0 Hp Hp' Hpk Hkind (F1 & F2 & F3 & F4 & F5) Hra C296 Hbof D296 J1 Kok Kbad.
  change CKT.RC_R_DETECT with (CC.cp_pc GA.cp2).
  assert (Hrav : 0 <= rav < 2 ^ 64) by (destruct Hra; lia).
  pose proof (fun q : reg => bv_unsigned_in_range _ (getr R0 q)) as RG. change (bv_modulus 64) with (2 ^ 64) in RG.
  pose proof (RG 8%bv) as G8. pose proof (RG 9%bv) as G9. pose proof (RG 18%bv) as G18. pose proof (RG 19%bv) as G19.
  set (gl := [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bofb]).
  ck_open FPM GA.cp2 (GA.plans 2%nat _ eq_refl) (-48) gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E0 (18%bv : reg) H18. ck_gh E0 0%nat rav. ck_gh E0 1%nat (bv_unsigned (getr R0 8%bv)). ck_gh E0 2%nat (bv_unsigned (getr R0 9%bv)). ck_gh E0 3%nat (bv_unsigned (getr R0 18%bv)).
    ck_gh E0 4%nat (bv_unsigned (getr R0 19%bv)). ck_gh E0 5%nat bofb.
    unfold know_ok, GA.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + ck_kw64 (sp1 - 8) rav F1. + ck_kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2. + ck_kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + ck_kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + ck_kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5.
    + e_range. + ck_kw8 (Rr + 296) bofb C296. + e_range. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E0 (9%bv : reg) H9. ck_reg E0 (8%bv : reg) H8. ck_reg E0 (18%bv : reg) H18. ck_reg E0 (19%bv : reg) H19. ck_reg E0 (10%bv : reg) H10. ck_reg E0 (11%bv : reg) H11 (* [comment removed for export] *). ck_gh E0 5%nat bofb.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj8 : (j < 6)%nat) by (change 6%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GA.cp2) with 70%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    assert (FRM : TK.samem (fun a => ~ (Rr + 296 <= a < Rr + 297)) M M').
    { apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk1. cbn [CC.cp_F]. tk_outside. }
    ck_leaf_k k Hnth; [|ck_leaf_k k Hnth; [|ck_leaf_end k Hnth]].
    + (* [comment removed for export] *)
      assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (tk_reg HLF (1%bv : reg); exact (GH 0%nat _ eq_refl)).
      apply (CK.ret_leaf fx' R' _ M' model K rav ret_rc Hh Hl R1 Hra).
      assert (KT : kind_test kind = 1).
      { pose proof (CK.lf_cell _ _ _ _ _ _ (KRange KIND_EXPR 1 1) HLF ltac:(vm_compute; reflexivity)) as [X1 X2].
        assert (EV : ev E' 43 = ev (EK kind) 43).
        { cbn [EK ev Nat.eqb]. match goal with U : bv_unsigned (ev E' 43) = kind |- _ => exact (RK.w_of_u _ _ U) end. }
        unfold kind_test. rewrite <- (RLF.edenot_closed_but 43 KIND_EXPR E' (EK kind) eq_refl EV). lia. }
      apply (Kok fx' R' M' Hfp'); [.. | exact KT].
      * tk_lin HLF (2%bv : reg).
      * rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [10%nat] 10%bv HLF eq_refl Hag64 ltac:(ck_in)). exact H10.
      * tk_lin HLF (11%bv : reg).
      * unfold same_s03. repeat split.
        -- tk_reg HLF (8%bv : reg). etransitivity; [exact (GH 1%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (9%bv : reg). etransitivity; [exact (GH 2%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (18%bv : reg). etransitivity; [exact (GH 3%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
        -- tk_reg HLF (19%bv : reg). etransitivity; [exact (GH 4%nat _ eq_refl) | apply Z_to_bv_bv_unsigned].
      * ck_keeps HLF Hag64 KO.
      * ck_cell8 HLF (EVar 50) 296 (ELit 0). reflexivity.
      * exact FRM. * exact MG.
    + (* [comment removed for export] *)
      assert (KB : 2 <= kind).
      { pose proof (CK.lf_cell _ _ _ _ _ _ (KRange (EVar 43) 2 18446744073709551615) HLF ltac:(vm_compute; reflexivity)) as [X1 X2]. cbn [edenot] in X1.
        match goal with U : bv_unsigned (ev E' 43) = kind |- _ => rewrite U in X1 end. exact X1. }
      apply (Kbad fx' R' M' Hfp'); [.. | exact KB].
      * tk_lin HLF (2%bv : reg). * unfold CKT.RC_R_SETEC. tk_lin HLF (1%bv : reg). * tk_lin HLF (10%bv : reg). * tk_lin HLF (11%bv : reg).
      * ck_keeps HLF Hag64 KO. * ck_cell8 HLF (EVar 50) 296 (EVar 69). ck_atom. * exact FRM. * exact MG.
Qed.

End S.
End CSW.
