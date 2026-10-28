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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u TopSpecs2_u ReadKit_u ChunkKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_iosbinit_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module II.
Module G := Cut_iosbinit_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma al8_add : forall a k, a mod 8 = 0 -> k mod 8 = 0 -> (a + k) mod 8 = 0.
Proof. intros a k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; apply Z.mod_divide; try lia; assumption. Qed.

Lemma u64_zero : forall (M : mem) A, (forall i, 0 <= i < 8 -> M (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0)) -> L5.u64_at RSEGS M A 0.
Proof.
  intros M A H. unfold L5.u64_at. cbn [rdn]. rewrite !L5C.add1_lit.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  replace (A + 1 + 1) with (A + 2) by lia. replace (A + 2 + 1) with (A + 3) by lia. replace (A + 3 + 1) with (A + 4) by lia. replace (A + 4 + 1) with (A + 5) by lia.
  replace (A + 5 + 1) with (A + 6) by lia. replace (A + 6 + 1) with (A + 7) by lia.
  rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)), (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition KI (sp1 B : Z) (a : Z) : Prop := ~ (sp1 - 16 <= a < sp1) /\ ~ (B + 8 <= a < B + 136).

Definition init_cells (M : mem) (B rb : Z) : Prop :=
  L5.u32_at RSEGS M (B + 32) 0 /\ L5.u32_at RSEGS M (B + 36) 0 /\ L5.u64_at RSEGS M (B + 40) rb /\ (forall k, 0 <= k < 10 -> L5.u64_at RSEGS M (B + 56 + 8 * k) 0).
Lemma init_cells_x : forall (K : Z -> Prop) (M M' : mem) B rb, TK.samem K M M' -> 0 <= B < 2 ^ 60 -> (forall i, (B + 32 <= i < B + 48 \/ B + 56 <= i < B + 136) -> K i) ->
  init_cells M B rb -> init_cells M' B rb.
Proof.
  intros K M M' B rb AG HB HK (C32 & C36 & C40 & CZ). unfold init_cells.
  split; [apply (TK.u32_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C32]|].
  split; [apply (TK.u32_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C36]|].
  split; [apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact C40]|].
  intros k Hk. apply (TK.u64_samem K M M' _ _ AG); [lia | intros i Hi; apply HK; lia | exact (CZ k Hk)].
Qed.

Lemma s_ii_entry : forall (fx : FPState) R M model K sp1 B rb,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp1 -> CK.spok sp1 -> getr R 10%bv = Z_to_bv 64 B -> getr R 11%bv = Z_to_bv 64 rb ->
  2 ^ 40 <= B <= 2 ^ 47 - 152 -> 1 <= rb <= 2 ^ 47 -> L5.defined M (sp1 - 16) 16 -> L5.defined M B 152 -> sp1 <= B ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = getr R 1%bv -> getr R' 10%bv = Z_to_bv 64 (B + 48) -> TK.keepsR CK.CSR R R' ->
      init_cells M' B rb -> TK.samem (KI sp1 B) M M' -> mem_grows M M' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_LOCALE_CTOR M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_IOSB_INIT M model) K.
Proof.
  intros fx R M model K sp1 B rb Hh Hl Hfp H2 [Hsp Hal] H10 H11 HB Hrb DF DB J1 Kloc.
  change PML.PC_IOSB_INIT with (CC.cp_pc G.cp0).
  ck_open FPM G.cp0 (G.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 ck_no_pins.
  - ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11.
    unfold know_ok, G.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range. + e_range. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) H10. ck_reg E (11%bv : reg) H11.
    ck_leaf Hag E'.
    assert (FRM : TK.samem (KI sp1 B) M M') by (apply (TK.frame_samem _ _ _ _ _ _ _ HLF); intros a Ha (Hk1 & Hk2); cbn [CC.cp_F]; tk_outside).
    pose proof (CC.lf_grows _ _ _ _ _ _ _ HLF) as MG.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (Kloc fx' R' M' Hfp'); [tk_lin HLF (2%bv : reg) | exact (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ [1%nat] 1%bv HLF eq_refl Hag64 ltac:(ck_in)) | tk_lin HLF (10%bv : reg) | ck_keeps HLF Hag64 CK.CSR | | exact FRM | exact MG].
    unfold init_cells.
    split; [ck_cell32 HLF (EVar 42) 32 (ELit 0); reflexivity|]. split; [ck_cell32 HLF (EVar 42) 36 (ELit 0); reflexivity|]. split; [ck_cell64 HLF (EVar 42) 40 (EVar 43); ck_atom|].
    pose proof (CK.lf_cell _ _ _ _ _ _ (KZero (SA (EVar 42) 56) (ELit 80)) HLF ltac:(vm_compute; reflexivity)) as KZ. cbn [kentry_ok] in KZ. destruct KZ as (_ & KZ).
    assert (ES : estart E' (SA (EVar 42) 56) = B + 56) by ev_start. rewrite ES in KZ. change (elenZ E' (ELit 80)) with 80 in KZ.
    intros j Hj. apply u64_zero. intros i Hi. replace (B + 56 + 8 * j + i) with (B + 56 + (8 * j + i)) by lia. apply KZ. lia.
Qed.

Theorem iosb_init_later_ok : PMS.locale_ctor_later_spec L -> TPS2.iosb_init_later_spec L.
Proof.
  intros LOC B rb sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & Hrb & GL & RO & (O1 & O2 & O3) & DB) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). unfold PML.a0, PML.a1, TPS2.IOSBI_SCR in *.
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  apply (s_ii_entry fx R M model K sp B rb Hh Hl Hfp Hsp SPOK A0 A1 ltac:(lia) ltac:(lia) ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) DB O1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a KR1 IC1 AG1 MG1.
  apply (LOC (B + 48) sp r fx1 R1 M1 model K Hh Hl HK0 Hfp1).
  { split; [apply (CK.mk_entry L R1 M1 sp r 32 ltac:(rewrite H1a; exact Hra) Hrok H2a ltac:(rewrite (KR1 4%bv ltac:(ck_in)); exact Htp)); apply (CK.sub_stk _ M M1 sp _ _ _ STK MG1 S1); lia|].
    split; [exact H10a|].
    split; [destruct GL as (G1 & G2); split; [apply (TK2.u8_x _ M M1 AG1); [lia | intros i Hi; unfold KI; lia | exact G1] | apply (TK2.u64_x _ M M1 AG1); [lia | intros i Hi; unfold KI; lia | exact G2]]|].
    split; [apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold KI; lia | exact RO]|].
    split; [split; [lia | split; [lia | apply al8_add; [exact O3 | reflexivity]]]|].
    apply (L5.defined_grows _ _ _ _ MG1). eapply L5.defined_sub; [exact DB | lia | lia]. }
  intros fx2 R2 M2 Hfp2 C48 RP2 FB2 MG2. pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
  assert (OUT2 : forall a, ~ (sp - 32 <= a < sp) -> ~ (B + 48 <= a < B + 56) -> L5.outside [(sp - 32, 32); (B + 48, 8)] a).
  { intros a Z1 Z2 w Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  apply (Hcont fx2 R2 M2 Hfp2).
  - destruct (init_cells_x _ M1 M2 B rb AG2 ltac:(lia) ltac:(intros i Hi; apply OUT2; lia) IC1) as (C32 & C36 & C40 & CZ).
    split; [exact C32|]. split; [exact C36|]. split; [exact C40|]. split; [exact C48|]. split; [exact CZ|].
    exact (L5.defined_grows _ _ _ _ MG2 (L5.defined_grows _ _ _ _ MG1 DB)).
  - intros q Hq. rewrite (RP2 q Hq). apply (CK.rp_of_keeps R R1); [rewrite H2a, Hsp; reflexivity | exact KR1 | exact Hq].
  - apply (CK.samem_frame_but (fun a => KI sp B a /\ L5.outside [(sp - 32, 32); (B + 48, 8)] a)); [exact (CK.samem_weaken2 _ _ _ _ _ _ AG1 AG2 (fun a Ha => Ha))|].
    intros a Ha. pose proof (Ha (sp - 48, 48) ltac:(ck_in)) as X1. pose proof (Ha (B, 136) ltac:(ck_in)) as X2. unfold L5.in_rng in X1, X2. cbn [fst snd] in X1, X2.
    split; [unfold KI; lia | apply OUT2; lia].
  - intros z Hz. apply MG2, MG1. exact Hz.
Qed.

Theorem iosb_init_first_ok : PMS.locale_ctor_first_spec L -> TPS2.iosb_init_first_spec L.
Proof.
  intros LOC B rb sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & Hrb & LS & (O1 & O2 & O3) & DB) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). unfold PML.a0, PML.a1 in *.
  assert (ISL : PMS.ISLAND_SCR = 4096) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [lia | exact S1]).
  apply (s_ii_entry fx R M model K sp B rb Hh Hl Hfp Hsp SPOK A0 A1 ltac:(lia) ltac:(lia) ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) DB O1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a KR1 IC1 AG1 MG1.
  apply (LOC (B + 48) sp r fx1 R1 M1 model K Hh Hl HK0 Hfp1).
  { split; [apply (CK.mk_entry L R1 M1 sp r _ ltac:(rewrite H1a; exact Hra) Hrok H2a ltac:(rewrite (KR1 4%bv ltac:(ck_in)); exact Htp)); apply (CK.sub_stk _ M M1 sp _ _ _ STK MG1 S1); lia|].
    split; [exact H10a|].
    split; [apply (TK2.ls_ok_x _ M M1 AG1); [apply CK.statics_cov_lo; intros a Ha; unfold KI; lia | exact LS]|].
    split; [split; [lia | split; [lia | apply al8_add; [exact O3 | reflexivity]]]|].
    apply (L5.defined_grows _ _ _ _ MG1). eapply L5.defined_sub; [exact DB | lia | lia]. }
  intros fx2 R2 M2 Hfp2 (C48 & IP) RP2 FB2 MG2. pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
  assert (OUT2 : forall a, 2 ^ 40 <= a -> ~ (sp - PMS.ISLAND_SCR <= a < sp) -> ~ (B + 48 <= a < B + 56) -> L5.outside ((sp - PMS.ISLAND_SCR, PMS.ISLAND_SCR) :: (B + 48, 8) :: TPS2.island_W) a).
  { intros a Z0 Z1 Z2 w Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|Hw]]; cbn [fst snd]; [lia | lia |].
    unfold TPS2.island_W, PML.ll_prist_csrc in Hw. cbn [map fst snd] in Hw. repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; lia|]). destruct Hw. }
  apply (Hcont fx2 R2 M2 Hfp2).
  - split; [|exact IP].
    destruct (init_cells_x _ M1 M2 B rb AG2 ltac:(lia) ltac:(intros i Hi; apply OUT2; lia) IC1) as (C32 & C36 & C40 & CZ).
    split; [exact C32|]. split; [exact C36|]. split; [exact C40|]. split; [exact C48|]. split; [exact CZ|].
    exact (L5.defined_grows _ _ _ _ MG2 (L5.defined_grows _ _ _ _ MG1 DB)).
  - intros q Hq. rewrite (RP2 q Hq). apply (CK.rp_of_keeps R R1); [rewrite H2a, Hsp; reflexivity | exact KR1 | exact Hq].
  - apply (CK.samem_frame_but (fun a => KI sp B a /\ L5.outside ((sp - PMS.ISLAND_SCR, PMS.ISLAND_SCR) :: (B + 48, 8) :: TPS2.island_W) a)); [exact (CK.samem_weaken2 _ _ _ _ _ _ AG1 AG2 (fun a Ha => Ha))|].
    intros a Ha. split.
    + pose proof (Ha (sp - (16 + PMS.ISLAND_SCR), 16 + PMS.ISLAND_SCR) ltac:(left; reflexivity)) as X1. pose proof (Ha (B, 136) ltac:(right; left; reflexivity)) as X2.
      unfold L5.in_rng in X1, X2. cbn [fst snd] in X1, X2. unfold KI. lia.
    + intros w Hw Hin. destruct Hw as [<-|[<-|Hw]].
      * apply (Ha (sp - (16 + PMS.ISLAND_SCR), 16 + PMS.ISLAND_SCR) ltac:(left; reflexivity)). unfold L5.in_rng in *. cbn [fst snd] in *. lia.
      * apply (Ha (B, 136) ltac:(right; left; reflexivity)). unfold L5.in_rng in *. cbn [fst snd] in *. lia.
      * apply (Ha w ltac:(right; right; exact Hw)). exact Hin.
  - intros z Hz. apply MG2, MG1. exact Hz.
Qed.
End S.
End II.
