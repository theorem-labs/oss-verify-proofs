(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibWP2Spec LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec AsLibCurveSpec BoLibReadA2Ba BoLibReadA2Bb BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

Section RC.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z) (fs : Z) (ch : chain).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre_bo SEGS as_both ceil data len bs sp T A pcs fs ch FPI0 regs0 mem0.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation eobw := (Z_to_bv 64 (bv_unsigned data + len)).
  #[local] Abbreviation ADM := (adm ceil FPI0 regs0 mem0 ret data len bs sp T A fs ch).
  #[local] Abbreviation TAGC := (tagc data len T).
  #[local] Abbreviation pre_factsI := (pre_facts ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation pre_tagI := (pre_tag ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).

  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 240)%Z) by (rewrite A2, u_small by lia; lia).

  (* [comment removed for export] *)
  Definition bb (buf : word) (i : Z) : Z := bs_byte bs (bv_unsigned buf + i - bv_unsigned data).
  Definition W (buf : word) (i : Z) : word := Z_to_bv 64 (bb buf i).

  Lemma bb_range : forall buf i, (0 <= bb buf i < 256)%Z.
  Proof using data bs. intros. unfold bb. apply bs_byte_range. Qed.
  Lemma uW : forall buf i, bv_unsigned (W buf i) = bb buf i.
  Proof using data bs. intros. unfold W. pose proof (bb_range buf i). rewrite u_small by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition curves10 (M : word -> option byte) : Prop :=
    Forall (fun off => curve_ok SEGS M data len (a + off)) a2b_curve_offsets.

  (* [comment removed for export] *)
  Definition mab_cells (ic mc : Z) (M : word -> option byte) : Prop :=
    cell32 SEGS M (a + 144) ic /\ cell32 SEGS M (a + 300) 3 /\ cell32 SEGS M (a + 296) mc /\
    (0 <= ic <= 4)%Z /\ (mc = 0 \/ mc = 3)%Z.

  Lemma mab_cells_frame : forall ic mc M M' rs,
    mab_cells ic mc M -> frame_mod M M' rs -> apart (a + 144) 4 rs -> apart (a + 296) 8 rs -> mab_cells ic mc M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE.
    intros ic mc M M' rs (C1 & C2 & C3 & H4 & H5) Hf Hap1 Hap2. pose proof pre_factsI as (P1 & P2 & P3 & P4 & _). app_facts.
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|exact Hap1]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|eapply apart_sub; [exact Hap2|lia|lia|lia]]|].
    split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|eapply apart_sub; [exact Hap2|lia|lia|lia]]|].
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition be4 (buf : word) (i : Z) : Z :=
    (bb buf (i + 3) + 256 * bb buf (i + 2) + 65536 * bb buf (i + 1) + 16777216 * bb buf i)%Z.
  Lemma be4_range : forall buf i, (0 <= be4 buf i < 4294967296)%Z.
  Proof using data bs.
    intros buf i. unfold be4. pose proof (bb_range buf i). pose proof (bb_range buf (i+1)).
    pose proof (bb_range buf (i+2)). pose proof (bb_range buf (i+3)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition le4w (buf : word) (i : Z) : word :=
    alu64 ALU_ADD (W buf i) (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 256) (W buf (i + 1)))
      (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 65536) (W buf (i + 2))) (mul_div M_MUL (Z_to_bv 64 16777216) (W buf (i + 3))))).
  Definition LE4 (v : nat) : expr :=
    EAlu ALU_ADD (EVar v) (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar (S v)))
      (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar (S (S v)))) (EMd M_MUL (ELit 16777216) (EVar (S (S (S v))))))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stk (buf : word) (M : word -> option byte) : Prop :=
    cell64 SEGS M (spv - 240 + 0) (Z_to_bv 64 0xff00) /\ cell64 SEGS M (spv - 240 + 8) (W buf 29) /\
    cell64 SEGS M (spv - 240 + 16) (W buf 28) /\ cell64 SEGS M (spv - 240 + 24) (W buf 31) /\
    cell64 SEGS M (spv - 240 + 32) (W buf 30) /\
    cell64 SEGS M (spv - 240 + 40) (Z_to_bv 64 (SB + (a + 300) / 8)) /\
    cell64 SEGS M (spv - 240 + 48) (Z_to_bv 64 (a + 300)) /\
    cell64 SEGS M (spv - 240 + 56) (Z_to_bv 64 (SB + (t + 8) / 8)) /\
    cell64 SEGS M (spv - 240 + 64) (Z_to_bv 64 (SB + (t + 16) / 8)) /\
    cell64 SEGS M (spv - 240 + 72) (Z_to_bv 64 (t + 16)) /\
    cell64 SEGS M (spv - 240 + 80) (Z_to_bv 64 (a + 144)) /\
    cell64 SEGS M (spv - 240 + 88) (Z_to_bv 64 (SB + (a + 144) / 8)) /\
    cell64 SEGS M (spv - 240 + 96) (W buf 25) /\ cell64 SEGS M (spv - 240 + 104) (W buf 26) /\
    cell64 SEGS M (spv - 240 + 112) (W buf 27) /\ cell64 SEGS M (spv - 240 + 120) (W buf 24) /\
    cell64 SEGS M (spv - 240 + 128) eobw.

  Lemma stk_frame : forall buf M M' rs,
    stk buf M -> frame_mod M M' rs -> apart (spv - 240) 136 rs -> stk buf M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE.
    intros buf M M' rs HS Hf Hap.
    destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17).
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & _). unfold stk. app_facts.
    repeat match goal with |- _ /\ _ => split end;
      (eapply cell64_frame; [exact Hf | eassumption | lia | lia | eapply apart_sub; [exact Hap|lia|lia|lia]]).
  Qed.

  Lemma stk_frame0 : forall buf M M' rs,
    stk buf M -> frame_mod M M' rs -> rs_within rs (BIG0 sp A) -> apart (spv - 240) 136 rs -> stk buf M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE. intros. eapply stk_frame; eauto. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mbytes (buf : word) : list word :=
    [W buf 8; W buf 9; W buf 12; W buf 13; W buf 14; W buf 15; W buf 16; W buf 17; W buf 18; W buf 19; W buf 20;
     W buf 21; W buf 22; W buf 23; W buf 24; W buf 25; W buf 26; W buf 27; W buf 28; W buf 29; W buf 30; W buf 31].
  Definition mvals (sz : Z) (buf : word) : list word := [Z_to_bv 64 sz; buf; T] ++ mbytes buf ++ [eobw].

  (* [comment removed for export] *)
  Definition bix (i : Z) : nat := if (i <? 12)%Z then Z.to_nat (74 + i) else Z.to_nat (72 + i).

  (* [comment removed for export] *)
  Definition kn_tagv : list kentry :=
    [KWord (SA (EVar 81) 8) 4 (EVar 79); KWord (SA (EVar 81) 16) 8 (EVar 80);
     KRange (EVar 79) 32 67108864; KRange (EVar 80) 1 (2 ^ 47 - 2048);
     KRange (EVar 81) AS_STKLO (2 ^ 47 - 24); KAlign (EVar 81) 8;
     KZero (SA (EAlu ALU_SRL (EVar 81) (ELit 3)) SB) (ELit 3);
     KDisj (SA (EVar 81) 0) 24 (SA (EVar 2) (-2304)) 2544;
     KDisj (SA (EVar 8) 0) 400 (SA (EVar 81) 0) 24].

  Definition kn_bytes : list kentry :=
    [KWord (SA (EVar 80) 8) 1 (EVar 82); KWord (SA (EVar 80) 9) 1 (EVar 83);
     KWord (SA (EVar 80) 12) 1 (EVar 84); KWord (SA (EVar 80) 13) 1 (EVar 85); KWord (SA (EVar 80) 14) 1 (EVar 86);
     KWord (SA (EVar 80) 15) 1 (EVar 87); KWord (SA (EVar 80) 16) 1 (EVar 88); KWord (SA (EVar 80) 17) 1 (EVar 89);
     KWord (SA (EVar 80) 18) 1 (EVar 90); KWord (SA (EVar 80) 19) 1 (EVar 91); KWord (SA (EVar 80) 20) 1 (EVar 92);
     KWord (SA (EVar 80) 21) 1 (EVar 93); KWord (SA (EVar 80) 22) 1 (EVar 94); KWord (SA (EVar 80) 23) 1 (EVar 95);
     KWord (SA (EVar 80) 24) 1 (EVar 96); KWord (SA (EVar 80) 25) 1 (EVar 97); KWord (SA (EVar 80) 26) 1 (EVar 98);
     KWord (SA (EVar 80) 27) 1 (EVar 99); KWord (SA (EVar 80) 28) 1 (EVar 100); KWord (SA (EVar 80) 29) 1 (EVar 101);
     KWord (SA (EVar 80) 30) 1 (EVar 102); KWord (SA (EVar 80) 31) 1 (EVar 103);
     KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255; KRange (EVar 85) 0 255; KRange (EVar 86) 0 255;
     KRange (EVar 87) 0 255; KRange (EVar 88) 0 255; KRange (EVar 89) 0 255; KRange (EVar 90) 0 255; KRange (EVar 91) 0 255;
     KRange (EVar 92) 0 255; KRange (EVar 93) 0 255; KRange (EVar 94) 0 255; KRange (EVar 95) 0 255; KRange (EVar 96) 0 255;
     KRange (EVar 97) 0 255; KRange (EVar 98) 0 255; KRange (EVar 99) 0 255; KRange (EVar 100) 0 255; KRange (EVar 101) 0 255;
     KRange (EVar 102) 0 255; KRange (EVar 103) 0 255;
     KRange (EVar 104) 1 (2 ^ 47 - 2048);
     KDisj (SA (EVar 80) 0) 32 (SA (EVar 8) 0) 400;
     KDisj (SA (EVar 80) 0) 32 (SA (EVar 2) (-2304)) 2544].

  (* [comment removed for export] *)
  Definition SHX (b : nat) (c : Z) : expr := EAlu ALU_ADD (EAlu ALU_SRL (EVar b) (ELit 3)) (ELit (SB + c)).

  Definition kn_stk : list kentry :=
    [KWord (SA (EVar 2) 0) 8 (ELit 0xff00); KWord (SA (EVar 2) 8) 8 (EVar 101); KWord (SA (EVar 2) 16) 8 (EVar 100);
     KWord (SA (EVar 2) 24) 8 (EVar 103); KWord (SA (EVar 2) 32) 8 (EVar 102);
     KWord (SA (EVar 2) 40) 8 (SHX 8 37); KWord (SA (EVar 2) 48) 8 (EAlu ALU_ADD (EVar 8) (ELit 300));
     KWord (SA (EVar 2) 56) 8 (SHX 81 1); KWord (SA (EVar 2) 64) 8 (SHX 81 2);
     KWord (SA (EVar 2) 72) 8 (EAlu ALU_ADD (EVar 81) (ELit 16));
     KWord (SA (EVar 2) 80) 8 (EAlu ALU_ADD (EVar 8) (ELit 144));
     KWord (SA (EVar 2) 88) 8 (SHX 8 18);
     KWord (SA (EVar 2) 96) 8 (EVar 97); KWord (SA (EVar 2) 104) 8 (EVar 98); KWord (SA (EVar 2) 112) 8 (EVar 99);
     KWord (SA (EVar 2) 120) 8 (EVar 96); KWord (SA (EVar 2) 128) 8 (EVar 104)].

  #[local] Abbreviation MENV R FPI sz buf rest :=
    (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++ (mvals sz buf ++ rest))) (blobs_ev [bs])).

  Lemma kn_tagv_ok : forall (FPI : FPState) R M sz buf rest,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z ->
    know_ok SEGS (MENV R FPI sz buf rest) M kn_tagv.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M sz buf rest HADM (C1 & C2 & C3 & H4 & H5) Hsz. adm_facts HADM.
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4). pose proof (u64_range T). pose proof (u64_range buf).
    destruct H5 as (H5a & H5b & H5c). destruct AASF as (S1 & _).
    set (E := Env _ _). unfold base_vals, mvals, mbytes in E. unfold kn_tagv.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E M (EVar 81) T 8 4 (EVar 79) (Z_to_bv 64 sz));
        [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C2)].
    - eapply (kword_intro SEGS E M (EVar 81) T 16 8 (EVar 80) buf);
        [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact C3].
    - apply krange_intro; cbn [edenot]; ev_simpl E. destruct C2 as [Hsz' _]. rewrite u_small by lia. lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E. lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E. lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. exact Q1.
    - apply (kzero_shz_intro SEGS E M (EVar 81) T 3); [cbn [edenot]; ev_simpl E; reflexivity | exact S1 | lia | lia].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite U2. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite A8. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma data_byteW : forall M buf i, as_data_ok ceil M data len bs ->
    (bv_unsigned data <= bv_unsigned buf + i)%Z -> (bv_unsigned buf + i < bv_unsigned data + len)%Z ->
    cell SEGS M (bv_unsigned buf + i) 1 (W buf i).
  Proof using ceil data len bs.
    intros M buf i (HD & _) H1 H2. unfold cell, W, bb. apply (data_byte_cell SEGS M data len bs _ HD H1 H2).
  Qed.

  Lemma kn_bytes_ok : forall (FPI : FPState) R M sz buf rest,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z ->
    know_ok SEGS (MENV R FPI sz buf rest) M kn_bytes.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M sz buf rest HADM HTAG Hsz. adm_facts HADM.
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & _). app_facts.
    set (E := Env _ _). unfold base_vals, mvals, mbytes in E. unfold kn_bytes.
    repeat apply Forall_cons; try apply Forall_nil.
    all: try (lazymatch goal with
              | |- kentry_ok _ _ _ (KWord (SA (EVar 80) ?i) 1 (EVar ?v)) =>
                  eapply (kword_intro SEGS E _ (EVar 80) buf i 1 (EVar v));
                  [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia
                  | apply data_byteW; [exact AD|lia|lia]]
              | |- kentry_ok _ _ _ (KRange (EVar 104) _ _) =>
                  apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | |- kentry_ok _ _ _ (KRange (EVar ?v) 0 255) =>
                  apply krange_intro; cbn [edenot]; ev_simpl E; rewrite uW;
                  match goal with |- (_ <= bb ?b ?i <= _)%Z => pose proof (bb_range b i); lia end
              end).
    all: cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite ?A8, ?U2; unfold inDATA in *; lia.
  Qed.

  Lemma kn_stk_ok : forall (FPI : FPState) R M sz buf rest,
    ADM FPI R M -> stk buf M ->
    know_ok SEGS (MENV R FPI sz buf rest) M kn_stk.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M sz buf rest HADM HS. adm_facts HADM.
    destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17).
    pose proof pre_tagI as (Q1 & Q2 & Q3 & Q4). pose proof (u64_range T).
    set (E := Env _ _). unfold base_vals, mvals, mbytes in E. unfold kn_stk, SHX.
    repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with
         | |- kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?ve) =>
             eapply (kword_intro SEGS E M (EVar 2) (getr R 2) off 8 ve);
             [cbn [edenot]; ev_simpl E; reflexivity | | lia | lia | lia | lia |
              rewrite U2; unfold cell64, cell in *;
              match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with (spv - 240 + off)%Z by ring; eassumption end]
         end.
    all: cbn [edenot]; ev_simpl E; rewrite ?A8; try reflexivity.
    all: first [ apply add_lit_word; lia
               | symmetry; apply add_lit_word; lia
               | symmetry; apply sh_addr_word; first [assumption | reflexivity | lia]
               | apply sh_addr_word; first [assumption | reflexivity | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma kn_m_ok : forall (FPI : FPState) R M sz buf rest,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z ->
    know_ok SEGS (MENV R FPI sz buf rest) M (kn_tagv ++ kn_bytes).
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M sz buf rest HADM HTAG Hsz. apply know_ok_app; [eapply kn_tagv_ok; eauto | eapply kn_bytes_ok; eauto].
  Qed.
  Lemma kn_ms_ok : forall (FPI : FPState) R M sz buf rest,
    ADM FPI R M -> TAGC 0x6d414220 sz buf M -> (32 <= sz)%Z -> stk buf M ->
    know_ok SEGS (MENV R FPI sz buf rest) M (kn_tagv ++ kn_bytes ++ kn_stk).
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M sz buf rest HADM HTAG Hsz HS.
    apply know_ok_app; [eapply kn_tagv_ok; eauto |]. apply know_ok_app; [eapply kn_bytes_ok; eauto | eapply kn_stk_ok; eauto].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation adm_frame0I := (adm_frame0 ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE).
  #[local] Abbreviation curves0I := (curves0 data len A).

  Lemma rc_pre_at : forall (FPI : FPState) R M ty sz buf Cz k (offw : word),
    ADM FPI R M -> TAGC ty sz buf M -> (0 <= k <= 4)%Z -> (a <= Cz)%Z -> (Cz + 32 * k <= a + 400)%Z -> (Cz mod 8 = 0)%Z ->
    (0 < k -> exists o, Cz = a + o /\ (o = 0 \/ (o = 152 /\ k <= 3) \/ o = 304))%Z ->
    getr R 10 = buf -> getr R 11 = Z_to_bv 64 sz -> getr R 12 = offw -> getr R 13 = Z_to_bv 64 k ->
    getr R 14 = Z_to_bv 64 Cz ->
    rcurves_pre_bo SEGS as_both ceil data len bs (Z_to_bv 64 (spv - 240)) buf (Z_to_bv 64 Cz) sz offw k FPI R M.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M ty sz buf Cz k offw HADM (T1 & T2 & T3 & T4 & T5) Hk HC1 HC2 HC3 HCo H10 H11 H12 H13 H14.
    adm_facts HADM. pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _). app_facts.
    destruct AASF as (S1 & S2 & S3 & S4 & (E1 & E2 & E3 & E4) & S6 & S7).
    unfold rcurves_pre_bo, as_frame, stackish, heapish. cbv zeta. change RCURVES_DB with 2304%Z. cbn [al_abi as_both].
    rewrite !u_small by lia. destruct T2 as [Hsz _].
    split; [exact A2|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
    split; [exact H14|]. split; [exact AD|]. split; [lia|]. split; [exact T5|]. split; [exact Hk|].
    split; [intros Hk0; eapply writable_sub; [exact AWA|lia|lia|lia]|].
    split; [exact HC3|].
    split.
    { intros Hk0. destruct (HCo Hk0) as (o & -> & Ho3).
      split; [plc|]. split.
      - eapply shz_sub; [exact S2 | exact HC3 | lia | lia | lia].
      - intros i Hi.
        assert (Hin : In (o + 32 * i)%Z a2b_curve_offsets).
        { assert (Hi4 : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia.
          destruct Ho3 as [-> | [[-> Hk3] | ->]]; destruct Hi4 as [-> | [-> | [-> | ->]]]; cbn; try tauto; exfalso; lia. }
        pose proof (proj1 (Forall_forall _ _) S3 _ Hin) as Hw. cbv beta in Hw.
        replace (a + o + 32 * i + 12)%Z with (a + (o + 32 * i) + 12)%Z by lia. exact Hw. }
    split; [lia|].
    split; [exact E3|]. split; [exact E2|]. split; [exact E1|].
    split.
    { split; [lia|]. split; [apply mod16_sub; [exact P1|reflexivity]|]. eapply writable_sub; [exact AWS|lia|lia|lia]. }
    eapply shz_sub; [exact S4 | | lia | lia | lia].
    replace (spv - 240 - 96)%Z with (spv - 2544 + 276 * 8)%Z by lia. rewrite Z_mod_plus_full. exact (proj1 S4).
  Qed.

  Lemma adm_rc : forall (FPI FPI' : FPState) R R' M M' Cz k,
    ADM FPI R M -> (a <= Cz)%Z -> (0 <= k)%Z -> (Cz + 32 * k <= a + 400)%Z ->
    frame_mod M M' [(Z_to_bv 64 (spv - 240 - 2304), 2304%Z); (Z_to_bv 64 Cz, (32 * k)%Z)] ->
    regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M' /\ (forall ty sz buf, TAGC ty sz buf M -> TAGC ty sz buf M') /\ (forall buf, stk buf M -> stk buf M').
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE.
    intros FPI FPI' R R' M M' Cz k HADM H1 H2 H3 Hf Hk Hfk.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). app_facts.
    assert (Hw : rs_within [(Z_to_bv 64 (spv - 240 - 2304), 2304%Z); (Z_to_bv 64 Cz, (32 * k)%Z)] (BIG0 sp A)) by (unfold BIG0; solve_within).
    split; [|split].
    - apply (adm_frame0I FPI FPI' R R' M M' _ HADM Hf Hw).
      + solve_apart.
      + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)].
      + exact Hfk.
    - intros ty sz buf HT. eapply tagc_frame0; eauto.
    - intros buf HS. eapply stk_frame; [exact HS|exact Hf|]. solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma curves0_rc : forall M M' base k,
    curves0I M ->
    frame_mod M M' [(Z_to_bv 64 (spv - 240 - 2304), 2304%Z); (Z_to_bv 64 (a + base), (32 * k)%Z)] ->
    (0 <= k)%Z -> (0 <= base)%Z -> (base + 32 * k <= 128 \/ (144 <= base /\ base + 32 * k <= 400))%Z ->
    (forall i, (0 <= i < k)%Z -> curve_ok SEGS M' data len (a + base + 32 * i)) ->
    (forall o, In o a2b_curve_offsets ->
       (base + 32 * k <= o \/ o + 32 <= base)%Z \/ (exists i, (0 <= i < k)%Z /\ o = (base + 32 * i)%Z)) ->
    curves0I M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE.
    intros M M' base k [Hall (g8 & g16 & Hg8 & Hg16)] Hf Hk Hb Hbk Hnew Ho.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _). app_facts.
    split.
    - apply Forall_forall. intros o Hin.
      destruct (Ho o Hin) as [Hap | (i & Hi & ->)].
      + pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Hc. cbv beta in Hc.
        pose proof (offsets_bound o Hin) as (B1 & B2 & _).
        eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|]. solve_apart.
      + replace (a + (base + 32 * i))%Z with (a + base + 32 * i)%Z by lia. apply Hnew. exact Hi.
    - exists g8, g16. split; (eapply cell64_frame; [exact Hf|eassumption|lia|lia|solve_apart]).
  Qed.

  (* [comment removed for export] *)
  Lemma curves10_rc : forall M M' base k,
    curves10 M ->
    frame_mod M M' [(Z_to_bv 64 (spv - 240 - 2304), 2304%Z); (Z_to_bv 64 (a + base), (32 * k)%Z)] ->
    (0 <= k)%Z -> (0 <= base)%Z -> (base + 32 * k <= 400)%Z ->
    (forall i, (0 <= i < k)%Z -> curve_ok SEGS M' data len (a + base + 32 * i)) ->
    (forall o, In o a2b_curve_offsets ->
       (base + 32 * k <= o \/ o + 32 <= base)%Z \/ (exists i, (0 <= i < k)%Z /\ o = (base + 32 * i)%Z)) ->
    curves10 M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE.
    intros M M' base k Hall Hf Hk Hb Hbk Hnew Ho.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _). app_facts.
    apply Forall_forall. intros o Hin.
    destruct (Ho o Hin) as [Hap | (i & Hi & ->)].
    + pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Hc. cbv beta in Hc.
      pose proof (offsets_bound o Hin) as (B1 & B2 & _).
      eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|]. solve_apart.
    + replace (a + (base + 32 * i))%Z with (a + base + 32 * i)%Z by lia. apply Hnew. exact Hi.
  Qed.
End RC.
