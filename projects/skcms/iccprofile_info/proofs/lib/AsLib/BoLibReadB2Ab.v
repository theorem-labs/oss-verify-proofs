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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase BoLibDefs AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec BoLibReadA2Ba BoLibReadA2Bb BoLibReadB2Aa BoLibSpec AsLibPlace.
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

Section RBB.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z) (fs : Z) (ch : chain).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : b2a_pre_bo SEGS as_both ceil data len bs sp T B pcs fs ch FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract_as SEGS as_both ceil.
  Hypothesis Hmftc : read_mft_common_b2a_contract_as SEGS as_both ceil.
  Hypothesis Hitab : init_tables_b2a_contract_as SEGS as_both ceil.

  #[local] Abbreviation a := (bv_unsigned B).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).
  #[local] Abbreviation ADM := (adm ceil FPI0 regs0 mem0 ret data len bs sp T B fs ch).
  #[local] Abbreviation QP := (Qpost FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch).
  #[local] Abbreviation CI := (chain_inv data len B).
  #[local] Abbreviation pre_factsI := (pre_facts ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation pre_spI := (pre_sp ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_adm_okI := (kn_adm_ok ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation kn_end_okI := (kn_end_ok ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation adm_frame0I := (adm_frame0 ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE).
  #[local] Abbreviation base_valsI := (base_vals regs0 ret data len).
  #[local] Abbreviation failkI := (failk ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE).
  #[local] Abbreviation okkI := (okk ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon).

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL);
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 240)%Z) by (rewrite A2, u_small by lia; lia).

  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++
         [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
          getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
          data; Z_to_bv 64 len] ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in let HK3 := fresh "HK3" in
      pose proof (kn_adm_okI FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (kn_end_okI FPI R M extra HADM) as HK3; change (know_ok SEGS E M kn_end) in HK3;
      pose proof (know_ok_app SEGS E M kn_adm (kx ++ kn_end) HK1 (know_ok_app SEGS E M kx kn_end HK2 HK3)) as HK;
      clear HK1 HK2 HK3;
      cbv beta delta [kn_adm kn_end] in HK; cbn [app] in HK
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?R ?M0 =>
        assert (HADM1 : ADM I1 R1 M1);
        [ apply (adm_frame0I I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac pin_lit HR r H := lazymatch type of H with getr _ _ = Z_to_bv 64 ?v => pin_reg HR r (ELit v) by (cbn [edenot]; exact H) end.
  Ltac pin_add HR r Hr b Hb k :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EVar b) (ELit k))
        by (cbn [edenot]; ev_simpl E; rewrite Hb, Hr; apply add_lit_word; lia)
    end.
  Ltac pin_sh HR r Hr b Hb P k c :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EAlu ALU_SRL (EVar b) (ELit 3)) (ELit (SB + c)))
        by (cbn [edenot]; ev_simpl E; rewrite Hb, Hr; symmetry;
            apply (sh_addr_word P k); first [assumption | reflexivity | lia])
    end.
  Ltac pin_var HR r Hr v :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EVar v) by (cbn [edenot]; ev_simpl E; exact Hr)
    end.

  (* [comment removed for export] *)
  Ltac kreg Hkeep r :=
    lazymatch goal with HR : regs_ok _ _ _ |- _ =>
      rewrite (Hkeep r ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])); regv HR r; rewrite_getr;
      first [ reflexivity | assumption
            | symmetry; apply add_lit_word; lia
            | apply sh_addr_word; first [assumption | reflexivity | lia] ]
    end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition tagc (ty sz : Z) (buf : word) (M : word -> option byte) : Prop :=
    cell32 SEGS M (t + 4) ty /\ cell32 SEGS M (t + 8) sz /\ cell64 SEGS M (t + 16) buf /\
    (4 <= sz)%Z /\ inDATA data len (bv_unsigned buf) sz.

  Lemma pre_tag :
    (t mod 8 = 0)%Z /\ (ceil <= t)%Z /\ (t + 24 <= 2 ^ 47)%Z /\ (spv <= t)%Z.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). app_facts.
    repeat split; assumption.
  Qed.

  Lemma tagc_frame : forall ty sz buf M M' rs,
    tagc ty sz buf M -> frame_mod M M' rs -> apart t 24 rs -> tagc ty sz buf M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE.
    intros ty sz buf M M' rs (C1 & C2 & C3 & H4 & H5) Hf Hap.
    pose proof pre_tag as (Q1 & Q2 & Q3 & _). pose proof (u64_range T).
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]|].
    split; [eapply cell64_frame; [exact Hf|exact C3|lia|lia|eapply apart_sub; [exact Hap|lia|lia|lia]]|].
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma tagc_frame0 : forall ty sz buf M M' rs,
    tagc ty sz buf M -> frame_mod M M' rs -> rs_within rs (BIG0 sp B) -> tagc ty sz buf M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE.
    intros ty sz buf M M' rs HT Hf Hw. eapply tagc_frame; [exact HT | exact Hf |].
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & _). app_facts.
    eapply apart_within; [exact Hw|]. unfold BIG0. solve_apart.
  Qed.

  (* [comment removed for export] *)
  Definition kn_tag (tye : expr) : list kentry :=
    [KWord (SA (EVar 18) 4) 4 tye; KWord (SA (EVar 18) 8) 4 (EVar 79); KWord (SA (EVar 18) 16) 8 (EVar 80);
     KRange (EVar 79) 4 67108864; KRange (EVar 80) 1 (2 ^ 47 - 2048);
     KRange (EVar 18) AS_STKLO (2 ^ 47 - 24); KAlign (EVar 18) 8;
     KZero (SA (EAlu ALU_SRL (EVar 18) (ELit 3)) SB) (ELit 3);
     KDisj (SA (EVar 18) 0) 24 (SA (EVar 2) (-2304)) 2544;
     KDisj (SA (EVar 8) 0) 400 (SA (EVar 18) 0) 24].

  Lemma kn_tag_ok : forall (FPI : FPState) R M ty sz buf rest tye,
    ADM FPI R M -> tagc ty sz buf M -> getr R 18 = T ->
    let E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_valsI ++ ([Z_to_bv 64 sz; buf] ++ rest))) (blobs_ev [bs]) in
    edenot E tye = Z_to_bv 64 ty ->
    know_ok SEGS E M (kn_tag tye).
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE.
    intros FPI R M ty sz buf rest tye HADM (C1 & C2 & C3 & H4 & H5) A18 E Htye. adm_facts HADM.
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4). pose proof (u64_range T). pose proof (u64_range buf).
    destruct H5 as (H5a & H5b & H5c). destruct AASF as (S1 & _).
    unfold base_vals in E. unfold kn_tag.
    repeat apply Forall_cons; try apply Forall_nil.
    - eapply (kword_intro SEGS E M (EVar 18) T 4 4 tye (Z_to_bv 64 ty));
        [cbn [edenot]; ev_simpl E; exact A18 | exact Htye | lia | lia | lia | lia | exact (proj2 C1)].
    - eapply (kword_intro SEGS E M (EVar 18) T 8 4 (EVar 79) (Z_to_bv 64 sz));
        [cbn [edenot]; ev_simpl E; exact A18 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact (proj2 C2)].
    - eapply (kword_intro SEGS E M (EVar 18) T 16 8 (EVar 80) buf);
        [cbn [edenot]; ev_simpl E; exact A18 | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact C3].
    - apply krange_intro; cbn [edenot]; ev_simpl E. destruct C2 as [Hsz _]. rewrite u_small by lia. lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E. lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite A18. lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite A18. exact Q1.
    - apply (kzero_shz_intro SEGS E M (EVar 18) T 3); [cbn [edenot]; ev_simpl E; exact A18 | exact S1 | lia | lia].
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite U2, A18. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite A8, A18. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac pkg_tag HADM HTAG H18 rest kx ktac :=
    lazymatch type of HTAG with tagc ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag (ELit ty) ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_ok _ _ _ ty sz buf rest (ELit ty) HADM HTAG H18 eq_refl) | ktac])
    end.
  (* [comment removed for export] *)
  Ltac pkg_tag_e HADM HTAG H18 rest tye kx ktac :=
    lazymatch type of HTAG with tagc ?ty ?sz ?buf _ =>
      pkg HADM ([Z_to_bv 64 sz; buf] ++ rest) (kn_tag tye ++ kx)
        ltac:(apply know_ok_app; [exact (kn_tag_ok _ _ _ ty sz buf rest tye HADM HTAG H18 ltac:(cbn [edenot]; reflexivity)) | ktac])
    end.

  (* [comment removed for export] *)
  Lemma f1b : forall (FPI : FPState) R M sz buf r oc,
    ADM FPI R M -> tagc 0x6d667431 sz buf M ->
    getr R 18 = T -> getr R 19 = Z_to_bv 64 (t + 4) -> getr R 23 = Z_to_bv 64 (SB + (t + 4) / 8) ->
    getr R 24 = Z_to_bv 64 SB -> getr R 9 = Z_to_bv 64 0x6d667000 ->
    getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ CI 3 0 oc M)) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x858e8) M rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon.
    intros FPI R M sz buf r oc HADM HTAG H18 H19 H23 H24 H9 H10 Hr. adm_facts HADM.
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4).
    assert (Hr01 : exists rv, r = rv /\ (rv = 0 \/ rv = 1)%Z) by (destruct Hr as [-> | [-> _]]; eauto).
    destruct Hr01 as (rv & -> & Hrv).
    pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor).
    pin_add HR (19%bv:reg) H19 18%nat H18 4%Z. pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z.
    pin_lit HR (24%bv:reg) H24. pin_lit HR (9%bv:reg) H9.
    run_fp 40%nat [0x85e54%Z] noscr true.
    adm_now HADM HADM1. apply (okkI _ _ _ 3%Z 0%Z oc rv HADM1); [regv HR (24%bv:reg); reflexivity | regv HR (10%bv:reg); exact H10 | exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma f2b : forall (FPI : FPState) R M ty sz buf r oc,
    ADM FPI R M -> tagc ty sz buf M -> (ty = 0x6d667431 \/ ty = 0x6d667432)%Z ->
    getr R 18 = T -> getr R 19 = Z_to_bv 64 (t + 4) -> getr R 23 = Z_to_bv 64 (SB + (t + 4) / 8) ->
    getr R 24 = Z_to_bv 64 SB ->
    getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ CI 3 0 oc M)) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x85a58) M rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ty sz buf r oc HADM HTAG Hty H18 H19 H23 H24 H10 Hr. adm_facts HADM.
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4).
    assert (Hr01 : exists rv, r = rv /\ (rv = 0 \/ rv = 1)%Z) by (destruct Hr as [-> | [-> _]]; eauto).
    destruct Hr01 as (rv & -> & Hrv).
    destruct Hty as [-> | ->];
      pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor);
      pin_add HR (19%bv:reg) H19 18%nat H18 4%Z; pin_sh HR (23%bv:reg) H23 18%nat H18 T 4%Z 0%Z;
      pin_lit HR (24%bv:reg) H24;
      run_fp 30%nat [0x85e54%Z] noscr true;
      adm_now HADM HADM1; apply (okkI _ _ _ 3%Z 0%Z oc rv HADM1); (first [regv HR (24%bv:reg); reflexivity | regv HR (10%bv:reg); exact H10 | exact Hr]).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mftc_cells (oc g : Z) (M : word -> option byte) : Prop :=
    (3 <= oc <= 4)%Z /\ (2 <= g <= 255)%Z /\
    cell32 SEGS M (a + 96) 3 /\ cell32 SEGS M (a + 100) 0 /\ cell32 SEGS M (a + 396) oc /\
    (forall i, (0 <= i < 3)%Z -> cell8 SEGS M (a + 392 + i) g).

  (* [comment removed for export] *)
  Definition curves0 (M : word -> option byte) : Prop :=
    Forall (fun off => curve_ok SEGS M data len (a + off)) b2a_curve_offsets.

  Lemma curves0_frame : forall M M' rs,
    curves0 M -> frame_mod M M' rs ->
    Forall (fun off => apart (a + off) 32 rs) b2a_curve_offsets ->
    curves0 M'.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T B pcs fs ch HPRE.
    intros M M' rs Hall Hf Haps.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & _). app_facts.
    apply Forall_forall. intros o Ho.
    pose proof (proj1 (Forall_forall _ _) Hall o Ho) as Hc. pose proof (proj1 (Forall_forall _ _) Haps o Ho) as Ha.
    cbv beta in Hc, Ha. pose proof (BoLibReadB2Aa.offsets_bound o Ho) as (B1 & B2 & _).
    eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|]. eapply apart_sub; [exact Ha|lia|lia|lia].
  Qed.

  Ltac offsets_apart_tac :=
    unfold b2a_curve_offsets; repeat (apply Forall_cons; [solve_apart|]); apply Forall_nil.

  (* [comment removed for export] *)
  Lemma adm_sb : forall (FPI : FPState) R M, ADM FPI R M -> as_sb SEGS as_both M.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE.
    intros FPI R M HADM. adm_facts HADM. destruct AASF as (_ & _ & _ & _ & (Hc & _) & _).
    apply as_sb_both. pose proof (both_cells64 SEGS M Hc) as (C1 & C2 & _). split; [exact C1 | exact C2].
  Qed.

  (* [comment removed for export] *)
  Lemma mftc_pre_at : forall (FPI : FPState) R M ty sz buf,
    ADM FPI R M -> tagc ty sz buf M -> (48 <= sz)%Z -> getr R 10 = buf -> getr R 11 = B ->
    mftc_b2a_pre_as SEGS as_both ceil data len bs buf B FPI R M.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE.
    intros FPI R M ty sz buf HADM (T1 & T2 & T3 & T4 & T5a & T5b & T5c) Hsz H10 H11. adm_facts HADM.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & _). app_facts.
    destruct AASF as (S1 & S2 & _).
    unfold mftc_b2a_pre_as. cbv zeta.
    split; [exact H10|]. split; [exact H11|]. split; [exact AD|]. split; [unfold inDATA; lia|].
    split; [exact AWA|]. split; [exact P2|]. split; [unfold heapish; plc|]. split; [exact S2|].
    split; [exact P10|]. split; [exact (adm_sb FPI R M HADM)|].
    exists (Z_to_bv 64 (spv - 240)). split; [exact A2|].
    unfold as_frame, stackish. rewrite !u_small by lia.
    split; [lia|]. split; [apply mod16_sub; [exact P1|reflexivity]|]. eapply writable_sub; [exact AWS|lia|lia|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma adm_mftc : forall (FPI FPI' : FPState) R R' M M',
    ADM FPI R M ->
    frame_mod M M' [(Z_to_bv 64 (bv_unsigned (getr R 2) - 16), 16%Z); (Z_to_bv 64 (a + 96), 8%Z); (Z_to_bv 64 (a + 392), 8%Z)] ->
    regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M' /\ (forall ty sz buf, tagc ty sz buf M -> tagc ty sz buf M') /\ (curves0 M -> curves0 M').
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE.
    intros FPI FPI' R R' M M' HADM Hf Hk Hfk. adm_facts HADM. rewrite U2 in Hf.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & P13 & P14 & _). app_facts.
    assert (Hw : rs_within [(Z_to_bv 64 (spv - 240 - 16), 16%Z); (Z_to_bv 64 (a + 96), 8%Z); (Z_to_bv 64 (a + 392), 8%Z)] (BIG0 sp B))
      by (unfold BIG0; solve_within).
    split; [|split].
    - apply (adm_frame0I FPI FPI' R R' M M' _ HADM Hf Hw); [solve_apart | apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] .. | exact Hfk].
    - intros ty sz buf HT. eapply tagc_frame0; eauto.
    - intros HC. eapply curves0_frame; [exact HC | exact Hf | offsets_apart_tac].
  Qed.

  (* [comment removed for export] *)
  Lemma itab_pre_mft : forall (FPI : FPState) R M ty sz buf oc g hdr bw ite ote,
    ADM FPI R M -> tagc ty sz buf M -> (hdr <= sz)%Z -> (hdr = 48 \/ hdr = 52)%Z -> mftc_cells oc g M ->
    (bw = 1 \/ bw = 2)%Z -> (2 <= ite <= 4096)%Z -> (2 <= ote <= 4096)%Z ->
    getr R 10 = Z_to_bv 64 (bv_unsigned buf + hdr) -> getr R 11 = Z_to_bv 64 (sz - hdr) ->
    getr R 12 = Z_to_bv 64 bw -> getr R 13 = Z_to_bv 64 ite -> getr R 14 = Z_to_bv 64 ote -> getr R 15 = B ->
    itab_b2a_pre_as SEGS as_both ceil data len bs (Z_to_bv 64 (spv - 240)) (Z_to_bv 64 (bv_unsigned buf + hdr)) B
                 (sz - hdr) bw ite ote oc (repeat g 3) FPI R M.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T B pcs fs ch HPRE.
    intros FPI R M ty sz buf oc g hdr bw ite ote HADM HTAG Hhdr Hhdr2 (Hoc & Hg & C1 & C2 & C3 & Cg) Hbw Hite Hote
           H10 H11 H12 H13 H14 H15. adm_facts HADM.
    pose proof pre_factsI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & _). app_facts.
    destruct HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct AASF as (S1 & S2 & _).
    unfold itab_b2a_pre_as, as_frame, stackish, heapish. cbv zeta. change ITAB_FR with 112%Z.
    rewrite !u_small by lia.
    split; [exact A2|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
    split; [exact H14|]. split; [exact H15|]. split; [exact AD|]. split; [lia|].
    split; [unfold inDATA; lia|].
    split; [exact Hbw|]. split; [exact Hite|]. split; [exact Hote|]. split; [exact Hoc|].
    split; [reflexivity|].
    split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; lia|].
    split; [exact C1|]. split; [exact C3|].
    split; [intros i Hi; rewrite nth_repeat_lt by lia; apply Cg; lia|].
    split; [rewrite Z.add_0_r; exact AWA|]. split; [exact P2|]. split; [plc|]. split; [exact S2|].
    split; [exact P10|]. split; [exact (adm_sb FPI R M HADM)|].
    split; [lia|]. split; [apply mod16_sub; [exact P1|reflexivity]|].
    eapply writable_sub; [exact AWS|lia|lia|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma adm_itab : forall (FPI FPI' : FPState) R R' M M' oc rs,
    ADM FPI R M -> (3 <= oc <= 4)%Z ->
    (rs = [(Z_to_bv 64 (spv - 240 - 112), 112%Z)] \/
     rs = [(Z_to_bv 64 (spv - 240 - 112), 112%Z); (Z_to_bv 64 a, 96%Z); (Z_to_bv 64 (a + 248), (32 * oc)%Z); (Z_to_bv 64 (a + 376), 16%Z)]) ->
    frame_mod M M' rs -> regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    ADM FPI' R' M' /\ (forall ty sz buf, tagc ty sz buf M -> tagc ty sz buf M').
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE.
    intros FPI FPI' R R' M M' oc rs HADM Hoc Hrs Hf Hk Hfk.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _). app_facts.
    assert (Hw : rs_within rs (BIG0 sp B)) by (destruct Hrs as [-> | ->]; unfold BIG0; solve_within).
    split.
    - apply (adm_frame0I FPI FPI' R R' M M' rs HADM Hf Hw).
      + destruct Hrs as [-> | ->]; solve_apart.
      + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]. + apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)].
      + exact Hfk.
    - intros ty sz buf HT. eapply tagc_frame0; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma chain_from_itab : forall M M' oc g,
    mftc_cells oc g M -> curves0 M ->
    frame_mod M M' [(Z_to_bv 64 (spv - 240 - 112), 112%Z); (Z_to_bv 64 a, 96%Z); (Z_to_bv 64 (a + 248), (32 * oc)%Z); (Z_to_bv 64 (a + 376), 16%Z)] ->
    (forall i, (0 <= i < 3)%Z -> curve_ok SEGS M' data len (a + 32 * i)) ->
    (forall i, (0 <= i < oc)%Z -> curve_ok SEGS M' data len (a + 248 + 32 * i)) ->
    CI 3 0 oc M'.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch HPRE.
    intros M M' oc g (Hoc & Hg & C1 & C2 & C3 & Cg) Hall Hf Hin Hout.
    pose proof pre_factsI as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _). app_facts.
    assert (AP : forall lo n, (a + 96 <= lo)%Z -> (lo + n <= a + 248 \/ a + 248 + 32 * oc <= lo)%Z ->
              (lo + n <= a + 376 \/ a + 392 <= lo)%Z -> (lo + n <= a + 400)%Z -> (0 <= n)%Z ->
              apart lo n [(Z_to_bv 64 (spv - 240 - 112), 112%Z); (Z_to_bv 64 a, 96%Z); (Z_to_bv 64 (a + 248), (32 * oc)%Z); (Z_to_bv 64 (a + 376), 16%Z)]).
    { intros lo n H1 H2 H3 H4 H5. solve_apart. }
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|apply AP; lia]|].
    split; [lia|]. split; [left; reflexivity|]. split; [lia|].
    unfold b2a_curve_offsets.
    assert (X : forall i, (0 <= i < 3)%Z -> curve_ok SEGS M' data len (a + 32 * i)) by exact Hin.
    assert (Y : forall o, In o [104; 136; 168]%Z -> curve_ok SEGS M' data len (a + o)).
    { intros o Ho.
      assert (Hoin : In o b2a_curve_offsets) by (cbn in Ho |- *; tauto).
      pose proof (proj1 (Forall_forall _ _) Hall o Hoin) as Hc. cbv beta in Hc.
      assert (104 <= o /\ o + 32 <= 200)%Z by (cbn in Ho; repeat (destruct Ho as [<-|Ho]); [..|destruct Ho]; lia).
      eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|apply AP; lia]. }
    assert (W : curve_ok SEGS M' data len (a + 344)).
    { destruct (Z.eq_dec oc 4) as [->|Hne].
      - replace (a + 344)%Z with (a + 248 + 32 * 3)%Z by lia. apply Hout. lia.
      - assert (Hoin : In 344%Z b2a_curve_offsets) by (first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]).
        pose proof (proj1 (Forall_forall _ _) Hall 344%Z Hoin) as Hc. cbv beta in Hc.
        eapply curve_ok_frame; [exact Hf|exact Hc|lia|lia|apply AP; lia]. }
    repeat apply Forall_cons; try apply Forall_nil;
      first [ replace (a + 0)%Z with (a + 32 * 0)%Z by lia; apply X; lia
            | replace (a + 32)%Z with (a + 32 * 1)%Z by lia; apply X; lia
            | replace (a + 64)%Z with (a + 32 * 2)%Z by lia; apply X; lia
            | apply Y; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]
            | replace (a + 248)%Z with (a + 248 + 32 * 0)%Z by lia; apply Hout; lia
            | replace (a + 280)%Z with (a + 248 + 32 * 1)%Z by lia; apply Hout; lia
            | replace (a + 312)%Z with (a + 248 + 32 * 2)%Z by lia; apply Hout; lia
            | exact W ].
  Qed.

  (* [comment removed for export] *)
  Lemma data_byte : forall M p, as_data_ok ceil M data len bs ->
    (bv_unsigned data <= p)%Z -> (p < bv_unsigned data + len)%Z ->
    cell SEGS M p 1 (Z_to_bv 64 (bs_byte bs (p - bv_unsigned data))).
  Proof using ceil data len bs. intros M p (HD & _) H1 H2. unfold cell. apply (data_byte_cell SEGS M data len bs p HD H1 H2). Qed.

  (* [comment removed for export] *)
  Lemma f1 : forall (FPI : FPState) R M sz buf r,
    ADM FPI R M -> tagc 0x6d667431 sz buf M -> (48 <= sz)%Z ->
    getr R 18 = T -> getr R 19 = Z_to_bv 64 (t + 4) -> getr R 23 = Z_to_bv 64 (SB + (t + 4) / 8) ->
    getr R 24 = Z_to_bv 64 SB -> getr R 9 = Z_to_bv 64 0x6d667000 ->
    getr R 20 = Z_to_bv 64 (t + 8) -> getr R 25 = Z_to_bv 64 (SB + (t + 8) / 8) -> getr R 21 = buf ->
    getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ exists oc g, mftc_cells oc g M)) -> curves0 M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x858b8) M rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hitab.
    intros FPI R M sz buf r HADM HTAG Hsz H18 H19 H23 H24 H9 H20 H25 H21 H10 Hr HC0. adm_facts HADM.
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct Hr as [-> | (-> & oc & g & HMC)].
    - pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor).
      pin_lit HR (10%bv:reg) H10.
      run_fp 20%nat [0x858e8%Z] noscr true.
      adm_now HADM HADM1.
      apply (f1b _ _ _ sz buf 0%Z 0%Z HADM1); [exact HTAG | regv HR (18%bv:reg); exact H18 | regv HR (19%bv:reg); exact H19
        | regv HR (23%bv:reg); exact H23 | regv HR (24%bv:reg); exact H24 | regv HR (9%bv:reg); exact H9
        | regv HR (10%bv:reg); reflexivity | left; reflexivity].
    - pose proof HMC as (Hoc & Hg & _).
      pkg_tag HADM HTAG H18 (@nil word) [KRange (EVar 79) 48 67108864]
        ltac:(constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia | constructor]).
      pin_lit HR (10%bv:reg) H10. pin_lit HR (24%bv:reg) H24.
      pin_add HR (20%bv:reg) H20 18%nat H18 8%Z. pin_sh HR (25%bv:reg) H25 18%nat H18 T 8%Z 1%Z.
      pin_var HR (21%bv:reg) H21 80%nat.
      run_fp 40%nat [0x858e8%Z; 0x88514%Z] noscr true.
      adm_now HADM HADM1.
      eapply rt_call.
      { eapply (Hitab data len bs (Z_to_bv 64 (spv - 240)) (Z_to_bv 64 (bv_unsigned buf + 48)) B
                  (sz - 48)%Z 1%Z 256%Z 256%Z oc (repeat g 3) _ _ _ rom (Z_to_bv 64 0x858e8)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - eapply (itab_pre_mft _ _ _ 0x6d667431%Z sz buf oc g 48%Z); try first [exact HADM1 | lia].
          + exact HTAG.
          + exact HMC.
          + regv_lin HR (10%bv:reg). f_equal. lia.
          + regv_lin HR (11%bv:reg). rewrite u_small by lia. f_equal. lia.
          + regv HR (12%bv:reg). reflexivity.
          + regv HR (13%bv:reg). reflexivity.
          + regv HR (14%bv:reg). reflexivity.
          + regv HR (15%bv:reg). exact A8. }
      cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & r' & H10' & Hpost).
      change ITAB_FR with 112%Z in Hpost. rewrite (u_small (spv - 240)) in Hpost by lia.
      destruct Hpost as [[-> Hfr] | [-> (Hfr & Hin & Hout & Hgrid)]].
      + destruct (adm_itab _ FPI' _ R' _ M' oc _ HADM1 Hoc (or_introl eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f1b FPI' R' M' sz buf 0%Z 0%Z HADM'); [apply HT'; exact HTAG | kreg Hkeep (18%bv:reg) | kreg Hkeep (19%bv:reg)
          | kreg Hkeep (23%bv:reg) | kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | exact H10' | left; reflexivity].
      + destruct (adm_itab _ FPI' _ R' _ M' oc _ HADM1 Hoc (or_intror eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f1b FPI' R' M' sz buf 1%Z oc HADM'); [apply HT'; exact HTAG | kreg Hkeep (18%bv:reg) | kreg Hkeep (19%bv:reg)
          | kreg Hkeep (23%bv:reg) | kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | exact H10' | right; split; [reflexivity|]].
        eapply (chain_from_itab _ M' oc g);
          [exact HMC | exact HC0 | exact Hfr | exact Hin | exact Hout].
  Qed.


  (* [comment removed for export] *)
  Lemma f2 : forall (FPI : FPState) R M sz buf r,
    ADM FPI R M -> tagc 0x6d667432 sz buf M -> (52 <= sz)%Z ->
    getr R 18 = T -> getr R 19 = Z_to_bv 64 (t + 4) -> getr R 23 = Z_to_bv 64 (SB + (t + 4) / 8) ->
    getr R 24 = Z_to_bv 64 SB ->
    getr R 20 = Z_to_bv 64 (t + 8) -> getr R 9 = Z_to_bv 64 (SB + (t + 8) / 8) -> getr R 21 = buf ->
    getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ exists oc g, mftc_cells oc g M)) -> curves0 M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x8595c) M rom) QP.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T B pcs fs ch Hret HPRE Hcanon Hitab.
    intros FPI R M sz buf r HADM HTAG Hsz H18 H19 H23 H24 H20 H9 H21 H10 Hr HC0. adm_facts HADM.
    pose proof pre_tag as (Q1 & Q2 & Q3 & Q4).
    pose proof HTAG as (T1 & T2 & T3 & T4 & T5a & T5b & T5c). pose proof (u64_range buf).
    destruct Hr as [-> | (-> & oc & g & HMC)].
    - pkg_tag HADM HTAG H18 (@nil word) (@nil kentry) ltac:(constructor).
      pin_lit HR (10%bv:reg) H10.
      run_fp 20%nat [0x85a58%Z] noscr true.
      adm_now HADM HADM1.
      apply (f2b _ _ _ 0x6d667432%Z sz buf 0%Z 0%Z HADM1); [exact HTAG | right; reflexivity | regv HR (18%bv:reg); exact H18 | regv HR (19%bv:reg); exact H19
        | regv HR (23%bv:reg); exact H23 | regv HR (24%bv:reg); exact H24
        | regv HR (10%bv:reg); reflexivity | left; reflexivity].
    - pose proof HMC as (Hoc & Hg & _).
      set (b48 := bs_byte bs (bv_unsigned buf + 48 - bv_unsigned data)).
      set (b49 := bs_byte bs (bv_unsigned buf + 49 - bv_unsigned data)).
      set (b50 := bs_byte bs (bv_unsigned buf + 50 - bv_unsigned data)).
      set (b51 := bs_byte bs (bv_unsigned buf + 51 - bv_unsigned data)).
      pose proof (bs_byte_range bs (bv_unsigned buf + 48 - bv_unsigned data)) as R48.
      pose proof (bs_byte_range bs (bv_unsigned buf + 49 - bv_unsigned data)) as R49.
      pose proof (bs_byte_range bs (bv_unsigned buf + 50 - bv_unsigned data)) as R50.
      pose proof (bs_byte_range bs (bv_unsigned buf + 51 - bv_unsigned data)) as R51.
      fold b48 in R48. fold b49 in R49. fold b50 in R50. fold b51 in R51.
      pkg_tag HADM HTAG H18 [Z_to_bv 64 b48; Z_to_bv 64 b49; Z_to_bv 64 b50; Z_to_bv 64 b51]
        [KRange (EVar 79) 52 67108864;
         KWord (SA (EVar 80) 48) 1 (EVar 81); KWord (SA (EVar 80) 49) 1 (EVar 82);
         KWord (SA (EVar 80) 50) 1 (EVar 83); KWord (SA (EVar 80) 51) 1 (EVar 84);
         KRange (EVar 81) 0 255; KRange (EVar 82) 0 255; KRange (EVar 83) 0 255; KRange (EVar 84) 0 255]
        ltac:(repeat apply Forall_cons; try apply Forall_nil;
              [ apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | eapply (kword_intro SEGS E _ (EVar 80) buf 48 1 (EVar 81)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | eapply (kword_intro SEGS E _ (EVar 80) buf 49 1 (EVar 82)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | eapply (kword_intro SEGS E _ (EVar 80) buf 50 1 (EVar 83)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | eapply (kword_intro SEGS E _ (EVar 80) buf 51 1 (EVar 84)); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | apply data_byte; [exact AD|lia|lia]]
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia
              | apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia ]).
      pin_lit HR (10%bv:reg) H10. pin_lit HR (24%bv:reg) H24.
      pin_add HR (20%bv:reg) H20 18%nat H18 8%Z. pin_sh HR (9%bv:reg) H9 18%nat H18 T 8%Z 1%Z.
      pin_var HR (21%bv:reg) H21 80%nat.
      run_fp 80%nat [0x85a58%Z; 0x88514%Z] noscr true.
      branch_case as Hc1.
      { adm_now HADM HADM1.
        apply (f2b _ _ _ 0x6d667432%Z sz buf 0%Z 0%Z HADM1); [exact HTAG | right; reflexivity | regv HR (18%bv:reg); exact H18 | regv HR (19%bv:reg); exact H19
          | regv HR (23%bv:reg); exact H23 | regv HR (24%bv:reg); reflexivity
          | regv HR (10%bv:reg); reflexivity | left; reflexivity]. }
      br_simpl_in E Hc1. apply (mft2_check b48 b49 R48 R49) in Hc1.
      run_fp 60%nat [0x85a58%Z; 0x88514%Z] noscr true.
      branch_case as Hc2.
      { adm_now HADM HADM1.
        apply (f2b _ _ _ 0x6d667432%Z sz buf 0%Z 0%Z HADM1); [exact HTAG | right; reflexivity | regv HR (18%bv:reg); exact H18 | regv HR (19%bv:reg); exact H19
          | regv HR (23%bv:reg); exact H23 | regv HR (24%bv:reg); reflexivity
          | regv HR (10%bv:reg); reflexivity | left; reflexivity]. }
      br_simpl_in E Hc2. apply (mft2_check b50 b51 R50 R51) in Hc2.
      run_fp 60%nat [0x85a58%Z; 0x88514%Z] noscr true.
      adm_now HADM HADM1.
      eapply rt_call.
      { eapply (Hitab data len bs (Z_to_bv 64 (spv - 240)) (Z_to_bv 64 (bv_unsigned buf + 52)) B
                  (sz - 52)%Z 2%Z (256 * b48 + b49)%Z (256 * b50 + b51)%Z oc (repeat g 3) _ _ _ rom (Z_to_bv 64 0x85a58)).
        - regv HR (1%bv:reg). reflexivity.
        - apply ret_ok_even. rewrite u_small by lia. reflexivity.
        - eapply (itab_pre_mft _ _ _ 0x6d667432%Z sz buf oc g 52%Z); try first [exact HADM1 | lia].
          + exact HTAG.
          + exact HMC.
          + regv_lin HR (10%bv:reg). f_equal. lia.
          + regv_lin HR (11%bv:reg). rewrite u_small by lia. f_equal. lia.
          + regv HR (12%bv:reg). reflexivity.
          + regv HR (13%bv:reg). exact (mft2_val b48 b49 R48 R49).
          + regv HR (14%bv:reg). exact (mft2_val b50 b51 R50 R51).
          + regv HR (15%bv:reg). exact A8. }
      cbv beta. intros FPI' R' M' (Hkeep & Hfkeep & r' & H10' & Hpost).
      change ITAB_FR with 112%Z in Hpost. rewrite (u_small (spv - 240)) in Hpost by lia.
      destruct Hpost as [[-> Hfr] | [-> (Hfr & Hin & Hout & Hgrid)]].
      + destruct (adm_itab _ FPI' _ R' _ M' oc _ HADM1 Hoc (or_introl eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f2b FPI' R' M' 0x6d667432%Z sz buf 0%Z 0%Z HADM'); [apply HT'; exact HTAG | right; reflexivity | kreg Hkeep (18%bv:reg) | kreg Hkeep (19%bv:reg)
          | kreg Hkeep (23%bv:reg) | kreg Hkeep (24%bv:reg) | exact H10' | left; reflexivity].
      + destruct (adm_itab _ FPI' _ R' _ M' oc _ HADM1 Hoc (or_intror eq_refl) Hfr Hkeep Hfkeep) as [HADM' HT'].
        apply (f2b FPI' R' M' 0x6d667432%Z sz buf 1%Z oc HADM'); [apply HT'; exact HTAG | right; reflexivity | kreg Hkeep (18%bv:reg) | kreg Hkeep (19%bv:reg)
          | kreg Hkeep (23%bv:reg) | kreg Hkeep (24%bv:reg) | exact H10' | right; split; [reflexivity|]].
        eapply (chain_from_itab _ M' oc g);
          [exact HMC | exact HC0 | exact Hfr | exact Hin | exact Hout].
  Qed.
End RBB.
