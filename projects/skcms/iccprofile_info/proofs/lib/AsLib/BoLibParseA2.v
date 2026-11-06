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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec LibWP2Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec BoLibParseDefs AsLibKit BoLibParseF BoLibParseE BoLibParseD BoLibParseC3 BoLibParseC2 BoLibParseC1 BoLibParseB AsLibCurveSpec BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
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
(* [comment removed for export] *)
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

Section A2.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hgettag : gettag_contract_as SEGS as_both ceil.
  Hypothesis Hrc : read_curve_contract_as SEGS as_both ceil.
  Hypothesis Hmc : imemcpy32_contract SEGS as_both ceil.
  Hypothesis Hxyz : xyzd50_contract_bo SEGS as_both ceil.
  Hypothesis Ha2b : read_a2b_contract_bo SEGS as_both ceil.
  Hypothesis Hb2a : read_b2a_contract_bo SEGS as_both ceil.
  Hypothesis Hcicp : cicp_contract_bo SEGS as_both ceil.
  Hypothesis Husable : usable_contract_bo SEGS as_both ceil.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len fs bs).
  #[local] Notation BIG := (BIG sp P fs).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).
  #[local] Notation FSOK := (FSOK fs).

  Ltac common HR HF H2 H3 H4 H21 H22 HFK :=
    split; [regv HR (2%bv:reg); first [exact H2 | cbn [edenot]; ev_simpl_goal; exact H2 | rewrite ?H2; try reflexivity; lia]|];
    split; [regv HR (3%bv:reg); exact H3|];
    split; [regv HR (4%bv:reg); exact H4|];
    split; [regv HR (21%bv:reg); first [exact H21 | reflexivity]|];
    split; [regv HR (22%bv:reg); first [exact H22 | reflexivity]|];
    frk HF HFK.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw wpcs wdcs w80 w40 w48 w56 w64 : word).
  Hypothesis Htc : (0 <= tc < 2 ^ 32)%Z.
  Hypothesis Hpsz : (132 + 12 * tc <= psz <= len)%Z.

  #[local] Notation ZFACTS := (ZFACTS sp data prio P psz tc raw).

  Variable M : word -> option byte.
  Hypothesis HS : SAVED M.
  Hypothesis Hf : frame_mod mem M BIG.
  Hypothesis HFS : FSOK M.
  Hypothesis HF : ZFACTS M.
  Hypothesis HXp : cell64 SEGS M (bv_unsigned sp - 352) wpcs.
  Hypothesis HXd : cell64 SEGS M (bv_unsigned sp - 360) wdcs.
  Hypothesis HX80 : cell64 SEGS M (bv_unsigned sp - 304) w80.
  Hypothesis HX40 : cell64 SEGS M (bv_unsigned sp - 344) w40.
  Hypothesis HX48 : cell64 SEGS M (bv_unsigned sp - 336) w48.
  Hypothesis HX56 : cell64 SEGS M (bv_unsigned sp - 328) w56.
  Hypothesis HX64 : cell64 SEGS M (bv_unsigned sp - 320) w64.

  (* [comment removed for export] *)
  Definition AREGS (Rc : bvmap 5 word) : Prop :=
    (bv_unsigned (getr Rc 15) = psz)%Z /\ (bv_unsigned (getr Rc 12) = tc)%Z /\
    ((bv_unsigned (getr Rc 9) = 0)%Z <-> tc = 0%Z) /\ getr Rc 19 = data /\ getr Rc 20 = Z_to_bv 64 len.

  Ltac fail_here HR HFr HC :=
    let HC' := fresh "HCx" in
    pose proof HC as HC'; destruct HC' as (?H2 & ?H3 & ?H4 & ?H21 & ?H22 & ?HFK);
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M');
      [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS | exact Hf | exact HFS ]
    end.

  Lemma ro_none : forall i, (0x20cf8 <= i < 0x20f00)%Z -> M (Z_to_bv 64 i) = None.
  Proof.
    intros i Hi. destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
    apply (Hro 0x20cf8%Z 0x20f00%Z i); [cbn; tauto | exact Hi].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Setup.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [Z_to_bv 64 tc])) (blobs_ev [bs]).

    Definition kn_s (lo18 hi18 : Z) : list kentry :=
      [KRange (EVar 9) lo18 hi18; KRange (EVar 64) 0 (2^32 - 1); KRange (EVar 19) 1 (2 ^ 47 - 16)].

    Lemma kn_s_ok : forall lo18 hi18, (lo18 <= bv_unsigned (getr Rc 9) <= hi18)%Z -> know_ok SEGS E M (kn_s lo18 hi18).
    Proof.
      intros lo18 hi18 H18. destruct HA as (A11 & A12 & A18 & A19 & A20).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      unfold kn_s, know_ok. repeat (apply Forall_cons); [..|apply Forall_nil];
        apply krange_intro; cbn; rewrite ?A19, ?u_small by lia; lia.
    Qed.

    Lemma setup_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x821e0) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof HA as HA'. destruct HA' as (A11 & A12 & A18 & A19 & A20).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      pose proof (u64_range data) as Rd. pose proof (u64_range (getr Rc 9)) as R18.
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      destruct (Z.eq_dec tc 0) as [Htc0 | Htc0].
      - (* [comment removed for export] *)
        pose proof (kn_s_ok 0 0 ltac:(lia)) as HK.
        run_fp 10%nat [0x82328%Z] noscr false.
        assert (Htags : tags_ok len bs tc psz) by (apply tags_ok_intro; [lia | lia | lia | intros j Hj; exfalso; lia]).
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (blockC1_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hrc Hmc Hxyz Ha2b Hb2a Hcicp Husable psz tc raw Htags I R2 M wpcs wdcs)
        end;
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS | exact Hf | exact HFS
        | regv HR (19%bv:reg); exact A19
        | regv HR (20%bv:reg); exact A20
        | exact HF | exact HXp | exact HXd ].
      - (* [comment removed for export] *)
        pose proof (kn_s_ok 1 (2^64 - 1) ltac:(lia)) as HK.
        pin_reg HR (12%bv:reg) (EVar 64) by (rewrite (HR (12%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E;
           rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rc 12)), A12; reflexivity).
        add_krange (EVar 64) 1%Z (2^32 - 1)%Z by (rewrite u_small by lia; lia).
        run_fp 20%nat [0x82214%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (blockB_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hrc Hmc Hxyz Ha2b Hb2a Hcicp Husable psz tc raw wpcs wdcs
                   ltac:(lia) Hpsz M HS Hf HFS HF HXp HXd I R2)
        end.
        unfold INV.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]].
        + lia.
        + regv_lin HR (17%bv:reg). rewrite A19, u_small by lia. lia.
        + regv_lin HR (10%bv:reg). rewrite A19, u_small by lia. lia.
        + regv HR (6%bv:reg). rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite (u_small 1), (u_small tc) by lia.
          destruct (Z.ltb_spec tc 1); [exfalso; lia|]. rewrite alu_add. unfold v_add. rewrite (u_small tc), (u_small 0), u_small by lia. lia.
        + regv HR (15%bv:reg). exact A11.
        + regv HR (7%bv:reg). reflexivity.
        + regv HR (16%bv:reg). reflexivity.
        + regv_lin HR (5%bv:reg). rewrite A19, Z_to_bv_unsigned, bv_wrap64_mod.
          match goal with |- (?x mod _ = _)%Z => replace x with ((2 ^ 64 - 133 - bv_unsigned data) + (-1) * 2 ^ 64)%Z by lia end.
          rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
        + regv HR (19%bv:reg). exact A19.
        + regv HR (20%bv:reg). exact A20.
        + common HR HFr H2 H3 H4 H21 H22 HFK.
        + intros j Hj. exfalso. lia.
    Qed.
  End Setup.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section StageZ.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [w40; w48; w56; w64])) (blobs_ev [bs]).

    Lemma kn_z_ok : know_ok SEGS E M
      [KImg 0x20cf8 0x20f00; KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47 - 384);
       KWord (SA (EVar 2) 40) 8 (EVar 64); KWord (SA (EVar 2) 48) 8 (EVar 65);
       KWord (SA (EVar 2) 56) 8 (EVar 66); KWord (SA (EVar 2) 64) 8 (EVar 67)].
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK). pose proof (u64_range sp).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kimg_intro; [lia | lia | exact ro_none].
      - apply krange_intro; cbn. rewrite H2. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr Rc 2) 40 8 (EVar 64) w40); cbn; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 40)%Z with (bv_unsigned sp - 344)%Z by lia. exact HX40.
      - eapply (kword_intro SEGS E M (EVar 2) (getr Rc 2) 48 8 (EVar 65) w48); cbn; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 48)%Z with (bv_unsigned sp - 336)%Z by lia. exact HX48.
      - eapply (kword_intro SEGS E M (EVar 2) (getr Rc 2) 56 8 (EVar 66) w56); cbn; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 56)%Z with (bv_unsigned sp - 328)%Z by lia. exact HX56.
      - eapply (kword_intro SEGS E M (EVar 2) (getr Rc 2) 64 8 (EVar 67) w64); cbn; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 64)%Z with (bv_unsigned sp - 320)%Z by lia. exact HX64.
    Qed.

    Lemma stageZ_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x82138) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof HA as HA'. destruct HA' as (A11 & A12 & A18 & A19 & A20).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU. pose proof (u64_range sp).
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pose proof kn_z_ok as HK.
      run_fp 30%nat [0x821e0%Z; 0x82190%Z] noscr false.
      branch_case as Habs;
        run_fp 10%nat [0x821e0%Z; 0x82190%Z] noscr false;
        branch_case as Hok.
      { lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x821e0) _ _) _ => apply (setup_run I R2) end.
        - common HR HFr H2 H3 H4 H21 H22 HFK.
        - unfold AREGS.
              split; [regv HR (15%bv:reg); exact A11|].
              split; [regv HR (12%bv:reg); exact A12|].
              split; [regv HR (9%bv:reg); exact A18|].
              split; [regv HR (19%bv:reg); exact A19|].
              regv HR (20%bv:reg); exact A20. }
      { fail_here HR HFr HC. }
      { lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x821e0) _ _) _ => apply (setup_run I R2) end.
        - common HR HFr H2 H3 H4 H21 H22 HFK.
        - unfold AREGS.
              split; [regv HR (15%bv:reg); exact A11|].
              split; [regv HR (12%bv:reg); exact A12|].
              split; [regv HR (9%bv:reg); exact A18|].
              split; [regv HR (19%bv:reg); exact A19|].
              regv HR (20%bv:reg); exact A20. }
      { fail_here HR HFr HC. }

    Qed.
  End StageZ.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section StageY.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [w80])) (blobs_ev [bs]).

    Lemma kn_y_ok : know_ok SEGS E M [KImg 0x20cf8 0x20f00; KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47 - 384); KWord (SA (EVar 2) 80) 8 (EVar 64)].
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK). pose proof (u64_range sp).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kimg_intro; [lia | lia | exact ro_none].
      - apply krange_intro; cbn. rewrite H2. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr Rc 2) 80 8 (EVar 64) w80); cbn; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 80)%Z with (bv_unsigned sp - 304)%Z by lia. exact HX80.
    Qed.

    Lemma stageY_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x820ec) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof HA as HA'. destruct HA' as (A11 & A12 & A18 & A19 & A20).
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pose proof kn_y_ok as HK.
      run_fp 30%nat [0x82138%Z; 0x82190%Z] noscr false.
      branch_case as Habs;
        run_fp 10%nat [0x82138%Z; 0x82190%Z] noscr false;
        branch_case as Hok;
        first
          [ lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x82138) _ _) _ => apply (stageZ_run I R2) end;
            [ common HR HFr H2 H3 H4 H21 H22 HFK
            | unfold AREGS;
              split; [regv HR (15%bv:reg); exact A11|];
              split; [regv HR (12%bv:reg); exact A12|];
              split; [regv HR (9%bv:reg); exact A18|];
              split; [regv HR (19%bv:reg); exact A19|];
              regv HR (20%bv:reg); exact A20 ]
          | fail_here HR HFr HC ].
    Qed.
  End StageY.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section StageX.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev [bs]).

    Lemma kn_x_ok : know_ok SEGS E M [KImg 0x20cf8 0x20f00].
    Proof.
      unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      apply kimg_intro; [lia | lia | exact ro_none].
    Qed.

    Lemma stageX_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x82094) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof HA as HA'. destruct HA' as (A11 & A12 & A18 & A19 & A20).
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pose proof kn_x_ok as HK.
      run_fp 30%nat [0x820ec%Z; 0x82190%Z] noscr false.
      branch_case as Habs;
        run_fp 10%nat [0x820ec%Z; 0x82190%Z] noscr false;
        branch_case as Hok;
        first
          [ lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x820ec) _ _) _ => apply (stageY_run I R2) end;
            [ common HR HFr H2 H3 H4 H21 H22 HFK
            | unfold AREGS;
              split; [regv HR (15%bv:reg); exact A11|];
              split; [regv HR (12%bv:reg); exact A12|];
              split; [regv HR (9%bv:reg); exact A18|];
              split; [regv HR (19%bv:reg); exact A19|];
              regv HR (20%bv:reg); exact A20 ]
          | fail_here HR HFr HC ].
    Qed.
  End StageX.
End A2.
