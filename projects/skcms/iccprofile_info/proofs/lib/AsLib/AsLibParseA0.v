(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec LibWP2Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibParseDefs AsLibKit AsLibParseF AsLibParseE AsLibParseD AsLibParseC3 AsLibParseC2 AsLibParseC1 AsLibParseB AsLibParseA2 AsLibParseA1 AsLibCurveSpec AsLibPlace.
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

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

Section A0.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hmemset : imemset976_contract SEGS as_asan ceil.
  Hypothesis Hgettag : gettag_contract_as SEGS as_asan ceil.
  Hypothesis Hrc : read_curve_contract_as SEGS as_asan ceil.
  Hypothesis Hmc : imemcpy32_contract SEGS as_asan ceil.
  Hypothesis Hxyz : xyzd50_contract_as SEGS as_asan ceil.
  Hypothesis Ha2b : read_a2b_contract_as SEGS as_asan ceil.
  Hypothesis Hb2a : read_b2a_contract_as SEGS as_asan ceil.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len fs bs).
  #[local] Notation BIG := (BIG sp P fs).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).
  #[local] Notation FSOK := (FSOK fs).

  (* [comment removed for export] *)
  Hypotheses (R10 : (132 <= len)%Z -> getr regs 10 = data) (R11 : getr regs 11 = Z_to_bv 64 len) (R12 : getr regs 12 = prio)
             (R13 : getr regs 13 = Z_to_bv 64 2) (R14 : getr regs 14 = P).

  Let E0 : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FP0)) ++ [])) (blobs_ev [bs]).

  Definition kn_A : list kentry :=
    [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2896) (2 ^ 47); KWr (SA (EVar 2) (-2896)) 2896;
     KAlign (EVar 14) 64; KRange (EVar 14) 1 (2 ^ 47 - 976); KWr (SA (EVar 14) 0) 976;
     KRange (EVar 11) 0 (2^26);
     KWord (SA (ELit 0) 0x9eaf0) 8 (ELit 0xa6bb8); KWord (SA (ELit 0) 0xa6bb8) 8 (ELit SB)].

  Lemma kn_A_ok : know_ok SEGS E0 mem kn_A.
  Proof.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
    destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE mem (frame_mod_refl mem BIG)) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _ & Hsb & _).
    pose proof HE as HE'. destruct HE' as (_ & _ & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data). unfold FS_SIZE in *.
    destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4).
    apply (proj1 (as_sb_asan SEGS mem)) in Hsb. destruct Hsb as [Hg Hs]. unfold cell64, LibDefs.cell in Hg, Hs.
    unfold kn_A, know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply kalign_intro; [lia|]. cbn. rewrite Hsp. exact N6.
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E0 mem (EVar 2) sp (-2896) 2896); cbn; try lia; [exact Hsp|].
      replace (bv_unsigned sp + -2896)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4.
    - apply kalign_intro; [lia|]. cbn. rewrite R14. exact Hpal.
    - apply krange_intro; cbn. rewrite R14. lia.
    - apply (kwr_intro SEGS E0 mem (EVar 14) P 0 976); cbn; try lia; [exact R14|]. rewrite Z.add_0_r. exact W4.
    - apply krange_intro; cbn. rewrite R11, u_small by lia. lia.
    - eapply (kword_intro SEGS E0 mem (ELit 0) (Z_to_bv 64 0) 0x9eaf0 8 (ELit 0xa6bb8) (Z_to_bv 64 0xa6bb8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E0 mem (ELit 0) (Z_to_bv 64 0) 0xa6bb8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
  Qed.

  (* [comment removed for export] *)
  Ltac commonA HR HF Hsp R14 HFK0 :=
    split; [regv_lin HR (2%bv:reg); rewrite Hsp, u_small by lia; lia|];
    split; [regv HR (3%bv:reg); reflexivity|];
    split; [regv HR (4%bv:reg); reflexivity|];
    split; [regv HR (21%bv:reg); exact R14|];
    split; [regv HR (22%bv:reg); reflexivity|];
    frk HF HFK0.

  Lemma blockA_run : runs_to SEGS (mkst (FP:=FP0) regs (Z_to_bv 64 0x81950) mem rom) Q.
  Proof.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _ & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _ & _ & Henv & _ & _ & Hhint & Hfl0).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2, Hdar.
    pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
    assert (HR : regs_ok E0 (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HFr : fregs_ok E0 (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    assert (HFK0 : forall r : reg, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
              reg_get (fp_regs (FPState:=FP0)) r = reg_get (fp_regs (FPState:=FP0)) r) by (intros; reflexivity).
    pose proof kn_A_ok as HK. unfold kn_A in HK.
    assert (Hf0 : frame_mod mem mem BIG) by apply frame_mod_refl.
    assert (HFS0 : FSOK mem) by (split; [exact Hfl0 | exact Hhint]).
    (* [comment removed for export] *)
    run_fp 40%nat [0x514d0%Z] noscr true.
    (* [comment removed for export] *)
    kcell HK (EVar 2) (-8)%Z 8%nat (EVar 1) K1. kcell HK (EVar 2) (-16)%Z 8%nat (EVar 8) K2.
    kcell HK (EVar 2) (-24)%Z 8%nat (EVar 9) K3. kcell HK (EVar 2) (-32)%Z 8%nat (EVar 18) K4.
    kcell HK (EVar 2) (-40)%Z 8%nat (EVar 19) K5. kcell HK (EVar 2) (-48)%Z 8%nat (EVar 20) K6.
    kcell HK (EVar 2) (-56)%Z 8%nat (EVar 21) K7. kcell HK (EVar 2) (-64)%Z 8%nat (EVar 22) K8.
    kcell HK (EVar 2) (-72)%Z 8%nat (EVar 23) K9. kcell HK (EVar 2) (-80)%Z 8%nat (EVar 24) K10.
    kcell HK (EVar 2) (-88)%Z 8%nat (EVar 25) K11. kcell HK (EVar 2) (-96)%Z 8%nat (EVar 26) K12.
    kcell HK (EVar 2) (-104)%Z 8%nat (EVar 27) K13. kcell HK (EVar 2) (-112)%Z 8%nat (EVar 40) K14.
    kcell HK (EVar 2) (-120)%Z 8%nat (EVar 41) K15. kcell HK (EVar 2) (-128)%Z 8%nat (EVar 50) K16.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      assert (HS1 : SAVED M1) by
        (unfold AsLibParseDefs.SAVED; cbv zeta;
         repeat match goal with |- _ /\ _ => split end;
         (lazymatch goal with |- cell64 _ _ (?a - ?k)%Z _ => replace (a - k)%Z with (a + - k)%Z by lia end; cbn [Z.opp]; unfold cell64, LibDefs.cell; rewrite ?Hra; assumption))
    end.
    clear K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
    lazymatch goal with EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr1 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 2) (-128), 128%Z)]))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats E2 | vm_compute; reflexivity]);
      unfold regions_denot in Hfr1; cbn [map fst snd] in Hfr1; unfold adenot in Hfr1; cbn [a_base a_off edenot] in Hfr1;
      ev_simpl_in E2 Hfr1; rewrite Hsp in Hfr1; unfold v_addi in Hfr1; clear EQM HLF
    end.
    assert (Hf1 : frame_mod mem _ BIG)
      by (eapply frame_BIG_app; [exact Hf0 | exact Hfr1 |]; apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); lia).
    assert (HFS1 : FSOK _)
      by (destruct HFS0 as [HFa [hh HFb]]; split;
          [ eapply (fs_flags0_but_frame fs [] []); [exact Hfr1 | exact HFa | lia | unfold FS_SIZE; lia |];
            intros i Hi Hni; split; [exact Hni|]; unfold FS_FLAGS0_LEN in Hi; unfold FS_FLAGS0; solve_apart
          | exists hh; unfold FS_HINT0; eapply acellw_frame; [exact Hfr1 | exact HFb | lia | lia | solve_apart] ]).
    clear Hfr1 Hf0 HFS0.
    (* [comment removed for export] *)
    lazymatch goal with
    | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hf1) as (_ & HEV1 & _ & _ & _ & _ & _ & WP1 & HshP1 & WS1 & _);
      destruct HEV1 as (Hcells1 & _);
      eapply rt_call;
      [ eapply (Hmemset P I R1 Mx ro (Z_to_bv 64 0x819c8));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | unfold imemset_pre; cbn [Z.leb al_abi as_asan];
          split; [regv HR (10%bv:reg); exact R14|];
          split; [regv HR (11%bv:reg); reflexivity|];
          split; [regv HR (12%bv:reg); reflexivity|];
          split; [exact Hpal|];
          split; [unfold heapish; plc|];
          split; [exact WP1|];
          split; [exact HshP1|];
          split; [exact Hcells1|];
          exists (Z_to_bv 64 (bv_unsigned sp - 368)); split; [regv_lin HR (2%bv:reg); rewrite Hsp; apply (f_equal (Z_to_bv 64)); lia|];
          unfold as_frame, stackish; rewrite !u_small by lia; split; [lia|]; split;
          [ apply (mod_down _ 16 1); [lia|lia|]; change (16*1)%Z with 16%Z; apply mod_sub_multiple; [lia | exact N6 | reflexivity]
          | eapply writable_sub; [exact WS1 | lia | lia | lia] ] ]
      | cbv beta ]
    end.
    intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfrm & Hzero & Ha0).
    lazymatch type of HR with regs_ok _ _ ?R1 =>
      assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (regv_lin HR (2%bv:reg); rewrite Hsp; apply (f_equal (Z_to_bv 64)); lia);
      rewrite HR2c, !u_small in Hfrm by lia; clear HR2c end.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    replace (P, 976%Z) with (Z_to_bv 64 (bv_unsigned P + 0), 976%Z) in Hfrm by (rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    kframe HK Hfrm [(SA (EVar 2) (-368 - 2208), 2208%Z); (SA (EVar 14) 0, 976%Z)].
    assert (HS2 : SAVED mq1) by (eapply (SAVED_frame FP0 regs sp); [exact HS1 | exact Hfrm | solve_apart | lia]).
    assert (Hf2 : frame_mod mem mq1 BIG)
      by (eapply frame_BIG_app; [exact Hf1 | exact Hfrm |]; apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          first [ apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                | rewrite <- (Z.add_0_r (bv_unsigned P)) || idtac; apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                | apply (in_big_P' regs mem rom ret sp data prio P len fs bs ch HE) ]).
    assert (HFS2 : FSOK mq1)
      by (destruct HFS1 as [HFa [hh HFb]]; split;
          [ eapply (fs_flags0_but_frame fs [] []); [exact Hfrm | exact HFa | lia | unfold FS_SIZE; lia |];
            intros i Hi Hni; split; [exact Hni|]; unfold FS_FLAGS0_LEN in Hi; unfold FS_FLAGS0; solve_apart
          | exists hh; unfold FS_HINT0; eapply acellw_frame; [exact Hfrm | exact HFb | lia | lia | solve_apart] ]).
    assert (Hz : zero mq1 (bv_unsigned P) 976) by (intros i Hi; apply Hzero; exact Hi).
    clear HS1 Hf1 HFS1 Hfrm Hzero.
    run_fp 10%nat (@nil Z) noscr false.
    (* [comment removed for export] *)
    branch_case as Hl132.
    { lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
        apply (fail_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M');
        [ commonA HR HFr Hsp R14 HFK0 | exact HS2 | exact Hf2 | exact HFS2 ]
      end. }
    rewrite branch_taken_Z in Hl132. cbv beta iota in Hl132. cbn [edenot] in Hl132. ev_simpl_in E0 Hl132.
    rewrite R11, !u_small in Hl132 by lia. apply Z.ltb_ge in Hl132.
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (hdr_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hrc Hmc Hxyz Ha2b Hb2a I R' M');
      [ commonA HR HFr Hsp R14 HFK0 | exact HS2 | exact Hf2 | exact HFS2 | exact Hz
      | regv HR (8%bv:reg); exact R12
      | regv HR (9%bv:reg); exact R13
      | regv HR (18%bv:reg); exact R11
      | regv HR (19%bv:reg); exact (R10 Hl132)
      | exact Hl132 ]
    end.
  Qed.
End A0.
