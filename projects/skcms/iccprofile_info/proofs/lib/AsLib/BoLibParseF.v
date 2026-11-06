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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsSpec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec BoLibParseDefs AsLibKit BoLibSpec AsLibPlace.
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

(* [comment removed for export] *)
Ltac flia := first [ clia | lia ].

Section F.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.

  (* [comment removed for export] *)
  Ltac nlia := first [ (pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NUMP; cbv zeta in NUMP; clear - NUMP; lia) ].
  Ltac flia ::= first [ nlia | clia | lia ].
  Ltac sc_lia ::= first [ nlia | clia | dlia ].
  Ltac plc ::= first [ nlia | clia | place_app | (split; plc) | (app_facts; clia) | lia ].
  Hypothesis Hgettag : gettag_contract_as SEGS as_both ceil.
  Hypothesis Hcicp : cicp_contract_bo SEGS as_both ceil.
  Hypothesis Husable : usable_contract_bo SEGS as_both ceil.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len fs bs).
  #[local] Notation BIG := (BIG sp P fs).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).
  #[local] Notation FSOK := (FSOK fs).

  (* [comment removed for export] *)
  Ltac common HR HF H2 H3 H4 H21 H22 HFK :=
    split; [regv HR (2%bv:reg); first [exact H2 | cbn [edenot]; ev_simpl_goal; exact H2 | rewrite ?H2; try reflexivity; flia]|];
    split; [regv HR (3%bv:reg); exact H3|];
    split; [regv HR (4%bv:reg); exact H4|];
    split; [regv HR (21%bv:reg); first [exact H21 | reflexivity]|];
    split; [regv HR (22%bv:reg); first [exact H22 | reflexivity]|];
    frk HF HFK.

  (* [comment removed for export] *)
  Ltac fail_now HR HF H2 H3 H4 H21 H22 HFK HS Hf HFS :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M');
      [ common HR HF H2 H3 H4 H21 H22 HFK | exact HS | exact Hf | exact HFS ]
    end.

  (* [comment removed for export] *)
  Ltac fsok_over Hfr HFS HFSn Mq :=
    let HF1 := fresh "HF1" in let hh := fresh "hh" in let HF2 := fresh "HF2" in
    destruct HFS as [HF1 [hh HF2]];
    assert (HFSn : FSOK Mq);
    [ split;
      [ eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HF1 | flia | unfold FS_SIZE; flia |];
        intros i Hi Hni; split; [exact Hni|]; unfold FS_FLAGS0_LEN in Hi; unfold FS_FLAGS0, FS_SIZE in *; rewrite ?u_small by flia; solve_apart
      | exists hh; unfold FS_HINT0, FS_SIZE in *; eapply acellw_frame; [exact Hfr | exact HF2 | flia | flia | rewrite ?u_small by flia; solve_apart] ]
    | clear HF1 HF2 ].

  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (h965 : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis Hpo : parsed_ok SEGS M data len bs (bv_unsigned P).
    Hypothesis C965 : cell8 SEGS M (bv_unsigned P + 965) h965.
    Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [data; Z_to_bv 64 len])) (blobs_ev [bs]).

    Definition kn_F : list kentry :=
      [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47 - 384); KWr (SA (EVar 2) (-2544)) 2928;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KRange (EVar 64) 1 (2 ^ 47 - 16); KRange (EVar 65) 0 (2 ^ 26);
       KDisj (SA (EVar 21) 0) 976 ZSH ZSHL; KDisj (SA (EVar 21) 0) 976 ZIMG ZIMGL; KDisj (SA (EVar 21) 0) 976 (SA (EVar 2) (-2544)) 2928].

    Lemma kn_F_ok : know_ok SEGS E M kn_F.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data). unfold FS_SIZE in *.
      destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4).
      unfold kn_F, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kalign_intro; [flia|]. cbn.
        apply (mod_down _ 16 1); [flia|flia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by flia. apply mod_sub_multiple; [flia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. flia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2544) 2928); cbn; try flia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2544)%Z with (bv_unsigned sp - 2928)%Z by flia. exact S4.
      - apply kalign_intro; [flia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. flia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try flia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | flia | flia].
      - apply krange_intro; cbn. flia.
      - apply krange_intro; cbn. rewrite u_small by flia. flia.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
    Qed.

    (* [comment removed for export] *)
    Ltac call_usable HR HF H2 H21 Hfx Hpox C965x :=
      lazymatch goal with
      | |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        let HR2c := fresh "HR2u" in
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (regv HR (2%bv:reg); rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity);
        let WP := fresh "WP" in let HshP := fresh "HshP" in let WS := fresh "WS" in let Hsb := fresh "Hsb" in
        pose proof (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hfx) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _ & Hsb & _);
        let C964 := fresh "C964" in let R964 := fresh "R964" in let C966 := fresh "C966" in let R966 := fresh "R966" in
        pose proof Hpox as (? & ? & ? & ? & _ & _ & _ & _ & _ & C964 & R964 & C966 & R966 & _);
        let Hpal := fresh "Hpal" in
        pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _);
        eapply rt_call;
        [ eapply (Husable P (Z_to_bv 64 (bv_unsigned sp - 384)) I R1 Mx ro (Z_to_bv 64 0x827a0));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by flia; reflexivity
          | unfold usable_pre_bo; cbv zeta;
            split; [exact HR2c|];
            split; [regv HR (10%bv:reg); first [exact H21 | rewrite_getr; reflexivity]|];
            split; [apply (mod_down _ 8 8); [flia|flia|exact Hpal]|];
            split; [unfold heapish; plc|];
            split; [exact HshP|];
            split; [eexists; split; [exact C964| exact R964]|];
            split; [eexists; split; [exact C965x| exact R965]|];
            split; [eexists; split; [exact C966| exact R966]|];
            split; [exact Hsb|];
            unfold as_frame, stackish; rewrite !u_small by flia;
            split; [flia|]; split; [let NU := fresh "NU" in pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU; cbv zeta in NU;
                                  apply mod_sub_multiple; [flia | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 NU)))))) | reflexivity] |];
            eapply writable_sub; [exact WS|flia|flia|flia] ]
        | cbv beta; clear HR2c WP HshP WS Hsb C964 R964 C966 R966 Hpal ]
      end.

    Lemma blockF_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82754) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof Hpo as Hpo'.
      destruct Hpo' as (psz & tc & htrc & hasA2B & C0 & C8 & C20 & Htags & _).
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_F_ok as HK. unfold kn_F in HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      run_fp 20%nat [0x8125c%Z] noscr false.
      (* [comment removed for export] *)
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz 0x63696370%Z (Z_to_bv 64 (bv_unsigned sp - 384 + 208)) I R1 Mx ro (Z_to_bv 64 0x82768));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by flia; reflexivity
          | apply (gettag_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 208 _ psz tc Hf C0 C20 Htags);
            [ regv HR (21%bv:reg); exact H21
            | regv HR (10%bv:reg); exact H21
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); flia
            | exact HR2c
            | flia | cbn; tauto ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag).
      rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 208, 24%Z)].
      assert (Hf1 : frame_mod mem mq1 BIG) by (eapply frame_BIG_app; [exact Hf | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 208); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 208 ltac:(cbn; tauto) HS Hfr) as HS1.
      pose proof (parsed_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 208 ltac:(cbn; tauto) Hpo Hfr) as Hpo1.
      pose proof (cell8_P_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 208 965 h965 ltac:(cbn; tauto) ltac:(flia) C965 Hfr) as C965a.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 208 ltac:(cbn; tauto) HFS Hfr) as HFS1.
      clear Hfr.
      (* [comment removed for export] *)
      Ltac finish_usable HSx Hfx HFSx Hpox C965x :=
        lazymatch goal with
        | H2 : bv_unsigned (getr R 2) = _, H3 : getr R 3 = _, H4 : getr R 4 = _, H21 : getr R 21 = P, H22 : getr R 22 = _,
          HFK : forall r, In r _ -> reg_get _ r = reg_get _ r |- _ =>
        lazymatch goal with HR : regs_ok _ _ _, HF : fregs_ok _ _ _ |- _ =>
          call_usable HR HF H2 H21 Hfx Hpox C965x;
          let FQ := fresh "FQ" in let rq := fresh "rq" in let mq := fresh "mq" in
          let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in
          let r := fresh "r" in let Hr := fresh "Hr" in let Hr01 := fresh "Hr01" in
          intros FQ rq mq (Hkeep & Hfkeep & Hfr & r & Hr & Hr01);
          rewrite !u_small in Hfr by flia;
          unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep;
          after_call Hkeep Hfkeep FQ; clear Hkeep Hfkeep;
          lazymatch goal with HK : know_ok _ _ _ _ |- _ => kframe HK Hfr [(SA (EVar 2) (-16), 16%Z)] end;
          run_fp 5%nat [0x82194%Z] noscr false;
          lazymatch goal with HR' : regs_ok _ _ ?R2, HF' : fregs_ok _ _ _ |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
            apply (exit_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R2 M2 r);
            [ common HR' HF' H2 H3 H4 H21 H22 HFK
            | regv HR' (11%bv:reg); exact Hr
            | exact Hr01
            | eapply (SAVED_frame FP0 regs sp); [exact HSx | exact Hfr | solve_apart | flia]
            | eapply frame_BIG_app; [exact Hfx | exact Hfr |]; apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
              apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); flia
            | let HFSn := fresh "HFSn" in fsok_over Hfr HFSx HFSn mq; exact HFSn
            | intros _; eapply parsed_ok_frame; [exact Hfr | exact Hpox | flia | flia | solve_apart | solve_apart | solve_apart] ]
          end
        end end.
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 76) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by flia; flia).
        run_fp 10%nat [0x87418%Z] noscr false.
        finish_usable HS1 Hf1 HFS1 Hpo1 C965a. }
      (* [comment removed for export] *)
      destruct (Htag eq_refl) as ((sz & buf & Csz & Cbuf & Hsz4 & HinT) & Csig & (ty & Cty)).
      rewrite !u_small_frame in Csz, Cbuf, Csig, Cty by flia.
      add_krange (EVar 76) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by flia; flia).
      run_fp 10%nat [0x87228%Z] noscr false.
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2, Hdar.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (regv HR (2%bv:reg); exact HR2z);
        destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hf1) as (HD1 & _ & _ & _ & _ & _ & _ & WP1 & HshP1 & WS1 & HshS1 & Hsb1 & _);
        eapply rt_call;
        [ eapply (Hcicp data len bs (Z_to_bv 64 (bv_unsigned sp - 384)) (Z_to_bv 64 (bv_unsigned sp - 384 + 208)) (Z_to_bv 64 (bv_unsigned P + 960)) I R1 Mx ro (Z_to_bv 64 0x82778));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by flia; reflexivity
          | unfold cicp_pre_bo; cbv zeta; rewrite !u_small by flia;
            split; [exact HR2c|];
            split; [regv_lin HR (10%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); flia|];
            split; [regv_lin HR (11%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); flia|];
            split; [exact HD1|];
            split; [exists ty; exact Cty|];
            split; [exists sz, buf; split; [exact Csz|]; split; [exact Cbuf|]; split; [exact Hsz4 | exact HinT]|];
            split; [replace (bv_unsigned sp - 384 + 208)%Z with (bv_unsigned sp - 176)%Z by flia; apply mod_sub_multiple; [flia| apply (mod_down _ 8 2); [flia|flia|exact N6] |reflexivity]|];
            split; [unfold stackish; flia|];
            split; [eapply (shz_sub Mx _ _ _ _ HshS1); [replace (bv_unsigned sp - 384 + 208)%Z with (bv_unsigned sp - 176)%Z by flia; apply mod_sub_multiple; [flia| apply (mod_down _ 8 2); [flia|flia|exact N6] |reflexivity] | flia | flia | flia]|];
            split; [flia|];
            split; [eapply writable_sub; [exact WP1|flia|flia|flia]|];
            split; [apply mod_add_multiple; [flia | apply (mod_down _ 8 8); [flia|flia|exact Hpal] | reflexivity]|];
            split; [unfold heapish; plc|];
            split; [eapply (shz_sub Mx _ _ _ _ HshP1); [apply mod_add_multiple; [flia | apply (mod_down _ 8 8); [flia|flia|exact Hpal] | reflexivity] | flia | flia | flia]|];
            split; [flia|];
            split; [exact Hsb1|];
            unfold as_frame, stackish; rewrite !u_small by flia;
            split; [flia|]; split; [apply mod_sub_multiple; [flia | exact N6 | reflexivity]|];
            eapply writable_sub; [exact WS1|flia|flia|flia] ]
        | cbv beta ]
      end.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr2 & r2 & Hr2 & Hr02).
      rewrite !u_small in Hfr2 by flia.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      kframe HK Hfr2 [(SA (EVar 2) (-16), 16%Z); (SA (EVar 21) 960, 4%Z)].
      assert (Hf2 : frame_mod mem mq2 BIG).
      { eapply frame_BIG_app; [exact Hf1 | exact Hfr2 |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
        [apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); flia | apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); flia]. }
      assert (HS2 : SAVED mq2) by (eapply (SAVED_frame FP0 regs sp); [exact HS1 | exact Hfr2 | solve_apart | flia]).
      fsok_over Hfr2 HFS1 HFS2 mq2.
      assert (Hpo2 : parsed_ok SEGS mq2 data len bs (bv_unsigned P))
        by (eapply parsed_ok_frame; [exact Hfr2 | exact Hpo1 | flia | flia | solve_apart | solve_apart | solve_apart]).
      assert (C965b : cell8 SEGS mq2 (bv_unsigned P + 965) h965) by (eapply cell8_frame; [exact Hfr2 | exact C965a | flia | flia | solve_apart]).
      clear Hfr2 HS1 Hf1 Hpo1 C965a HD1 WP1 HshP1 WS1 HshS1 Hsb1.
      destruct Hr02 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 140) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by flia; flia).
        run_fp 10%nat [0x82190%Z] noscr false.
        fail_now HR HF H2 H3 H4 H21 H22 HFK HS2 Hf2 HFS2. }
      add_krange (EVar 140) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by flia; flia).
      (* [comment removed for export] *)
      run_fp 20%nat [0x87418%Z] noscr true.
      lazymatch goal with EQM : ?Mn = mem_denot _ mq2 _ |- _ =>
        assert (Hfr3 : frame_mod mq2 Mn [(Z_to_bv 64 (bv_unsigned P + 968), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 968, 1%Z)]); clear EQM HLF end.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?Mn _) _ =>
        assert (Hf3 : frame_mod mem Mn BIG) by
          (eapply frame_BIG_app; [exact Hf2 | exact Hfr3 |]; apply bincl_of; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
           apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); flia);
        assert (HS3 : SAVED Mn) by (eapply (SAVED_frame FP0 regs sp); [exact HS2 | exact Hfr3 | solve_apart | flia]);
        fsok_over Hfr3 HFS2 HFS3 Mn;
        assert (Hpo3 : parsed_ok SEGS Mn data len bs (bv_unsigned P))
          by (eapply parsed_ok_frame; [exact Hfr3 | exact Hpo2 | flia | flia | solve_apart | solve_apart | solve_apart]);
        assert (C965c : cell8 SEGS Mn (bv_unsigned P + 965) h965) by (eapply cell8_frame; [exact Hfr3 | exact C965b | flia | flia | solve_apart]);
        finish_usable HS3 Hf3 HFS3 Hpo3 C965c
      end.
    Qed.
  End Run.
End F.
