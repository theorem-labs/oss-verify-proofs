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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibParseDefs AsLibKit AsLibPlace.
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

Section F.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hgettag : gettag_contract_as SEGS as_asan ceil.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len fs bs).
  #[local] Notation BIG := (BIG sp P fs).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).
  #[local] Notation FSOK := (FSOK fs).

  (* [comment removed for export] *)
  Ltac common HR HF H2 H3 H4 H21 H22 HFK :=
    split; [regv HR (2%bv:reg); first [exact H2 | cbn [edenot]; ev_simpl_goal; exact H2 | rewrite ?H2; try reflexivity; lia]|];
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
  Ltac exit_with v HR HF H2 H3 H4 H21 H22 HFK HS Hf HFS :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M' v);
      [ common HR HF H2 H3 H4 H21 H22 HFK
      | regv HR (10%bv:reg); reflexivity
      | lia | exact HS | exact Hf | exact HFS | ]
    end.

  Section Tail.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (h965 : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis Hpo : parsed_ok SEGS M data len bs (bv_unsigned P).
    Hypothesis C965 : cell8 SEGS M (bv_unsigned P + 965) h965.
    Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_tail (a b c : Z) : list kentry :=
      [KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976);
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KWord (SA (EVar 21) 966) 1 (ELit a);
       KWord (SA (EVar 21) 964) 1 (ELit b);
       KWord (SA (EVar 21) 965) 1 (ELit c)].

    Lemma kn_tail_ok : forall a b,
      cell8 SEGS M (bv_unsigned P + 966) a -> cell8 SEGS M (bv_unsigned P + 964) b ->
      know_ok SEGS E M (kn_tail a b h965).
    Proof.
      intros a b [Ra Ca] [Rb Cb]. destruct C965 as [Rc Cc]. unfold cell in Ca, Cb, Cc.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & HshP & _).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
      unfold kn_tail. pose proof (u64_range P). 
      unfold know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. lia.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
      - eapply (kword_intro SEGS E M (EVar 21) P 966 1 (ELit a) (Z_to_bv 64 a)); cbn; rewrite ?H21; try lia; auto.
      - eapply (kword_intro SEGS E M (EVar 21) P 964 1 (ELit b) (Z_to_bv 64 b)); cbn; rewrite ?H21; try lia; auto.
      - eapply (kword_intro SEGS E M (EVar 21) P 965 1 (ELit h965) (Z_to_bv 64 h965)); cbn; rewrite ?H21; try lia; auto.
    Qed.

    Lemma tailF_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82504) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof Hpo as Hpo'.
      destruct Hpo' as (psz & tc & htrc & hasA2B & _ & _ & _ & _ & _ & C964 & R964 & C966 & R966 & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof (kn_tail_ok hasA2B htrc C966 C964) as HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      destruct R966 as [-> | ->]; destruct R964 as [-> | ->]; destruct R965 as [-> | ->];
        run_fp 30%nat [0x81e9c%Z] noscr false;
        first
          [ (exit_with 0%Z HR HF H2 H3 H4 H21 H22 HFK HS Hf HFS; [intros; exfalso; lia])
          | (exit_with 1%Z HR HF H2 H3 H4 H21 H22 HFK HS Hf HFS; [intros _; exact Hpo]) ].
    Qed.
  End Tail.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
      [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2528) (2 ^ 47 - 368); KWr (SA (EVar 2) (-2528)) 2896;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KRange (EVar 64) 1 (2 ^ 47 - 16); KRange (EVar 65) 0 (2 ^ 26)].

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
      - apply kalign_intro; [lia|]. cbn.
        apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2528) 2896); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2528)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4.
      - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. lia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
      - apply krange_intro; cbn. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
    Qed.

    Lemma blockF_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x823f4) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof Hpo as Hpo'.
      destruct Hpo' as (psz & tc & htrc & hasA2B & C0 & C8 & C20 & Htags & _).
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_F_ok as HK. unfold kn_F in HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      run_fp 20%nat [0x81018%Z] noscr false.
      (* [comment removed for export] *)
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz 0x63696370%Z (Z_to_bv 64 (bv_unsigned sp - 368 + 192)) I R1 Mx ro (Z_to_bv 64 0x8240c));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 192 _ psz tc Hf C0 C20 Htags);
            [ regv HR (21%bv:reg); exact H21
            | regv HR (10%bv:reg); exact H21
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); lia
            | exact HR2c
            | lia | cbn; tauto ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag).
      rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 192, 24%Z)].
      assert (Hf1 : frame_mod mem mq1 BIG) by (eapply frame_BIG_app; [exact Hf | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 192); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 ltac:(cbn; tauto) HS Hfr) as HS1.
      pose proof (parsed_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 ltac:(cbn; tauto) Hpo Hfr) as Hpo1.
      pose proof (cell8_P_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 965 h965 ltac:(cbn; tauto) ltac:(lia) C965 Hfr) as C965a.
      assert (HFS1 : FSOK mq1).
      { destruct HFS as [HF1 [hh HF2]]. split.
        - eapply (fs_flags0_but_frame fs [] [] M mq1); [exact Hfr | exact HF1 | lia | unfold FS_SIZE; lia |].
          intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0, FS_SIZE in *. rewrite u_small by lia. solve_apart.
        - exists hh. unfold FS_HINT0, FS_SIZE in *. eapply acellw_frame; [exact Hfr | exact HF2 | lia | lia | rewrite u_small by lia; solve_apart]. }
      clear Hfr.
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 76) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82504%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (tailF_run I R2 mq1 h965) end;
          [ common HR HF H2 H3 H4 H21 H22 HFK | exact HS1 | exact Hf1 | exact HFS1 | exact Hpo1 | exact C965a | exact R965 ]. }
      (* [comment removed for export] *)
      destruct (Htag eq_refl) as ((sz & buf & Csz & Cbuf & Hsz4 & Hin) & Csig & (ty & Cty)).
      rewrite !u_small_frame in Csz, Cbuf, Csig, Cty by lia.
      destruct Csz as [Rsz Csz]. destruct Cty as [Rty Cty]. unfold cell64, cell in Cbuf. unfold cell in Csz, Cty.
      destruct Hin as (In1 & In2 & In3). pose proof (u64_range buf) as Rbuf.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE mq1 Hf1) as ((Hd1 & _ & _ & Hshd1) & _).
      pose proof Hd1 as (_ & Hbs & _ & _ & _).
      add_krange (EVar 76) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      env_extend [Z_to_bv 64 ty; Z_to_bv 64 sz; buf].
      kn_prefix HK [KWord (SA (EVar 2) 196) 4 (EVar 130); KWord (SA (EVar 2) 200) 4 (EVar 131); KWord (SA (EVar 2) 208) 8 (EVar 132);
                    KRange (EVar 130) 0 (2^32 - 1); KRange (EVar 132) 1 (2 ^ 47 - 16)].
      { eapply (kword_intro SEGS _ mq1 (EVar 2) (getr R 2) 196 4 (EVar 130) (Z_to_bv 64 ty)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 196)%Z with (bv_unsigned sp - 368 + 192 + 4)%Z by lia; exact Cty. }
      { eapply (kword_intro SEGS _ mq1 (EVar 2) (getr R 2) 200 4 (EVar 131) (Z_to_bv 64 sz)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 200)%Z with (bv_unsigned sp - 368 + 192 + 8)%Z by lia; exact Csz. }
      { eapply (kword_intro SEGS _ mq1 (EVar 2) (getr R 2) 208 8 (EVar 132) buf); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 208)%Z with (bv_unsigned sp - 368 + 192 + 16)%Z by lia; exact Cbuf. }
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      { apply krange_intro; cbn; lia. }
      kn_suffix HK [KShad (EVar 64) (EVar 65) SB; KBlobD (SA (EVar 64) 0) (EVar 65) 0].
      { eapply (kshad_intro SEGS _ mq1 (EVar 64) (EVar 65) data len); [cbn; ev_simpl_goal; reflexivity | cbn; ev_simpl_goal; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd1]. }
      { cbn [kentry_ok]; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; ev_simpl_goal;
          rewrite u_small by lia; split; [lia|]; split; [exact Hbs|]; intros i Hi; rewrite Z.add_0_r;
          eapply (proj2 (proj2 (proj2 (proj2 Hd1)))); exact Hi. }
      run_fp 30%nat [0x81e98%Z; 0x82504%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hty.
      { fail_now HR HF H2 H3 H4 H21 H22 HFK HS1 Hf1 HFS1. }
      destruct (Z_lt_le_dec sz 12) as [Hsz|Hsz].
      { (* [comment removed for export] *)
        add_krange (EVar 131) 4%Z 11%Z by (rewrite u_small by lia; lia).
        run_fp 10%nat [0x81e98%Z] noscr false.
        fail_now HR HF H2 H3 H4 H21 H22 HFK HS1 Hf1 HFS1. }
      add_krange (EVar 131) 12%Z (2^26)%Z by (rewrite u_small by lia; lia).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2, Hdar.
      kn_prefix HK [KDisj (SA (EVar 21) 0) 976 (SA (EVar 132) 8) 4].
      { cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl_goal; rewrite H21; lia. }
      clear Hdar.
      run_fp 80%nat [0x82504%Z] noscr true.
      lazymatch goal with EQM : ?Mn = mem_denot _ mq1 _ |- _ =>
        assert (Hfr2 : frame_mod mq1 Mn [(Z_to_bv 64 (bv_unsigned P + 960), 4%Z); (Z_to_bv 64 (bv_unsigned P + 968), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 960, 4%Z); (SA (EVar 21) 968, 1%Z)]); clear EQM end.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (tailF_run I R2 M2 h965) end.
      - common HR HF H2 H3 H4 H21 H22 HFK.
      - eapply (SAVED_frame FP0 regs sp); [exact HS1 | exact Hfr2 | solve_apart | lia].
      - eapply frame_BIG_app; [exact Hf1 | exact Hfr2 |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia.
      - destruct HFS1 as [HF1 [hh HF2]]. split.
        + eapply (fs_flags0_but_frame fs [] []); [exact Hfr2 | exact HF1 | lia | unfold FS_SIZE; lia |].
          intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
        + exists hh. unfold FS_HINT0. eapply acellw_frame; [exact Hfr2 | exact HF2 | lia | lia | solve_apart].
      - eapply parsed_ok_frame; [exact Hfr2 | exact Hpo1 | lia | lia | solve_apart | solve_apart | solve_apart].
      - eapply cell8_frame; [exact Hfr2 | exact C965a | lia | lia | solve_apart].
      - exact R965.
    Qed.
  End Run.
End F.
