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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec BoLibParseDefs AsLibKit BoLibParseF BoLibParseE BoLibParseD BoLibSpec BoLibCicp AsLibPlace.
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

Section C3.
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
    split; [regv HR (2%bv:reg); first [exact H2 | cbn [edenot]; ev_simpl_goal; exact H2 | rewrite ?H2; try reflexivity; flia]|];
    split; [regv HR (3%bv:reg); exact H3|];
    split; [regv HR (4%bv:reg); exact H4|];
    split; [regv HR (21%bv:reg); first [exact H21 | reflexivity]|];
    split; [regv HR (22%bv:reg); first [exact H22 | reflexivity]|];
    frk HF HFK.

  (* [comment removed for export] *)
  Variables (psz tc h964 : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.
  Hypothesis R964 : (h964 = 0 \/ h964 = 1)%Z.

  #[local] Notation DFACTS := (DFACTS sp data prio P len psz tc h964).

  (* [comment removed for export] *)
  Definition XT (Mx : word -> option byte) (k sig : Z) : Prop :=
    tag_ok SEGS Mx data len (bv_unsigned sp - 384 + k) /\
    cell32 SEGS Mx (bv_unsigned sp - 384 + k) sig /\
    (exists ty, cell32 SEGS Mx (bv_unsigned sp - 384 + k + 4) ty).

  Lemma XT_frame : forall Mx My rs k sig,
    XT Mx k sig -> frame_mod Mx My rs -> (0 <= k <= 232)%Z -> apart (bv_unsigned sp - 384 + k) 24 rs -> XT My k sig.
  Proof.
    intros Mx My rs k sig (X1 & X2 & [ty X3]) Hf Hk Hap. pose proof (u64_range sp).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    split; [eapply tag_ok_frame; [exact Hf | exact X1 | flia | flia | exact Hap]|].
    split; [eapply cell32_frame; [exact Hf | exact X2 | flia | flia | eapply apart_sub; [exact Hap | flia | flia | flia]]|].
    exists ty. eapply cell32_frame; [exact Hf | exact X3 | flia | flia | eapply apart_sub; [exact Hap | flia | flia | flia]].
  Qed.

  Lemma XT_intro : forall Mx k sig,
    (0 <= k <= 232)%Z ->
    tag_ok SEGS Mx data len (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384 + k))) /\
    cell32 SEGS Mx (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384 + k))) sig /\
    (exists ty, cell32 SEGS Mx (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384 + k)) + 4) ty) -> XT Mx k sig.
  Proof.
    intros Mx k sig Hk H. pose proof (u64_range sp).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    rewrite !u_small_frame in H by flia. exact H.
  Qed.

  Lemma XT_tag : forall Mx My k sig j, In j tag_offsets -> (k = 136 \/ k = 112 \/ k = 88)%Z -> (k + 24 <= j \/ j + 24 <= k)%Z ->
    XT Mx k sig ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + j), 24%Z)] ->
    XT My k sig.
  Proof.
    intros Mx My k sig j Hj Hk Hkj X Hfr. pose proof (u64_range sp).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    assert (Hj' : (j = 232 \/ j = 208 \/ j = 184 \/ j = 160 \/ j = 136 \/ j = 112 \/ j = 88)%Z) by (cbn in Hj; clear -Hj; intuition flia).
    eapply XT_frame; [exact X | exact Hfr | flia | rewrite u_small by flia; solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xyz_pre_at : forall Mx (FP : FPState) R s1 s2 s3,
    frame_mod mem Mx BIG ->
    XT Mx 136 s1 -> XT Mx 112 s2 -> XT Mx 88 s3 ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384) ->
    getr R 10 = Z_to_bv 64 (bv_unsigned sp - 384 + 136) ->
    getr R 11 = Z_to_bv 64 (bv_unsigned sp - 384 + 112) ->
    getr R 12 = Z_to_bv 64 (bv_unsigned sp - 384 + 88) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned P + 120) ->
    xyzd50_pre_bo SEGS as_both ceil data len bs (Z_to_bv 64 (bv_unsigned sp - 384))
      (Z_to_bv 64 (bv_unsigned sp - 384 + 136)) (Z_to_bv 64 (bv_unsigned sp - 384 + 112))
      (Z_to_bv 64 (bv_unsigned sp - 384 + 88)) (Z_to_bv 64 (bv_unsigned P + 120)) FP R Mx.
  Proof.
    intros Mx FP R s1 s2 s3 Hf X1 X2 X3 R2 R10 R11 R12 R13.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hf) as (HD & HEV & Hhdr & Hfsw & _ & _ & _ & WP & HshP & WS & HshS & Hsb & _).
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & Htp & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2, Hdar.
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    assert (XK : forall k s, XT Mx k s -> (k = 136 \/ k = 112 \/ k = 88)%Z ->
              xtag_ok_bo SEGS ceil Mx data len (Z_to_bv 64 (bv_unsigned sp - 384)) (Z_to_bv 64 (bv_unsigned sp - 384 + k))).
    { intros k s (T1 & T2 & T3) Hk. unfold xtag_ok_bo. cbv zeta. unfold XYZD50_DB.
      rewrite !u_small by flia.
      assert (K8 : ((bv_unsigned sp - 384 + k) mod 8 = 0)%Z).
      { destruct Hk as [-> | [-> | ->]];
        [ replace (bv_unsigned sp - 384 + 136)%Z with (bv_unsigned sp + (-248))%Z by flia
        | replace (bv_unsigned sp - 384 + 112)%Z with (bv_unsigned sp + (-272))%Z by flia
        | replace (bv_unsigned sp - 384 + 88)%Z with (bv_unsigned sp + (-296))%Z by flia ];
        (apply mod_add_multiple; [flia | apply (mod_down _ 8 2); [flia|flia|exact N6] | reflexivity]). }
      split; [exact T3|]. split; [exact T1|]. split; [exact K8|]. split; [unfold stackish; flia|].
      split; [eapply (shz_sub Mx _ _ _ _ HshS); [exact K8 | flia | flia | flia]|]. left; flia. }
    unfold xyzd50_pre_bo. cbv zeta. unfold XYZD50_DB.
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [exact HD|].
    split; [apply (XK 136%Z s1 X1); flia|]. split; [apply (XK 112%Z s2 X2); flia|]. split; [apply (XK 88%Z s3 X3); flia|].
    rewrite !u_small by flia.
    split; [eapply writable_sub; [exact WP | flia | flia | flia]|].
    split; [apply mod_add_multiple; [flia | apply (mod_down _ 4 16); [flia|flia|exact Hpal] | reflexivity]|].
    split; [unfold heapish; plc|].
    assert (M8 : ((bv_unsigned P + 120) mod 8 = 0)%Z) by (apply mod_add_multiple; [flia | apply (mod_down _ 8 8); [flia|flia|exact Hpal] | reflexivity]).
    split; [rewrite M8, Z.sub_0_r; eapply (shz_sub Mx _ _ _ _ HshP); [exact M8 | flia | flia | flia]|].
    split; [flia|].
    split; [exact Hsb|].
    unfold as_frame, stackish. rewrite !u_small by flia. split; [flia|]. split.
    - apply (mod_down _ 16 1); [flia|flia|]. change (16*1)%Z with 16%Z. apply mod_sub_multiple; [flia | exact N6 | reflexivity].
    - eapply writable_sub; [exact WS | flia | flia | flia].
  Qed.

  Lemma after_xyz : forall Mx My,
    DFACTS 0 raw Mx -> SAVED Mx -> frame_mod mem Mx BIG -> FSOK Mx ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - XYZD50_DB), XYZD50_DB);
                     (Z_to_bv 64 (bv_unsigned P + 120), 36%Z)] ->
    SAVED My /\ frame_mod mem My BIG /\ FSOK My /\ DFACTS 0 raw My.
  Proof.
    intros Mx My HF HS Hf [HFa [hh HFb]] Hfr.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
    pose proof (u64_range sp). pose proof (u64_range P). unfold XYZD50_DB in *.
    rewrite !u_small_frame in Hfr by flia.
    split; [eapply (SAVED_frame FP0 regs sp); [exact HS | exact Hfr | solve_apart | flia]|].
    split. { eapply frame_BIG_app; [exact Hf | exact Hfr |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
             first [ apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); flia
                   | apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); flia ]. }
    split. { split.
             - eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HFa | flia | unfold FS_SIZE; flia |].
               intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
             - exists hh. unfold FS_HINT0. eapply acellw_frame; [exact Hfr | exact HFb | flia | flia | solve_apart]. }
    eapply (DFACTS_frame4 ceil regs mem ret sp data prio P len fs bs ch HE); [exact HF | exact Hfr | solve_apart | solve_apart | solve_apart | solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis H19 : getr R 19 = data.
    Hypothesis H20 : getr R 20 = Z_to_bv 64 len.
    Hypothesis HF : DFACTS 0 raw M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_C3 : list kentry :=
      [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47 - 384); KWr (SA (EVar 2) (-2544)) 2928;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122)].

    Lemma kn_C3_ok : know_ok SEGS E M kn_C3.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
      pose proof (u64_range sp). pose proof (u64_range P). unfold FS_SIZE in *.
      destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4).
      unfold kn_C3, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kalign_intro; [flia|]. cbn. apply (mod_down _ 16 1); [flia|flia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by flia. apply mod_sub_multiple; [flia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. flia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2544) 2928); cbn; try flia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2544)%Z with (bv_unsigned sp - 2928)%Z by flia. exact S4.
      - apply kalign_intro; [flia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. flia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try flia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | flia | flia].
    Qed.

    Ltac call_gettag sig k retw Mx0 Hfx C0 C20 H21 HR2z :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        let HR2c := fresh "HR2c" in
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 384 + k)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by flia; reflexivity
          | apply (gettag_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 k _ psz tc Hfx C0 C20 Htags);
            [ regv HR (21%bv:reg); exact H21
            | regv HR (10%bv:reg); exact H21
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite ?HR2z; rewrite ?u_small by flia; apply (f_equal (Z_to_bv 64)); flia
            | exact HR2c
            | flia | cbn; tauto ] ]
        | cbv beta ]
      end.

    (* [comment removed for export] *)
    Ltac to_D HR HFr H2 H3 H4 H21 H22 HFK HSx Hfx HFSx HFx H19 H20 :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockD_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Ha2b Hb2a Hcicp Husable psz tc h964 0 raw
                 Htags R964 ltac:(flia) I R2 M2);
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HSx | exact Hfx | exact HFSx
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | exact HFx ]
      end.

    Lemma blockC3_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82534) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_C3_ok as HK. unfold kn_C3 in HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as (_ & _ & _ & F3 & _ & F5 & _).
      run_fp 30%nat [0x8125c%Z] noscr false.
      call_gettag 0x7258595a%Z 136%Z (Z_to_bv 64 0x82548) M Hf F3 F5 H21 HR2z.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag1). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 136, 24%Z)].
      assert (Hf1 : frame_mod mem mq1 BIG) by (eapply frame_BIG_app; [exact Hf | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 136); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 136 ltac:(cbn; tauto) HS Hfr) as HS1.
      pose proof (DFACTS_tag ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ _ _ 136%Z ltac:(cbn; tauto) HF Hfr) as HF1.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 136 ltac:(cbn; tauto) HFS Hfr) as HFS1.
      clear Hfr F3 F5.
      destruct Hr01 as [-> | ->].
      { add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by flia; flia).
        run_fp 10%nat [0x825b0%Z] noscr false. to_D HR HFr H2 H3 H4 H21 H22 HFK HS1 Hf1 HFS1 HF1 H19 H20. }
      pose proof (XT_intro mq1 136%Z _ ltac:(flia) (Htag1 eq_refl)) as X1. clear Htag1.
      add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by flia; flia).
      (* [comment removed for export] *)
      pose proof HF1 as HF'. destruct HF' as (_ & _ & _ & F3 & _ & F5 & _).
      run_fp 30%nat [0x8125c%Z] noscr false.
      call_gettag 0x6758595a%Z 112%Z (Z_to_bv 64 0x82560) mq1 Hf1 F3 F5 H21 HR2z.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 112, 24%Z)].
      assert (Hf2 : frame_mod mem mq2 BIG) by (eapply frame_BIG_app; [exact Hf1 | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 112); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 112 ltac:(cbn; tauto) HS1 Hfr) as HS2.
      pose proof (DFACTS_tag ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ _ _ 112%Z ltac:(cbn; tauto) HF1 Hfr) as HF2.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 112 ltac:(cbn; tauto) HFS1 Hfr) as HFS2.
      pose proof (XT_tag _ _ 136 _ 112 ltac:(cbn; tauto) ltac:(flia) ltac:(flia) X1 Hfr) as X1b.
      clear Hfr F3 F5 X1 HF1 HS1 Hf1 HFS1.
      destruct Hr02 as [-> | ->].
      { add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by flia; flia).
        run_fp 10%nat [0x825b0%Z] noscr false. to_D HR HFr H2 H3 H4 H21 H22 HFK HS2 Hf2 HFS2 HF2 H19 H20. }
      pose proof (XT_intro mq2 112%Z _ ltac:(flia) (Htag2 eq_refl)) as X2. clear Htag2.
      add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by flia; flia).
      (* [comment removed for export] *)
      pose proof HF2 as HF'. destruct HF' as (_ & _ & _ & F3 & _ & F5 & _).
      run_fp 30%nat [0x8125c%Z] noscr false.
      call_gettag 0x6258595a%Z 88%Z (Z_to_bv 64 0x82578) mq2 Hf2 F3 F5 H21 HR2z.
      intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & r3 & Hr3 & Hr03 & Htag3). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ3. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 88, 24%Z)].
      assert (Hf3 : frame_mod mem mq3 BIG) by (eapply frame_BIG_app; [exact Hf2 | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 88); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 88 ltac:(cbn; tauto) HS2 Hfr) as HS3.
      pose proof (DFACTS_tag ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ _ _ 88%Z ltac:(cbn; tauto) HF2 Hfr) as HF3.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 88 ltac:(cbn; tauto) HFS2 Hfr) as HFS3.
      pose proof (XT_tag _ _ 136 _ 88 ltac:(cbn; tauto) ltac:(flia) ltac:(flia) X1b Hfr) as X1c.
      pose proof (XT_tag _ _ 112 _ 88 ltac:(cbn; tauto) ltac:(flia) ltac:(flia) X2 Hfr) as X2c.
      clear Hfr F3 F5 X1b X2 HF2 HS2 Hf2 HFS2.
      destruct Hr03 as [-> | ->].
      { add_krange (EVar 202) 0%Z 0%Z by (rewrite Hr3; rewrite u_small by flia; flia).
        run_fp 10%nat [0x825b0%Z] noscr false. to_D HR HFr H2 H3 H4 H21 H22 HFK HS3 Hf3 HFS3 HF3 H19 H20. }
      pose proof (XT_intro mq3 88%Z _ ltac:(flia) (Htag3 eq_refl)) as X3. clear Htag3.
      add_krange (EVar 202) 1%Z 1%Z by (rewrite Hr3; rewrite u_small by flia; flia).
      (* [comment removed for export] *)
      run_fp 30%nat [0x83c78%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hxyz data len bs (Z_to_bv 64 (bv_unsigned sp - 384)) (Z_to_bv 64 (bv_unsigned sp - 384 + 136))
                    (Z_to_bv 64 (bv_unsigned sp - 384 + 112)) (Z_to_bv 64 (bv_unsigned sp - 384 + 88))
                    (Z_to_bv 64 (bv_unsigned P + 120)) I R1 Mx ro (Z_to_bv 64 0x82590));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by flia; reflexivity
          | apply (xyz_pre_at Mx I R1 _ _ _ Hf3 X1c X2c X3);
            [ regv HR (2%bv:reg); exact HR2z
            | regv_lin HR (10%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); flia
            | regv_lin HR (11%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); flia
            | regv_lin HR (12%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); flia
            | regv_lin HR (13%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); flia ] ]
        | cbv beta ]
      end.
      intros FQ4 rq4 mq4 (Hkeep & Hfkeep & Hfr & r4 & Hr4 & Hr04).
      destruct (after_xyz mq3 mq4 HF3 HS3 Hf3 HFS3 Hfr) as (HS4 & Hf4 & HFS4 & HF4).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE mq4 Hf4) as (_ & _ & _ & _ & _ & _ & _ & WP4 & HshP4 & _).
      destruct WP4 as (_ & _ & _ & W4).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ4. clear Hkeep Hfkeep Hfr.
      clear HK.
      lazymatch type of HR with regs_ok ?E2 _ _ =>
        assert (HK : know_ok SEGS E2 mq4
          [KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976; KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122)]);
        [ unfold know_ok; repeat (apply Forall_cons); [..|apply Forall_nil];
          [ apply kalign_intro; [flia|]; cbn; ev_simpl E2; rewrite H21; exact Hpal
          | apply krange_intro; cbn; ev_simpl E2; rewrite H21; flia
          | apply (kwr_intro SEGS E2 mq4 (EVar 21) P 0 976); cbn; ev_simpl E2; rewrite ?H21; try flia; try reflexivity; rewrite Z.add_0_r; exact W4
          | eapply (kzero_shz_intro SEGS E2 mq4 (EVar 21) P 122); [cbn; ev_simpl E2; exact H21 | exact HshP4 | flia | flia] ]
        |] end.
      destruct Hr04 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 266) 0%Z 0%Z by (rewrite Hr4; rewrite u_small by flia; flia).
        run_fp 10%nat [0x82190%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
          apply (fail_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M');
          [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS4 | exact Hf4 | exact HFS4 ]
        end. }
      add_krange (EVar 266) 1%Z 1%Z by (rewrite Hr4; rewrite u_small by flia; flia).
      run_fp 15%nat [0x825b0%Z] noscr true.
      lazymatch goal with EQM : ?Mn = mem_denot _ mq4 _ |- _ =>
        assert (Hfr2 : frame_mod mq4 Mn [(Z_to_bv 64 (bv_unsigned P + 965), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 965, 1%Z)]); clear EQM end.
      kcell HK (EVar 21) 965%Z 1%nat (ELit 1) C965.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockD_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Ha2b Hb2a Hcicp Husable psz tc h964 1 raw
                 Htags R964 ltac:(flia) I R2 M2) end.
      - common HR HFr H2 H3 H4 H21 H22 HFK.
      - eapply (SAVED_frame FP0 regs sp); [exact HS4 | exact Hfr2 | solve_apart | flia].
      - eapply frame_BIG_app; [exact Hf4 | exact Hfr2 |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); flia.
      - destruct HFS4 as [HFa [hh1 HFb]]. split.
        + eapply (fs_flags0_but_frame fs [] []); [exact Hfr2 | exact HFa | flia | unfold FS_SIZE; flia |].
          intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
        + exists hh1. unfold FS_HINT0. eapply acellw_frame; [exact Hfr2 | exact HFb | flia | flia | solve_apart].
      - regv HR (19%bv:reg). exact H19.
      - regv HR (20%bv:reg). exact H20.
      - eapply (DFACTS_set965 ceil regs mem ret sp data prio P len fs bs ch HE); [exact HF4 | exact Hfr2 | split; [flia | unfold LibDefs.cell; exact C965]].
    Qed.
  End Run.

End C3.
