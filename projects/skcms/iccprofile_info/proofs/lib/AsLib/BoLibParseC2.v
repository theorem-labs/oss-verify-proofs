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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec BoLibParseDefs AsLibKit BoLibParseF BoLibParseE BoLibParseD BoLibParseC3 AsLibCurveSpec BoLibSpec BoLibSpec BoLibCicp AsLibPlace.
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

Section C2.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hgettag : gettag_contract_as SEGS as_both ceil.
  Hypothesis Hrc : read_curve_contract_as SEGS as_both ceil.
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
  Ltac fail_now HR HF H2 H3 H4 H21 H22 HFK HS Hf HFS :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M');
      [ common HR HF H2 H3 H4 H21 H22 HFK | exact HS | exact Hf | exact HFS ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.

  #[local] Notation DFACTS := (DFACTS sp data prio P len psz tc).
  #[local] Notation XT := (XT sp data len).

  (* [comment removed for export] *)
  Definition ZH (Mx : word -> option byte) : Prop :=
    let p := bv_unsigned P in let s := bv_unsigned sp in
    cell64 SEGS Mx (s - 368) (Z_to_bv 64 2) /\ cell64 SEGS Mx (s - 376) raw /\
    cell64 SEGS Mx (s - 312) prio /\
    cell64 SEGS Mx p data /\ cell32 SEGS Mx (p + 8) psz /\ cell32 SEGS Mx (p + 20) tc.

  (* [comment removed for export] *)
  Definition ZFACTS (Mx : word -> option byte) : Prop := ZH Mx /\ zero Mx (bv_unsigned P + 24) 952.

  Lemma ZH_frame : forall Mx My rs,
    ZH Mx -> frame_mod Mx My rs -> apart (bv_unsigned sp - 384) 80 rs -> apart (bv_unsigned P) 24 rs -> ZH My.
  Proof.
    intros Mx My rs (F1 & F2 & F4 & F5 & F6 & F7) Hf As Ap.
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    unfold ZH. cbv zeta.
    split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F4 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F5 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F6 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    eapply cell32_frame; [exact Hf | exact F7 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]].
  Qed.

  Lemma ZFACTS_tag : forall Mx My (k : Z), In k tag_offsets ->
    ZFACTS Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + k), 24%Z)] -> ZFACTS My.
  Proof.
    intros Mx My k Hk [HZ Hz] Hfr. pose proof (u64_range sp). pose proof (u64_range P).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; clear -Hk; intuition lia).
    rewrite u_small in Hfr by lia.
    split; [eapply ZH_frame; [exact HZ | exact Hfr | solve_apart | solve_apart]|].
    eapply zero_frame; [exact Hfr | exact Hz | lia | lia | solve_apart].
  Qed.

  Lemma ZFACTS_D : forall Mx, ZFACTS Mx -> DFACTS 0 0 raw Mx /\ cell64 SEGS Mx (bv_unsigned sp - 312) prio.
  Proof.
    intros Mx ((F1 & F2 & F4 & F5 & F6 & F7) & Hz). pose proof (u64_range P).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    split; [|exact F4].
    unfold BoLibParseD.DFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
    split.
    { eapply (zero_curve_list SEGS Mx data len (bv_unsigned P + 24) 952); [exact Hz | lia | lia |].
      repeat constructor; cbn; lia. }
    split; [eapply zero_sub; [exact Hz | lia | lia]|].
    split; [replace (bv_unsigned P + 964)%Z with (bv_unsigned P + 24 + 940)%Z by lia; eapply zero_cell8; [exact Hz | lia | lia | lia | lia]|].
    split; [replace (bv_unsigned P + 965)%Z with (bv_unsigned P + 24 + 941)%Z by lia; eapply zero_cell8; [exact Hz | lia | lia | lia | lia]|].
    replace (bv_unsigned P + 966)%Z with (bv_unsigned P + 24 + 942)%Z by lia; eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma trc_D : forall My Mz,
    ZH My -> zero My (bv_unsigned P + 120) 856 ->
    curve_ok SEGS My data len (bv_unsigned P + 24) ->
    curve_ok SEGS My data len (bv_unsigned P + 56) ->
    curve_ok SEGS My data len (bv_unsigned P + 88) ->
    frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
    cell8 SEGS Mz (bv_unsigned P + 964) 1 ->
    DFACTS 1 0 raw Mz /\ cell64 SEGS Mz (bv_unsigned sp - 312) prio.
  Proof.
    intros My Mz HZ Hz C1 C2 C3 Hf C964. pose proof (u64_range P). pose proof (u64_range sp).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    pose proof (ZH_frame My Mz _ HZ Hf ltac:(solve_apart) ltac:(solve_apart)) as (F1 & F2 & F4 & F5 & F6 & F7).
    split; [|exact F4].
    unfold BoLibParseD.DFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
    split.
    { repeat constructor.
      - eapply curve_ok_frame; [exact Hf | exact C1 | lia | lia | solve_apart].
      - eapply curve_ok_frame; [exact Hf | exact C2 | lia | lia | solve_apart].
      - eapply curve_ok_frame; [exact Hf | exact C3 | lia | lia | solve_apart]. }
    split; [eapply zero_frame; [exact Hf | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]|].
    split; [exact C964|].
    split.
    - eapply cell8_frame; [exact Hf | | lia | lia | solve_apart].
      replace (bv_unsigned P + 965)%Z with (bv_unsigned P + 120 + 845)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
    - eapply cell8_frame; [exact Hf | | lia | lia | solve_apart].
      replace (bv_unsigned P + 966)%Z with (bv_unsigned P + 120 + 846)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rcurve_pre_at : forall Mx (FP : FPState) R (c sz : Z) (buf : word),
    frame_mod mem Mx BIG -> inDATA data len (bv_unsigned buf) sz -> (0 <= sz < 2 ^ 32)%Z ->
    (c = bv_unsigned P + 24 \/ c = bv_unsigned P + 56 \/ c = bv_unsigned P + 88)%Z ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384) ->
    getr R 10 = buf -> getr R 11 = Z_to_bv 64 sz -> getr R 12 = Z_to_bv 64 c -> getr R 13 = Z_to_bv 64 0 ->
    rcurve_pre_as SEGS as_both ceil data len bs (Z_to_bv 64 (bv_unsigned sp - 384)) buf (Z_to_bv 64 c) (Z_to_bv 64 0) sz FP R Mx.
  Proof.
    intros Mx FP R c sz buf Hf Hin Hsz Hc R2 R10 R11 R12 R13.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hf) as (HD & HEV & Hhdr & Hfsw & _ & _ & _ & WP & HshP & WS & HshS & Hsb & Hro).
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & Htp & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2, Hdar.
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct HEV as (Hcells & Hshb & _ & _).
    unfold rcurve_pre_as. cbv zeta. cbn [al_abi as_both]. unfold RCURVE_D. rewrite !u_small by lia.
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [exact HD|]. split; [exact Hsz|]. split; [exact Hin|].
    split; [eapply writable_sub; [exact WP | lia | lia | lia]|].
    assert (C8 : (c mod 8 = 0)%Z).
    { destruct Hc as [-> | [-> | ->]]; (apply mod_add_multiple; [lia | apply (mod_down _ 8 8); [lia|lia|exact Hpal] | reflexivity]). }
    split; [exact C8|].
    split; [unfold heapish; plc|].
    split; [replace c with (bv_unsigned P + (c - bv_unsigned P))%Z by lia; eapply (shz_sub Mx _ _ _ _ HshP); [rewrite Zplus_minus; exact C8 | lia | lia | lia]|].
    split. { replace (c + 12)%Z with (bv_unsigned P + (c - bv_unsigned P + 12))%Z by lia. apply shwz_in_P; [exact HshP | exact Hpal | lia | lia | lia]. }
    split; [lia|].
    split; [exact Hro|]. split; [exact Hshb|]. split; [exact Hcells|].
    split. { unfold as_frame, stackish. rewrite !u_small by lia. split; [lia|]. split.
             - apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
             - eapply writable_sub; [exact WS | lia | lia | lia]. }
    left. reflexivity.
  Qed.

  Lemma rcurve_frame_norm : forall Mx My (C : word),
    frame_mod Mx My ((Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - RCURVE_D), RCURVE_D) :: (C, 32%Z)
                      :: (if Z.eq_dec (bv_unsigned (Z_to_bv 64 0)) 0 then [] else [(Z_to_bv 64 0 : word, 4%Z)])) ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 384 - 2208), 2208%Z); (C, 32%Z)].
  Proof.
    intros Mx My C Hf. pose proof (u64_range sp).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    unfold RCURVE_D in Hf. rewrite (u_small 0) in Hf by lia. rewrite u_small_frame in Hf by lia. cbn [Z.eq_dec] in Hf. exact Hf.
  Qed.

  (* [comment removed for export] *)
  Lemma after_rcurve : forall Mx My (c : Z),
    (c = bv_unsigned P + 24 \/ c = bv_unsigned P + 56 \/ c = bv_unsigned P + 88)%Z ->
    SAVED Mx -> frame_mod mem Mx BIG -> FSOK Mx -> ZH Mx -> forall n, zero Mx c n -> (c + n = bv_unsigned P + 976)%Z ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 384 - 2208), 2208%Z); (Z_to_bv 64 c, 32%Z)] ->
    SAVED My /\ frame_mod mem My BIG /\ FSOK My /\ ZH My /\
    (forall c2 n2, (c + 32 <= c2)%Z -> (0 <= n2)%Z -> (c2 + n2 <= bv_unsigned P + 976)%Z -> zero My c2 n2) /\
    (forall c', curve_ok SEGS Mx data len c' -> (bv_unsigned P <= c')%Z -> (c' + 32 <= c)%Z -> curve_ok SEGS My data len c').
  Proof.
    intros Mx My c Hc HS Hf [HFa [hh HFb]] HZ n Hz Hn Hfr.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
    pose proof (u64_range sp). pose proof (u64_range P).
    split; [eapply (SAVED_frame FP0 regs sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split. { eapply frame_BIG_app; [exact Hf | exact Hfr |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
             first [ apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                   | apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia ]. }
    split. { split.
             - eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HFa | lia | unfold FS_SIZE; lia |].
               intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
             - exists hh. unfold FS_HINT0. eapply acellw_frame; [exact Hfr | exact HFb | lia | lia | solve_apart]. }
    split; [eapply ZH_frame; [exact HZ | exact Hfr | solve_apart | solve_apart]|].
    split.
    { intros c2 n2 H1 H2 H3. eapply zero_frame; [exact Hfr | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]. }
    intros c' Hc' H1 H2. eapply curve_ok_frame; [exact Hfr | exact Hc' | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma after_trc : forall My Mz,
    SAVED My -> frame_mod mem My BIG -> FSOK My -> ZH My -> zero My (bv_unsigned P + 120) 856 ->
    curve_ok SEGS My data len (bv_unsigned P + 24) ->
    curve_ok SEGS My data len (bv_unsigned P + 56) ->
    curve_ok SEGS My data len (bv_unsigned P + 88) ->
    frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
    cell8 SEGS Mz (bv_unsigned P + 964) 1 ->
    SAVED Mz /\ frame_mod mem Mz BIG /\ FSOK Mz /\ DFACTS 1 0 raw Mz /\ cell64 SEGS Mz (bv_unsigned sp - 312) prio.
  Proof.
    intros My Mz HS Hf [HFa [hh HFb]] HZ Hz C1 C2 C3 Hfr C964.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
    pose proof (u64_range sp). pose proof (u64_range P).
    split; [eapply (SAVED_frame FP0 regs sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split. { eapply frame_BIG_app; [exact Hf | exact Hfr |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
             apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia. }
    split. { split.
             - eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HFa | lia | unfold FS_SIZE; lia |].
               intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
             - exists hh. unfold FS_HINT0. eapply acellw_frame; [exact Hfr | exact HFb | lia | lia | solve_apart]. }
    eapply trc_D; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section RunB.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (s1 s2 s3 : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis H19 : getr R 19 = data.
    Hypothesis H20 : getr R 20 = Z_to_bv 64 len.
    Hypothesis HF : ZFACTS M.
    Hypothesis X1 : XT M 208 s1.
    Hypothesis X2 : XT M 184 s2.
    Hypothesis X3 : XT M 160 s3.

    Ltac call_rcurve c sz buf Hin Rsz retw Hfx H21 HR2z :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hrc data len bs (Z_to_bv 64 (bv_unsigned sp - 384)) buf (Z_to_bv 64 c) (Z_to_bv 64 0) sz I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (rcurve_pre_at Mx I R1 c sz buf Hfx Hin Rsz ltac:(lia));
            [ regv HR (2%bv:reg); exact HR2z
            | regv HR (10%bv:reg); reflexivity
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv HR (13%bv:reg); reflexivity ] ]
        | cbv beta ]
      end.

    Lemma blockC2b_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x824bc) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _).
      destruct WS as (_ & _ & _ & S4M). destruct WP as (_ & _ & _ & W4M).
      (* [comment removed for export] *)
      destruct X1 as ((sz1 & buf1 & [Rs1 Cs1] & Cb1 & Hs1 & In1) & _ & _).
      destruct X2 as ((sz2 & buf2 & [Rs2 Cs2] & Cb2 & Hs2 & In2) & _ & _).
      destruct X3 as ((sz3 & buf3 & [Rs3 Cs3] & Cb3 & Hs3 & In3) & _ & _).
      unfold cell64, cell in Cb1, Cb2, Cb3. unfold cell in Cs1, Cs2, Cs3.
      pose proof In1 as (In1a & In1b & In1c). pose proof In2 as (In2a & In2b & In2c). pose proof In3 as (In3a & In3b & In3c).
      pose proof (u64_range buf1). pose proof (u64_range buf2). pose proof (u64_range buf3).
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
                               ++ [Z_to_bv 64 sz1; buf1; Z_to_bv 64 sz2; buf2; Z_to_bv 64 sz3; buf3])) (blobs_ev [bs])).
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS E M
        [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47 - 384); KWr (SA (EVar 2) (-2544)) 2928;
         KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
         KWord (SA (EVar 2) 216) 4 (EVar 64); KWord (SA (EVar 2) 224) 8 (EVar 65);
         KWord (SA (EVar 2) 192) 4 (EVar 66); KWord (SA (EVar 2) 200) 8 (EVar 67);
         KWord (SA (EVar 2) 168) 4 (EVar 68); KWord (SA (EVar 2) 176) 8 (EVar 69);
         KRange (EVar 64) 4 (2^26); KRange (EVar 66) 4 (2^26); KRange (EVar 68) 4 (2^26);
       KDisj (SA (EVar 21) 0) 976 ZSH ZSHL; KDisj (SA (EVar 21) 0) 976 ZIMG ZIMGL; KDisj (SA (EVar 21) 0) 976 (SA (EVar 2) (-2544)) 2928]).
      { unfold know_ok.
        repeat (apply Forall_cons); [..|apply Forall_nil].
        - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
          rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
        - apply krange_intro; cbn. rewrite H2. lia.
        - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2544) 2928); cbn; try lia; try reflexivity.
          replace (bv_unsigned (getr R 2) + -2544)%Z with (bv_unsigned sp - 2928)%Z by lia. exact S4M.
        - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
        - apply krange_intro; cbn. rewrite H21. lia.
        - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4M.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 216 4 (EVar 64) (Z_to_bv 64 sz1)); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 216)%Z with (bv_unsigned sp - 384 + 208 + 8)%Z by lia. exact Cs1.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 224 8 (EVar 65) buf1); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 224)%Z with (bv_unsigned sp - 384 + 208 + 16)%Z by lia. exact Cb1.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 192 4 (EVar 66) (Z_to_bv 64 sz2)); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 192)%Z with (bv_unsigned sp - 384 + 184 + 8)%Z by lia. exact Cs2.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 200 8 (EVar 67) buf2); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 200)%Z with (bv_unsigned sp - 384 + 184 + 16)%Z by lia. exact Cb2.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 168 4 (EVar 68) (Z_to_bv 64 sz3)); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 168)%Z with (bv_unsigned sp - 384 + 160 + 8)%Z by lia. exact Cs3.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 176 8 (EVar 69) buf3); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 176)%Z with (bv_unsigned sp - 384 + 160 + 16)%Z by lia. exact Cb3.
        - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
        - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
        - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
        - kdisj_place.
        - kdisj_place.
        - kdisj_place.
      }
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as (HZ3 & Hz3).
      run_fp 30%nat [0x829d4%Z] noscr false.
      call_rcurve (bv_unsigned P + 24)%Z sz1 buf1 In1 Rs1 (Z_to_bv 64 0x824d4) Hf H21 HR2z.
      intros FQ4 rq4 mq4 (Hkeep & Hfkeep & Hfr & r4 & Hr4 & Hr04 & Hc4 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ4. clear Hkeep Hfkeep.
      apply rcurve_frame_norm in Hfr.
      kframe HK Hfr [(SA (EVar 2) (-2208), 2208%Z); (SA (EVar 21) 24, 32%Z)].
      rewrite !u_small_frame in Hc4 by lia.
      destruct (after_rcurve M mq4 (bv_unsigned P + 24) ltac:(lia) HS Hf HFS HZ3 _ Hz3 ltac:(lia) Hfr) as (HS4 & Hf4 & HFS4 & HZ4 & Hz4 & _).
      specialize (Hz4 (bv_unsigned P + 56)%Z 920%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      clear Hfr HZ3 Hz3.
      destruct Hr04 as [-> | ->].
      { add_krange (EVar 80) 0%Z 0%Z by (rewrite Hr4; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82190%Z] noscr false. fail_now HR HFr H2 H3 H4 H21 H22 HFK HS4 Hf4 HFS4. }
      specialize (Hc4 eq_refl).
      add_krange (EVar 80) 1%Z 1%Z by (rewrite Hr4; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 30%nat [0x829d4%Z] noscr false.
      call_rcurve (bv_unsigned P + 56)%Z sz2 buf2 In2 Rs2 (Z_to_bv 64 0x824f4) Hf4 H21 HR2z.
      intros FQ5 rq5 mq5 (Hkeep & Hfkeep & Hfr & r5 & Hr5 & Hr05 & Hc5 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ5. clear Hkeep Hfkeep.
      apply rcurve_frame_norm in Hfr.
      kframe HK Hfr [(SA (EVar 2) (-2208), 2208%Z); (SA (EVar 21) 56, 32%Z)].
      rewrite !u_small_frame in Hc5 by lia.
      destruct (after_rcurve mq4 mq5 (bv_unsigned P + 56) ltac:(lia) HS4 Hf4 HFS4 HZ4 _ Hz4 ltac:(lia) Hfr) as (HS5 & Hf5 & HFS5 & HZ5 & Hz5 & HK5).
      specialize (Hz5 (bv_unsigned P + 88)%Z 888%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      pose proof (HK5 _ Hc4 ltac:(lia) ltac:(lia)) as C1_5.
      clear Hfr HZ4 Hz4 HS4 Hf4 HFS4 Hc4 HK5.
      destruct Hr05 as [-> | ->].
      { add_krange (EVar 144) 0%Z 0%Z by (rewrite Hr5; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82190%Z] noscr false. fail_now HR HFr H2 H3 H4 H21 H22 HFK HS5 Hf5 HFS5. }
      specialize (Hc5 eq_refl).
      add_krange (EVar 144) 1%Z 1%Z by (rewrite Hr5; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 30%nat [0x829d4%Z] noscr false.
      call_rcurve (bv_unsigned P + 88)%Z sz3 buf3 In3 Rs3 (Z_to_bv 64 0x82514) Hf5 H21 HR2z.
      intros FQ6 rq6 mq6 (Hkeep & Hfkeep & Hfr & r6 & Hr6 & Hr06 & Hc6 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ6. clear Hkeep Hfkeep.
      apply rcurve_frame_norm in Hfr.
      kframe HK Hfr [(SA (EVar 2) (-2208), 2208%Z); (SA (EVar 21) 88, 32%Z)].
      rewrite !u_small_frame in Hc6 by lia.
      destruct (after_rcurve mq5 mq6 (bv_unsigned P + 88) ltac:(lia) HS5 Hf5 HFS5 HZ5 _ Hz5 ltac:(lia) Hfr) as (HS6 & Hf6 & HFS6 & HZ6 & Hz6 & HK6).
      specialize (Hz6 (bv_unsigned P + 120)%Z 856%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      pose proof (HK6 _ C1_5 ltac:(lia) ltac:(lia)) as C1_6.
      pose proof (HK6 _ Hc5 ltac:(lia) ltac:(lia)) as C2_6.
      clear Hfr HZ5 Hz5 HS5 Hf5 HFS5 Hc5 C1_5 HK6.
      destruct Hr06 as [-> | ->].
      { add_krange (EVar 208) 0%Z 0%Z by (rewrite Hr6; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82190%Z] noscr false. fail_now HR HFr H2 H3 H4 H21 H22 HFK HS6 Hf6 HFS6. }
      specialize (Hc6 eq_refl).
      add_krange (EVar 208) 1%Z 1%Z by (rewrite Hr6; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE mq6 Hf6) as (_ & _ & _ & _ & _ & _ & _ & WP6 & HshP6 & _).
      destruct WP6 as (_ & _ & _ & W46).
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      lazymatch type of HR with regs_ok ?E2 _ _ =>
        kn_prefix HK [KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122)];
        [ eapply (kzero_shz_intro SEGS E2 mq6 (EVar 21) P 122); [cbn; ev_simpl E2; exact H21 | exact HshP6 | lia | lia] |] end.
      run_fp 10%nat [0x82534%Z] noscr true.
      lazymatch goal with EQM : ?Mn = mem_denot _ mq6 _ |- _ =>
        assert (Hfr2 : frame_mod mq6 Mn [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 964, 1%Z)]); clear EQM end.
      kcell HK (EVar 21) 964%Z 1%nat (ELit 1) C964.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        destruct (after_trc mq6 M2 HS6 Hf6 HFS6 HZ6 Hz6 C1_6 C2_6 Hc6 Hfr2 ltac:(split; [lia | unfold LibDefs.cell; exact C964])) as (HS7 & Hf7 & HFS7 & HF7 & H56);
        apply (blockC3_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hxyz Ha2b Hb2a Hcicp Husable psz tc 1 raw
                 Htags ltac:(lia) I R2 M2) end.
      - common HR HFr H2 H3 H4 H21 H22 HFK.
      - exact HS7.
      - exact Hf7.
      - exact HFS7.
      - regv HR (19%bv:reg). exact H19.
      - regv HR (20%bv:reg). exact H20.
      - exact HF7.
    Qed.
  End RunB.

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
    Hypothesis HF : ZFACTS M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_C2 : list kentry :=
      [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2544) (2 ^ 47 - 384); KWr (SA (EVar 2) (-2544)) 2928;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KWord (SA (EVar 2) 16) 8 (ELit 2);
       KDisj (SA (EVar 21) 0) 976 ZSH ZSHL; KDisj (SA (EVar 21) 0) 976 ZIMG ZIMGL; KDisj (SA (EVar 21) 0) 976 (SA (EVar 2) (-2544)) 2928].

    Lemma kn_C2_ok : know_ok SEGS E M kn_C2.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
      pose proof (u64_range sp). pose proof (u64_range P). unfold FS_SIZE in *.
      destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4). destruct HF as ((F1 & _) & _).
      unfold kn_C2, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2544) 2928); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2544)%Z with (bv_unsigned sp - 2928)%Z by lia. exact S4.
      - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. lia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 16 8 (ELit 2) (Z_to_bv 64 2)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 16)%Z with (bv_unsigned sp - 368)%Z by lia. exact F1.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
    Qed.

    Ltac call_gettag sig k retw Mx0 Hfx C0 C20 H21 HR2z :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        let HR2c := fresh "HR2c" in
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 384 + k)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 k _ psz tc Hfx C0 C20 Htags);
            [ regv HR (21%bv:reg); exact H21
            | regv HR (10%bv:reg); exact H21
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite ?HR2z; rewrite ?u_small by lia; apply (f_equal (Z_to_bv 64)); lia
            | exact HR2c
            | lia | cbn; tauto ] ]
        | cbv beta ]
      end.

    (* [comment removed for export] *)
    Ltac to_C3 HR HFr H2 H3 H4 H21 H22 HFK HSx Hfx HFSx HFx H19 H20 :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockC3_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hxyz Ha2b Hb2a Hcicp Husable psz tc 0 raw
                 Htags ltac:(lia) I R2 M2);
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HSx | exact Hfx | exact HFSx
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | exact (proj1 (ZFACTS_D _ HFx)) ]
      end.

    Lemma blockC2_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82474) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_C2_ok as HK. unfold kn_C2 in HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as ((_ & _ & _ & F3 & _ & F5) & _).
      run_fp 30%nat [0x8125c%Z] noscr false.
      call_gettag 0x72545243%Z 208%Z (Z_to_bv 64 0x82488) M Hf F3 F5 H21 HR2z.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag1). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 208, 24%Z)].
      assert (Hf1 : frame_mod mem mq1 BIG) by (eapply frame_BIG_app; [exact Hf | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 208); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 208 ltac:(cbn; tauto) HS Hfr) as HS1.
      pose proof (ZFACTS_tag _ _ 208 ltac:(cbn; tauto) HF Hfr) as HF1.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 208 ltac:(cbn; tauto) HFS Hfr) as HFS1.
      clear Hfr F3 F5.
      destruct Hr01 as [-> | ->].
      { add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82534%Z] noscr false. to_C3 HR HFr H2 H3 H4 H21 H22 HFK HS1 Hf1 HFS1 HF1 H19 H20. }
      pose proof (XT_intro ceil regs mem ret sp data prio P len fs bs ch HE mq1 208%Z _ ltac:(lia) (Htag1 eq_refl)) as X1. clear Htag1.
      add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      pose proof HF1 as HF'. destruct HF' as ((_ & _ & _ & F3 & _ & F5) & _).
      run_fp 30%nat [0x8125c%Z] noscr false.
      call_gettag 0x67545243%Z 184%Z (Z_to_bv 64 0x824a0) mq1 Hf1 F3 F5 H21 HR2z.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 184, 24%Z)].
      assert (Hf2 : frame_mod mem mq2 BIG) by (eapply frame_BIG_app; [exact Hf1 | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 184); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 184 ltac:(cbn; tauto) HS1 Hfr) as HS2.
      pose proof (ZFACTS_tag _ _ 184 ltac:(cbn; tauto) HF1 Hfr) as HF2.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 184 ltac:(cbn; tauto) HFS1 Hfr) as HFS2.
      pose proof (XT_frame ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ X1 Hfr ltac:(lia) ltac:(rewrite u_small by lia; solve_apart)) as X1b.
      clear Hfr F3 F5 X1 HF1 HS1 Hf1 HFS1.
      destruct Hr02 as [-> | ->].
      { add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82534%Z] noscr false. to_C3 HR HFr H2 H3 H4 H21 H22 HFK HS2 Hf2 HFS2 HF2 H19 H20. }
      pose proof (XT_intro ceil regs mem ret sp data prio P len fs bs ch HE mq2 184%Z _ ltac:(lia) (Htag2 eq_refl)) as X2. clear Htag2.
      add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      pose proof HF2 as HF'. destruct HF' as ((_ & _ & _ & F3 & _ & F5) & _).
      run_fp 30%nat [0x8125c%Z] noscr false.
      call_gettag 0x62545243%Z 160%Z (Z_to_bv 64 0x824b8) mq2 Hf2 F3 F5 H21 HR2z.
      intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & r3 & Hr3 & Hr03 & Htag3). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ3. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 160, 24%Z)].
      assert (Hf3 : frame_mod mem mq3 BIG) by (eapply frame_BIG_app; [exact Hf2 | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 160); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 160 ltac:(cbn; tauto) HS2 Hfr) as HS3.
      pose proof (ZFACTS_tag _ _ 160 ltac:(cbn; tauto) HF2 Hfr) as HF3.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 160 ltac:(cbn; tauto) HFS2 Hfr) as HFS3.
      pose proof (XT_frame ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ X1b Hfr ltac:(lia) ltac:(rewrite u_small by lia; solve_apart)) as X1c.
      pose proof (XT_frame ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ X2 Hfr ltac:(lia) ltac:(rewrite u_small by lia; solve_apart)) as X2c.
      clear Hfr F3 F5 X1b X2 HF2 HS2 Hf2 HFS2.
      destruct Hr03 as [-> | ->].
      { add_krange (EVar 202) 0%Z 0%Z by (rewrite Hr3; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82534%Z] noscr false. to_C3 HR HFr H2 H3 H4 H21 H22 HFK HS3 Hf3 HFS3 HF3 H19 H20. }
      pose proof (XT_intro ceil regs mem ret sp data prio P len fs bs ch HE mq3 160%Z _ ltac:(lia) (Htag3 eq_refl)) as X3. clear Htag3.
      add_krange (EVar 202) 1%Z 1%Z by (rewrite Hr3; rewrite u_small by lia; lia).
      run_fp 5%nat [0x824bc%Z] noscr false.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
        eapply (blockC2b_run I R2 mq3);
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS3 | exact Hf3 | exact HFS3
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | exact HF3 | exact X1c | exact X2c | exact X3 ] end.
    Qed.
  End Run.
End C2.
