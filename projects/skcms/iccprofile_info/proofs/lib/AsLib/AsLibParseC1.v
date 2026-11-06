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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibParseDefs AsLibKit AsLibParseF AsLibParseE AsLibParseD AsLibParseC3 AsLibParseC2 AsLibCurveSpec AsLibPlace.
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

Section C1.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
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

  #[local] Notation ZFACTS := (ZFACTS sp data prio P len psz tc raw).
  #[local] Notation ZH := (ZH sp data prio P len psz tc raw).
  #[local] Notation DFACTS := (DFACTS sp data P len psz tc).
  #[local] Notation XT := (XT sp data len).

  (* [comment removed for export] *)
  Definition KST (Mx : word -> option byte) (o : Z) (w0 w1 w2 w3 : word) : Prop :=
    let p := bv_unsigned P in
    SAVED Mx /\ frame_mod mem Mx BIG /\ FSOK Mx /\ ZH Mx /\ zero Mx (p + o) (976 - o) /\
    curve_ok SEGS Mx data len (p + 24) /\
    cell64 SEGS Mx (p + 24) w0 /\ cell64 SEGS Mx (p + 32) w1 /\ cell64 SEGS Mx (p + 40) w2 /\ cell64 SEGS Mx (p + 48) w3 /\
    (88 <= o -> cell64 SEGS Mx (p + 56) w0 /\ cell64 SEGS Mx (p + 64) w1 /\ cell64 SEGS Mx (p + 72) w2) /\
    (120 <= o -> cell64 SEGS Mx (p + 88) w0 /\ cell64 SEGS Mx (p + 96) w1 /\ cell64 SEGS Mx (p + 104) w2).

  (* [comment removed for export] *)
  Lemma mc_pre_at : forall Mx (FP : FPState) R o w0 w1 w2 w3,
    (o = 56 \/ o = 88)%Z -> KST Mx o w0 w1 w2 w3 ->
    (bv_unsigned (getr R 2) = bv_unsigned sp - 368)%Z ->
    getr R 10 = Z_to_bv 64 (bv_unsigned P + o) -> getr R 11 = Z_to_bv 64 (bv_unsigned P + 24) -> getr R 12 = Z_to_bv 64 32 ->
    imemcpy32_pre SEGS as_asan ceil o P w0 w1 w2 w3 FP R Mx.
  Proof.
    intros Mx FP R o w0 w1 w2 w3 Ho (HS & Hf & HFS & HZ & Hz & Hc & C0 & C1 & C2 & C3 & _) R2 R10 R11 R12.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hf) as (HD & HEV & Hhdr & Hfsw & _ & _ & _ & WP & HshP & WS & HshS & Hsb & Hro).
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct HEV as (Hcells & _ & _ & _).
    unfold imemcpy32_pre. cbn [al_abi as_asan].
    split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact Hpal|].
    split; [unfold heapish; plc|].
    split; [eapply writable_sub; [exact WP | lia | lia | lia]|].
    split; [exact HshP|]. split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [exact Hcells|].
    exists (getr R 2). split; [reflexivity|].
    unfold as_frame, stackish. rewrite R2. split; [lia|]. split.
    - apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
    - eapply writable_sub; [exact WS | lia | lia | lia].
  Qed.

  Lemma after_mc : forall Mx My o w0 w1 w2 w3,
    (o = 56 \/ o = 88)%Z -> KST Mx o w0 w1 w2 w3 ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 368 - 2144), 2144%Z); (Z_to_bv 64 (bv_unsigned P + o), 32%Z)] ->
    cell64 SEGS My (bv_unsigned P + o) w0 -> cell64 SEGS My (bv_unsigned P + o + 8) w1 -> cell64 SEGS My (bv_unsigned P + o + 16) w2 ->
    KST My (o + 32) w0 w1 w2 w3.
  Proof.
    intros Mx My o w0 w1 w2 w3 Ho (HS & Hf & [HFa [hh HFb]] & HZ & Hz & Hc & C0 & C1 & C2 & C3 & K56 & K88) Hfr D0 D1 D2.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
    pose proof (u64_range sp). pose proof (u64_range P).
    unfold KST. cbv zeta.
    split; [eapply (SAVED_frame FP0 regs sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split. { eapply frame_BIG_app; [exact Hf | exact Hfr |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
             first [ apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                   | apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia ]. }
    split. { split.
             - eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HFa | lia | unfold FS_SIZE; lia |].
               intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
             - exists hh. unfold FS_HINT0. eapply acellw_frame; [exact Hfr | exact HFb | lia | lia | solve_apart]. }
    split; [eapply (ZH_frame ceil regs mem ret sp data prio P len fs bs ch HE); [exact HZ | exact Hfr | solve_apart | solve_apart]|].
    split. { replace (976 - (o + 32))%Z with (976 - o - 32)%Z by lia. replace (bv_unsigned P + (o + 32))%Z with (bv_unsigned P + o + 32)%Z by lia.
             eapply zero_frame; [exact Hfr | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]. }
    split; [eapply curve_ok_frame; [exact Hfr | exact Hc | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact C0 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact C1 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact C2 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact C3 | lia | lia | solve_apart]|].
    split.
    - intros H88. destruct Ho as [-> | ->].
      + split; [exact D0|]. split; [replace (bv_unsigned P + 64)%Z with (bv_unsigned P + 56 + 8)%Z by lia; exact D1|].
        replace (bv_unsigned P + 72)%Z with (bv_unsigned P + 56 + 16)%Z by lia; exact D2.
      + destruct (K56 ltac:(lia)) as (E0 & E1 & E2).
        split; [eapply cell64_frame; [exact Hfr | exact E0 | lia | lia | solve_apart]|].
        split; [eapply cell64_frame; [exact Hfr | exact E1 | lia | lia | solve_apart]|].
        eapply cell64_frame; [exact Hfr | exact E2 | lia | lia | solve_apart].
    - intros H120. destruct Ho as [-> | ->]; [exfalso; lia|].
      split; [exact D0|]. split; [replace (bv_unsigned P + 96)%Z with (bv_unsigned P + 88 + 8)%Z by lia; exact D1|].
      replace (bv_unsigned P + 104)%Z with (bv_unsigned P + 88 + 16)%Z by lia; exact D2.
  Qed.

  (* [comment removed for export] *)
  Lemma after_trc : forall My Mz w0 w1 w2 w3,
    KST My 120 w0 w1 w2 w3 ->
    frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
    cell8 SEGS Mz (bv_unsigned P + 964) 1 ->
    SAVED Mz /\ frame_mod mem Mz BIG /\ FSOK Mz /\ DFACTS 1 0 raw Mz /\ cell64 SEGS Mz (bv_unsigned sp - 368) raw.
  Proof.
    intros My Mz w0 w1 w2 w3 (HS & Hf & [HFa [hh HFb]] & HZ & Hz & Hc & C0 & C1 & C2 & C3 & K56 & K88) Hfr C964.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
    unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct (K56 ltac:(lia)) as (D0 & D1 & D2). destruct (K88 ltac:(lia)) as (E0 & E1 & E2).
    split; [eapply (SAVED_frame FP0 regs sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split. { eapply frame_BIG_app; [exact Hf | exact Hfr |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
             apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia. }
    split. { split.
             - eapply (fs_flags0_but_frame fs [] []); [exact Hfr | exact HFa | lia | unfold FS_SIZE; lia |].
               intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
             - exists hh. unfold FS_HINT0. eapply acellw_frame; [exact Hfr | exact HFb | lia | lia | solve_apart]. }
    pose proof (ZH_frame ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ My Mz _ HZ Hfr ltac:(solve_apart) ltac:(solve_apart)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    split; [|exact F2].
    unfold AsLibParseD.DFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
    split.
    { repeat constructor.
      - eapply curve_ok_frame; [exact Hfr | exact Hc | lia | lia | solve_apart].
      - eapply curve_ok_frame; [exact Hfr | | lia | lia | solve_apart].
        eapply (curve_ok_copy SEGS My data len (bv_unsigned P + 24) w0 w1 w2 Hc C0);
          [replace (bv_unsigned P + 24 + 8)%Z with (bv_unsigned P + 32)%Z by lia; exact C1
          |replace (bv_unsigned P + 24 + 16)%Z with (bv_unsigned P + 40)%Z by lia; exact C2
          |exact D0
          |replace (bv_unsigned P + 56 + 8)%Z with (bv_unsigned P + 64)%Z by lia; exact D1
          |replace (bv_unsigned P + 56 + 16)%Z with (bv_unsigned P + 72)%Z by lia; exact D2].
      - eapply curve_ok_frame; [exact Hfr | | lia | lia | solve_apart].
        eapply (curve_ok_copy SEGS My data len (bv_unsigned P + 24) w0 w1 w2 Hc C0);
          [replace (bv_unsigned P + 24 + 8)%Z with (bv_unsigned P + 32)%Z by lia; exact C1
          |replace (bv_unsigned P + 24 + 16)%Z with (bv_unsigned P + 40)%Z by lia; exact C2
          |exact E0
          |replace (bv_unsigned P + 88 + 8)%Z with (bv_unsigned P + 96)%Z by lia; exact E1
          |replace (bv_unsigned P + 88 + 16)%Z with (bv_unsigned P + 104)%Z by lia; exact E2]. }
    split; [eapply zero_frame; [exact Hfr | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]|].
    split; [exact C964|].
    split.
    - eapply cell8_frame; [exact Hfr | | lia | lia | solve_apart].
      replace (bv_unsigned P + 965)%Z with (bv_unsigned P + 120 + 845)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
    - eapply cell8_frame; [exact Hfr | | lia | lia | solve_apart].
      replace (bv_unsigned P + 966)%Z with (bv_unsigned P + 120 + 846)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma after_fsw : forall M2 M3,
    SAVED M2 -> frame_mod mem M2 BIG -> FSOK M2 -> DFACTS 1 0 raw M2 ->
    frame_mod M2 M3 [(Z_to_bv 64 (bv_unsigned P + 120), 4%Z); (Z_to_bv 64 (bv_unsigned P + 136), 4%Z);
                     (Z_to_bv 64 (bv_unsigned P + 152), 4%Z); (Z_to_bv 64 (bv_unsigned P + 965), 1%Z)] ->
    cell8 SEGS M3 (bv_unsigned P + 965) 1 ->
    SAVED M3 /\ frame_mod mem M3 BIG /\ FSOK M3 /\ DFACTS 1 1 raw M3.
  Proof.
    intros M2 M3 HS Hf [HFa [hh HFb]] HF Hfr C965.
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
    destruct HF as (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    unfold AsLibParseD.DFACTS. cbv zeta.
    split; [eapply cell64_frame; [exact Hfr | exact F1 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact F2 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact F2b | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact F3 | lia | lia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hfr | exact F4 | lia | lia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hfr | exact F5 | lia | lia | solve_apart]|].
    split; [eapply trc_curves_frame; [exact Hfr | exact F6 | lia | lia | solve_apart]|].
    split; [eapply zero_frame; [exact Hfr | exact F7 | lia | lia | solve_apart]|].
    split; [eapply cell8_frame; [exact Hfr | exact F8 | lia | lia | solve_apart]|].
    split; [exact C965|].
    eapply cell8_frame; [exact Hfr | exact F10 | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma trc0_words : forall Mq,
    present Mq (bv_unsigned P + 24) 32 ->
    exists w0 w1 w2 w3,
      cell64 SEGS Mq (bv_unsigned P + 24) w0 /\ cell64 SEGS Mq (bv_unsigned P + 32) w1 /\
      cell64 SEGS Mq (bv_unsigned P + 40) w2 /\ cell64 SEGS Mq (bv_unsigned P + 48) w3.
  Proof.
    intros Mq Hp. pose proof (u64_range P).
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 24) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w0 C0].
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 32) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w1 C1].
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 40) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w2 C2].
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 48) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w3 C3].
    exists w0, w1, w2, w3. auto.
  Qed.

  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (w24 w8 : word).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis H19 : getr R 19 = data.
    Hypothesis H24 : getr R 24 = prio.
    Hypothesis HF : ZFACTS M.
    Hypothesis HX24 : cell64 SEGS M (bv_unsigned sp - 344) w24.
    Hypothesis HX8 : cell64 SEGS M (bv_unsigned sp - 360) w8.

    Ltac to_C2 HR HFr H2 H3 H4 H21 H22 HFK HSx Hfx HFSx HFx :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockC2_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc raw
                 Htags I R2 M2);
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HSx | exact Hfx | exact HFSx
        | regv HR (19%bv:reg); exact H19
        | regv HR (24%bv:reg); exact H24
        | exact HFx ]
      end.

    Ltac to_D HR HFr H2 H3 H4 H21 H22 HFK HSx Hfx HFSx HFx v :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockD_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Ha2b Hb2a psz tc 1 v raw
                 Htags ltac:(lia) ltac:(lia) I R2 M2);
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HSx | exact Hfx | exact HFSx
        | regv HR (18%bv:reg); reflexivity
        | regv HR (19%bv:reg); exact H19
        | regv HR (24%bv:reg); exact H24
        | exact HFx ]
      end.

    (* [comment removed for export] *)
    Lemma ktrc_run : forall (FPc : FPState) Rc,
      COMMON FPc Rc -> getr Rc 19 = data -> getr Rc 24 = prio ->
      runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x82054) M rom) Q.
    Proof.
      clear HC H19 H24.
      intros FPc Rc HC H19 H24.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _).
      destruct WS as (_ & _ & _ & S4M). destruct WP as (_ & _ & _ & W4M).
      set (Ec := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [raw; w24; w8])) (blobs_ev [bs])).
      assert (HR2z : getr Rc 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rc 2)), H2; reflexivity).
      assert (HR : regs_ok Ec (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok Ec (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS Ec M
        [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2528) (2 ^ 47 - 368); KWr (SA (EVar 2) (-2528)) 2896;
         KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
         KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
         KWord (SA (EVar 2) 0) 8 (EVar 64); KWord (SA (EVar 2) 24) 8 (EVar 65); KWord (SA (EVar 2) 8) 8 (EVar 66);
         KWord (SA (EVar 2) 16) 8 (ELit 2);
       KDisj (SA (EVar 21) 0) 976 ZSH ZSHL; KDisj (SA (EVar 21) 0) 976 ZIMG ZIMGL; KDisj (SA (EVar 21) 0) 976 (SA (EVar 2) (-2528)) 2896]).
      { destruct HF as ((F1 & F2 & _) & _).
        unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
        - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
          rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rc 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
        - apply krange_intro; cbn. rewrite H2. lia.
        - apply (kwr_intro SEGS Ec M (EVar 2) (getr Rc 2) (-2528) 2896); cbn; try lia; try reflexivity.
          replace (bv_unsigned (getr Rc 2) + -2528)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4M.
        - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
        - apply krange_intro; cbn. rewrite H21. lia.
        - apply (kwr_intro SEGS Ec M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4M.
        - eapply (kzero_shz_intro SEGS Ec M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
        - eapply (kword_intro SEGS Ec M (EVar 2) (getr Rc 2) 0 8 (EVar 64) raw); cbn; try lia; auto.
          replace (bv_unsigned (getr Rc 2) + 0)%Z with (bv_unsigned sp - 368)%Z by lia. exact F2.
        - eapply (kword_intro SEGS Ec M (EVar 2) (getr Rc 2) 24 8 (EVar 65) w24); cbn; try lia; auto.
          replace (bv_unsigned (getr Rc 2) + 24)%Z with (bv_unsigned sp - 344)%Z by lia. exact HX24.
        - eapply (kword_intro SEGS Ec M (EVar 2) (getr Rc 2) 8 8 (EVar 66) w8); cbn; try lia; auto.
          replace (bv_unsigned (getr Rc 2) + 8)%Z with (bv_unsigned sp - 360)%Z by lia. exact HX8.
        - eapply (kword_intro SEGS Ec M (EVar 2) (getr Rc 2) 16 8 (ELit 2) (Z_to_bv 64 2)); cbn; try lia; auto.
          replace (bv_unsigned (getr Rc 2) + 16)%Z with (bv_unsigned sp - 352)%Z by lia. exact F1.
        - kdisj_place.
        - kdisj_place.
        - kdisj_place.
      }
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      run_fp 30%nat [0x81018%Z; 0x82150%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hgray.
      { (* [comment removed for export] *) to_C2 HR HFr H2 H3 H4 H21 H22 HFK HS Hf HFS HF. }
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as ((_ & _ & _ & _ & F3 & _ & F5) & Hz).
      run_fp 30%nat [0x81018%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz 0x6b545243%Z (Z_to_bv 64 (bv_unsigned sp - 368 + 216)) I R1 Mx ro (Z_to_bv 64 0x82078));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 216 _ psz tc Hf F3 F5 Htags);
            [ regv HR (21%bv:reg); exact H21
            | regv HR (10%bv:reg); exact H21
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite ?HR2z; rewrite ?u_small by lia; apply (f_equal (Z_to_bv 64)); lia
            | exact HR2c
            | lia | cbn; tauto ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag1). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 216, 24%Z)].
      assert (Hf1 : frame_mod mem mq1 BIG) by (eapply frame_BIG_app; [exact Hf | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 216); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 216 ltac:(cbn; tauto) HS Hfr) as HS1.
      pose proof (ZFACTS_tag ceil regs mem ret sp data prio P len fs bs ch HE _ _ _ _ _ 216%Z ltac:(cbn; tauto) HF Hfr) as HF1.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 216 ltac:(cbn; tauto) HFS Hfr) as HFS1.
      assert (Hpr1 : present mq1 (bv_unsigned P + 24) 32)
        by (eapply present_frame; [exact Hfr|]; apply zero_present; eapply zero_sub; [exact Hz | lia | lia]).
      clear Hfr F3 F5 Hz.
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 77) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x82150%Z] noscr false. to_C2 HR HFr H2 H3 H4 H21 H22 HFK HS1 Hf1 HFS1 HF1. }
      pose proof (XT_intro ceil regs mem ret sp data prio P len fs bs ch HE mq1 216%Z _ ltac:(lia) (Htag1 eq_refl)) as X1. clear Htag1.
      add_krange (EVar 77) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      destruct X1 as ((sz1 & buf1 & [Rs1 Cs1] & Cb1 & Hs1 & In1) & _ & _).
      unfold cell64, cell in Cb1. unfold cell in Cs1.
      pose proof In1 as (In1a & In1b & In1c). pose proof (u64_range buf1).
      env_extend [Z_to_bv 64 sz1; buf1].
      kn_prefix HK [KWord (SA (EVar 2) 224) 4 (EVar 131); KWord (SA (EVar 2) 232) 8 (EVar 132); KRange (EVar 131) 4 (2^26)].
      { eapply (kword_intro SEGS _ mq1 (EVar 2) (getr Rc 2) 224 4 (EVar 131) (Z_to_bv 64 sz1)); cbn [edenot]; ev_simpl_goal; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 224)%Z with (bv_unsigned sp - 368 + 216 + 8)%Z by lia; exact Cs1. }
      { eapply (kword_intro SEGS _ mq1 (EVar 2) (getr Rc 2) 232 8 (EVar 132) buf1); cbn [edenot]; ev_simpl_goal; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 232)%Z with (bv_unsigned sp - 368 + 216 + 16)%Z by lia; exact Cb1. }
      { apply krange_intro; cbn [edenot]; ev_simpl_goal; rewrite u_small by lia; lia. }
      (* [comment removed for export] *)
      pose proof HF1 as HF'. destruct HF' as (HZ1 & Hz1).
      run_fp 30%nat [0x82814%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hrc data len bs (Z_to_bv 64 (bv_unsigned sp - 368)) buf1 (Z_to_bv 64 (bv_unsigned P + 24)) (Z_to_bv 64 0) sz1 I R1 Mx ro (Z_to_bv 64 0x82094));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (rcurve_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 (bv_unsigned P + 24) sz1 buf1 Hf1 In1 Rs1 ltac:(lia));
            [ regv HR (2%bv:reg); exact HR2z
            | regv HR (10%bv:reg); reflexivity
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv HR (13%bv:reg); reflexivity ] ]
        | cbv beta ]
      end.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Hc2 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      apply (rcurve_frame_norm ceil regs mem ret sp data prio P len fs bs ch HE) in Hfr.
      kframe HK Hfr [(SA (EVar 2) (-2208), 2208%Z); (SA (EVar 21) 24, 32%Z)].
      rewrite !u_small_frame in Hc2 by lia.
      destruct (after_rcurve ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE psz tc raw mq1 mq2 (bv_unsigned P + 24) ltac:(lia) HS1 Hf1 HFS1 HZ1 _ Hz1 ltac:(lia) Hfr)
        as (HS2 & Hf2 & HFS2 & HZ2 & Hz2 & _).
      specialize (Hz2 (bv_unsigned P + 56)%Z 920%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Hpr2 : present mq2 (bv_unsigned P + 24) 32) by (eapply present_frame; [exact Hfr | exact Hpr1]).
      clear Hfr HZ1 Hz1 HS1 Hf1 Hpr1 HF1 HFS1.
      destruct Hr02 as [-> | ->].
      { add_krange (EVar 143) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x81e9c%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
          apply (exit_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M' 0);
          [ common HR HFr H2 H3 H4 H21 H22 HFK | regv HR (10%bv:reg); exact Hr2 | lia | exact HS2 | exact Hf2 | exact HFS2 | intros; exfalso; lia ]
        end. }
      specialize (Hc2 eq_refl).
      add_krange (EVar 143) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      destruct (trc0_words mq2 Hpr2) as (w0 & w1 & w2 & w3 & C0 & C1 & C2 & C3).
      assert (K2 : KST mq2 56 w0 w1 w2 w3).
      { split; [exact HS2|]. split; [exact Hf2|]. split; [exact HFS2|]. split; [exact HZ2|]. split; [exact Hz2|]. split; [exact Hc2|].
        split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; intros; exfalso; lia. }
      clear HS2 Hf2 HFS2 HZ2 Hz2 Hc2 C0 C1 C2 C3 Hpr2.
      run_fp 15%nat [0x51034%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hmc 56%Z P w0 w1 w2 w3 ltac:(lia) I R1 Mx ro (Z_to_bv 64 0x820ac));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (mc_pre_at Mx I R1 56 w0 w1 w2 w3 ltac:(lia) K2);
            [ rewrite HR2c, u_small by lia; reflexivity
            | regv_lin HR (10%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv_lin HR (11%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv HR (12%bv:reg); reflexivity ] ]
        | cbv beta ]
      end.
      intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & D0 & D1 & D2 & D3 & Ha0). rewrite HR2c, u_small in Hfr by lia. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ3. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-2144), 2144%Z); (SA (EVar 21) 56, 32%Z)].
      pose proof (after_mc mq2 mq3 56 w0 w1 w2 w3 ltac:(lia) K2 Hfr D0 D1 D2) as K3. change (56 + 32)%Z with 88%Z in K3.
      clear Hfr K2 D0 D1 D2 D3.
      pin_reg HR (10%bv:reg) (EAlu ALU_ADD (EVar 21) (ELit 56)) by (rewrite Ha0; cbn [edenot]; ev_simpl_goal; rewrite H21, alu_add_lit; reflexivity).
      run_fp 15%nat [0x51034%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hmc 88%Z P w0 w1 w2 w3 ltac:(lia) I R1 Mx ro (Z_to_bv 64 0x820bc));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (mc_pre_at Mx I R1 88 w0 w1 w2 w3 ltac:(lia) K3);
            [ rewrite HR2c, u_small by lia; reflexivity
            | regv_lin HR (10%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv_lin HR (11%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv HR (12%bv:reg); reflexivity ] ]
        | cbv beta ]
      end.
      intros FQ4 rq4 mq4 (Hkeep & Hfkeep & Hfr & D0 & D1 & D2 & D3 & Ha0'). rewrite HR2c, u_small in Hfr by lia. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ4. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-2144), 2144%Z); (SA (EVar 21) 88, 32%Z)].
      pose proof (after_mc mq3 mq4 88 w0 w1 w2 w3 ltac:(lia) K3 Hfr D0 D1 D2) as K4. change (88 + 32)%Z with 120%Z in K4.
      clear Hfr K3 D0 D1 D2 D3.
      (* [comment removed for export] *)
      pose proof K4 as K4'. destruct K4' as (HS4 & Hf4 & HFS4 & _).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE mq4 Hf4) as (_ & _ & _ & _ & _ & _ & _ & WP4 & HshP4 & _).
      destruct WP4 as (_ & _ & _ & W44).
      lazymatch type of HR with regs_ok ?E2 _ _ =>
        kn_prefix HK [KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122)];
        [ eapply (kzero_shz_intro SEGS E2 mq4 (EVar 21) P 122); [cbn; ev_simpl E2; exact H21 | exact HshP4 | lia | lia] |] end.
      run_fp 15%nat [0x820e0%Z] noscr true.
      lazymatch goal with EQM : ?Mn = mem_denot _ mq4 _ |- _ =>
        assert (Hfr2 : frame_mod mq4 Mn [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 964, 1%Z)]); clear EQM; try clear HLF end.
      kcell HK (EVar 21) 964%Z 1%nat (ELit 1) C964.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M2 _) _ =>
        destruct (after_trc mq4 M2 w0 w1 w2 w3 K4 Hfr2 ltac:(split; [lia | unfold LibDefs.cell; exact C964])) as (HS5 & Hf5 & HFS5 & HF5 & Hraw5) end.
      clear C964 Hfr2 K4 HS4 Hf4 HFS4.
      run_fp 10%nat [0x82284%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hx.
      { (* [comment removed for export] *) to_D HR HFr H2 H3 H4 H21 H22 HFK HS5 Hf5 HFS5 HF5 0%Z. }
      run_fp 30%nat [0x82284%Z] noscr true.
      lazymatch goal with EQM : ?M3 = mem_denot _ ?M2 _ |- _ =>
        assert (Hfr3 : frame_mod M2 M3 [(Z_to_bv 64 (bv_unsigned P + 120), 4%Z); (Z_to_bv 64 (bv_unsigned P + 136), 4%Z);
                                       (Z_to_bv 64 (bv_unsigned P + 152), 4%Z); (Z_to_bv 64 (bv_unsigned P + 965), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 120, 4%Z); (SA (EVar 21) 136, 4%Z); (SA (EVar 21) 152, 4%Z); (SA (EVar 21) 965, 1%Z)]);
        clear EQM; try clear HLF end.
      kcell HK (EVar 21) 965%Z 1%nat (ELit 1) C965.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M3 _) _ =>
        destruct (after_fsw _ M3 HS5 Hf5 HFS5 HF5 Hfr3 ltac:(split; [lia | unfold LibDefs.cell; exact C965])) as (HS6 & Hf6 & HFS6 & HF6) end.
      to_D HR HFr H2 H3 H4 H21 H22 HFK HS6 Hf6 HFS6 HF6 1%Z.
    Qed.

    Lemma blockC1_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82038) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP.
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WS & _).
      destruct WS as (_ & _ & _ & S4M).
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [w24])) (blobs_ev [bs])).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS E M [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2528) (2 ^ 47 - 368); KWr (SA (EVar 2) (-2528)) 2896;
                                      KWord (SA (EVar 2) 24) 8 (EVar 64)]).
      { unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
        - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
          rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
        - apply krange_intro; cbn. rewrite H2. lia.
        - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2528) 2896); cbn; try lia; try reflexivity.
          replace (bv_unsigned (getr R 2) + -2528)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4M.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 24 8 (EVar 64) w24); cbn; try lia; auto.
          replace (bv_unsigned (getr R 2) + 24)%Z with (bv_unsigned sp - 344)%Z by lia. exact HX24. }
      run_fp 10%nat [0x82054%Z] noscr false.
      branch_case as Hpx.
      { (* [comment removed for export] *)
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ => apply (ktrc_run I R2) end;
          [ common HR HFr H2 H3 H4 H21 H22 HFK | regv HR (19%bv:reg); exact H19 | regv HR (24%bv:reg); exact H24 ]. }
      run_fp 10%nat [0x82054%Z; 0x81e98%Z] noscr false.
      branch_case as Hlab.
      { (* [comment removed for export] *) fail_now HR HFr H2 H3 H4 H21 H22 HFK HS Hf HFS. }
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ => apply (ktrc_run I R2) end;
        [ common HR HFr H2 H3 H4 H21 H22 HFK | regv HR (19%bv:reg); exact H19 | regv HR (24%bv:reg); exact H24 ].
    Qed.
  End Run.
End C1.
