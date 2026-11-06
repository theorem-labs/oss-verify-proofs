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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibParseDefs AsLibKit AsLibParseF AsLibParseE AsLibPlace.
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

(* [comment removed for export] *)
Ltac solve_apart_v2 :=
  unfold apart, SB; repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?u_small_frame by alia; first [alia | (div8_facts; app_sh; dlia)] |]);
  apply Forall_nil.

Section D.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).
  Hypothesis HE : PENV ceil regs mem ret sp data prio P len fs bs ch.
  Hypothesis Hgettag : gettag_contract_as SEGS as_asan ceil.
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
  Variables (psz tc h964 h965 : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.
  Hypothesis R964 : (h964 = 0 \/ h964 = 1)%Z.
  Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.

  #[local] Notation EFACTS := (EFACTS sp data P len psz tc h964 h965).

  (* [comment removed for export] *)
  Definition DFACTS (Mx : word -> option byte) : Prop :=
    let p := bv_unsigned P in let s := bv_unsigned sp in
    cell64 SEGS Mx (s - 352) (Z_to_bv 64 2) /\ cell64 SEGS Mx (s - 368) raw /\ cell64 SEGS Mx (s - 304) (Z_to_bv 64 len) /\
    cell64 SEGS Mx p data /\ cell32 SEGS Mx (p + 8) psz /\ cell32 SEGS Mx (p + 20) tc /\
    Forall (fun off => curve_ok SEGS Mx data len (p + off)) [24; 56; 88]%Z /\
    zero Mx (p + 160) 800 /\
    cell8 SEGS Mx (p + 964) h964 /\ cell8 SEGS Mx (p + 965) h965 /\ cell8 SEGS Mx (p + 966) 0.

  Lemma DFACTS_frame : forall Mx My rs,
    DFACTS Mx -> frame_mod Mx My rs ->
    apart (bv_unsigned sp - 368) 72 rs -> apart (bv_unsigned P) 976 rs -> DFACTS My.
  Proof.
    intros Mx My rs (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf As Ap.
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    unfold DFACTS. cbv zeta.
    split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2b | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F8 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F9 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    eapply cell8_frame; [exact Hf | exact F10 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]].
  Qed.

  Lemma DFACTS_frame4 : forall Mx My rs,
    DFACTS Mx -> frame_mod Mx My rs ->
    apart (bv_unsigned sp - 368) 72 rs -> apart (bv_unsigned P) 120 rs ->
    apart (bv_unsigned P + 160) 800 rs -> apart (bv_unsigned P + 964) 3 rs -> DFACTS My.
  Proof.
    intros Mx My rs (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf As Ap Az Afl.
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    unfold DFACTS. cbv zeta.
    split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2b | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | exact Az]|].
    split; [eapply cell8_frame; [exact Hf | exact F8 | lia | lia | eapply apart_sub; [exact Afl | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F9 | lia | lia | eapply apart_sub; [exact Afl | lia | lia | lia]]|].
    eapply cell8_frame; [exact Hf | exact F10 | lia | lia | eapply apart_sub; [exact Afl | lia | lia | lia]].
  Qed.

  Lemma DFACTS_tag : forall Mx My (k : Z), In k tag_offsets ->
    DFACTS Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 368)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 368 + k), 24%Z)] -> DFACTS My.
  Proof.
    intros Mx My k Hk HF Hfr. pose proof (u64_range sp). pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    assert (Hk' : (k = 216 \/ k = 192 \/ k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72)%Z) by (cbn in Hk; clear -Hk; intuition lia).
    eapply DFACTS_frame; [exact HF | exact Hfr | rewrite u_small by lia; solve_apart | rewrite u_small by lia; solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma DFACTS_E : forall Mx, DFACTS Mx -> EFACTS 0 raw Mx.
  Proof.
    intros Mx (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    unfold AsLibParseE.EFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|].
    split; [apply zero_a2b_curves; [eapply zero_sub; [exact F7 | lia | lia] | lia | lia]|].
    split; [eapply zero_sub; [exact F7 | lia | lia]|].
    split; [exact F8|]. split; [exact F9|]. split; [exact F10|]. intros Hc; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma a2b_pre_at : forall Mx (FP : FPState) R sig,
    frame_mod mem Mx BIG -> DFACTS Mx -> FSOK Mx ->
    tag_ok SEGS Mx data len (bv_unsigned sp - 368 + 192) ->
    cell32 SEGS Mx (bv_unsigned sp - 368 + 192) sig ->
    (exists ty, cell32 SEGS Mx (bv_unsigned sp - 368 + 192 + 4) ty) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 368) ->
    getr R 10 = Z_to_bv 64 (bv_unsigned sp - 368 + 192) ->
    getr R 11 = Z_to_bv 64 (bv_unsigned P + 160) ->
    getr R 12 = Z_to_bv 64 (pcs_of raw) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned data + len) ->
    getr R 4 = getr regs 4 ->
    a2b_pre_as SEGS as_asan ceil data len bs (Z_to_bv 64 (bv_unsigned sp - 368)) (Z_to_bv 64 (bv_unsigned sp - 368 + 192))
            (Z_to_bv 64 (bv_unsigned P + 160)) (pcs_of raw) fs ch FP R Mx.
  Proof.
    intros Mx FP R sig Hf HF HFS Htag Hsig Hty R2 R10 R11 R12 R13 R4.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx Hf) as (HD & HEV & Hhdr & Hfsw & _ & _ & _ & WP & HshP & WS & HshS & _ & _).
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & Htp & _ & Hdar & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct HF as (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10). destruct HFS as [HF1 HF2].
    unfold a2b_pre_as. cbv zeta. rewrite !u_small_frame by lia. cbn [al_abi as_asan].
    unfold A2B_D, FS_FRAMES5, FS_SIZE in *.
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [rewrite R4; exact Htp|].
    split; [apply pcs_of_01|].
    split; [exact HD|].
    split; [exact Hty|]. split; [exact Htag|].
    assert (T8 : ((bv_unsigned sp - 368 + 192) mod 8 = 0)%Z).
    { replace (bv_unsigned sp - 368 + 192)%Z with (bv_unsigned sp + (-176))%Z by lia.
      apply mod_add_multiple; [lia | apply (mod_down _ 8 2); [lia|lia|exact N6] | reflexivity]. }
    split; [exact T8|].
    split; [unfold stackish; lia|].
    split; [eapply (shz_sub Mx _ _ _ _ HshS); [exact T8 | lia | lia | lia]|].
    split; [lia|].
    split; [eapply writable_sub; [exact WP | lia | lia | lia]|].
    assert (A8 : ((bv_unsigned P + 160) mod 8 = 0)%Z) by (apply mod_add_multiple; [lia | apply (mod_down _ 8 8); [lia|lia|exact Hpal] | reflexivity]).
    split; [exact A8|].
    split; [unfold heapish; plc|].
    split; [eapply (shz_sub Mx _ _ _ _ HshP); [exact A8 | lia | lia | lia]|].
    split. { apply (shwz_curves Mx (bv_unsigned P)); [exact HshP | exact Hpal | lia | lia |].
             unfold a2b_curve_offsets. repeat (apply Forall_cons); try apply Forall_nil; lia. }
    split; [lia|]. split; [lia|].
    split; [apply zero_a2b_curves; [eapply zero_sub; [exact F7 | lia | lia] | lia | lia]|].
    split.
    { exists (Z_to_bv 64 0), (Z_to_bv 64 0). split.
      - eapply (zero_cell64 SEGS Mx (bv_unsigned P + 160) 800 128); [exact F7 | lia | lia | lia | lia].
      - eapply (zero_cell64 SEGS Mx (bv_unsigned P + 160) 800 136); [exact F7 | lia | lia | lia | lia]. }
    split. { unfold as_frame, stackish. rewrite !u_small by lia. split; [lia|]. split.
             - apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
             - eapply writable_sub; [exact WS | lia | lia | lia]. }
    split; [change (2528 / 8)%Z with 316%Z; eapply (shz_sub Mx _ _ _ _ HshS); [| lia | lia | lia];
            apply (mod_down _ 8 2); [lia|lia|]; change (8*2)%Z with 16%Z; replace (bv_unsigned sp - 368 - 2528)%Z with (bv_unsigned sp - 2896)%Z by lia;
            apply mod_sub_multiple; [lia | exact N6 | reflexivity]|].
    split; [exact HEV|]. split; [exact Hhdr|]. split; [exact Hfsw|]. split; [exact HF2|]. split; [exact HF1|].
    split; [exact Hdar|]. unfold FS_FRAMES5, FS_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma after_a2b : forall Mx My,
    DFACTS Mx -> SAVED Mx -> frame_mod mem Mx BIG ->
    frame_mod Mx My ([(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 368)) - A2B_D), A2B_D);
                      (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 160))), 400%Z)] ++ fs_mod0 fs) ->
    SAVED My /\ frame_mod mem My BIG /\
    (Forall (fun off => curve_ok SEGS My data len (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 160)) + off)) a2b_curve_offsets ->
     a2b_grid_ok SEGS My data len (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 160))) ->
     forall Mz, frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell8 SEGS Mz (bv_unsigned P + 966) 1 ->
     EFACTS 1 raw Mz).
  Proof.
    intros Mx My HF HS Hf Hfr.
    pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
    pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp1 & Hp2 & _).
    pose proof (penv_quot ceil regs mem ret sp data prio P len fs bs ch HE) as HQ. hide HQ.
    pose proof (u64_range sp). pose proof (u64_range P). unfold FS_FRAMES5, FS_SIZE, A2B_D in *.
    rewrite !u_small_frame in Hfr by lia. rewrite !u_small_frame by lia. unfold fs_mod0 in Hfr. cbn [app] in Hfr.
    unfold FS_HINT0, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES0, FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_SB in Hfr.
    destruct HF as (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    split; [eapply (SAVED_frame FP0 regs sp); [exact HS | exact Hfr | solve_apart_v2 | lia]|].
    split. { eapply frame_BIG_app; [exact Hf | exact Hfr |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
             first [ apply (in_big_stack ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                   | apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia
                   | apply (in_big_fs sp P fs); cbn; tauto ]. }
    intros Hc Hg Mz Hfz C966. unfold AsLibParseE.EFACTS. cbv zeta.
    lazymatch type of Hfr with frame_mod _ _ ?rs =>
    assert (T64 : forall a x, cell64 SEGS Mx a x -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> apart a 8 rs ->
              apart a 8 [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell64 SEGS Mz a x);
    [ intros a x C Ha Ha8 Ap1 Ap2; eapply cell64_frame; [exact Hfz | | lia | lia | exact Ap2];
      eapply cell64_frame; [exact Hfr | exact C | lia | lia | exact Ap1] |];
    assert (T32 : forall a x, cell32 SEGS Mx a x -> (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> apart a 4 rs ->
              apart a 4 [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell32 SEGS Mz a x);
    [ intros a x C Ha Ha4 Ap1 Ap2; eapply cell32_frame; [exact Hfz | | lia | lia | exact Ap2];
      eapply cell32_frame; [exact Hfr | exact C | lia | lia | exact Ap1] |];
    assert (T8 : forall a x, cell8 SEGS Mx a x -> (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z -> apart a 1 rs ->
              apart a 1 [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell8 SEGS Mz a x);
    [ intros a x C Ha Ha1 Ap1 Ap2; eapply cell8_frame; [exact Hfz | | lia | lia | exact Ap2];
      eapply cell8_frame; [exact Hfr | exact C | lia | lia | exact Ap1] |]
    end.
    split; [apply T64; [exact F1 | lia | lia | solve_apart_v2 | solve_apart]|].
    split; [apply T64; [exact F2 | lia | lia | solve_apart_v2 | solve_apart]|].
    split; [apply T64; [exact F3 | lia | lia | solve_apart_v2 | solve_apart]|].
    split; [apply T32; [exact F4 | lia | lia | solve_apart_v2 | solve_apart]|].
    split; [apply T32; [exact F5 | lia | lia | solve_apart_v2 | solve_apart]|].
    split.
    { eapply trc_curves_frame; [exact Hfz | | lia | lia | solve_apart].
      eapply trc_curves_frame; [exact Hfr | exact F6 | lia | lia | solve_apart_v2]. }
    split; [eapply a2b_curves_frame; [exact Hfz | exact Hc | lia | lia | solve_apart]|].
    split.
    { eapply zero_frame; [exact Hfz | | lia | lia | solve_apart].
      eapply zero_frame; [exact Hfr | eapply zero_sub; [exact F7 | lia | lia] | lia | lia | solve_apart_v2]. }
    split; [apply T8; [exact F8 | lia | lia | solve_apart_v2 | solve_apart]|].
    split; [apply T8; [exact F9 | lia | lia | solve_apart_v2 | solve_apart]|].
    split; [exact C966|].
    intros _. eapply grid_ok_A2B_frame288; [exact Hfz | exact Hg | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Found.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (sig : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis H24 : getr R 24 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 (bv_unsigned data + len).
    Hypothesis HF : DFACTS M.
    Hypothesis Htag : tag_ok SEGS M data len (bv_unsigned sp - 368 + 192).
    Hypothesis Hsig : cell32 SEGS M (bv_unsigned sp - 368 + 192) sig.
    Hypothesis Hty : exists ty, cell32 SEGS M (bv_unsigned sp - 368 + 192 + 4) ty.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [raw])) (blobs_ev [bs]).

    Definition kn_found : list kentry :=
      [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2528) (2 ^ 47 - 368); KWr (SA (EVar 2) (-2528)) 2896;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KWord (SA (EVar 2) 0) 8 (EVar 64)].

    Lemma kn_found_ok : know_ok SEGS E M kn_found.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & _ & _ & _ & WP & HshP & WS & _).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
      pose proof (u64_range sp). pose proof (u64_range P). unfold FS_SIZE in *.
      destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4). destruct HF as (F1 & F2 & _).
      unfold kn_found, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2528) 2896); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2528)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4.
      - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. lia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 0 8 (EVar 64) raw); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 0)%Z with (bv_unsigned sp - 368)%Z by lia. exact F2.
    Qed.

    Lemma foundD_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x822fc) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
      unfold FS_FRAMES5, FS_SIZE in Hp1, Hp2.
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF' : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_found_ok as HK. unfold kn_found in HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      run_fp 20%nat [0x83980%Z] noscr false.
      (* [comment removed for export] *)
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Ha2b data len bs (Z_to_bv 64 (bv_unsigned sp - 368)) (Z_to_bv 64 (bv_unsigned sp - 368 + 192))
                    (Z_to_bv 64 (bv_unsigned P + 160)) (pcs_of raw) fs ch I R1 Mx ro (Z_to_bv 64 0x82320));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (a2b_pre_at Mx I R1 sig Hf HF HFS Htag Hsig Hty);
            [ regv HR (2%bv:reg); exact HR2z
            | regv_lin HR (10%bv:reg); rewrite H2; apply (f_equal (Z_to_bv 64)); lia
            | regv_lin HR (11%bv:reg); rewrite H21; apply (f_equal (Z_to_bv 64)); lia
            | regv HR (12%bv:reg); rewrite alu_sltu, alu_xor; apply sltiu_xor_pcs
            | regv HR (13%bv:reg); exact H19
            | regv HR (4%bv:reg); exact H4 ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & HF1q & [hh Hh1q] & r1 & Hr1 & Hr01 & Hpost).
      destruct (after_a2b M mq1 HF HS Hf Hfr) as (HS1 & Hf1 & HE1).
      assert (HFS1 : FSOK mq1) by (split; [exact HF1q | exists hh; exact Hh1q]).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE mq1 Hf1) as (_ & _ & _ & _ & _ & _ & _ & WP1 & HshP1 & _).
      destruct WP1 as (_ & _ & _ & W4).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep Hfr.
      clear HK.
      lazymatch type of HR with regs_ok ?E2 _ _ =>
        assert (HK : know_ok SEGS E2 mq1
          [KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976; KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122)]);
        [ unfold know_ok; repeat (apply Forall_cons); [..|apply Forall_nil];
          [ apply kalign_intro; [lia|]; cbn; ev_simpl E2; rewrite H21; exact Hpal
          | apply krange_intro; cbn; ev_simpl E2; rewrite H21; lia
          | apply (kwr_intro SEGS E2 mq1 (EVar 21) P 0 976); cbn; ev_simpl E2; rewrite ?H21; try lia; try reflexivity; rewrite Z.add_0_r; exact W4
          | eapply (kzero_shz_intro SEGS E2 mq1 (EVar 21) P 122); [cbn; ev_simpl E2; exact H21 | exact HshP1 | lia | lia] ]
        |] end.
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 75) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x81e9c%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
          apply (exit_ok ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE I R' M' 0);
          [ common HR HF' H2 H3 H4 H21 H22 HFK | regv HR (10%bv:reg); exact Hr1 | lia | exact HS1 | exact Hf1 | exact HFS1 | intros; exfalso; lia ]
        end. }
      destruct (Hpost eq_refl) as [Hcurves Hgrid].
      add_krange (EVar 75) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      run_fp 15%nat [0x82340%Z] noscr true.
      lazymatch goal with EQM : ?Mn = mem_denot _ mq1 _ |- _ =>
        assert (Hfr2 : frame_mod mq1 Mn [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)])
          by (rewrite EQM; frame_of_log [(SA (EVar 21) 966, 1%Z)]); clear EQM end.
      kcell HK (EVar 21) 966%Z 1%nat (ELit 1) C966.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockE_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hb2a psz tc h964 h965 1 raw
                 Htags R964 R965 ltac:(lia) I R2 M2) end.
      - common HR HF' H2 H3 H4 H21 H22 HFK.
      - eapply (SAVED_frame FP0 regs sp); [exact HS1 | exact Hfr2 | solve_apart | lia].
      - eapply frame_BIG_app; [exact Hf1 | exact Hfr2 |]. apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
          apply (in_big_P ceil regs mem rom ret sp data prio P len fs bs ch HE); lia.
      - destruct HFS1 as [HFa [hh1 HFb]]. split.
        + eapply (fs_flags0_but_frame fs [] []); [exact Hfr2 | exact HFa | lia | unfold FS_SIZE; lia |].
          intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0. solve_apart.
        + exists hh1. unfold FS_HINT0. eapply acellw_frame; [exact Hfr2 | exact HFb | lia | lia | solve_apart].
      - regv HR (24%bv:reg). exact H24.
      - regv HR (19%bv:reg). exact H19.
      - apply (HE1 Hcurves Hgrid _ Hfr2). split; [lia|]. unfold LibDefs.cell. rewrite Z.add_0_r in C966 || idtac. exact C966.
    Qed.
  End Found.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis H18 : getr R 18 = Z_to_bv 64 2.
    Hypothesis H19 : getr R 19 = data.
    Hypothesis H24 : getr R 24 = prio.
    Hypothesis HF : DFACTS M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [Z_to_bv 64 len])) (blobs_ev [bs]).

    Definition kn_D : list kentry :=
      [KAlign (EVar 2) 16; KRange (EVar 2) (AS_STKLO + 2528) (2 ^ 47 - 368); KWr (SA (EVar 2) (-2528)) 2896;
       KAlign (EVar 21) 64; KRange (EVar 21) 1 (2 ^ 47 - 976); KWr (SA (EVar 21) 0) 976;
       KZero (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SB) (ELit 122);
       KAlign (EVar 24) 8; KRange (EVar 24) 1 (2 ^ 47 - 8);
       KZero (SA (EAlu ALU_SRL (EVar 24) (ELit 3)) SB) (ELit 1);
       KRange (EVar 18) 2 2; KRange (EVar 19) 1 (2 ^ 47 - 16); KRange (EVar 64) 0 (2 ^ 26);
       KWord (SA (EVar 2) 16) 8 (ELit 2);
       KWord (SA (EVar 2) 64) 8 (EVar 64);
       KWord (SA (EVar 24) 0) 4 (ELit 0);
       KWord (SA (EVar 24) 4) 4 (ELit 1);
       KDisj (SA (EVar 21) 0) 976 ZSH ZSHL; KDisj (SA (EVar 21) 0) 976 ZIMG ZIMGL; KDisj (SA (EVar 21) 0) 976 (SA (EVar 2) (-2528)) 2896;
       KDisj (SA (EVar 24) 0) 8 ZSH ZSHL; KDisj (SA (EVar 24) 0) 8 ZIMG ZIMGL; KDisj (SA (EVar 24) 0) 8 (SA (EVar 2) (-2528)) 2896].

    Lemma kn_D_ok : know_ok SEGS E M kn_D.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
      destruct (penv_at ceil regs mem rom ret sp data prio P len fs bs ch HE M Hf) as (_ & _ & _ & _ & C0 & C4 & Hshq & WP & HshP & WS & _).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & Hqal & _ & _ & _ & _ & _ & _ & Hpal & _).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range prio). pose proof (u64_range data). unfold FS_SIZE in *.
      destruct WS as (_ & _ & _ & S4). destruct WP as (_ & _ & _ & W4). destruct HF as (F1 & F2 & F2b & _). destruct C0 as [_ C0]. destruct C4 as [_ C4].
      unfold kn_D, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kalign_intro; [lia|]. cbn. apply (mod_down _ 16 1); [lia|lia|]. change (16*1)%Z with 16%Z.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2, u_small by lia. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2528) 2896); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -2528)%Z with (bv_unsigned sp - 2896)%Z by lia. exact S4.
      - apply kalign_intro; [lia|]. cbn; rewrite H21. exact Hpal.
      - apply krange_intro; cbn. rewrite H21. lia.
      - apply (kwr_intro SEGS E M (EVar 21) P 0 976); cbn; rewrite ?H21; try lia; try reflexivity. rewrite Z.add_0_r. exact W4.
      - eapply (kzero_shz_intro SEGS E M (EVar 21) P 122); [cbn; exact H21 | exact HshP | lia | lia].
      - apply kalign_intro; [lia|]. cbn; rewrite H24. exact Hqal.
      - apply krange_intro; cbn. rewrite H24. lia.
      - eapply (kzero_shz_intro SEGS E M (EVar 24) prio 1); [cbn; exact H24 | exact Hshq | lia | lia].
      - apply krange_intro; cbn. rewrite H18, u_small by lia. lia.
      - apply krange_intro; cbn. rewrite H19. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 16 8 (ELit 2) (Z_to_bv 64 2)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 16)%Z with (bv_unsigned sp - 352)%Z by lia. exact F1.
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 64 8 (EVar 64) (Z_to_bv 64 len)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 64)%Z with (bv_unsigned sp - 304)%Z by lia. exact F2b.
      - eapply (kword_intro SEGS E M (EVar 24) prio 0 4 (ELit 0) (Z_to_bv 64 0)); cbn; rewrite ?H24; try lia; auto.
        rewrite Z.add_0_r. exact C0.
      - eapply (kword_intro SEGS E M (EVar 24) prio 4 4 (ELit 1) (Z_to_bv 64 1)); cbn; rewrite ?H24; try lia; auto.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
      - kdisj_place.
    Qed.

    (* [comment removed for export] *)
    Ltac call_gettag sig retw Mx0 Hfx C0 C20 H21 HR2z :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        let HR2c := fresh "HR2c" in
        assert (HR2c : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (regv HR (2%bv:reg); exact HR2z);
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 368 + 192)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at ceil regs mem rom ret sp data prio P len fs bs ch HE Mx I R1 192 _ psz tc Hfx C0 C20 Htags);
            [ regv HR (21%bv:reg); exact H21
            | regv HR (10%bv:reg); exact H21
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); rewrite ?HR2z; rewrite ?u_small by lia; apply (f_equal (Z_to_bv 64)); lia
            | exact HR2c
            | lia | cbn; tauto ] ]
        | cbv beta ]
      end.

    Lemma blockD_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82284) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
      pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
      destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13). unfold FS_SIZE in N2.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd. pose proof (u64_range prio) as Rq.
      pose proof HF as HF'. destruct HF' as (F1 & F2 & F2b & F3 & F4 & F5 & _).
      assert (HR2z : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 368)) by (rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_D_ok as HK. unfold kn_D in HK.
      pin_reg HR (22%bv:reg) (ELit SB) by (regv HR (22%bv:reg); exact H22).
      run_fp 30%nat [0x81018%Z] noscr false.
      (* [comment removed for export] *)
      call_gettag 0x41324230%Z (Z_to_bv 64 0x822d0) M Hf F3 F5 H21 HR2z.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 192, 24%Z)].
      assert (Hf1 : frame_mod mem mq1 BIG) by (eapply frame_BIG_app; [exact Hf | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 192); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 ltac:(cbn; tauto) HS Hfr) as HS1.
      pose proof (DFACTS_tag _ _ 192 ltac:(cbn; tauto) HF Hfr) as HF1.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 ltac:(cbn; tauto) HFS Hfr) as HFS1.
      clear Hfr.
      destruct Hr01 as [-> | ->].
      2:{ (* [comment removed for export] *)
        destruct (Htag eq_refl) as (Htg & Csig & Cty). rewrite !u_small_frame in Htg, Csig, Cty by lia.
        add_krange (EVar 75) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x822fc%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (foundD_run I R2 mq1 0x41324230%Z) end;
          [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS1 | exact Hf1 | exact HFS1
          | regv HR (24%bv:reg); exact H24
          | regv_lin HR (19%bv:reg); rewrite H19, ?u_small by lia; apply (f_equal (Z_to_bv 64)); lia
          | exact HF1 | exact Htg | exact Csig | exact Cty ]. }
      add_krange (EVar 75) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      pose proof HF1 as HF1'. destruct HF1' as (G1 & G2 & G2b & G3 & G4 & G5 & _).
      run_fp 30%nat [0x81018%Z] noscr false.
      (* [comment removed for export] *)
      call_gettag 0x41324231%Z (Z_to_bv 64 0x822d0) mq1 Hf1 G3 G5 H21 HR2z.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2). rewrite HR2c in Hfr. clear HR2c.
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      kframe HK Hfr [(SA (EVar 2) (-16), 16%Z); (SA (EVar 2) 192, 24%Z)].
      assert (Hf2 : frame_mod mem mq2 BIG) by (eapply frame_BIG_app; [exact Hf1 | exact Hfr | apply (gettag_big ceil regs mem rom ret sp data prio P len fs bs ch HE 192); cbn; tauto]).
      pose proof (saved_tag ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 ltac:(cbn; tauto) HS1 Hfr) as HS2.
      pose proof (DFACTS_tag _ _ 192 ltac:(cbn; tauto) HF1 Hfr) as HF2.
      pose proof (FSOK_tag ceil regs mem rom ret sp data prio P len fs bs ch HE _ _ 192 ltac:(cbn; tauto) HFS1 Hfr) as HFS2.
      clear Hfr.
      destruct Hr02 as [-> | ->].
      2:{ (* [comment removed for export] *)
        destruct (Htag2 eq_refl) as (Htg & Csig & Cty). rewrite !u_small_frame in Htg, Csig, Cty by lia.
        add_krange (EVar 139) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x822fc%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (foundD_run I R2 mq2 0x41324231%Z) end;
          [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS2 | exact Hf2 | exact HFS2
          | regv HR (24%bv:reg); exact H24
          | regv_lin HR (19%bv:reg); rewrite H19, ?u_small by lia; apply (f_equal (Z_to_bv 64)); lia
          | exact HF2 | exact Htg | exact Csig | exact Cty ]. }
      (* [comment removed for export] *)
      add_krange (EVar 139) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      run_fp 10%nat [0x82340%Z] noscr false.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
        apply (blockE_run ceil FP0 regs mem rom ret sp data prio P len fs bs ch HE Hgettag Hb2a psz tc h964 h965 0 raw
                 Htags R964 R965 ltac:(lia) I R2 mq2) end;
        [ common HR HFr H2 H3 H4 H21 H22 HFK | exact HS2 | exact Hf2 | exact HFS2
        | regv HR (24%bv:reg); exact H24
        | regv_lin HR (19%bv:reg); rewrite H19, ?u_small by lia; apply (f_equal (Z_to_bv 64)); lia
        | apply DFACTS_E; exact HF2 ].
    Qed.
  End Run.
End D.

(* [comment removed for export] *)
Lemma DFACTS_set965 : forall ceil regs (mem : word -> option byte) ret sp data prio P len fs bs ch,
  PENV ceil regs mem ret sp data prio P len fs bs ch ->
  forall psz tc h964 h965 raw v Mx My,
  DFACTS sp data P len psz tc h964 h965 raw Mx ->
  frame_mod Mx My [(Z_to_bv 64 (bv_unsigned P + 965), 1%Z)] ->
  cell8 SEGS My (bv_unsigned P + 965) v ->
  DFACTS sp data P len psz tc h964 v raw My.
Proof.
  intros ceil regs mem ret sp data prio P len fs bs ch HE psz tc h964 h965 raw v Mx My
         (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf C.
  pose proof (u64_range sp). pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
  unfold DFACTS. cbv zeta.
  split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F2b | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | solve_apart]|].
  split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | solve_apart]|].
  split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | solve_apart]|].
  split; [eapply cell8_frame; [exact Hf | exact F8 | lia | lia | solve_apart]|].
  split; [exact C|].
  eapply cell8_frame; [exact Hf | exact F10 | lia | lia | solve_apart].
Qed.

(* [comment removed for export] *)
Lemma DFACTS_set964 : forall ceil regs (mem : word -> option byte) ret sp data prio P len fs bs ch,
  PENV ceil regs mem ret sp data prio P len fs bs ch ->
  forall psz tc h964 h965 raw v Mx My,
  DFACTS sp data P len psz tc h964 h965 raw Mx ->
  frame_mod Mx My [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
  cell8 SEGS My (bv_unsigned P + 964) v ->
  DFACTS sp data P len psz tc v h965 raw My.
Proof.
  intros ceil regs mem ret sp data prio P len fs bs ch HE psz tc h964 h965 raw v Mx My
         (F1 & F2 & F2b & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf C.
  pose proof (u64_range sp). pose proof (u64_range P). pose proof (penv_nums ceil regs mem ret sp data prio P len fs bs ch HE) as NU. cbv zeta in NU.
  unfold DFACTS. cbv zeta.
  split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F2b | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | solve_apart]|].
  split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | solve_apart]|].
  split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | solve_apart]|].
  split; [exact C|].
  split; [eapply cell8_frame; [exact Hf | exact F9 | lia | lia | solve_apart]|].
  eapply cell8_frame; [exact Hf | exact F10 | lia | lia | solve_apart].
Qed.
