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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs BoBase AsLibFrame AsLibTagsSpec AsLibTagsLib AsLibTagsCall BoLibTagXyz BoLibSpec.
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
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation XYZ := 0x815e0%Z.          (* [comment removed for export] *)

Section TO.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp T1 T2 T3 M data : word) (len : Z) (bs : list byte).

  Hypothesis Hxyz : tagxyz_contract_as SEGS as_both ceil.
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis HT1 : getr regs 10 = T1.
  Hypothesis HT2 : getr regs 11 = T2.
  Hypothesis HT3 : getr regs 12 = T3.
  Hypothesis HM : getr regs 13 = M.
  Hypothesis Hdok : as_data_ok ceil mem data len bs.
  Hypothesis HX1 : xtag_ok_bo SEGS ceil mem data len sp T1.
  Hypothesis HX2 : xtag_ok_bo SEGS ceil mem data len sp T2.
  Hypothesis HX3 : xtag_ok_bo SEGS ceil mem data len sp T3.
  Hypothesis HW : writable SEGS mem (bv_unsigned M) 36.
  Hypothesis HMal : (bv_unsigned M mod 4 = 0)%Z.
  Hypothesis HMrange : (appm (bv_unsigned M) 36 /\ (0 < bv_unsigned M)%Z) /\ (bv_unsigned M + 36 <= ceil)%Z.
  Hypothesis HMsh : shz mem (bv_unsigned M - bv_unsigned M mod 8) 5.
  Hypothesis HDM : (bv_unsigned data + len <= bv_unsigned M \/ bv_unsigned M + 36 <= bv_unsigned data)%Z.
  Hypothesis Hsb : as_sb SEGS as_both mem.
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 64 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hspal : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HWsp : writable SEGS mem (bv_unsigned sp - 64) 64.

  Definition BIG : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 64), 64%Z); (M, 36%Z)].

  (* [comment removed for export] *)
  Lemma pre_at : forall Mx (FP : FPState) R T (o1 o2 o3 s' : Z),
    frame_mod mem Mx BIG ->
    xtag_ok_bo SEGS ceil mem data len sp T ->
    getr R 10 = T ->
    getr R 11 = Z_to_bv 64 (bv_unsigned M + o1) ->
    getr R 12 = Z_to_bv 64 (bv_unsigned M + o2) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned M + o3) ->
    getr R 2 = Z_to_bv 64 s' ->
    (o1 = 0 \/ o1 = 4 \/ o1 = 8)%Z -> o2 = (o1 + 12)%Z -> o3 = (o1 + 24)%Z ->
    (s' = bv_unsigned sp - 48 \/ s' = bv_unsigned sp)%Z ->
    tagxyz_pre_as SEGS as_both ceil data len bs T (Z_to_bv 64 (bv_unsigned M + o1)) (Z_to_bv 64 (bv_unsigned M + o2))
               (Z_to_bv 64 (bv_unsigned M + o3)) FP R Mx.
  Proof using ceil mem rom sp M data len bs Hdok HW HMal HMrange HMsh HDM Hsb Hsprange Hspal HWsp.
    intros Mx FP R T o1 o2 o3 s' Hf (Hty & Htag & Htal & HTst & HTsh & HTsp) R10 R11 R12 R13 R2 Ho1 -> -> Hs'.
    pose proof (u64_range data). pose proof (u64_range T). pose proof (u64_range M). pose proof (u64_range sp).
    destruct Hdok as ((D1 & D2 & D3 & D4 & D5) & Dheap & Dal & Dsh). destruct HW as (W1 & W2 & W3 & W4). destruct HWsp as (S1 & S2 & S3 & S4).
    unfold XYZD50_DB in HTsp. unfold stackish, heapish in *. app_facts.
    assert (HM8 : (0 <= bv_unsigned M mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    unfold tagxyz_pre_as. cbv zeta.
    split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split.
    { split; [|split; [unfold heapish; exact Dheap| split; [exact Dal|]]].
      - eapply data_ok_frame; [exact Hf | exact (conj D1 (conj D2 (conj D3 (conj D4 D5)))) | unfold BIG; solve_apart].
      - eapply shdata_frame; [exact Hf | exact Dsh | lia | lia | lia |].
        unfold BIG, SB. assert (bv_unsigned data / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia).
        assert (len / 8 <= 2 ^ 23)%Z by (apply Z.div_le_upper_bound; lia). solve_apart. }
    split.
    { destruct Hty as [ty Hty]. exists ty. eapply cell32_frame; [exact Hf | exact Hty | lia | lia | unfold BIG; solve_apart]. }
    split.
    { eapply tag_ok_frame; [exact Hf | exact Htag | lia | lia | unfold BIG; solve_apart]. }
    split; [exact Htal|]. split; [unfold stackish; lia|].
    split.
    { eapply shz_frame; [exact Hf | exact HTsh | lia | lia |].
      unfold BIG, SB. assert (bv_unsigned T / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). solve_apart. }
    assert (FC : forall o, (0 <= o <= 32)%Z -> (o mod 4 = 0)%Z ->
              fcell_ok_as SEGS ceil Mx data len (Z_to_bv 64 (bv_unsigned M + o))).
    { intros o Ho Hom. unfold fcell_ok_as. cbv zeta. rewrite u_small_frame by lia.
      split.
      { eapply writable_frame; [exact Hf|].
        eapply writable_sub; [exact (conj W1 (conj W2 (conj W3 W4))) | lia | lia | lia]. }
      split; [lia|]. split; [unfold heapish; plc|]. split; [|lia].
      eapply shbyte_frame; [exact Hf | | lia |].
      - destruct HMsh as [_ Hz]. unfold shbyte.
        replace (SB + (bv_unsigned M + o) / 8)%Z with (SB + (bv_unsigned M - bv_unsigned M mod 8) / 8 + ((bv_unsigned M + o) / 8 - (bv_unsigned M - bv_unsigned M mod 8) / 8))%Z by lia.
        apply Hz. lia.
      - unfold BIG, SB. assert ((bv_unsigned M + o) / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). solve_apart. }
    split; [apply FC; lia|]. split; [apply FC; lia|]. split; [apply FC; lia|].
    split.
    { destruct Hsb as (got & cellp & G1 & G2 & Hsbc). exists got, cellp. split; [exact G1|]. split; [exact G2|].
      cbn in G1, G2. injection G1 as <- <-.
      eapply sbcell_frame; [exact Hf | exact Hsbc | lia | lia | lia | lia | unfold BIG; solve_apart | unfold BIG; solve_apart]. }
    exists (Z_to_bv 64 s'). split; [exact R2|]. split.
    - unfold as_frame, stackish. rewrite u_small_frame by lia. split; [lia|]. split.
      + destruct Hs' as [-> | ->]; [|exact Hspal]. lia.
      + eapply writable_frame; [exact Hf|]. eapply writable_sub; [exact (conj S1 (conj S2 (conj S3 S4))) | lia | lia | lia].
    - rewrite u_small_frame by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_frame : forall Mx My (o1 o2 o3 s' : Z),
    (o1 = 0 \/ o1 = 4 \/ o1 = 8)%Z -> o2 = (o1 + 12)%Z -> o3 = (o1 + 24)%Z ->
    (s' = bv_unsigned sp - 48 \/ s' = bv_unsigned sp)%Z ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 s') - 16), 16%Z);
                     (Z_to_bv 64 (bv_unsigned M + o1), 4%Z); (Z_to_bv 64 (bv_unsigned M + o2), 4%Z);
                     (Z_to_bv 64 (bv_unsigned M + o3), 4%Z)] ->
    frame_mod Mx My BIG.
  Proof using ceil mem rom sp M data HW HMal HMrange Hsprange Hspal HWsp.
    intros Mx My o1 o2 o3 s' Ho1 -> -> Hs' Hf. pose proof (u64_range M). pose proof (u64_range sp).
    destruct HW as (W1 & W2 & W3 & W4). destruct HWsp as (S1 & S2 & S3 & S4).
    rewrite (u_small_frame s') in Hf by lia.
    eapply frame_mod_of_covered; [| exact Hf]. unfold BIG. destruct Hs' as [-> | ->]; solve_covered.
  Qed.

  (* [comment removed for export] *)
  Lemma post_frame_call : forall Mx My (o1 o2 o3 : Z),
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) - 16), 16%Z);
                     (Z_to_bv 64 (bv_unsigned M + o1), 4%Z); (Z_to_bv 64 (bv_unsigned M + o2), 4%Z);
                     (Z_to_bv 64 (bv_unsigned M + o3), 4%Z)] ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp + - 64), 16%Z);
                     (Z_to_bv 64 (bv_unsigned M + o1), 4%Z); (Z_to_bv 64 (bv_unsigned M + o2), 4%Z);
                     (Z_to_bv 64 (bv_unsigned M + o3), 4%Z)].
  Proof using ceil rom sp M data HMrange Hsprange Hspal.
    intros Mx My o1 o2 o3 Hf. pose proof (u64_range sp).
    rewrite (u_small_frame (bv_unsigned sp - 48)) in Hf by lia.
    replace (bv_unsigned sp - 48 - 16)%Z with (bv_unsigned sp + -64)%Z in Hf by lia. exact Hf.
  Qed.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

  Definition kn0v1 : list kentry :=
    [KRange (EVar 2) (AS_STKLO + 64) (2^47);
     KRange (EVar 13) 1 (2 ^ 47 - 36);
     KAlign (EVar 13) 4;
     KWr (SA (EVar 2) (-48)) 48;
     KDisj (SA (EVar 2) (-48)) 48 (SA (EVar 13) 0) 36].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem rom sp M data bs Hsp HM HW HMal HMrange Hsprange Hspal HWsp.
    unfold kn0v1. pose proof (u64_range M). pose proof (u64_range sp).
    destruct HWsp as (S1 & S2 & S3 & S4). destruct HW as (W1 & W2 & W3 & W4).
    unfold know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply krange_intro; cbn. rewrite HM. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite HM. exact HMal.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-48) 48); cbn; try lia. exact Hsp.
      replace (bv_unsigned sp + -48)%Z with (bv_unsigned sp - 48)%Z by lia.
      apply (store_ok_sub SEGS mem (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 (bv_unsigned sp - 48)) (Z.to_nat 64) (Z.to_nat 48));
        rewrite ?u_small_frame by lia; try lia. exact S4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp, HM. lia.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KDisj (SA (EVar 13) 0) 36 ZSH ZSHL; KDisj (SA (EVar 13) 0) 36 ZIMG ZIMGL;
     KDisj (SA (EVar 13) 0) 36 (SA (EVar 2) (-48)) 48].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem rom sp M data len bs Hsp HM Hdok HW HMal HMrange Hsprange Hspal HWsp. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  Definition POST (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    frame_mod mem mem' BIG /\
    exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z.

  (* [comment removed for export] *)
  Ltac call_xyz Tn HXn o1 o2 o3 s' retw Hf :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R |- runs_to _ (@mkst ?I ?R _ ?Mx ?ro) _ =>
      eapply rt_call;
      [ eapply (Hxyz data len bs Tn _ _ _ I R Mx ro retw);
        [ regv HR (1%bv:reg); rewrite ?Hra; reflexivity
        | first [exact Hret | apply ret_ok_even; rewrite u_small by lia; reflexivity]
        | apply (pre_at Mx I R Tn o1 o2 o3 s' Hf HXn);
          [ regv HR (10%bv:reg); rewrite_getr; reflexivity
          | regv_lin HR (11%bv:reg); rewrite ?HM; f_equal; lia
          | regv_lin HR (12%bv:reg); rewrite ?HM; f_equal; lia
          | regv_lin HR (13%bv:reg); rewrite ?HM; f_equal; lia
          | first [regv_lin HR (2%bv:reg) | regv HR (2%bv:reg)]; rewrite ?Hsp; first [reflexivity | f_equal; lia | rewrite Z_to_bv_bv_unsigned; reflexivity]
          | lia | reflexivity | reflexivity | lia ] ]
      | cbv beta ]
    end.

  (* [comment removed for export] *)
  Ltac fin0 HR0 HF0 Hf :=
    fin_ret;
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
      exists FP2, R2, M2;
      split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
      lift_hyp HR0; lift_hyp HF0; unfold regs_kept, fregs_kept;
      split; [eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity]|];
      split; [eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity]|];
      unfold POST; split; [exact Hf | eexists; split; [regv HR (10%bv:reg); reflexivity | lia]]
    end.

  Lemma xyzd50_run :
    runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x83c78) mem rom)
      (fun st' => exists (FPI' : FPState) regs' mem',
          st' = mkst (FP:=FPI') regs' ret mem' rom /\
          regs_kept abi_kept regs regs' /\
          fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
          POST regs' mem').
  Proof using ceil FPI regs mem rom ret sp T1 T2 T3 M data len bs Hxyz Hra Hret Hsp HT1 HT2 HT3 HM Hdok HX1 HX2 HX3 HW HMal HMrange HMsh HDM Hsb Hsprange Hspal HWsp.
    pose proof (u64_range data) as Rd. pose proof (u64_range M) as RM. pose proof (u64_range sp) as Rsp.
    pose proof HW as HW'. destruct HW' as (W1 & W2 & W3 & W4). pose proof HWsp as HWsp'. destruct HWsp' as (S1 & S2 & S3 & S4).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof kn0_ok as HK.
    (* [comment removed for export] *)
    run_fp 30%nat [XYZ] noscr true.
    assert (Hf1 : frame_mod mem M0 BIG).
    { rewrite EQM. eapply frame_mod_of_covered;
        [| apply (frame_mod_mem_denot E mem _ [(SA (EVar 2) (-48), 48%Z)] HLF); [flats_auto | vm_compute; reflexivity]].
      unfold BIG, regions_denot. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp.
      unfold v_addi. solve_covered. }
    clear EQM HLF.
    (* [comment removed for export] *)
    call_xyz T1 HX1 0%Z 12%Z 24%Z (bv_unsigned sp - 48)%Z (Z_to_bv 64 0x83cd0) Hf1.
    intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. unfold tagxyz_post_as in Hfr.
    lazymatch goal with HR : regs_ok _ _ ?R |- _ =>
      assert (HR2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by (regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia);
      rewrite HR2 in Hfr; clear HR2 end.
    pose proof (post_frame _ _ 0 12 24 (bv_unsigned sp - 48) ltac:(lia) eq_refl eq_refl ltac:(lia) Hfr) as HfB.
    pose proof (post_frame_call _ _ 0 12 24 Hfr) as Hfr'.
    after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    know_frame HK Hfr' [(SA (EVar 2) (-64), 16%Z); (SA (EVar 13) 0, 4%Z); (SA (EVar 13) 12, 4%Z); (SA (EVar 13) 24, 4%Z)];
      [rewrite Hsp, HM; reflexivity|].
    pose proof (frame_mod_trans_same _ _ _ _ Hf1 HfB) as Hf2.
    clear Hfr Hfr' HfB Hf1.
    destruct Hr01 as [-> | ->].
    { add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      run_fp 30%nat [XYZ] noscr false.
      fin0 HR0 HF0 Hf2. }
    add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
    run_fp 30%nat [XYZ] noscr false.
    (* [comment removed for export] *)
    call_xyz T2 HX2 4%Z 16%Z 28%Z (bv_unsigned sp - 48)%Z (Z_to_bv 64 0x83d08) Hf2.
    intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. unfold tagxyz_post_as in Hfr.
    lazymatch goal with HR : regs_ok _ _ ?R |- _ =>
      assert (HR2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by (regv_lin HR (2%bv:reg); rewrite Hsp; f_equal; lia);
      rewrite HR2 in Hfr; clear HR2 end.
    pose proof (post_frame _ _ 4 16 28 (bv_unsigned sp - 48) ltac:(lia) eq_refl eq_refl ltac:(lia) Hfr) as HfB.
    pose proof (post_frame_call _ _ 4 16 28 Hfr) as Hfr'.
    after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
    know_frame HK Hfr' [(SA (EVar 2) (-64), 16%Z); (SA (EVar 13) 4, 4%Z); (SA (EVar 13) 16, 4%Z); (SA (EVar 13) 28, 4%Z)];
      [rewrite Hsp, HM; reflexivity|].
    pose proof (frame_mod_trans_same _ _ _ _ Hf2 HfB) as Hf3.
    clear Hfr Hfr' HfB Hf2.
    destruct Hr02 as [-> | ->].
    { add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      run_fp 30%nat [XYZ] noscr false.
      fin0 HR0 HF0 Hf3. }
    add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    run_fp 30%nat [XYZ] noscr false.
    call_xyz T3 HX3 8%Z 20%Z 32%Z (bv_unsigned sp) ret Hf3.
    intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & r3 & Hr3 & Hr03).
    unfold tagxyz_post_as in Hfr.
    lazymatch goal with HR : regs_ok _ _ ?R |- _ =>
      assert (HR2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp)) by (first [regv_lin HR (2%bv:reg) | regv HR (2%bv:reg)]; rewrite Hsp; first [rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]);
      rewrite HR2 in Hfr; clear HR2 end.
    pose proof (post_frame _ _ 8 20 32 (bv_unsigned sp) ltac:(lia) eq_refl eq_refl ltac:(lia) Hfr) as HfB.
    apply runs_to_here.
    lazymatch goal with
    | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2) |- _ =>
      exists FQ3, rq3, mq3;
      split; [reflexivity|];
      lift_hyp HR0; lift_hyp HF0; unfold regs_kept, fregs_kept in *;
      split; [intros r Hin; rewrite (Hkeep r Hin); revert r Hin;
              eapply (regs_same_on _ _ _ regs R2 abi_kept); [exact HR0 | exact HR | vm_compute; reflexivity]|];
      split; [intros r Hin; rewrite (Hfkeep r Hin); revert r Hin;
              eapply (fregs_same_on _ _ _ _ _ abi_fkept); [exact HF0 | exact HF | vm_compute; reflexivity]|]
    end.
    unfold POST. split.
    - eapply frame_mod_trans_same; [exact Hf3|]. exact HfB.
    - exists r3. split; [exact Hr3 | exact Hr03].
  Qed.
End TO.

Theorem xyzd50_as_from_tagxyz : forall ceil, tagxyz_contract_as SEGS as_both ceil -> xyzd50_contract_bo SEGS as_both ceil.
Proof.
  intros ceil Hxyz data len bs sp T1 T2 T3 M FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & HT1 & HT2 & HT3 & HM & Hdok & HX1 & HX2 & HX3 & HW & HMal & HMheap & HMsh & HDM & Hsb & Hfr).
  destruct Hfr as (Hstk & Hspal & HWsp). unfold XYZD50_DB in *.
  unfold heapish, stackish in HMheap, Hstk. app_facts.
  destruct (xyzd50_run ceil FPI regs mem rom ret sp T1 T2 T3 M data len bs Hxyz Hra Hret Hsp HT1 HT2 HT3 HM Hdok
              HX1 HX2 HX3 HW HMal ltac:(plc) HMsh HDM Hsb ltac:(plc) Hspal HWsp)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|]. exact Hpost.
Qed.

Theorem xyzd50_bo_ok : forall ceil, xyzd50_contract_bo SEGS as_both ceil.
Proof. intros ceil. exact (xyzd50_as_from_tagxyz ceil (tagxyz_bo_ok ceil)). Qed.
