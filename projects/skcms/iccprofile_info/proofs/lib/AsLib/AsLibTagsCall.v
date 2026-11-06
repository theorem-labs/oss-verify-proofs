(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
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

Section Lib.
Variable segs : list Segment.

Lemma writable_sub : forall mem lo n lo' n',
  writable segs mem lo n -> (lo <= lo')%Z -> (0 < n')%Z -> (lo' + n' <= lo + n)%Z ->
  writable segs mem lo' n'.
Proof.
  intros mem lo n lo' n' (W1 & W2 & W3 & W4) H1 H2 H3.
  split; [lia|]. split; [lia|]. split; [lia|].
  apply (store_ok_sub segs mem (Z_to_bv 64 lo) (Z_to_bv 64 lo') (Z.to_nat n) (Z.to_nat n'));
    rewrite ?u_small_frame by lia; rewrite ?Z2Nat.id by lia; try lia. exact W4.
Qed.

(* [comment removed for export] *)
Definition covered (rs big : list (word * Z)) : Prop :=
  Forall (fun r => Exists (fun b => (bv_unsigned (fst b) <= bv_unsigned (fst r))%Z /\
                                    (bv_unsigned (fst r) + snd r <= bv_unsigned (fst b) + snd b)%Z) big) rs.

Lemma outside_covered : forall a rs big, covered rs big -> outside a big -> outside a rs.
Proof.
  intros a rs big Hc. induction rs as [|[r n] rs IH]; cbn [outside]; intros Hout; [exact I|].
  apply Forall_cons_iff in Hc as [H1 H2]. split; [| apply IH; assumption].
  cbn [fst snd] in H1. clear IH H2. induction big as [|[b m] big IHb]; [inversion H1|].
  cbn [outside] in Hout. destruct Hout as [Hb Hrest].
  apply Exists_cons in H1 as [H1|H1]; [| apply IHb; assumption].
  cbn [fst snd] in H1. unfold in_rng in *. lia.
Qed.

Lemma frame_mod_of_covered : forall mem mem' rs big,
  covered rs big -> frame_mod mem mem' rs -> frame_mod mem mem' big.
Proof.
  intros mem mem' rs big Hc Hf. eapply frame_mod_weaken; [| exact Hf].
  intros a Ha. eapply outside_covered; eassumption.
Qed.

End Lib.

(* [comment removed for export] *)
Ltac solve_covered :=
  unfold covered; repeat (apply Forall_cons; [cbn [fst snd];
    first [ apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia ] |]);
  try apply Forall_nil.

(* [comment removed for export] *)
Ltac lift_to H Vt :=
  lazymatch type of H with
  | regs_ok (Env (vals_ev Vt) _) _ _ => idtac
  | fregs_ok (Env (vals_ev Vt) _) _ _ => idtac
  | regs_ok (Env (vals_ev ?V) ?B) ?sr ?R =>
      lazymatch Vt with
      | ?X ++ ?c =>
          lift_to H X;
          let H2 := fresh "Hl" in
          pose proof (env_app_regs X c B sr R ltac:(reflexivity) H) as H2; clear H; rename H2 into H
      end
  | fregs_ok (Env (vals_ev ?V) ?B) ?sfr ?FR =>
      lazymatch Vt with
      | ?X ++ ?c =>
          lift_to H X;
          let H2 := fresh "Hl" in
          pose proof (env_app_fregs X c B sfr FR ltac:(reflexivity) H) as H2; clear H; rename H2 into H
      end
  end.

(* [comment removed for export] *)
Ltac lift_hyp H :=
  unfold id in H;
  lazymatch type of H with
  | regs_ok ?E0 _ _ => try unfold E0 in H
  | fregs_ok ?E0 _ _ => try unfold E0 in H
  end;
  lazymatch goal with
  | HR : regs_ok (Env (vals_ev ?Vt) _) _ ?R |- runs_to _ (@mkst _ ?R _ _ _) _ => lift_to H Vt
  | HR : regs_ok (Env (vals_ev ?Vt) _) _ _ |- _ => lift_to H Vt
  end.

(* [comment removed for export] *)
Ltac add_krange_with HK e lo hi tac :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
      let H := fresh "HK" in
      assert (H : know_ok segs E M (KRange e lo hi :: kn));
      [ apply know_ok_cons; [| exact HK];
        apply krange_intro; cbn [edenot]; ev_simpl E; tac
      | clear HK; rename H into HK ]
  end.
Tactic Notation "add_krange" constr(e) constr(lo) constr(hi) "by" tactic3(tac) :=
  lazymatch goal with
  | HK : know_ok _ _ ?M _ |- runs_to _ (@mkst _ _ _ ?M _) _ => add_krange_with HK e lo hi tac
  end.
