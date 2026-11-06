(* io_send_segs: the model-side pieces the segment files of the image-A walk of io_send share
   (lib/A/Prog/io_send_cg.v transport_io_send_cg_holds_stmt, entry 0x82d60 = TImgA.v ti_io_send timg_A).

   This file names no machine state and runs no code; it reads lib/TModel/TCb.v io_send_m only. It holds
   - the world the call runs on (ios_B0 Bw = set_g_fail_next Bw 0, the store at 0x82da4, :829) and the return
     value (ios_ret Bw: -EIO when bit 0 of the entry g_fail_next is set, else 0, :898);
   - that every check_* io_send calls but check_latest_sent leaves the world it was handed (ios_*_same), which is
     what the code's branch order needs: each world between two calls is ios_B0 Bw with the fields io_send itself
     stored;
   - the frame in flight (ios_fly, :883-889 = io_send_m's `fly`), the DATA arm's tail (ios_B6, :869-879) and the
     whole dispatch (ios_arm, :833-896) as definitions, with ios_m_arm: the statement's model premise
     io_send_m timg_A Bw frame = Some (Bw', r) gives check_sent_frame's model call at ios_B0 Bw, the dispatch
     ios_arm Bw frame = Some (Bw', tt) and r = ios_ret Bw;
   - one lemma per arm of the dispatch, reading ios_arm: ACK (ios_arm_ack), E3 (ios_arm_e3), a cmd byte that is
     none of the four (ios_arm_other), the retry arm (ios_arm_retry), E2 (ios_arm_e2) and DATA (ios_arm_data),
     and the three cases of the DATA tail (ios_B6_ka, ios_B6_sent, ios_B6_raw).
   Each gives the model calls the segment hands to the callees' contracts and the world it must leave. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TImgA.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* The checks that leave the world they were handed                    *)
(* ------------------------------------------------------------------ *)

Lemma ios_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

Ltac ios_fin H := first [ exact (ios_some_inv _ _ H) | exact (eq_sym (ios_some_inv _ _ H)) ].
Ltac ios_eq E := first [ exact E | reflexivity ].

Ltac ios_same H :=
  cbv zeta in H;
  repeat (match type of H with
          | context [if ?c then _ else _] => destruct c; cbv beta iota in H
          end);
  try discriminate H; ios_fin H.

Lemma ios_csf_same : forall B frame B', TC.check_sent_frame_m B frame = Some (B', tt) -> B' = B.
Proof. intros B frame B' H. unfold TC.check_sent_frame_m in H. ios_same H. Qed.

Lemma ios_caf_same : forall B frame B', TC.check_ack_frame_m B frame = Some (B', tt) -> B' = B.
Proof. intros B frame B' H. unfold TC.check_ack_frame_m in H. ios_same H. Qed.

Lemma ios_clc_same : forall B frame B', TC.check_latest_control_m B frame = Some (B', tt) -> B' = B.
Proof. intros B frame B' H. unfold TC.check_latest_control_m in H. ios_same H. Qed.

Lemma ios_cir_same : forall B frame B', TC.check_inflight_retry_m B frame = Some (B', tt) -> B' = B.
Proof. intros B frame B' H. unfold TC.check_inflight_retry_m in H. ios_same H. Qed.

Lemma ios_csw_same : forall B B', TC.check_state_wake_m B = Some (B', tt) -> B' = B.
Proof. intros B B' H. unfold TC.check_state_wake_m in H. ios_same H. Qed.

Lemma ios_cin_same : forall B B', TC.check_inflight_new_m B = Some (B', tt) -> B' = B.
Proof. intros B B' H. unfold TC.check_inflight_new_m in H. ios_same H. Qed.

Lemma ios_clf_same : forall B frame cmds B',
  TC.check_latest_frame_m B frame cmds = Some (B', tt) -> B' = B.
Proof. intros B frame cmds B' H. unfold TC.check_latest_frame_m in H. ios_same H. Qed.

Lemma ios_ckd_same : forall B B', TC.check_keepalive_due_m B = Some (B', tt) -> B' = B.
Proof. intros B B' H. unfold TC.check_keepalive_due_m in H. ios_same H. Qed.

Lemma ios_cld_same : forall B B', TC.check_latest_display_m B = Some (B', tt) -> B' = B.
Proof. intros B B' H. unfold TC.check_latest_display_m in H. ios_same H. Qed.

(* ------------------------------------------------------------------ *)
(* The worlds of the walk                                              *)
(* ------------------------------------------------------------------ *)

(* The world after the store of 0 at g_fail_next (0x82da4, :829): every call of the walk takes it. *)
Definition ios_B0 (Bw : list byte) : list byte := TW.set_g_fail_next Bw 0.

(* The return value (:898): the code tests bit 0 of the byte it read into s3. *)
Definition ios_ret (Bw : list byte) : Z := if TC.truth (TW.g_fail_next Bw) then - TC.EIO else 0.

(* min (len, SPEC_MAX_FRAME), the length the tail stores at M.fly.len and copies (:888). *)
Definition ios_flen (frame : list byte) : Z :=
  if Z.of_nat (length frame) <? TC.SPEC_MAX_FRAME then Z.of_nat (length frame) else TC.SPEC_MAX_FRAME.

(* The frame in flight (:883-889): io_send_m's `fly` at the world Bx. *)
Definition ios_fly (frame Bx : list byte) : list byte :=
  TW.set_M_fly_frame
    (TW.set_M_fly_len
       (TW.set_M_fly_sent
          (TW.set_M_fly_retries
             (TW.set_M_fly_counter
                (TW.set_M_fly_cmd (TW.set_M_fly_on Bx 1) (DSpec.sf_cmd (TC.rf frame)))
                (DSpec.sf_send (TC.rf frame)))
             0)
          (TW.g_now Bx))
       (ios_flen frame))
    (firstn (Z.to_nat (ios_flen frame)) frame).

(* f.body as a byte list, f.body_len, and the keepalive flag of :854. *)
Definition ios_body (frame : list byte) : list byte :=
  skipn (Z.to_nat (DSpec.sf_body (TC.rf frame))) frame.
Definition ios_blen (frame : list byte) : Z := DSpec.sf_body_len (TC.rf frame).
Definition ios_ka (frame : list byte) : bool :=
  ((ios_blen frame =? 1) && (DSpec.at8 (ios_body frame) 0 =? 0) &&
   (DSpec.sf_ncmds (TC.rf frame) =? 1))%bool.

(* The DATA arm's tail (:869-879): the keepalive case, the check_latest_sent case and the g_raw case. *)
Definition ios_B6 (frame : list byte) (B5 : list byte) : option (list byte * unit) :=
  if (negb (TC.truth (TW.g_raw B5)) && ios_ka frame)%bool then
    match TC.check_keepalive_due_m B5 with
    | None => None
    | Some (Bk, _) =>
        let nk := TS0.u64 (TW.M_next_ka Bk + TC.h_ms_m (TW.Cfg_keepalive_ms Bk)) in
        let Bk1 := TW.set_M_next_ka Bk nk in
        if nk <=? TW.g_now Bk1
        then Some (TW.set_M_next_ka Bk1 (TS0.u64 (TW.g_now Bk1 + TC.h_ms_m (TW.Cfg_keepalive_ms Bk1))), tt)
        else Some (Bk1, tt)
    end
  else if negb (TC.truth (TW.g_raw B5)) then
    match TC.check_latest_sent_m B5 (firstn (Z.to_nat (ios_blen frame)) (ios_body frame)) (ios_blen frame) with
    | None => None
    | Some (Bs, disp) =>
        if TC.truth disp then
          match TC.check_latest_display_m Bs with
          | None => None
          | Some (Bd, _) => Some (TW.set_M_last_display (TW.set_M_display_sent Bd 1) (TW.g_now Bd), tt)
          end
        else Some (Bs, tt)
    end
  else Some (B5, tt).

(* The dispatch (:833-896), at the world ios_B0 Bw check_sent_frame left. *)
Definition ios_arm (Bw frame : list byte) : option (list byte * unit) :=
  if DSpec.sf_cmd (TC.rf frame) =? TC.SPEC_CMD_ACK then
    match TC.int_inc (TW.GOT_acks (ios_B0 Bw)) with
    | None => None
    | Some a =>
        match TC.check_ack_frame_m (TW.set_GOT_acks (ios_B0 Bw) a) frame with
        | None => None
        | Some (B3, _) => TC.check_latest_control_m B3 frame
        end
    end
  else if ((DSpec.sf_cmd (TC.rf frame) =? TC.SPEC_CMD_E2) ||
           (DSpec.sf_cmd (TC.rf frame) =? TC.SPEC_CMD_DATA))%bool then
    if TC.truth (DSpec.sf_retry (TC.rf frame)) then
      match TC.check_inflight_retry_m (ios_B0 Bw) frame with
      | None => None
      | Some (B3, _) =>
          Some (TW.set_M_fly_sent (TW.set_M_fly_retries B3 (DSpec.u32 (TW.M_fly_retries B3 + 1)))
                  (TW.g_now B3), tt)
      end
    else if DSpec.sf_cmd (TC.rf frame) =? TC.SPEC_CMD_E2 then
      match TC.check_state_wake_m (ios_B0 Bw) with
      | None => None
      | Some (B3, _) =>
          match TC.check_latest_control_m B3 frame with
          | None => None
          | Some (B4, _) =>
              match TC.int_inc (TW.GOT_e2 B4) with
              | None => None
              | Some e2 =>
                  let B5 := TW.set_g_last_counter (TW.set_GOT_e2 B4 e2) (DSpec.sf_send (TC.rf frame)) in
                  if TC.truth (TW.g_fail_next Bw) then Some (B5, tt) else Some (ios_fly frame B5, tt)
              end
          end
      end
    else
      match TC.check_inflight_new_m (ios_B0 Bw) with
      | None => None
      | Some (B3, _) =>
          match (if (negb (TC.truth (TW.g_raw B3)) && negb (ios_ka frame))%bool
                 then TC.cmds_loop (S (Z.to_nat (ios_blen frame))) B3 (ios_body frame) (ios_blen frame) 0 0
                 else Some (DSpec.sf_ncmds (TC.rf frame))) with
          | None => None
          | Some cmds =>
              match TC.check_latest_frame_m B3 frame cmds with
              | None => None
              | Some (B4, _) =>
                  let B5 := TW.set_g_last_counter (TW.set_M_host_counter B4 (DSpec.sf_send (TC.rf frame)))
                              (DSpec.sf_send (TC.rf frame)) in
                  match ios_B6 frame B5 with
                  | None => None
                  | Some (B6, _) => Some (ios_fly frame B6, tt)
                  end
              end
          end
      end
  else if DSpec.sf_cmd (TC.rf frame) =? TC.SPEC_CMD_E3 then
    match TC.int_inc (TW.GOT_e3 (ios_B0 Bw)) with
    | None => None
    | Some e3 => TC.check_latest_control_m (TW.set_GOT_e3 (ios_B0 Bw) e3) frame
    end
  else Some (ios_B0 Bw, tt).

(* ------------------------------------------------------------------ *)
(* io_send_m = check_sent_frame, the dispatch, the return value        *)
(* ------------------------------------------------------------------ *)

Lemma ios_match_inv : forall (X : option (list byte * unit)) (ret : Z) (Bw' : list byte) (r : Z),
  match X with Some (B2, _) => Some (B2, ret) | None => None end = Some (Bw', r) ->
  X = Some (Bw', tt) /\ r = ret.
Proof.
  intros X ret Bw' r H. destruct X as [[B2 []]|]; [|discriminate H].
  injection H as H1 H2. split; [rewrite H1; reflexivity | symmetry; exact H2].
Qed.

Lemma ios_m_arm : forall Bw frame Bw' r,
  TC.io_send_m timg_A Bw frame = Some (Bw', r) ->
  TC.check_sent_frame_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) /\
  ios_arm Bw frame = Some (Bw', tt) /\ r = ios_ret Bw.
Proof.
  intros Bw frame Bw' r H.
  unfold TC.io_send_m in H. cbv zeta in H.
  destruct (TC.check_sent_frame_m (TW.set_g_fail_next Bw 0) frame) as [[B1 []]|] eqn:Ecsf; [|discriminate H].
  pose proof (ios_csf_same _ _ _ Ecsf) as EB1. subst B1.
  apply ios_match_inv in H. destruct H as [HA HR].
  split; [exact Ecsf|]. split; [exact HA | exact HR].
Qed.

(* ------------------------------------------------------------------ *)
(* The arms                                                            *)
(* ------------------------------------------------------------------ *)

Ltac ios_cmd_ne :=
  exfalso;
  unfold TC.SPEC_CMD_ACK, TC.SPEC_CMD_E2, TC.SPEC_CMD_E3, TC.SPEC_CMD_DATA in *; lia.

(* ACK (:833-836). *)
Lemma ios_arm_ack : forall Bw frame Bw',
  ios_arm Bw frame = Some (Bw', tt) ->
  DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_ACK ->
  exists a, TC.int_inc (TW.GOT_acks (ios_B0 Bw)) = Some a /\
            Bw' = TW.set_GOT_acks (ios_B0 Bw) a /\
            TC.check_ack_frame_m Bw' frame = Some (Bw', tt) /\
            TC.check_latest_control_m Bw' frame = Some (Bw', tt).
Proof.
  intros Bw frame Bw' H Hfc. unfold ios_arm in H.
  rewrite Hfc, Z.eqb_refl in H. cbv beta iota in H.
  destruct (TC.int_inc (TW.GOT_acks (ios_B0 Bw))) as [a|] eqn:Ea; [|discriminate H].
  destruct (TC.check_ack_frame_m (TW.set_GOT_acks (ios_B0 Bw) a) frame) as [[B3 []]|] eqn:E3; [|discriminate H].
  pose proof (ios_caf_same _ _ _ E3) as EB3. subst B3.
  pose proof (ios_clc_same _ _ _ H) as EB4. subst Bw'.
  exists a. split; [ios_eq Ea|]. split; [reflexivity|]. split; [ios_eq E3 | exact H].
Qed.

(* E3 (:891-893). *)
Lemma ios_arm_e3 : forall Bw frame Bw',
  ios_arm Bw frame = Some (Bw', tt) ->
  DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E3 ->
  exists e3, TC.int_inc (TW.GOT_e3 (ios_B0 Bw)) = Some e3 /\
             Bw' = TW.set_GOT_e3 (ios_B0 Bw) e3 /\
             TC.check_latest_control_m Bw' frame = Some (Bw', tt).
Proof.
  intros Bw frame Bw' H Hfc. unfold ios_arm in H. rewrite Hfc in H.
  change (TC.SPEC_CMD_E3 =? TC.SPEC_CMD_ACK) with false in H.
  change (TC.SPEC_CMD_E3 =? TC.SPEC_CMD_E2) with false in H.
  change (TC.SPEC_CMD_E3 =? TC.SPEC_CMD_DATA) with false in H.
  rewrite Z.eqb_refl in H. cbn [orb] in H. cbv beta iota in H.
  destruct (TC.int_inc (TW.GOT_e3 (ios_B0 Bw))) as [e3|] eqn:Ee; [|discriminate H].
  pose proof (ios_clc_same _ _ _ H) as EB. subst Bw'.
  exists e3. split; [ios_eq Ee|]. split; [reflexivity | exact H].
Qed.

(* A cmd byte that is none of the four (:895-896). *)
Lemma ios_arm_other : forall Bw frame Bw',
  ios_arm Bw frame = Some (Bw', tt) ->
  DSpec.sf_cmd (TC.rf frame) <> TC.SPEC_CMD_ACK ->
  DSpec.sf_cmd (TC.rf frame) <> TC.SPEC_CMD_E2 ->
  DSpec.sf_cmd (TC.rf frame) <> TC.SPEC_CMD_DATA ->
  DSpec.sf_cmd (TC.rf frame) <> TC.SPEC_CMD_E3 ->
  Bw' = ios_B0 Bw.
Proof.
  intros Bw frame Bw' H N1 N2 N3 N4. unfold ios_arm in H.
  rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3),
    (proj2 (Z.eqb_neq _ _) N4) in H.
  cbn [orb] in H. cbv beta iota in H. ios_fin H.
Qed.

(* The retry arm (:840-843). *)
Lemma ios_arm_retry : forall Bw frame Bw',
  ios_arm Bw frame = Some (Bw', tt) ->
  (DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 \/ DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA) ->
  TC.truth (DSpec.sf_retry (TC.rf frame)) = true ->
  TC.check_inflight_retry_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) /\
  Bw' = TW.set_M_fly_sent
          (TW.set_M_fly_retries (ios_B0 Bw) (DSpec.u32 (TW.M_fly_retries (ios_B0 Bw) + 1)))
          (TW.g_now (ios_B0 Bw)).
Proof.
  intros Bw frame Bw' H Hfc Hr. unfold ios_arm in H.
  destruct Hfc as [Hfc|Hfc]; rewrite Hfc in H;
    [ change (TC.SPEC_CMD_E2 =? TC.SPEC_CMD_ACK) with false in H;
      rewrite Z.eqb_refl in H; cbn [orb] in H
    | change (TC.SPEC_CMD_DATA =? TC.SPEC_CMD_ACK) with false in H;
      change (TC.SPEC_CMD_DATA =? TC.SPEC_CMD_E2) with false in H;
      rewrite Z.eqb_refl in H; cbn [orb] in H ];
  cbv beta iota in H; rewrite Hr in H; cbv beta iota in H;
  (destruct (TC.check_inflight_retry_m (ios_B0 Bw) frame) as [[B3 []]|] eqn:E3; [|discriminate H]);
  (pose proof (ios_cir_same _ _ _ E3) as EB3; subst B3);
  (split; [ios_eq E3 | ios_fin H]).
Qed.

(* E2 (:846-852). *)
Lemma ios_arm_e2 : forall Bw frame Bw',
  ios_arm Bw frame = Some (Bw', tt) ->
  DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_E2 ->
  TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
  TC.check_state_wake_m (ios_B0 Bw) = Some (ios_B0 Bw, tt) /\
  TC.check_latest_control_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) /\
  exists e2, TC.int_inc (TW.GOT_e2 (ios_B0 Bw)) = Some e2 /\
    (let B5 := TW.set_g_last_counter (TW.set_GOT_e2 (ios_B0 Bw) e2) (DSpec.sf_send (TC.rf frame)) in
     (TC.truth (TW.g_fail_next Bw) = true /\ Bw' = B5) \/
     (TC.truth (TW.g_fail_next Bw) = false /\ Bw' = ios_fly frame B5)).
Proof.
  intros Bw frame Bw' H Hfc Hr. unfold ios_arm in H. rewrite Hfc in H.
  change (TC.SPEC_CMD_E2 =? TC.SPEC_CMD_ACK) with false in H.
  rewrite Z.eqb_refl in H. cbn [orb] in H. cbv beta iota in H.
  rewrite Hr in H. cbv beta iota in H.
  destruct (TC.check_state_wake_m (ios_B0 Bw)) as [[B3 []]|] eqn:E3; [|discriminate H].
  pose proof (ios_csw_same _ _ E3) as EB3. subst B3.
  destruct (TC.check_latest_control_m (ios_B0 Bw) frame) as [[B4 []]|] eqn:E4; [|discriminate H].
  pose proof (ios_clc_same _ _ _ E4) as EB4. subst B4.
  destruct (TC.int_inc (TW.GOT_e2 (ios_B0 Bw))) as [e2|] eqn:Ee; [|discriminate H].
  cbv zeta in H.
  split; [ios_eq E3|]. split; [ios_eq E4|]. exists e2. split; [ios_eq Ee|]. cbv zeta.
  destruct (TC.truth (TW.g_fail_next Bw)) eqn:Hf; cbv beta iota in H.
  - left. split; [reflexivity | ios_fin H].
  - right. split; [reflexivity | ios_fin H].
Qed.

(* DATA (:853-889). *)
Lemma ios_arm_data : forall Bw frame Bw',
  ios_arm Bw frame = Some (Bw', tt) ->
  DSpec.sf_cmd (TC.rf frame) = TC.SPEC_CMD_DATA ->
  TC.truth (DSpec.sf_retry (TC.rf frame)) = false ->
  TC.check_inflight_new_m (ios_B0 Bw) = Some (ios_B0 Bw, tt) /\
  exists cmds,
    (if (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool
     then TC.cmds_loop (S (Z.to_nat (ios_blen frame))) (ios_B0 Bw) (ios_body frame) (ios_blen frame) 0 0
     else Some (DSpec.sf_ncmds (TC.rf frame))) = Some cmds /\
    TC.check_latest_frame_m (ios_B0 Bw) frame cmds = Some (ios_B0 Bw, tt) /\
    exists B6,
      ios_B6 frame (TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) (DSpec.sf_send (TC.rf frame)))
                      (DSpec.sf_send (TC.rf frame))) = Some (B6, tt) /\
      Bw' = ios_fly frame B6.
Proof.
  intros Bw frame Bw' H Hfc Hr. unfold ios_arm in H. rewrite Hfc in H.
  change (TC.SPEC_CMD_DATA =? TC.SPEC_CMD_ACK) with false in H.
  change (TC.SPEC_CMD_DATA =? TC.SPEC_CMD_E2) with false in H.
  rewrite Z.eqb_refl in H. cbn [orb] in H. cbv beta iota in H.
  rewrite Hr in H. cbv beta iota in H.
  destruct (TC.check_inflight_new_m (ios_B0 Bw)) as [[B3 []]|] eqn:E3; [|discriminate H].
  pose proof (ios_cin_same _ _ E3) as EB3. subst B3.
  split; [ios_eq E3|].
  destruct (if (negb (TC.truth (TW.g_raw (ios_B0 Bw))) && negb (ios_ka frame))%bool
            then TC.cmds_loop (S (Z.to_nat (ios_blen frame))) (ios_B0 Bw) (ios_body frame) (ios_blen frame) 0 0
            else Some (DSpec.sf_ncmds (TC.rf frame))) as [cmds|] eqn:Ec; [|discriminate H].
  exists cmds. split; [ios_eq Ec|].
  destruct (TC.check_latest_frame_m (ios_B0 Bw) frame cmds) as [[B4 []]|] eqn:E4; [|discriminate H].
  pose proof (ios_clf_same _ _ _ _ E4) as EB4. subst B4.
  split; [ios_eq E4|]. cbv zeta in H.
  destruct (ios_B6 frame (TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) (DSpec.sf_send (TC.rf frame)))
                            (DSpec.sf_send (TC.rf frame)))) as [[B6 []]|] eqn:E6; [|discriminate H].
  exists B6. split; [ios_eq E6 | ios_fin H].
Qed.

(* ------------------------------------------------------------------ *)
(* The three cases of the DATA tail                                    *)
(* ------------------------------------------------------------------ *)

(* keepalive (:869-873) *)
Lemma ios_B6_ka : forall frame B5 B6,
  ios_B6 frame B5 = Some (B6, tt) ->
  TC.truth (TW.g_raw B5) = false -> ios_ka frame = true ->
  TC.check_keepalive_due_m B5 = Some (B5, tt) /\
  (let nk := TS0.u64 (TW.M_next_ka B5 + TC.h_ms_m (TW.Cfg_keepalive_ms B5)) in
   let B51 := TW.set_M_next_ka B5 nk in
   (nk <=? TW.g_now B51) = true /\
     B6 = TW.set_M_next_ka B51 (TS0.u64 (TW.g_now B51 + TC.h_ms_m (TW.Cfg_keepalive_ms B51))) \/
   (nk <=? TW.g_now B51) = false /\ B6 = B51).
Proof.
  intros frame B5 B6 H Hraw Hka. unfold ios_B6 in H. rewrite Hraw, Hka in H.
  cbn [negb andb] in H. cbv beta iota in H.
  destruct (TC.check_keepalive_due_m B5) as [[Bk []]|] eqn:Ek; [|discriminate H].
  pose proof (ios_ckd_same _ _ Ek) as EBk. subst Bk.
  split; [ios_eq Ek|]. cbv zeta in H. cbv zeta.
  destruct (TS0.u64 (TW.M_next_ka B5 + TC.h_ms_m (TW.Cfg_keepalive_ms B5)) <=?
            TW.g_now (TW.set_M_next_ka B5 (TS0.u64 (TW.M_next_ka B5 + TC.h_ms_m (TW.Cfg_keepalive_ms B5)))))
    eqn:Hle; cbv beta iota in H.
  - left. split; [reflexivity | ios_fin H].
  - right. split; [reflexivity | ios_fin H].
Qed.

(* check_latest_sent and the display (:874-879) *)
Lemma ios_B6_sent : forall frame B5 B6,
  ios_B6 frame B5 = Some (B6, tt) ->
  TC.truth (TW.g_raw B5) = false -> ios_ka frame = false ->
  exists Bs disp,
    TC.check_latest_sent_m B5 (firstn (Z.to_nat (ios_blen frame)) (ios_body frame)) (ios_blen frame)
      = Some (Bs, disp) /\
    ((TC.truth disp = false /\ B6 = Bs) \/
     (TC.truth disp = true /\ TC.check_latest_display_m Bs = Some (Bs, tt) /\
      B6 = TW.set_M_last_display (TW.set_M_display_sent Bs 1) (TW.g_now Bs))).
Proof.
  intros frame B5 B6 H Hraw Hka. unfold ios_B6 in H. rewrite Hraw, Hka in H.
  cbn [negb andb] in H. cbv beta iota in H.
  destruct (TC.check_latest_sent_m B5 (firstn (Z.to_nat (ios_blen frame)) (ios_body frame)) (ios_blen frame))
    as [[Bs disp]|] eqn:Es; [|discriminate H].
  exists Bs, disp. split; [ios_eq Es|].
  destruct (TC.truth disp) eqn:Hd; cbv beta iota in H.
  - right. split; [reflexivity|].
    destruct (TC.check_latest_display_m Bs) as [[Bd []]|] eqn:Ed; [|discriminate H].
    pose proof (ios_cld_same _ _ Ed) as EBd. subst Bd.
    split; [ios_eq Ed | ios_fin H].
  - left. split; [reflexivity | ios_fin H].
Qed.

(* g_raw set: nothing between check_latest_frame and the tail (:874) *)
Lemma ios_B6_raw : forall frame B5 B6,
  ios_B6 frame B5 = Some (B6, tt) -> TC.truth (TW.g_raw B5) = true -> B6 = B5.
Proof.
  intros frame B5 B6 H Hraw. unfold ios_B6 in H. rewrite Hraw in H.
  cbn [negb andb] in H. cbv beta iota in H. ios_fin H.
Qed.
