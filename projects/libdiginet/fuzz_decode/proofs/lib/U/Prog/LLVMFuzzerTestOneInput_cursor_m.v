(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the model facts of one pass of the cursor loop of LLVMFuzzerTestOneInput
   (fuzz_decode.c:306-321) on the UBSan image, the pcs 0x12e18-0x12e88 (LLVMFuzzerTestOneInput_cursor.v walks them).
   A pass calls spec_msg_step (0x12e2c, contract over DgnSpec.spec_msg_step), diginet_msg_next (0x12e48, contract over
   DgnLib.msg_step), check_cursor_step (0x12e58) and, for a whole message, check_cursor_message (0x12e70). This file
   relates the two step models and gives the two checks their premises:
   - spec_msg_step_res: spec_msg_step over the body's bytes at a cursor (pos, st) is res_spec of msg_step at the same
     cursor: the same code, the same next position and running status, the same message fields;
   - msg_cells_dmsg: for a whole message, the 40 bytes diginet_msg_next leaves in a zeroed struct diginet_msg
     (msg_cells) are DgnLayout.dmsg_cells of the message the step describes (DgnAgreeCursor.msg_of_step);
   - cursor_check_step_ok / cursor_check_message_ok: the two checks hold of the pass (no abort), for every body and
     every cursor;
   - the ranges the contracts ask for (codes, status byte, the payload offset of a sysex). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import Cells.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness DgnAgreeCursor.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c diginet_msg_next_c
  DgnLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- the library's step as fuzz/spec.h's struct spec_msg ---- *)

(* the struct spec_msg a library step stands for: every field the step does not write is 0, as after the memset of
   spec.h:301; the running flag is the message's only for a whole message *)
Definition res_spec (r : msg_res) : spec_msg :=
  {| sm_code := mr_code r; sm_at := Z.of_nat (mr_start r); sm_len := Z.of_nat (mr_len r);
     sm_next := Z.of_nat (mr_pos r); sm_status := mr_status r;
     sm_running := if writes_status (mr_kind r) then mr_running r else 0;
     sm_d1 := mr_d1 r; sm_d2 := mr_d2 r; sm_status_out := mr_st r;
     sm_sysex_at := Z.of_nat (mr_sysex r); sm_sysex_len := Z.of_nat (mr_sysex_len r) |}.

Lemma nth_map_bz : forall (bb : list byte) i, nth i (map bz bb) 0 = bz (nth i bb (b8 0)).
Proof. induction bb as [|x bb IH]; intros [|i]; cbn; try reflexivity. apply IH. Qed.

Lemma byte_at_bz : forall bb k, byte_at (map bz bb) (Z.of_nat k) = at8 bb k.
Proof. intros bb k. unfold byte_at, at8. rewrite Nat2Z.id. apply nth_map_bz. Qed.

Lemma Forall_bz : forall bb, Forall (fun x => 0 <= x < 256) (map bz bb).
Proof.
  intros bb. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & _).
  pose proof (bz_range y). lia.
Qed.

Lemma skipn_nth_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros [|k] d H; cbn in H |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.

(* spec.h's F7 scan is the library's search for the first F7 *)
Lemma scan_find : forall bb fuel k, (k <= length bb)%nat -> (length bb - k <= fuel)%nat ->
  scan_f7 (map bz bb) (Z.of_nat (length bb)) (Z.of_nat k) fuel =
  Z.of_nat (match find_f7 (skipn k bb) with Some j => k + j | None => length bb end).
Proof.
  intros bb fuel. induction fuel as [|f IH]; intros k Hk Hf.
  - replace k with (length bb) by lia. rewrite skipn_all. reflexivity.
  - cbn [scan_f7]. destruct (Nat.eq_dec k (length bb)) as [->|Hne].
    + rewrite skipn_all. rewrite Z.ltb_irrefl. reflexivity.
    + replace (Z.of_nat k <? Z.of_nat (length bb)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (skipn_nth_cons bb k (b8 0)) by lia. cbn [find_f7 andb].
      rewrite byte_at_bz. unfold at8.
      destruct (bz (nth k bb (b8 0)) =? 247) eqn:E; cbn [negb]; cbv beta iota.
      * f_equal. lia.
      * replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
        rewrite IH by lia.
        destruct (find_f7 (skipn (S k) bb)); cbn [option_map]; cbv beta iota; [f_equal; lia | reflexivity].
Qed.

Lemma scan_find_at : forall bb pos, (pos < length bb)%nat ->
  scan_f7 (map bz bb) (Z.of_nat (length bb)) (Z.of_nat pos + 1)
    (Z.to_nat (Z.of_nat (length bb) - (Z.of_nat pos + 1))) =
  Z.of_nat (match find_f7 (skipn (S pos) bb) with Some j => S pos + j | None => length bb end).
Proof. intros bb pos H. replace (Z.of_nat pos + 1) with (Z.of_nat (S pos)) by lia. apply scan_find; lia. Qed.

(* boolean comparison outcomes, Z and nat, as arithmetic facts *)
Local Ltac cbools :=
  repeat match goal with
  | H : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in H
  | H : (_ =? _)%nat = false |- _ => apply Nat.eqb_neq in H
  | H : (_ <? _)%nat = true |- _ => apply Nat.ltb_lt in H
  | H : (_ <? _)%nat = false |- _ => apply Nat.ltb_ge in H
  | H : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in H
  | H : (_ <=? _)%nat = false |- _ => apply Nat.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H : (_ && _) = false |- _ => apply andb_false_iff in H as [?|?]
  | H : (_ || _) = true |- _ => apply orb_true_iff in H as [?|?]
  | H : (_ || _) = false |- _ => apply orb_false_iff in H as [? ?]
  end.

(* a leaf of the case analysis: the two records field by field *)
Local Ltac rfin :=
  unfold res_spec;
  cbn [mr_code mr_kind mr_start mr_pos mr_st mr_status mr_running mr_d1 mr_d2 mr_sysex mr_sysex_len mr_len
       writes_status mr_plain];
  f_equal; lia.

(* the channel-message tail, diginet_msg.c:83-102 against spec.h:339-359 *)
Local Ltac rchan :=
  match goal with
  | |- context [(Z.land ?s 240 =? 192) || (Z.land ?s 240 =? 208)] =>
      destruct ((Z.land s 240 =? 192) || (Z.land s 240 =? 208))
  end;
  cbn [Nat.eqb Z.eqb Pos.eqb andb orb negb]; cbv beta iota;
  rewrite <- ?byte_at_bz in *;
  rewrite ?Nat2Z.inj_succ in *; unfold Z.succ in *;
  split_ifs; cbools; rfin.

Lemma nat_leb_z : forall n m, (n <=? m)%nat = (Z.of_nat n <=? Z.of_nat m).
Proof. intros n m. destruct (Nat.leb_spec n m), (Z.leb_spec (Z.of_nat n) (Z.of_nat m)); try reflexivity; exfalso; lia. Qed.

(* One step of the library's cursor is the step of fuzz/spec.h, at every cursor. *)
Lemma spec_msg_step_res : forall bb pos st,
  spec_msg_step (map bz bb) (Z.of_nat (length bb)) (Z.of_nat pos) st = res_spec (msg_step bb pos st).
Proof.
  intros bb pos st.
  unfold spec_msg_step, msg_step, chan_step, chan_n. cbv beta zeta.
  unfold SPEC_E_TRUNCATED, SPEC_E_STATUS, SPEC_E_NO_STATUS.
  rewrite <- nat_leb_z.
  destruct (length bb <=? pos)%nat eqn:E0; [rfin|].
  apply Nat.leb_gt in E0.
  rewrite byte_at_bz.
  pose proof (at8_range bb pos) as Hx. change (2 ^ 8) with 256 in Hx.
  destruct (at8 bb pos =? 240) eqn:E1.
  - rewrite scan_find_at by exact E0.
    destruct (find_f7 (skipn (S pos) bb)) as [j|] eqn:F; cbv beta iota.
    + pose proof (find_f7_some _ _ F) as [Hj _]. rewrite length_skipn in Hj.
      replace (Z.of_nat (S pos + j) =? Z.of_nat (length bb)) with false by (symmetry; apply Z.eqb_neq; lia).
      rfin.
    + rewrite Z.eqb_refl. rfin.
  - apply Z.eqb_neq in E1.
    destruct (Z.ltb_spec 240 (at8 bb pos)) as [H2|H2].
    + replace (0xf0 <=? at8 bb pos) with true by (symmetry; apply Z.leb_le; lia). rfin.
    + replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.ltb_spec (at8 bb pos) 128) as [H3|H3].
      * replace (128 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
        cbn [andb]. destruct (st =? 0) eqn:E4; [rfin|].
        rchan.
      * replace (128 <=? at8 bb pos) with true by (symmetry; apply Z.leb_le; lia).
        cbn [andb]. rchan.
Qed.

(* the same with the contract's form of the bytes, map bv_unsigned *)
Lemma spec_msg_step_res_u : forall bb pos st,
  spec_msg_step (map bv_unsigned bb) (Z.of_nat (length bb)) (Z.of_nat pos) st = res_spec (msg_step bb pos st).
Proof. intros bb pos st. exact (spec_msg_step_res bb pos st). Qed.

(* ---- the two checks of a pass ---- *)

Lemma mr_code_cases : forall r, mr_code r = 0 \/ mr_code r = 1 \/ mr_code r = -6 \/ mr_code r = -7 \/ mr_code r = -8.
Proof. intros r. unfold mr_code. destruct (mr_kind r); auto. Qed.

Lemma mr_code_range : forall r, -8 <= mr_code r <= 1.
Proof. intros r. destruct (mr_code_cases r) as [E|[E|[E|[E|E]]]]; lia. Qed.

Lemma mr_code_1 : forall r, mr_code r = 1 -> mr_kind r = MkSysex \/ mr_kind r = MkChan.
Proof. intros r. unfold mr_code. destruct (mr_kind r); intros H; try discriminate H; auto. Qed.

(* check_cursor_step (fuzz_decode.c:41-91) of the pass at the cursor (pos, st): the step of spec.h, the library's
   result and the cursor after it *)
Lemma cursor_check_step_ok : forall bb pos st,
  check_cursor_step_ok (spec_msg_step (map bv_unsigned bb) (Z.of_nat (length bb)) (Z.of_nat pos) st)
    (mr_code (msg_step bb pos st))
    (DgnCursor (Z.of_nat (length bb)) (Z.of_nat (mr_pos (msg_step bb pos st))) (mr_st (msg_step bb pos st)))
  = true.
Proof.
  intros bb pos st. rewrite spec_msg_step_res_u.
  exact (check_cursor_step_ok_refl (res_spec (msg_step bb pos st)) (Z.of_nat (length bb))).
Qed.

(* case on every test of the step, keeping each outcome *)
Local Ltac step_cases :=
  repeat (match goal with
          | |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E
          | |- context [match ?x with Some _ => _ | None => _ end] => let E := fresh "F" in destruct x eqn:E
          end; cbv beta iota).

(* a step that is not a sysex leaves m->sysex at offset 0 *)
Lemma msg_step_sysex0 : forall bb pos st,
  mr_kind (msg_step bb pos st) <> MkSysex -> mr_sysex (msg_step bb pos st) = 0%nat.
Proof.
  intros bb pos st. unfold msg_step, chan_step.
  step_cases; cbn [mr_kind mr_sysex mr_plain]; intros H; congruence.
Qed.

(* m->sysex of a step: body + the payload offset for a sysex, else NULL *)
Lemma msg_step_sysex_ptr : forall bb pos st body,
  (if writes_sysex (mr_kind (msg_step bb pos st)) then body + Z.of_nat (mr_sysex (msg_step bb pos st)) else 0) =
  sysex_ptr body (Z.of_nat (mr_sysex (msg_step bb pos st))).
Proof.
  intros bb pos st body. unfold sysex_ptr.
  destruct (mr_kind (msg_step bb pos st)) eqn:K.
  all: try (rewrite (msg_step_sysex0 bb pos st) by (rewrite K; discriminate); reflexivity).
  cbn [writes_sysex]. destruct (msg_step_sysex bb pos st K) as (_ & -> & _).
  replace (Z.of_nat (S pos) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* the 40 bytes diginet_msg_next leaves for a whole message are the message the step describes *)
Lemma msg_cells_dmsg : forall bb pos st body mj, mr_code (msg_step bb pos st) = 1 ->
  msg_cells body mj (msg_step bb pos st) =
  dmsg_cells body (firstn 4 (skipn 4 mj)) (msg_of_step (res_spec (msg_step bb pos st))).
Proof.
  intros bb pos st body mj H1.
  pose proof (msg_step_sysex_ptr bb pos st body) as SP.
  unfold msg_cells, dmsg_cells, is_end, msg_of_step, res_spec.
  cbn [dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len dm_offset dm_len
       sm_status sm_running sm_d1 sm_d2 sm_sysex_at sm_sysex_len sm_at sm_len].
  rewrite SP.
  destruct (mr_code_1 _ H1) as [K|K]; rewrite K; reflexivity.
Qed.

(* check_cursor_message (fuzz_decode.c:93-115) of a pass whose step is a whole message *)
Lemma cursor_check_message_ok : forall bb pos st,
  check_cursor_message_ok (spec_msg_step (map bv_unsigned bb) (Z.of_nat (length bb)) (Z.of_nat pos) st)
    (msg_of_step (res_spec (msg_step bb pos st))) = true.
Proof.
  intros bb pos st. rewrite spec_msg_step_res_u. unfold check_cursor_message_ok. apply msg_agrees_of_step.
Qed.

(* ---- ranges ---- *)

Lemma msg_step_status_range : forall bb pos st, st_ok st -> 0 <= mr_status (msg_step bb pos st) < 256.
Proof.
  intros bb pos st Hs. unfold st_ok in Hs. pose proof (at8_range bb pos) as Hx. change (2 ^ 8) with 256 in Hx.
  unfold msg_step, chan_step.
  step_cases; cbn [mr_status mr_plain]; lia.
Qed.

(* a step whose status is F0 is a sysex: its payload starts at pos + 1, inside the body *)
Lemma msg_step_f0 : forall bb pos st, st_ok st -> mr_status (msg_step bb pos st) = 240 ->
  mr_sysex (msg_step bb pos st) = S pos /\ (S pos < length bb)%nat.
Proof.
  intros bb pos st Hs H.
  assert (K : mr_kind (msg_step bb pos st) = MkSysex).
  { unfold st_ok in Hs. pose proof (at8_range bb pos) as Hx. change (2 ^ 8) with 256 in Hx. revert H.
    unfold msg_step, chan_step.
    step_cases; cbools; cbn [mr_status mr_kind mr_plain]; intros; first [reflexivity | lia]. }
  destruct (msg_step_sysex bb pos st K) as (_ & S1 & S2 & _). split; [exact S1 | lia].
Qed.
