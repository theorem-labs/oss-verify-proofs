(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/simdjson/fuzz_parser/lib/SegP2/S2Entry.v, with its module paths and module names changed; 542 of its 560 lines of code are new or changed and 163 lines of the source are left out. *)
(* Lemmas of the walk of on_announce in the plain image (on_announce.v): the model after the first notice, the
   frame and notice cells on the stack, and the model facts the walk needs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb TSess TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import codec_cells diginet_announce_parse_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model of on_announce after its first notice (diginet_session.c:200-220) ---- *)
Definition oa_rest_m (I : timg) (F : option tframe) (B : list byte) (cmd off : Z) (ann : tann) (now : Z)
    : option (list byte * unit) :=
  if cmd =? DIGINET_CMD_ANNOUNCE then
    let B := set_S_foreign B 0 in
    let lost := if S_state B =? DIGINET_S_ONLINE
                then session_lost_m I F B DIGINET_R_DESK_OFFLINE else Some (B, tt) in
    match lost with
    | None => None
    | Some (B, _) =>
        if (S_state B =? DIGINET_S_IDLE) && negb (S_cfg_auto_wake B =? 0) then
          match diginet_session_wake_m I F B now with
          | None => None
          | Some (B, _) => Some (B, tt)
          end
        else Some (B, tt)
    end
  else if 0 <=? off then
    let B := set_S_foreign B 0 in
    let B := set_S_e1_named_us B 1 in
    maybe_online_m I F B
  else
    let B := set_S_foreign B 1 in
    let fn := Ntc DIGINET_N_FOREIGN (S_state B) 0 0 0 0 0 0 (Some ann) [] 0 in
    match call_notify I F B fn with
    | None => None
    | Some (B, _) =>
        if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
        then session_lost_m I F B DIGINET_R_FOREIGN else Some (B, tt)
    end.

(* the announce the notices carry *)
Definition oa_ann (body : list byte) : tann := TAnn (ann_field (skipn 15 body)) (ann_field (skipn 24 body)).

Lemma oa_unfold : forall I F B buf now, on_announce_m I F B buf now =
  if negb (ann_code (fr_cmd buf) (fr_body_len buf) =? DIGINET_OK) then
    Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt)
  else
    let p := TNeed.diginet_personality_from_name
               (firstn (copy_len 10 9 (skipn 24 (fr_body buf))) (skipn 24 (fr_body buf))) in
    let pv := match p with Some i => ti_personalities I + 24 * i | None => 0 end in
    let B := match p with Some _ => set_S_personality B pv | None => B end in
    let off := if fr_cmd buf =? DIGINET_CMD_ANNOUNCE_SESSION
               then find_mac_m (ann_unknown (fr_body buf)) 15 (S_cfg_host_mac B) else -1 in
    match call_notify I F B (Ntc DIGINET_N_DESK (S_state B) 0 0 0 0 off pv (Some (oa_ann (fr_body buf))) [] 0) with
    | None => None
    | Some (B, _) => oa_rest_m I F B (fr_cmd buf) off (oa_ann (fr_body buf)) now
    end.
Proof. reflexivity. Qed.

(* ---- memory helpers ---- *)

Lemma oa_cut : forall m A n l k, rw_cells rsegs m A [CB n l] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k l)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (n - k) (skipn k l)].
Proof.
  intros m A n l k [[Hwf Hb] Hw] Hk. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. destruct Hw as (W1 & W2 & W).
  rewrite <- (firstn_skipn k l) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min k (length l)) with k in B2 by lia.
  split; split; [split| |split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W. lia.
Qed.

Lemma oa_split : forall m A B cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.


Lemma oa_join : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma oa_bytes_sub : forall m A l k n, bytes_at rsegs m A l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hkn. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma oa_cell_bytes : forall m A cs k c, rw_cells rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [[Hwf Hb] _] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* the 1184-byte window and the world, the footprint of on_announce *)
Definition oa_W (sp : word) : list ivl :=
  [(bv_unsigned sp - 1184, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)].

Lemma oa_bytes_keep : forall m m' (sp : word) a bs, bytes_at rsegs m a bs -> munch (oa_W sp) m m' ->
  off_world a (Z.of_nat (length bs)) -> off_window sp 1184 a (Z.of_nat (length bs)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' sp a bs H MU OW OS. eapply bytes_at_transport; [exact H | exact MU |].
  unfold oa_W, off_world, off_window in *. cbn [disjoint_from]. lia.
Qed.

Lemma oa_tframe : forall m m' (sp sp' : word) K' TF,
  tframe_at m sp 1184 TF -> munch (oa_W sp) m m' ->
  bv_unsigned sp - 1184 <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' TF.
Proof.
  intros m m' sp sp' K' [fr|] H MU H1 H2; [|exact I].
  destruct H as (P & BA & OW & OS). split; [exact P|]. split; [eapply oa_bytes_keep; eassumption|].
  split; [exact OW|]. unfold off_window in *. lia.
Qed.

Lemma oa_relro : forall m m' (sp : word), TContract.relro_img m -> munch (oa_W sp) m m' ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 1184 -> TContract.relro_img m'.
Proof.
  intros m m' sp H MU Hs i Hi. unfold mrd. rewrite MU; [apply H; exact Hi|].
  unfold TContract.RELRO_BASE, TContract.RELRO_LEN in *. rewrite wa_unsigned by lia.
  unfold oa_W. cbn [outside]. unfold W_BASE_PLAIN, W_LEN in *. lia.
Qed.

Lemma oa_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* ---- model helpers ---- *)

Lemma oa_body_len : forall b, fr_code b = 0 ->
  0 <= fr_body_len b /\ 30 + fr_body_len b <= Z.of_nat (length b) /\
  length (fr_body b) = Z.to_nat (fr_body_len b).
Proof.
  intros b H. destruct (fr_code_ok b H) as (L & _ & N1 & N2).
  unfold fr_body, fr_body_len. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma oa_name_nul : forall bb old, In (codec_cells.b8 0) (ann_name bb old).
Proof.
  intros bb old. unfold ann_name, copy_strz. apply in_or_app. right. exact (in_eq _ _).
Qed.

(* the bytes copy_strz keeps hold no NUL, so cstring stops at the NUL it writes *)
Lemma oa_cstring_nz : forall n (l : list byte) rest,
  cstring (zb (firstn (nz_run (firstn n l)) l ++ DgnSpec.b8 0 :: rest)) = zb (firstn (nz_run (firstn n l)) l).
Proof.
  induction n as [|n IH]; intros [|x l] rest; try reflexivity.
  cbn [firstn nz_run].
  destruct (Z.eqb_spec (DgnSpec.bz x) 0) as [E|E]; [reflexivity|].
  cbn [firstn app]. unfold zb in *. cbn [map cstring].
  unfold DgnSpec.bz in E. apply Z.eqb_neq in E. rewrite E. f_equal. apply IH.
Qed.

Lemma oa_z_list_eqb : forall x y, z_list_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate H; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. subst b. f_equal. apply IH. exact H2.
Qed.

Lemma oa_from_name_z : forall z,
  (if list_eq_dec Z.eq_dec z NAME_C24 then PERS else if list_eq_dec Z.eq_dec z NAME_PC then PERS + 24 else 0) =
  match personality_name_find personalities 0 z with Some i => PERS + 24 * i | None => 0 end.
Proof.
  intros z.
  destruct (list_eq_dec Z.eq_dec z NAME_C24) as [E1|E1]; [subst z; reflexivity|].
  destruct (list_eq_dec Z.eq_dec z NAME_PC) as [E2|E2]; [subst z; reflexivity|].
  unfold personalities. cbn [personality_name_find dp_announce_name].
  repeat match goal with |- context [z_list_eqb z ?l] =>
    let H := fresh "H" in destruct (z_list_eqb z l) eqn:H;
    [apply oa_z_list_eqb in H; subst z; exfalso; first [apply E1; reflexivity | apply E2; reflexivity] |]
  end.
  reflexivity.
Qed.

Lemma oa_from_name : forall bb old,
  from_name_res (ann_name bb old) =
  match TNeed.diginet_personality_from_name (firstn (copy_len 10 9 (skipn 24 bb)) (skipn 24 bb)) with
  | Some i => PERS + 24 * i | None => 0 end.
Proof.
  intros bb old. unfold ann_name, copy_strz, from_name_res, TNeed.diginet_personality_from_name.
  change (copy_len 10 9 (skipn 24 bb)) with (nz_run (firstn 9 (skipn 24 bb))).
  rewrite oa_cstring_nz.
  exact (oa_from_name_z (zb (firstn (nz_run (firstn 9 (skipn 24 bb))) (skipn 24 bb)))).
Qed.

(* ---- notice: the GOT writes leave g_fail_next and the world length alone ---- *)

Definition oa_ok (X Y : list byte) : Prop := length Y = Z.to_nat W_LEN /\ g_fail_next Y = g_fail_next X.

Lemma oa_ok_refl : forall X, length X = Z.to_nat W_LEN -> oa_ok X X.
Proof. intros X H. split; [exact H | reflexivity]. Qed.

Lemma oa_ok_upd : forall X Y k v, oa_ok X Y -> OFF_GOT <= k -> k + 4 <= OFF_GOT + SZ_GOT ->
  oa_ok X (upd Y k (put 4 v)).
Proof.
  intros X Y k v [HL HF] H1 H2. unfold OFF_GOT, SZ_GOT in *. split.
  - rewrite length_upd_put; [exact HL | lia | rewrite HL; unfold W_LEN; lia].
  - rewrite <- HF. unfold g_fail_next, OFF_g_fail_next.
    apply u_at_upd_out; [lia | lia | lia | rewrite length_put, HL; unfold W_LEN; lia].
Qed.

Lemma oa_ok_fail : forall X Y, oa_ok X Y -> g_fail_next Y = g_fail_next X.
Proof. intros X Y [_ H]. exact H. Qed.

Ltac oa_crush :=
  repeat (cbv beta iota zeta; match goal with |- context [match ?c with _ => _ end] => destruct c end).

Lemma oa_online_same : forall X Y u, check_state_online_m X = Some (Y, u) -> Y = X.
Proof.
  intros X Y u. unfold check_state_online_m. oa_crush; intros H; try discriminate H.
  injection H; intros; subst; reflexivity.
Qed.

Lemma oa_desk_same : forall I F X n Y u, check_state_desk_m I F X n = Some (Y, u) -> Y = X.
Proof.
  intros I F X n Y u. unfold check_state_desk_m. oa_crush; intros H; try discriminate H.
  injection H; intros; subst; reflexivity.
Qed.

Ltac oa_kind :=
  repeat match goal with
  | |- context [?a =? ?b] =>
      match a with
      | DIGINET_N_STATE => idtac
      | DIGINET_N_DESK => idtac
      | DIGINET_N_FOREIGN => idtac
      end;
      let k := eval vm_compute in (a =? b) in change (a =? b) with k
  end.

Ltac oa_got HL :=
  apply oa_ok_fail;
  unfold set_GOT_n, set_GOT_t_reason, set_GOT_t_old, set_GOT_t_state, set_GOT_desk, set_GOT_foreign,
    A_GOT_n, A_GOT_t_reason, A_GOT_t_old, A_GOT_t_state, A_GOT_desk, A_GOT_foreign;
  repeat (apply oa_ok_upd; [| unfold OFF_GOT, SZ_GOT; lia | unfold OFF_GOT, SZ_GOT; lia]);
  apply oa_ok_refl; exact HL.

Lemma oa_notice_fail : forall I F B n B',
  length B = Z.to_nat W_LEN ->
  (n_kind n = DIGINET_N_DESK \/ n_kind n = DIGINET_N_STATE \/ n_kind n = DIGINET_N_FOREIGN) ->
  notice_m I F B n = Some (B', tt) -> g_fail_next B' = g_fail_next B.
Proof.
  intros I F B n B' HL Hk. unfold notice_m. cbv beta zeta.
  destruct Hk as [Hk|[Hk|Hk]]; rewrite Hk; oa_kind; cbv beta iota.
  - (* DESK *)
    destruct (int_inc (GOT_desk B)) as [d|]; cbv beta iota; intros H; [|discriminate H].
    apply oa_desk_same in H. subst B'. oa_got HL.
  - (* STATE *)
    destruct (GOT_n B <? TRANS_MAX) eqn:E1; [destruct (GOT_n B <? 0) eqn:E2|]; cbv beta iota;
      [intros H; discriminate H | |].
    + apply Z.ltb_lt in E1. apply Z.ltb_ge in E2. unfold TRANS_MAX in E1.
      destruct (int_inc (GOT_n B)) as [g1|]; cbv beta iota; [|intros H; discriminate H].
      destruct (n_state n =? S_ONLINE); intros H; [apply oa_online_same in H | injection H; intros]; subst B';
        oa_got HL.
    + destruct (int_inc (GOT_n B)) as [g1|]; cbv beta iota; [|intros H; discriminate H].
      destruct (n_state n =? S_ONLINE); intros H; [apply oa_online_same in H | injection H; intros]; subst B';
        oa_got HL.
  - (* FOREIGN *)
    destruct (int_inc (GOT_foreign B)) as [fo|]; cbv beta iota; intros H; [|discriminate H].
    injection H; intros; subst B'. oa_got HL.
Qed.

Lemma oa_memcmp6 : forall ls rs v, (6 <= length ls)%nat -> (6 <= length rs)%nat ->
  memcmp_model ls rs 6 = Some v -> (v =? 0) = memeq 6 ls rs.
Proof.
  intros ls rs v Hl Hr.
  destruct ls as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 ls]]]]]]; cbn [length] in Hl; try lia.
  destruct rs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 rs]]]]]]; cbn [length] in Hr; try lia.
  unfold memeq, DgnSpec.at8, DgnSpec.bz. cbn [memcmp_model forallb seq nth].
  repeat (match goal with |- context [bv_unsigned ?a =? bv_unsigned ?b] =>
            destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) end; cbn [andb]);
    intros H; injection H as <-; first [reflexivity | apply Z.eqb_neq; lia].
Qed.


(* ---- cells as bytes ---- *)

Lemma oa_rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma oa_forget : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge rsegs m A [] cs [] ) as M. rewrite app_nil_r in M.
  cbn [app] in M. apply M. exact H.
Qed.

(* ---- reading the fields of a byte list built of pieces ---- *)

Lemma oa_uat_app_r : forall (l1 l2 : list byte) k n, Z.of_nat (length l1) <= k ->
  u_at (l1 ++ l2) k n = u_at l2 (k - Z.of_nat (length l1)) n.
Proof.
  intros l1 l2 k n H. unfold u_at, sub. rewrite skipn_app.
  rewrite (skipn_all2 l1) by lia. cbn [app]. do 3 f_equal. lia.
Qed.

Lemma oa_uat_app_l : forall (l1 l2 : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length l1) ->
  u_at (l1 ++ l2) k n = u_at l1 k n.
Proof.
  intros l1 l2 k n H1 H2. unfold u_at, sub. rewrite skipn_app, firstn_app.
  rewrite length_skipn. replace (n - (length l1 - Z.to_nat k))%nat with O by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma oa_ble_zeros : forall n, bytes_le_to_Z (repeat (Z_to_bv 8 0) n) = 0.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat bytes_le_to_Z]. rewrite IH. reflexivity.
Qed.

Lemma oa_skipn_repeat : forall {A} (x : A) k j, skipn j (repeat x k) = repeat x (k - j).
Proof. intros A x k. induction k as [|k IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.

Lemma oa_firstn_repeat : forall {A} (x : A) k n, firstn n (repeat x k) = repeat x (Nat.min n k).
Proof. intros A x k. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma oa_uat_zeros : forall k j n, 0 <= j -> j + Z.of_nat n <= Z.of_nat k ->
  u_at (repeat (Z_to_bv 8 0) k) j n = 0.
Proof.
  intros k j n H1 H2. unfold u_at, sub. rewrite oa_skipn_repeat, oa_firstn_repeat. apply oa_ble_zeros.
Qed.

Lemma oa_swrap : forall v, -2^31 <= v < 2^31 -> bv_swrap 32 (v mod 2 ^ (8 * Z.of_nat 4)) = v.
Proof.
  intros v Hv. change (8 * Z.of_nat 4) with 32. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Ltac oa_len := rewrite ?length_app, ?length_put, ?repeat_length, ?length_le8, ?length_le4; cbn [length Nat.add]; lia.

(* peel u_at / s32_at of a concatenation down to one piece *)
Ltac oa_peel :=
  unfold s32_at;
  repeat match goal with
  | |- context [u_at (?l1 ++ ?l2) ?k ?n] =>
      first [ rewrite (oa_uat_app_r l1 l2 k n) by oa_len
            | rewrite (oa_uat_app_l l1 l2 k n) by oa_len ]
  end;
  rewrite ?length_put, ?repeat_length, ?length_app, ?length_le8, ?length_le4;
  match goal with |- context [u_at ?l ?k ?n] => let k' := eval vm_compute in k in change k with k' end.

Ltac oa_field :=
  lazymatch goal with |- @eq Z _ _ => idtac end;
  oa_peel;
  first [ rewrite u_at_put; first [ apply oa_swrap; lia | apply Z.mod_small; lia | reflexivity | (vm_compute; reflexivity) ]
        | rewrite oa_uat_zeros by lia; first [reflexivity | (vm_compute; reflexivity)]
        | (vm_compute; reflexivity) ].

(* ---- the world: an 8-byte store over two 4-byte fields ---- *)

Lemma oa_upd_app : forall (B l1 l2 : list byte) k, 0 <= k ->
  (Z.to_nat k + length l1 + length l2 <= length B)%nat ->
  upd B k (l1 ++ l2) = upd (upd B k l1) (k + Z.of_nat (length l1)) l2.
Proof.
  intros B l1 l2 k Hk HL. unfold upd.
  replace (Z.to_nat (k + Z.of_nat (length l1))) with (Z.to_nat k + length l1)%nat by lia.
  remember (Z.to_nat k) as K eqn:EK. clear EK Hk.
  assert (E1 : firstn (K + length l1) (firstn K B ++ l1 ++ skipn (K + length l1) B) = firstn K B ++ l1).
  { rewrite app_assoc. rewrite firstn_app. rewrite length_app, length_firstn.
    replace (Nat.min K (length B)) with K by lia. rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
    apply firstn_all2. rewrite length_app, length_firstn. lia. }
  assert (E2 : skipn (K + length l1 + length l2) (firstn K B ++ l1 ++ skipn (K + length l1) B) =
               skipn (K + (length l1 + length l2)) B).
  { rewrite app_assoc. rewrite skipn_app. rewrite length_app, length_firstn.
    replace (Nat.min K (length B)) with K by lia.
    rewrite skipn_all2 by (rewrite length_app, length_firstn; lia). cbn [app].
    rewrite skipn_skipn. f_equal. lia. }
  rewrite E1, E2. rewrite length_app. rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- small facts ---- *)

Lemma oa_zxb : forall c, 0 <= c < 256 -> zxb (DgnSpec.b8 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold zxb, DgnSpec.b8. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma oa_cmd_range : forall b, 0 <= fr_cmd b < 2^8.
Proof.
  intros b. unfold fr_cmd, at8, DgnSpec.bz. pose proof (bv_unsigned_in_range 8 (nth 28 b (DgnSpec.b8 0))) as H.
  unfold bv_modulus in H. exact H.
Qed.

Lemma oa_cmd_ok : forall cmd blen, ann_code cmd blen = 0 ->
  (cmd = DIGINET_CMD_ANNOUNCE \/ cmd = DIGINET_CMD_ANNOUNCE_SESSION) /\ 33 <= blen.
Proof.
  intros cmd blen. unfold ann_code, ann_cmd, DIGINET_CMD_ANNOUNCE, DIGINET_CMD_ANNOUNCE_SESSION.
  destruct (Z.eqb_spec cmd 0xe0); destruct (Z.eqb_spec cmd 0xe1); cbn [orb negb];
    destruct (Z.ltb_spec blen 33); intros Hc; try discriminate Hc; lia.
Qed.

Lemma oa_pfn_range : forall name i, TNeed.diginet_personality_from_name name = Some i -> i = 0 \/ i = 1.
Proof.
  intros name i. unfold TNeed.diginet_personality_from_name, personalities. cbn [personality_name_find].
  destruct (z_list_eqb _ _); [intros H; injection H; lia|].
  destruct (z_list_eqb _ _); [intros H; injection H; lia|]. intros H; discriminate H.
Qed.

Lemma oa_memcmp_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H; cbn in H; [injection H; lia|].
  destruct l as [|a l]; [discriminate H|]. destruct r as [|c r]; [discriminate H|].
  destruct (bv_unsigned a =? bv_unsigned c); [eapply IH; exact H|].
  injection H as <-. pose proof (bv_unsigned_in_range 8 a). pose proof (bv_unsigned_in_range 8 c).
  unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.





(* ---- struct diginet_notice built on the stack ---- *)

Lemma oa_ntc_mk : forall m p n (spc : word) K NB,
  bytes_at rsegs m p NB -> length NB = 72%nat ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window spc K p 72 -> 0 <= bv_unsigned spc - K ->
  s32_at NB 0 = n_kind n -> s32_at NB 4 = n_state n -> s32_at NB 8 = n_old n -> s32_at NB 12 = n_reason n ->
  u_at NB 32 8 = n_pers n -> s32_at NB 40 = n_mac_offset n -> u_at NB 56 8 = n_body_len n ->
  u_at NB 64 4 = n_counter n -> u_at NB 68 2 = n_retry n -> u_at NB 48 8 = 0 -> n_body n = [] ->
  match n_ann n with
  | None => u_at NB 24 8 = 0
  | Some a =>
      0 < u_at NB 24 8 /\ u_at NB 24 8 mod 8 = 0 /\
      bytes_at rsegs m (u_at NB 24 8) (ta_version a) /\ bytes_at rsegs m (u_at NB 24 8 + 10) (ta_name a) /\
      off_world (u_at NB 24 8) 20 /\ off_window spc K (u_at NB 24 8) 20
  end ->
  ntc_at m p n spc K.
Proof.
  intros m p n spc K NB HB HL P1 P2 P3 P4 P5 F0 F4 F8 F12 F32 F40 F56 F64 F68 F48 NBd HA.
  unfold ntc_at. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
  exists NB. split; [exact HB|]. split; [exact HL|].
  repeat (split; [assumption|]). rewrite F48, NBd. split; [apply bytes_at_nil; lia|].
  split; [unfold off_world, W_BASE_PLAIN; cbn; lia|]. split; [unfold off_window; cbn; lia|]. exact HA.
Qed.

Ltac oa_cells_bytes H :=
  let B := fresh "NBb" in
  pose proof (oa_rw_bytes _ _ _ H) as B; cbn [cells_bytes cbytes] in B;
  rewrite ?le4_put, ?le8_put, ?app_nil_r in B.

Lemma oa_bytes_join : forall m p l1 l2 q, bytes_at rsegs m p l1 -> bytes_at rsegs m q l2 ->
  q = p + Z.of_nat (length l1) -> bytes_at rsegs m p (l1 ++ l2).
Proof. intros m p l1 l2 q H1 H2 ->. apply bytes_at_app. split; assumption. Qed.

(* the DESK notice of on_announce (diginet_session.c:196-197) *)
Lemma oa_ntc_desk : forall m (spc : word) K p st fpv ap pv off ann,
  rw_cells rsegs m p [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 st); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 fpv);
                      C8 (Z_to_bv 64 ap); C8 (Z_to_bv 64 pv); C4 (Z_to_bv 64 off)] ->
  rw_cells rsegs m (p + 44) [CB 28 (repeat (Z_to_bv 8 0) 28)] ->
  -2^31 <= st < 2^31 -> -2^31 <= off < 2^31 -> 0 <= pv < 2^64 -> 0 <= ap < 2^64 ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window spc K p 72 -> 0 <= bv_unsigned spc - K ->
  0 < ap -> ap mod 8 = 0 -> bytes_at rsegs m ap (ta_version ann) -> bytes_at rsegs m (ap + 10) (ta_name ann) ->
  off_world ap 20 -> off_window spc K ap 20 ->
  ntc_at m p (Ntc DIGINET_N_DESK st 0 0 0 0 off pv (Some ann) [] 0) spc K.
Proof.
  intros m spc K p st fpv ap pv off ann H1 H2 Hst Hoff Hpv Hap P1 P2 P3 P4 P5 A1 A2 A3 A4 A5 A6.
  oa_cells_bytes H1. oa_cells_bytes H2.
  eapply oa_ntc_mk; [eapply oa_bytes_join; [exact NBb | exact NBb0 | rewrite ?length_app, ?length_put; reflexivity]
                    | rewrite ?length_app, ?length_put, ?repeat_length; reflexivity | exact P1 | exact P2 | exact P3
                    | exact P4 | exact P5 | .. ]; cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len
                      n_counter n_retry n_body n_ann]; try reflexivity;
    try (lazymatch goal with |- @eq Z _ _ => unfold DIGINET_N_DESK; oa_field end).
  match goal with |- context [u_at ?NB 24 8] => assert (U : u_at NB 24 8 = ap) by oa_field; rewrite U end.
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 A6))))).
Qed.


(* the strings of the announce as the notice reads them (TSess.v ann_field) are prefixes of the 10-byte fields
   diginet_announce_parse wrote (DgnSpec.v ann_version / ann_name) *)
Lemma oa_field_prefix : forall src old,
  copy_strz 10 9 src old = ann_field src ++ skipn (S (copy_len 10 9 src)) old.
Proof. intros src old. unfold copy_strz, ann_field. rewrite <- app_assoc. reflexivity. Qed.

Lemma oa_ann_bytes : forall m A bodyaddr body aj,
  rw_cells rsegs m A (ann_cells bodyaddr body aj) ->
  bytes_at rsegs m A (ta_version (oa_ann body)) /\ bytes_at rsegs m (A + 10) (ta_name (oa_ann body)).
Proof.
  intros m A bodyaddr body aj H. unfold ann_cells in H.
  pose proof (oa_cell_bytes m A _ 0 _ H eq_refl) as V. pose proof (oa_cell_bytes m A _ 10 _ H eq_refl) as N.
  cbn [cbytes] in V, N. replace (A + Z.of_nat 0) with A in V by lia. change (Z.of_nat 10) with 10 in N.
  unfold ann_version, ann_name in V, N. rewrite oa_field_prefix in V, N.
  apply bytes_at_app in V. apply bytes_at_app in N. cbn [ta_version ta_name oa_ann]. split; [exact (proj1 V) | exact (proj1 N)].
Qed.


Lemma oa_ltz : forall v, -2^63 <= v < 2^63 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_r. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec v 0) as [L|L].
  - apply Z.leb_le. rewrite <- (Z.mod_add v 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
  - apply Z.leb_gt. rewrite Z.mod_small by lia. lia.
Qed.

Lemma oa_len_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd B k v) = Z.to_nat W_LEN.
Proof. intros B v k HL H1 H2. rewrite length_upd; [exact HL | lia | rewrite HL; unfold W_LEN in *; lia]. Qed.

Lemma oa_gf_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd B k v) = g_fail_next B.
Proof.
  intros B v k HL H1 H2 H3. unfold g_fail_next. apply u_at_upd_out; [lia | unfold OFF_g_fail_next; lia | cbn; lia |].
  rewrite HL. unfold W_LEN in *. lia.
Qed.


Lemma oa_put8_e1 : put 8 4294967296 = put 4 0 ++ put 4 1.
Proof.
  unfold put. cbn [Z_to_le_bytes app].
  repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity.
Qed.


Lemma oa_mod64 : forall v, -2^63 <= v < 2^63 -> v mod 2^64 = if v <? 0 then v + 2^64 else v.
Proof.
  intros v Hv. destruct (Z.ltb_spec v 0).
  - rewrite <- (Z.mod_add v 1 (2^64)) by lia. apply Z.mod_small. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma oa_eqb : forall v k, -2^63 <= v < 2^63 -> -2^63 <= k < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap. rewrite (oa_mod64 v Hv), (oa_mod64 k Hk).
  destruct (Z.ltb_spec v 0); destruct (Z.ltb_spec k 0); cbv beta iota;
    destruct (Z.eqb_spec v k); first [ reflexivity | exfalso; lia | apply (proj2 (Z.eqb_eq _ _)); lia | apply (proj2 (Z.eqb_neq _ _)); lia ].
Qed.


(* the STATE notice of session_lost's set_state (IDLE, DESK_OFFLINE) from ONLINE, as the e0 branch builds it:
   sd 2 (kind STATE, state IDLE), sd 2 + (3 << 32) (old ONLINE, reason DESK_OFFLINE), the rest zero *)
Lemma oa_ntc_e0 : forall m (spc : word) K p,
  rw_cells rsegs m p [C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 12884901890)] ->
  rw_cells rsegs m (p + 16) [CB 56 (repeat (Z_to_bv 8 0) 56)] ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window spc K p 72 -> 0 <= bv_unsigned spc - K ->
  ntc_at m p (Ntc DIGINET_N_STATE DIGINET_S_IDLE 2 DIGINET_R_DESK_OFFLINE 0 0 0 0 None [] 0) spc K.
Proof.
  intros m spc K p H1 H2 P1 P2 P3 P4 P5.
  oa_cells_bytes H1. oa_cells_bytes H2.
  eapply oa_ntc_mk; [eapply oa_bytes_join; [exact NBb | exact NBb0 | rewrite ?length_app, ?length_put; reflexivity]
                    | rewrite ?length_app, ?length_put, ?repeat_length; reflexivity | exact P1 | exact P2 | exact P3
                    | exact P4 | exact P5 | .. ]; cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len
                      n_counter n_retry n_body n_ann]; try reflexivity;
    try (lazymatch goal with |- @eq Z _ _ => vm_compute; reflexivity end).
Qed.


(* the FOREIGN notice (diginet_session.c:217) *)
Lemma oa_ntc_fg : forall m (spc : word) K p st (w : word) ap ann,
  rw_cells rsegs m p [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 st); C8 (Z_to_bv 64 0); C8 w; C8 (Z_to_bv 64 ap)] ->
  rw_cells rsegs m (p + 32) [CB 40 (repeat (Z_to_bv 8 0) 40)] ->
  -2^31 <= st < 2^31 -> 0 <= ap < 2^64 ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window spc K p 72 -> 0 <= bv_unsigned spc - K ->
  0 < ap -> ap mod 8 = 0 -> bytes_at rsegs m ap (ta_version ann) -> bytes_at rsegs m (ap + 10) (ta_name ann) ->
  off_world ap 20 -> off_window spc K ap 20 ->
  ntc_at m p (Ntc DIGINET_N_FOREIGN st 0 0 0 0 0 0 (Some ann) [] 0) spc K.
Proof.
  intros m spc K p st w ap ann H1 H2 Hst Hap P1 P2 P3 P4 P5 A1 A2 A3 A4 A5 A6.
  oa_cells_bytes H1. oa_cells_bytes H2.
  eapply oa_ntc_mk; [eapply oa_bytes_join; [exact NBb | exact NBb0 | rewrite ?length_app, ?length_put, ?length_le8; reflexivity]
                    | rewrite ?length_app, ?length_put, ?length_le8, ?repeat_length; reflexivity | exact P1 | exact P2
                    | exact P3 | exact P4 | exact P5 | .. ]; cbn [n_kind n_state n_old n_reason n_pers n_mac_offset
                      n_body_len n_counter n_retry n_body n_ann]; try reflexivity;
    try (lazymatch goal with |- @eq Z _ _ => unfold DIGINET_N_FOREIGN; oa_field end).
  match goal with |- context [u_at ?NB 24 8] => assert (U : u_at NB 24 8 = ap) by oa_field; rewrite U end.
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 A6))))).
Qed.

(* the STATE notice of session_lost's set_state (IDLE, FOREIGN) from state st, as the e1 branch builds it:
   sd 2 (kind STATE, state IDLE), sw st (old), sw 5 (reason FOREIGN), the rest zero *)
Lemma oa_ntc_fgst : forall m (spc : word) K p st,
  rw_cells rsegs m p [C8 (Z_to_bv 64 2); C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 5)] ->
  rw_cells rsegs m (p + 16) [CB 56 (repeat (Z_to_bv 8 0) 56)] ->
  -2^31 <= st < 2^31 ->
  0 < p -> p mod 8 = 0 -> off_world p 72 -> off_window spc K p 72 -> 0 <= bv_unsigned spc - K ->
  ntc_at m p (Ntc DIGINET_N_STATE DIGINET_S_IDLE st DIGINET_R_FOREIGN 0 0 0 0 None [] 0) spc K.
Proof.
  intros m spc K p st H1 H2 Hst P1 P2 P3 P4 P5.
  oa_cells_bytes H1. oa_cells_bytes H2.
  eapply oa_ntc_mk; [eapply oa_bytes_join; [exact NBb | exact NBb0 | rewrite ?length_app, ?length_put; reflexivity]
                    | rewrite ?length_app, ?length_put, ?repeat_length; reflexivity | exact P1 | exact P2 | exact P3
                    | exact P4 | exact P5 | .. ]; cbn [n_kind n_state n_old n_reason n_pers n_mac_offset n_body_len
                      n_counter n_retry n_body n_ann]; try reflexivity;
    try (lazymatch goal with |- @eq Z _ _ => unfold DIGINET_N_STATE, DIGINET_S_IDLE, DIGINET_R_FOREIGN; oa_field end).
Qed.


(* lw s1, state; addiw a0, s1, -1; bltu 1, a0: the session is neither WAKING (1) nor ONLINE (2) *)
Lemma oa_fgcond : forall st, -2^31 <= st < 2^31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 st) + -1))) =
  negb ((st =? DIGINET_S_ONLINE) || (st =? DIGINET_S_WAKING)).
Proof.
  intros st Hst. unfold DIGINET_S_ONLINE, DIGINET_S_WAKING.
  destruct (Z.eqb_spec st 2) as [E2|E2]; [subst; vm_compute; reflexivity|].
  destruct (Z.eqb_spec st 1) as [E1|E1]; [subst; vm_compute; reflexivity|].
  cbn [orb negb]. unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_lt.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.


(* find_mac's memcmp of 6 bytes reads only the first 6 bytes of either side *)
Lemma oa_memeq6 : forall x y, memeq 6 (firstn 6 x) y = memeq 6 x y.
Proof. intros x y. unfold memeq. cbn [seq forallb]. rewrite !at8_firstn by lia. reflexivity. Qed.

Lemma oa_unknown_at : forall (body : list byte) i, 0 <= i -> i + 6 <= 15 ->
  firstn 6 (skipn (Z.to_nat i) (ann_unknown body)) = firstn 6 (skipn (Z.to_nat i) body).
Proof.
  intros body i H1 H2. unfold ann_unknown. rewrite skipn_firstn_comm. rewrite firstn_firstn.
  f_equal. lia.
Qed.

Lemma oa_find_mac_S : forall u mac i fuel,
  find_mac_loop u mac i (S fuel) = if memeq 6 (skipn (Z.to_nat i) u) mac then i else find_mac_loop u mac (i + 1) fuel.
Proof. reflexivity. Qed.

Lemma oa_find_mac_range : forall u mac fuel i, 0 <= i -> -1 <= find_mac_loop u mac i fuel <= i + Z.of_nat fuel.
Proof.
  intros u mac fuel. induction fuel as [|f IH]; intros i Hi; cbn [find_mac_loop]; [lia|].
  destruct (memeq 6 (skipn (Z.to_nat i) u) mac); [lia|]. specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

Lemma oa_swrap_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.
