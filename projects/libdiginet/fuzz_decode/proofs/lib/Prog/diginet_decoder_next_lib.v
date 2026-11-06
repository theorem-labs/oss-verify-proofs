(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Pieces of the walk of diginet_decoder_next in fuzz_decode.plain (0x13e80): cell lemmas for its
   160-byte frame, its event and its decoder, the model split at the first diginet_msg_next call
   (dn_tail), the facts every path shares (dn_ctx, dn_at), and the shared epilogue at 0x140f8
   (dn_epi, which rebuilds the stack from the one at the start: the decoder and the event may lie in
   the stack below the frame).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  diginet_msg_next_c diginet_decoder_next_c diginet_decoder_next_bridge.
Import ListNotations.
Open Scope Z_scope.

(* ---- cells ---- *)

Lemma rw_cells_app : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in Hn, Hw.
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma rw_cells_app_merge : forall segs m A cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(* the same bytes under another cell layout *)
Lemma rw_cells_bytes : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma rw_cells_cons : forall segs m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs H. apply (rw_cells_app segs m A [c] cs) in H as [H1 H2].
  cbn [cells_size] in H2. rewrite Nat.add_0_r in H2. split; assumption.
Qed.

Lemma rw_cells_wf : forall segs m A cs, rw_cells segs m A cs -> cells_wf cs.
Proof. intros segs m A cs [[H _] _]. exact H. Qed.

Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

(* a CB of n + k bytes as two *)
Lemma rw_cells_CB2 : forall segs m A n k bs, rw_cells segs m A [CB (n + k) bs] ->
  rw_cells segs m A [CB n (firstn n bs)] /\ rw_cells segs m (A + Z.of_nat n) [CB k (skipn n bs)].
Proof.
  intros segs m A n k bs H.
  pose proof (rw_cells_wf segs m A _ H) as [L _]. cbn [cell_wf] in L.
  assert (H2 : rw_cells segs m A [CB n (firstn n bs); CB k (skipn n bs)]).
  { eapply rw_cells_bytes; [exact H| |].
    - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn. }
  apply rw_cells_cons in H2 as [H3 H4]. cbn [csize] in H4. split; assumption.
Qed.

(* the frame after the prologue: the five saved registers above 120 bytes of junk, cut into
   the 8 unused bytes, the message lsb (sp' + 8), the peek cursor (sp' + 0x30) and the message m
   (sp' + 0x50) *)
Lemma dn_frame_split : forall segs m A (J : list byte) (v3 v2 v1 v0 vr : word),
  rw_cells segs m A [CB 120 J; C8 v3; C8 v2; C8 v1; C8 v0; C8 vr] ->
  exists j0 jl jp jm, rw_cells segs m A [CB 8 j0] /\ rw_cells segs m (A + 8) [CB 40 jl] /\
    rw_cells segs m (A + 48) [CB 32 jp] /\ rw_cells segs m (A + 80) [CB 40 jm] /\
    rw_cells segs m (A + 120) [C8 v3; C8 v2; C8 v1; C8 v0; C8 vr].
Proof.
  intros segs m A J v3 v2 v1 v0 vr H.
  apply rw_cells_cons in H as [H1 H2]. cbn [csize] in H2.
  change 120%nat with (8 + 112)%nat in H1. apply rw_cells_CB2 in H1 as [Q0 H1].
  change 112%nat with (40 + 72)%nat in H1. apply rw_cells_CB2 in H1 as [Q1 H1].
  change 72%nat with (32 + 40)%nat in H1. apply rw_cells_CB2 in H1 as [Q2 Q3].
  do 4 eexists. split; [exact Q0|].
  split; [replace (A + 8) with (A + Z.of_nat 8) by lia; exact Q1|].
  split; [replace (A + 48) with (A + Z.of_nat 8 + Z.of_nat 40) by lia; exact Q2|].
  split; [replace (A + 80) with (A + Z.of_nat 8 + Z.of_nat 40 + Z.of_nat 32) by lia; exact Q3|].
  replace (A + 120) with (A + Z.of_nat (8 + 112)) by lia. exact H2.
Qed.

Lemma msg_cells_size : forall body mj r, cells_size (msg_cells body mj r) = 40%nat.
Proof.
  intros body mj r. unfold msg_cells. destruct (is_end r); [reflexivity|].
  destruct (writes_len (mr_kind r)); reflexivity.
Qed.

(* ---- the decoder ---- *)

Lemma dn_dec_cells_at : forall body cpad len pos st p,
  decoder_cells body cpad (decoder_at len pos st p) =
  cursor_cells body len pos st ++ [CB 7 cpad; C8 (Z_to_bv 64 (personality_ptr p))].
Proof.
  intros. unfold decoder_cells, decoder_at. cbn [dd_c dd_p dc_len dc_pos dc_status].
  rewrite Nat2Z.id. reflexivity.
Qed.

Lemma dn_dec_merge : forall segs m d body cpad len pos' st' p,
  rw_cells segs m d (cursor_cells body len pos' st') ->
  rw_cells segs m (d + 25) [CB 7 cpad; C8 (Z_to_bv 64 (personality_ptr p))] ->
  rw_cells segs m d (decoder_cells body cpad
    {| dd_c := {| dc_len := len; dc_pos := Z.of_nat pos'; dc_status := st' |}; dd_p := p |}).
Proof.
  intros segs m d body cpad len pos' st' p H1 H2. unfold decoder_cells.
  cbn [dd_c dd_p dc_len dc_pos dc_status]. rewrite Nat2Z.id.
  apply rw_cells_app_merge; [exact H1|]. cbn [cells_size csize cursor_cells Nat.add].
  replace (d + Z.of_nat 25) with (d + 25) by lia. exact H2.
Qed.

(* ---- values ---- *)

Lemma mr_code_range : forall r, -8 <= mr_code r <= 1.
Proof. intros r. unfold mr_code. destruct (mr_kind r); lia. Qed.

(* beq / bne of two 64-bit values that are signed 64-bit integers *)
Lemma dn_eqb_int64 : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  replace (2^64) with 18446744073709551616 in E by reflexivity.
  replace (2^63) with 9223372036854775808 in Hx, Hy by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* lbu of a cell C1 (b8 z) whose z is a byte *)
Lemma dn_zxb_b8 : forall z, 0 <= z < 256 -> zxb (b8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. exact Hz.
Qed.

Lemma byte_at_map : forall bb i, byte_at (map bz bb) (Z.of_nat i) = at8 bb i.
Proof.
  intros bb i. unfold byte_at, at8. rewrite Nat2Z.id.
  rewrite <- (map_nth bz bb (b8 0) i). reflexivity.
Qed.

Lemma u8_small : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. exact Hx. Qed.

Lemma u16_small : forall x, 0 <= x < 65536 -> u16 x = x.
Proof. intros x Hx. unfold u16. apply Z.mod_small. exact Hx. Qed.

(* x & m of two bytes is a byte below m *)
Lemma byte_land_le : forall x m, 0 <= x < 256 -> 0 <= m < 256 -> 0 <= Z.land x m <= m.
Proof.
  intros x m Hx Hm.
  assert (H : forallb (fun a => forallb (fun b => (0 <=? Z.land (Z.of_nat a) (Z.of_nat b)) &&
                                                  (Z.land (Z.of_nat a) (Z.of_nat b) <=? Z.of_nat b))
                                         (seq 0 256)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  specialize (H (Z.to_nat m) ltac:(apply in_seq; lia)).
  rewrite !Z2Nat.id in H by lia. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

(* sb of a register holding Z_to_bv 64 z stores the byte b8 z *)
Lemma le1_b8 : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply (mod_mod8_of_modw z 64). lia.
Qed.

(* the kit's handling of the memory after a store, which takes the bytes of an sb of Z_to_bv 64 z as
   the cell C1 (b8 z) *)
Ltac mem_after_store_opt ::=
  try rewrite le1_b8;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* ---- the message ---- *)

(* the message cells of a step that answers 1, as dmsg_cells of its DgnLib.v message *)
Lemma msg_cells_dmsg : forall body mj bb pos st,
  mr_code (msg_step bb pos st) = 1 ->
  msg_cells body mj (msg_step bb pos st) = dmsg_cells body (firstn 4 (skipn 4 mj)) (dn_msg (msg_step bb pos st)).
Proof.
  intros body mj bb pos st Hc. unfold msg_cells, dmsg_cells, dn_msg, is_end.
  unfold mr_code in Hc.
  destruct (mr_kind (msg_step bb pos st)) eqn:K; try discriminate;
    cbv beta iota delta [writes_status writes_running writes_len writes_sysex].
  - destruct (msg_step_sysex bb pos st K) as (_ & HS & _ & _). rewrite HS.
    unfold sysex_ptr. replace (Z.of_nat (S pos) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - reflexivity.
Qed.

(* ---- the event ---- *)

(* the 40 bytes of struct diginet_event before ev->msg *)
Definition ev_head (e : dgn_event) : list cell :=
  [ C4 (Z_to_bv 64 (de_kind e));
    C1 (b8 (de_strip e)); C1 (b8 (de_button e)); C1 (b8 (de_zone e)); C1 (b8 (de_on e));
    C1 (b8 (de_right e)); C1 (b8 (de_addr e)); C1 (b8 (de_lsb_missing e)); C1 (b8 0);
    C2 (Z_to_bv 64 (de_value e)); C2 (Z_to_bv 64 (de_delta e)); C2 (Z_to_bv 64 (de_mask e));
    C1 (b8 (de_segments e)); C1 (b8 (de_len e)) ]
  ++ arr_cells 9 (de_text e) ++ arr_cells 8 (de_seg e)
  ++ [ C1 (b8 (de_dots e)); C1 (b8 (de_device e)); C1 (b8 0) ].

Lemma event_cells_head : forall body mpad e,
  event_cells body mpad e = ev_head e ++ dmsg_cells body mpad (de_msg e).
Proof. intros. unfold event_cells, ev_head. rewrite <- !app_assoc. reflexivity. Qed.

(* memset's 40 zero bytes are the head of the zero event *)
Lemma dn_zero_head : forall segs m A,
  rw_cells segs m A [CB 40 (repeat (Z_to_bv 8 0) 40)] -> rw_cells segs m A (ev_head dgn_event_zero).
Proof.
  intros segs m A H. eapply rw_cells_bytes; [exact H| |].
  - vm_compute. repeat split.
  - vm_compute. reflexivity.
Qed.

(* ---- the model past the first diginet_msg_next ---- *)

(* diginet_decoder_next once its message m and cursor c1 are known and diginet_msg_next answered 1
   (DgnLib.v, diginet_decode.c:115-157) *)
Definition dn_tail (b : list Z) (m : dgn_msg) (c1 : dgn_cursor) (p : option Z) : Z * dgn_event * dgn_decoder :=
  let d1 := {| dd_c := c1; dd_p := p |} in
  let e := de_set_kind DIGINET_EV_OTHER (de_set_msg m dgn_event_zero) in
  if Z.land (dm_status m) 0xf0 =? 0x90 then (1, decode_note m e, d1)
  else if dm_status m =? 0xf0 then (1, decode_sysex b m e, d1)
  else if negb (Z.land (dm_status m) 0xf0 =? 0xb0) then (1, e, d1)
  else if dm_d1 m <? 0x20 then
    let e := de_set_kind DIGINET_EV_FADER e in
    let e := de_set_strip (dm_d1 m) e in
    let e := de_set_value (u16 (Z.shiftl (dm_d2 m) 3)) e in
    let '(rl, lsb, peek) := diginet_msg_next b c1 dgn_msg_zero in
    if (rl =? 1) && (Z.land (dm_status lsb) 0xf0 =? 0xb0) && (dm_d1 lsb =? 0x20 + dm_d1 m) then
      (1, de_set_value (u16 (Z.lor (de_value e) (u16 (Z.land (Z.shiftr (dm_d2 lsb) 4) 7)))) e,
       {| dd_c := peek; dd_p := p |})
    else (1, de_set_lsb_missing 1 e, d1)
  else if dm_d1 m =? DIGINET_JOG_CC then
    (1, de_set_delta (s16 (dm_d2 m - 64)) (de_set_kind DIGINET_EV_JOG e), d1)
  else if (0x40 <=? dm_d1 m) && (dm_d1 m <? 0x40 + DIGINET_ZONE_FIRST) then
    (1, de_set_delta (s16 (dm_d2 m - 64))
          (de_set_strip (u8 (dm_d1 m - 0x40)) (de_set_kind DIGINET_EV_VPOT e)), d1)
  else (1, e, d1).

Lemma dn_split : forall b d ev,
  diginet_decoder_next b d ev =
  let '(r, m, c1) := diginet_msg_next b (dd_c d) dgn_msg_zero in
  if negb (r =? 1) then (r, ev, {| dd_c := c1; dd_p := dd_p d |}) else dn_tail b m c1 (dd_p d).
Proof. reflexivity. Qed.

Lemma dn_res_n1 : forall bb pos st p ev0, st_ok st -> (pos <= length bb)%nat ->
  mr_code (msg_step bb pos st) <> 1 ->
  diginet_decoder_next (map bz bb) (decoder_at (Z.of_nat (length bb)) pos st p) ev0 =
  (mr_code (msg_step bb pos st), ev0,
   {| dd_c := cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st)); dd_p := p |}).
Proof.
  intros bb pos st p ev0 HS HP HC. rewrite dn_split.
  change (dd_c (decoder_at (Z.of_nat (length bb)) pos st p)) with (cursor_of bb pos st).
  change (dd_p (decoder_at (Z.of_nat (length bb)) pos st p)) with p.
  destruct (dn_msg_next bb pos st dgn_msg_zero) as (E1 & E2 & _).
  destruct (diginet_msg_next (map bz bb) (cursor_of bb pos st) dgn_msg_zero) as [[rc mm] cc] eqn:EE.
  cbn [fst snd] in E1, E2. subst rc cc.
  rewrite (proj2 (Z.eqb_neq _ _) HC). reflexivity.
Qed.

Lemma dn_res_1 : forall bb pos st p ev0, st_ok st -> (pos <= length bb)%nat ->
  mr_code (msg_step bb pos st) = 1 ->
  diginet_decoder_next (map bz bb) (decoder_at (Z.of_nat (length bb)) pos st p) ev0 =
  dn_tail (map bz bb) (dn_msg (msg_step bb pos st))
    (cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) p.
Proof.
  intros bb pos st p ev0 HS HP HC. rewrite dn_split.
  change (dd_c (decoder_at (Z.of_nat (length bb)) pos st p)) with (cursor_of bb pos st).
  change (dd_p (decoder_at (Z.of_nat (length bb)) pos st p)) with p.
  destruct (dn_msg_next bb pos st dgn_msg_zero) as (E1 & E2 & E3).
  specialize (E3 HC).
  destruct (diginet_msg_next (map bz bb) (cursor_of bb pos st) dgn_msg_zero) as [[rc mm] cc] eqn:EE.
  cbn [fst snd] in E1, E2, E3. subst rc cc mm.
  rewrite HC. reflexivity.
Qed.

(* ---- the contract's postcondition (with the frame's base written sp + -160, as carve_frame leaves
   it) and the epilogue at 0x140f8: a0 = s1, the saved registers back, the frame popped, ret ---- *)

Definition dn_Q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (d ev body lo : Z) (cpad ej : list byte) (res : Z * dgn_event * dgn_decoder)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (mpad : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (fst res))) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -160, bv_unsigned sp)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rw_cells rsegs m' d (decoder_cells body cpad (snd res)) /\
    rw_cells rsegs m' ev (if fst (fst res) =? 1 then event_cells body mpad (snd (fst res)) else [CB 80 ej]).

(* a byte inside cells is readable *)
Lemma rw_cells_mrd : forall segs m A cs x, rw_cells segs m A cs -> A <= x < A + Z.of_nat (cells_size cs) ->
  exists b, mrd segs m (wa x) = Some b.
Proof.
  intros segs m A cs x [[Hwf (Ha & Hl & Hb)] _] Hx.
  assert (Hi : (Z.to_nat (x - A) < length (cells_bytes cs))%nat) by (rewrite cells_bytes_length by exact Hwf; lia).
  specialize (Hb _ Hi). replace (A + Z.of_nat (Z.to_nat (x - A))) with x in Hb by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. exact Hb.
  - apply nth_error_None in E. lia.
Qed.

(* The stack at the end: outside the function's footprint the bytes are those of the start, inside
   it each byte is readable from the cells the walk ends with. The decoder and the event may lie in
   the stack below the frame, so the stack is rebuilt here rather than carried through the walk. *)
Lemma stk_final3 : forall segs m0 m lo hi a1 b1 a2 b2 a3 b3,
  stk segs m0 lo hi -> munch [(a1, b1); (a2, b2); (a3, b3)] m0 m -> wmono segs m0 m ->
  (forall x, a1 <= x < b1 -> exists b, mrd segs m (wa x) = Some b) ->
  (forall x, a2 <= x < b2 -> exists b, mrd segs m (wa x) = Some b) ->
  (forall x, a3 <= x < b3 -> exists b, mrd segs m (wa x) = Some b) ->
  stk segs m lo hi.
Proof.
  intros segs m0 m lo hi a1 b1 a2 b2 a3 b3 (H1 & H2 & H) MU WM K1 K2 K3.
  split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hw Hr]. split; [apply WM; exact Hw|].
  destruct (Z_le_gt_dec a1 a); [destruct (Z_lt_ge_dec a b1); [apply K1; lia|]|];
  (destruct (Z_le_gt_dec a2 a); [destruct (Z_lt_ge_dec a b2); [apply K2; lia|]|]);
  (destruct (Z_le_gt_dec a3 a); [destruct (Z_lt_ge_dec a b3); [apply K3; lia|]|]);
  (assert (E : m (wa a) = m0 (wa a))
    by (apply MU; unfold wa; rewrite unsigned_lit by lia; cbn [outside]; repeat split; lia);
   unfold mrd in *; rewrite E; exact Hr).
Qed.

Lemma dn_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (d ev body lo : Z) (cpad ej mpad0 : list byte) (res : Z * dgn_event * dgn_decoder)
    (cs0 cs1 cs2 cs3 : list cell)
    (ra' t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 : word) (rv : Z),
  rv = fst (fst res) ->
  stk rsegs m0 lo (bv_unsigned sp) ->
  rw_cells rsegs m (bv_unsigned sp + -160) cs0 -> cells_size cs0 = 8%nat ->
  rw_cells rsegs m (bv_unsigned sp + -152) cs1 -> cells_size cs1 = 40%nat ->
  rw_cells rsegs m (bv_unsigned sp + -112) cs2 -> cells_size cs2 = 32%nat ->
  rw_cells rsegs m (bv_unsigned sp + -80) cs3 -> cells_size cs3 = 40%nat ->
  rw_cells rsegs m (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -160, bv_unsigned sp)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m d (decoder_cells body cpad (snd res)) ->
  rw_cells rsegs m ev (if fst (fst res) =? 1 then event_cells body mpad0 (snd (fst res)) else [CB 80 ej]) ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 s0' (Z_to_bv 64 rv) a0 a1 a2 a3 a4 a5 a6 a7
             s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m d ev body lo cpad ej mpad0 res
    cs0 cs1 cs2 cs3 ra' t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 rv Hrv ST0
    F0 S0 F1 S1 F2 S2 F3 S3 HS MU WM MI HD HE.
  subst rv.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs m lo (bv_unsigned sp)).
  { eapply stk_final3; [exact ST0 | exact MU | exact WM | | |].
    - intros x Hx. eapply rw_cells_mrd; [exact HD|]. rewrite decoder_cells_size. lia.
    - intros x Hx. eapply rw_cells_mrd; [exact HE|].
      destruct (fst (fst res) =? 1); [rewrite event_cells_size | cbn [cells_size csize Nat.add]]; lia.
    - intros x Hx.
      destruct (Z_lt_ge_dec x (bv_unsigned sp + -152));
        [eapply rw_cells_mrd; [exact F0|]; rewrite S0; lia|].
      destruct (Z_lt_ge_dec x (bv_unsigned sp + -112));
        [eapply rw_cells_mrd; [exact F1|]; rewrite S1; lia|].
      destruct (Z_lt_ge_dec x (bv_unsigned sp + -80));
        [eapply rw_cells_mrd; [exact F2|]; rewrite S2; lia|].
      destruct (Z_lt_ge_dec x (bv_unsigned sp + -40));
        [eapply rw_cells_mrd; [exact F3|]; rewrite S3; lia|].
      eapply rw_cells_mrd; [exact HS|]. cbn [cells_size csize Nat.add]. lia. }
  clear ST0 F0 S0 F1 S1 F2 S2 F3 S3.
  do 8 step.
  apply evt_done. unfold dn_Q. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact HD | exact HE].
Qed.

(* ---- what a step that answers 1 tells about its message ---- *)

Lemma chan_step_facts : forall b start st status run d, 128 <= status < 240 ->
  mr_code (chan_step b start st status run d) = 1 ->
  mr_kind (chan_step b start st status run d) = MkChan /\ mr_status (chan_step b start st status run d) = status /\
  0 <= mr_d1 (chan_step b start st status run d) < 128 /\ 0 <= mr_d2 (chan_step b start st status run d) < 128.
Proof.
  intros b start st status run d Hs. unfold chan_step.
  destruct (_ <? _)%nat; [cbn; discriminate|].
  destruct (Z.leb_spec 0x80 (at8 b d)) as [A|A]; [cbn; discriminate|].
  destruct ((chan_n status =? 2)%nat && (0x80 <=? at8 b (S d))) eqn:B; [cbn; discriminate|].
  intros _. cbn [mr_kind mr_status mr_d1 mr_d2].
  pose proof (at8_range b d) as R1. pose proof (at8_range b (S d)) as R2.
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  destruct (chan_n status =? 2)%nat; [|lia]. cbn in B. apply Z.leb_gt in B. lia.
Qed.

Lemma dn_msg_facts : forall bb pos st, st_ok st -> mr_code (msg_step bb pos st) = 1 ->
  0 <= dm_d1 (dn_msg (msg_step bb pos st)) < 128 /\ 0 <= dm_d2 (dn_msg (msg_step bb pos st)) < 128 /\
  ((dm_status (dn_msg (msg_step bb pos st)) = 240 /\ 1 <= dm_sysex (dn_msg (msg_step bb pos st)) /\
    0 <= dm_sysex_len (dn_msg (msg_step bb pos st)) /\
    dm_sysex (dn_msg (msg_step bb pos st)) + dm_sysex_len (dn_msg (msg_step bb pos st)) < Z.of_nat (length bb)) \/
   128 <= dm_status (dn_msg (msg_step bb pos st)) < 240).
Proof.
  intros bb pos st HS. unfold dn_msg, msg_step.
  destruct (Nat.leb_spec (length bb) pos) as [L|L]; [cbn; discriminate|].
  destruct (Z.eqb_spec (at8 bb pos) 0xf0) as [E|E].
  - destruct (find_f7 (skipn (S pos) bb)) as [j|] eqn:FJ; [|cbn; discriminate].
    intros _. cbn [dm_status dm_d1 dm_d2 dm_sysex dm_sysex_len mr_kind mr_status mr_d1 mr_d2 mr_sysex
                   mr_sysex_len writes_sysex].
    apply find_f7_some in FJ. rewrite length_skipn in FJ.
    split; [lia|]. split; [lia|]. left. lia.
  - pose proof (at8_range bb pos) as R.
    destruct (Z.leb_spec 0xf0 (at8 bb pos)) as [A|A]; [cbn; discriminate|].
    destruct (Z.leb_spec 0x80 (at8 bb pos)) as [B|B].
    + intros HC. destruct (chan_step_facts bb pos st (at8 bb pos) 0 (S pos) ltac:(lia) HC) as (K & HSt & D1 & D2).
      rewrite K, HSt. cbn [writes_sysex dm_status dm_d1 dm_d2].
      split; [exact D1|]. split; [exact D2|]. right. lia.
    + destruct (Z.eqb_spec st 0) as [Z0|Z0]; [cbn; discriminate|].
      assert (Hr : 128 <= st < 240) by (destruct HS; lia).
      intros HC. destruct (chan_step_facts bb pos st st 1 pos Hr HC) as (K & HSt & D1 & D2).
      rewrite K, HSt. cbn [writes_sysex dm_status dm_d1 dm_d2].
      split; [exact D1|]. split; [exact D2|]. right. lia.
Qed.

Lemma if_one : forall (A B : list cell), (if 1 =? 1 then A else B) = A.
Proof. reflexivity. Qed.

Lemma byte_at_map_Z : forall bb z, 0 <= z -> byte_at (map bz bb) z = at8 bb (Z.to_nat z).
Proof. intros bb z Hz. rewrite <- (Z2Nat.id z Hz) at 1. apply byte_at_map. Qed.

(* lbu of byte s + k of the body *)
Lemma body_read : forall segs m body bb s k, bytes_at segs m body bb -> 0 <= s + k < Z.of_nat (length bb) ->
  ov_read_bytes segs m (wa (body + s + k)) 1 = Some [b8 (at8 bb (Z.to_nat (s + k)))].
Proof.
  intros segs m body bb s k HB Hk.
  replace (body + s + k) with (body + (s + k)) by lia.
  rewrite (bytes_at_read segs m body bb (s + k) 1 HB ltac:(lia) ltac:(lia)).
  f_equal. unfold at8. rewrite b8_bz.
  assert (L : (Z.to_nat (s + k) < length bb)%nat) by lia.
  revert L. generalize (Z.to_nat (s + k)) as i. clear.
  induction bb as [|x bb IH]; intros [|i] L; cbn [length] in L; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma dn_eqb_u64 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sysex_ptr_nz : forall body off, off <> 0 -> sysex_ptr body off = body + off.
Proof. intros body off H. unfold sysex_ptr. rewrite (proj2 (Z.eqb_neq off 0) H). reflexivity. Qed.

(* ---- the facts that hold on every path past the first diginet_msg_next call: the stack at the
   start, the bounds and disjointness of the contract, and the model's result as dn_tail of the
   message msg and the cursor after the call ---- *)

Definition dn_ctx (sp : word) (m0 : word -> option byte) (d ev body lo : Z) (bb : list byte) (p : option Z)
    (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad : list byte) : Prop :=
  stk rsegs m0 lo (bv_unsigned sp) /\ 0 <= bv_unsigned sp < 2^64 /\ lo + 160 <= bv_unsigned sp /\ 0 <= lo /\
  (0 <= d /\ d + 40 <= 2^64) /\ (0 <= ev /\ ev + 80 <= 2^64) /\
  (0 <= body /\ body + Z.of_nat (length bb) <= 2^64) /\
  (d + 40 <= ev \/ ev + 80 <= d) /\ (d + 40 <= body \/ body + Z.of_nat (length bb) <= d) /\
  (ev + 80 <= body \/ body + Z.of_nat (length bb) <= ev) /\
  (d + 40 <= bv_unsigned sp + -160 \/ bv_unsigned sp <= d) /\
  (ev + 80 <= bv_unsigned sp + -160 \/ bv_unsigned sp <= ev) /\
  (body + Z.of_nat (length bb) <= bv_unsigned sp + -160 \/ bv_unsigned sp <= body) /\
  bv_unsigned (Z_to_bv 64 ev) = ev /\
  res = dn_tail (map bz bb) msg (cursor_of bb pos1 st1) p /\
  0 <= dm_status msg < 256 /\ length mpad = 4%nat.

Ltac dn_ctx_open H :=
  destruct H as (ST0 & RSP & HLO & Hlo0 & BD & BE & BB & DJ1 & DJ2 & DJ3 & DJ4 & DJ5 & DJ6 & Ue & HRES & RST & Lmpad).

(* ---- the state of a path: the event's head is ev_head e (at the dispatch on the status, 0x13ef8,
   e is dn_e0 msg, the zero event with the message and the kind 13 stored) ---- *)

Definition dn_e0 (msg : dgn_msg) : dgn_event := de_set_kind DIGINET_EV_OTHER (de_set_msg msg dgn_event_zero).

Definition dn_at (sp : word) (m0 m1 : word -> option byte) (d ev body : Z) (bb cpad : list byte) (p : option Z)
    (pos1 : nat) (st1 : Z) (msg : dgn_msg) (mpad j0 jl jp : list byte) (v3 v2 v1 v0 vr : word) (e : dgn_event)
    : Prop :=
  rw_cells rsegs m1 d (cursor_cells body (Z.of_nat (length bb)) pos1 st1) /\
  rw_cells rsegs m1 (d + 25) [CB 7 cpad; C8 (Z_to_bv 64 (personality_ptr p))] /\
  bytes_at rsegs m1 body bb /\
  rw_cells rsegs m1 (bv_unsigned sp + -160) [CB 8 j0] /\
  rw_cells rsegs m1 (bv_unsigned sp + -152) [CB 40 jl] /\
  rw_cells rsegs m1 (bv_unsigned sp + -112) [CB 32 jp] /\
  rw_cells rsegs m1 (bv_unsigned sp + -80) (dmsg_cells body mpad msg) /\
  rw_cells rsegs m1 (bv_unsigned sp + -40) [C8 v3; C8 v2; C8 v1; C8 v0; C8 vr] /\
  rw_cells rsegs m1 ev (ev_head e) /\
  rw_cells rsegs m1 (ev + 40) (dmsg_cells body mpad msg) /\
  munch [(d, d + 40); (ev, ev + 80); (bv_unsigned sp + -160, bv_unsigned sp)] m0 m1 /\
  wmono rsegs m0 m1 /\ mem_inv rsegs m1.

(* dn_at's facts as hypotheses whose cells are literal lists, as the step tactics need them *)
Ltac dn_open H :=
  destruct H as (HDc & HD2 & HBB & H0 & HL & HP & HM & HS & HE & HEM & MU & WM & MI);
  unfold cursor_cells in HDc; unfold dmsg_cells in HM, HEM;
  unfold ev_head, arr_cells, dn_e0 in HE;
  cbn [map seq nth app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value
       de_delta de_mask de_segments de_len de_text de_seg de_dots de_device de_set_kind de_set_msg
       de_set_device dgn_event_zero repeat] in HE;
  unfold DIGINET_EV_OTHER in HE.

(* the event at the end: its 40-byte head as the walk leaves it, and the message the memcpy put in *)
Lemma dn_ev_final : forall segs m ev body mpad msg e cs,
  rw_cells segs m ev cs -> rw_cells segs m (ev + 40) (dmsg_cells body mpad msg) ->
  de_msg e = msg -> cs = ev_head e ->
  rw_cells segs m ev (event_cells body mpad e).
Proof.
  intros segs m ev body mpad msg e cs H1 H2 E ->. rewrite event_cells_head, E.
  apply rw_cells_app_merge; [exact H1|].
  replace (ev + Z.of_nat (cells_size (ev_head e))) with (ev + 40) by reflexivity. exact H2.
Qed.

(* the literal head cells of an event built by de_set_* *)
Ltac ev_head_lit :=
  unfold ev_head, arr_cells; try unfold dn_e0;
  cbn [map seq nth app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value
       de_delta de_mask de_segments de_len de_text de_seg de_dots de_device de_msg
       de_set_kind de_set_strip de_set_button de_set_zone de_set_on de_set_right de_set_addr
       de_set_lsb_missing de_set_value de_set_delta de_set_mask de_set_segments de_set_len de_set_text
       de_set_seg de_set_dots de_set_device de_set_msg dgn_event_zero repeat].

(* de_msg of an event built by de_set_* from de_set_msg msg *)
Ltac dmsg_eq :=
  try unfold dn_e0;
  cbn [de_msg de_set_kind de_set_strip de_set_button de_set_zone de_set_on de_set_right de_set_addr
       de_set_lsb_missing de_set_value de_set_delta de_set_mask de_set_segments de_set_len de_set_text
       de_set_seg de_set_dots de_set_device de_set_msg]; reflexivity.

(* At 0x140f8 with s1 = 1, the decoder's cursor HDc / HD2 as dn_open names them, and the event's head HE
   and message HEM: the epilogue (dn_epi). HR : res = (1, e, {| dd_c := c; dd_p := p |}). Two goals are
   left: de_msg e = msg, and HE's cell list = ev_head e. *)
Ltac dn_fin HR HDc HD2 HE HEM :=
  eapply dn_epi;
  [ rewrite HR; reflexivity | eassumption | eassumption | reflexivity | eassumption | reflexivity
  | eassumption | reflexivity | eassumption | reflexivity | eassumption | eassumption | eassumption
  | eassumption
  | rewrite HR; exact (dn_dec_merge rsegs _ _ _ _ _ _ _ _ HDc HD2)
  | rewrite HR; cbn [fst snd]; rewrite if_one; eapply dn_ev_final; [exact HE | exact HEM | |] ].
