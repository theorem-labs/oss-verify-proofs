(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 416 of its 465 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame lib/U/Prog into libdiginet/fuzz_decode (module path and addresses only: entry 0x141a0 -> 0x13bec, every other pc -0x5b4) *)
(* Modified by Theorem Labs, 2026-10: the walk of diginet_msg_next in fuzz_frame.ubsan (0x141a0) proves its contract, and no UBSan check branch is taken. *)
(* The walk follows msg_step (DgnLib): the entry checks to 0x13c4c, then the sysex scan (sloop, sfound,
   scut) or the channel message (chan, its data bytes, ccut, ctail); every exit ends at fin (0x13dc0).
   The ten branches to the trap at 0x13dc8 are each shown not taken (br false). The 40 bytes of the
   message are b0 :: b1 :: r; after the stores of 0x13c3c..0x13c48 they are the cells MC0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_cursor_init_c diginet_msg_next_c.
Import ListNotations.
Open Scope Z_scope.

(* ---------- bytes, words and cells ---------- *)

Lemma rd8 : forall m A l i, bytes_at rsegs m A l -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b8 (at8 l i)].
Proof.
  intros m A l i BL Hi. rewrite (bytes_at_ov_read rsegs m A l i 1 BL) by lia. f_equal. clear BL.
  unfold at8. rewrite b8_bz.
  revert i Hi. induction l as [|x l IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma at8_range : forall l i, 0 <= at8 l i < 256.
Proof. intros l i. unfold at8. apply bz_range. Qed.

Lemma at8_skipn : forall n l k, at8 (skipn n l) k = at8 l (n + k).
Proof.
  induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn [skipn Nat.add].
  - unfold at8. destruct k; reflexivity.
  - exact (IH l k).
Qed.

Lemma zxbu : forall x, 0 <= x < 256 -> bv_unsigned (zxb (b8 x)) = x.
Proof.
  intros x Hx. unfold zxb. pose proof (bz_range (b8 x)) as R. unfold bz in R.
  rewrite unsigned_lit by lia. apply bz_b8. lia.
Qed.

(* c & 7 and mp & 7, the alignment checks *)
Lemma land7 : forall x, 0 <= x < 2^64 -> x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x Hx H8. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H8.
Qed.

(* 0x13c18..0x13c20: (b != 0) ^ (b + start == 0) *)
Lemma snez_seqz_xor : forall x y, 0 < x < 2^64 -> 0 < y < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x))) (bv_unsigned (v_sltiu (Z_to_bv 64 y) 1)))
  = Z_to_bv 64 1.
Proof.
  intros x y Hx Hy. unfold v_sltu, v_sltiu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* not x, the bound of the overflow checks *)
Lemma not_val : forall x w, 0 <= x < 2^64 -> w = 18446744073709551615 ->
  Z.lxor (bv_unsigned (Z_to_bv 64 x)) w = 2^64 - 1 - x.
Proof. intros x w Hx ->. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. lia. Qed.

Lemma sl56 : forall x, 0 <= x < 256 -> bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  assert (G : forall x, 0 <= x < 2^8 ->
            Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x) = true).
  { apply (byte_forall (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x))).
    vm_compute. reflexivity. }
  intros x Hx. apply Bool.eqb_prop, G. lia.
Qed.

Lemma sxb_lts : forall x, 0 <= x < 256 -> bv_lts (sxb (b8 x)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  assert (G : forall x, 0 <= x < 2^8 -> Bool.eqb (bv_lts (sxb (b8 x)) (Z_to_bv 64 0)) (128 <=? x) = true).
  { apply (byte_forall (fun x => Bool.eqb (bv_lts (sxb (b8 x)) (Z_to_bv 64 0)) (128 <=? x))).
    vm_compute. reflexivity. }
  intros x Hx. apply Bool.eqb_prop, G. lia.
Qed.

(* the inlined channel_data_len: 1 + ((status & 0xe0) != 0xc0) *)
Lemma snez_n : forall s, 0 <= s < 256 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1 = Z.of_nat (chan_n s).
Proof.
  assert (G : forall s, 0 <= s < 2^8 ->
            Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1)
                  (Z.of_nat (chan_n s)) = true).
  { apply (byte_forall (fun s => Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1)
                                       (Z.of_nat (chan_n s)))).
    vm_compute. reflexivity. }
  intros s Hs. apply Z.eqb_eq, G. lia.
Qed.

Lemma land_c0 : forall s, 0 <= s < 256 ->
  bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192) = (chan_n s =? 1)%nat.
Proof.
  assert (G : forall s, 0 <= s < 2^8 ->
            Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat = true).
  { apply (byte_forall (fun s => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat)).
    vm_compute. reflexivity. }
  intros s Hs. apply Bool.eqb_prop, G. lia.
Qed.

Lemma le2_0 : le2 (Z_to_bv 64 0) = [b8 0; b8 0].
Proof. reflexivity. Qed.
Lemma le2_240 : le2 (Z_to_bv 64 240) = [b8 240; b8 0].
Proof. reflexivity. Qed.

(* the same bytes under other cells *)
Lemma rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite <- (cells_bytes_length cs' W'), EB, (cells_bytes_length cs W). exact V.
Qed.

(* a one-byte store of a word v: the cell holds its low byte; le1 (zxb b) is [b] by le1_zxb *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.
Ltac mem_after_store_opt ::=
  try rewrite ?le1_zxb;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; rewrite ?zxbu by lia; uns; solve_cond_rec]
  end.

(* two byte lists of cells, split at their common shape; each piece by computation or lia *)
Ltac bytes_tac :=
  cbn [cells_bytes cbytes app firstn skipn nth];
  rewrite ?le2_0, ?le2_240, ?skipn_skipn; cbn [app Nat.add];
  repeat match goal with
  | |- ?x :: _ = ?y :: _ => f_equal
  | |- le8 _ ++ _ = le8 _ ++ _ => f_equal
  | |- firstn _ _ ++ _ = firstn _ _ ++ _ => f_equal
  end;
  try reflexivity;
  try (f_equal; uns; first [reflexivity | f_equal; lia]).

(* ---------- the walk ---------- *)

Section MN.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (c mp body : Z) (bb : list byte) (b0 b1 : byte) (r : list byte) (pos : nat) (st : Z).
Hypothesis Hc : c <> 0.
Hypothesis Hmp : mp <> 0.
Hypothesis Hc8 : c mod 8 = 0.
Hypothesis Hm8 : mp mod 8 = 0.
Hypothesis Hb : body <> 0.
Hypothesis Hpos : (pos <= length bb)%nat.
Hypothesis Hst : st = 0 \/ 128 <= st < 240.
Hypothesis CC : rw_cells rsegs m c (cursor_cells body (Z.of_nat (length bb)) pos st).
Hypothesis BB : bytes_at rsegs m body bb.
Hypothesis CM : rw_cells rsegs m mp [CB 40 (b0 :: b1 :: r)].
Hypothesis D1 : c + 25 <= mp \/ mp + 40 <= c.
Hypothesis D2 : c + 25 <= body \/ body + Z.of_nat (length bb) <= c.
Hypothesis D3 : mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp.
Hypothesis MI : mem_inv rsegs m.
Hypothesis LR : length r = 38%nat.
(* the bounds of the three objects; the walk changes CC, BB, CM and MI, these stay *)
Hypothesis BCc : 0 <= c /\ c + 25 <= 2^64.
Hypothesis BMm : 0 <= mp /\ mp + 40 <= 2^64.
Hypothesis BBb : 0 <= body /\ body + Z.of_nat (length bb) <= 2^64.

Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation R := (msg_step bb pos st).
Local Abbreviation W := [(c, c + 25); (mp, mp + 40)].
Local Abbreviation Q := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (mr_code R))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' c (cursor_cells body L (mr_pos R) (mr_st R)) /\
         rw_cells rsegs m' mp (msg_cells body (b0 :: b1 :: r) R)).
Local Abbreviation ST pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 mm :=
  (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
(* the cursor with position p and status s *)
Local Abbreviation CUR p s := [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 (Z.of_nat p)); C1 (b8 s)].
(* the message after the four stores at 0x13c3c..0x13c48 *)
Local Abbreviation MC0 := [CB 2 [b0; b1]; C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 2 r)); C8 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 30 r)].
(* the message of a channel message once m->running is written *)
Local Abbreviation MC1 run := [CB 1 [b0]; C1 (b8 run); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 2 r));
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 30 r)].

Ltac wf_tac := cbn [cells_wf cell_wf skipn firstn]; rewrite ?length_firstn, ?length_skipn, ?LR; repeat split.

Lemma cur_conv : forall m1 (v : word) (b : byte) p s, rw_cells rsegs m1 c [C8 (Z_to_bv 64 body); C8 (Z_to_bv 64 L); C8 v; C1 b] ->
  v = Z_to_bv 64 (Z.of_nat p) -> b = b8 s -> rw_cells rsegs m1 c (cursor_cells body L p s).
Proof. intros m1 v b p s H -> ->. exact H. Qed.

(* 0x13dc0: mv a0, a2; ret *)
Lemma fin : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 : word) (m1 : word -> option byte),
  x12 = Z_to_bv 64 (mr_code R) ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (cursor_cells body L (mr_pos R) (mr_st R)) ->
  rw_cells rsegs m1 mp (msg_cells body (b0 :: b1 :: r) R) ->
  evt rsegs Q (ST 0x13dc0 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 m1).
Proof.
  intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 m1 -> MU WM MI1 HC HM.
  step. step.
  apply evt_done. cbv beta. do 12 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact HC|]. exact HM.
Qed.

Ltac cur_val := first [ reflexivity | (f_equal; uns; lia) ].
Ltac fin_with RS :=
  eapply fin;
  [ rewrite RS; cbn [mr_code mr_kind mr_plain]; first [reflexivity | apply bv_eq; reflexivity]
  | eassumption | eassumption | eassumption
  | rewrite RS; cbn [mr_pos mr_st mr_plain]; eapply cur_conv; [eassumption | cur_val | cur_val]
  | rewrite RS;
    cbn [msg_cells is_end mr_kind mr_plain writes_status writes_running writes_sysex writes_len
         mr_status mr_running mr_d1 mr_d2 mr_sysex mr_sysex_len mr_start mr_len nth Nat.eqb];
    eapply rw_conv; [eassumption | wf_tac | bytes_tac] ].

(* ---------- the sysex: F0 .. F7 ---------- *)

(* 0x13cdc: no F7 before the end of the body *)
Lemma scut : forall (x5 x6 x7 x11 x12 x13 x15 x16 x17 x28 : word) (m1 : word -> option byte),
  at8 bb pos = 240 -> (pos < length bb)%nat -> (forall q, (pos < q < length bb)%nat -> at8 bb q <> 247) ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (CUR pos st) -> rw_cells rsegs m1 mp MC0 ->
  evt rsegs Q (ST 0x13cdc x5 x6 x7 (Z_to_bv 64 c) x11 x12 x13 (Z_to_bv 64 L) x15 x16 x17 x28 m1).
Proof.
  intros x5 x6 x7 x11 x12 x13 x15 x16 x17 x28 m1 E0 Hlt Hnf MU1 WM1 MI1 HC HM.
  clear Hc8 Hm8.
  assert (RS : msg_step bb pos st = mr_plain MkSysexCut pos (length bb) 0 0).
  { unfold msg_step.
    replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    replace (at8 bb pos =? 0xf0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (find_f7_none_intro (skipn (S pos) bb)); [reflexivity|].
    intros k Hk. rewrite length_skipn in Hk. rewrite at8_skipn. apply Hnf. lia. }
  step. step. step. step.
  fin_with RS.
Qed.

(* 0x13c7c: the F7 at S i *)
Lemma sfound : forall (i : nat) (v15 v16 : Z) (x5 x6 x7 x13 x14 x17 x28 : word) (m1 : word -> option byte),
  at8 bb pos = 240 -> (pos <= i)%nat -> (S i < length bb)%nat -> at8 bb (S i) = 247 ->
  (forall q, (pos < q <= i)%nat -> at8 bb q <> 247) ->
  v15 = Z.of_nat i -> v16 = body + Z.of_nat pos ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (CUR pos st) -> rw_cells rsegs m1 mp MC0 ->
  evt rsegs Q (ST 0x13c7c x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 mp) (Z_to_bv 64 (Z.of_nat pos)) x13 x14
                 (Z_to_bv 64 v15) (Z_to_bv 64 v16) x17 x28 m1).
Proof.
  intros i v15 v16 x5 x6 x7 x13 x14 x17 x28 m1 E0 Hi1 Hi2 F7 Hnf -> -> MU1 WM1 MI1 HC HM.
  clear Hc8 Hm8.
  assert (RS : msg_step bb pos st = MsgRes MkSysex pos (pos + (i - pos) + 2) 0 0xf0 0 0 0 (S pos) (i - pos) (i - pos + 2)).
  { unfold msg_step.
    replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    replace (at8 bb pos =? 0xf0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite (find_f7_intro (skipn (S pos) bb) (i - pos)); [reflexivity | | |].
    - rewrite length_skipn. lia.
    - rewrite at8_skipn. replace (S pos + (i - pos))%nat with (S i) by lia. exact F7.
    - intros k Hk. rewrite at8_skipn. apply Hnf. lia. }
  step. step. step. step.
  step. br false.
  step. step. step. step. step. step. step. step. step. step. step.
  fin_with RS.
Qed.

(* 0x13c60: the scan for F7; the bytes pos+1 .. i are not F7 *)
Lemma sloop : forall (k i : nat) (v v5 v16 v17 : Z) (x15 x28 : word) (m1 : word -> option byte),
  at8 bb pos = 240 -> (pos <= i)%nat -> (i + k + 1 = length bb)%nat ->
  v = Z.of_nat i -> v5 = L - 1 -> v16 = body + Z.of_nat pos -> v17 = 2^64 - 1 - body ->
  (forall q, (pos < q <= i)%nat -> at8 bb q <> 247) ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (CUR pos st) -> bytes_at rsegs m1 body bb -> rw_cells rsegs m1 mp MC0 ->
  evt rsegs Q (ST 0x13c60 (Z_to_bv 64 v5) (Z_to_bv 64 247) (Z_to_bv 64 v) (Z_to_bv 64 c) (Z_to_bv 64 mp)
                 (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 body) (Z_to_bv 64 L) x15 (Z_to_bv 64 v16)
                 (Z_to_bv 64 v17) x28 m1).
Proof.
  clear Hc8 Hm8.
  induction k as [|k IH]; intros i v v5 v16 v17 x15 x28 m1 E0 Hi1 Hik -> -> -> -> Hnf MU1 WM1 MI1 HC HB HM.
  - step. br true.
    eapply scut; try eassumption; [lia|]. intros q Hq. apply Hnf. lia.
  - step. br false.
    step. step. step. br false.
    pose proof (rd8 m1 body bb (S i) HB ltac:(lia)) as HR.
    pose proof (at8_range bb (S i)) as XR.
    step. step. clear HR.
    step.
    destruct (Z.eq_dec (at8 bb (S i)) 247) as [F7|NF7].
    + br false.
      eapply (sfound i); try eassumption; lia.
    + br true.
      eapply (IH (S i)); try eassumption; try lia.
      intros q Hq. destruct (Nat.eq_dec q (S i)) as [->|NE]; [exact NF7 | apply Hnf; lia].
Qed.

(* ---------- the channel messages ---------- *)

(* 0x13d88: a status byte where data byte q is due *)
Lemma ccut : forall (q : nat) (run v7 : Z) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x28 : word) (m1 : word -> option byte),
  msg_step bb pos st = mr_plain MkChanCut pos q 0 run -> v7 = Z.of_nat q -> (q < length bb)%nat ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (CUR pos st) -> rw_cells rsegs m1 mp (MC1 run) ->
  evt rsegs Q (ST 0x13d88 x5 x6 (Z_to_bv 64 v7) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 x28 m1).
Proof.
  intros q run v7 x5 x6 x11 x12 x13 x14 x15 x16 x17 x28 m1 RS -> Hq MU1 WM1 MI1 HC HM.
  clear Hc8 Hm8.
  step. step. step. step.
  fin_with RS.
Qed.

(* 0x13d64: the data bytes d .. d + n - 1 are data bytes *)
Lemma ctail : forall (s run : Z) (d : nat) (v5 v14 v16 v17 : Z) (x6 x7 x28 : word) (m1 : word -> option byte),
  msg_step bb pos st = MsgRes MkChan pos (d + chan_n s) s s run (at8 bb d)
                         (if (chan_n s =? 2)%nat then at8 bb (S d) else 0) 0 0 (d + chan_n s - pos) ->
  128 <= s < 240 -> (pos <= d)%nat -> (d + chan_n s <= length bb)%nat ->
  v5 = Z.land s 224 -> v14 = 2^64 - 1 - body -> v16 = Z.of_nat (chan_n s) + Z.of_nat d -> v17 = Z.of_nat d ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (CUR pos st) -> bytes_at rsegs m1 body bb -> rw_cells rsegs m1 mp (MC1 run) ->
  evt rsegs Q (ST 0x13d64 (Z_to_bv 64 v5) x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 mp) (Z_to_bv 64 (Z.of_nat pos))
                 (Z_to_bv 64 body) (Z_to_bv 64 v14) (zxb (b8 s)) (Z_to_bv 64 v16) (Z_to_bv 64 v17) x28 m1).
Proof.
  intros s run d v5 v14 v16 v17 x6 x7 x28 m1 RS Hs Hd1 Hd2 -> -> -> -> MU1 WM1 MI1 HC HB HM.
  clear Hc8 Hm8.
  pose proof (chan_n_cases s) as HN.
  pose proof (at8_range bb d) as XD.
  step.
  step. br false.
  pose proof (rd8 _ body bb d HB ltac:(lia)) as HR.
  step. step. clear HR.
  step. step. step.
  rewrite land_c0 by lia.
  destruct HN as [N1|N1]; rewrite N1 in *; cbn [negb Nat.eqb]; cbv iota.
  - step. step.
    step. step. step. step. step. step.
    fin_with RS.
  - step. step. br false.
    pose proof (rd8 _ body bb (S d) HB ltac:(lia)) as HR2.
    step. step. clear HR2.
    step. step. step. step. step. step.
    fin_with RS.
Qed.

(* 0x13d20: a channel message with status s whose data starts at d; run is m->running *)
Lemma chan : forall (s run : Z) (d : nat) (v17 : Z) (x5 x6 x7 x16 x28 : word) (m1 : word -> option byte),
  msg_step bb pos st = chan_step bb pos st s run d ->
  128 <= s < 240 -> (pos <= d)%nat -> (d <= length bb)%nat -> v17 = Z.of_nat d ->
  munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (CUR pos st) -> bytes_at rsegs m1 body bb -> rw_cells rsegs m1 mp (MC1 run) ->
  evt rsegs Q (ST 0x13d20 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 mp) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 body)
                 (Z_to_bv 64 L) (zxb (b8 s)) x16 (Z_to_bv 64 v17) x28 m1).
Proof.
  intros s run d v17 x5 x6 x7 x16 x28 m1 RS Hs Hd1 Hd2 -> MU1 WM1 MI1 HC HB HM.
  clear Hc8 Hm8.
  pose proof (chan_n_cases s) as HN.
  step. rewrite zxbu by lia.
  step. step.
  step. rewrite snez_n by lia.
  step.
  step.
  destruct (Nat.ltb_spec (length bb) (d + chan_n s)) as [SH|SH].
  { (* the data bytes run past the end *)
    br false.
    assert (RS' : msg_step bb pos st = mr_plain MkChanShort pos (length bb) st run).
    { rewrite RS. unfold chan_step.
      replace (length bb <? d + chan_n s)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
    step. step. step. step.
    fin_with RS'. }
  br true.
  step. rewrite (not_val body) by first [lia | reflexivity].
  step.
  pose proof (at8_range bb d) as XD.
  step. br false.
  pose proof (rd8 _ body bb d HB ltac:(lia)) as HR.
  step. step. clear HR.
  step. rewrite sxb_lts by lia.
  destruct (Z.leb_spec 128 (at8 bb d)) as [C1d|C1d]; cbv iota.
  { eapply (ccut d run); try eassumption; try lia.
    rewrite RS. unfold chan_step.
    replace (length bb <? d + chan_n s)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (0x80 <=? at8 bb d) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  step. step. step.
  destruct HN as [N1|N2].
  { br false.
    eapply (ctail s run d); try eassumption; try lia.
    rewrite RS. unfold chan_step. rewrite N1.
    replace (length bb <? d + 1)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (0x80 <=? at8 bb d) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  br true.
  pose proof (at8_range bb (S d)) as XD2.
  step. br false.
  pose proof (rd8 _ body bb (S d) HB ltac:(lia)) as HR2.
  step. step. clear HR2.
  step. rewrite sxb_lts by lia.
  destruct (Z.leb_spec 128 (at8 bb (S d))) as [C2d|C2d]; cbv iota.
  { eapply (ccut (S d) run); try eassumption; try lia.
    rewrite RS. unfold chan_step. rewrite N2.
    replace (length bb <? d + 2)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (0x80 <=? at8 bb d) with false by (symmetry; apply Z.leb_gt; lia).
    replace (0x80 <=? at8 bb (S d)) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  step. step. step. br false.
  eapply (ctail s run d); try eassumption; try lia.
  rewrite RS. unfold chan_step. rewrite N2.
  replace (length bb <? d + 2)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (0x80 <=? at8 bb d) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x80 <=? at8 bb (S d)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* ---------- from the entry ---------- *)

Ltac to_mc1 run := match goal with H : rw_cells rsegs ?mm mp _ |- _ =>
  let H' := fresh "HM" in
  assert (H' : rw_cells rsegs mm mp (MC1 run)) by (eapply rw_conv; [exact H | wf_tac | bytes_tac]); clear H
  end.

Lemma mn_main : evt rsegs Q (ST 0x13bec t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 mp) a2 a3 a4 a5 a6 a7 t3 m).
Proof.
  pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold cursor_cells in CC.
  step. step. br false.
  step. br false.
  step. rewrite (land7 c) by lia. step. br false.
  clear Hc8.
  step. step. step.
  destruct (Nat.eq_dec pos (length bb)) as [E|E].
  { br true. step. step. step. step.
    assert (RS : msg_step bb pos st = mr_plain MkEnd pos pos st 0)
      by (unfold msg_step; replace (length bb <=? pos)%nat with true by (symmetry; apply Nat.leb_le; lia); reflexivity).
    apply evt_done. cbv beta. rewrite RS. cbn [mr_code mr_pos mr_st mr_plain mr_kind msg_cells is_end].
    do 12 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CC|]. exact CM. }
  br false.
  assert (Hlt : (pos < length bb)%nat) by lia.
  step. step. step. br false.
  step. step. step. step. rewrite (snez_seqz_xor body (body + Z.of_nat pos)) by lia. br false.
  step. br false.
  step.
  rewrite (land7 mp) by lia. step. br false.
  clear Hm8.
  pose proof (rd8 m body bb pos BB ltac:(lia)) as HR0.
  pose proof (at8_range bb pos) as X0.
  step. clear HR0. step.
  step. step. step. step.
  match goal with H : rw_cells rsegs ?mm mp _ |- _ =>
    assert (HM : rw_cells rsegs mm mp MC0) by (eapply rw_conv; [exact H | wf_tac | bytes_tac]); clear H
  end.
  step.
  destruct (Z.eq_dec (at8 bb pos) 240) as [X240|X240].
  { (* F0: a sysex *)
    br false.
    step. step. step. step.
    eapply (sloop (length bb - 1 - pos) pos); try eassumption; try lia.
    all: first [ eapply not_val; [lia | reflexivity] | intros q Hq; lia ]. }
  br true.
  step. rewrite zxbu by lia. step.
  rewrite sl56 by lia.
  destruct (Z.leb_spec 128 (at8 bb pos)) as [X128|X128]; cbv iota.
  { (* a status byte *)
    step. step.
    destruct (Z.ltb_spec (at8 bb pos) 240) as [XL|XL].
    { br true. step. step.
      to_mc1 0.
      eapply (chan (at8 bb pos) 0 (S pos)); try eassumption; try lia.
      unfold msg_step.
      replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
      replace (0x80 <=? at8 bb pos) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    br false.
    assert (RS : msg_step bb pos st = mr_plain MkBadStatus pos (S pos) 0 0).
    { unfold msg_step.
      replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0xf0 <=? at8 bb pos) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    step. step. step. step. step.
    fin_with RS. }
  (* a data byte: the running status *)
  step. step.
  destruct (Z.eq_dec st 0) as [S0|S0].
  { br true.
    assert (RS : msg_step bb pos st = mr_plain MkNoStatus pos (S pos) st 0).
    { unfold msg_step.
      replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
      replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
      replace (0x80 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
      replace (st =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    step. step. step. step.
    fin_with RS. }
  br false.
  step. step. step. step.
  to_mc1 1.
  eapply (chan st 1 pos); try eassumption; try lia.
  unfold msg_step.
  replace (length bb <=? pos)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  replace (at8 bb pos =? 0xf0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (0xf0 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x80 <=? at8 bb pos) with false by (symmetry; apply Z.leb_gt; lia).
  replace (st =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

End MN.

Theorem diginet_msg_next_holds : diginet_msg_next_contract.
Proof.
  unfold diginet_msg_next_contract, DIGINET_MSG_NEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c mp body bb mj pos st Hc Hmp Hc8 Hm8 Hb Hpos Hst CC BB CM D1 D2 D3 MI.
  assert (LJ : length mj = 40%nat) by (destruct CM as [[[Hl _] _] _]; exact Hl).
  destruct mj as [|b0 [|b1 r]]; try discriminate LJ.
  assert (LR : length r = 38%nat) by (cbn in LJ; lia).
  pose proof (rw_cells_bound rsegs m c _ CC) as BCc. cbn [cells_size csize cursor_cells Nat.add] in BCc.
  pose proof (rw_cells_bound rsegs m mp _ CM) as BMm. cbn [cells_size csize Nat.add] in BMm.
  pose proof (bytes_at_bound rsegs m body bb BB) as BBb.
  eapply mn_main; try eassumption; first [exact Hst | lia].
Qed.
