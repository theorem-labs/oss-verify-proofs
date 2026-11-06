(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 372 of its 412 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame: module paths, every pc by -0x180 (entry 0x13cb4 -> 0x13b34), the header's image. *)
(* Walk of diginet_msg_next (src/diginet_msg.c:27-103 at 835f336c) in fuzz_decode.plain, 0x13b34.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import diginet_cursor_init_c diginet_msg_next_c.
Import ListNotations.
Open Scope Z_scope.

(* ---------- facts about bytes, words and cells ---------- *)

Lemma rd8 : forall m A l i, bytes_at rsegs m A l -> (i < length l)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b8 (at8 l i)].
Proof.
  intros m A l i BL Hi. rewrite (bytes_at_ov_read rsegs m A l i 1 BL) by lia. f_equal. clear BL.
  unfold at8. rewrite b8_bz.
  revert i Hi. induction l as [|x l IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma zxb_b8 : forall x, 0 <= x < 256 -> zxb (b8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. change (bv_unsigned (b8 x)) with (bz (b8 x)). rewrite bz_b8 by lia. reflexivity. Qed.

Lemma sxb_lts : forall x, 0 <= x < 256 -> bv_lts (sxb (b8 x)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  intros x Hx.
  assert (G : forall x, 0 <= x < 2^8 -> Bool.eqb (bv_lts (sxb (b8 x)) (Z_to_bv 64 0)) (128 <=? x) = true).
  { apply (byte_forall (fun x => Bool.eqb (bv_lts (sxb (b8 x)) (Z_to_bv 64 0)) (128 <=? x))).
    vm_compute. reflexivity. }
  apply Bool.eqb_prop, G. lia.
Qed.

Lemma sl56 : forall x, 0 <= x < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 56)) (Z_to_bv 64 0) = (128 <=? x).
Proof.
  intros x Hx. rewrite unsigned_lit by lia.
  assert (G : forall x, 0 <= x < 2^8 ->
            Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x) = true).
  { apply (byte_forall (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x))).
    vm_compute. reflexivity. }
  apply Bool.eqb_prop, G. lia.
Qed.

(* the inlined channel_data_len: 1 + (status & 0xe0 != 0xc0) *)
Lemma snez_n : forall s, 0 <= s < 256 ->
  bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1 = Z.of_nat (chan_n s).
Proof.
  intros s Hs.
  assert (G : forall s, 0 <= s < 2^8 ->
            Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1)
                  (Z.of_nat (chan_n s)) = true).
  { apply (byte_forall (fun s => Z.eqb (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land s 224 + -192))) + 1)
                                       (Z.of_nat (chan_n s)))).
    vm_compute. reflexivity. }
  apply Z.eqb_eq, G. lia.
Qed.

Lemma land_c0 : forall s, 0 <= s < 256 ->
  bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192) = (chan_n s =? 1)%nat.
Proof.
  intros s Hs.
  assert (G : forall s, 0 <= s < 2^8 ->
            Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat = true).
  { apply (byte_forall (fun s => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land s 224)) (Z_to_bv 64 192)) (chan_n s =? 1)%nat)).
    vm_compute. reflexivity. }
  apply Bool.eqb_prop, G. lia.
Qed.

Lemma nn : forall y, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 (- y).
Proof.
  intros y. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma eqb0_neg : forall x, -2^64 < x < 0 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite unsigned_lit_wrap. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma rw_conv : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] V] W' EB. split; [split|].
  - exact W'.
  - rewrite EB. exact B.
  - rewrite <- (cells_bytes_length cs' W'), EB, (cells_bytes_length cs W). exact V.
Qed.

Lemma firstn2 : forall (l : list byte), (2 <= length l)%nat -> firstn 2 l = [nth 0 l (b8 0); nth 1 l (b8 0)].
Proof. intros [|x [|y l]] H; cbn in *; [lia|lia|reflexivity]. Qed.
Lemma f12a : forall (l : list byte), (2 <= length l)%nat -> firstn 1 (firstn 2 l) = [nth 0 l (b8 0)].
Proof. intros [|x [|y l]] H; cbn in *; [lia|lia|reflexivity]. Qed.
Lemma le2_0 : le2 (Z_to_bv 64 0) = [b8 0; b8 0].
Proof. reflexivity. Qed.
Lemma le2_240 : le2 (Z_to_bv 64 240) = [b8 240; b8 0].
Proof. reflexivity. Qed.
Lemma b8u : forall v v', 0 <= v < 2^64 -> v' = v -> b8 v' = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v)).
Proof. intros v v' H ->. rewrite unsigned_lit by exact H. reflexivity. Qed.

Ltac mnu := rewrite ?unsigned_lit by lia.
(* bv_unsigned (Z_to_bv 64 z) to z, for every innermost such z that lia puts in range *)
Ltac uin := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with context [bv_unsigned _] => fail | _ => rewrite (unsigned_lit z) by lia end
  end.
Ltac mnb v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; mnu; solve_cond_rec]
  end.
Ltac mnbw v tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; tac]
  end.

(* a one-byte store of a word v: the cell holds its low byte *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* the byte i of bb, read from the memory that holds bb now *)
Ltac rdat i := match goal with H : bytes_at _ ?mm _ ?l |- _ =>
  let HR := fresh "HR" in pose proof (rd8 mm _ l i H ltac:(lia)) as HR end.

(* split two lists of cell bytes that have the same shape *)
Ltac mnls := repeat lazymatch goal with
  | |- ?x :: _ = ?y :: _ => f_equal
  | |- le8 _ ++ _ = le8 _ ++ _ => f_equal
  | |- le8 _ = le8 _ => f_equal
  | |- firstn _ _ ++ _ = firstn _ _ ++ _ => f_equal
  end.
Ltac mncv := first [ reflexivity | (apply b8u; lia) | (f_equal; lia) | (f_equal; uin; lia) ].
(* a cells hypothesis H to the cells of the goal *)
Ltac mncnv H :=
  eapply rw_conv; [ exact H
                  | cbn [cells_wf cell_wf]; repeat split; rewrite ?length_firstn, ?length_skipn;
                    match goal with L : length _ = 40%nat |- _ => rewrite L end; reflexivity
                  | cbn [cells_bytes cbytes app];
                    rewrite ?f12a, ?firstn2, ?le2_0, ?le2_240 by lia;
                    cbn [app]; mnls; mncv ].

(* ---------- the post of the contract ---------- *)

Definition mn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z)
    : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (mr_code (msg_step bb pos st)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(c, c + 25); (mp, mp + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' c (cursor_cells body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st))
                           (mr_st (msg_step bb pos st))) /\
    rw_cells rsegs m' mp (msg_cells body mj (msg_step bb pos st)).

(* the 40 bytes of the message after the four stores at 0x13b5c..0x13b68 *)
Definition MC0 (mj : list byte) (pos : nat) : list cell :=
  [CB 2 (firstn 2 mj); C2 (Z_to_bv 64 0); CB 4 (firstn 4 (skipn 4 mj)); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)].

Section MN.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (c mp body : Z) (bb mj : list byte) (pos : nat) (st : Z).
Hypothesis Hc : c <> 0.
Hypothesis Hmp : mp <> 0.
Hypothesis Hst : st_ok st.
Hypothesis BC : 0 <= c /\ c + 25 <= 2^64.
Hypothesis BM : 0 <= mp /\ mp + 40 <= 2^64.
Hypothesis BB : 0 <= body /\ body + Z.of_nat (length bb) <= 2^64.
Hypothesis D1 : c + 25 <= mp \/ mp + 40 <= c.
Hypothesis D2 : c + 25 <= body \/ body + Z.of_nat (length bb) <= c.
Hypothesis D3 : mp + 40 <= body \/ body + Z.of_nat (length bb) <= mp.
Hypothesis LJ : length mj = 40%nat.

Local Abbreviation L := (Z.of_nat (length bb)).
Local Abbreviation R := (msg_step bb pos st).
Local Abbreviation Q := (mn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m c mp body bb mj pos st).
Local Abbreviation W := [(c, c + 25); (mp, mp + 40)].
Local Abbreviation ST pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 mm :=
  (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* 0x13cb8: mv a0, a2; ret *)
Lemma fin : forall (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 : word) (m1 : word -> option byte) (code : Z),
  code = mr_code R -> munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 c (cursor_cells body L (mr_pos R) (mr_st R)) ->
  rw_cells rsegs m1 mp (msg_cells body mj R) ->
  evt rsegs Q (ST 0x13cb8 x5 x6 x7 x10 x11 (Z_to_bv 64 code) x13 x14 x15 x16 x17 x28 m1).
Proof.
  intros x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 m1 code -> MU WM MI HC HM.
  step. step.
  apply evt_done. unfold mn_post.
  do 12 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HC|]. exact HM.
Qed.


(* The scan of src/diginet_msg.c:45-46 at 0x13b7c: a3 = k, the bytes pos+1 .. pos+k-1 are no F7. *)
Lemma sx_loop : forall (n k : nat) (x5 x6 x7 x28 : word) (v5 v13 : Z) (m1 : word -> option byte),
  n = (length bb - pos - k)%nat -> (1 <= k)%nat -> (pos + k <= length bb)%nat ->
  at8 bb pos = 0xf0 ->
  (forall i, (1 <= i < k)%nat -> at8 bb (pos + i) <> 0xf7) ->
  v5 = Z.of_nat pos - L -> v13 = Z.of_nat k ->
  rw_cells rsegs m1 c (cursor_cells body L pos st) -> rw_cells rsegs m1 mp (MC0 mj pos) ->
  bytes_at rsegs m1 body bb -> munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q (ST 0x13b7c x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 mp) (Z_to_bv 64 (Z.of_nat pos)) (Z_to_bv 64 v13)
                 (Z_to_bv 64 L) (Z_to_bv 64 v5) (Z_to_bv 64 (body + Z.of_nat pos)) (Z_to_bv 64 247) x28 m1).
Proof.
  induction n as [|n IH]; intros k x5 x6 x7 x28 v5 v13 m1 Hn Hk1 HkL F0 NF E5 E13 HC HM HB MU WM MI;
    subst v5 v13; unfold cursor_cells in HC; unfold MC0 in HM.
  - (* pos + k = L: no F7 up to the end, 0x13be4 *)
    assert (EK : (pos + k = length bb)%nat) by lia.
    step.
    replace (Z.of_nat pos - L + Z.of_nat k) with 0 by lia.
    step. mnb true. step. step. step. step.
    assert (ER : R = mr_plain MkSysexCut pos (length bb) 0 0).
    { unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [lia|]. rewrite F0, Z.eqb_refl.
      rewrite find_f7_none_intro; [reflexivity|].
      intros k0 Hk0. rewrite length_skipn in Hk0. rewrite at8_skipn.
      replace (S pos + k0)%nat with (pos + S k0)%nat by lia. apply NF. lia. }
    eapply fin; [rewrite ER; reflexivity | eassumption | eassumption | eassumption | | ].
    + rewrite ER. cbn [mr_pos mr_st mr_plain]. unfold cursor_cells. mncnv HC.
    + rewrite ER. unfold msg_cells.
      cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1 mr_d2
           mr_sysex mr_sysex_len mr_start mr_len mr_plain].
      mncnv HM.
  - assert (EK : (pos + k < length bb)%nat) by lia.
    step. step. mnbw false ltac:(apply eqb0_neg; lia).
    step. uin.
    pose proof (rd8 m1 body bb (pos + k) HB EK) as HR. rewrite Nat2Z.inj_add, Z.add_assoc in HR.
    step. rewrite zxb_b8 by (pose proof (at8_range bb (pos + k)); lia).
    step. uin.
    step.
    pose proof (at8_range bb (pos + k)) as RK.
    destruct (Z.eqb_spec (at8 bb (pos + k)) 247) as [F7|F7].
    + (* the F7 at pos + k: 0x13b94 *)
      mnb false. do 13 step.
      assert (ER : R = MsgRes MkSysex pos (pos + (k - 1) + 2) 0 0xf0 0 0 0 (S pos) (k - 1) (k - 1 + 2)).
      { unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [lia|]. rewrite F0, Z.eqb_refl.
        rewrite (find_f7_intro (skipn (S pos) bb) (k - 1)); [reflexivity | | | ].
        - rewrite length_skipn. lia.
        - rewrite at8_skipn. replace (S pos + (k - 1))%nat with (pos + k)%nat by lia. exact F7.
        - intros k0 Hk0. rewrite at8_skipn.
          replace (S pos + k0)%nat with (pos + S k0)%nat by lia. apply NF. lia. }
      eapply fin; [rewrite ER; reflexivity | eassumption | eassumption | eassumption | | ].
      * rewrite ER. cbn [mr_pos mr_st]. unfold cursor_cells. mncnv HC.
      * rewrite ER. unfold msg_cells.
        cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1 mr_d2
             mr_sysex mr_sysex_len mr_start mr_len].
        mncnv HM.
    + mnb true.
      eapply (IH (S k)); try eassumption; try lia.
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE]; [exact F7|]. apply NF. lia.
Qed.

(* src/diginet_msg.c:83-102 from 0x13c24: a3 = status, a6 = d (the first data byte), t2 = m->running. *)
Lemma chan : forall (status run : Z) (d : nat) (x5 x6 x17 x28 : word) (vs vr v16 : Z) (m1 : word -> option byte),
  0x80 <= status < 0xf0 -> (run = 0 \/ run = 1) -> (pos <= d)%nat -> (d <= length bb)%nat ->
  R = chan_step bb pos st status run d ->
  vs = status -> vr = run -> v16 = Z.of_nat d ->
  rw_cells rsegs m1 c (cursor_cells body L pos st) -> rw_cells rsegs m1 mp (MC0 mj pos) ->
  bytes_at rsegs m1 body bb -> munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Q (ST 0x13c24 x5 x6 (Z_to_bv 64 vr) (Z_to_bv 64 c) (Z_to_bv 64 mp) (Z_to_bv 64 (Z.of_nat pos))
                 (Z_to_bv 64 vs) (Z_to_bv 64 L) (Z_to_bv 64 body) (Z_to_bv 64 v16) x17 x28 m1).
Proof.
  intros status run d x5 x6 x17 x28 vs vr v16 m1 Hs Hr Hd1 Hd2 ER Es Er E16 HC HM HB MU WM MI.
  subst vs vr v16. unfold cursor_cells in HC.
  assert (HM2 : rw_cells rsegs m1 mp [CB 2 (firstn 2 mj); C1 (b8 0); C1 (b8 0); CB 4 (firstn 4 (skipn 4 mj));
                  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (Z.of_nat pos)); CB 8 (skipn 32 mj)])
    by (unfold MC0 in HM; mncnv HM).
  clear HM.
  pose proof (chan_n_cases status) as NC.
  do 5 step.
  rewrite (unsigned_lit status) by lia. rewrite snez_n by lia.
  step. step.
  assert (LB : L <= 2^64 - 25) by lia.
  destruct (Nat.ltb_spec (length bb) (d + chan_n status)) as [SH|SH].
  - (* data_at + n > c->len: 0x13c40 *)
    mnb false. do 4 step.
    assert (ER2 : R = mr_plain MkChanShort pos (length bb) st run).
    { rewrite ER. unfold chan_step. destruct (Nat.ltb_spec (length bb) (d + chan_n status)); [reflexivity|lia]. }
    eapply fin; [rewrite ER2; reflexivity | eassumption | eassumption | eassumption | | ].
    + rewrite ER2. cbn [mr_pos mr_st mr_plain]. unfold cursor_cells. mncnv HC.
    + rewrite ER2. unfold msg_cells.
      cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1 mr_d2
           mr_sysex mr_sysex_len mr_start mr_len mr_plain].
      mncnv HM2.
  - mnb true.
    assert (Hd : (d < length bb)%nat) by (destruct NC as [N|N]; rewrite N in SH; lia).
    pose proof (at8_range bb d) as RD.
    step. step.
    match goal with H : bytes_at _ ?mm body bb |- _ => pose proof (rd8 mm body bb d H Hd) as HR end.
    step. step. rewrite sxb_lts by lia.
    destruct (Z.leb_spec 128 (at8 bb d)) as [B1|B1].
    + (* a status byte at d: 0x13c88 *)
      do 5 step.
      assert (ER2 : R = mr_plain MkChanCut pos d 0 run).
      { rewrite ER. unfold chan_step. destruct (Nat.ltb_spec (length bb) (d + chan_n status)); [lia|].
        destruct (Z.leb_spec 0x80 (at8 bb d)); [reflexivity|lia]. }
      eapply fin; [rewrite ER2; reflexivity | eassumption | eassumption | eassumption | | ].
      * rewrite ER2. cbn [mr_pos mr_st mr_plain]. unfold cursor_cells.
        rewrite nn in HC. rewrite (unsigned_lit (Z.of_nat d)) in HC by lia. mncnv HC.
      * rewrite ER2. unfold msg_cells.
        cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1 mr_d2
             mr_sysex mr_sysex_len mr_start mr_len mr_plain].
        mncnv HM2.
    + do 4 step.
      destruct NC as [N1|N2].
      * (* n = 1: the data byte is d *)
        rewrite N1. mnb false.
        step. step. rdat d. step. rewrite zxb_b8 by lia. step. step.
        step. rewrite land_c0 by lia. rewrite N1. change (negb (1 =? 1)%nat) with false. cbv iota.
        do 2 step. do 6 step.
        assert (ER2 : R = MsgRes MkChan pos (d + 1) status status run (at8 bb d) 0 0 0 (d + 1 - pos)).
        { rewrite ER. unfold chan_step. destruct (Nat.ltb_spec (length bb) (d + chan_n status)); [lia|].
          destruct (Z.leb_spec 0x80 (at8 bb d)); [lia|]. rewrite N1. reflexivity. }
        eapply fin; [rewrite ER2; reflexivity | eassumption | eassumption | eassumption | | ].
        -- rewrite ER2. cbn [mr_pos mr_st]. unfold cursor_cells. mncnv HC.
        -- rewrite ER2. unfold msg_cells.
           cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1 mr_d2
                mr_sysex mr_sysex_len mr_start mr_len].
           mncnv HM2.
      * (* n = 2: the data bytes are d and d + 1 *)
        rewrite N2. mnb true.
        assert (Hd' : (S d < length bb)%nat) by (rewrite N2 in SH; lia).
        pose proof (at8_range bb (S d)) as RD'.
        rdat (S d). step. step. rewrite sxb_lts by lia.
        destruct (Z.leb_spec 128 (at8 bb (S d))) as [B2|B2].
        -- (* a status byte at d + 1: 0x13c88 *)
           do 5 step.
           assert (ER2 : R = mr_plain MkChanCut pos (S d) 0 run).
           { rewrite ER. unfold chan_step. destruct (Nat.ltb_spec (length bb) (d + chan_n status)); [lia|].
             destruct (Z.leb_spec 0x80 (at8 bb d)); [lia|]. rewrite N2.
             destruct (Z.leb_spec 0x80 (at8 bb (S d))); [reflexivity|lia]. }
           eapply fin; [rewrite ER2; reflexivity | eassumption | eassumption | eassumption | | ].
           ++ rewrite ER2. cbn [mr_pos mr_st mr_plain]. unfold cursor_cells.
              rewrite nn in HC. rewrite (unsigned_lit (Z.of_nat d)) in HC by lia. mncnv HC.
           ++ rewrite ER2. unfold msg_cells.
              cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1
                   mr_d2 mr_sysex mr_sysex_len mr_start mr_len mr_plain].
              mncnv HM2.
        -- do 4 step. mnb false.
           step. step. rdat d. step. rewrite zxb_b8 by lia. step. step.
           step. rewrite land_c0 by lia. rewrite N2. change (negb (2 =? 1)%nat) with true. cbv iota.
           rdat (S d). step. rewrite zxb_b8 by lia.
           do 6 step.
           assert (ER2 : R = MsgRes MkChan pos (d + 2) status status run (at8 bb d) (at8 bb (S d)) 0 0 (d + 2 - pos)).
           { rewrite ER. unfold chan_step. destruct (Nat.ltb_spec (length bb) (d + chan_n status)); [lia|].
             destruct (Z.leb_spec 0x80 (at8 bb d)); [lia|]. rewrite N2.
             destruct (Z.leb_spec 0x80 (at8 bb (S d))); [lia|]. reflexivity. }
           eapply fin; [rewrite ER2; reflexivity | eassumption | eassumption | eassumption | | ].
           ++ rewrite ER2. cbn [mr_pos mr_st]. unfold cursor_cells. mncnv HC.
           ++ rewrite ER2. unfold msg_cells.
              cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1
                   mr_d2 mr_sysex mr_sysex_len mr_start mr_len].
              mncnv HM2.
Qed.

Ltac msg_plain H :=
  unfold msg_cells;
  cbn [is_end mr_kind writes_status writes_running writes_len writes_sysex mr_status mr_running mr_d1 mr_d2
       mr_sysex mr_sysex_len mr_start mr_len mr_plain];
  mncnv H.

(* The walk from the entry 0x13b34. *)
Lemma walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 : word),
  (pos <= length bb)%nat ->
  rw_cells rsegs m c (cursor_cells body L pos st) -> bytes_at rsegs m body bb ->
  rw_cells rsegs m mp [CB 40 mj] -> mem_inv rsegs m ->
  evt rsegs Q (ST 0x13b34 t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 mp) a2 a3 a4 a5 a6 a7 t3 m).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 Hpos HC HB HM MI.
  unfold cursor_cells in HC.
  pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof MI as MI0.
  step. step. mnb false. step. mnb false. step. step. step.
  destruct (Nat.leb_spec (length bb) pos) as [E|E].
  - (* c->pos >= c->len: 0 *)
    mnb true. step. step.
    assert (ER : R = mr_plain MkEnd pos pos st 0).
    { unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [reflexivity|lia]. }
    eapply fin; [rewrite ER; reflexivity | exact MU | exact WM | exact MI | | ].
    + rewrite ER. exact HC.
    + rewrite ER. exact HM.
  - mnb false. step. step.
    pose proof (at8_range bb pos) as A0.
    rdat pos. step. rewrite zxb_b8 by lia.
    do 5 step.
    rewrite !skipn_skipn in HM. cbn [Nat.add] in HM.
    step.
    destruct (Z.eqb_spec (at8 bb pos) 0xf0) as [F0|F0].
    + (* lead F0: system exclusive *)
      mnb false. do 3 step. uin.
      eapply (sx_loop (length bb - pos - 1) 1); try eassumption; lia.
    + mnb true. step. step. rewrite sl56 by lia.
      destruct (Z.leb_spec 128 (at8 bb pos)) as [H80|H80].
      * (* lead & 0x80 *)
        cbv iota. do 3 step. uin.
        destruct (Z.ltb_spec (at8 bb pos) 240) as [HF|HF].
        -- mnb true. step.
           eapply (chan (at8 bb pos) 0 (S pos)); try eassumption; try lia.
           unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [lia|].
           destruct (Z.eqb_spec (at8 bb pos) 0xf0); [lia|].
           destruct (Z.leb_spec 0xf0 (at8 bb pos)); [lia|].
           destruct (Z.leb_spec 0x80 (at8 bb pos)); [reflexivity|lia].
        -- (* F1..FF: -8 *)
           mnb false. do 4 step.
           assert (ER : R = mr_plain MkBadStatus pos (S pos) 0 0).
           { unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [lia|].
             destruct (Z.eqb_spec (at8 bb pos) 0xf0); [lia|].
             destruct (Z.leb_spec 0xf0 (at8 bb pos)); [reflexivity|lia]. }
           eapply fin; [rewrite ER; reflexivity | eassumption | eassumption | eassumption | | ].
           ++ rewrite ER. cbn [mr_pos mr_st mr_plain]. unfold cursor_cells. mncnv HC.
           ++ rewrite ER. msg_plain HM.
      * (* a data byte: running status *)
        assert (Rst : 0 <= st < 256) by (destruct Hst; lia).
        cbv iota. step. rewrite zxb_b8 by lia. step.
        destruct (Z.eqb_spec st 0) as [S0|S0].
        -- (* no running status: -7 *)
           mnb true. do 4 step.
           assert (ER : R = mr_plain MkNoStatus pos (S pos) st 0).
           { unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [lia|].
             destruct (Z.eqb_spec (at8 bb pos) 0xf0); [lia|].
             destruct (Z.leb_spec 0xf0 (at8 bb pos)); [lia|].
             destruct (Z.leb_spec 0x80 (at8 bb pos)); [lia|].
             destruct (Z.eqb_spec st 0); [reflexivity|lia]. }
           eapply fin; [rewrite ER; reflexivity | eassumption | eassumption | eassumption | | ].
           ++ rewrite ER. cbn [mr_pos mr_st mr_plain]. unfold cursor_cells. mncnv HC.
           ++ rewrite ER. msg_plain HM.
        -- mnb false. do 3 step.
           eapply (chan st 1 pos); try eassumption; try lia.
           ++ destruct Hst; lia.
           ++ unfold msg_step. destruct (Nat.leb_spec (length bb) pos); [lia|].
              destruct (Z.eqb_spec (at8 bb pos) 0xf0); [lia|].
              destruct (Z.leb_spec 0xf0 (at8 bb pos)); [lia|].
              destruct (Z.leb_spec 0x80 (at8 bb pos)); [lia|].
              destruct (Z.eqb_spec st 0); [lia|reflexivity].
Qed.

End MN.

Theorem diginet_msg_next_holds : diginet_msg_next_contract.
Proof.
  unfold diginet_msg_next_contract, DIGINET_MSG_NEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c mp body bb mj pos st Hc Hmp Hpos Hst HC HB HM D1 D2 D3 MI.
  pose proof (rw_cells_bound _ _ _ _ HC) as BC. pose proof (rw_cells_bound _ _ _ _ HM) as BM.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  unfold cursor_cells in BC. cbn [cells_size csize Nat.add] in BC, BM.
  assert (LJ : length mj = 40%nat) by (destruct HM as [[[LW _] _] _]; exact LW).
  eapply walk; try eassumption; lia.
Qed.
