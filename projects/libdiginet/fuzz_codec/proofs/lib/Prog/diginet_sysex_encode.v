(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 526 of its 548 lines of code are new or changed and 38 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells memcpy_c diginet_sysex_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** diginet_sysex_encode of the plain image (0x152f0, 70 instructions, frame 0x30), walked with the tactics of
    libreac/fuzz_knock's walks (Lib/Tac.v, Lib/Step.v). Paths: the checks of the C in order (out, device bit 7,
    payload, fn = 0x70, fn bit 7, len + 5 > 24), each returning before any store to out; the payload loop
    (0x15374, one `lb` per byte, a loop lemma over the bytes left); the stores of the header, memcpy of the
    payload to out + 4 (len > 0) and the tail stores (0xf7, len + 5, display, key 0). The out area is carried
    as cells in three pieces after the header stores (header and payload at out, the 0xf7 byte and the kept
    bytes up to 24 at out + 4 + len, the last 8 bytes at out + 24) and joined at the end. *)

(* Stores of one byte from a register give le1 of the register: a C1 cell of its low byte. *)
#[local] Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

#[local] Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* ---- byte and spec facts ---- *)

Lemma sx_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma sx_shl56 : forall x, 0 <= x < 256 ->
  (Z.shiftl x 56 mod 18446744073709551616 < 9223372036854775808 <-> x < 128).
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 56) with 72057594037927936; lia).
  change (2 ^ 56) with 72057594037927936. lia.
Qed.

Lemma sx_sxb : forall b : byte,
  bv_unsigned (sxb b) < 9223372036854775808 <-> Z.testbit (bv_unsigned b) 7 = false.
Proof.
  intros b. unfold sxb. rewrite unsigned_lit_wrap.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  remember (bv_unsigned b) as x eqn:Ex. clear Ex.
  destruct (Z.ltb_spec0 x 128) as [L|L].
  - rewrite (Z.mod_small (x + 128) 256) by lia. replace (x + 128 - 128) with x by lia.
    rewrite Z.mod_small by lia.
    rewrite (testbit_high_false x 7 7) by (change (2 ^ 7) with 128; lia). split; [reflexivity | intros _; lia].
  - assert (E1 : (x + 128) mod 256 = x - 128) by (symmetry; apply Z.mod_unique with 1; lia).
    rewrite E1. replace (x - 128 - 128) with (x - 256) by lia.
    change (2 ^ 64) with 18446744073709551616.
    assert (E2 : (x - 256) mod 18446744073709551616 = x - 256 + 18446744073709551616)
      by (symmetry; apply Z.mod_unique with (-1); lia).
    rewrite E2.
    assert (T : Z.testbit x 7 = true).
    { rewrite Z.testbit_eqb by lia. change (2 ^ 7) with 128.
      replace (x / 128) with 1 by (apply Z.div_unique with (x - 128); lia). reflexivity. }
    rewrite T. split; [intros; exfalso; lia | discriminate].
Qed.

Definition hib (x : Z) : bool := Z.testbit x 7.

Lemma ex_prefix_step : forall (l : list Z) (i : nat),
  existsb hib (firstn i l) = false -> hib (nth i l 0) = false -> (i < length l)%nat ->
  existsb hib (firstn (S i) l) = false.
Proof.
  induction l as [|x l IH]; intros i H1 H2 H3; cbn in *; [lia|].
  destruct i as [|i]; cbn in *.
  - rewrite H2. reflexivity.
  - apply orb_false_iff in H1. destruct H1 as [H1a H1b]. rewrite H1a. cbn. apply IH; [exact H1b | exact H2 | lia].
Qed.

Lemma ex_hit : forall (l : list Z) (i : nat), hib (nth i l 0) = true -> (i < length l)%nat -> existsb hib l = true.
Proof.
  intros l i H Hi. apply existsb_exists. exists (nth i l 0). split; [apply nth_In; exact Hi | exact H].
Qed.

Lemma zb_nth : forall (pl : list byte) (i : nat), nth i (zb pl) 0 = bv_unsigned (nth i pl (Z_to_bv 8 0)).
Proof.
  intros pl i. unfold zb. change 0 with ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0)) at 1.
  apply map_nth.
Qed.

Lemma zb_length : forall pl, length (zb pl) = length pl.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma bz_zb : forall pl, bz (zb pl) = pl.
Proof.
  induction pl as [|b pl IH]; [reflexivity|]. cbn. unfold bz, zb in IH. rewrite IH. f_equal.
  apply bv_eq. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma sx_spec_arg : forall dev fn l, 0x7f < dev -> sysex_spec dev fn l = (E_ARG, None).
Proof. intros. unfold sysex_spec. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma sx_spec_refused : forall dev l, dev <= 0x7f -> sysex_spec dev 0x70 l = (E_REFUSED, None).
Proof. intros. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma sx_spec_rfn : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> 0x7f < fn -> sysex_spec dev fn l = (E_RANGE, None).
Proof.
  intros. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.ltb_lt _ _) H1).
  reflexivity.
Qed.

Lemma sx_spec_space : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> 24 < Z.of_nat (length l) + 5 ->
  sysex_spec dev fn l = (E_SPACE, None).
Proof.
  intros. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.ltb_ge _ _) H1),
    (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.

Lemma sx_spec_rpl : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length l) + 5 <= 24 ->
  existsb hib l = true -> sysex_spec dev fn l = (E_RANGE, None).
Proof.
  intros. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.ltb_ge _ _) H1),
    (proj2 (Z.ltb_ge _ _) H2). unfold hib in H3. rewrite H3. reflexivity.
Qed.

Lemma sx_spec_ok : forall dev fn l, dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length l) + 5 <= 24 ->
  existsb hib l = false ->
  sysex_spec dev fn l = (0, Some ([0xf0; 0x13; dev; fn] ++ l ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)).
Proof.
  intros. unfold sysex_spec. rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.ltb_ge _ _) H1),
    (proj2 (Z.ltb_ge _ _) H2). unfold hib in H3. rewrite H3. reflexivity.
Qed.

(* ---- cells in pieces ---- *)

Lemma wr_at_app : forall m A (n1 n2 : Z), 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). split; [split; [lia|]; split; [lia|]; intros i Hi; apply H; lia|].
    split; [lia|]. split; [lia|]. intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hb & H) (Ha' & Hb' & H')]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec0 i n1); [apply H; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

Lemma rw_cells_app_split : forall m A c1 c2,
  rw_cells rsegs m A (c1 ++ c2) -> rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2.
Proof.
  intros m A c1 c2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app, Nat2Z.inj_add in Hw. apply wr_at_app in Hw; [|lia|lia]. destruct Hw as [R1 R2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; (split; [split|]); assumption.
Qed.

Lemma rw_cells_app_join : forall m A c1 c2,
  rw_cells rsegs m A c1 -> rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2 -> rw_cells rsegs m A (c1 ++ c2).
Proof.
  intros m A c1 c2 [[W1 B1] R1] [[W2 B2] R2].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. apply wr_at_app; [lia|lia|]. split; assumption.
Qed.

Lemma rw_cells_to_CB : forall m A cs n bs,
  rw_cells rsegs m A cs -> cells_size cs = n -> cells_bytes cs = bs -> rw_cells rsegs m A [CB n bs].
Proof.
  intros m A cs n bs H Hn Hb. subst n bs.
  pose proof (rw_cells_merge rsegs m A [] cs []) as M. rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

Lemma rw_cells_base : forall m A A' cs, A = A' -> rw_cells rsegs m A cs -> rw_cells rsegs m A' cs.
Proof. intros; subst; assumption. Qed.

(* The out area after the three header stores, cut for the memcpy at out + 4 (n payload bytes), the 0xf7
   store at out + 4 + n and the tail stores at out + 24. *)
Lemma rw_cells_eq : forall m A A' cs cs', rw_cells rsegs m A cs -> A = A' -> cs = cs' -> rw_cells rsegs m A' cs'.
Proof. intros; subst; assumption. Qed.

Lemma out_pieces : forall m A (c1 : list cell) (r : list byte) (n : nat),
  rw_cells rsegs m A (c1 ++ [CB 28 r]) -> cells_size c1 = 4%nat -> (n <= 19)%nat ->
  rw_cells rsegs m A c1 /\
  rw_cells rsegs m (A + 4) [CB n (firstn n r)] /\
  rw_cells rsegs m (A + 4 + Z.of_nat n) [CB 1 (firstn 1 (skipn n r)); CB (19 - n) (firstn (19 - n) (skipn (S n) r))] /\
  rw_cells rsegs m (A + 24) [CB 8 (skipn 20 r)].
Proof.
  intros m A c1 r n H Hs Hn.
  pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [Hr _]]. cbn in Hr.
  apply (rw_cells_split_CB rsegs m A c1 28 r [] [n; 1%nat; (19 - n)%nat; 8%nat]) in H; [|cbn; lia].
  rewrite app_nil_r in H. cbn [mk_CB_cells] in H.
  apply rw_cells_app_split in H. destruct H as [H1 H]. rewrite Hs in H.
  change [CB n (firstn n r); CB 1 (firstn 1 (skipn n r)); CB (19 - n) (firstn (19 - n) (skipn 1 (skipn n r)));
          CB 8 (firstn 8 (skipn (19 - n) (skipn 1 (skipn n r))))]
    with ([CB n (firstn n r)] ++ [CB 1 (firstn 1 (skipn n r)); CB (19 - n) (firstn (19 - n) (skipn 1 (skipn n r)))]
          ++ [CB 8 (firstn 8 (skipn (19 - n) (skipn 1 (skipn n r))))]) in H.
  apply rw_cells_app_split in H. destruct H as [H2 H].
  apply rw_cells_app_split in H. destruct H as [H3 H4].
  split; [exact H1|]. split; [eapply rw_cells_eq; [exact H2 | cbn; lia | reflexivity]|]. split.
  - eapply rw_cells_eq; [exact H3 | cbn [cells_size csize]; lia | ]. rewrite skipn_skipn. reflexivity.
  - eapply rw_cells_eq; [exact H4 | cbn [cells_size csize]; lia | ]. rewrite !skipn_skipn.
    match goal with |- context [skipn ?k r] => replace k with 20%nat by lia end.
    rewrite firstn_all2 by (rewrite length_skipn; lia). reflexivity.
Qed.

Lemma hdr_bytes : forall dev fn, 0 <= dev < 256 -> 0 <= fn < 256 ->
  le2 (Z_to_bv 64 5104) ++ [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 dev))] ++ [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 fn))]
  = bz [0xf0; 0x13; dev; fn].
Proof.
  intros dev fn Hd Hf. rewrite !unsigned_lit by lia.
  unfold le2, bz, b8. cbn [Z_to_le_bytes map app].
  apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|].
  apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|].
  reflexivity.
Qed.

Lemma disp_ok : forall fn, 0 <= fn < 256 ->
  Z.b2z (Z.land ((fn + -48) mod 18446744073709551616) 239 <? 1) = bit_or_0 ((fn =? 64) || (fn =? 48)) 1.
Proof.
  intros fn Hf.
  assert (C : forallb (fun f => Z.b2z (Z.land ((f + -48) mod 18446744073709551616) 239 <? 1)
                               =? bit_or_0 ((f =? 64) || (f =? 48)) 1) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  assert (Hin : In fn (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat fn). split; [lia|]. apply in_seq. lia. }
  apply Z.eqb_eq. exact (C fn Hin).
Qed.

Lemma disp_byte : forall fn, 0 <= fn < 256 ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.b2z (Z.land ((fn + -48) mod 18446744073709551616) 239 <? 1))))
  = b8 (bit_or_0 ((fn =? 64) || (fn =? 48)) 1).
Proof.
  intros fn Hf. rewrite (disp_ok fn Hf). unfold b8. f_equal. apply unsigned_lit.
  unfold bit_or_0. destruct ((fn =? 64) || (fn =? 48)); lia.
Qed.

Lemma sx_out_bytes : forall dev fn (pl before : list byte) (bf bl bd : byte) (pad : list byte),
  bf = b8 0xf7 -> bl = b8 (Z.of_nat (length pl) + 5) -> bd = b8 (bit_or_0 ((fn =? 64) || (fn =? 48)) 1) ->
  pad = firstn 2 (skipn 26 before) ->
  bz [0xf0; 0x13; dev; fn] ++ pl ++ bf :: skipn (length pl + 5) (firstn 24 before) ++ bl :: bd :: pad ++ le4 (Z_to_bv 64 0)
  = cmd_out before (Some ([0xf0; 0x13; dev; fn] ++ zb pl ++ [0xf7], 0, bit_or_0 ((fn =? 0x40) || (fn =? 0x30)) 1)).
Proof.
  intros dev fn pl before bf bl bd pad Ef El Ed Ep. subst bf bl bd pad.
  unfold cmd_out.
  assert (Hl : length ([0xf0; 0x13; dev; fn] ++ zb pl ++ [0xf7]) = (length pl + 5)%nat)
    by (rewrite !length_app, zb_length; cbn; lia).
  rewrite Hl. unfold bz. rewrite !map_app.
  change (map b8 (zb pl)) with (bz (zb pl)). rewrite bz_zb.
  rewrite Nat2Z.inj_add. change (Z.of_nat 5) with 5.
  cbn [map]. rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

(* The out area after the header stores of either path, in the four pieces the rest of the walk uses. *)
Lemma sx_split : forall m1 A (before : list byte) (b1 b2 : byte) (v : word) (n : nat),
  rw_cells rsegs m1 A [C2 v; C1 b1; C1 b2; CB 28 (skipn 1 (skipn 1 (skipn 2 before)))] -> (n <= 19)%nat ->
  rw_cells rsegs m1 A [C2 v; C1 b1; C1 b2] /\
  rw_cells rsegs m1 (A + 4) [CB n (firstn n (skipn 4 before))] /\
  rw_cells rsegs m1 (A + 4 + Z.of_nat n)
    [CB 1 (firstn 1 (skipn (n + 4) before)); CB (19 - n) (skipn (n + 5) (firstn 24 before))] /\
  rw_cells rsegs m1 (A + 24) [CB 8 (skipn 24 before)].
Proof.
  intros m1 A before b1 b2 v n H Hn.
  destruct (out_pieces m1 A [C2 v; C1 b1; C1 b2] (skipn 1 (skipn 1 (skipn 2 before))) n H eq_refl Hn)
    as (P1 & P2 & P3 & P4).
  assert (Er : skipn 1 (skipn 1 (skipn 2 before)) = skipn 4 before) by (rewrite !skipn_skipn; reflexivity).
  rewrite Er in P2, P3, P4.
  split; [exact P1|]. split; [exact P2|]. split.
  - eapply rw_cells_eq; [exact P3 | reflexivity | ].
    rewrite !skipn_skipn, skipn_firstn_comm.
    replace (24 - (n + 5))%nat with (19 - n)%nat by lia.
    replace (S n + 4)%nat with (n + 5)%nat by lia. reflexivity.
  - eapply rw_cells_eq; [exact P4 | reflexivity | ]. rewrite skipn_skipn. reflexivity.
Qed.

(* ---- the walk ---- *)

Section SX.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo dev fn : Z) (pl before : list byte) (pa ln out : word).

Definition Qx (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    let '(rc, o) := sysex_spec dev fn (zb pl) in
    a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned out) [CB 32 (cmd_out before o)].

Definition saved (j : list byte) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Hypothesis LO : lo + 48 <= bv_unsigned sp.
Hypothesis LO0 : 0 <= lo.
Hypothesis RDEV : 0 <= dev < 256.
Hypothesis RFN : 0 <= fn < 256.
Hypothesis HPA : bv_unsigned pa <> 0.
Hypothesis HOUT : bv_unsigned out <> 0.
Hypothesis DJ : bv_unsigned pa + Z.of_nat (length pl) <= bv_unsigned out \/ bv_unsigned out + 32 <= bv_unsigned pa.
Hypothesis SPA : bv_unsigned sp <= bv_unsigned pa.
Hypothesis SPO : bv_unsigned sp <= bv_unsigned out.
Hypothesis HLN : bv_unsigned ln = Z.of_nat (length pl).
Hypothesis PAB : bv_unsigned pa + Z.of_nat (length pl) <= 2 ^ 64.
Hypothesis OUTB : bv_unsigned out + 32 <= 2 ^ 64.
Hypothesis BLEN : length before = 32%nat.
Hypothesis MEMCPY : memcpy_contract.

Lemma sx_exit : forall (j : list byte) (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 t3' t4' t5' t6' : word)
                       (m1 : word -> option byte) (rc : Z) (o : option cmd),
  sysex_spec dev fn (zb pl) = (rc, o) ->
  a0' = Z_to_bv 64 rc ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 (cmd_out before o)] ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qx
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x153ec) fc None m1 (seg_rom rsegs)).
Proof.
  intros j ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 t3' t4' t5' t6' m1 rc o
    E HA0 FR ST OUT MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold saved in FR.
  do 6 zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
  all: try (rewrite E; split; assumption).
Qed.

Lemma sx_tail : forall (j x : list byte) (r : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m1 : word -> option byte),
  dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length pl) + 5 <= 24 -> existsb hib (zb pl) = false ->
  (r + length pl = 19)%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB (4 + length pl) (bz [0xf0; 0x13; dev; fn] ++ pl)] ->
  rw_cells rsegs m1 (bv_unsigned ln + bv_unsigned out + 4) [CB 1 x; CB r (skipn (length pl + 5) (firstn 24 before))] ->
  rw_cells rsegs m1 (bv_unsigned out + 24) [CB 8 (skipn 24 before)] ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qx
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn) a0' a1' a2' a3' a4' a5' a6' a7'
             ln (Z_to_bv 64 (bv_unsigned ln + 5)) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x153c4) fc None m1 (seg_rom rsegs)).
Proof.
  intros j x r ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1
    D7 F70 F7 SP24 EX Hr FR ST H1 H2 H3 MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 out) as Rout. unfold bv_modulus in Rout.
  unfold saved in FR.
  remember (bz [0xf0; 0x13; dev; fn] ++ pl) as hp eqn:Ehp.
  remember (skipn (length pl + 5) (firstn 24 before)) as mid eqn:Emid.
  remember (skipn 24 before) as tl eqn:Etl.
  (* mv a0, zero; add s2, s2, s0; addi a1, zero, -9; sb a1, 4(s2) *)
  do 4 zstep.
  (* addi a1, s1, -0x30; andi a1, a1, 0xef; seqz a1, a1; sb s3, 0x18(s0); sb a1, 0x19(s0); sw zero, 0x1c(s0) *)
  do 6 zstep.
  eapply (sx_exit j); [ apply sx_spec_ok; first [ assumption | rewrite zb_length; lia ]
                      | reflexivity | exact FR | exact ST | | exact MU | exact WM | exact HMI ].
  eapply rw_cells_to_CB.
  - eapply rw_cells_app_join; [ eapply rw_cells_app_join; [ exact H1 | ] | ].
    + eapply rw_cells_eq; [ exact H2 | cbn [cells_size csize]; lia | reflexivity ].
    + eapply rw_cells_eq; [ exact H3 | rewrite cells_size_app; cbn [cells_size csize]; lia | reflexivity ].
  - rewrite !cells_size_app. cbn [cells_size csize]. lia.
  - subst hp mid tl. rewrite !cells_bytes_app. cbn [cells_bytes cbytes].
    rewrite !app_nil_r, <- !app_assoc. cbn [app].
    apply sx_out_bytes; [ | | apply disp_byte; lia | rewrite !skipn_skipn; reflexivity ].
    + apply bv_eq. vm_compute. reflexivity.
    + rewrite unsigned_lit by lia. rewrite HLN. reflexivity.
Qed.

(* 0x15388, every payload byte below 0x80 and len >= 1: the header stores, memcpy(out + 4, payload, len),
   then the tail. *)
Lemma sx_copy : forall (j : list byte) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m1 : word -> option byte),
  dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length pl) + 5 <= 24 -> existsb hib (zb pl) = false ->
  1 <= Z.of_nat (length pl) ->
  bytes_at rsegs m1 (bv_unsigned pa) pl ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 before] ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qx
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn) (Z_to_bv 64 (-11))
             (Z_to_bv 64 dev) pa a3' a4' a5' a6' a7' ln (Z_to_bv 64 (bv_unsigned ln + 5))
             s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15388) fc None m1 (seg_rom rsegs)).
Proof.
  intros j t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 D7 F70 F7 SP24 EX L1 HD FR ST OUT MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 out) as Rout. unfold bv_modulus in Rout.
  unfold saved in FR.
  (* lui a0, 1; addi a0, a0, 0x3f0; sh a0, 0(s0); sb a1, 2(s0); sb s1, 3(s0) *)
  do 5 zstep.
  destruct (sx_split _ _ before _ _ _ (length pl) OUT ltac:(lia)) as (H1 & HC & H2 & H3). clear OUT.
  assert (Edst : bv_unsigned (Z_to_bv 64 (bv_unsigned out + 4)) = bv_unsigned out + 4) by (apply unsigned_lit; lia).
  apply (rw_cells_base _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned out + 4)))) in HC; [ | lia ].
  replace (length pl) with (Z.to_nat (bv_unsigned ln)) in HC by lia.
  (* addi a0, s0, 4; mv a1, a2; mv a2, s2; jal memcpy *)
  do 4 zstep.
  unfold memcpy_contract in MEMCPY.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply MEMCPY; [ exact HD | lia | exact HC | lia | exact HMI ] | post_call rsegs mm ]
  end.
  (* j 0x153c4 *)
  zstep.
  eapply (sx_tail j (firstn 1 (skipn (length pl + 4) before)) (19 - length pl));
    [ exact D7 | exact F70 | exact F7 | exact SP24 | exact EX | lia | exact FR | exact ST | | | exact H3
    | assumption | assumption | assumption ].
  - eapply rw_cells_to_CB.
    + eapply rw_cells_app_join; [ exact H1 | eapply rw_cells_eq; [ eassumption | cbn [cells_size csize]; lia | reflexivity ] ].
    + rewrite cells_size_app. cbn [cells_size csize]. lia.
    + rewrite cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
      rewrite (hdr_bytes dev fn RDEV RFN). reflexivity.
  - eapply rw_cells_eq; [ exact H2 | lia | reflexivity ].
Qed.

(* 0x153b0, len = 0: the header stores, then the tail. *)
Lemma sx_zero : forall (j : list byte) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m1 : word -> option byte),
  dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length pl) = 0 ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 before] ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qx
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn) (Z_to_bv 64 (-11))
             (Z_to_bv 64 dev) pa a3' a4' a5' a6' a7' ln (Z_to_bv 64 (bv_unsigned ln + 5))
             s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x153b0) fc None m1 (seg_rom rsegs)).
Proof.
  intros j t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 D7 F70 F7 L0 FR ST OUT MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 out) as Rout. unfold bv_modulus in Rout.
  assert (Epl : pl = []) by (apply length_zero_iff_nil; lia).
  unfold saved in FR.
  (* lui a0, 1; addi a0, a0, 0x3f0; sh a0, 0(s0); sb a1, 2(s0); sb s1, 3(s0) *)
  do 5 zstep.
  destruct (sx_split _ _ before _ _ _ (length pl) OUT ltac:(lia)) as (H1 & _ & H2 & H3). clear OUT.
  eapply (sx_tail j (firstn 1 (skipn (length pl + 4) before)) (19 - length pl));
    [ exact D7 | exact F70 | exact F7 | lia | rewrite Epl; reflexivity | lia | exact FR | exact ST | | | exact H3
    | assumption | assumption | assumption ].
  - eapply rw_cells_to_CB; [ exact H1 | cbn [cells_size csize]; lia | ].
    cbn [cells_bytes cbytes]. rewrite !app_nil_r. rewrite (hdr_bytes dev fn RDEV RFN), Epl, app_nil_r. reflexivity.
  - eapply rw_cells_eq; [ exact H2 | lia | reflexivity ].
Qed.

(* The payload loop at 0x15374: a3 = payload + i, a4 = len - i, the bytes before i below 0x80. *)
Definition loop_ok (fuel : nat) : Prop :=
  forall (j : list byte) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' cur rem : word) (i : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned rem) <= fuel)%nat ->
  dev <= 0x7f -> fn <> 0x70 -> fn <= 0x7f -> Z.of_nat (length pl) + 5 <= 24 ->
  bv_unsigned cur = bv_unsigned pa + i -> bv_unsigned rem = Z.of_nat (length pl) - i -> 0 <= i < Z.of_nat (length pl) ->
  existsb hib (firstn (Z.to_nat i) (zb pl)) = false ->
  bytes_at rsegs m1 (bv_unsigned pa) pl ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) (saved j) ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned out) [CB 32 before] ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m1 ->
  wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qx
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' out (Z_to_bv 64 fn) (Z_to_bv 64 (-11))
             (Z_to_bv 64 dev) pa cur rem a5' a6' a7' ln (Z_to_bv 64 (bv_unsigned ln + 5))
             s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15374) fc None m1 (seg_rom rsegs)).

Lemma sx_loop : forall fuel, loop_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold loop_ok;
    intros j t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' cur rem i m1 HF D7 F70 F7 SP24 HC HR HI EXP HD FR ST OUT MU WM HMI.
  { exfalso. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur. unfold bv_modulus in Rcur.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem. unfold bv_modulus in Rrem.
  assert (HB : ov_read_bytes rsegs m1 cur 1 = Some [nth (Z.to_nat i) pl (Z_to_bv 8 0)]).
  { rewrite <- (Z_to_bv_bv_unsigned cur). rewrite HC. apply sx_byte; [exact HD | lia]. }
  (* lb a5, 0(a3); bltz a5 *)
  zstep. zstep.
  if_cases K.
  - zify_cond K.
    assert (T : hib (nth (Z.to_nat i) (zb pl) 0) = true).
    { rewrite zb_nth. unfold hib.
      destruct (Z.testbit (bv_unsigned (nth (Z.to_nat i) pl (Z_to_bv 8 0))) 7) eqn:E; [reflexivity|].
      apply sx_sxb in E. lia. }
    eapply (sx_exit j) with (rc := E_RANGE) (o := None);
      [ apply sx_spec_rpl; [ lia | lia | lia | rewrite zb_length; lia | eapply ex_hit; [ exact T | rewrite zb_length; lia ] ]
      | reflexivity | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ].
  - zify_cond K.
    assert (T : hib (nth (Z.to_nat i) (zb pl) 0) = false) by (rewrite zb_nth; apply sx_sxb; exact K).
    assert (EXP' : existsb hib (firstn (S (Z.to_nat i)) (zb pl)) = false)
      by (apply ex_prefix_step; [ exact EXP | exact T | rewrite zb_length; lia ]).
    (* addi a4, a4, -1; addi a3, a3, 1; bnez a4 *)
    zstep. zstep. zstep.
    if_cases K2.
    + zify_cond K2.
      eapply (IH j) with (i := i + 1).
      all: first [ assumption | (rewrite unsigned_lit by lia; lia) | lia | idtac ].
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact EXP'.
    + zify_cond K2.
      assert (Hi : S (Z.to_nat i) = length (zb pl)) by (rewrite zb_length; lia).
      rewrite Hi, firstn_all in EXP'.
      eapply (sx_copy j); [ exact D7 | exact F70 | exact F7 | exact SP24 | exact EXP' | lia | exact HD | exact FR
                          | exact ST | exact OUT | exact MU | exact WM | exact HMI ].
Qed.

Lemma sx_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m (bv_unsigned pa) pl ->
  rw_cells rsegs m (bv_unsigned out) [CB 32 before] ->
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs Qx
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dev) (Z_to_bv 64 fn) pa ln out a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152f0) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 HD OUT HMI ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 out) as Rout. unfold bv_modulus in Rout.
  pose proof (bv_unsigned_in_range 64 pa) as Rpa. unfold bv_modulus in Rpa.
  carve_frame 48%nat ST.
  assert (MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned out, bv_unsigned out + 32)] m m)
    by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  (* prologue; mv s1, a1; mv a1, a0; addi a0, zero, -1; beqz a4 *)
  do 6 zstep. do 3 zstep. zstep.
  if_cases K1.
  { zify_cond K1. exfalso. lia. }
  zify_cond K1.
  (* mv s2, a3; slli a3, a1, 0x38; bltz a3 *)
  zstep. zstep. zstep.
  if_cases K2.
  { zify_cond K2.
    assert (D : 0x7f < dev).
    { destruct (Z.ltb_spec0 dev 128) as [L|L]; [ | lia ]. apply (proj2 (sx_shl56 dev RDEV)) in L. lia. }
    eapply sx_exit with (rc := E_ARG) (o := None);
      [ apply sx_spec_arg; exact D | reflexivity | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ]. }
  zify_cond K2.
  assert (D7 : dev <= 0x7f) by (apply (proj1 (sx_shl56 dev RDEV)) in K2; lia).
  (* mv s0, a4; snez a3, s2; seqz a4, a2; and a3, a4, a3; bnez a3 *)
  do 5 zstep.
  if_cases K3.
  { zify_cond K3.
    exfalso. rewrite (proj2 (Z.ltb_ge (bv_unsigned pa) 1)) in K3 by lia. cbn [Z.b2z] in K3.
    rewrite Z.land_0_l in K3. rewrite ?Zmod_0_l in K3. lia. }
  (* addi a0, zero, 0x70; bne s1, a0 *)
  zstep. zstep.
  if_cases K4.
  - zify_cond K4.
    (* slli a3, s1, 0x38; addi a0, zero, -0xb; bltz a3 *)
    zstep. zstep. zstep.
    if_cases K5.
    { zify_cond K5.
      assert (Fb : 0x7f < fn).
      { destruct (Z.ltb_spec0 fn 128) as [L|L]; [ | lia ]. apply (proj2 (sx_shl56 fn RFN)) in L. lia. }
      eapply sx_exit with (rc := E_RANGE) (o := None);
        [ apply sx_spec_rfn; lia | reflexivity | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ]. }
    zify_cond K5.
    assert (F7 : fn <= 0x7f) by (apply (proj1 (sx_shl56 fn RFN)) in K5; lia).
    (* addi s3, s2, 5; addi a3, zero, 0x18; bgeu a3, s3 *)
    zstep. zstep. zstep.
    if_cases K6.
    + zify_cond K6.
      rewrite ?Z.mod_small in K6 by lia.
      (* beqz s2 *)
      zstep.
      if_cases K7.
      * zify_cond K7.
        eapply sx_zero; [ exact D7 | lia | exact F7 | lia | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ].
      * zify_cond K7.
        (* mv a3, a2; mv a4, s2 *)
        zstep. zstep.
        eapply (sx_loop 19) with (i := 0); [ lia | exact D7 | lia | exact F7 | lia | lia | lia | lia | reflexivity
          | exact HD | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ].
    + zify_cond K6. rewrite ?Z.mod_small in K6 by lia.
      (* addi a0, zero, -5; j *)
      zstep. zstep.
      eapply sx_exit with (rc := E_SPACE) (o := None);
        [ apply sx_spec_space; first [ lia | rewrite zb_length; lia ] | reflexivity | exact FR | exact ST | exact OUT
        | exact MU | exact WM | exact HMI ].
  - zify_cond K4.
    (* addi a0, zero, -0xa; j *)
    zstep. zstep.
    assert (E : sysex_spec dev fn (zb pl) = (E_REFUSED, None)).
    { replace fn with 0x70 by lia. apply sx_spec_refused. exact D7. }
    eapply sx_exit; [ exact E | reflexivity | exact FR | exact ST | exact OUT | exact MU | exact WM | exact HMI ].
Qed.

End SX.

Theorem diginet_sysex_encode_holds : memcpy_contract -> diginet_sysex_encode_contract.
Proof.
  intros MEMCPY. unfold diginet_sysex_encode_contract, DIGINET_SYSEX_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo dev fn pl before PRE.
  unfold diginet_sysex_encode_pre, DIGINET_SYSEX_ENCODE_DEPTH in *.
  destruct PRE as (HDEV & HFN & HA2 & HPL & HLEN & HA4 & OUT & DJ & SPA2 & SPA4 & HMI & ST & LO).
  destruct HDEV as [RDEV ->]. destruct HFN as [RFN ->].
  change (2 ^ 8) with 256 in RDEV, RFN.
  unfold disj in DJ.
  pose proof (bytes_at_bound rsegs m _ _ HPL) as PAB.
  pose proof (rw_cells_bound rsegs m _ _ OUT) as OB. cbn [cells_size csize] in OB.
  pose proof OUT as [[[BL _] _] _]. cbn in BL.
  pose proof ST as [LO0 _].
  change (evt rsegs (Qx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo dev fn pl before a4)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dev) (Z_to_bv 64 fn) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152f0) fc None m (seg_rom rsegs))).
  eapply sx_entry.
  all: first [ assumption | lia ].
Qed.
