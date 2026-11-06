(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 546 of its 563 lines of code are new or changed and 43 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  codec_contract_sat LLVMFuzzerTestOneInput_c memset_c memcpy_c diginet_personality_of_c
  check_personality_c check_refusal_c check_range_c check_bytes_c check_text_masks_c
  check_text_scribble_c check_text_seg7_c check_text_counter_c owed_counter_text_c text_arg_c
  owe_sysex_c diginet_fader_encode_c diginet_button_encode_c diginet_touch_encode_c
  diginet_vpot_encode_c diginet_jog_encode_c diginet_ring_encode_c diginet_meter_encode_c
  diginet_strip_leds_encode_c diginet_counter_leds_encode_c diginet_scribble_encode_c
  diginet_counter_encode_c diginet_sysex_encode_c.
Import ListNotations.
Open Scope Z_scope.

(** The function runs a loop of at most 256 operations over the input cursor. Every segment of the
    walk is stated here as a predicate on one cut state, so that a segment file proves exactly one
    implication between two of them and the composition in LLVMFuzzerTestOneInput.v chains them.
    All of the cut states share the frame, the entry registers and the entry memory, bundled in
    [cenv]; a segment proof begins by destructing it, which turns every field into a plain variable:
      intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ...; cenv_cbn.
    The frame addresses are written [bv_unsigned sp + <literal>]; after the prologue the stack
    register holds [Z_to_bv 64 (bv_unsigned sp + -416)], so a segment rewrites with [u_frame] once
    and the address normaliser of Lib/Step then matches the cell bases. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- helpers every segment uses ---- *)

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_error_nil_any : forall (A : Type) (k : nat), nth_error (@nil A) k = None.
Proof. intros A [|k]; reflexivity. Qed.

Lemma nth_error_skipn_nat : forall (A : Type) (l : list A) (n i : nat),
  nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l. induction l as [|x l IH]; intros n i.
  - rewrite skipn_nil, !nth_error_nil_any. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [skipn Nat.add]. apply IH.
Qed.

(** The tail of a byte list from offset [k] is in memory at [a + k]. *)
Lemma bytes_at_skipn : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (skipn (Z.to_nat k) bs).
Proof.
  intros m a bs k (Ha & Hl & H) Hk.
  split; [lia|]. rewrite length_skipn. split; [lia|]. intros i Hi.
  rewrite nth_error_skipn_nat.
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

Lemma rw_cells_bytes_at : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof.
  intros m A n bs [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma kcall_cells_size : forall k, cells_size (kcall_cells k) = 184%nat.
Proof. intros k. reflexivity. Qed.

(** [k.out] is the 32-byte cell at offset 108 of the record: the split every encoder call needs. *)
Lemma kcall_cells_split_out : forall k,
  kcall_cells k =
    [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
     CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)]
    ++ [CB 32 (k_out k)]
    ++ [C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
        C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].
Proof. intros k. reflexivity. Qed.

Lemma kcall_pre_size : forall k,
  cells_size [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
     C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
     CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)] = 108%nat.
Proof. intros k. reflexivity. Qed.

Lemma lor_lt_pow : forall x y n, 0 < n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
  intros x y n Hn Hx Hy. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)); lia|].
  assert (Hpos : 0 < Z.lor x y) by (pose proof (Z.lor_nonneg x y); lia).
  pose proof (Z.log2_spec (Z.lor x y) Hpos) as [_ Hup].
  rewrite Z.log2_lor in Hup by lia.
  assert (Lx : Z.log2 x < n).
  { destruct (Z.eq_dec x 0) as [Ex|Ex]; [subst x; rewrite Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
  assert (Ly : Z.log2 y < n).
  { destruct (Z.eq_dec y 0) as [Ey|Ey]; [subst y; rewrite Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
  assert (2 ^ Z.succ (Z.max (Z.log2 x) (Z.log2 y)) <= 2 ^ n) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

(** The stack register after the prologue. *)
Lemma u_frame : forall x : Z, 416 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 (x + -416)) = x + -416.
Proof. intros x Hx. apply unsigned_lit. lia. Qed.

Ltac refute_trap T := exfalso; zify_cond T; repeat (rewrite Z.mod_small in T by lia); lia.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(** ---- the frame, the entry state and the post ---- *)

(** The entry registers the walk must restore, the entry memory, the stack floor, the input
    pointer and the input bytes. *)
Record cenv := mkCenv {
  c_ra : word; c_sp : word; c_gp : word; c_tp : word;
  c_s0 : word; c_s1 : word; c_s2 : word; c_s3 : word; c_s4 : word; c_s5 : word;
  c_s6 : word; c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_p : word; c_F : bvmap 5 word; c_fc : bv 32; c_m : word -> option byte;
  c_lo : Z; c_data : list byte }.

Ltac cenv_cbn := cbn [c_ra c_sp c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10
                      c_s11 c_p c_F c_fc c_m c_lo c_data] in *.

(** The 13 callee-saved words the prologue writes at sp - 104 .. sp - 1 (s11 lowest, ra highest). *)
Definition saved (E : cenv) : list cell :=
  [C8 (c_s11 E); C8 (c_s10 E); C8 (c_s9 E); C8 (c_s8 E); C8 (c_s7 E); C8 (c_s6 E); C8 (c_s5 E);
   C8 (c_s4 E); C8 (c_s3 E); C8 (c_s2 E); C8 (c_s1 E); C8 (c_s0 E); C8 (c_ra E)].

(** The post of codec_main_contract. *)
Definition Qk (E : cenv) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (c_ra E) (c_sp E) (c_gp E) (c_tp E) t0' t1' t2' (c_s0 E) (c_s1 E) (Z_to_bv 64 0)
                  a1' a2' a3' a4' a5' a6' a7' (c_s2 E) (c_s3 E) (c_s4 E) (c_s5 E) (c_s6 E) (c_s7 E)
                  (c_s8 E) (c_s9 E) (c_s10 E) (c_s11 E) t3' t4' t5' t6')
             (c_F E) (ret_pc (c_ra E)) (c_fc E) None m' (seg_rom rsegs) /\
    munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m' /\
    wmono rsegs (c_m E) m' /\
    mem_inv rsegs m' /\
    stk rsegs m' (c_lo E) (bv_unsigned (c_sp E)).

(** The premises of codec_main_contract, with the RELRO-disjointness one of the stack window. *)
Definition env_ok (E : cenv) : Prop :=
  bytes_at rsegs (c_m E) (bv_unsigned (c_p E)) (c_data E) /\
  mem_inv rsegs (c_m E) /\
  stk rsegs (c_m E) (c_lo E) (bv_unsigned (c_sp E)) /\
  c_lo E + 640 <= bv_unsigned (c_sp E) /\
  bv_unsigned (c_sp E) mod 16 = 0 /\
  (bv_unsigned (c_p E) + Z.of_nat (length (c_data E)) <= c_lo E \/ bv_unsigned (c_sp E) <= bv_unsigned (c_p E)) /\
  bv_unsigned (c_p E) + Z.of_nat (length (c_data E)) < 2 ^ 63 /\
  (0 < Z.of_nat (length (c_data E)) -> 0 < bv_unsigned (c_p E)) /\
  relro_img (c_m E) /\
  disj (c_lo E) (bv_unsigned (c_sp E) - c_lo E) RELRO_BASE RELRO_LEN.

(** The frame after the prologue, low to high: 8 unused bytes, the three spilled constants
    (fuzz_codec.c owe3 of TOUCH and JOG and the SPEC_KEY mask), the 184-byte call record, the
    16-byte input cursor, 5 bytes of padding, text[65], the 10 bytes that hold COUNTER_TEXT's dots
    and owe()'s pl[], and the saved registers. *)
Definition fr (E : cenv) (m1 : word -> option byte) (kc : list cell) (cur nl : word)
              (u0 pj tj plj : list byte) : Prop :=
  cells_size kc = 184%nat /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) kc /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 cur; C8 nl] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] /\
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E).

(** Every write of the walk is inside the stack window, which the contract's new premise keeps off
    the RELRO tables: so the tables still read as the image, and the input bytes are unchanged. *)
Lemma relro_at : forall E m1, env_ok E ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 -> relro_img m1.
Proof.
  intros E m1 (_ & _ & ST & LO & _ & _ & _ & _ & RI & DJR) MU i Hi.
  pose proof ST as (Hlo0 & Hhi0 & _).
  unfold mrd. rewrite MU.
  - exact (RI i Hi).
  - cbn [outside]. split; [|exact I].
    rewrite wa_unsigned by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    unfold disj, RELRO_BASE, RELRO_LEN in *. lia.
Qed.

Lemma data_at : forall E m1, env_ok E ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  bytes_at rsegs m1 (bv_unsigned (c_p E)) (c_data E).
Proof.
  intros E m1 (BY & _ & ST & LO & _ & DJ & HPB & _ & _ & _) MU.
  pose proof ST as (Hlo0 & Hhi0 & _).
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** The whole frame as one block above the saved registers: what the epilogue releases. The two
    early returns reach it without [fr], with the block still the caller's bytes. *)
Lemma fr_exit : forall E m1 kc cur nl u0 pj tj plj,
  fr E m1 kc cur nl u0 pj tj plj ->
  exists cs, cells_size cs = 312%nat /\
    rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) (cs ++ saved E).
Proof.
  intros E m1 kc cur nl u0 pj tj plj (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  assert (J7 : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) ([CB 10 plj] ++ saved E)).
  { apply rw_cells_app_join; [exact FPL|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -114 + Z.of_nat 10) with (bv_unsigned (c_sp E) + -104) by lia.
    exact FSV. }
  assert (J6 : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179)
                 ([CB 65 tj] ++ [CB 10 plj] ++ saved E)).
  { apply rw_cells_app_join; [exact FTX|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -179 + Z.of_nat 65) with (bv_unsigned (c_sp E) + -114) by lia.
    exact J7. }
  assert (J5 : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184)
                 ([CB 5 pj] ++ [CB 65 tj] ++ [CB 10 plj] ++ saved E)).
  { apply rw_cells_app_join; [exact FPD|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -184 + Z.of_nat 5) with (bv_unsigned (c_sp E) + -179) by lia.
    exact J6. }
  assert (J4 : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200)
                 ([C8 cur; C8 nl] ++ [CB 5 pj] ++ [CB 65 tj] ++ [CB 10 plj] ++ saved E)).
  { apply rw_cells_app_join; [exact FIN|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -200 + Z.of_nat 16) with (bv_unsigned (c_sp E) + -184) by lia.
    exact J5. }
  assert (J3 : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384)
                 (kc ++ [C8 cur; C8 nl] ++ [CB 5 pj] ++ [CB 65 tj] ++ [CB 10 plj] ++ saved E)).
  { apply rw_cells_app_join; [exact FK|]. rewrite HS.
    replace (bv_unsigned (c_sp E) + -384 + Z.of_nat 184) with (bv_unsigned (c_sp E) + -200) by lia.
    exact J4. }
  assert (J2 : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
                 ([C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ++ kc
                  ++ [C8 cur; C8 nl] ++ [CB 5 pj] ++ [CB 65 tj] ++ [CB 10 plj] ++ saved E)).
  { apply rw_cells_app_join; [exact F8|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -408 + Z.of_nat 24) with (bv_unsigned (c_sp E) + -384) by lia.
    exact J3. }
  exists ([CB 8 u0] ++ [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ++ kc
          ++ [C8 cur; C8 nl] ++ [CB 5 pj] ++ [CB 65 tj] ++ [CB 10 plj]).
  split.
  { rewrite !cells_size_app. cbn [cells_size csize Nat.add]. rewrite HS. reflexivity. }
  rewrite <- !app_assoc.
  apply rw_cells_app_join; [exact F0|]. cbn [cells_size csize Nat.add].
  replace (bv_unsigned (c_sp E) + -416 + Z.of_nat 8) with (bv_unsigned (c_sp E) + -408) by lia.
  exact J2.
Qed.

(** ---- the call record at the cut states ---- *)

(** &SPEC_C24 and &SPEC_PC in .data.rel.ro: the two values of SPEC_DESK[1..2], what k.desk holds. *)
Definition SDESK_C24 : Z := 0x1f690.
Definition SDESK_PC : Z := 0x1f6a0.

(** SPEC_DESK[i] (0x1f678), the desk the head stores in k.desk. *)
Definition sdesk (i : Z) : Z := if i =? 1 then SDESK_C24 else if i =? 2 then SDESK_PC else 0.

(** k.p and k.desk always come from one index of DESK / SPEC_DESK. *)
Definition desk_at (k : kcall) : Prop :=
  (k_p k = 0 /\ k_desk k = 0) \/
  (k_p k = PERS /\ k_desk k = SDESK_C24) \/
  (k_p k = PERS + 24 /\ k_desk k = SDESK_PC).

(** The desk of the record as the model sees it. *)
Definition od_of (k : kcall) : option desk :=
  if k_desk k =? SDESK_C24 then Some c24 else if k_desk k =? SDESK_PC then Some pc else None.

Definition enc_k (k : kcall) : Z * option cmd :=
  enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k).
Definition owe_k (k : kcall) : Z * cmd :=
  owe_spec (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k).

Definition with_out (k : kcall) (o : option cmd) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) (cmd_out (k_before k) o)
          (k_want_rc k) (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

Definition with_rc (k : kcall) (rc : Z) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) rc (k_before k) (k_out k)
          (k_want_rc k) (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

Definition with_want_rc (k : kcall) (wrc : Z) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) (k_out k)
          wrc (k_want k) (k_want_len k) (k_want_key k) (k_want_display k).

Definition with_want_key (k : kcall) (wk : Z) : kcall :=
  mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
          (k_bytes k) (k_n k) (k_rc k) (k_before k) (k_out k)
          (k_want_rc k) (k_want k) (k_want_len k) wk (k_want_display k).

(** The record after run() stored k.rc: what owe() starts from. *)
Definition k_run (k : kcall) : kcall := with_rc (with_out k (snd (enc_k k))) (fst (enc_k k)).

(** The record the head leaves: k zeroed, kind, p and desk of index i, before and out 0xa5. *)
Definition k_head (kind i : Z) : kcall :=
  mkKcall kind (repeat (b8 0) 4) (pers_of i) (sdesk i) 0 0 0 0 (repeat (b8 0) 24) 0 0
          (repeat (b8 0xa5) 32) (repeat (b8 0xa5) 32) 0 (repeat (b8 0) 24) 0 0 0.

(** What a reader leaves for run(): a kind run() dispatches, a desk of the image, the fields in the
    range the readers can produce, out still the 0xa5 of the head's memset, and owe()'s fields 0. *)
Definition rec_wf (k : kcall) : Prop :=
  0 <= k_kind k <= 11 /\
  desk_at k /\
  k_before k = repeat (b8 0xa5) 32 /\
  k_out k = repeat (b8 0xa5) 32 /\
  k_rc k = 0 /\ k_want_rc k = 0 /\ k_want_len k = 0 /\ k_want_key k = 0 /\ k_want_display k = 0 /\
  reader_ok (k_kind k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k).

(** What the three checks are called with: the library's code and command in k.rc / k.out, and
    owe()'s in k.want_*. *)
Definition chk_wf (k : kcall) : Prop :=
  0 <= k_kind k <= 11 /\
  desk_at k /\
  kcall_wf k /\
  k_before k = repeat (b8 0xa5) 32 /\
  reader_ok (k_kind k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k) /\
  k_rc k = fst (enc_k k) /\
  k_out k = cmd_out (k_before k) (snd (enc_k k)) /\
  k_want_rc k = fst (owe_k k) /\
  (fst (owe_k k) = 0 ->
     let '(w, wk, wd) := snd (owe_k k) in
     firstn (length w) (k_want k) = bz w /\
     k_want_len k = Z.of_nat (length w) /\
     Z.of_nat (length w) <= 24 /\
     k_want_key k = wk /\
     k_want_display k = wd).

(** ---- the cut states ---- *)

(** The reader each kind of the switch at fuzz_codec.c:578 enters (T1 at 0x10444; kind 14 is the
    switch's default). *)
Definition pc_rd (kind : Z) : Z :=
  nth (Z.to_nat kind) [0x13448; 0x13714; 0x137b4; 0x13588; 0x138f4; 0x139fc; 0x13854; 0x13448;
                       0x13ac8; 0x13674; 0x13a9c; 0x134e8; 0x13628; 0x13994; 0x13b68] 0.

(** The encoder call of run() (T2 at 0x1047c; kind 11 is the switch's default). *)
Definition pc_run (kind : Z) : Z :=
  nth (Z.to_nat kind) [0x143b4; 0x14454; 0x1440c; 0x14424; 0x143fc; 0x1446c; 0x14484; 0x1443c;
                       0x144a0; 0x143cc; 0x143e4; 0x144b4] 0.

(** The case of owe() (T3 at 0x104a8; kind 11 is the switch's default). *)
Definition pc_owe (kind : Z) : Z :=
  nth (Z.to_nat kind) [0x14528; 0x14738; 0x14688; 0x146d0; 0x145b4; 0x14790; 0x14890; 0x14718;
                       0x14a0c; 0x145d0; 0x14928; 0x145a0] 0.

(** owe()'s needs_desk (fuzz_codec.c:126), the 0x812 bit test of 0x144e4. *)
Definition needs_desk (kind : Z) : bool := negb ((kind =? 1) || (kind =? 4) || (kind =? 11)).

(** 0x14b78: a0 := 0, the registers restored, the frame released. Only the saved registers are
    fixed: the early return of fuzz_codec.c:564 (0x132fc) arrives before anything else of the frame
    is stored, and the one of :568 (0x13310) before the spilled constants are (0x13348-0x1335c), so
    the rest of the frame holds anything. *)
Definition exit_ok (E : cenv) : Prop :=
  forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9'
          s10' s11' t3' t4' t5' t6' : word)
         (cs : list cell) (m1 : word -> option byte),
  cells_size cs = 312%nat ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) (cs ++ saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2' s0' s1'
             a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 0x14b78) (c_fc E) None m1 (seg_rom rsegs)).

(** 0x13368, the loop head of fuzz_codec.c:568: s5 = in.n (at least one byte left), s6 = ops, the
    nine constant registers of the setup, the cursor in memory, and the record and the text slots
    arbitrary (each is rewritten before it is read). The measure is 256 - ops. *)
Definition loop_ok (E : cenv) (n : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word)
         (cur nl rem : word) (kc : list cell) (u0 pj tj plj : list byte) (c ops : Z)
         (m1 : word -> option byte),
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  1 <= bv_unsigned rem ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 0 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 kc cur nl u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             rem (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 0x13368) (c_fc E) None m1 (seg_rom rsegs)).

(** T1[kind]: the head consumed the op byte, so the cursor is one on (c >= 1: the input is not
    empty, which is what makes the cursor non-NULL even when no byte is left) and in.n is in memory;
    s5 is k.p and the record is the head's. *)
Definition rd_ok (E : cenv) (n : nat) (kind i : Z) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word)
         (cur rem : word) (u0 pj tj plj : list byte) (c ops : Z) (m1 : word -> option byte),
  0 <= i <= 2 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 1 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells (k_head kind i)) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             (Z_to_bv 64 (pers_of i)) (Z_to_bv 64 ops) s7'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 (pc_rd kind)) (c_fc E) None m1 (seg_rom rsegs)).

(** The record is complete and run() is about to call its encoder: at 0x14390 (the switch) or at
    the arm T2[kind] a text reader jumps to directly. *)
Definition rec_ok (E : cenv) (n : nat) (k : kcall) (pcv : Z) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (cur rem : word) (u0 pj tj plj : list byte) (c ops : Z) (m1 : word -> option byte),
  rec_wf k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 0 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells k) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 pcv) (c_fc E) None m1 (seg_rom rsegs)).

(** 0x144cc: every encoder returns here with its code in a0 and out written. *)
Definition join_ok (E : cenv) (n : nat) (k : kcall) : Prop :=
  forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (cur rem : word) (u0 pj tj plj : list byte) (c ops : Z) (m1 : word -> option byte),
  rec_wf k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 0 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells (with_out k (snd (enc_k k)))) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             (Z_to_bv 64 (fst (enc_k k))) a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 0x144cc) (c_fc E) None m1 (seg_rom rsegs)).

(** T3[kind]: owe()'s prologue stored k.rc, zeroed want_rc, want_len, want_key and want_display,
    put k.desk in s7 and the pl[] base in a7, and (when the kind needs a desk) proved it non-NULL
    with a0 = 1. a1 held the kind; for kinds 0-10 the switch overwrote it with the jump target
    (0x1450c-0x14524), kind 11 keeps it, so it is free here and no case reads it before writing. *)
Definition owe_ok (E : cenv) (n : nat) (k : kcall) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' : word)
         (cur rem : word) (u0 pj tj plj : list byte) (c ops : Z) (m1 : word -> option byte),
  rec_wf k ->
  (needs_desk (k_kind k) = true -> a0' = Z_to_bv 64 1 /\ k_desk k <> 0) ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 0 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells (k_run k)) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             a0' a1' a2' a3' a4' a5' a6'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -114))
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             s5' (Z_to_bv 64 ops) (Z_to_bv 64 (k_desk k))
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 (pc_owe (k_kind k))) (c_fc E) None m1 (seg_rom rsegs)).

(** 0x14a34: the record is complete, the three checks run and must not abort. *)
Definition chk_ok (E : cenv) (n : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (k : kcall) (cur rem : word) (u0 pj tj plj : list byte) (c ops : Z)
         (m1 : word -> option byte),
  chk_wf k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 0 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 (kcall_cells k) cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 0x14a34) (c_fc E) None m1 (seg_rom rsegs)).

(** 0x14a54 (and 0x14b1c, the MASKS copy): the operation is over, in.n is in memory, s6 is the
    count before the increment. The record holds anything. *)
Definition latch_ok (E : cenv) (n : nat) (pcv : Z) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
         (cur rem : word) (kc : list cell) (u0 pj tj plj : list byte) (c ops : Z)
         (m1 : word -> option byte),
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned cur = bv_unsigned (c_p E) + c -> 0 <= c ->
  c + bv_unsigned rem = Z.of_nat (length (c_data E)) ->
  fr E m1 kc cur rem u0 pj tj plj ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned (c_sp E) + -416)) (c_gp E) (c_tp E) t0' t1' t2'
             (Z_to_bv 64 (bv_unsigned (c_sp E) + -308)) (Z_to_bv 64 0x1f678)
             a0' a1' a2' a3' a4' a5' a6' a7'
             (Z_to_bv 64 0x104d4) (Z_to_bv 64 254) (Z_to_bv 64 18446744073709422983)
             s5' (Z_to_bv 64 ops) s7' (Z_to_bv 64 (bv_unsigned (c_sp E) + -216)) (Z_to_bv 64 1)
             (Z_to_bv 64 18446744073709484843) (Z_to_bv 64 10) t3' t4' t5' t6')
        (c_F E) (Z_to_bv 64 pcv) (c_fc E) None m1 (seg_rom rsegs)).

(** 0x132b8, the entry the contract gives. *)
Definition entry_ok (E : cenv) : Prop :=
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bv_unsigned a1 = Z.of_nat (length (c_data E)) ->
  evt rsegs (Qk E)
    (MS (mkR (c_ra E) (c_sp E) (c_gp E) (c_tp E) t0 t1 t2 (c_s0 E) (c_s1 E) (c_p E) a1 a2 a3 a4 a5
             a6 a7 (c_s2 E) (c_s3 E) (c_s4 E) (c_s5 E) (c_s6 E) (c_s7 E) (c_s8 E) (c_s9 E)
             (c_s10 E) (c_s11 E) t3 t4 t5 t6)
        (c_F E) (Z_to_bv 64 0x132b8) (c_fc E) None (c_m E) (seg_rom rsegs)).

(** ---- the segment obligations ---- *)

(** 0x14b78-0x14bb4, 16 instructions. *)
Definition seg_exit_stmt : Prop := forall E, env_ok E -> exit_ok E.

(** 0x14a54-0x14a64 and 0x14b1c-0x14b20, 7 instructions: the only place the measure falls. *)
Definition seg_latch_stmt : Prop :=
  forall E n, env_ok E -> exit_ok E -> loop_ok E n ->
    latch_ok E (S n) 0x14a54 /\ latch_ok E (S n) 0x14b1c.

(** 0x132b8-0x13364, 44 instructions, one call. *)
Definition seg_entry_stmt : Prop :=
  forall E, env_ok E -> check_personality_contract -> exit_ok E -> loop_ok E 256 -> entry_ok E.

(** 0x13368-0x13444, 56 instructions: op = fuzz_u8, the two memsets, op % 15 and op / 15 % 3, the
    personality, and the reader switch. *)
Definition seg_head_stmt : Prop :=
  forall E n, env_ok E -> memset_contract -> diginet_personality_of_contract ->
    (forall kind i, 0 <= kind <= 14 -> 0 <= i <= 2 -> rd_ok E n kind i) ->
    loop_ok E n.

(** Each reader: it fills the record and reaches run(), except COUNTER_TEXT's refusal and MASKS,
    which reach the latch. [rd_run] is what a reader has to produce for a record it built. *)
Definition rd_run (E : cenv) (n : nat) : Prop :=
  forall k, rec_wf k -> rec_ok E n k 0x14390.
Definition rd_run_arm (E : cenv) (n : nat) : Prop :=
  forall k, rec_wf k -> rec_ok E n k (pc_run (k_kind k)).

Definition seg_rd0_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 0 i /\ rd_ok E n 7 i.
Definition seg_rd1_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 1 i /\ rd_ok E n 2 i.
Definition seg_rd3_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 3 i /\ rd_ok E n 4 i.
Definition seg_rd5_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 5 i.
Definition seg_rd6_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 6 i.
Definition seg_rd8_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 8 i.
Definition seg_rd9_stmt : Prop :=
  forall E n, env_ok E -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 9 i /\ rd_ok E n 10 i.
Definition seg_rd11_stmt : Prop :=
  forall E n, env_ok E -> memcpy_contract -> rd_run E n -> forall i, 0 <= i <= 2 -> rd_ok E n 11 i.
Definition seg_rd12_stmt : Prop :=
  forall E n, env_ok E -> diginet_personality_of_contract -> text_arg_contract ->
    check_text_scribble_contract -> rd_run_arm E n -> forall i, 0 <= i <= 2 -> rd_ok E n 12 i.
Definition seg_rd13_stmt : Prop :=
  forall E n, env_ok E -> diginet_personality_of_contract -> text_arg_contract ->
    check_text_seg7_contract -> check_text_counter_contract -> owed_counter_text_contract ->
    rd_run_arm E n -> latch_ok E n 0x14a54 -> forall i, 0 <= i <= 2 -> rd_ok E n 13 i.
Definition seg_rd14_stmt : Prop :=
  forall E n, env_ok E -> check_text_masks_contract -> latch_ok E n 0x14b1c ->
    forall i, 0 <= i <= 2 -> rd_ok E n 14 i.

(** 0x14390-0x144c8, 79 instructions: the switch of fuzz_codec.c:533 and the twelve calls. *)
Definition seg_run_stmt : Prop :=
  forall E n, env_ok E ->
    diginet_fader_encode_contract -> diginet_button_encode_contract -> diginet_touch_encode_contract ->
    diginet_vpot_encode_contract -> diginet_jog_encode_contract -> diginet_ring_encode_contract ->
    diginet_meter_encode_contract -> diginet_strip_leds_encode_contract ->
    diginet_counter_leds_encode_contract -> diginet_scribble_encode_contract ->
    diginet_counter_encode_contract -> diginet_sysex_encode_contract ->
    (forall k, rec_wf k -> join_ok E n k) ->
    rd_run E n /\ rd_run_arm E n.

(** 0x144cc-0x14524, 0x14588-0x1459c and the E_ARG tail 0x145ac-0x145b0 with the want_rc store
    0x14a30: owe()'s prologue, its switch, and the return of fuzz_codec.c:132-133. *)
Definition seg_owehd_stmt : Prop :=
  forall E n, env_ok E -> chk_ok E n -> (forall k, rec_wf k -> owe_ok E n k) ->
    forall k, rec_wf k -> join_ok E n k.

(** The cases of owe(), each ending at 0x14a34 through its own tail or through OWEX 0x14a2c. *)
Definition seg_owe0_stmt : Prop :=
  forall E n, env_ok E -> chk_ok E n ->
    forall k, rec_wf k -> k_kind k <= 4 -> owe_ok E n k.
Definition seg_owe5_stmt : Prop :=
  forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 5 -> owe_ok E n k.
Definition seg_owe6_stmt : Prop :=
  forall E n, env_ok E -> chk_ok E n -> forall k, rec_wf k -> k_kind k = 6 -> owe_ok E n k.
Definition seg_owe7_stmt : Prop :=
  forall E n, env_ok E -> chk_ok E n ->
    forall k, rec_wf k -> (k_kind k = 7 \/ k_kind k = 8) -> owe_ok E n k.
Definition seg_owe9_stmt : Prop :=
  forall E n, env_ok E -> memcpy_contract -> owe_sysex_contract -> chk_ok E n ->
    forall k, rec_wf k -> k_kind k = 9 -> owe_ok E n k.
Definition seg_owe10_stmt : Prop :=
  forall E n, env_ok E -> memcpy_contract -> chk_ok E n ->
    forall k, rec_wf k -> k_kind k = 10 -> owe_ok E n k.
Definition seg_owe11_stmt : Prop :=
  forall E n, env_ok E -> owe_sysex_contract -> chk_ok E n ->
    forall k, rec_wf k -> k_kind k = 11 -> owe_ok E n k.

(** 0x14a34-0x14a50, 8 instructions: the three checks, their premises discharged by codec_agree. *)
Definition seg_chk_stmt : Prop :=
  forall E n, env_ok E -> check_refusal_contract -> check_range_contract -> check_bytes_contract ->
    latch_ok E n 0x14a54 -> chk_ok E n.

(** ---- a closed witness that the head invariant is satisfiable ---- *)

(** The witness stack of codec_contract_sat, with the frame the prologue leaves: the three spilled
    constants, a zeroed record, the cursor at the input, and the saved registers (all zero). *)
Definition sat_main_mem : word -> option byte :=
  smem [(MSP + 8, le8 (Z_to_bv 64 0x990) ++ le8 (Z_to_bv 64 0x5cb0) ++ le8 (Z_to_bv 64 0xffff));
        (SIN, le8 (Z_to_bv 64 SDATA) ++ le8 (Z_to_bv 64 10));
        (SDATA, sat_input)].

Definition sat_env (F : bvmap 5 word) (fc : bv 32) : cenv :=
  mkCenv (Z_to_bv 64 0) (Z_to_bv 64 SAT_SP) (Z_to_bv 64 0) (Z_to_bv 64 0)
         (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
         (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
         (Z_to_bv 64 SDATA) F fc sat_main_mem SAT_LO sat_input.

(** Every premise of [loop_ok] holds at ops = 0, c = 0 of this state: the invariant is not vacuous. *)
Lemma sat_loop_ok_head : forall (F : bvmap 5 word) (fc : bv 32),
  env_ok (sat_env F fc) /\
  256 - 0 <= Z.of_nat 256 /\ 0 <= 0 <= 255 /\
  1 <= bv_unsigned (Z_to_bv 64 10) /\
  bv_unsigned (Z_to_bv 64 SDATA) = bv_unsigned (c_p (sat_env F fc)) + 0 /\ 0 <= 0 /\
  0 + bv_unsigned (Z_to_bv 64 10) = Z.of_nat (length (c_data (sat_env F fc))) /\
  fr (sat_env F fc) (c_m (sat_env F fc)) [CB 184 (sat_z0 184)] (Z_to_bv 64 SDATA) (Z_to_bv 64 10)
     (sat_z0 8) (sat_z0 5) (sat_z0 65) (sat_z0 10) /\
  stk rsegs (c_m (sat_env F fc)) (c_lo (sat_env F fc)) (bv_unsigned (c_sp (sat_env F fc)) + -416) /\
  munch [(bv_unsigned (c_sp (sat_env F fc)) - 640, bv_unsigned (c_sp (sat_env F fc)))]
        (c_m (sat_env F fc)) (c_m (sat_env F fc)) /\
  wmono rsegs (c_m (sat_env F fc)) (c_m (sat_env F fc)) /\
  mem_inv rsegs (c_m (sat_env F fc)).
Proof.
  intros F fc. unfold sat_env, env_ok, fr, saved, sat_main_mem. cenv_cbn.
  repeat match goal with |- _ /\ _ => split end;
    try (apply munch_refl); try (apply wmono_refl);
    try (unfold disj, RELRO_BASE, RELRO_LEN, SAT_LO, SAT_SP, MSP, SIN, SDATA; sat).
Qed.
