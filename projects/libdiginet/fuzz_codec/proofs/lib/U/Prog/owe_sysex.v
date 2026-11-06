(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 532 of its 545 lines of code are new or changed and 47 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_next_lib.v, with its module paths and module names changed; 213 of its 263 lines of code are new or changed and 495 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_chk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells memcpy_c owe_sysex_c.
Import ListNotations.
Open Scope Z_scope.

(** The function writes want[0..2) (sh 0x13f0 at k + 0x90), want[2] = device and want[3] = fn (sb), then
    memcpy(k + 0x94, pl, n), want[4 + n] = 0xf7, want_len = n + 5 and want_display. Before the walk the CB 24
    cell of want is cut into CB 2, CB 1, CB 1 (the three stores), CB n (memcpy's destination), CB 1 (the
    0xf7 byte) and CB (19 - n) (left unchanged); after the walk the pieces are merged back into the CB 24
    cell of set_want. The three UBSan traps (target 0x155ec): the alignment test of k (k mod 8 = 0), the
    bound 4 + n < 24 (n <= 19) and the pointer-overflow test of want + 4 + n (k + 184 <= 2^64, since the
    cells of k are in memory) are each refuted by the premise or fact named. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma ow_app_split : forall m A cs1 cs2,
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

Lemma ow_app_join : forall m A cs1 cs2,
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

(** The 14 cells of struct call before want (offsets 0 .. 144). *)
Definition kpre (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k));
   CB 32 (k_before k); CB 32 (k_out k); C4 (Z_to_bv 64 (k_want_rc k))].

Lemma kcall_cells_eq : forall k, kcall_cells k =
  kpre k ++ CB 24 (k_want k)
    :: [C8 (Z_to_bv 64 (k_want_len k)); C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].
Proof. reflexivity. Qed.

Lemma kpre_set_want : forall k w wl wd, kpre (set_want k w wl wd) = kpre k.
Proof. reflexivity. Qed.

Lemma ow_split6 : forall m A pre post (c1 c2 c3 c4 c5 c6 : cell),
  rw_cells rsegs m A (pre ++ [c1; c2; c3; c4; c5; c6] ++ post) ->
  rw_cells rsegs m A (pre ++ [c1; c2; c3]) /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (pre ++ [c1; c2; c3]))) [c4] /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (pre ++ [c1; c2; c3; c4]))) [c5; c6] /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (pre ++ [c1; c2; c3; c4; c5; c6]))) post.
Proof.
  intros m A pre post c1 c2 c3 c4 c5 c6 H.
  replace (pre ++ [c1; c2; c3; c4; c5; c6] ++ post)
    with ((pre ++ [c1; c2; c3]) ++ [c4] ++ [c5; c6] ++ post) in H by (rewrite <- app_assoc; reflexivity).
  apply ow_app_split in H. destruct H as [H1 H]. split; [exact H1|].
  apply ow_app_split in H. destruct H as [H2 H]. split; [exact H2|].
  apply ow_app_split in H. destruct H as [H3 H4].
  assert (E3 : A + Z.of_nat (cells_size (pre ++ [c1; c2; c3])) + Z.of_nat (cells_size [c4])
               = A + Z.of_nat (cells_size (pre ++ [c1; c2; c3; c4])))
    by (rewrite !cells_size_app; cbn [cells_size]; lia).
  assert (E4 : A + Z.of_nat (cells_size (pre ++ [c1; c2; c3])) + Z.of_nat (cells_size [c4])
                 + Z.of_nat (cells_size [c5; c6])
               = A + Z.of_nat (cells_size (pre ++ [c1; c2; c3; c4; c5; c6])))
    by (rewrite !cells_size_app; cbn [cells_size]; lia).
  rewrite E3 in H3. rewrite E4 in H4. split; [exact H3 | exact H4].
Qed.

(** The cells of k with want cut for the walk: CB 2, CB 1, CB 1 (stored by the walk), CB n (memcpy's
    destination), CB 1 (the 0xf7 byte), CB (19 - n) (the bytes after want[4 + n], kept). The last two are
    separate hypotheses: the store tactic normalizes the cell list it writes, which would unfold 19 - n. *)
Lemma ow_split : forall m A k (n : nat),
  length (k_want k) = 24%nat -> (n <= 19)%nat ->
  rw_cells rsegs m A (kcall_cells k) ->
  exists x1 x2 x3 x4 x5,
    rw_cells rsegs m A (kpre k ++ [CB 2 x1; CB 1 x2; CB 1 x3]) /\
    rw_cells rsegs m (A + 148) [CB n x4] /\
    rw_cells rsegs m (A + 148 + Z.of_nat n) [CB 1 x5] /\
    rw_cells rsegs m (A + 148 + Z.of_nat n + 1) [CB (19 - n) (skipn (n + 5) (k_want k))] /\
    rw_cells rsegs m (A + 168)
      [C8 (Z_to_bv 64 (k_want_len k)); C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].
Proof.
  intros m A k n Lw Hn H.
  rewrite kcall_cells_eq in H.
  apply (rw_cells_split_CB rsegs m A (kpre k) 24 (k_want k) _ [2; 1; 1; n; 1; 19 - n]%nat) in H;
    [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells] in H.
  apply ow_split6 in H. destruct H as (H1 & H2 & H3 & H4).
  match type of H2 with rw_cells _ _ ?a _ => replace a with (A + 148) in H2 by reflexivity end.
  match type of H3 with rw_cells _ _ ?a _ =>
    replace a with (A + 148 + Z.of_nat n) in H3
      by (rewrite !cells_size_app; change (cells_size (kpre k)) with 144%nat; cbn [cells_size csize]; lia) end.
  match type of H4 with rw_cells _ _ ?a _ =>
    replace a with (A + 168) in H4
      by (rewrite !cells_size_app; change (cells_size (kpre k)) with 144%nat; cbn [cells_size csize]; lia) end.
  match type of H3 with rw_cells _ _ _ [CB 1 _; CB _ ?x6] =>
    replace x6 with (skipn (n + 5) (k_want k)) in H3
      by (rewrite !skipn_skipn; rewrite firstn_all2 by (rewrite length_skipn; lia); f_equal; lia) end.
  match type of H3 with rw_cells _ _ ?a [CB 1 ?x5; ?c6] =>
    destruct (ow_app_split m a [CB 1 x5] [c6] H3) as [H3a H3b] end.
  do 5 eexists. split; [exact H1|]. split; [exact H2|]. split; [exact H3a|]. split; [exact H3b | exact H4].
Qed.

(** The pieces of k after the walk, joined back: want is one CB 24 cell again. *)
Lemma ow_join : forall m A k (pl : list byte) (v2 : word) (b2 b3 b4 : byte) (tail : list byte) (wl wd : word),
  (length pl <= 19)%nat ->
  rw_cells rsegs m A (kpre k ++ [C2 v2; C1 b2; C1 b3]) ->
  rw_cells rsegs m (A + 148) [CB (length pl) pl] ->
  rw_cells rsegs m (A + 148 + Z.of_nat (length pl)) [C1 b4] ->
  rw_cells rsegs m (A + 148 + Z.of_nat (length pl) + 1) [CB (19 - length pl) tail] ->
  rw_cells rsegs m (A + 168) [C8 wl; C4 (Z_to_bv 64 (k_want_key k)); C4 wd] ->
  rw_cells rsegs m A (kpre k ++ CB 24 (le2 v2 ++ [b2; b3] ++ pl ++ [b4] ++ tail)
                        :: [C8 wl; C4 (Z_to_bv 64 (k_want_key k)); C4 wd]).
Proof.
  intros m A k pl v2 b2 b3 b4 tail wl wd Hn H1 H2 H3a H3b H4.
  assert (H3 : rw_cells rsegs m (A + 148 + Z.of_nat (length pl)) [C1 b4; CB (19 - length pl) tail])
    by (apply (ow_app_join m _ [C1 b4] [CB (19 - length pl) tail]); [exact H3a | exact H3b]).
  assert (S1 : cells_size (kpre k ++ [C2 v2; C1 b2; C1 b3]) = 148%nat) by reflexivity.
  assert (J1 : rw_cells rsegs m A ((kpre k ++ [C2 v2; C1 b2; C1 b3]) ++ [CB (length pl) pl])).
  { apply ow_app_join; [exact H1|]. rewrite S1. exact H2. }
  assert (S2 : cells_size ((kpre k ++ [C2 v2; C1 b2; C1 b3]) ++ [CB (length pl) pl]) = (148 + length pl)%nat).
  { rewrite cells_size_app, S1. cbn [cells_size csize]. lia. }
  assert (J2 : rw_cells rsegs m A
                 (((kpre k ++ [C2 v2; C1 b2; C1 b3]) ++ [CB (length pl) pl]) ++ [C1 b4; CB (19 - length pl) tail])).
  { apply ow_app_join; [exact J1|]. rewrite S2.
    replace (A + Z.of_nat (148 + length pl)) with (A + 148 + Z.of_nat (length pl)) by lia. exact H3. }
  assert (S3 : cells_size (((kpre k ++ [C2 v2; C1 b2; C1 b3]) ++ [CB (length pl) pl])
                             ++ [C1 b4; CB (19 - length pl) tail]) = 168%nat).
  { rewrite cells_size_app, S2. cbn [cells_size csize]. lia. }
  assert (J3 : rw_cells rsegs m A
                 ((((kpre k ++ [C2 v2; C1 b2; C1 b3]) ++ [CB (length pl) pl]) ++ [C1 b4; CB (19 - length pl) tail])
                    ++ [C8 wl; C4 (Z_to_bv 64 (k_want_key k)); C4 wd])).
  { apply ow_app_join; [exact J2|]. rewrite S3. exact H4. }
  rewrite <- !app_assoc in J3.
  pose proof (rw_cells_merge rsegs m A (kpre k)
                [C2 v2; C1 b2; C1 b3; CB (length pl) pl; C1 b4; CB (19 - length pl) tail]
                [C8 wl; C4 (Z_to_bv 64 (k_want_key k)); C4 wd] J3) as M.
  replace (cells_size [C2 v2; C1 b2; C1 b3; CB (length pl) pl; C1 b4; CB (19 - length pl) tail])
    with 24%nat in M by (cbn [cells_size csize]; lia).
  replace (cells_bytes [C2 v2; C1 b2; C1 b3; CB (length pl) pl; C1 b4; CB (19 - length pl) tail])
    with (le2 v2 ++ [b2; b3] ++ pl ++ [b4] ++ tail) in M
    by (cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity).
  exact M.
Qed.

Lemma le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

Lemma le2_13f0 : le2 (Z_to_bv 64 0x13f0) = [b8 0xf0; b8 0x13].
Proof.
  apply nth_ext with (d := b8 0) (d' := b8 0); [rewrite length_le2; reflexivity|].
  intros i Hi. rewrite length_le2 in Hi.
  destruct i as [|[|i]]; [| | lia]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma b8_zb : forall l : list byte, map b8 (zb l) = l.
Proof.
  intros l. unfold zb, b8. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(** want_display: ((fn - 0x30) & 0xef) == 0 holds for fn = 0x30 and 0x40 only. *)
Lemma ow_disp : forall fn, 0 <= fn < 256 ->
  Z.b2z (Z.land ((fn + -48) mod 18446744073709551616) 239 <? 1) = bit_or_0 ((u8 fn =? 0x40) || (u8 fn =? 0x30)) 1.
Proof.
  intros fn Hfn.
  change 18446744073709551616 with (2 ^ 64).
  rewrite <- land_mask_mod by lia.
  assert (G : forallb (fun x => Z.b2z (Z.land (x + -48) 239 <? 1) =? bit_or_0 ((u8 x =? 0x40) || (u8 x =? 0x30)) 1)
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in G.
  apply Z.eqb_eq. apply G. apply in_map_iff. exists (Z.to_nat fn). split; [lia | apply in_seq; lia].
Qed.

(** The postcondition's cells from the joined pieces. *)
Lemma ow_final : forall m A k dev fn (pl : list byte) (b2 b3 b4 : byte) (wl wd : word),
  rw_cells rsegs m A (kpre k ++ [C2 (Z_to_bv 64 0x13f0); C1 b2; C1 b3]) ->
  rw_cells rsegs m (A + 148) [CB (length pl) pl] ->
  rw_cells rsegs m (A + 148 + Z.of_nat (length pl)) [C1 b4] ->
  rw_cells rsegs m (A + 148 + Z.of_nat (length pl) + 1) [CB (19 - length pl) (skipn (length pl + 5) (k_want k))] ->
  rw_cells rsegs m (A + 168) [C8 wl; C4 (Z_to_bv 64 (k_want_key k)); C4 wd] ->
  0 <= dev < 256 -> 0 <= fn < 256 -> (length pl <= 19)%nat ->
  b2 = b8 dev -> b3 = b8 fn -> b4 = b8 0xf7 ->
  wl = Z_to_bv 64 (Z.of_nat (length pl) + 5) ->
  wd = Z_to_bv 64 (bit_or_0 ((u8 fn =? 0x40) || (u8 fn =? 0x30)) 1) ->
  let '(w, dp) := owe_sx dev fn (zb pl) in
  rw_cells rsegs m A (kcall_cells (set_want k (bz w ++ skipn (length w) (k_want k)) (Z.of_nat (length w)) dp)).
Proof.
  intros m A k dev fn pl b2 b3 b4 wl wd H1 H2 H3a H3b H4 Hd Hf Hn -> -> -> -> ->.
  pose proof (ow_join m A k pl _ _ _ _ _ _ _ Hn H1 H2 H3a H3b H4) as J.
  unfold owe_sx. cbv beta iota zeta.
  rewrite kcall_cells_eq, kpre_set_want. cbn [set_want k_want k_want_len k_want_key k_want_display].
  assert (L5 : length ([0xf0; 0x13; u8 dev; u8 fn] ++ zb pl ++ [0xf7]) = (length pl + 5)%nat)
    by (rewrite !length_app; unfold zb; rewrite length_map; cbn [length]; lia).
  rewrite L5.
  replace (bz ([0xf0; 0x13; u8 dev; u8 fn] ++ zb pl ++ [0xf7]))
    with (le2 (Z_to_bv 64 0x13f0) ++ [b8 dev; b8 fn] ++ pl ++ [b8 0xf7]).
  2: { unfold bz. rewrite !map_app, b8_zb, le2_13f0. cbn [map app]. unfold u8.
       rewrite !Z.mod_small by lia. reflexivity. }
  replace (Z.of_nat (length pl + 5)) with (Z.of_nat (length pl) + 5) by lia.
  rewrite <- !app_assoc. exact J.
Qed.

Theorem owe_sysex_holds : memcpy_contract -> owe_sysex_contract.
Proof.
  intros MEMCPY. unfold memcpy_contract in MEMCPY.
  unfold owe_sysex_contract, owe_sysex_pre, OWE_SYSEX, OWE_SYSEX_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo dev fn k pl
         (HK & HW & HAL & [Hdev Ea1] & [Hfn Ea2] & HPL & Ea4 & HN & HDJ & HSP0 & HSP3 & HMI & ST & LO).
  subst a1 a2.
  unfold disj in HDJ.
  change (2 ^ 8) with 256 in Hdev, Hfn.
  assert (HBk : 0 <= bv_unsigned a0 /\ bv_unsigned a0 + 184 <= 2 ^ 64)
    by (pose proof (rw_cells_bound _ _ _ _ HK) as X; cbn [kcall_cells cells_size csize Nat.add] in X; exact X).
  assert (Lw : length (k_want k) = 24%nat).
  { destruct HK as [[Hwf _] _]. unfold kcall_cells in Hwf. cbn [cells_wf cell_wf] in Hwf. tauto. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a3) as Ra3. unfold bv_modulus in Rsp, Ra0, Ra3.
  remember (length pl) as n eqn:En.
  assert (Ea4' : a4 = Z_to_bv 64 (Z.of_nat n)) by (rewrite <- Ea4; symmetry; apply Z_to_bv_bv_unsigned).
  subst a4. rename Ea4 into Un.
  destruct (ow_split m (bv_unsigned a0) k n Lw HN HK) as (x1 & x2 & x3 & x4 & x5 & HP & HM & HT1 & HT2 & HQ).
  clear HK.
  unfold kpre in HP. cbn [app] in HP.
  remember (bv_unsigned a0 + 148 + Z.of_nat n) as B eqn:EB.
  assert (U148 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 148)) = bv_unsigned a0 + 148)
    by (apply unsigned_lit; lia).
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a0 + 144, bv_unsigned a0 + 184)] m m)
    by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  carve_frame 32%nat ST.
  (* addi sp, sp, -0x20; sd ra, s0, s1, s2 *)
  zstep. zstep. zstep. zstep. zstep.
  (* mv s0, a0; andi a0, a0, 7; bnez a0 -> trap 0x155ec: k mod 8 = 0 *)
  step. step. step.
  if_cases K0.
  { exfalso. rewrite chk_land7, HAL, bv_eqb_refl in K0 by lia. discriminate K0. }
  (* mv s2, a4; mv s1, a2; lui a0, 1; addi a0, a0, 0x3f0; sh a0, 0x90(s0) *)
  zstep. zstep. zstep. zstep. zstep.
  (* sb a1, 0x92(s0); sb a2, 0x93(s0) *)
  step. rewrite le1_byte. mem_after_store.
  step. rewrite le1_byte. mem_after_store.
  (* addi a0, s0, 0x94; mv a1, a3; mv a2, a4; jal memcpy *)
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply MEMCPY with (src := pl) (junk := x4);
                      [ exact HPL | rewrite Un; lia | rewrite U148, Un, Nat2Z.id; exact HM
                      | rewrite U148, Un; lia | exact HMI ]
                    | post_call segs mm ] end.
  rewrite U148, Un, Nat2Z.id in PC. rename PC into HM.
  (* addi a0, s2, 4; addi a1, zero, 0x18; bgeu a0, a1 -> trap: 4 + n < 24 needs n <= 19 (premise) *)
  zstep. zstep. zstep.
  if_cases T1; [ exfalso; zify_cond T1; lia | zify_cond T1 ].
  (* addi a1, s0, 0x90; not a2, a1; bltu a2, a0 -> trap: k + 0x90 + 4 + n does not wrap, since the cells
     of k lie below 2^64 *)
  zstep. zstep. zstep.
  if_cases T2; [ exfalso; zify_cond T2; rewrite zb_lxor_ones in T2 by lia; lia | zify_cond T2 ].
  (* add a0, a1, a0; addi a1, zero, -9; addi s2, s2, 5; addi a2, s1, -0x30; sb a1, 0(a0) *)
  zstep. zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (bv_unsigned a0 + 144 + ?x)] =>
    replace (Z_to_bv 64 (bv_unsigned a0 + 144 + x)) with (Z_to_bv 64 B) by (f_equal; lia) end.
  step. rewrite le1_byte. mem_after_store.
  (* andi a0, a2, 0xef; seqz a0, a0; sd s2, 0xa8(s0); sw a0, 0xb4(s0) *)
  zstep. zstep. zstep. zstep.
  (* ld ra, s0, s1, s2; addi sp, sp, 0x20; ret *)
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. zstep.
  finish.
  subst B n.
  match type of HP with
  | rw_cells ?s ?mm ?A (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?c1 :: ?c2 :: ?c3 :: []) =>
      change (rw_cells s mm A (kpre k ++ [c1; c2; c3])) in HP
  end.
  eapply (ow_final _ _ k dev fn pl _ _ _ _ _ HP HM HT1 HT2 HQ Hdev Hfn HN).
  - unfold b8. rewrite unsigned_lit by lia. reflexivity.
  - unfold b8. rewrite unsigned_lit by lia. reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - reflexivity.
  - f_equal. apply ow_disp. exact Hfn.
Qed.
