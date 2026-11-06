(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths changed; 482 of its 519 lines of code are new or changed and 224 lines of the source are left out. *)
(** The key segment of reac_headamp_prop_parse_result (plain image, 0x14ab4-0x14b58) against Prog/Seg/ParseCut.v:
    [pk_key] proves the cut [S_KEY] from the value cut [S_VALUE] and the refusal cut [S_REFUSE] it reaches, with
    strtol_contract (Prog/strtol_c.v) and strcmp_contract (Prog/strcmp_c.v) as premises. The code is parse_key
    (reac_headamp_prop.c:70-85, 153-160): keys++, strtol(key + 13, &dot, 10) at 0x14acc (its premises from
    ParseSites.strtol_site), dot == rest and *dot != '.' to BAD_KEY, ch = the value, strcmp of the name dot + 1
    against "phantom", "pad" and "sens" (0x1d744, the literals by ParseSites.lits_at) to the param or BAD_KEY, the
    channel range (bltu at 0x14b50) to the value cut or OUT_OF_RANGE. Pod/Headamp.v's parse_key reads the same tests:
    e = s10_end rest, the byte nth e rest (rest's NUL when e = |rest|), param_of_name (cstr (skipn (S e) rest)),
    the range on s10_val rest. The dot cell 0x28 lies in the frame's temporary cells 0x20 .. 0x38: the frame is cut
    around it for strtol's write and merged back for the cuts. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Step Image FP ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Strtol Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import
  reac_headamp_prop_parse_result_c strtol_c strcmp_c ParseSites.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import ParseCut.
Import ListNotations.
Open Scope Z_scope.

Definition pk_hide (A : Prop) : Prop := A.
Ltac pk_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

(** ** strtol's end offset *)
Lemma pk_ndig_le : forall l, (ndig l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [ndig length]; [lia|]. destruct (c_digit b); lia. Qed.

Lemma pk_rest_le : forall s, (length (s10_rest s) <= length s)%nat.
Proof.
  intros s. unfold s10_rest. pose proof (length_sign_split (skip_space s)). pose proof (length_skip_space s). lia.
Qed.

Lemma pk_end_le : forall s, 0 <= s10_end s <= Z.of_nat (length s).
Proof.
  intros s. pose proof (pk_rest_le s) as R. pose proof (pk_ndig_le (s10_rest s)) as N.
  unfold s10_end, s10_nd. destruct (Nat.eqb (ndig (s10_rest s)) 0); lia.
Qed.

Lemma pk_val_range : forall s, - 2^63 <= s10_val s < 2^63.
Proof. intros s. unfold s10_val, LMIN. lia. Qed.

(** ** Cells and bytes *)
Lemma pk_rwc_split : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (H0 & H1 & H2)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in H1, H2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H2. lia.
Qed.

Lemma pk_rwc_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H2)] [[W2 B2] (G0 & G1 & G2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - unfold wr_at. rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply H2. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G2. lia.
Qed.

(** The frame after the store of the dot cell, in three parts: below the dot cell, the dot cell, above it. *)
Lemma pk_split_dot : forall m A B B' c1 c2 c3 d rest,
  rw_cells rsegs m A (c1 :: c2 :: c3 :: C8 d :: rest) -> (csize c1 + csize c2 + csize c3 = 40)%nat ->
  B = A + 40 -> B' = A + 48 ->
  rw_cells rsegs m A [c1; c2; c3] /\ rw_cells rsegs m B [C8 d] /\ rw_cells rsegs m B' rest.
Proof.
  intros m A B B' c1 c2 c3 d rest H Hs -> ->.
  destruct (pk_rwc_split m A (A + 40) [c1; c2; c3] (C8 d :: rest) H) as [H1 H2].
  { cbn [cells_size]. lia. }
  destruct (pk_rwc_split m (A + 40) (A + 48) [C8 d] rest H2) as [H3 H4]; [cbn; lia|].
  tauto.
Qed.

Lemma pk_join_dot : forall m A B B' c1 c2 c3 d rest,
  rw_cells rsegs m A [c1; c2; c3] -> rw_cells rsegs m B [C8 d] -> rw_cells rsegs m B' rest ->
  (csize c1 + csize c2 + csize c3 = 40)%nat -> B = A + 40 -> B' = A + 48 ->
  rw_cells rsegs m A (c1 :: c2 :: c3 :: C8 d :: rest).
Proof.
  intros m A B B' c1 c2 c3 d rest H1 H2 H3 Hs -> ->.
  pose proof (pk_rwc_join m (A + 40) (A + 48) [C8 d] rest H2 H3 ltac:(cbn; lia)) as H23.
  exact (pk_rwc_join m A (A + 40) [c1; c2; c3] (C8 d :: rest) H1 H23 ltac:(cbn [cells_size]; lia)).
Qed.

Lemma pk_stk_frame : forall m lo A cs n,
  stk rsegs m lo A -> rw_cells rsegs m A cs -> Z.of_nat (cells_size cs) = n -> lo <= A -> stk rsegs m lo (A + n).
Proof. intros m lo A cs n S F <- H. exact (stk_release rsegs m lo A cs S F H). Qed.

Lemma pk_first1 : forall (l : list byte) k b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  induction l as [|x l IH]; intros [|k] b H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma pk_read1 : forall m A bs k b, bytes_at rsegs m A bs -> 0 <= k -> nth_error bs (Z.to_nat k) = Some b ->
  ov_read_bytes rsegs m (wa (A + k)) 1 = Some [b].
Proof.
  intros m A bs k b H Hk Hn.
  assert (L : (Z.to_nat k < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m A bs k 1 H Hk) by lia.
  rewrite (pk_first1 _ _ _ Hn). reflexivity.
Qed.

Lemma pk_bytes_skip : forall m A (l : list byte) n, bytes_at rsegs m A l -> (n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat n) (skipn n l).
Proof.
  intros m A l n H Hn. rewrite <- (firstn_skipn n l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min n (length l)) with n in H by lia. exact H.
Qed.

Lemma pk_bytes_first : forall m A (l : list byte) n, bytes_at rsegs m A l -> bytes_at rsegs m A (firstn n l).
Proof.
  intros m A l n H. rewrite <- (firstn_skipn n l) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma pk_bytes_sub : forall m A bs o n, bytes_at rsegs m A bs -> 0 <= o -> o + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (A + o) (firstn n (skipn (Z.to_nat o) bs)).
Proof.
  intros m A bs o n H Ho Hn. apply pk_bytes_first.
  pose proof (pk_bytes_skip m A bs (Z.to_nat o) H ltac:(lia)) as H1.
  replace (A + o) with (A + Z.of_nat (Z.to_nat o)) by lia. exact H1.
Qed.

Lemma pk_bytes_addr : forall m A A' l, bytes_at rsegs m A l -> A = A' -> bytes_at rsegs m A' l.
Proof. intros m A A' l H <-. exact H. Qed.

Lemma pk_skipn_app_le : forall (l r : list byte) n, (n <= length l)%nat -> skipn n (l ++ r) = skipn n l ++ r.
Proof. intros l r n H. rewrite skipn_app. replace (n - length l)%nat with O by lia. reflexivity. Qed.

Lemma pk_nth_app : forall (l : list byte) i, (i <= length l)%nat -> nth_error (l ++ [NUL]) i = Some (nth i l NUL).
Proof.
  intros l i H. destruct (Nat.eq_dec i (length l)) as [->|N].
  - rewrite nth_error_app2, Nat.sub_diag by lia. rewrite nth_overflow by lia. reflexivity.
  - rewrite nth_error_app1 by lia. apply nth_error_nth'. lia.
Qed.

Lemma pk_nonul_skipn : forall (l : list byte) n, ~ In NUL l -> ~ In NUL (skipn n l).
Proof.
  intros l n H X. apply H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact X.
Qed.

Lemma pk_cstr_nonul : forall l, ~ In NUL l -> cstr l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. unfold cstr in *. cbn [nul_idx].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
  - exfalso. apply H. left. apply bv_eq. rewrite E. reflexivity.
  - cbn [firstn]. f_equal. apply IH. intros X. apply H. right. exact X.
Qed.

Lemma pk_nth_len : forall (l : list byte) i, bv_unsigned (nth i l NUL) = 46 -> (i < length l)%nat.
Proof.
  intros l i H. destruct (Nat.lt_ge_cases i (length l)) as [L|L]; [exact L|].
  rewrite nth_overflow in H by exact L. vm_compute in H. discriminate H.
Qed.

(** ** Branch conditions *)
Lemma pk_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pk_eqb_byte : forall (b : byte) y, 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 y) = (bv_unsigned b =? y).
Proof. intros b y Hy. pose proof (byte_range b). apply pk_eqb_lit; lia. Qed.

Lemma pk_ltu48 : forall v, - 2^63 <= v < 2^63 -> bv_ltu (Z_to_bv 64 v) (Z_to_bv 64 48) = (0 <=? v) && (v <? 48).
Proof.
  intros v Hv. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.leb_spec 0 v) as [H0|H0].
  - rewrite (Z.mod_small v) by lia. reflexivity.
  - cbn [andb]. replace (v mod 2^64) with (v + 2^64).
    + change (48 mod 2^64) with 48. apply Z.ltb_ge. lia.
    + rewrite <- (Z.mod_small (v + 2^64) (2^64)) by lia. rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia.
      reflexivity.
Qed.

Lemma pk_word0 : forall r : word, bv_eqb r (Z_to_bv 64 0) = true -> r = Z_to_bv 64 0.
Proof. intros r H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma pk_word_ne : forall (r : word) (A : Prop), (r = Z_to_bv 64 0 <-> A) -> bv_eqb r (Z_to_bv 64 0) = false -> ~ A.
Proof.
  intros r A H E X. apply H in X. subst r. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate E.
Qed.

(** The frame with the dot cell merged back into the temporary cells 0x20 .. 0x38. *)
Lemma pk_merge_w : forall m A ja p j1 d j2 rest,
  rw_cells rsegs m A (CB 24 ja :: C8 p :: CB 8 j1 :: C8 d :: CB 8 j2 :: rest) ->
  rw_cells rsegs m A (CB 24 ja :: C8 p :: CB 24 (j1 ++ le8 d ++ j2) :: rest).
Proof.
  intros m A ja p j1 d j2 rest H.
  pose proof (rw_cells_merge rsegs m A [CB 24 ja; C8 p] [CB 8 j1; C8 d; CB 8 j2] rest H) as M.
  cbn [app cells_size cells_bytes cbytes csize Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.
(** The frame at the value cut: the dot cell merged back into the temporary cells 0x20 .. 0x38. *)
Lemma pk_merge_v : forall m A j0 b ch p j1 d j2 rest,
  rw_cells rsegs m A (CB 8 j0 :: C8 b :: C8 ch :: C8 p :: CB 8 j1 :: C8 d :: CB 8 j2 :: rest) ->
  rw_cells rsegs m A (CB 8 j0 :: C8 b :: C8 ch :: C8 p :: CB 24 (j1 ++ le8 d ++ j2) :: rest).
Proof.
  intros m A j0 b ch p j1 d j2 rest H.
  pose proof (rw_cells_merge rsegs m A [CB 8 j0; C8 b; C8 ch; C8 p] [CB 8 j1; C8 d; CB 8 j2] rest H) as M.
  cbn [app cells_size cells_bytes cbytes csize Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

(** The bound and the channel merged back into the temporary cells 0x00 .. 0x18. *)
Lemma pk_merge_vw : forall m A j0 b ch rest,
  rw_cells rsegs m A (CB 8 j0 :: C8 b :: C8 ch :: rest) ->
  rw_cells rsegs m A (CB 24 (j0 ++ le8 b ++ le8 ch) :: rest).
Proof.
  intros m A j0 b ch rest H.
  pose proof (rw_cells_merge rsegs m A [] [CB 8 j0; C8 b; C8 ch] rest H) as M.
  cbn [app cells_size cells_bytes cbytes csize Nat.add] in M. rewrite app_nil_r in M. exact M.
Qed.

(** ** parse_key on the rest string, by the tests the code makes *)
Lemma pk_key_nodot : forall s, s10_end s <> 0 -> bv_unsigned (nth (Z.to_nat (s10_end s)) s NUL) <> 46 ->
  parse_key s = KBad.
Proof.
  intros s H1 H2. unfold parse_key. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

Lemma pk_key_name : forall s, s10_end s <> 0 -> bv_unsigned (nth (Z.to_nat (s10_end s)) s NUL) = 46 ->
  parse_key s =
  match param_of_name (cstr (skipn (S (Z.to_nat (s10_end s))) s)) with
  | None => KBad
  | Some p => if (s10_val s <? 0) || (REAC_HEADAMP_MAX_CH <=? s10_val s) then KRange else KCell (s10_val s) p
  end.
Proof.
  intros s H1 H2. unfold parse_key. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_eq _ _) H2). reflexivity.
Qed.

Lemma pk_param_range : forall n p, param_of_name n = Some p -> 0 <= p <= HA_SENS.
Proof.
  intros n p H. unfold param_of_name in H.
  destruct (bytes_eqb n NAME_PHANTOM); [injection H as <-; unfold HA_PHANTOM, HA_SENS; lia|].
  destruct (bytes_eqb n NAME_PAD); [injection H as <-; unfold HA_PAD, HA_SENS; lia|].
  destruct (bytes_eqb n NAME_SENS); [injection H as <-; unfold HA_SENS; lia | discriminate H].
Qed.


(** ** The footprint *)
Lemma pk_sub : forall sp O n E R,
  sub_fp [(sp - 528, sp); (E, E + 4)] (parse_writes sp O n E R).
Proof.
  intros sp O n E R x H. unfold parse_writes, PARSE_STACK in H. cbn [app outside] in H.
  destruct H as (H1 & _ & H3 & _). cbn [outside]. split; [lia|]. split; [lia | exact I].
Qed.

(** ** The names *)
Lemma pk_nonul_lit : ~ In NUL NAME_PHANTOM /\ ~ In NUL NAME_PAD /\ ~ In NUL NAME_SENS.
Proof.
  unfold NAME_PHANTOM, NAME_PAD, NAME_SENS, NUL. vm_compute.
  split; [|split]; intros H; repeat destruct H as [H|H]; try discriminate H; exact H.
Qed.

Lemma pk_prefix_len : forall k, ha_prefix k = true -> (13 <= length k)%nat.
Proof.
  intros k H. unfold ha_prefix in H. apply bytes_eqb_eq in H.
  assert (L : length (firstn (length HA_PREFIX) k) = length HA_PREFIX) by (rewrite H; reflexivity).
  rewrite length_firstn in L. change (length HA_PREFIX) with 13%nat in L. lia.
Qed.

Section PK.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mi : word -> option byte)
  (lo P O cap R : Z) (bs : list byte) (ev can : word).
Local Abbreviation c := (PCtx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mi lo P O cap R bs ev can).
Hypothesis HC : pc_ok c.

Lemma pk_key_sec : strtol_contract -> strcmp_contract -> S_VALUE c -> S_REFUSE c -> S_KEY c.
Proof.
  intros HSTL HSCMP HV HRF. unfold S_KEY.
  intros r cc kk k rest cl keys rf m F fc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ja jb
    HKA Hst Hcc Hcc8 Hin Hcl Hk0 Hkr Hrf HKOK HPRE HRES HPM HFP.
  unfold PMem, wframe, saves, c_spf, c_E in HPM. pc_simpl. unfold c_spf. pc_simpl.
  destruct HPM as (FR & ST & MU & OB & (ev1 & EV) & WM & MI).
  pose proof HC as (HA & HSTK & HLO & HNR & HMI). pc_simpl.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (proj1 HSTK) as Hlo0.
  pose proof HA as (HB & HP0 & _ & HLEN & _ & HPlo & Hcap & HO0 & _ & HOlo & _ & _ & _ & HEd & _).
  cbn [disjoint_from] in HEd. destruct HEd as (HEd & HEd2 & HEd3 & _). unfold PARSE_ERRNO in HEd, HEd2, HEd3.
  pose proof (length_ha_cells_bytes cl) as LOB. apply (f_equal Z.of_nat) in LOB. rewrite Nat2Z.inj_mul in LOB.
  change (Z.of_nat 3) with 3 in LOB.
  cbn [key_ok] in HKOK. pc_simpl. destruct HKOK as (Hkk0 & Hkk1 & HkN & Hkb).
  pose proof (pk_prefix_len k HPRE) as Hk13.
  (* the rest string after the prefix, its bytes in the entry memory *)
  assert (BK : bytes_at rsegs mi (P + kk + 13) (skipn 13 k ++ [NUL])).
  { pose proof (pk_bytes_sub mi P bs kk (S (length k)) HB Hkk0 ltac:(lia)) as B1. rewrite Hkb in B1.
    pose proof (pk_bytes_skip mi (P + kk) (k ++ [NUL]) 13 B1 ltac:(rewrite length_app; lia)) as B2.
    rewrite pk_skipn_app_le in B2 by lia. eapply pk_bytes_addr; [exact B2 | lia]. }
  pose proof (pk_nonul_skipn k 13 HkN) as HsN.
  assert (Estr : skipn (length HA_PREFIX) k = skipn 13 k) by reflexivity.
  set (str := skipn 13 k) in *. assert (Lstr : Z.of_nat (length str) + 13 = Z.of_nat (length k))
    by (unfold str; rewrite length_skipn; lia).
  clearbody str.
  change (pk_hide (munch (parse_writes (bv_unsigned sp) O (Z.of_nat (length cl)) (PARSE_ERRNO tp) R) mi m)) in MU.
  unfold PARSE_STACK in HLO. unfold PARSE_ERRNO in EV.
  pose proof (munch_refl [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU1.
  (* 0x14ab4-0x14acc: keys++, rest = key + 13, dot = 0, then strtol(rest, &dot, 10) *)
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  (* strtol's premises at 0x1c998 (ParseSites.strtol_site) *)
  pose proof (pk_stk_frame m0 lo _ _ 160 ST FR ltac:(reflexivity) ltac:(lia)) as STK1.
  replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) in STK1 by lia.
  destruct (pk_split_dot m0 _ (bv_unsigned sp + -120) (bv_unsigned sp + -112) _ _ _ _ _ FR
              ltac:(reflexivity) ltac:(lia) ltac:(lia)) as (F1 & FD & F3).
  clear FR.
  assert (MU2 : munch (parse_writes (bv_unsigned sp) O (Z.of_nat (length cl)) (PARSE_ERRNO tp) R) mi m0).
  { eapply munch_trans; [exact MU | eapply munch_weaken; [apply pk_sub | exact MU1]]. }
  pose proof (strtol_site mi m0 lo sp tp P O cap R bs ev can (Z.of_nat (length cl)) (P + kk + 13) str
     (bv_unsigned sp + -120) (Z_to_bv 64 0) ev1 HA HLO ltac:(lia) MU2 ltac:(lia) ltac:(lia) BK STK1 MI EV
     ltac:(unfold PARSE_FRAME, PARSE_DOT; lia) FD) as PRE.
  clear MU2 STK1.
  assert (Esp : Z_to_bv 64 (bv_unsigned sp - PARSE_FRAME) = Z_to_bv 64 (bv_unsigned sp + -160))
    by (f_equal; unfold PARSE_FRAME; lia).
  rewrite Esp in PRE. clear Esp.
  pose proof (proj1 PRE) as BK0.
  eapply evt_cut; [eapply (strtol_use HSTL); exact PRE |].
  clear PRE.
  intros ms' PO. unfold strtol_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MUc
                  & WMc & MIc & STc & DOTc & ERRc).
  subst ms'. rewrite unsigned_lit in MUc, STc by lia.
  pose proof (rw_cells_transport rsegs _ m0 m2 _ _ F1 MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia))
    as F1'.
  pose proof (rw_cells_transport rsegs _ m0 m2 _ _ F3 MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia))
    as F3'.
  pose proof (bytes_at_transport rsegs _ m0 m2 _ _ OB MUc ltac:(cbn [disjoint_from]; lia)) as OB'.
  pose proof (bytes_at_transport rsegs _ m0 m2 _ _ BK0 MUc
                ltac:(cbn [disjoint_from]; rewrite length_app; cbn [length]; lia)) as BK2.
  assert (MU1' : munch [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)]
                   m m2).
  { eapply munch_trans; [exact MU1 | eapply munch_weaken; [| exact MUc]].
    unfold sub_fp. cbn [outside]. intros. lia. }
  pose proof (wmono_trans rsegs mi m0 m2 WM WMc) as WM'.
  pose proof (pk_join_dot m2 _ _ _ _ _ _ _ _ F1' DOTc F3' eq_refl ltac:(lia) ltac:(lia)) as FR.
  clear F1 F3 FD OB BK0 MU1 WM ST MI EV F1' F3' DOTc MUc WMc m0.
  rename OB' into OB, MU1' into MU1, WM' into WM, STc into ST, MIc into MI, ERRc into EV.
  pk_ret.
  pose proof (pk_end_le str) as HE. pose proof (pk_val_range str) as HVR.
  (* the refusal cut 0x14c5c from any memory the parse may reach here *)
  unfold S_REFUSE in HRF.
  assert (REF : forall bad (m' : word -> option byte) ja' jb'
                  (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word),
    0 <= bad <= 5 -> parse_cell k (child_at bs cc) = inl bad ->
    rw_cells rsegs m' (bv_unsigned sp + -160) (wframe c ja' jb') ->
    stk rsegs m' lo (bv_unsigned sp + -160) ->
    munch [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m' ->
    bytes_at rsegs m' O (ha_cells_bytes cl) ->
    (exists e', rw_cells rsegs m' (bv_unsigned tp + -164) [C4 e']) ->
    wmono rsegs mi m' -> mem_inv rsegs m' ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y5 y6 y7 (Z_to_bv 64 R)
               (Z_to_bv 64 (Z.of_nat (length cl))) y10 y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 cap) (Z_to_bv 64 O) (Z_to_bv 64 rf) (Z_to_bv 64 (P + r + 16))
               y22 (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 bad) (Z_to_bv 64 (P + r + 8))
               (Z_to_bv 64 (P + cc)) (Z_to_bv 64 8) y28 y29 y30 y31)
          F (Z_to_bv 64 0x14c5c) fc None m' (seg_rom rsegs))).
  { intros bad m' ja' jb' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31
      Hbad Hpc FR' ST' MU' OB' EV' WM' MI'.
    eapply HRF; [exact HKA | exact Hcl | exact Hk0 | exact Hkr | exact Hrf | exact Hbad | | | exact HFP].
    - unfold fold_after in HRES. rewrite Hpc in HRES. exact HRES.
    - unfold PMem, c_spf, c_E, PARSE_ERRNO. pc_simpl.
      split; [exact FR'|]. split; [exact ST'|].
      split; [eapply munch_trans; [exact MU | eapply munch_weaken; [apply pk_sub | exact MU']]|].
      split; [exact OB'|]. split; [exact EV'|]. split; [exact WM' | exact MI']. }
  (* 0x14ad0-0x14ad8: a3 = dot, s8 = BAD_KEY, dot == rest *)
  zstep. zstep. zstep.
  destruct (Z.eq_dec (s10_end str) 0) as [E0|E0].
  { replace (bv_eqb (Z_to_bv 64 (P + kk + 13 + s10_end str)) (Z_to_bv 64 (P + kk + 13))) with true;
      [cbv iota | symmetry; rewrite pk_eqb_lit by lia; apply Z.eqb_eq; lia].
    eapply REF.
    - unfold REFUSE_BAD_KEY. lia.
    - unfold parse_cell. rewrite Estr. unfold parse_key. rewrite E0. reflexivity.
    - exact (pk_merge_w _ _ _ _ _ _ _ _ FR).
    - exact ST.
    - exact MU1.
    - exact OB.
    - exists (s10_errno str ev1). exact EV.
    - exact WM.
    - exact MI. }
  replace (bv_eqb (Z_to_bv 64 (P + kk + 13 + s10_end str)) (Z_to_bv 64 (P + kk + 13))) with false;
    [cbv iota | symmetry; rewrite pk_eqb_lit by lia; apply Z.eqb_neq; lia].
  (* 0x14adc-0x14ae4: *dot == '.' *)
  pose proof (pk_read1 m2 (P + kk + 13) (str ++ [NUL]) (s10_end str) _ BK2 ltac:(lia)
                (pk_nth_app str (Z.to_nat (s10_end str)) ltac:(lia))) as HRD.
  unfold wa in HRD.
  zstep. clear HRD. zstep. zstep.
  rewrite pk_eqb_byte by lia.
  destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat (s10_end str)) str NUL)) 46) as [D46|D46].
  2:{ replace (negb (bv_unsigned (nth (Z.to_nat (s10_end str)) str NUL) =? 46)) with true;
        [cbv iota | symmetry; apply negb_true_iff, Z.eqb_neq; exact D46].
      eapply REF.
      - unfold REFUSE_BAD_KEY. lia.
      - unfold parse_cell. rewrite Estr, (pk_key_nodot str E0 D46). reflexivity.
      - exact (pk_merge_w _ _ _ _ _ _ _ _ FR).
      - exact ST.
      - exact MU1.
      - exact OB.
      - exists (s10_errno str ev1). exact EV.
      - exact WM.
      - exact MI. }
  replace (negb (bv_unsigned (nth (Z.to_nat (s10_end str)) str NUL) =? 46)) with false;
    [cbv iota | symmetry; apply negb_false_iff, Z.eqb_eq; exact D46].
  pose proof (pk_nth_len str _ D46) as Hel.
  (* the name after the dot: a C string inside the pod *)
  pose proof (pk_bytes_skip m2 _ (str ++ [NUL]) (S (Z.to_nat (s10_end str))) BK2
                ltac:(rewrite length_app; cbn [length]; lia)) as BN.
  rewrite pk_skipn_app_le in BN by lia.
  apply (pk_bytes_addr _ _ (P + kk + 13 + s10_end str + 1)) in BN; [|lia].
  pose proof (pk_nonul_skipn str (S (Z.to_nat (s10_end str))) HsN) as HxN.
  pose proof (pk_cstr_nonul _ HxN) as Ecs.
  pose proof (pk_key_name str E0 D46) as EK. rewrite Ecs in EK.
  set (sx := skipn (S (Z.to_nat (s10_end str))) str) in *.
  assert (Lsx : Z.of_nat (length sx) + s10_end str + 1 = Z.of_nat (length str)) by (unfold sx; rewrite length_skipn; lia).
  clearbody sx.
  clear BK2.
  (* the channel range at 0x14b48 for the param p, then the value cut or the refusal OUT_OF_RANGE *)
  unfold S_VALUE in HV.
  assert (TAIL : forall p (m' : word -> option byte) j0 j1 d j2
                   (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    param_of_name sx = Some p ->
    rw_cells rsegs m' (bv_unsigned sp + -160)
      [CB 8 j0; C8 (Z_to_bv 64 (if p =? HA_SENS then 0x38 else 2)); C8 (Z_to_bv 64 (s10_val str));
       C8 (Z_to_bv 64 LIT_PREFIX); CB 8 j1; C8 d; CB 8 j2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
       C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m' lo (bv_unsigned sp + -160) ->
    munch [(bv_unsigned sp - 528, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m m' ->
    bytes_at rsegs m' O (ha_cells_bytes cl) ->
    (exists e', rw_cells rsegs m' (bv_unsigned tp + -164) [C4 e']) ->
    wmono rsegs mi m' -> mem_inv rsegs m' ->
    evt rsegs (PPost c (RESM c))
      (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y5 y6 y7 (Z_to_bv 64 R)
               (Z_to_bv 64 (Z.of_nat (length cl))) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 cap) (Z_to_bv 64 O) (Z_to_bv 64 rf) (Z_to_bv 64 (P + r + 16))
               (Z_to_bv 64 (P + kk + 13 + s10_end str + 1)) (Z_to_bv 64 (keys + 1)) (Z_to_bv 64 4)
               (Z_to_bv 64 (P + r + 8)) (Z_to_bv 64 (P + cc)) (Z_to_bv 64 8) y28 y29 y30 y31)
          F (Z_to_bv 64 0x14b48) fc None m' (seg_rom rsegs))).
  { intros p m' j0 j1 d j2 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Hp FR' ST' MU' OB' EV' WM' MI'.
    pose proof (pk_param_range _ _ Hp) as Hp2.
    rewrite Hp in EK.
    zstep. zstep. zstep.
    rewrite pk_ltu48 by lia.
    destruct (Z.le_gt_cases 0 (s10_val str)) as [V0|V0]; [destruct (Z.lt_ge_cases (s10_val str) 48) as [V1|V1]|].
    - replace ((0 <=? s10_val str) && (s10_val str <? 48)) with true;
        [cbv iota | symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
      eapply HV with (ch := s10_val str) (p := p);
                 [exact HKA | exact Hst | exact Hcc | exact Hcc8 | exact Hin | exact Hcl | exact Hk0 | exact Hkr
                 | exact Hrf | unfold REAC_HEADAMP_MAX_CH; lia | exact Hp2 | | | exact HFP].
      + pc_simpl. rewrite <- (parse_cell_vcell k (child_at bs cc) (s10_val str) p); [exact HRES|].
        rewrite Estr, EK. unfold REAC_HEADAMP_MAX_CH.
        rewrite (proj2 (Z.ltb_ge _ _) V0), (proj2 (Z.leb_gt _ _) V1). reflexivity.
      + unfold PMem, vframe, saves, c_spf, c_E, PARSE_ERRNO. pc_simpl.
        split; [exact (pk_merge_v _ _ _ _ _ _ _ _ _ _ FR')|]. split; [exact ST'|].
        split; [eapply munch_trans; [exact MU | eapply munch_weaken; [apply pk_sub | exact MU']]|].
        split; [exact OB'|]. split; [exact EV'|]. split; [exact WM' | exact MI'].
    - replace ((0 <=? s10_val str) && (s10_val str <? 48)) with false;
        [cbv iota | symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia].
      zstep. zstep.
      eapply REF.
      + unfold REFUSE_OUT_OF_RANGE. lia.
      + unfold parse_cell. rewrite Estr, EK. unfold REAC_HEADAMP_MAX_CH.
        rewrite (proj2 (Z.ltb_ge _ _) V0), (proj2 (Z.leb_le _ _) V1). reflexivity.
      + exact (pk_merge_w _ _ _ _ _ _ _ _ (pk_merge_vw _ _ _ _ _ _ FR')).
      + exact ST'.
      + exact MU'.
      + exact OB'.
      + exact EV'.
      + exact WM'.
      + exact MI'.
    - replace ((0 <=? s10_val str) && (s10_val str <? 48)) with false;
        [cbv iota | symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia].
      zstep. zstep.
      eapply REF.
      + unfold REFUSE_OUT_OF_RANGE. lia.
      + unfold parse_cell. rewrite Estr, EK. rewrite (proj2 (Z.ltb_lt _ _) V0). reflexivity.
      + exact (pk_merge_w _ _ _ _ _ _ _ _ (pk_merge_vw _ _ _ _ _ _ FR')).
      + exact ST'.
      + exact MU'.
      + exact OB'.
      + exact EV'.
      + exact WM'.
      + exact MI'. }
  destruct pk_nonul_lit as (NLph & NLpa & NLse).
  (* 0x14ae8-0x14afc: ch = c, name = dot + 1, strcmp(name, "phantom") *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSCMP with (sx := sx) (sy := NAME_PHANTOM).
    - rewrite unsigned_lit by lia. exact BN.
    - exact HxN.
    - rewrite unsigned_lit by lia. exact (proj1 (proj2 (lits_at m0 MI))).
    - exact NLph. }
  intros ms' (rr & r11 & r12 & r13 & E & IFF). subst ms'. pk_ret.
  (* 0x14b00-0x14b08: bound = 2, name == "phantom" *)
  zstep. zstep. zstep.
  destruct (bv_eqb rr (Z_to_bv 64 0)) eqn:ER; cbv iota.
  { apply pk_word0 in ER. pose proof (proj1 IFF ER) as Ex. subst rr.
    eapply TAIL with (p := HA_PHANTOM).
    - unfold param_of_name. rewrite (proj2 (bytes_eqb_eq sx NAME_PHANTOM) Ex). reflexivity.
    - exact FR.
    - exact ST.
    - exact MU1.
    - exact OB.
    - eexists. exact EV.
    - exact WM.
    - exact MI. }
  pose proof (pk_word_ne rr _ IFF ER) as NEph.
  assert (Bph : bytes_eqb sx NAME_PHANTOM = false).
  { destruct (bytes_eqb sx NAME_PHANTOM) eqn:X; [apply bytes_eqb_eq in X; contradiction | reflexivity]. }
  (* 0x14b0c-0x14b1c: strcmp(name, "pad") *)
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSCMP with (sx := sx) (sy := NAME_PAD).
    - rewrite unsigned_lit by lia. exact BN.
    - exact HxN.
    - rewrite unsigned_lit by lia. exact (proj1 (proj2 (proj2 (lits_at _ MI)))).
    - exact NLpa. }
  intros ms' (rr2 & q11 & q12 & q13 & E2 & IFF2). subst ms'. pk_ret.
  zstep.
  destruct (bv_eqb rr2 (Z_to_bv 64 0)) eqn:ER2; cbv iota.
  { apply pk_word0 in ER2. pose proof (proj1 IFF2 ER2) as Ex2.
    zstep.
    eapply TAIL with (p := HA_PAD).
    - unfold param_of_name. rewrite Bph, (proj2 (bytes_eqb_eq sx NAME_PAD) Ex2). reflexivity.
    - exact FR.
    - exact ST.
    - exact MU1.
    - exact OB.
    - eexists. exact EV.
    - exact WM.
    - exact MI. }
  pose proof (pk_word_ne rr2 _ IFF2 ER2) as NEpa.
  assert (Bpa : bytes_eqb sx NAME_PAD = false).
  { destruct (bytes_eqb sx NAME_PAD) eqn:X; [apply bytes_eqb_eq in X; contradiction | reflexivity]. }
  (* 0x14b20-0x14b30: strcmp(name, "sens") *)
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSCMP with (sx := sx) (sy := NAME_SENS).
    - rewrite unsigned_lit by lia. exact BN.
    - exact HxN.
    - rewrite unsigned_lit by lia. exact (proj2 (proj2 (proj2 (lits_at _ MI)))).
    - exact NLse. }
  intros ms' (rr3 & u11 & u12 & u13 & E3 & IFF3). subst ms'. pk_ret.
  zstep.
  destruct (bv_eqb rr3 (Z_to_bv 64 0)) eqn:ER3; cbn [negb]; cbv iota.
  { apply pk_word0 in ER3. pose proof (proj1 IFF3 ER3) as Ex3.
    (* 0x14b34-0x14b40: param = SENS, bound = 0x38 *)
    zstep. zstep. zstep. zstep.
    eapply TAIL with (p := HA_SENS).
    - unfold param_of_name. rewrite Bph, Bpa, (proj2 (bytes_eqb_eq sx NAME_SENS) Ex3). reflexivity.
    - exact FR.
    - exact ST.
    - exact MU1.
    - exact OB.
    - eexists. exact EV.
    - exact WM.
    - exact MI. }
  pose proof (pk_word_ne rr3 _ IFF3 ER3) as NEse.
  assert (Bse : bytes_eqb sx NAME_SENS = false).
  { destruct (bytes_eqb sx NAME_SENS) eqn:X; [apply bytes_eqb_eq in X; contradiction | reflexivity]. }
  (* no param: BAD_KEY *)
  eapply REF.
  - unfold REFUSE_BAD_KEY. lia.
  - unfold parse_cell. rewrite Estr, EK.
    replace (param_of_name sx) with (@None Z) by (unfold param_of_name; rewrite Bph, Bpa, Bse; reflexivity).
    reflexivity.
  - exact (pk_merge_w _ _ _ _ _ _ _ _ (pk_merge_vw _ _ _ _ _ _ FR)).
  - exact ST.
  - exact MU1.
  - exact OB.
  - eexists. exact EV.
  - exact WM.
  - exact MI.
Qed.

End PK.

Lemma pk_key : strtol_contract -> strcmp_contract -> forall c, pc_ok c -> S_VALUE c -> S_REFUSE c -> S_KEY c.
Proof.
  intros HSTL HSCMP c HC HV HRF.
  destruct c as [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mi lo P O cap R bs ev can].
  eapply pk_key_sec; eassumption.
Qed.
