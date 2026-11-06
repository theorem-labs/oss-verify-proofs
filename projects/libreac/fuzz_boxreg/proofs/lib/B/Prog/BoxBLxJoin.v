(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module paths and module names changed; 1025 of its 1105 lines of code are new or changed and 900 lines of the source are left out. *)
(* The phase JOIN of the walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (BoxBLxDefs.v's cuts): from the cut
   LP_K (0x80b08, the case of turn i is done) to the next loop head LP_J (0x80258, turn i + 1) or, after the 64th turn,
   to LP_X (0x80e54). The code:
   - 0x80b08 .. 0x80b10: check (r, fabric) (lh_check: bs' passes Pau's checks, boxreg_B16 from boxreg_inv);
   - 0x80b14 .. 0x80c48: check_kept (r, &prev, renamed), inlined: n = prev.n (lw 0x118(s5)); for each row j < n the
     UBSan tests (j = 6 and the pointer overflow of prev + 56 j and r + 56 j: refuted by the block and frame laws),
     the ASan checks of prev's and r's base / nch / pinned words (the registry block's shadow, prev's shadow in
     LSH_iter), the comparisons of the three words (equal by lkept), bcmp (prev.mac, ZERO, 6) (0x80c10) and, when that
     is not 0, bcmp (prev.mac, r.mac, 6) (0x80c24) (equal by lkept: a bound MAC stays), and, when j <> renamed,
     strncmp (prev.name, r.name, 32) (0x80c3c) (equal names by lkept); every abort (0x80fa4) is refuted;
   - 0x80cb0 .. 0x80d58: mac and prev out of scope again (LSH_entry), s8 = i + 1 (ld 0x58(s1); addiw), s3 = 1, and
     `bne s8, 64` to the loop head, else 0x80e54.
   The model facts are Pau's (lib/Prog/Boxreg.v rd4, bsub, boxreg_B6), used as they are. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC45 YC85 BoxBLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Bytes Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the registry's words and strings, as the walk reads them ---- *)

(* The unsigned value of the 4 bytes of bs at k (the chunk a lw reads): rd4 bs k = bv_swrap 32 (lu4 bs k). *)
Definition lu4 (bs : list byte) (k : Z) : Z := bytes_le_to_Z (Boxreg.bsub bs k 4).

Lemma lj_bsub_len : forall (bs : list byte) k n, (length (Boxreg.bsub bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold Boxreg.bsub. rewrite length_firstn. lia. Qed.

Lemma lu4_range : forall bs k, 0 <= lu4 bs k < 2 ^ 32.
Proof.
  intros bs k. unfold lu4. pose proof (YK11.bytes_le_to_Z_nonneg (Boxreg.bsub bs k 4)) as H0.
  pose proof (YK11.bytes_le_to_Z_bound (Boxreg.bsub bs k 4)) as H1.
  pose proof (lj_bsub_len bs k 4) as H2. change (Z.to_nat 4) with 4%nat in H2.
  split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma rd4_lu4 : forall bs k, Boxreg.rd4 bs k = bv_swrap 32 (lu4 bs k).
Proof. reflexivity. Qed.

Lemma lj_swrap32 : forall x, 0 <= x < 2 ^ 32 -> bv_swrap 32 x = if x <? 2 ^ 31 then x else x - 2 ^ 32.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  destruct (Z.ltb_spec x (2 ^ 31)); Z.div_mod_to_equations; lia.
Qed.

Lemma lu4_mod : forall bs k, lu4 bs k = Boxreg.rd4 bs k mod 2 ^ 32.
Proof.
  intros bs k. rewrite rd4_lu4. pose proof (lu4_range bs k) as R. rewrite lj_swrap32 by exact R.
  destruct (Z.ltb_spec (lu4 bs k) (2 ^ 31)).
  - rewrite Z.mod_small by lia. reflexivity.
  - replace (lu4 bs k - 2 ^ 32) with (lu4 bs k + (-1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma lu4_of_rd4 : forall bs bs' k, Boxreg.rd4 bs k = Boxreg.rd4 bs' k -> lu4 bs k = lu4 bs' k.
Proof. intros bs bs' k H. rewrite !lu4_mod, H. reflexivity. Qed.

(* A byte of a little-endian value. *)
Lemma lj_le_byte_nth : forall (l : list byte) (t : nat), (t < length l)%nat ->
  Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat t) mod 256 = bv_unsigned (nth t l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros t Ht; cbn [length] in Ht; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (YK11.bytes_le_to_Z_nonneg l) as Hl.
  cbn [bytes_le_to_Z]. rewrite Bytes.lor_shiftl8_add by lia.
  destruct t as [|t].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. Z.div_mod_to_equations. lia.
  - cbn [nth]. rewrite <- (IH t) by lia.
    rewrite !Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat (S t)) with (8 + 8 * Z.of_nat t) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l); [reflexivity|].
    Z.div_mod_to_equations. lia.
Qed.

Lemma lj_nth_bsub : forall (bs : list byte) k n t d, 0 <= k -> (t < Z.to_nat n)%nat ->
  nth t (Boxreg.bsub bs k n) d = nth (Z.to_nat k + t) bs d.
Proof.
  intros bs k n t d Hk Ht. unfold Boxreg.bsub. revert t Ht.
  generalize (Z.to_nat n) as m. generalize (Z.to_nat k) as p. clear.
  intros p m t Ht. revert bs t m Ht. induction p as [|p IH]; intros bs t m Ht.
  - cbn [skipn Nat.add]. revert t m Ht. induction bs as [|x bs IHb]; intros t m Ht.
    + destruct m; cbn; destruct t; reflexivity.
    + destruct m as [|m]; [lia|]. destruct t as [|t]; cbn [firstn nth]; [reflexivity|]. apply IHb. lia.
  - destruct bs as [|x bs]; cbn [skipn].
    + destruct m; cbn; destruct t; reflexivity.
    + replace (S p + t)%nat with (S (p + t)) by lia. cbn [nth]. apply IH. exact Ht.
Qed.

Lemma lj_bsub_len_eq : forall (bs : list byte) k n, 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length bs) ->
  length (Boxreg.bsub bs k n) = Z.to_nat n.
Proof. intros bs k n Hk Hn H. apply Boxreg.bsub_length; lia. Qed.

(* The bytes a view shows of bs at a, as the 4-byte value a lw reads at a + k. *)
Lemma lu4_val_mem : forall segs (H : word -> bool) mem a (bs : list byte) k,
  0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  (forall t, 0 <= t < 4 -> aview segs H mem (a + k + t) = Some (bv_unsigned (nth (Z.to_nat (k + t)) bs (Z_to_bv 8 0)))) ->
  val_mem segs (mrestrict H mem) (a + k) 4 (lu4 bs k).
Proof.
  intros segs H mem a bs k Hk Hlen HV t Ht.
  pose proof (HV (Z.of_nat t) ltac:(lia)) as Hv.
  unfold aview in Hv. destruct (mbyte segs (mrestrict H mem) (a + k + Z.of_nat t)) as [b|] eqn:Hb; [|discriminate].
  cbn [option_map] in Hv. injection Hv as Hv.
  f_equal. apply bv_eq. rewrite Hv, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. pose proof (lu4_range bs k) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite (Z.mod_small (lu4 bs k)) by exact R. rewrite Z.mod_mod by lia.
  unfold lu4. rewrite lj_le_byte_nth by (rewrite lj_bsub_len_eq by lia; cbn; lia).
  rewrite lj_nth_bsub by (cbn; lia). f_equal. f_equal. lia.
Qed.

(* lw sign-extends: the 64-bit value of the word is rd4. *)
Lemma lu4_sext : forall bs k, sext 64 (bv_extract 0 32 (Z_to_bv 64 (lu4 bs k))) = Z_to_bv 64 (Boxreg.rd4 bs k).
Proof.
  intros bs k. pose proof (lu4_range bs k) as R. rewrite Mem.sext_small. f_equal.
  rewrite Mem.signed_of_extract by lia. rewrite rd4_lu4. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

(* The kept rows: the three words of row j are the same in prev (bs) and in r (bs'). *)
Lemma lkept_words : forall bs bs' ren j, lkept bs bs' ren -> 0 <= j < Boxreg.bx_n bs ->
  lu4 bs' (56 * j + 8) = lu4 bs (56 * j + 8) /\ lu4 bs' (56 * j + 12) = lu4 bs (56 * j + 12) /\
  lu4 bs' (56 * j + 20) = lu4 bs (56 * j + 20).
Proof.
  intros bs bs' ren j HK Hj. destruct (HK j Hj) as (E1 & E2 & E3 & _).
  unfold Boxreg.bx_base, Boxreg.bx_nch, Boxreg.bx_pinned in E1, E2, E3.
  split; [|split]; apply lu4_of_rd4; assumption.
Qed.

(* A byte of row j's MAC or name is a byte of bs. *)
Lemma lj_mac_nth : forall bs j i d, 0 <= j -> 0 <= i < 6 ->
  nth (Z.to_nat i) (Boxreg.bx_mac bs j) d = nth (Z.to_nat (56 * j + i)) bs d.
Proof.
  intros bs j i d Hj Hi. unfold Boxreg.bx_mac. rewrite lj_nth_bsub by (cbn; lia). f_equal. lia.
Qed.
Lemma lj_name_nth : forall bs j i d, 0 <= j -> 0 <= i < 32 ->
  nth (Z.to_nat i) (Boxreg.bx_name bs j) d = nth (Z.to_nat (56 * j + 24 + i)) bs d.
Proof.
  intros bs j i d Hj Hi. unfold Boxreg.bx_name. rewrite lj_nth_bsub by (cbn; lia). f_equal. lia.
Qed.
Lemma lj_mac_eq : forall bs bs' j i d, 0 <= j -> 0 <= i < 6 -> Boxreg.bx_mac bs' j = Boxreg.bx_mac bs j ->
  nth (Z.to_nat (56 * j + i)) bs' d = nth (Z.to_nat (56 * j + i)) bs d.
Proof. intros bs bs' j i d Hj Hi E. rewrite <- !lj_mac_nth by lia. rewrite E. reflexivity. Qed.
Lemma lj_mac_zero : forall bs j i, 0 <= j -> 0 <= i < 6 -> Boxreg.bx_mac bs j = Boxreg.zero6 ->
  nth (Z.to_nat (56 * j + i)) bs (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros bs j i Hj Hi E. rewrite <- lj_mac_nth by lia. rewrite E. unfold Boxreg.zero6. apply nth_repeat.
Qed.
(* A MAC whose six bytes are 0 is zero6. *)
Lemma lj_mac_zero_of : forall bs j, 0 <= j -> 56 * j + 6 <= Z.of_nat (length bs) ->
  (forall i, 0 <= i < 6 -> bv_unsigned (nth (Z.to_nat (56 * j + i)) bs (Z_to_bv 8 0)) = 0) ->
  Boxreg.bx_mac bs j = Boxreg.zero6.
Proof.
  intros bs j Hj Hl HZ. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  - unfold Boxreg.zero6. rewrite repeat_length. unfold Boxreg.bx_mac. rewrite lj_bsub_len_eq by lia. reflexivity.
  - intros t Ht. unfold Boxreg.bx_mac in Ht. rewrite lj_bsub_len_eq in Ht by lia. change (Z.to_nat 6) with 6%nat in Ht.
    unfold Boxreg.zero6. rewrite nth_repeat.
    replace t with (Z.to_nat (Z.of_nat t)) by lia. rewrite lj_mac_nth by lia.
    apply bv_eq. rewrite (HZ (Z.of_nat t)) by lia. reflexivity.
Qed.

(* The C string a 32-byte name field holds: its bytes before the first NUL. *)
Fixpoint lj_cpre (l : list Z) : list Z :=
  match l with [] => [] | c :: t => if c =? 0 then [] else c :: lj_cpre t end.
Lemma lj_cpre_prefix : forall l, In 0 l -> exists rest, l = lj_cpre l ++ 0 :: rest.
Proof.
  induction l as [|c t IH]; intros Hin; [destruct Hin|]. cbn [lj_cpre].
  destruct (Z.eqb_spec c 0) as [-> | Hc].
  - exists t. reflexivity.
  - destruct Hin as [-> | Hin]; [contradiction|]. destruct (IH Hin) as (rest & E). exists rest.
    cbn [app]. rewrite <- E. reflexivity.
Qed.
Lemma lj_cpre_nz : forall l, Forall (fun c => c <> 0) (lj_cpre l).
Proof.
  induction l as [|c t IH]; cbn [lj_cpre]; [constructor|].
  destruct (Z.eqb_spec c 0); [constructor | constructor; [exact n | exact IH]].
Qed.
Lemma lj_cpre_len : forall l, In 0 l -> (length (lj_cpre l) < length l)%nat.
Proof.
  intros l Hin. destruct (lj_cpre_prefix l Hin) as (rest & E).
  rewrite E at 2. rewrite length_app. cbn [length]. lia.
Qed.
Lemma lj_cpre_nth : forall l t, In 0 l -> (t <= length (lj_cpre l))%nat ->
  nth t (lj_cpre l ++ [0]) 0 = nth t l 0.
Proof.
  intros l t Hin Ht. destruct (lj_cpre_prefix l Hin) as (rest & E).
  rewrite E at 2. replace (lj_cpre l ++ 0 :: rest) with ((lj_cpre l ++ [0]) ++ rest) by (rewrite <- app_assoc; reflexivity).
  rewrite (app_nth1 (lj_cpre l ++ [0]) rest); [reflexivity|]. rewrite length_app. cbn [length]. lia.
Qed.
(* The name of row j as the strncmp contract states a string. *)
Definition lname (bs : list byte) (j : Z) : list Z :=
  lj_cpre (map (fun b : byte => bv_unsigned b) (Boxreg.bx_name bs j)).
Lemma lname_nul : forall bs j, In (Z_to_bv 8 0) (Boxreg.bx_name bs j) ->
  In 0 (map (fun b : byte => bv_unsigned b) (Boxreg.bx_name bs j)).
Proof. intros bs j H. change 0 with ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0)). apply in_map. exact H. Qed.
Lemma lname_len : forall bs j, 0 <= j -> 56 * j + 56 <= Z.of_nat (length bs) ->
  In (Z_to_bv 8 0) (Boxreg.bx_name bs j) -> (length (lname bs j) < 32)%nat.
Proof.
  intros bs j Hj Hl Hn. unfold lname. pose proof (lj_cpre_len _ (lname_nul bs j Hn)) as H.
  rewrite length_map in H. unfold Boxreg.bx_name in H. rewrite lj_bsub_len_eq in H by lia. exact H.
Qed.
Lemma lname_eq : forall bs bs' j, Boxreg.bx_name bs' j = Boxreg.bx_name bs j -> lname bs' j = lname bs j.
Proof. intros bs bs' j E. unfold lname. rewrite E. reflexivity. Qed.
(* The bytes of the string with its NUL are bytes of the field. *)
Lemma lname_nth : forall bs j t, 0 <= j -> 56 * j + 56 <= Z.of_nat (length bs) ->
  In (Z_to_bv 8 0) (Boxreg.bx_name bs j) -> (t <= length (lname bs j))%nat ->
  nth t (lname bs j ++ [0]) 0 = bv_unsigned (nth (Z.to_nat (56 * j + 24 + Z.of_nat t)) bs (Z_to_bv 8 0)).
Proof.
  intros bs j t Hj Hl Hn Ht. pose proof (lname_len bs j Hj Hl Hn) as HL.
  assert (HN : length (Boxreg.bx_name bs j) = 32%nat)
    by (unfold Boxreg.bx_name; rewrite lj_bsub_len_eq by lia; reflexivity).
  assert (Ht32 : (t < 32)%nat) by lia.
  unfold lname in Ht |- *. rewrite lj_cpre_nth by (try exact (lname_nul bs j Hn); exact Ht).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, HN; exact Ht32).
  rewrite map_nth. replace t with (Z.to_nat (Z.of_nat t)) at 1 by lia. rewrite lj_name_nth by lia.
  reflexivity.
Qed.

(* renamed, as the code holds it in s8 (ren mod 2 ^ 32, times 56), against the row offset 56 j. *)
Lemma lj_ren_eq : forall ren j, -1 <= ren < 5 -> 0 <= j < 5 ->
  (56 * (ren mod 2 ^ 32) = 56 * j <-> j = ren).
Proof.
  intros ren j Hr Hj. destruct (Z.eq_dec ren (-1)) as [-> | Hn].
  - change ((-1) mod 2 ^ 32) with 4294967295. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the phase's own cuts ---- *)
(* Offsets in the listing: the head of check_kept's loop (0x80b44, s7 = 56 j) and the turn's end (0x80cb0). *)
Definition LP_L : Z := 0xb98.
Definition LP_E : Z := 0xd04.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.

(* 0x80b44, row j of check_kept's loop in turn i: as LI_K, after check (r still holds bs'), with s7 = 56 j,
   s8 = 56 (ren mod 2 ^ 32), s10 = 56 n (n = prev.n). *)
Definition LI_L (i : nat) (j : Z) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab ren : Z) (bs bs' : list byte),
  lx_body cx fp LP_L W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 3 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT /\
  lblk B cx ly3 S3 r /\ lprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\ Boxreg.bx_fabric bs = fab /\
  lreg W3 ms3 r bs' /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = fab /\ lkept bs bs' ren /\
  -1 <= ren < Boxreg.bx_n bs /\ 0 <= j < Boxreg.bx_n bs /\
  lcur cx W3 ms3 pos /\ lslots_loop cx fp W3 ms3 r fab /\ lslot cx W3 ms3 0x58 (Z.of_nat i) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\
  getr (ms_regs ms3) 23 = w64 (56 * j) /\ getr (ms_regs ms3) 24 = w64 (56 * (ren mod 2 ^ 32)) /\
  getr (ms_regs ms3) 26 = w64 (56 * Boxreg.bx_n bs) /\ getr (ms_regs ms3) 27 = w64 fab.

(* 0x80cb0, turn i: check_kept is done; mac and prev go out of scope next. *)
Definition LI_E (i : nat) (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (pos : nat) (r fab : Z) (bs' : list byte),
  lx_body cx fp LP_E W3 ms3 LSH_iter /\ (i < 64)%nat /\
  k <= 3 + 2 * Z.of_nat i /\ acc <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT /\
  lblk B cx ly3 S3 r /\ lreg W3 ms3 r bs' /\ Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = fab /\
  lcur cx W3 ms3 pos /\ lslots_loop cx fp W3 ms3 r fab /\ lslot cx W3 ms3 0x58 (Z.of_nat i) /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) /\ getr (ms_regs ms3) 27 = w64 fab.

Hypothesis HY : lx_hyps B MT.

(* ---- strncmp (0x80c3c), in the caller's journal (YCbq.v aj_bcmp_at's form) ---- *)
(* Its read-only premises: abfm_rom_viewN from arodata_okP at the call (BoxBLxDefs.v lx_rom_viewN), abfm_rom_viewO
   from AR at the call and BLxLib's blx_pinned (lx_rom_viewO). *)
Lemma lj_strncmp_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw l1 l2,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memT) ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  abfm_cstr_ok SEGS W memT x l1 -> abfm_cstr_ok SEGS W memT y l2 ->
  SRr SEGS W (mkCfg (YK11.mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_strncmp)) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 v,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 v /\
       (v = 0 <-> abfm_strn_eq (Z.to_nat n) l1 l2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
  intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw l1 l2
    HJ HRO Ha0 Ha1 Ha2 Hn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hx Hy.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HPRE : abfm_ecall_pre_k SEGS B ABFM_STK_RT_STR lyc Sc W regsT memT mdc).
  { split; [eapply ecall_pre_at with (o := o); try eassumption; [lia | rewrite Hra; exact Hraw]|].
    unfold ABFM_STK_RT_STR, ASAN_CEIL. rewrite Eslo, Hsp'.
    split; [lia|]. split; [lia|]. intros a Ha. apply Hpres. lia. }
  pose proof (lx_rom_viewN B W memT HRO) as HRVN.
  pose proof (lx_rom_viewO B lyc Sc W memT mdc (blx_pinned _ (lh_glob B MT HY)) HAR) as HRVO.
  eapply SRr_mono.
  { exact (lh_strncmp B MT HY lyc Sc W regsT memT mdc x y n l1 l2 HPRE HRVN HRVO Ha0 Ha1 Ha2 Hn Hx Hy). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hv & HR & Hfr & Hpres2).
  unfold ABFM_STK_RT_STR in Hfr. rewrite Hsp' in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2, v.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split.
  { eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
      (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
    - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
    - exact Hpres2.
    - exact Hsame.
    - intros a Ha; left; left; lia.
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact HR|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ---- helpers of the walks ---- *)
Lemma lj_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
  destruct H1 as [H1 H1']. split; [exact H1 | exact (IH l2 H1' H2)].
Qed.

(* A region the walk does not write: its window is closed (set_window r 0 0). *)
Lemma lj_unwin : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  regions_wf (list_upd (ss_mem ss) i (set_window r 0 0)) = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) i (set_window r 0 0)) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms i r HS Hn Hw. apply (ast_ok_pi_set_region E ss ms i r); [exact HS | exact Hn | | exact Hw |].
  - destruct r. reflexivity.
  - apply region_ok_rewindow; [exact (st_ok_pi_region_nth E ss ms i r HS Hn) | intros o Ho; lia].
Qed.

(* An empty window list: a run writes no byte. *)
Lemma lj_awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs. induction rs as [|r rs IH]; intros STK sp0 FP bl0 blc ly own H; [apply awr_ok_nil|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  apply awr_ok_cons_ro; [exact H1 | exact (IH _ _ _ _ _ _ _ H2)].
Qed.


(* A run whose regions all have closed windows writes no byte. *)
Lemma lj_frame_ro : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
  intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
  rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.
Lemma lj_aview_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF Hw a. unfold aview, mbyte. rewrite (lj_frame_ro E rs _ _ HF Hw). reflexivity.
Qed.

(* A region with a closed window is kept when the bytes of its extent are. *)
Lemma lj_rkept : forall E (H : word -> bool) (m m' : word -> option byte) r,
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     aview SEGS H m' a = aview SEGS H m a) ->
  YP09.r_whi r <= YP09.r_wlo r ->
  region_kept SEGS E (mrestrict H m) (mrestrict H m') r.
Proof.
  intros E H m m' r Hk Hw. split; intros a Ha; [|lia].
  apply (mbyte_of_aview SEGS). apply Hk. exact Ha.
Qed.

Lemma lj_mod16_8 : forall z, z mod 16 = 0 -> z mod 8 = 0.
Proof.
  intros z H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
  destruct H as [q Hq]. exists (2 * q). lia.
Qed.
Lemma lj_sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
  destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

(* The callee chain at the realigned stack pointer (BoxBLxDefs.v lx_achain) through the phase's layout. *)
Lemma lj_achain : forall cx k ly3 S3 W3 mem md3 own sp',
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) own ly3 S3 W3 mem md3 k ->
  rdword (aview SEGS (w_H W3) mem) (lsp0 cx - 8) = Some (raZ (lc_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (lsp0 cx - 16) = Some (s0Z (lc_regs cx)) ->
  sp' + 16 <= lsp0 cx ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (lsp0 cx) (lch cx).
Proof.
  intros cx k ly3 S3 W3 mem md3 own sp' HB HJ H8 H16 Hsp.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop2 & Htop).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  apply (achain_ly_top (lc_ly cx) ly3 _ _ _ _ Etop).
  eapply lx_achain; [exact Hch | lia | unfold lsp0, LX_STK in *; lia | exact (lj_mod16_8 _ Hal16) | exact Hra4 | | exact H8 | exact H16 | exact Hsp].
  intros a Ha. apply F1; unfold lsp0, LX_STK in *; lia.
Qed.

(* ZERO's shadow (lh_glob: its cells are constants of AR). *)
Lemma lj_globs_zero : globs_marked SEGS B [(VAL (A_OBJ 4), 6)].
Proof.
  intros ly S W mem md q sz Hin HAR. destruct Hin as [Eq | []]. injection Eq as <- <-.
  pose proof (lh_glob B MT HY) as GL.
  pose proof (blx_al _ GL (4%nat, 6) ltac:(cbn; left; reflexivity)) as Hal. cbn [fst] in Hal.
  unfold block_shadow. split.
  { apply Z.mod_divide in Hal; [|lia]. apply Z.mod_divide; [lia|]. destruct Hal as [x Hx]. exists (4 * x). lia. }
  split; [lia|]. intros i Hi. change ((6 + 7) / 8) with 1 in Hi. assert (i = 0) as -> by lia.
  change (0 <? 6 / 8) with false. cbv iota. change (6 mod 8) with 6. rewrite Z.add_0_r.
  destruct HAR as (M & _).
  pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
  specialize (C (z1 (ANum (shadow_addr (VAL (A_OBJ 4)))) 6)
    (blx_cells _ GL ly _ ltac:(unfold lx_glob_cells; cbn [flat_map LX_GLOBS fst snd]; left; reflexivity))).
  specialize (C 0%nat ltac:(cbn; lia)). cbn [aeval c_at c_val c_w z1 c1] in C. rewrite Z.add_0_r in C.
  unfold shadow_of_addr. unfold shadow_addr in C. rewrite C. reflexivity.
Qed.

(* A memory that shows every byte as before keeps the phase's facts. *)
Lemma lj_keep_eq : forall cx fp (W3 : world SEGS) rs (m m' : word -> option byte),
  (forall a, aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> lx_keep cx fp W3 rs m m'.
Proof. intros cx fp W3 rs m m' H a _. exact (H a). Qed.

(* The value of an atom (plus an offset) as a word. *)
Lemma lj_den_atom : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof.
  intros E n v c H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity.
Qed.

(* blez a0 (0x80b18) with a0 = prev.n (atom 48, 0 .. 5). *)
Lemma lj_bge0 : forall E (m : nat) n, ew E m = w64 n -> 0 <= n <= 5 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff m 0)) = (n =? 0).
Proof.
  intros E m n H Hn. rewrite (lj_den_atom E m n 0 H ltac:(lia)), Z.add_0_r.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5) as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] by lia;
  vm_compute; reflexivity.
Qed.

(* s8 at the loop head: 56 (ren mod 2 ^ 32) (the engine's SMd M_MUL of slli 6 - slli 3). *)
Lemma lj_s8 : forall E (m : nat) x, ew E m = w64 x -> 0 <= x < 2 ^ 32 ->
  sv_denot E (SMd M_MUL (SOff m 0) (SLit 56)) = w64 (56 * x).
Proof.
  intros E m x H Hx. rewrite denot_lit_U, U_SMd, (U_atom E m x H) by lia. rewrite U_SLit.
  unfold w64. f_equal. cbn [zmd_raw]. unfold zcanon, M64.
  rewrite (Z.mod_small 56) by lia. rewrite Z.mul_comm. apply Z.mod_small. lia.
Qed.

(* s10 at the loop head: 56 n (sgtz / neg / and / slli 6 - slli 3 of n = prev.n, 1 .. 5). *)
Lemma lj_s10 : forall E (m : nat) n, ew E m = w64 n -> 1 <= n <= 5 ->
  sv_denot E (SAlu ALU_SUB
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff m 0))) (SOff m 0)) (SLit 6))
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff m 0))) (SOff m 0)) (SLit 3)))
  = w64 (56 * n).
Proof.
  intros E m n H Hn. cbn [sv_denot]. rewrite !H.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5) as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] by lia;
  vm_compute; reflexivity.
Qed.

(* An address of the application's memory is no shadow byte of the frame (YC1h.v fshadow_not_app). *)
Lemma lj_app_nsh : forall (F p n a : Z), 4096 <= F -> F + 512 <= alloc_ceiling -> in_app p n ->
  p <= a < p + n -> ~ (shadow_addr F <= a < shadow_addr F + 64).
Proof.
  intros F p n a HF0 HFc Hin Ha Hsh.
  pose proof asan_consts as (C1 & _).
  apply (fshadow_not_app F 64 p n a HF0 ltac:(lia) Hin); [|exact Ha].
  unfold shadow_addr, SHADOW_OFF in Hsh. lia.
Qed.

(* A word of the application's memory across a run that wrote only the frame's shadow. *)
Lemma lj_nsh_rdword : forall (W3 : world SEGS) (F : Z) (m m' : word -> option byte) p n a v,
  (forall x, ~ (shadow_addr F <= bv_unsigned x < shadow_addr F + 64) -> m' x = m x) ->
  4096 <= F -> F + 512 <= alloc_ceiling -> in_app p n -> p <= a -> a + 8 <= p + n -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros W3 F m m' p n a v HM HF0 HFc Hin Hlo Hhi Ha0 Ha1 Hv.
  rewrite <- Hv. apply rdword_ext. intros j Hj. unfold aview, mbyte, mrestrict.
  rewrite HM; [reflexivity|]. rewrite unsigned_lit_small by lia.
  exact (lj_app_nsh F p n (a + j) HF0 HFc Hin ltac:(lia)).
Qed.
Lemma lj_nsh_byte : forall (W3 : world SEGS) (F : Z) (m m' : word -> option byte) p n a,
  (forall x, ~ (shadow_addr F <= bv_unsigned x < shadow_addr F + 64) -> m' x = m x) ->
  4096 <= F -> F + 512 <= alloc_ceiling -> in_app p n -> p <= a < p + n -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros W3 F m m' p n a HM HF0 HFc Hin Ha Ha0. unfold aview, mbyte, mrestrict.
  rewrite HM; [reflexivity|]. rewrite unsigned_lit_small by lia.
  exact (lj_app_nsh F p n a HF0 HFc Hin Ha).
Qed.
Lemma lj_nsh_above : forall (W3 : world SEGS) (F : Z) (m m' : word -> option byte) a v,
  (forall x, ~ (shadow_addr F <= bv_unsigned x < shadow_addr F + 64) -> m' x = m x) ->
  shadow_addr F + 64 <= a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros W3 F m m' a v HM Ha Ha0 Ha1 Hv. rewrite <- Hv. apply rdword_ext. intros j Hj.
  unfold aview, mbyte, mrestrict. rewrite HM; [reflexivity|]. rewrite unsigned_lit_small by lia. lia.
Qed.
Definition LX_SBX : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).

(* After a run with closed windows: the phase's facts extend to the run's memory (HKA : lx_keep .. m0 m). *)
Ltac lj_keep_run HKA :=
  lazymatch type of HKA with lx_keep ?cx ?fp ?W ?rs ?m0 ?m =>
  lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ m) (mrestrict _ ?m') |- _ =>
    let H := fresh "HKA" in
    assert (H : lx_keep cx fp W rs m0 m')
      by (eapply lx_keep_trans; [exact HKA | apply lj_keep_eq; exact (lj_aview_ro _ _ _ _ _ HFr0 ltac:(vm_compute; reflexivity))]);
    clear HKA; rename H into HKA;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end
  end end.
(* A register of the symbolic state, as the symbolic value it holds. *)
Ltac lj_reg HS r R :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R end.
(* A fact of the phase, from the cut's fact and the keep relation in the context. *)
Ltac lj_keepf0 L :=
  eapply L; try eassumption; try lia; try (left; reflexivity);
  try (unfold LSH_iter, LSH_entry; change (fs_frame_bytes LX_CID / 8) with 64; cbn [length app repeat]; lia).
Ltac lj_kf :=
  first [ solve [lj_keepf0 lx_saved_keep] | solve [lj_keepf0 lx_shadow_keep] | solve [lj_keepf0 lx_flag_keep]
        | solve [lj_keepf0 lx_slot_keep] | solve [lj_keepf0 lx_input_keep] | solve [lj_keepf0 lx_reg_keep]
        | solve [lj_keepf0 lx_prev_keep] | solve [lj_keepf0 lx_cur_keep] | solve [lj_keepf0 lx_slots_loop_keep] ].
(* lx_body at the landing state HS (registers from the symbolic state, the rest kept). *)
Ltac lj_land_body HS :=
  eapply lx_land; [eassumption | exact HS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf | lj_kf].

(* Close region i's window in the seat's state, and normalize the state. *)
Ltac lj_unwin_tac HS i :=
  let H := fresh "HSu" in
  pose proof (lj_unwin _ _ _ i _ HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)) as H;
  clear HS; rename H into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.

(* An address the phase's facts speak about (Seat's lx_keep_at), from the bounds in the context. *)
Ltac lj_keep_at_tac :=
  unfold lx_keep_at;
  first [ left; lia | right; left; lia | right; right; left; change (fs_frame_bytes LX_CID) with 512; lia
        | right; right; right; left; change (fs_frame_bytes LX_CID / 8) with 64; lia
        | right; right; right; right; apply Exists_cons_hd; cbn [fst snd]; unfold LX_REG; lia ].
(* After a call that kept the phase's facts (HK : lx_keep ...): the regions idxs survive (their windows are closed). *)
Ltac lj_reseat HS HP W3 mem2 HK idxs :=
  let K := run_K_hi HS in
  let HS2 := fresh "HS2" in
  lazymatch type of HP with aregs_preserved _ ?regs2 =>
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W3) mem2) HP idxs HS2 end;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in assert (HQ : Q);
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (apply lj_rkept; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
       [ let a := fresh "a" in let Ha := fresh "Ha" in
         intros a Ha; rewrite ?YN3v.ew_havoc_old in Ha by lia;
         repeat match goal with Hu : bv_unsigned (ew ?Ex ?n) = _ |- _ =>
           lazymatch type of Ha with context [bv_unsigned (ew Ex n)] => rewrite Hu in Ha end end;
         apply HK; lj_keep_at_tac
       | lia ])
    | specialize (HS2 HQ); clear HQ ] end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
(* After a call (havoc above K): the facts on the old atoms hold in the new environment (grant's restate). *)
Ltac lj_restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = v |- _ => fail
      | _ => let F' := fresh F in assert (F' : ew En n = v) by (rewrite OLD by lia; exact F); clear F; rename F' into F
      end
  | F : bv_unsigned (ew Eo ?n) = ?v |- _ =>
      lazymatch goal with
      | _ : bv_unsigned (ew En n) = v |- _ => fail
      | _ => let F' := fresh F in assert (F' : bv_unsigned (ew En n) = v) by (rewrite OLD by lia; exact F); clear F; rename F' into F
      end
  end end.
(* Name the environment after a call (havoc E K ws) and carry the old atoms' facts and lx_E into it. *)
Ltac lj_newenv HS E1 HE1 OLD :=
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
    remember (havoc Eo K ws) as E1 eqn:HE1 in HS;
    assert (OLD : forall q, (q < K)%nat -> ew E1 q = ew Eo q)
      by (let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq);
    let HEIn := fresh "HEI" in
    assert (HEIn : img_env VAL A_LIM E1)
      by (rewrite HE1; apply img_env_havoc_hi; [assumption | cbv; lia]);
    let HEn := fresh "HE" in
    lazymatch goal with HEo : lx_E ?cx ?fp Eo |- _ =>
      assert (HEn : lx_E cx fp E1)
        by (apply (lx_E_agree cx fp Eo E1 HEo); let n := fresh "n" in let Hn := fresh "Hn" in
            intros n Hn; apply OLD; unfold LA_EX in Hn; lia);
      clear HEo end;
    lj_restate OLD;
    repeat match goal with H : img_env _ _ Eo |- _ => clear H end
  end.

(* ---- the premises of check_kept's calls: bcmp (prev.mac, ZERO / r.mac, 6), strncmp (prev.name, r.name, 32) ---- *)

(* One byte of a view as a value of the memory. *)
Lemma lj_val_mem1 : forall (H : word -> bool) mem a v,
  aview SEGS H mem a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
  intros H mem a v Ha Hv q Hq. destruct q; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Ha. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; cbn [option_map] in Ha; [|discriminate].
  injection Ha as <-. f_equal.
  unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The end of the NUL's 8-byte word, for a string of length < 32 at an 8-aligned address. *)
Lemma lj_word_end : forall p L a, p mod 8 = 0 -> 0 <= L < 32 ->
  p + L < a < p + L - (p + L) mod 8 + 8 -> p <= a < p + 32.
Proof.
  intros p L a Hp HL Ha.
  assert (E : (p + L) mod 8 = L mod 8) by (rewrite Z.add_mod, Hp by lia; rewrite Z.add_0_l; apply Z.mod_mod; lia).
  rewrite E in Ha. pose proof (Z.div_mod L 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as M.
  assert (L / 8 < 4) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* The shadow of prev's bytes while a turn has prev in scope (Seat's lx_shent_frame). *)
Lemma lj_ra_prev : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k lo n,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lshadow cx fp W3 ms LSH_iter -> 64 <= lo -> 0 <= n -> lo + n <= 352 ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (lF cx fp + lo) n.
Proof.
  intros cx fp W3 ms ly3 S3 md3 k lo n HB HJ HFR HSH Hlo Hn Hhi.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & _).
  set (Ex := lx_env cx fp (ms_regs ms) []).
  assert (X32 : ew Ex 32 = w64 SHADOW_OFF) by exact (lx_env_x cx fp (ms_regs ms) [] 0 ltac:(lia)).
  assert (X46 : ew Ex 46 = w64 (lF cx fp)).
  { exact (eq_trans (lx_env_x cx fp (ms_regs ms) [] 14 ltac:(lia)) ltac:(unfold lx_xatoms, lx_sregs; reflexivity)). }
  assert (U32 : U Ex (SOff LA_SB 0) = SHADOW_OFF) by (apply (U_atom Ex 32 SHADOW_OFF X32); unfold SHADOW_OFF; lia).
  pose proof asan_consts as (C1 & _).
  assert (U46 : U Ex (SOff LA_F 0) = lF cx fp) by (apply (U_atom Ex 46 (lF cx fp) X46); lia).
  pose proof (lx_shent_frame B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR Ex lo (lo + n) U32 U46 HSH
    ltac:(right; lia)) as Hsh.
  unfold shent_ok in Hsh. cbn [she_m she_lo she_hi] in Hsh.
  first [destruct Hsh as [Hra _] | rename Hsh into Hra].
  unfold LA_SB, LA_F in Hra, U32, U46. rewrite U32, U46 in Hra. replace (lo + n - lo) with n in Hra by lia.
  rewrite (aview_rd_of SEGS). exact Hra.
Qed.

Lemma lj_bcmp_prev : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k bs j (regsT : bvmap 5 word),
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lprev cx fp W3 ms bs -> lshadow cx fp W3 ms LSH_iter -> 0 <= j < 5 -> spZ regsT = lsp1 cx ->
  src_ok SEGS W3 regsT (ms_mem ms) (lF cx fp + 64 + 56 * j) 6 /\
  (forall a, lF cx fp + 64 + 56 * j <= a < lF cx fp + 64 + 56 * j + 6 -> ~ (lsp1 cx - 2 * ESTACK <= a < lsp1 cx)) /\
  0 <= lF cx fp + 64 + 56 * j /\ lF cx fp + 64 + 56 * j + 6 <= 2 ^ 63 /\
  amem_range (lF cx fp + 64 + 56 * j) 6 /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (lF cx fp + 64 + 56 * j) 6 /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms)) (lF cx fp + 64 + 56 * j) 6.
Proof.
  intros cx fp W3 ms ly3 S3 md3 k bs j regsT HB HJ HFR HPV HSH Hj Hsp.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _).
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & _ & Hsp1 & _).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ) as HFA.
  pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
  assert (ESTACK = 4096) as Hes by reflexivity.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha. split.
    + unfold lprev, lview in HPV. replace a with (lF cx fp + 64 + (a - lF cx fp - 64)) by lia.
      rewrite HPV by (unfold LX_REG; lia). discriminate.
    + rewrite Hsp. lia.
  - intros a Ha. lia.
  - lia.
  - lia.
  - apply (amem_range_sub_app (lF cx fp) 512); [exact HFapp | lia | lia | lia | lia].
  - replace (lF cx fp + 64 + 56 * j) with (lF cx fp + (64 + 56 * j)) by lia.
    apply (lj_ra_prev cx fp W3 ms ly3 S3 md3 k); [exact HB | exact HJ | exact HFR | exact HSH | lia | lia | lia].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 LX_CID fp); [exact HAR | rewrite HFR; left; reflexivity | | | lia];
      rewrite HFA; change (fs_frame_bytes LX_CID) with 512; lia.
Qed.

Lemma lj_bcmp_reg : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k r bs' j (regsT : bvmap 5 word),
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  In (r, LX_REG) (ablocks B ly3 S3) -> lreg W3 ms r bs' -> 0 <= j < 5 -> spZ regsT = lsp1 cx ->
  src_ok SEGS W3 regsT (ms_mem ms) (r + 56 * j) 6 /\
  (forall a, r + 56 * j <= a < r + 56 * j + 6 -> ~ (lsp1 cx - 2 * ESTACK <= a < lsp1 cx)) /\
  0 <= r + 56 * j /\ r + 56 * j + 6 <= 2 ^ 63 /\
  amem_range (r + 56 * j) 6 /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (r + 56 * j) 6 /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms)) (r + 56 * j) 6.
Proof.
  intros cx fp W3 ms ly3 S3 md3 k r bs' j regsT HB HJ HrIn HRG Hj Hsp.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & _ & Hsp1 & _).
  pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size LX_REG) with 288 in Hrceil.
  assert (ESTACK = 4096) as Hes by reflexivity.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha. split.
    + unfold lreg, lview in HRG. replace a with (r + (a - r)) by lia.
      rewrite HRG by (unfold LX_REG; lia). discriminate.
    + rewrite Hsp. lia.
  - intros a Ha. lia.
  - lia.
  - lia.
  - eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HrIn); change (req_size LX_REG) with 288; lia.
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HrIn); change (req_size LX_REG) with 288; lia.
  - eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HrIn); change (req_size LX_REG) with 288; lia.
Qed.

Lemma lj_bcmp_zero : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k (regsT : bvmap 5 word),
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  spZ regsT = lsp1 cx ->
  src_ok SEGS W3 regsT (ms_mem ms) (VAL (A_OBJ 4)) 6 /\
  (forall a, VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 6 -> ~ (lsp1 cx - 2 * ESTACK <= a < lsp1 cx)) /\
  0 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 6 <= 2 ^ 63 /\
  amem_range (VAL (A_OBJ 4)) 6 /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (VAL (A_OBJ 4)) 6 /\
  shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms)) (VAL (A_OBJ 4)) 6 /\
  (forall i, 0 <= i < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 4) + i) = Some 0).
Proof.
  intros cx fp W3 ms ly3 S3 md3 k regsT HB HJ Hsp.
  pose proof (lh_laws B MT HY) as LAWS. pose proof (lh_glob B MT HY) as GL.
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & _ & Hsp1 & _).
  pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
  assert (HRO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
    by (eapply lx_arodata_kept; [exact HJ | exact HRO0]).
  pose proof (lx_absn_rom_kept B W3 (ms_mem ms) HRO) as HRK.
  pose proof (blx_marg _ GL (4%nat, 6) ltac:(cbn; left; reflexivity)) as (HM1 & HM2). cbn [fst snd] in HM1, HM2.
  unfold IMG_HI in HM2.
  pose proof (blx_rom_bytes _ GL (4%nat, [0; 0; 0; 0; 0; 0]) ltac:(cbn; left; reflexivity)) as HZB. cbn [fst snd] in HZB.
  assert (ESTACK = 4096) as Hes by reflexivity.
  assert (HZ : forall i, 0 <= i < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 4) + i) = Some 0).
  { intros i Hi. destruct (HZB i ltac:(cbn; lia)) as (Hrom & Hown & Herr & Hb).
    rewrite (HRK _ Hrom Hown Herr), Hb.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] by lia;
    reflexivity. }
  assert (HM2' : VAL (A_OBJ 4) + 6 + 64 <= IMG_HI) by (unfold IMG_HI; lia).
  destruct (ro_read_ok_glob SEGS B [(VAL (A_OBJ 4), 6)] ly3 S3 W3 (ms_mem ms) md3 (VAL (A_OBJ 4)) 6 (VAL (A_OBJ 4)) 6
    lj_globs_zero ltac:(left; reflexivity) (blx_isv _ GL) HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HM2')
    as [HRA HHV].
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros a Ha. split.
    + replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia. rewrite HZ by lia. discriminate.
    + rewrite Hsp. lia.
  - intros a Ha. lia.
  - lia.
  - lia.
  - unfold amem_range, kLowMemEnd. left. lia.
  - exact HRA.
  - exact HHV.
  - exact HZ.
Qed.

Lemma lj_cstr_prev : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k bs j,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lprev cx fp W3 ms bs -> lshadow cx fp W3 ms LSH_iter -> length bs = 288%nat -> 0 <= j < 5 ->
  In (Z_to_bv 8 0) (Boxreg.bx_name bs j) ->
  abfm_cstr_ok SEGS W3 (ms_mem ms) (lF cx fp + 64 + 56 * j + 24) (lname bs j).
Proof.
  intros cx fp W3 ms ly3 S3 md3 k bs j HB HJ HFR HPV HSH HL Hj Hn.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HF64 & _).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 md3 k HB HJ) as HFA.
  pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
  pose proof (lname_len bs j ltac:(lia) ltac:(rewrite HL; lia) Hn) as HLn.
  set (L := Z.of_nat (length (lname bs j))) in *.
  assert (HL32 : 0 <= L < 32) by (unfold L; lia).
  assert (HP8 : (lF cx fp + 64 + 56 * j + 24) mod 8 = 0).
  { apply Z.mod_divide in HF64; [|lia]. apply Z.mod_divide; [lia|]. destruct HF64 as [q Hq]. exists (8 * q + 8 + 7 * j + 3). lia. }
  unfold abfm_cstr_ok, abfm_cstr. fold L.
  split; [split|].
  { intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    rewrite (lname_nth bs j t ltac:(lia) ltac:(rewrite HL; lia) Hn ltac:(lia)).
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (56 * j + 24 + Z.of_nat t)) bs (Z_to_bv 8 0))) as R.
    change (bv_modulus 8) with 256 in R.
    split; [|exact R]. apply lj_val_mem1; [|exact R].
    unfold lprev, lview in HPV. replace (lF cx fp + 64 + 56 * j + 24 + Z.of_nat t) with (lF cx fp + 64 + (56 * j + 24 + Z.of_nat t)) by lia.
    apply HPV. unfold LX_REG, L in *. lia. }
  { apply lj_cpre_nz. }
  split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
  split; [apply (amem_range_sub_app (lF cx fp) 512); [exact HFapp | lia | lia | lia | lia]|].
  split.
  { replace (lF cx fp + 64 + 56 * j + 24) with (lF cx fp + (88 + 56 * j)) by lia.
    apply (lj_ra_prev cx fp W3 ms ly3 S3 md3 k); [exact HB | exact HJ | exact HFR | exact HSH | lia | lia | lia]. }
  split.
  { apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md3 LX_CID fp); [exact HAR | rewrite HFR; left; reflexivity | | | lia];
      rewrite HFA; change (fs_frame_bytes LX_CID) with 512; lia. }
  intros a Ha. pose proof (lj_word_end _ L a HP8 HL32 Ha) as Ha'.
  unfold lprev, lview in HPV. replace a with (lF cx fp + 64 + (a - lF cx fp - 64)) by lia.
  rewrite HPV by (unfold LX_REG; lia). discriminate.
Qed.

Lemma lj_cstr_reg : forall cx fp W3 (ms : machine_state) ly3 S3 md3 k r bs' j,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  In (r, LX_REG) (ablocks B ly3 S3) -> lreg W3 ms r bs' -> length bs' = 288%nat -> 0 <= j < 5 ->
  In (Z_to_bv 8 0) (Boxreg.bx_name bs' j) ->
  abfm_cstr_ok SEGS W3 (ms_mem ms) (r + 56 * j + 24) (lname bs' j).
Proof.
  intros cx fp W3 ms ly3 S3 md3 k r bs' j HB HJ HrIn HRG HL Hj Hn.
  pose proof (lh_laws B MT HY) as LAWS.
  pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size LX_REG) with 288 in Hrceil.
  pose proof (lname_len bs' j ltac:(lia) ltac:(rewrite HL; lia) Hn) as HLn.
  set (L := Z.of_nat (length (lname bs' j))) in *.
  assert (HL32 : 0 <= L < 32) by (unfold L; lia).
  assert (HP8 : (r + 56 * j + 24) mod 8 = 0).
  { apply Z.mod_divide in Hr16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hr16 as [q Hq]. exists (2 * q + 7 * j + 3). lia. }
  unfold abfm_cstr_ok, abfm_cstr. fold L.
  split; [split|].
  { intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    rewrite (lname_nth bs' j t ltac:(lia) ltac:(rewrite HL; lia) Hn ltac:(lia)).
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (56 * j + 24 + Z.of_nat t)) bs' (Z_to_bv 8 0))) as R.
    change (bv_modulus 8) with 256 in R.
    split; [|exact R]. apply lj_val_mem1; [|exact R].
    unfold lreg, lview in HRG. replace (r + 56 * j + 24 + Z.of_nat t) with (r + (56 * j + 24 + Z.of_nat t)) by lia.
    apply HRG. unfold LX_REG, L in *. lia. }
  { apply lj_cpre_nz. }
  split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
  split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HrIn); change (req_size LX_REG) with 288; lia|].
  split; [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HrIn); change (req_size LX_REG) with 288; lia|].
  split; [eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HrIn); change (req_size LX_REG) with 288; lia|].
  intros a Ha. pose proof (lj_word_end _ L a HP8 HL32 Ha) as Ha'.
  unfold lreg, lview in HRG. replace a with (r + (a - r)) by lia.
  rewrite HRG by (unfold LX_REG; lia). discriminate.
Qed.

(* ---- K: check (r, fabric), prev.n, to the loop head or the turn's end ---- *)
Section k.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Hypothesis HLE : lx_from B MT POST (LI_E i).
Hypothesis HLL : lx_from B MT POST (LI_L i 0).

Definition KF_fcs : list YP09.chunk := [YP09.mkChunk 344 (CVal 4 (SOff 48 0))].
Definition KF_G : facts := mkFacts (LX_AF ++ [(48%nat, mkAF 0 5 0)]) [] [].

Lemma lj_kwalk : lx_from B MT POST (LI_K B MT i).
Proof.
  pose proof (lh_laws B MT HY) as LAWS.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (pos & r & fab & ren & bs & bs' & HBD & Hi & Hk & Hacc & HBLK & HPV & HIV & HFB & HRG & HIV' & HFB'
    & HKP & Hren & HCUR & HSL & H58 & R20 & R21 & R24 & R27).
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HLR & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof HIV as ((HL288 & HB1 & HB2 & HB3 & HB4 & HB5 & HB6) & HB7).
  set (ex := [w64 (lu4 bs 280)]).
  set (E := lx_env cx fp (ms_regs ms3) ex).
  assert (HE : lx_E cx fp E) by exact (lx_env_E cx fp ms3 ex HLR).
  assert (E48 : ew E 48 = w64 (lu4 bs 280)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
  assert (HEI : img_env VAL A_LIM E) by exact (lx_env_img cx fp (ms_regs ms3) ex).
  assert (Hn : lu4 bs 280 = Boxreg.bx_n bs).
  { rewrite lu4_mod. unfold Boxreg.bx_n. unfold Boxreg.boxreg_B1, Boxreg.bx_n in HB1. apply Z.mod_small. lia. }
  assert (HS0 : st_ok_pi SEGS VAL E (lx_ss LP_K (lx_sr LX_OVP) LSH_iter (lx_slot_chunks []) KF_fcs 0 0 0 0 [] KF_G)
                  (restrict (w_H W3) ms3)).
  { eapply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
    - exact HE.
    - exact HBD.
    - apply lx_regs_ok; [apply lx_regs_ok_atoms | exact (lx_ovp_ok cx fp ms3 ex HLR R21)].
    - constructor.
    - constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (lF cx fp) 344 4 (SOff 48 0) (lu4 bs 280)).
      + rewrite lx_sv_SOff0. exact E48.
      + pose proof (lu4_range bs 280). cbn. lia.
      + cbn. lia.
      + replace (lF cx fp + 344) with (lF cx fp + 64 + 280) by lia. apply lu4_val_mem; [lia | rewrite HL288; cbn; lia |].
        intros t Ht. rewrite <- Z.add_assoc. apply HPV. unfold LX_REG. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - unfold lx_regions0. repeat constructor.
    - unfold KF_G. split; [|split; exact I]. cbn [f_atoms]. apply lj_atoms_ok_app.
      + exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
      + cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E48.
        unfold w64. rewrite unsigned_lit_small by (pose proof (lu4_range bs 280); lia). rewrite Hn.
        unfold Boxreg.boxreg_B1 in HB1. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  rename HS0 into HS.
  lj_unwin_tac HS 1%nat.
  pose proof HE as (H2E & H8E & H3E & H4E & H22E & H32E & HSAVE & H46E & H47E).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in H2E, H8E, H22E, H32E, H46E, H47E.
  assert (E20 : ew E 20 = w64 r) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 20 20%bv eq_refl) R20).
  assert (E27 : ew E 27 = w64 fab) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 27 27%bv eq_refl) R27).
  assert (E24 : ew E 24 = w64 (ren mod 2 ^ 32))
    by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 24 24%bv eq_refl) R24).
  clearbody E.
  pose proof HB as (HPRE0 & _ & _ & HPN & _ & _ & _ & _ & HRO0 & _).
  pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
  pose proof HJ as (HAR & _).
  assert (HrIn : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
  assert (Hbl : forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3))
    by (intros p n Hp; unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left; exact Hp).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size LX_REG) with 288 in Hrceil.
  pose proof asan_consts as (C1 & _).
  pose proof (lx_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HSH0 & HSH1).
  assert (U2E : bv_unsigned (ew E 2) = lsp1 cx) by (rewrite H2E; unfold w64; apply unsigned_lit_small; lia).
  assert (U8E : bv_unsigned (ew E 8) = lsp0 cx) by (rewrite H8E; unfold w64; apply unsigned_lit_small; lia).
  assert (U46E : bv_unsigned (ew E 46) = lF cx fp) by (rewrite H46E; unfold w64; apply unsigned_lit_small; lia).
  assert (U22E : bv_unsigned (ew E 22) = lSH cx fp) by (rewrite H22E; unfold w64; apply unsigned_lit_small; lia).
  assert (U20E : bv_unsigned (ew E 20) = r) by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
  assert (SHOK : sh_ok SEGS (SOff LA_SB 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUN := paj_run B LAWS).
  paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  (* the run wrote nothing *)
  pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
  assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) (ms_mem ms)) by (apply lj_keep_eq; exact HMEQ).
  clear HF HFr.
  (* at the call of check (0x80b10) *)
  pmkst HS. rewrite pa_sigma_check.
  prreg HS (1%bv : bv 5) CR1. prreg HS (2%bv : bv 5) CR2. prreg HS (3%bv : bv 5) CR3. prreg HS (4%bv : bv 5) CR4.
  prreg HS (8%bv : bv 5) CR8. prreg HS (10%bv : bv 5) CR10. prreg HS (11%bv : bv 5) CR11.
  rewrite H2E in CR2. rewrite H3E, Hgp0 in CR3. rewrite H4E, Htp0 in CR4. rewrite H8E in CR8.
  rewrite E20 in CR10. rewrite E27 in CR11.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (HRB0 : forall i0, 0 <= i0 < REG_SIZEB ->
      aview SEGS (w_H W3) mm (r + i0) = Some (bv_unsigned (nth (Z.to_nat i0) bs' (Z_to_bv 8 0))))
      by (intros i0 Hi0; rewrite HMEQ; apply HRG; exact Hi0);
    assert (HSV1 : lsaved cx W3 ms) by (destruct HSV as [Hs1 Hs2]; split; [rewrite <- Hs1 | intros j Hj; rewrite <- (Hs2 j Hj)];
      apply rdword_ext; intros q Hq; apply HMEQ);
    eapply SRr_bind;
    [ eapply (cl_callS B LAWS W3 rg mm _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
        [(LX_CID, fp)] ly3 S3 mdq k CHECK_STKB [] 0 (lsp1 cx - lsp0 cx) _ (lch cx)
        (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
           Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
           (forall i0, 0 <= i0 < REG_SIZEB ->
              aview SEGS (w_H W2) mem2 (r + i0) = Some (bv_unsigned (nth (Z.to_nat i0) bs' (Z_to_bv 8 0))))) HJ);
      [ unfold spZ at 1; rewrite CR2; unfold w64; rewrite unsigned_lit_small by lia; lia
      | apply lj_sub_mod16; [exact Hsp32 | exact Hsp16]
      | lia
      | unfold CHECK_STKB, ESTACK; lia
      | unfold CHECK_STKB, ESTACK, LX_STK; lia
      | exact CR3
      | exact CR4
      | reflexivity
      | rewrite CR1; apply ret_ok_codeptr_v; [lia | reflexivity]
      | rewrite CR1; pose proof (pa_base_lo (PL := PL_boxb) (PI := PI)); pose proof pa_B_ok;
        rewrite unsigned_lit_small by lia; lia
      | replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia;
        unfold s0Z at 1; rewrite CR8; unfold w64; rewrite unsigned_lit_small by lia;
        destruct HSV1 as [Hra1 Hsj1];
        apply (lj_achain cx k ly3 S3 W3 mm _ _ _ HB HJ Hra1);
        [ pose proof (Hsj1 0 ltac:(lia)) as H0s; rewrite Z.mul_0_r, Z.sub_0_r in H0s; unfold lview in H0s;
          rewrite H0s; unfold s0Z; do 3 f_equal; apply bv_eq; reflexivity | lia ]
      | intros HPRE1;
        exact (lh_check B MT HY ly3 S3 W3 rg mm mdq (lch cx) r fab bs' [(VAL (A_OBJ 4), 6)] HPRE1
          ltac:(eapply lx_arodata_kept; [exact HJ | exact HRO0]) CR10 CR11 HrIn HRB0 (proj1 HIV') HFB'
          (blx_isv _ (lh_glob B MT HY)) lj_globs_zero
          (blx_rom_bytes _ (lh_glob B MT HY) (4%nat, [0; 0; 0; 0; 0; 0]) ltac:(cbn; left; reflexivity))
          ltac:(left; reflexivity)
          (proj1 (blx_marg _ (lh_glob B MT HY) (4%nat, 6) ltac:(cbn; left; reflexivity)))
          (proj2 (blx_marg _ (lh_glob B MT HY) (4%nat, 6) ltac:(cbn; left; reflexivity)))
          (blx_mch _ (lh_glob B MT HY)))
      | intros a0 Ha0; exfalso; exact (lx_inFP_nil a0 Ha0) ]
    | ] end.
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (-> & -> & -> & _ & HRB2)).
  rewrite Z.add_0_r in HJ2.
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJc by lia.
  assert (HK : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms) mem2).
  { eapply (lx_keep_call B MT LAWS cx fp W3 ms ly3 S3 _ k HB HJ HFR); [lia | exact Hbl | | exact HJc].
    constructor; [|constructor]. exists LX_REG. split; [exact HrIn | cbn [snd]; change (req_size LX_REG) with 288; unfold LX_REG; lia]. }
  assert (HKA2 : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms3) mem2) by (eapply lx_keep_trans; [exact HKA | exact HK]).
  clear HKA; rename HKA2 into HKA.
  rewrite CR1.
  lj_reseat HS HP W3 mem2 HK [0; 1; 2; 3]%nat.
  lj_newenv HS E1 HE1 OLD1.
  clear SHOK. assert (SHOK : sh_ok SEGS (SOff LA_SB 0) [] E1 (mrestrict (w_H W3) mem2)) by constructor.
  clear HJ. rename HJ2 into HJ.
  paj_run_tok RUN HS HJ SHOK LX_SBX; [apply lj_awr_ro; vm_compute; reflexivity |].
  lj_keep_run HKA.
  pose (BR := paj_branch (PI := PI)). pose (RUNTO := paj_run_to B LAWS).
  psrr_branch_tok RUN BR HS SHOK LX_SBX;
    rewrite (lj_bge0 _ 48 (Boxreg.bx_n bs) ltac:(rewrite E48, Hn; reflexivity) ltac:(unfold Boxreg.boxreg_B1 in HB1; lia)) in Hc.
  - (* n = 0: no row; to the turn's end 0x80cb0 *)
    apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_E; [apply lj_awr_ro; vm_compute; reflexivity |].
    lj_keep_run HKA.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
      apply (HLE cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end.
    exists pos, r, fab, bs'.
    split; [lj_land_body HS|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|].
    split; [lj_kf|]. split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    rewrite G27, lx_sv_SOff0; exact E27.
  - (* n >= 1: to the head of check_kept's loop, row 0 *)
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK LX_SBX LP_L; [apply lj_awr_ro; vm_compute; reflexivity |].
    lj_keep_run HKA.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
      apply (HLL cx fp k acc ly3 S3 W3 msx _ HB HJ HFR HMO) end.
    exists pos, r, fab, ren, bs, bs'.
    split; [lj_land_body HS|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV|]. split; [exact HFB|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|]. split; [exact HKP|]. split; [exact Hren|].
    split; [unfold Boxreg.boxreg_B1 in HB1; lia|].
    split; [lj_kf|]. split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21. lj_reg HS (23%bv : bv 5) G23. lj_reg HS (24%bv : bv 5) G24.
    lj_reg HS (26%bv : bv 5) G26. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    split; [rewrite G23; reflexivity|].
    split; [rewrite G24; apply lj_s8; [exact E24 | apply Z.mod_pos_bound; lia]|].
    split; [rewrite G26; apply lj_s10; [rewrite E48, Hn; reflexivity | unfold Boxreg.boxreg_B1 in HB1; lia]|].
    rewrite G27, lx_sv_SOff0; exact E27.
Qed.
End k.

(* ---- the turn's end: mac and prev out of scope (LSH_entry), i + 1, to J or X ---- *)
Section e.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Hypothesis HLX : lx_from B MT POST (LI_X B MT).
Hypothesis HLJ : lx_from B MT POST (LI_J B MT (S i)).

Definition EF_G : facts := mkFacts (LX_AF ++ [(48%nat, mkAF 0 63 0)]) [] [].

Lemma lj_ewalk : lx_from B MT POST (LI_E i).
Proof.
  pose proof (lh_laws B MT HY) as LAWS.
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (pos & r & fab & bs' & HBD & Hi & Hk & Hacc & HBLK & HRG & HIV' & HFB' & HCUR & HSL & H58
    & R20 & R21 & R27).
  pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & HLR & HSV & HSH & HFL & S10 & S18 & S80 & HIN).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HF64 & HSHe).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof (lx_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HSH0 & HSH1).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as HFA.
  set (ex := [w64 (Z.of_nat i)]).
  set (E := lx_env cx fp (ms_regs ms3) ex).
  assert (HE : lx_E cx fp E) by exact (lx_env_E cx fp ms3 ex HLR).
  assert (E48 : ew E 48 = w64 (Z.of_nat i)) by exact (lx_env_ex cx fp (ms_regs ms3) ex 0 ltac:(lia)).
  assert (HEI : img_env VAL A_LIM E) by exact (lx_env_img cx fp (ms_regs ms3) ex).
  assert (HS0 : st_ok_pi SEGS VAL E (lx_ss LP_E (lx_sr LX_OVP) LSH_iter (lx_slot_chunks [(0x58, SOff 48 0)]) [] 0 0 4 44 [] EF_G)
                  (restrict (w_H W3) ms3)).
  { eapply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
    - exact HE.
    - exact HBD.
    - apply lx_regs_ok; [apply lx_regs_ok_atoms | exact (lx_ovp_ok cx fp ms3 ex HLR R21)].
    - constructor; [|constructor]. cbn [fst snd].
      apply (lx_slot_atom cx W3 ms3 E 0x58 48 (Z.of_nat i) 0); [rewrite Z.add_0_r; exact H58 | exact E48 | lia | lia].
    - constructor.
    - lia.
    - lia.
    - lia.
    - lia.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - unfold lx_regions0. repeat constructor.
    - unfold EF_G. split; [|split; exact I]. cbn [f_atoms]. apply lj_atoms_ok_app.
      + exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
      + cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E48.
        unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  rename HS0 into HS.
  lj_unwin_tac HS 1%nat.
  pose proof HE as (H2E & H8E & H3E & H4E & H22E & H32E & HSAVE & H46E & H47E).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in H2E, H8E, H22E, H32E, H46E, H47E.
  assert (E20 : ew E 20 = w64 r) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 20 20%bv eq_refl) R20).
  assert (E27 : ew E 27 = w64 fab) by exact (eq_trans (lx_env_reg cx fp (ms_regs ms3) ex 27 27%bv eq_refl) R27).
  clearbody E.
  assert (U22E : bv_unsigned (ew E 22) = lSH cx fp) by (rewrite H22E; unfold w64; apply unsigned_lit_small; lia).
  pose (RUNP := SRr_run_pi_AJ B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ B LAWS). pose (BR := paj_branch (PI := PI)).
  paj_run_sh RUNP HS HJ.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U22E | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right.
    exists LX_CID, fp. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite HFA. change (fs_frame_bytes LX_CID / 8) with 64. unfold lSH in Ha. lia. }
  (* the run wrote only the frame's shadow bytes [lSH + 4, lSH + 44) *)
  assert (HM : forall x : word, ~ (shadow_addr (lF cx fp) <= bv_unsigned x < shadow_addr (lF cx fp) + 64) ->
                 ms_mem ms x = ms_mem ms3 x).
  { intros x Hx. apply HF. intros (rr & Hin & Hb).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U22E in Hb; unfold lSH in Hb; lia |]).
    destruct Hin. }
  pose proof asan_consts as (C1 & _).
  assert (HFd : lF cx fp / 8 <= 35184372088832) by (apply Z.div_le_upper_bound; lia).
  assert (HSHA : shadow_addr (lF cx fp) + 64 < alloc_ceiling)
    by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (HrIn : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
  pose proof HJ as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR HrIn) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hria, Hrceil.
  pose proof HB as (HPRE0 & _ & _ & HPN & _).
  (* the facts of the cut, across the shadow stores *)
  assert (KSV : lsaved cx W3 ms).
  { destruct HSV as [Hra1 Hsj1]. split.
    - apply (lj_nsh_above W3 (lF cx fp) (ms_mem ms3) (ms_mem ms) _ _ HM); [lia | lia | lia | exact Hra1].
    - intros j Hj.
      apply (lj_nsh_above W3 (lF cx fp) (ms_mem ms3) (ms_mem ms) _ _ HM); [lia | lia | lia | exact (Hsj1 j Hj)]. }
  assert (KSL : forall off v, 0 <= off -> off <= 0x90 -> lslot cx W3 ms3 off v -> lslot cx W3 ms off v).
  { intros off v H0 H1 Hv. unfold lslot, lview in *.
    apply (lj_nsh_above W3 (lF cx fp) (ms_mem ms3) (ms_mem ms) _ _ HM); [lia | lia | lia | exact Hv]. }
  assert (KFL : rdword (lview W3 ms) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp)).
  { unfold lview in *. change (fs_frame_bytes LX_CID) with 512 in HFL |- *.
    apply (lj_nsh_rdword W3 (lF cx fp) (ms_mem ms3) (ms_mem ms) (lF cx fp) 512 _ _ HM HF0 HFc HFapp);
      [lia | lia | lia | lia | exact HFL]. }
  assert (KRG : lreg W3 ms r bs').
  { intros q Hq. unfold lreg, lview in *.
    rewrite (lj_nsh_byte W3 (lF cx fp) (ms_mem ms3) (ms_mem ms) r 288 (r + q) HM HF0 HFc Hria ltac:(unfold LX_REG in Hq; lia)
      ltac:(unfold LX_REG in Hq; lia)).
    exact (HRG q Hq). }
  assert (KIN : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx))).
  { destruct HPN as [[Hn0 _] | (Hn & Hinp)].
    - intros j Hj. rewrite length_map in Hj. unfold lc_n in Hn0. lia.
    - assert (HinL : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
        by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left; exact Hinp).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinL) as (_ & Hp4096 & Hpceil & Hpia & _).
      pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hrq].
      intros j Hj. pose proof (HIN j Hj) as [Hv Hr]. split; [|exact Hr].
      intros q Hq. destruct q as [|q]; [|cbn [Nat.lt] in Hq; lia].
      pose proof (Hv 0%nat ltac:(lia)) as Hv0.
      rewrite length_map in Hj.
      assert (AEQ : aview SEGS (w_H W3) (ms_mem ms) (lc_p cx + Z.of_nat j + Z.of_nat 0)
                  = aview SEGS (w_H W3) (ms_mem ms3) (lc_p cx + Z.of_nat j + Z.of_nat 0))
        by (apply (lj_nsh_byte W3 (lF cx fp) (ms_mem ms3) (ms_mem ms) (lc_p cx) (req_size (lc_n cx)));
            [exact HM | lia | lia | exact Hpia | change (Z.of_nat 0) with 0; unfold lc_n in *; lia
            | change (Z.of_nat 0) with 0; unfold lc_n in *; lia]).
      rewrite (mbyte_of_aview SEGS _ _ _ _ _ AEQ). exact Hv0. }
  assert (KSH : lshadow cx fp W3 ms LSH_entry).
  { lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
      let r3 := eval vm_compute in (nth_error (ss_mem ss) 3) in
      lazymatch r3 with Some (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
        apply (lx_shadow_of_ss B MT LAWS cx fp W3 ms ly3 S3 _ k HB HJ HFR Ex ss lo hi wlo whi cs LSH_entry HE HS);
          [vm_compute; reflexivity | vm_compute; reflexivity] end end. }
  (* the facts at the stores' end; then close region 3's window: the branch run writes nothing *)
  assert (KS10 : lslot cx W3 ms 0x10 (lF cx fp)) by (apply KSL; [lia | lia | exact S10]).
  assert (KS18 : lslot cx W3 ms 0x18 (lF cx fp)) by (apply KSL; [lia | lia | exact S18]).
  assert (KS80 : lslot cx W3 ms 0x80 (lF cx fp)) by (apply KSL; [lia | lia | exact S80]).
  assert (KCUR : lcur cx W3 ms pos).
  { destruct HCUR as (Hp & C88 & C90). split; [exact Hp|]. split; apply KSL; first [lia | assumption]. }
  assert (KSLL : lslots_loop cx fp W3 ms r fab).
  { destruct HSL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
    repeat split; apply KSL; first [lia | assumption]. }
  clear HSV HSH HFL S10 S18 S80 HIN HRG HCUR HSL H58 KSL HM HF HFr HG.
  lj_unwin_tac HS 3%nat.
  assert (HBR : forall Ex, ew Ex 48 = w64 (Z.of_nat i) ->
            branch_taken BC_NE (sv_denot Ex (SOff 48 1)) (sv_denot Ex (SLit 64)) = negb (Z.of_nat i + 1 =? 64)).
  { intros Ex H48. rewrite branch_ne_U, (U_lit Ex 64) by lia. rewrite U_SOff, H48. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity. }
  psrr_branch_pi RUNP BR HS; rewrite (HBR _ E48) in Hc.
  - (* i + 1 < 64: the next turn's head 0x80258 *)
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_sh RUNTOP HS HJ LP_J; [apply lj_awr_ro; vm_compute; reflexivity |].
    pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
    assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms) (ms_mem ms0)) by (apply lj_keep_eq; exact HMEQ).
    clear HF HFr HG.
    apply (HLJ cx fp k acc ly3 S3 W3 ms0 _ HB HJ HFR HMO).
    exists pos, r, fab, bs'.
    split; [lj_land_body HS|].
    split; [lia|]. split; [lia|]. split; [rewrite Nat2Z.inj_succ; lia|]. split; [exact HBLK|].
    split; [lj_kf|]. split; [exact HIV'|]. split; [exact HFB'|].
    split; [lj_kf|]. split; [lj_kf|].
    lj_reg HS (19%bv : bv 5) G19. lj_reg HS (20%bv : bv 5) G20. lj_reg HS (21%bv : bv 5) G21.
    lj_reg HS (24%bv : bv 5) G24. lj_reg HS (27%bv : bv 5) G27.
    split; [rewrite G19; reflexivity|].
    split; [rewrite G20, lx_sv_SOff0; exact E20|].
    split; [rewrite G21, (lj_den_atom _ 46 (lF cx fp) 64 H46E) by lia; reflexivity|].
    split; [rewrite G24, (lj_den_atom _ 48 (Z.of_nat i) 1 E48) by lia; rewrite Nat2Z.inj_succ; reflexivity|].
    rewrite G27, lx_sv_SOff0; exact E27.
  - (* i + 1 = 64: the loop is done, 0x80e54 *)
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_sh RUNTOP HS HJ LP_X; [apply lj_awr_ro; vm_compute; reflexivity |].
    pose proof (lj_aview_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as HMEQ.
    assert (HKA : lx_keep cx fp W3 [(r, LX_REG)] (ms_mem ms) (ms_mem ms0)) by (apply lj_keep_eq; exact HMEQ).
    clear HF HFr HG.
    apply (HLX cx fp k acc ly3 S3 W3 ms0 _ HB HJ HFR HMO).
    exists r.
    split; [lj_land_body HS|].
    split; [lia|]. split; [replace 64 with (Z.of_nat i + 1) by lia; exact Hacc|]. split; [exact HBLK|].
    lj_reg HS (20%bv : bv 5) G20. rewrite G20, lx_sv_SOff0; exact E20.
Qed.
End e.

End a.
