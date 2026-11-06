(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v; 376 of its 398 lines of code are new or changed and 496 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of segment S14 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x858f4 .. 0x85ac0 with the continue join
   0x859c4 .. 0x859f8), the head of the inlined m_declared loop at turn i.

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s43.v (the trim loop: a seed, the
   symbolic engine's runs and their branches, a loop by induction on its counter) and _s40.v (the inner cut
   statements of a segment), at origin/ossv/recipes 501c0d516c69.

   This file holds the part of S14 that is pure Gallina: the model lemmas that say what the code's tests mean in
   SegModel's terms. No function of the binary is proved here.

   - strrchr: the runtime row's answer (RtSeg.last_at / "c does not occur") against SegModel.strrchr.
   - the digit loop 0x85974 <- 0x859a8: SegModel.m_digits through SegModel.m_digits_spec's closed form.
   - the parent loop 0x85a18 <- 0x85a78: the three byte tests (isdigit, the `& ~32` letter test, and bit b - 45 of
     the mask 0x4000000002003 = 2 ^ 50 + 2 ^ 13 + 2 + 1) against SegModel.h_parent_ok.
   - the loop's model step: m_decl_go over firstn (S i) against firstn i, and its answer at the loop's exit. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the byte-class mask the code keeps at 136(s1) (0x858c4 .. 0x858e0), as LLVMFuzzerTestOneInput_defs.LT_MASK *)
Definition S22_MASK : Z := 0x4000000002003.

(* ======================= generic list helpers ======================= *)
Lemma s22_firstn_S : forall {A} (l : list A) n (d : A),
  (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l. induction l as [|a l IH]; intros n d H; cbn [length] in H; [lia|].
destruct n as [|n]; [reflexivity|].
change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l).
change (firstn (S n) (a :: l)) with (a :: firstn n l).
change (nth (S n) (a :: l) d) with (nth n l d).
cbn [app]. f_equal. apply IH. lia.
Qed.

(* ======================= strrchr: the row's answer against SegModel.strrchr ======================= *)
Lemma s22_last_idx_notin : forall c l i acc, ~ In c l -> SegModel.last_idx c l i acc = acc.
Proof.
intros c l. induction l as [|b r IH]; intros i acc H; cbn [SegModel.last_idx]; [reflexivity|].
destruct (Z.eqb_spec b c) as [->|Hne]; [exfalso; apply H; left; reflexivity|].
apply IH. intros H'. apply H. right. exact H'.
Qed.

Lemma s22_last_idx_at : forall c l j i acc,
  RtSeg.last_at l c j -> SegModel.last_idx c l i acc = Some (i + j)%nat.
Proof.
intros c l. induction l as [|b r IH]; intros j i acc (Hj & Hnth & Hnin); cbn [length] in Hj; [lia|].
cbn [SegModel.last_idx]. destruct j as [|j'].
- cbn [nth] in Hnth. subst b. rewrite Z.eqb_refl.
  rewrite (s22_last_idx_notin c r (S i) (Some i)); [f_equal; lia|].
  cbn [skipn] in Hnin. exact Hnin.
- cbn [nth] in Hnth. cbn [skipn] in Hnin.
  replace (i + S j')%nat with (S i + j')%nat by lia.
  apply IH. split; [cbn [length] in Hj; lia | split; [exact Hnth | exact Hnin]].
Qed.

Lemma s22_strrchr_none : forall l c, SegModel.nulfree l -> ~ In c l -> SegModel.strrchr l c = None.
Proof.
intros l c Hn Hin. unfold SegModel.strrchr. rewrite SegModel.cut_nul_id by exact Hn.
apply (s22_last_idx_notin c l 0%nat None Hin).
Qed.

Lemma s22_strrchr_some : forall l c j,
  SegModel.nulfree l -> RtSeg.last_at l c j -> SegModel.strrchr l c = Some j.
Proof.
intros l c j Hn Hla. unfold SegModel.strrchr. rewrite SegModel.cut_nul_id by exact Hn.
rewrite (s22_last_idx_at c l j 0%nat None Hla). reflexivity.
Qed.

(* ======================= the digit loop against SegModel.m_digits ======================= *)
Lemma s22_dstep_ge : forall v d, 0 <= v -> SegModel.isdigit d = true -> v <= SegModel.dstep v d.
Proof.
intros v d Hv Hd. unfold SegModel.isdigit in Hd. apply andb_prop in Hd as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. unfold SegModel.dstep. lia.
Qed.

Lemma s22_fold_ge : forall l v, 0 <= v -> forallb SegModel.isdigit l = true ->
  v <= fold_left SegModel.dstep l v.
Proof.
intros l. induction l as [|d r IH]; intros v Hv Hall; cbn [fold_left]; [lia|].
cbn [forallb] in Hall. apply andb_prop in Hall as [Hd Hr].
pose proof (s22_dstep_ge v d Hv Hd) as Hstep.
pose proof (IH (SegModel.dstep v d) ltac:(lia) Hr). lia.
Qed.

(* the loop fails on a byte that is not a digit: the model's answer is None *)
Lemma s22_digits_none_nondigit : forall l t,
  (t < length l)%nat -> SegModel.isdigit (nth t l 0) = false -> SegModel.m_digits l 0 = None.
Proof.
intros l t Ht Hnd. rewrite SegModel.m_digits_spec by lia.
assert (Hall : forallb SegModel.isdigit l = false).
{ destruct (forallb SegModel.isdigit l) eqn:E; [|reflexivity].
  rewrite forallb_forall in E. rewrite (E (nth t l 0) (nth_In l 0 Ht)) in Hnd. discriminate Hnd. }
rewrite Hall. reflexivity.
Qed.

(* the loop fails because the running value passed 4094: the model's answer is None *)
Lemma s22_digits_none_big : forall l t,
  (t < length l)%nat -> 4094 < fold_left SegModel.dstep (firstn (S t) l) 0 ->
  SegModel.m_digits l 0 = None.
Proof.
intros l t Ht Hbig. rewrite SegModel.m_digits_spec by lia.
destruct (forallb SegModel.isdigit l) eqn:Hall; [|reflexivity].
cbn [andb].
assert (Hsplit : fold_left SegModel.dstep l 0 =
                 fold_left SegModel.dstep (skipn (S t) l) (fold_left SegModel.dstep (firstn (S t) l) 0)).
{ rewrite <- fold_left_app, firstn_skipn. reflexivity. }
assert (Hsuf : forallb SegModel.isdigit (skipn (S t) l) = true).
{ rewrite forallb_forall in Hall |- *. intros x Hx. apply Hall.
  rewrite <- (firstn_skipn (S t) l). apply in_or_app. right. exact Hx. }
pose proof (s22_fold_ge (skipn (S t) l) (fold_left SegModel.dstep (firstn (S t) l) 0) ltac:(lia) Hsuf) as Hge.
rewrite <- Hsplit in Hge.
destruct (Z.leb_spec (fold_left SegModel.dstep l 0) 4094) as [Hle|_]; [lia | reflexivity].
Qed.

(* the loop ran out of digits: the model's answer is the fold *)
Lemma s22_digits_some : forall l,
  forallb SegModel.isdigit l = true -> fold_left SegModel.dstep l 0 <= 4094 ->
  SegModel.m_digits l 0 = Some (fold_left SegModel.dstep l 0).
Proof.
intros l Hall Hle. rewrite SegModel.m_digits_spec by lia. rewrite Hall. cbn [andb].
destruct (Z.leb_spec (fold_left SegModel.dstep l 0) 4094) as [_|Hgt]; [reflexivity | lia].
Qed.

(* ======================= the parent loop's byte test against h_parent_ok ======================= *)
(* the letter test of 0x85a38 .. 0x85a48: (b & ~32) - 65 as a byte is below 26 *)
Definition s22_alpha (b : Z) : bool := ((65 <=? b) && (b <=? 90)) || ((97 <=? b) && (b <=? 122)).

(* the finite check: a byte identity over [0, 256) from one vm_compute *)
Lemma s22_byte_all : forall (f g : Z -> bool),
  forallb (fun n => Bool.eqb (f (Z.of_nat n)) (g (Z.of_nat n))) (seq 0 256) = true ->
  forall b, 0 <= b < 256 -> f b = g b.
Proof.
intros f g H b Hb. rewrite forallb_forall in H.
assert (Hin : In (Z.to_nat b) (seq 0 256)) by (apply in_seq; lia).
pose proof (H (Z.to_nat b) Hin) as E. rewrite Z2Nat.id in E by lia.
apply Bool.eqb_prop. exact E.
Qed.

(* 0x85a2c .. 0x85a34: (b - 48) as a byte is below 10 *)
Lemma s22_dig_b : forall b, 0 <= b < 256 -> ((b - 48) mod 256 <? 10) = SegModel.isdigit b.
Proof. apply s22_byte_all. vm_compute. reflexivity. Qed.

(* 0x85a38 .. 0x85a48: ((b & 0xffffffffffffffdf) - 65) as a byte is below 26 *)
Lemma s22_alpha_b : forall b, 0 <= b < 256 ->
  ((Z.land b 18446744073709551583 - 65) mod 256 <? 26) = s22_alpha b.
Proof. apply s22_byte_all. vm_compute. reflexivity. Qed.

(* h_parent_ok split the way the code tests it *)
Lemma s22_pk_split : forall b, 0 <= b < 256 ->
  SegModel.h_parent_ok b =
  (SegModel.isdigit b || s22_alpha b || ((b =? 45) || (b =? 46) || (b =? 58) || (b =? 95))).
Proof.
intros b Hb. symmetry. revert b Hb. apply s22_byte_all. vm_compute. reflexivity.
Qed.

(* 0x85a5c .. 0x85a68: bit k of the mask, for the k = b - 45 the code reaches *)
Lemma s22_mask_bit : forall k, 0 <= k <= 50 ->
  Z.land (Z.shiftr S22_MASK k) 1 = (if ((k =? 0) || (k =? 1) || (k =? 13) || (k =? 50))%bool then 1 else 0).
Proof.
intros k Hk.
assert (H : forallb (fun n => Z.eqb (Z.land (Z.shiftr S22_MASK (Z.of_nat n)) 1)
              (if ((Z.of_nat n =? 0) || (Z.of_nat n =? 1) || (Z.of_nat n =? 13) || (Z.of_nat n =? 50))%bool
               then 1 else 0)) (seq 0 51) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H.
assert (Hin : In (Z.to_nat k) (seq 0 51)) by (apply in_seq; lia).
pose proof (H (Z.to_nat k) Hin) as E. rewrite Z2Nat.id in E by lia.
apply Z.eqb_eq. exact E.
Qed.

(* the mask bit decides h_parent_ok for a byte that is neither a digit nor a letter *)
Definition s22_pkr (b : Z) : bool :=
  ((b - 45 =? 0) || (b - 45 =? 1) || (b - 45 =? 13) || (b - 45 =? 50))%bool.

Lemma s22_pk_rest_all : forall b, 0 <= b < 256 ->
  (SegModel.isdigit b || s22_alpha b || SegModel.h_parent_ok b)%bool =
  (SegModel.isdigit b || s22_alpha b || s22_pkr b)%bool.
Proof. apply s22_byte_all. vm_compute. reflexivity. Qed.

Lemma s22_pk_rest : forall b, 0 <= b < 256 -> SegModel.isdigit b = false -> s22_alpha b = false ->
  SegModel.h_parent_ok b = s22_pkr b.
Proof.
intros b Hb Hd Ha. pose proof (s22_pk_rest_all b Hb) as H. rewrite Hd, Ha in H. cbn [orb] in H. exact H.
Qed.

(* a byte the third test rejects (b - 45 outside [0, 50] as an unsigned 64-bit value) is not a parent byte *)
Lemma s22_pk_out : forall b, 0 <= b < 256 -> SegModel.isdigit b = false -> s22_alpha b = false ->
  (b < 45 \/ 95 < b) -> SegModel.h_parent_ok b = false.
Proof.
intros b Hb Hd Ha Hout. rewrite (s22_pk_rest b Hb Hd Ha). unfold s22_pkr.
repeat apply orb_false_intro; (apply Z.eqb_neq; lia).
Qed.

(* the parent loop's answer: every byte of the prefix passed, or one failed *)
Lemma s22_forallb_false : forall {A} (f : A -> bool) l t d,
  (t < length l)%nat -> f (nth t l d) = false -> forallb f l = false.
Proof.
intros A f l t d Ht Hf. destruct (forallb f l) eqn:E; [|reflexivity].
rewrite forallb_forall in E. rewrite (E (nth t l d) (nth_In l d Ht)) in Hf. discriminate Hf.
Qed.

(* ======================= the loop's model step ======================= *)
Lemma s22_decl_app : forall l1 l2 tab cap a,
  0 <= fst (SegModel.m_decl_go l1 tab cap a) ->
  SegModel.m_decl_go (l1 ++ l2) tab cap a =
  SegModel.m_decl_go l2 (snd (SegModel.m_decl_go l1 tab cap a)) cap (fst (SegModel.m_decl_go l1 tab cap a)).
Proof.
intros l1. induction l1 as [|g l1 IH]; intros l2 tab cap a Ha; [reflexivity|].
cbn [app SegModel.m_decl_go] in Ha |- *.
destruct (SegModel.ms_ignore g); [apply IH; exact Ha|].
destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|apply IH; exact Ha].
destruct (existsb (fun e => (snd e =? v) && (SegModel.strcmp (fst e) p =? 0)) tab); [apply IH; exact Ha|].
destruct (Z.leb_spec cap (Z.of_nat (length tab))) as [Hc|Hc]; [cbn [fst] in Ha; lia|].
apply IH; exact Ha.
Qed.

Lemma s22_decl_one_skip : forall g tab cap a,
  SegModel.ms_ignore g = true \/ SegModel.m_split (SegModel.ms_name g) = None ->
  SegModel.m_decl_go [g] tab cap a = (a, tab).
Proof.
intros g tab cap a [Hi|Hs]; cbn [SegModel.m_decl_go].
- rewrite Hi. reflexivity.
- destruct (SegModel.ms_ignore g); [reflexivity|]. rewrite Hs. reflexivity.
Qed.

(* turn i changes nothing: the segment is ignored or its name does not split *)
Lemma s22_decl_step_skip : forall l i tab cap,
  (i < length l)%nat -> 0 <= fst (SegModel.m_decl_go (firstn i l) tab cap 0) ->
  (SegModel.ms_ignore (nth i l SegModel.mseg_d) = true \/
   SegModel.m_split (SegModel.ms_name (nth i l SegModel.mseg_d)) = None) ->
  SegModel.m_decl_go (firstn (S i) l) tab cap 0 = SegModel.m_decl_go (firstn i l) tab cap 0.
Proof.
intros l i tab cap Hi Hpos Hskip.
rewrite (s22_firstn_S l i SegModel.mseg_d Hi), (s22_decl_app _ _ _ _ _ Hpos).
rewrite (s22_decl_one_skip _ _ _ _ Hskip).
destruct (SegModel.m_decl_go (firstn i l) tab cap 0). reflexivity.
Qed.

Lemma s22_decl_bound : forall l tab cap a, 0 <= a ->
  0 <= fst (SegModel.m_decl_go l tab cap a) ->
  fst (SegModel.m_decl_go l tab cap a) <= a + Z.of_nat (length l).
Proof.
intros l. induction l as [|g l IH]; intros tab cap a Ha Hpos; cbn [SegModel.m_decl_go length] in Hpos |- *.
- cbn [fst]. lia.
- destruct (SegModel.ms_ignore g); [pose proof (IH tab cap a Ha Hpos); lia|].
  destruct (SegModel.m_split (SegModel.ms_name g)) as [[p v]|]; [|pose proof (IH tab cap a Ha Hpos); lia].
  destruct (existsb (fun e => (snd e =? v) && (SegModel.strcmp (fst e) p =? 0)) tab);
    [pose proof (IH tab cap a Ha Hpos); lia|].
  destruct (Z.leb_spec cap (Z.of_nat (length tab))) as [Hc|Hc]; [cbn [fst] in Hpos; lia|].
  pose proof (IH (tab ++ [(p, v)]) cap (a + 1) ltac:(lia) Hpos). lia.
Qed.

(* at the loop's exit the model's answer is m_declared *)
Lemma s22_decl_all : forall (c : SegModel.mconf) tab cap i,
  (i = length (SegModel.mc_seg c))%nat ->
  SegModel.m_decl_go (firstn i (SegModel.mc_seg c)) tab cap 0 = SegModel.m_declared c tab cap.
Proof.
intros c tab cap i ->. unfold SegModel.m_declared. rewrite firstn_all. reflexivity.
Qed.

(* ================================================================================================= *)
(* ===================== the inner cut points of S14 and what holds at each ========================= *)
(* ================================================================================================= *)
From Stdlib Require Import String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable SegSyms SegList SegPa SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.

(* the inner cut points, as offsets from BASE = 0x84d34 *)
Definition S22_V0 : Z := 0xbc0.    (* 0x858f4, the head of turn i (LT_K858f4) *)
Definition S22_VR : Z := 0xbfc.    (* 0x85930, strrchr returned *)
Definition S22_VD : Z := 0xc40.    (* 0x85974, the head of the digit loop *)
Definition S22_JOIN : Z := 0xc90.  (* 0x859c4, the continue join: v out of scope, the latch *)
Definition S22_VP : Z := 0xce4.    (* 0x85a18, the head of the parent loop *)
Definition S22_VM : Z := 0xd58.    (* 0x85a8c, the parent passed: 88(s1) := tab, the memcpy of the parent *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the name of segment i of the model block, as a C string at m + 256 i *)
Lemma s22_fld_bytes : forall (rd : reader) a bs off n,
  sa_bytes rd a bs -> (off + n <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat off) (seg_spec.fld off n bs).
Proof.
intros rd a bs off n H Hlen k Hk.
unfold seg_spec.fld in Hk |- *. rewrite length_firstn, length_skipn in Hk.
replace (a + Z.of_nat off + Z.of_nat k) with (a + Z.of_nat (off + k)) by lia.
rewrite (H (off + k)%nat ltac:(lia)). f_equal. f_equal.
rewrite nth_firstn, nth_skipn.
destruct (Nat.ltb_spec k n) as [_|Hge]; [reflexivity | lia].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* segment i of the model block, with its 256 bytes at m + 256 i *)
Lemma s22_mseg_at : forall cx i c m (rd : reader),
  lt_cm rd c m (x_run cx) -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  exists f, sa_bytes rd (seg_spec.mseg_addr m i) f /\ seg_spec.mseg_enc (x_seg cx i) f.
Proof.
intros cx i c m rd Hcm Hi. destruct Hcm as [_ Hm].
destruct Hm as (bs & Hbs & Henc).
pose proof Henc as (Hlen & Hn32 & Hsegs & _).
exists (seg_spec.fld (256 * i) 256 bs). split; [|exact (Hsegs i Hi)].
pose proof (Hsegs i Hi) as Hf. destruct Hf as (Hf256 & _).
unfold seg_spec.fld in Hf256. rewrite length_firstn, length_skipn in Hf256.
replace (seg_spec.mseg_addr m i) with (m + Z.of_nat (256 * i))
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
apply (s22_fld_bytes rd m bs (256 * i) 256 Hbs). lia.
Qed.

(* its name field: a C string of at most 15 bytes, with no NUL inside *)
Lemma s22_name_str : forall cx i c m (rd : reader),
  lt_cm rd c m (x_run cx) -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  sa_strz rd (seg_spec.mseg_addr m i) (SegModel.ms_name (x_seg cx i)) /\
  (length (SegModel.ms_name (x_seg cx i)) < 16)%nat /\
  SegModel.nulfree (SegModel.ms_name (x_seg cx i)).
Proof.
intros cx i c m rd Hcm Hi. destruct (s22_mseg_at cx i c m rd Hcm Hi) as (f & Hf & Henc).
pose proof Henc as (Hlen & Hname & _).
destruct Hname as (Hf16 & Hs16 & Hn0 & Hpre).
split; [|split; [exact Hs16 | exact Hn0]].
split; [|exact Hn0].
intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
assert (Hkf : (k < length f)%nat) by (rewrite Hlen; lia).
rewrite (Hf k Hkf). f_equal.
assert (Hk16 : (k < length (seg_spec.fld 0 16 f))%nat) by (rewrite Hf16; lia).
assert (E1 : nth k (seg_spec.zs (seg_spec.fld 0 16 f)) 0 =
             nth k (SegModel.ms_name (x_seg cx i) ++ [0]) 0).
{ rewrite <- Hpre, nth_firstn. destruct (Nat.ltb_spec k (S (length (SegModel.ms_name (x_seg cx i)))));
  [reflexivity | lia]. }
rewrite <- E1. unfold seg_spec.zs.
assert (Hff : nth k (seg_spec.fld 0 16 f) ZB0 = nth k f ZB0).
{ unfold seg_spec.fld. rewrite nth_firstn, nth_skipn.
  destruct (Nat.ltb_spec k 16) as [_|Hge]; [cbn [Nat.add]; reflexivity | rewrite Hf16 in Hk16; lia]. }
rewrite <- Hff. rewrite <- (map_nth bv_unsigned (seg_spec.fld 0 16 f) ZB0 k). reflexivity.
Qed.

(* the slot list of the loop's head, and the one with 88(s1) = tab that the memcpy block adds *)
Definition s22_L (cx : lcx) (i : nat) (c m mt : Z) : list (Z * Z) :=
  LT_LV cx c m ++
  [(96, mt + 16); (104, fst (x_decl cx i)); (112, mt); (120, Z.of_nat (length (snd (x_decl cx i))));
   (128, LT_VIDMAX); (136, LT_MASK); (152, shadow_addr (m + seg_spec.MC_N))].
Definition s22_L8 (cx : lcx) (i : nat) (c m tab mt : Z) : list (Z * Z) :=
  LT_LV cx c m ++
  [(88, tab); (96, mt + 16); (104, fst (x_decl cx i)); (112, mt);
   (120, Z.of_nat (length (snd (x_decl cx i)))); (128, LT_VIDMAX); (136, LT_MASK);
   (152, shadow_addr (m + seg_spec.MC_N))].

(* the five registers the whole turn keeps: s6 = s11 = &m->seg[i], s7 = -8, s9 = i, s10 = -&m->seg[i] *)
Definition s22_rk (m : Z) (i : nat) (regs : bvmap 5 word) : Prop :=
  getr regs 22 = w64 (seg_spec.mseg_addr m i) /\ getr regs 23 = w64 (-8) /\
  getr regs 25 = w64 (Z.of_nat i) /\ getr regs 26 = w64 (- seg_spec.mseg_addr m i) /\
  getr regs 27 = w64 (seg_spec.mseg_addr m i).

(* what every point of S14 keeps: the core, the four blocks, the slots, the model states and the tables *)
Definition s22_inv (cx : lcx) (i : nat) (c m tab mt : Z) (o : lfo) (L : list (Z * Z))
  ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) : Prop :=
  (i < length (SegModel.mc_seg (x_mcF cx)))%nat /\
  0 <= fst (x_decl cx i) /\
  lt_core B MT cx ly S W regs mem md k acc 4 o
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem) mt (x_mtn cx) /\
  lt_slots cx (rdW W mem) L /\
  lt_cm (rdW W mem) c m (x_run cx) /\
  lt_tabs cx (rdW W mem) tab mt (snd (x_decl cx i)).

(* ---------------- 0x85930: strrchr(&m->seg[i].name, '.') returned r ---------------- *)
Definition S22_VR_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (r : Z),
  lt_base B MT cx -> sa_frm0 ->
  s22_inv cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  ((r = 0 /\ SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = None) \/
   (exists j, SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some j /\
              r = seg_spec.mseg_addr m i + Z.of_nat j)) ->
  getr regs 10 = w64 r -> getr regs 19 = w64 (seg_spec.mseg_addr m i) ->
  getr regs 20 = w64 4 -> getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab ->
  s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VR) regs mem md) (lt_post B MT cx).

(* ---------------- 0x85974: the head of the digit loop, t digits read ---------------- *)
Definition S22_VD_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (di t : nat) (v : Z),
  lt_base B MT cx -> sa_frm0 ->
  s22_inv cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (di <> 0)%nat ->
  (t < length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))))%nat ->
  forallb SegModel.isdigit (firstn t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i)))) = true ->
  v = fold_left SegModel.dstep (firstn t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i)))) 0 ->
  0 <= v <= 4094 ->
  getr regs 5 = w64 10 -> getr regs 6 = w64 4094 -> getr regs 17 = w64 (-10) ->
  (* a0 still holds strrchr's answer: the exit 0x85a00 .. 0x85a0c reads it back as di (found by S22P3Digits) *)
  getr regs 10 = w64 (seg_spec.mseg_addr m i + Z.of_nat di) ->
  getr regs 11 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) ->
  getr regs 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) ->
  getr regs 13 = w64 (nth t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) 0) ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 m -> getr regs 18 = w64 v ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 20 = w64 4 ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VD) regs mem md) (lt_post B MT cx).

(* ---------------- 0x85a18: the head of the parent loop, t bytes checked ---------------- *)
Definition S22_VP_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (di t : nat) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s22_inv cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (di <> 0)%nat ->
  SegModel.m_digits (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) 0 = Some vid ->
  1 <= vid <= 4094 ->
  (t < di)%nat ->
  forallb SegModel.h_parent_ok (firstn t (SegModel.ms_name (x_seg cx i))) = true ->
  getr regs 5 = w64 10 ->
  getr regs 10 = w64 (seg_spec.mseg_addr m i + Z.of_nat t) ->
  getr regs 11 = w64 (Z.of_nat di - Z.of_nat t) ->
  getr regs 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat t) ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 m -> getr regs 18 = w64 vid ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 20 = w64 (Z.of_nat di) ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VP) regs mem md) (lt_post B MT cx).

(* ---------------- 0x85a8c: m_split succeeded; 88(s1) := tab, the copy of the parent ---------------- *)
Definition S22_VM_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z) (di : nat) (vid : Z),
  lt_base B MT cx -> sa_frm0 ->
  s22_inv cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) =
    Some (firstn di (SegModel.ms_name (x_seg cx i)), vid) ->
  (0 < di < length (SegModel.ms_name (x_seg cx i)))%nat -> 1 <= vid <= 4094 ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 18 = w64 vid ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 20 = w64 (Z.of_nat di) ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VM) regs mem md) (lt_post B MT cx).

(* ---------------- 0x859c4: the continue join (turn i added nothing) ---------------- *)
Definition S22_JOIN_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base B MT cx -> sa_frm0 ->
  x_decl cx (Datatypes.S i) = x_decl cx i ->
  s22_inv cx i c m tab mt LFO_NV (s22_L cx i c m mt) ly S W regs mem md k acc ->
  getr regs 15 = w64 SHADOW_OFF -> getr regs 16 = w64 m -> getr regs 20 = w64 4 ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 24 = w64 tab -> s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_JOIN) regs mem md) (lt_post B MT cx).

(* ---------------- the six pieces and how they chain ---------------- *)
Definition s22_p1_stmt : Prop := forall i, S22_JOIN_stmt i -> S22_VR_stmt i -> LT_K858f4_stmt B MT i.
Definition s22_p2_stmt : Prop := forall i, S22_JOIN_stmt i -> S22_VD_stmt i -> S22_VR_stmt i.
Definition s22_p3_stmt : Prop := forall i, S22_JOIN_stmt i -> S22_VP_stmt i -> S22_VD_stmt i.
Definition s22_p4_stmt : Prop := forall i, S22_JOIN_stmt i -> S22_VM_stmt i -> S22_VP_stmt i.
Definition s22_p5_stmt : Prop := forall i, LTA_K85ac4 B MT i -> S22_VM_stmt i.
Definition s22_p6_stmt : Prop :=
  forall i, LTA_K858f4 B MT (Datatypes.S i) -> LTA_K85bd0 B MT -> S22_JOIN_stmt i.

Lemma s22_compose :
  s22_p1_stmt -> s22_p2_stmt -> s22_p3_stmt -> s22_p4_stmt -> s22_p5_stmt -> s22_p6_stmt ->
  lt_seg_S14_stmt B MT.
Proof.
intros P1 P2 P3 P4 P5 P6. unfold lt_seg_S14_stmt. intros i HAC4 HNX HBD0.
pose proof (P6 i HNX HBD0) as HJ.
exact (P1 i HJ (P2 i HJ (P3 i HJ (P4 i HJ (P5 i HAC4))))).
Qed.

End e.
End f.
End d.
