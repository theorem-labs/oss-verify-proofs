(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module paths and module names changed; 139 of its 188 lines of code are new or changed and 260 lines of the source are left out. *)
(* check_marks (fuzz_link.asan 0x8848c) on image A: the support facts of its walk (lib/A/Prog/check_marks.v, contract
   lib/A/Prog/check_marks_c.v `check_marks_acontract`, K = CHECK_MARKS_AK = 32 + 2 * ESTACK = 8224). They are the
   facts lib/A/Prog/fuzz_if_nametoindex.v proves for its own walk (its ix_ lemmas), with check_marks' K:
   - views: cm_grow (a present byte stays present), cm_cstr_frame and cm_val_frame (a C string and a value stay
     where their bytes did not change), cm_cstr_frame_sep and cm_arg_frame (the same for a string apart from the
     32-byte frame and the strcmp wrapper's window, when a run changed the memory only in [sp - K, sp));
   - sub-ranges of the instrumented check's facts: cm_ra_sub2, cm_hull_sub2, cm_amem_sub2;
   - cm_src_ok: the strcmp wrapper's `src_ok` of the first kk + 1 bytes of a C string;
   - cm_shadow_low, cm_shadow_low8: the shadow byte of an application address is below alloc_ceiling;
   - cm_argf, cm_argf_of: the six facts of index_of_c.v's `astrcmp_arg` that the strcmp wrapper's contract
     (lib/Reusable/AStrcmpDef.v) reads; its tail clause stays behind;
   - cm_set_fs_id, cm_strcmp_res_cases, cm_res_eq, cm_res_ne: the Post's state and the wrapper's answer word;
   - cm_field: a field of a byte block read as a value (the two counts got->n and m->n_mark).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk index_of_c check_marks_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.

(* ---- the Post's state and the strcmp wrapper's answer word ---- *)

Lemma cm_set_fs_id : forall (S : astate), S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

Lemma cm_strcmp_res_cases : forall c1 c2,
  AStrcmpDef.strcmp_res c1 c2 = 0 \/ AStrcmpDef.strcmp_res c1 c2 = -1 \/ AStrcmpDef.strcmp_res c1 c2 = 1.
Proof.
  intros c1 c2. unfold AStrcmpDef.strcmp_res.
  destruct (c1 =? c2); [left; reflexivity|]. destruct (c1 <? c2); [right; left; reflexivity | right; right; reflexivity].
Qed.

Lemma cm_res_eq : forall c1 c2, bv_unsigned (w64 (AStrcmpDef.strcmp_res c1 c2)) = 0 ->
  AStrcmpDef.strcmp_res c1 c2 = 0.
Proof.
  intros c1 c2 H.
  destruct (cm_strcmp_res_cases c1 c2) as [Eq|[Eq|Eq]]; rewrite Eq in H |- *; [reflexivity| |];
    exfalso; unfold w64 in H; rewrite Z_to_bv_unsigned in H;
    unfold bv_wrap, bv_modulus in H; change (2 ^ Z.of_N 64) with (2 ^ 64) in H.
  - assert (Hm : (-1) mod 2 ^ 64 = 2 ^ 64 - 1).
    { replace (-1) with ((2 ^ 64 - 1) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
      apply Z.mod_small. lia. }
    lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma cm_res_ne : forall c1 c2, bv_unsigned (w64 (AStrcmpDef.strcmp_res c1 c2)) <> 0 ->
  AStrcmpDef.strcmp_res c1 c2 <> 0.
Proof.
  intros c1 c2 H Eq. apply H. rewrite Eq. unfold w64. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_0_l. lia.
Qed.

(* ---- views and the facts that travel with them ---- *)

Lemma cm_grow : forall (H : word -> bool) (m m' : word -> option byte),
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity].
Qed.

Lemma cm_cstr_frame : forall (m m' : word -> option byte) x s,
  acstr_at SEGS m x s ->
  (forall a, x <= a <= x + Z.of_nat (length s) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  acstr_at SEGS m' x s.
Proof.
  intros m m' x s ((H0 & Hl & Hb) & Hn) HK. split; [|exact Hn]. split; [exact H0|]. split; [exact Hl|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HK (x + Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

Lemma cm_val_frame : forall (m m' : word -> option byte) a (n : nat) v,
  val_mem SEGS m a n v -> (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m' a n v.
Proof. intros m m' a n v HV HK j Hj. rewrite (HK (a + Z.of_nat j) ltac:(lia)). exact (HV j Hj). Qed.

Lemma cm_ra_sub2 : forall (rd : reader) a n a' n',
  range_addressable rd SHADOW_OFF a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  range_addressable rd SHADOW_OFF a' n'.
Proof. intros rd a n a' n' H H1 H2 H3 x Hx. apply H. lia. Qed.

Lemma cm_hull_sub2 : forall (rd : reader) a n n',
  shadow_hull_vis rd a n -> 1 <= n' -> n' <= n ->
  shadow_hull_vis rd a n'.
Proof.
  intros rd a n n' H H1 H2 s Hs. apply H.
  pose proof (shadow_mono (a + n' - 1) (a + n - 1) ltac:(lia)) as Hm.
  unfold shadow_addr in *. split; [lia|].
  pose proof (Z.div_le_mono (SHADOW_OFF + (a + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma cm_amem_sub2 : forall x n n', amem_range x n -> 0 <= n' -> n' <= n -> amem_range x n'.
Proof. intros x n n' H H1 H2. unfold amem_range in *. destruct H as [H|[H H']]; [left; lia | right; split; lia]. Qed.

Lemma cm_src_ok : forall (W : world SEGS) rgs (m : word -> option byte) x s kk,
  acstr_at SEGS (rdW W m) x s -> 0 <= kk <= Z.of_nat (length s) ->
  (forall a, x <= a < x + (kk + 1) -> ~ (spZ rgs - ESTACK <= a < spZ rgs)) ->
  src_ok SEGS W rgs m x (kk + 1).
Proof.
  intros W rgs m x s kk ((_ & _ & Hb) & _) Hkk Hsep a Ha. split; [|exact (Hsep a Ha)].
  assert (Hi : (Z.to_nat (a - x) < length (s ++ [zb 0]))%nat)
    by (rewrite length_app; cbn [length]; lia).
  pose proof (Hb (Z.to_nat (a - x)) Hi) as Hby.
  replace (x + Z.of_nat (Z.to_nat (a - x))) with a in Hby by lia.
  unfold aview. rewrite Hby.
  destruct (nth_error (s ++ [zb 0]) (Z.to_nat (a - x))) as [b|] eqn:E; [discriminate|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* ---- the strcmp wrapper's facts of one string, and how they travel ---- *)

(* the part of index_of_c.v's astrcmp_arg the walk moves from one memory to the next: the wrapper's contract
   (AStrcmpDef) reads no tail byte, so the tail conjunct never has to travel *)
Definition cm_argf (rgs : bvmap 5 word) (m : word -> option byte) (x : Z) (s : list byte) : Prop :=
  0 < x /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ amem_range x (Z.of_nat (length s) + 1) /\
  range_addressable (ard SEGS m) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (ard SEGS m) x (Z.of_nat (length s) + 1) /\
  apart_frame rgs CHECK_MARKS_AK x (Z.of_nat (length s) + 1).

Lemma cm_argf_of : forall rgs m x s,
  astrcmp_arg SEGS rgs CHECK_MARKS_AK m x s -> cm_argf rgs m x s.
Proof. intros rgs m x s (H1 & H2 & H3 & H4 & H5 & H6 & _). repeat split; assumption. Qed.

Lemma cm_shadow_low : forall x, 0 <= x < kHighMemEnd -> 0 <= shadow_addr x < alloc_ceiling.
Proof.
  intros x Hx. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (shadow_addr_bounds x Hx) as Hsb. unfold kHighShadowEnd in Hsb. lia.
Qed.

Lemma cm_shadow_low8 : forall x, 0 <= x < kHighMemEnd -> 0 <= shadow_addr x /\ shadow_addr x + 8 < alloc_ceiling.
Proof.
  intros x Hx. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (shadow_addr_bounds x Hx) as Hsb. unfold kHighShadowEnd in Hsb. lia.
Qed.

Lemma cm_arg_frame : forall (W : world SEGS) (rgs : bvmap 5 word) (m m' : word -> option byte) x s,
  cm_argf rgs (rdW W m) x s ->
  alloc_ceiling <= spZ rgs - CHECK_MARKS_AK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rgs - CHECK_MARKS_AK <= a < spZ rgs) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  cm_argf rgs (rdW W m') x s.
Proof.
  intros W rgs m m' x s (H1 & H2 & H3 & H4 & H5 & H6) Hceil UN.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSH : forall y, x <= y < x + (Z.of_nat (length s) + 1) ->
    aview SEGS (w_H W) m' (shadow_addr y) = aview SEGS (w_H W) m (shadow_addr y)).
  { intros y Hy. pose proof (cm_shadow_low y ltac:(unfold amem_range, kHighMemBeg, kLowMemEnd in H3; lia)) as Hs.
    apply UN; lia. }
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply (ra_shadow_eq (ard SEGS (rdW W m))); [exact H4 | exact HSH]|].
  split; [|exact H6].
  intros sadr Hsadr.
  assert (Hlo : 0 <= shadow_addr x /\ shadow_addr x + 8 < alloc_ceiling)
    by (apply cm_shadow_low8; unfold amem_range, kHighMemBeg, kLowMemEnd in H3; lia).
  assert (Hhi : 0 <= shadow_addr (x + (Z.of_nat (length s) + 1) - 1) /\
                shadow_addr (x + (Z.of_nat (length s) + 1) - 1) + 8 < alloc_ceiling)
    by (apply cm_shadow_low8; unfold amem_range, kHighMemBeg, kLowMemEnd in H3; lia).
  pose proof (Z_div_mod_eq_full (shadow_addr x) 8) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as M1.
  pose proof (Z_div_mod_eq_full (shadow_addr (x + (Z.of_nat (length s) + 1) - 1)) 8) as D2.
  pose proof (Z.mod_pos_bound (shadow_addr (x + (Z.of_nat (length s) + 1) - 1)) 8 ltac:(lia)) as M2.
  assert (HEq : ard SEGS (rdW W m') sadr = ard SEGS (rdW W m) sadr)
    by exact (UN sadr ltac:(lia) ltac:(lia)).
  rewrite HEq. exact (H5 sadr Hsadr).
Qed.

Lemma cm_cstr_frame_sep : forall (W : world SEGS) (rgs : bvmap 5 word) (m m' : word -> option byte) x s,
  acstr_at SEGS (rdW W m) x s ->
  apart_frame rgs CHECK_MARKS_AK x (Z.of_nat (length s) + 1) ->
  amem_range x (Z.of_nat (length s) + 1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rgs - CHECK_MARKS_AK <= a < spZ rgs) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  acstr_at SEGS (rdW W m') x s.
Proof.
  intros W rgs m m' x s HC Hpart Hmem UN.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((Hx0 & Hxl & _) & _).
  rewrite length_app in Hxl. cbn [length] in Hxl.
  apply (cm_cstr_frame (rdW W m)); [exact HC|].
  intros a Ha. apply (mbyte_of_aview SEGS).
  unfold apart_frame in Hpart.
  apply UN; destruct Hpart as [Hp|Hp]; lia.
Qed.

(* ---- a field of a byte block, as the entry state needs it ---- *)

Lemma cm_field : forall (m : word -> option byte) p bs off (n : nat),
  au8arr SEGS m p bs -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length bs) ->
  val_mem SEGS m (p + off) n (rdn bs off (Z.of_nat n)).
Proof. intros m p bs off n [Hab _] Hoff Hn. apply val_mem_of_abytes; [exact Hab | exact Hoff | lia]. Qed.

End w.
