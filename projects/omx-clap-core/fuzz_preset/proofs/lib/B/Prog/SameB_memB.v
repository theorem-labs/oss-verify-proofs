(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan #102 pin d663f82d7f48, twin c90d4fa54d43), the walk of same:
   memory facts, part B: what the calls same makes need of the tree at the current point of the walk.
   - strcmp (the wrapper __wrap_strcmp; YGcallMxmn.v astrcmp_realizes_xrom / aj_strcmp_at_xrom): a string of the tree
     (the str field of a number or string node, a key of an object) meets the row's premises (smb_str_ok); the row's
     answer, equal bytes up to the NUL, is equality of the strings (smb_str_eq).
   - bcmp (__wrap_bcmp; abcmp_realizes_xm / aj_bcmp_at_xm): the 8 bytes of a root's num field meet the row's premises
     (smb_num_ok); equal bytes are equal values (smb_num_eq).
   - the slots of the key array: their shadow is addressable (smb_slot_ra).
   - same itself (the tsame_specX, the induction hypothesis): the i-th kid of a container is a tree there, and its
     footprint is below YM05.alloc_ceiling, so apart from every stack window (smb_kid_tree).
   Ported from the image-A walk's lib/A/Prog/Wsame_memB.v (origin/cold/h-hpreset-7-walk-s9-got-rob 9a0674f0b5f2),
   renamed s9_ -> smb_; the ledger carries #102's most / own. No image constant, no address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import SameB_kit SameB_memA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {L : ptable asym} {PA : PAImg L}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator laws at the harness head length cf_head: field 14 (alx_hshadow) is the hidden-head block shadow law,
   field 15 (alx_blocks_tail) the block's tail granule up to (p + req_size n + 7) / 8 * 8 *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx cf_head.
(* the three allocator facts of lib/B/Prog/SameB_walk.v's Section W (derived there from SMB_CF, ARx refining ARcf) *)
Hypothesis SMB_BMAX : forall ly S Hp (W : world pa_segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < cf_malloc_max.
Hypothesis SMB_STK64 : forall ly S Hp (W : world pa_segs) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0.
Hypothesis SMB_FR64 : forall ly S Hp (W : world pa_segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Let HSL : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd := pa_segs_low.
Local Notation PST := (prh_pst (PI := prh_img_B)).

(* helpers: a byte of a value in memory, as the view reads it; a present byte is visible; the header of a node *)
Lemma smbb_aview_vm : forall segs (H : word -> bool) (mem : word -> option byte) a (n : nat) v (j : nat),
  val_mem segs (mrestrict H mem) a n v -> (j < n)%nat -> aview segs H mem (a + Z.of_nat j) = Some (le_byte v n j).
Proof using.
intros segs H mem a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
change (bv_unsigned (Z_to_bv 8 (le_byte v n j)) = le_byte v n j).
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. apply Z.mod_mod. lia.
Qed.

Lemma smbb_garr8_at : forall segs (H : word -> bool) (mem : word -> option byte) x l (j : nat),
  garr8 segs (mrestrict H mem) x l -> (j < length l)%nat -> aview segs H mem (x + Z.of_nat j) = Some (nth j l 0).
Proof using.
intros segs H mem x l j Hg Hj. destruct (Hg j Hj) as [Hv Hr].
pose proof (smbb_aview_vm segs H mem (x + Z.of_nat j) 1 (nth j l 0) 0 Hv ltac:(lia)) as E.
replace (x + Z.of_nat j + Z.of_nat 0) with (x + Z.of_nat j) in E by lia. rewrite E. f_equal.
change (Z.shiftr (nth j l 0 mod 256) 0 mod 256 = nth j l 0).
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (nth j l 0) 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma smbb_aview_pres : forall segs (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> aview segs H mem a <> None.
Proof using. intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma smbb_le_byte_bit : forall v (k : nat) j, (k < 8)%nat -> 0 <= j < 8 ->
  Z.testbit (le_byte v 8 k) j = Z.testbit v (8 * Z.of_nat k + j).
Proof using.
intros v k j Hk Hj. unfold le_byte. replace 256 with (2 ^ 8) by reflexivity.
rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia.
f_equal. lia.
Qed.

Lemma smbb_u64_inj : forall v w, 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  (forall k : nat, (k < 8)%nat -> le_byte v 8 k = le_byte w 8 k) -> v = w.
Proof using.
intros v w Hv Hw E. apply Z.bits_inj'. intros n Hn.
destruct (Z.lt_ge_cases n 64) as [Hl|Hl].
- pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn.
  assert (Hq : 0 <= n / 8 < 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (E (Z.to_nat (n / 8)) ltac:(lia)) as Ek.
  pose proof (smbb_le_byte_bit v (Z.to_nat (n / 8)) (n mod 8) ltac:(lia) Mn) as Bv.
  pose proof (smbb_le_byte_bit w (Z.to_nat (n / 8)) (n mod 8) ltac:(lia) Mn) as Bw.
  rewrite Z2Nat.id in Bv, Bw by lia. rewrite <- Dn in Bv, Bw. rewrite <- Bv, <- Bw, Ek. reflexivity.
- rewrite <- (Z.mod_small v (2 ^ 64)) by lia. rewrite <- (Z.mod_small w (2 ^ 64)) by lia.
  rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma smbb_hdr : forall segs m Lb p t D, pj_nodeR segs m Lb p t D ->
  exists num str kids keys nn cap, pj_hdrR segs m p (tag t) num str kids keys nn cap.
Proof using.
intros segs m Lb p t D H. destruct t; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & nn & cap & Hh & _);
  exists num, str, kids, keys, nn, cap; exact Hh.
Qed.

(* the strcmp row's answer: two strings of a tree are equal exactly when their bytes up to the NUL are *)
Lemma smb_str_eq : forall segs (H : word -> bool) (mem : word -> option byte) (Lb : Z -> Z -> Prop)
    x kx s y ky s',
  pj_cstrR segs (mrestrict H mem) Lb x kx s -> pj_cstrR segs (mrestrict H mem) Lb y ky s' ->
  (Z.of_nat (length s) = Z.of_nat (length s') /\
   forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (x + i) = aview segs H mem (y + i)) <-> s = s'.
Proof using.
intros segs H mem Lb x kx s y ky s' (_ & _ & _ & Fs & Gs) (_ & _ & _ & Fs' & Gs'). split.
- intros (EL & EA). apply smb_list_eq_nth; [lia|].
  intros i Hi.
  assert (Hi1 : (i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  assert (Hi2 : (i < length (s' ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (smbb_garr8_at segs H mem x (s ++ [0]) i Gs Hi1) as Ax.
  pose proof (smbb_garr8_at segs H mem y (s' ++ [0]) i Gs' Hi2) as Ay.
  rewrite app_nth1 in Ax by lia. rewrite app_nth1 in Ay by lia.
  pose proof (EA (Z.of_nat i) ltac:(lia)) as Ei. rewrite Ax, Ay in Ei. injection Ei as Ei.
  transitivity (Some (nth i s 0)); [apply nth_error_nth'; lia|].
  rewrite Ei. symmetry. apply nth_error_nth'. lia.
- intros <-. split; [reflexivity|]. intros i Hi.
  assert (Hj : (Z.to_nat i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (smbb_garr8_at segs H mem x (s ++ [0]) (Z.to_nat i) Gs Hj) as Ax.
  pose proof (smbb_garr8_at segs H mem y (s ++ [0]) (Z.to_nat i) Gs' Hj) as Ay.
  rewrite Z2Nat.id in Ax, Ay by lia. rewrite Ax, Ay. reflexivity.
Qed.

(* the bcmp row's answer: two 8-byte values are equal exactly when their bytes are *)
Lemma smb_num_eq : forall segs (H : word -> bool) (mem : word -> option byte) p q v w,
  rd_u64 segs (mrestrict H mem) p v -> rd_u64 segs (mrestrict H mem) q w ->
  (forall i, 0 <= i < 8 -> aview segs H mem (p + i) = aview segs H mem (q + i)) <-> v = w.
Proof using.
intros segs H mem p q v w (Hv & Vv) (Hw & Vw).
assert (Bp : forall k : nat, (k < 8)%nat -> aview segs H mem (p + Z.of_nat k) = Some (le_byte v 8 k))
  by (intros k Hk; exact (smbb_aview_vm segs H mem p 8 v k Vv Hk)).
assert (Bq : forall k : nat, (k < 8)%nat -> aview segs H mem (q + Z.of_nat k) = Some (le_byte w 8 k))
  by (intros k Hk; exact (smbb_aview_vm segs H mem q 8 w k Vw Hk)).
split.
- intros E. apply smbb_u64_inj; [exact Hv | exact Hw |]. intros k Hk.
  pose proof (E (Z.of_nat k) ltac:(lia)) as Ek. rewrite (Bp k Hk), (Bq k Hk) in Ek. injection Ek as Ek. exact Ek.
- intros <-. intros i Hi.
  pose proof (Bp (Z.to_nat i) ltac:(lia)) as A1. pose proof (Bq (Z.to_nat i) ltac:(lia)) as A2.
  rewrite Z2Nat.id in A1, A2 by lia. rewrite A1, A2. reflexivity.
Qed.

(* a string of the tree (a block of the ledger's Lam, read at the current memory) meets the strcmp row's per-string
   premises at kx = its length, for any call whose sp is at least YM05.alloc_ceiling + ESTACK *)
Lemma smb_str_ok : forall ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 (regsT : bvmap 5 word) x k s,
  prh_ledger (PI := prh_img_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  pj_cstrR pa_segs (mrestrict (w_H W1) mem1) (prh_lin Lam) x k s ->
  YM05.alloc_ceiling + ESTACK <= spZ regsT ->
  0 < x /\ 0 <= Z.of_nat (length s) /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ x + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
  first_byte pa_segs W1 mem1 x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)) /\
  src_ok pa_segs W1 regsT mem1 x (Z.of_nat (length s) + 1) /\
  (forall a, x <= a <= x + Z.of_nat (length s) -> a < YM05.alloc_ceiling) /\
  amem_range x (Z.of_nat (length s) + 1) /\
  range_addressable (aview pa_segs (w_H W1) mem1) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview pa_segs (w_H W1) mem1) x (Z.of_nat (length s) + 1) /\
  (forall a, x + Z.of_nat (length s) < a < x + Z.of_nat (length s) - (x + Z.of_nat (length s)) mod 8 + 8 ->
     aview pa_segs (w_H W1) mem1 a <> None).
Proof using LAWS SMB_BMAX SMB_STK64 SMB_FR64.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 regsT x k s HLED HAR1 EB EH Hc Hsp.
destruct Hc as (Hin & Hk & H32 & Fs & Gs). unfold prh_lin in Hin.
destruct HLED as (_ & _ & HF & _).
pose proof (proj1 (Forall_forall _ _) HF (x, k) Hin) as (Hk0 & Hblk & HHp & _). cbn [fst snd] in Hk0, Hblk, HHp.
rewrite <- EB in Hblk. rewrite <- EH in HHp.
pose proof (@cf_head_nonneg cp) as Hc0.
destruct (alx_blocks pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk) as (_ & H4096 & Hcl & Happ & Hpres & _).
pose proof (SMB_BMAX ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk) as Hmax.
destruct (alx_hshadow pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk HHp) as (Hbs & Hhull).
assert (Erq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
rewrite Erq in Hcl, Happ, Hpres, Hbs, Hhull.
replace (x - cf_head + cf_head) with x in Hbs by lia. replace (x - cf_head + cf_head) with x in Hhull by lia.
replace (k + cf_head - cf_head) with k in Hbs by lia. replace (k + cf_head - cf_head) with k in Hhull by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YG08cf.cf_malloc_max_bound cp) as MMB.
assert (P30 : 2 ^ 30 = 1073741824) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
assert (P63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
unfold ESTACK in *.
assert (PRES : forall a, x <= a < x + k -> aview pa_segs (w_H W1) mem1 a <> None).
{ intros a Ha. apply smbb_aview_pres. exact (proj1 (Hpres a ltac:(lia))). }
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold first_byte. split; [lia|]. split.
  - intros i Hi. exists (nth (Z.to_nat i) s 0).
    assert (Hj : (Z.to_nat i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (smbb_garr8_at pa_segs (w_H W1) mem1 x (s ++ [0]) (Z.to_nat i) Gs Hj) as A.
    rewrite Z2Nat.id in A by lia. rewrite app_nth1 in A by lia. split; [exact A|].
    assert (Hn : In (nth (Z.to_nat i) s 0) s) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Fs _ Hn). cbn beta in *. lia.
  - intros _.
    assert (Hj : (length s < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (smbb_garr8_at pa_segs (w_H W1) mem1 x (s ++ [0]) (length s) Gs Hj) as A.
    rewrite nth_middle in A. exact A. }
split.
{ intros a Ha. split; [apply PRES; lia | unfold ESTACK; lia]. }
split; [intros a Ha; lia|]. split.
{ unfold amem_range. destruct Happ as (Ha0 & [Hl | (Hh1 & Hh2)]); [left | right];
    unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; lia. }
split; [exact (smb_ra_of_bshadow _ x k x (Z.of_nat (length s) + 1) Hbs ltac:(lia) ltac:(lia))|].
split; [apply (smb_hull_sub _ x k x (Z.of_nat (length s) + 1)); [apply Hhull; lia | lia | lia | lia]|].
intros a Ha.
pose proof (Z.div_mod (x + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + k + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (x + k + 7) 8 ltac:(lia)) as M3.
destruct (Z.lt_ge_cases a (x + k)) as [Hak | Hak]; [apply PRES; lia|].
apply (alx_blocks_tail pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 (x - cf_head) (k + cf_head) a HAR1 Hblk). rewrite Erq.
replace (x - cf_head + (k + cf_head)) with (x + k) by lia. lia.
Qed.

(* the 8 bytes of a root's num field (p + 8) meet the bcmp row's per-window premises, for a call whose sp is at most
   the entry sp and at least YM05.alloc_ceiling + 2 * ESTACK. The entry's stack size STK is at least 64: the shadow hull of
   a root at the entry sp starts at the 64-aligned word below it, and the stack's zero shadow covers only
   [ly_stk_lo, ly_stk_hi), with ly_stk_lo <= sp - STK and no alignment known (S9S11Disambiguate's ruling) *)
Lemma smb_num_ok : forall STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1
    (regsT : bvmap 5 word),
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_tree ly S Lam W regs mem p t D ->
  ajournal_x (SK := SK) pa_segs B PST ARx STK (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
  ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  YM05.alloc_ceiling + 2 * ESTACK <= spZ regsT <= spZ regs ->
  64 <= STK ->
  0 <= p + 8 /\ p + 8 + 8 <= 2 ^ 63 /\
  src_ok pa_segs W1 regsT mem1 (p + 8) 8 /\
  (forall a, p + 8 <= a < p + 8 + 8 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
  amem_range (p + 8) 8 /\
  range_addressable (aview pa_segs (w_H W1) mem1) SHADOW_OFF (p + 8) 8 /\
  shadow_hull_vis (aview pa_segs (w_H W1) mem1) (p + 8) 8.
Proof using LAWS SMB_BMAX SMB_STK64 SMB_FR64.
intros STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 regsT
  HAR HLED HT HJ EB EH Hsp HSTK.
pose proof (smb_node_now B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64
  STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 HAR HLED HT HJ EB) as HN1.
pose proof (smb_ra_now B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64
  STK ly S Hp W regs mem md Lam peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 HAR HLED HT HJ EB EH) as HRA1.
destruct HT as (_ & Hh & _).
pose proof HJ as (HAR1 & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct (smbb_hdr _ _ _ _ _ _ HN1) as (num & str & kids & keys & nn & cap & ((Hal8 & _) & _ & (Hnum0 & Hnum) & _)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
assert (P63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
assert (HP8 : forall a, p + 8 <= a < p + 8 + 8 -> aview pa_segs (w_H W1) mem1 a <> None).
{ intros a Ha. pose proof (smbb_aview_vm pa_segs (w_H W1) mem1 (p + 8) 8 num (Z.to_nat (a - (p + 8))) Hnum ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. replace (p + 8 + (a - (p + 8))) with a in E by lia. rewrite E. discriminate. }
assert (FIN : 0 <= p /\ p + 56 <= 2 ^ 47 /\ (forall a, p + 8 <= a < p + 16 -> a < YM05.alloc_ceiling \/ spZ regs <= a) /\
  amem_range (p + 8) 8 /\ shadow_hull_vis (aview pa_segs (w_H W1) mem1) (p + 8) 8).
{ destruct Hh as [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
  - (* a harness block: the hidden-head shadow law at the later state *)
    destruct HLED as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & HHp & _).
    cbn [fst snd] in Hm0, Hblk, HHp.
    destruct (alx_blocks pa_segs B ARx LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hcl & Happ & _).
    assert (Erq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
    rewrite Erq in Hcl, Happ.
    rewrite <- EB in Hblk. rewrite <- EH in HHp.
    destruct (alx_hshadow pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk HHp) as (_ & Hhull).
    rewrite Erq in Hhull. replace (b - cf_head + cf_head) with b in Hhull by lia.
    replace (m + cf_head - cf_head) with m in Hhull by lia.
    split; [lia|]. split; [lia|]. split; [intros a Ha; left; lia|]. split.
    + unfold amem_range. destruct Happ as (Ha0 & [Hl | (Hh1 & Hh2)]); [left | right];
        unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; lia.
    + apply (smb_hull_sub _ b m (p + 8) 8); [apply Hhull; lia | lia | lia | lia].
  - (* a fake frame: its shadow is present at the later state (ARx_frames_law), the frame 64-aligned *)
    destruct (frames_bounds_x pa_segs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
    assert (Hin1 : In (cid, pos) (frames S1)) by (rewrite Hfr; exact Hin).
    destruct (alx_layout pa_segs B ARx LAWS ly S Hp W mem md ly1 HAR Hly) as (_ & Efa & _).
    destruct (SMB_FR64 ly1 S1 Hp1 W1 mem1 md1 cid pos HAR1 Hin1) as (A1 & A2).
    destruct (alx_frames pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 cid pos HAR1 Hin1) as (_ & _ & _ & Hsh).
    rewrite (Efa cid pos) in A1, Hsh.
    set (fa := frame_addr ly cid pos) in *. set (fs := fs_frame_bytes cid) in *.
    split; [lia|]. split; [lia|]. split; [intros a Ha; left; lia|]. split.
    + unfold amem_range. destruct Hfa as (Ha0 & [Hl | (Hh1 & Hh2)]); [left | right];
        unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; lia.
    + pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa8. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as Mfa8.
      pose proof (Z.div_mod fa 64 ltac:(lia)) as Dfa64. pose proof (Z.mod_pos_bound fa 64 ltac:(lia)) as Mfa64.
      pose proof (Z.div_mod fs 8 ltac:(lia)) as Dfs8. pose proof (Z.mod_pos_bound fs 8 ltac:(lia)) as Mfs8.
      pose proof (Z.div_mod fs 64 ltac:(lia)) as Dfs64. pose proof (Z.mod_pos_bound fs 64 ltac:(lia)) as Mfs64.
      assert (Fa8 : fa mod 8 = 0) by lia. assert (Fs8 : fs mod 8 = 0) by lia.
      apply (smb_hull_al64 _ fa (fa + fs) (p + 8) 8); [exact A1 | | lia | lia | lia |].
      * pose proof (Z.div_mod (fa + fs) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (fa + fs) 64 ltac:(lia)). lia.
      * intros a Ha Ha8.
        assert (Ea : a / 8 = fa / 8 + (a - fa) / 8).
        { assert (E1 : a = (a - fa) + (fa / 8) * 8) by lia. rewrite E1 at 1. rewrite Z.div_add by lia. lia. }
        assert (Hi : 0 <= (a - fa) / 8 < fs / 8).
        { pose proof (Z.div_mod (a - fa) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a - fa) 8 ltac:(lia)). lia. }
        destruct (Hsh _ Hi) as (Hpr & _).
        rewrite Ea. replace (SHADOW_OFF + (fa / 8 + (a - fa) / 8)) with (shadow_addr fa + (a - fa) / 8)
          by (unfold shadow_addr; lia).
        apply smbb_aview_pres. exact Hpr.
  - (* the real stack: its zero shadow at the later state (ARx_zshadow_byte_law), the top 64-aligned *)
    destruct Hstk as (Hal16 & HS0 & Hceil & Hlo & Hhi & H47 & _).
    pose proof (SMB_STK64 ly S Hp W mem md HAR) as Hst64.
    destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
    split; [lia|]. split; [lia|]. split; [intros a Ha; right; lia|]. split.
    + unfold amem_range. right. unfold kHighMemBeg, kHighMemEnd in *. lia.
    + pose proof (Z.div_mod (p + 8) 64 ltac:(lia)) as D64. pose proof (Z.mod_pos_bound (p + 8) 64 ltac:(lia)) as M64.
      apply (smb_hull_al64 _ (64 * ((p + 8) / 64)) (ly_stk_hi ly) (p + 8) 8);
        [rewrite Z.mul_comm; apply Z.mod_mul; lia | exact Hst64 | lia | lia | lia |].
      intros a Ha Ha8.
      rewrite (alx_zshadow_byte pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 a HAR1) by (rewrite Elo, Ehi; lia).
      discriminate. }
destruct FIN as (F0 & F47 & FW & FA & FH).
unfold ESTACK in *.
split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [exact (HP8 a Ha)|]. destruct (FW a ltac:(lia)); unfold ESTACK; lia. }
split.
{ intros a Ha. destruct (FW a ltac:(lia)); lia. }
split; [exact FA|]. split; [|exact FH].
exact (smb_ra_sub _ _ p 56 (p + 8) 8 HRA1 ltac:(lia) ltac:(lia)).
Qed.

(* bytes inside a block of the ledger's Lam have an addressable shadow at the current state *)
Lemma smb_slot_ra : forall ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 a k x m,
  prh_ledger (PI := prh_img_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  In (a, k) Lam -> a <= x -> 0 <= m -> x + m <= a + k ->
  range_addressable (aview pa_segs (w_H W1) mem1) SHADOW_OFF x m.
Proof using LAWS SMB_BMAX SMB_STK64 SMB_FR64.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 a k x m HLED HAR1 EB EH Hin H1 H2 H3.
destruct (Z.eq_dec m 0) as [-> | Hm]; [intros y Hy; lia|].
destruct HLED as (_ & _ & HF & _).
pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk0 & Hblk & HHp & _). cbn [fst snd] in Hk0, Hblk, HHp.
rewrite <- EB in Hblk. rewrite <- EH in HHp.
pose proof (@cf_head_nonneg cp) as Hc0.
destruct (alx_hshadow pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk HHp) as (Hbs & _).
assert (Erq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
rewrite Erq in Hbs. replace (a - cf_head + cf_head) with a in Hbs by lia.
replace (k + cf_head - cf_head) with k in Hbs by lia.
exact (smb_ra_of_bshadow _ a k x m Hbs H1 H3).
Qed.

(* the i-th kid of a container (its kid array a block (kids, c) of Lam) is a tree at the current state, for any
   registers of the callee, and its footprint lies below YM05.alloc_ceiling *)
Lemma smb_kid_tree : forall ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 (regs1 : bvmap 5 word)
    kids c (i : nat) u D1,
  prh_ledger (PI := prh_img_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  In (kids, c) Lam -> 56 * Z.of_nat i + 56 <= c ->
  pj_nodeR pa_segs (mrestrict (w_H W1) mem1) (prh_lin Lam) (kids + 56 * Z.of_nat i) u D1 ->
  prhex_tree ly1 S1 Lam W1 regs1 mem1 (kids + 56 * Z.of_nat i) u D1 /\
  (forall z, pj_footR (kids + 56 * Z.of_nat i) D1 z -> 0 <= z < YM05.alloc_ceiling).
Proof using LAWS SMB_BMAX SMB_STK64 SMB_FR64.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 regs1 kids c i u D1 HLED HAR1 EB EH Hin Hc Hn.
pose proof (@cf_head_nonneg cp) as Hc0.
assert (BLK : forall a k, In (a, k) Lam -> 4096 <= a /\ a + k <= YM05.alloc_ceiling).
{ intros a k Hak. destruct HLED as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a, k) Hak) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
  rewrite <- EB in Hblk.
  destruct (alx_blocks pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk) as (_ & H4096 & Hcl & _).
  assert (Hkc : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hkc) as [_ Hq]. lia. }
split.
- unfold prhex_tree, prhex_home. split; [exact Hn|]. split.
  + left. exists kids, c. split; [exact Hin|]. lia.
  + split.
    * exact (smb_slot_ra ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 kids c (kids + 56 * Z.of_nat i) 56
        HLED HAR1 EB EH Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    * (* the kid root's hull: inside the kid array's user range, whose hull the hidden-head law gives *)
      pose proof HLED as (_ & _ & HF & _).
      pose proof (proj1 (Forall_forall _ _) HF (kids, c) Hin) as (Hk0 & Hblk & HHp & _). cbn [fst snd] in Hk0, Hblk, HHp.
      rewrite <- EB in Hblk. rewrite <- EH in HHp.
      destruct (alx_hshadow pa_segs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk HHp) as (_ & Hhv).
      assert (Erq : req_size (c + cf_head) = c + cf_head)
        by (unfold req_size; destruct (Z.eqb_spec (c + cf_head) 0); lia).
      rewrite Erq in Hhv. replace (kids - cf_head + cf_head) with kids in Hhv by lia.
      replace (c + cf_head - cf_head) with c in Hhv by lia.
      apply (smb_hull_sub _ kids c); [apply Hhv; lia | lia | lia | lia].
- intros z [Hz | (b & Hb & Hz)].
  + destruct (BLK kids c Hin). lia.
  + assert (HD : Forall (fun b => prh_lin Lam (fst b) (snd b)) D1) by (eapply smb_D_lblk; exact Hn).
    pose proof (proj1 (Forall_forall _ _) HD b Hb) as Hl.
    destruct b as [b0 b1]. cbn [fst snd] in Hl. unfold prh_lin in Hl. unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
    destruct (BLK b0 b1 Hl). lia.
Qed.
End m.
