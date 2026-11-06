(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses changed; 684 of its 824 lines of code are new or changed and 5925 lines of the source are left out. *)
(* Segment E of LLVMFuzzerTestOneInput's walk on image B (fuzz_identity.asan-ubsan), BASE + 0xff0 .. BASE + 0x1080
   (0x81764 .. 0x817f4, 36 slots): seg_E_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v, from inv_exit (the record
   loop's exit) to inv_E_end.

   The code (the neutral listing of fuzz_identity.asan-ubsan):
     0x81764 .. 0x8176c   x22 := &hw (mf+32), x19 := hw.have (mf+24), the low 4 bytes of x19 stored at &hw
     0x81770 .. 0x81774   a0 := &id (mf+184), the call of reac_box_family_of (BASE + 0x1004 is its return)
     0x81778 .. 0x8177c   x18 := the result; when hw.have = 0 the run goes to 0x817c4
     0x81780 .. 0x81794   x19 := 0, x22 := &hw + 4, x21 := HW_TABLE (object 6), x20 := HW_TABLE + 4, x23 := -36
     0x81798 .. 0x817b4   the loop over the three rows: bcmp (x22, x20, 8) at 0x817a4 (BASE + 0x1034 is its
                          return), on 0 to 0x817d0, else x19 -= 12, x20 += 12 and back while x19 <> -36
     0x817b8 .. 0x817c0   no row is equal: a0 := 0, a4 := the shadow base (mf+168), to 0x817ec
     0x817c4 .. 0x817cc   hw.have = 0: a0 := 0, a4 := the shadow base, to 0x817f0
     0x817d0 .. 0x817e8   row j is equal: the shadow test of HW_TABLE + 12 j (the report at 0x82670 is not
                          reached: the table is a registered global) and a0 := its 4-byte family field
     0x817ec              x23 := the frame's shadow address (mf+160)
     0x817f0              a0 <> x18 goes to the abort at 0x82614: not reached, both are the model's family
   The family the library computes from `id` (reac_box_family_of, famof_res) and the one the harness computes from
   `hw` are equal in the plain model (SlotModel.rec_P7), which decides the test at 0x817f0. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_E_hand_stmt
LLVMFuzzerTestOneInput_seg_E_hand_tail LLVMFuzzerTestOneInput_seg_E_hand_fin LLVMFuzzerTestOneInput_seg_E_hand_loop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_box_family_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the model: the two family computations agree --------------------------------------------------------- *)
Lemma e_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.
Lemma e_have01 : forall inp i, SlotModel.rec_have inp i = 0 \/ SlotModel.rec_have inp i = 1.
Proof. intros inp i. unfold SlotModel.rec_have. destruct (SlotModel.rec_hw inp i); [right | left]; reflexivity. Qed.
Lemma e_HWT_len : forall j, (j < 3)%nat -> length (SlotModel.HWT j) = 8%nat.
Proof. intros j Hj. destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia]. Qed.
(* Row j of the harness's table: the family field at 12 j, the eight hw bytes at 12 j + 4. *)
Lemma e_HWT_rows : forall j i, (j < 3)%nat -> (i < 8)%nat -> nth i (SlotModel.HWT j) 0 = nth (12 * j + 4 + i) HW_ROWS 0.
Proof.
intros j i Hj Hi.
destruct j as [|[|[|j]]]; [| | | lia]; (do 8 (destruct i as [|i]; [reflexivity|])); lia.
Qed.
Lemma e_l8 : forall l1 l2 : list Z, length l1 = 8%nat -> length l2 = 8%nat ->
  (forall i, (i < 8)%nat -> nth i l1 0 = nth i l2 0) -> l1 = l2.
Proof. intros l1 l2 H1 H2 H. apply nth_ext with (d := 0) (d' := 0); [lia|]. intros n Hn. apply H. lia. Qed.
Lemma e_nth_map_bv : forall (hw : list byte) n, (n < length hw)%nat ->
  nth n (map (fun b : byte => bv_unsigned b) hw) 0 = bv_unsigned (nth n hw (Z_to_bv 8 0)).
Proof.
intros hw n Hn. rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0))) by (rewrite length_map; lia).
apply map_nth.
Qed.
(* Eight bytes read at xa equal row j of the table at ta (both in the reader rdr) iff the bytes are HWT j. *)
Lemma e_row_iff : forall (rdr : reader) (xa ta : Z) (hw : list byte) (j : nat),
  length hw = 8%nat -> (j < 3)%nat ->
  (forall n, (n < 8)%nat -> rdr (xa + Z.of_nat n) = Some (bv_unsigned (nth n hw (Z_to_bv 8 0)))) ->
  (forall n, (n < 36)%nat -> rdr (ta + Z.of_nat n) = Some (nth n HW_ROWS 0)) ->
  ((forall i, 0 <= i < 8 -> rdr (xa + i) = rdr (ta + 12 * Z.of_nat j + 4 + i)) <->
   map (fun b : byte => bv_unsigned b) hw = SlotModel.HWT j).
Proof.
intros rdr xa ta hw j Hl Hj Hx Ht. split.
- intros H. apply e_l8; [rewrite length_map; exact Hl | apply e_HWT_len; exact Hj |].
  intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)).
  rewrite (Hx i Hi) in H.
  replace (ta + 12 * Z.of_nat j + 4 + Z.of_nat i) with (ta + Z.of_nat (12 * j + 4 + i)) in H by lia.
  rewrite (Ht (12 * j + 4 + i)%nat ltac:(lia)) in H.
  rewrite (e_HWT_rows j i Hj Hi), e_nth_map_bv by lia. congruence.
- intros H i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  assert (Hi' : (Z.to_nat i < 8)%nat) by lia. set (n := Z.to_nat i) in *.
  rewrite (Hx n Hi').
  replace (ta + 12 * Z.of_nat j + 4 + Z.of_nat n) with (ta + Z.of_nat (12 * j + 4 + n)) by lia.
  rewrite (Ht (12 * j + 4 + n)%nat ltac:(lia)). f_equal.
  rewrite <- (e_HWT_rows j n Hj Hi'), <- H, e_nth_map_bv by lia. reflexivity.
Qed.
Lemma e_FAM_range : forall idb, 0 <= SlotModel.FAM idb <= 3.
Proof.
intros idb. unfold SlotModel.FAM, reac_box_family_of_c.FAMOF_FAM.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.
Lemma e_sx32_small : forall v, 0 <= v <= 3 -> reac_box_family_of.famof_sx32 v = v.
Proof. intros v Hv. unfold reac_box_family_of.famof_sx32. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
(* The library's result is FAM of the box, when the box's bytes and the table's rows are in the reader. *)
Lemma e_famof_FAM : forall (rdr : reader) (p t r : Z) (idb : list byte),
  length idb = 38%nat -> p <> 0 ->
  (forall n, (n < 38)%nat -> rdr (p + Z.of_nat n) = Some (bv_unsigned (nth n idb (Z_to_bv 8 0)))) ->
  (forall n, (n < 36)%nat -> rdr (t + Z.of_nat n) = Some (nth n HW_ROWS 0)) ->
  reac_box_family_of.famof_res rdr p t 1 2 3 r -> r = SlotModel.FAM idb.
Proof.
intros rdr p t r idb Hl Hp Hx Ht Hres.
set (hw := firstn 8 (skipn 28 idb)).
assert (Hhl : length hw = 8%nat) by (subst hw; rewrite length_firstn, length_skipn; lia).
assert (Hhx : forall n, (n < 8)%nat -> rdr (p + 28 + Z.of_nat n) = Some (bv_unsigned (nth n hw (Z_to_bv 8 0)))).
{ intros n Hn. subst hw. rewrite nth_firstn. destruct (Nat.ltb_spec n 8) as [_|Hc]; [|lia]. rewrite nth_skipn.
  replace (p + 28 + Z.of_nat n) with (p + Z.of_nat (28 + n)) by lia. apply Hx. lia. }
assert (R : forall i : nat, (i < 3)%nat ->
  (reac_box_family_of.famof_row rdr p t (Z.of_nat i) <-> map (fun b : byte => bv_unsigned b) hw = SlotModel.HWT i)).
{ intros i Hi. unfold reac_box_family_of.famof_row.
  rewrite <- (e_row_iff rdr (p + 28) t hw i Hhl Hi Hhx Ht). split; intros H j Hj; exact (H j Hj). }
assert (H36 : rdr (p + 36) = Some (bv_unsigned (nth 36 idb (Z_to_bv 8 0)))) by exact (Hx 36%nat ltac:(lia)).
pose proof (R 0%nat ltac:(lia)) as R0. pose proof (R 1%nat ltac:(lia)) as R1. pose proof (R 2%nat ltac:(lia)) as R2.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ SlotModel.HWT nth] in R0, R1, R2.
unfold SlotModel.FAM, reac_box_family_of_c.FAMOF_FAM. cbv zeta. change (1 =? 0) with false. cbv iota.
fold hw.
destruct Hres as [(Hp0 & _) | [(_ & H0 & ->) | [(_ & Hn0 & Hr0 & ->) | [(_ & Hn0 & Hr0 & Hr1 & ->) |
  [(_ & Hn0 & Hr0 & Hr1 & Hr2 & ->) | (_ & Hn0 & Hr0 & Hr1 & Hr2 & ->)]]]]].
- contradiction.
- rewrite H36 in H0. injection H0 as H0. rewrite H0. reflexivity.
- rewrite H36 in Hn0. destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [E|_]; [rewrite E in Hn0; contradiction|].
  apply R0 in Hr0. destruct (list_eq_dec Z.eq_dec _ _) as [_|N]; [reflexivity | contradiction].
- rewrite H36 in Hn0. destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [E|_]; [rewrite E in Hn0; contradiction|].
  apply R1 in Hr1. rewrite R0 in Hr0.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [_|N]; [reflexivity | contradiction].
- rewrite H36 in Hn0. destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [E|_]; [rewrite E in Hn0; contradiction|].
  apply R2 in Hr2. rewrite R0 in Hr0. rewrite R1 in Hr1.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW3) as [_|N]; [reflexivity | contradiction].
- rewrite H36 in Hn0. destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [E|_]; [reflexivity|].
  rewrite R0 in Hr0. rewrite R1 in Hr1. rewrite R2 in Hr2.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW3) as [E|_]; [contradiction | reflexivity].
Qed.
(* The harness's loop: row j is the first equal row, or none is. *)
Lemma e_fam_cmp_hit : forall (hw : list byte) j, (j < 3)%nat ->
  (forall j', (j' < j)%nat -> map (fun b : byte => bv_unsigned b) hw <> SlotModel.HWT j') ->
  map (fun b : byte => bv_unsigned b) hw = SlotModel.HWT j -> SlotModel.fam_cmp hw = Z.of_nat j + 1.
Proof.
intros hw j Hj Hm He. unfold SlotModel.fam_cmp. cbv zeta.
destruct j as [|[|[|j]]]; [| | | lia].
- cbn [SlotModel.HWT nth] in He.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [_|N]; [reflexivity | contradiction].
- cbn [SlotModel.HWT nth] in He. pose proof (Hm 0%nat ltac:(lia)) as M0. cbn [SlotModel.HWT nth] in M0.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [_|N]; [reflexivity | contradiction].
- cbn [SlotModel.HWT nth] in He. pose proof (Hm 0%nat ltac:(lia)) as M0. pose proof (Hm 1%nat ltac:(lia)) as M1.
  cbn [SlotModel.HWT nth] in M0, M1.
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [E|_]; [contradiction|].
  destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW3) as [_|N]; [reflexivity | contradiction].
Qed.
Lemma e_fam_cmp_none : forall (hw : list byte),
  (forall j', (j' < 3)%nat -> map (fun b : byte => bv_unsigned b) hw <> SlotModel.HWT j') -> SlotModel.fam_cmp hw = 0.
Proof.
intros hw Hm. pose proof (Hm 0%nat ltac:(lia)) as M0. pose proof (Hm 1%nat ltac:(lia)) as M1.
pose proof (Hm 2%nat ltac:(lia)) as M2. cbn [SlotModel.HWT nth] in M0, M1, M2.
unfold SlotModel.fam_cmp. cbv zeta.
destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [E|_]; [contradiction|].
destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW3) as [E|_]; [contradiction | reflexivity].
Qed.

(* ---- bytes and shadow kept ------------------------------------------------------------------------------- *)
Section h.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma e_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma e_aview_garr8 : forall H (m : word -> option byte) a l n,
  garr8 segs (mrestrict H m) a l -> (n < length l)%nat -> aview segs H m (a + Z.of_nat n) = Some (nth n l 0).
Proof.
intros H m a l n Hg Hn. destruct (Hg n Hn) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (nth n l 0) 256) by lia. reflexivity.
Qed.
(* A 4-byte value read from the bytes of a garr8 list at offset o. *)
Lemma e_val4_garr8 : forall mem a l o v b,
  garr8 segs mem a l -> (o + 4 <= length l)%nat -> b = a + Z.of_nat o ->
  (forall k, (k < 4)%nat -> YO0f.le_byte (nth (o + k) l 0) 1 0 = YO0f.le_byte v 4 k) ->
  val_mem segs mem b 4 v.
Proof.
intros mem a l o v b Hg Hl -> Hb k Hk. destruct (Hg (o + k)%nat ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite Nat2Z.inj_add, Z.add_assoc in Hv. rewrite Hv, (Hb k Hk). reflexivity.
Qed.
Lemma e_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma e_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi). Qed.
Lemma e_region_kept_ro : forall E H (m m2 : word -> option byte) n b lo hi wlo cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
  region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo wlo cs).
Proof.
intros E H m m2 n b lo hi wlo cs Hn Hav.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview segs). apply Hav. exact Ha.
Qed.
Lemma e_val_eqm : forall H (m m' : word -> option byte) a n v,
  (forall x, mrestrict H m' x = mrestrict H m x) -> val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof. intros H m m' a n v HM Hv k Hk. pose proof (Hv k Hk) as Vk. unfold mbyte in *. rewrite HM. exact Vk. Qed.
End h.

(* The runs after the first one write nothing (their regions are read-only): the memory is the same function. *)
Ltac e_awr_ro :=
  intros ?a (rr & Hrr & Ha); cbn [ss_mem In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia | ]);
  destruct Hrr.
Ltac e_ro_eq HM :=
  lazymatch goal with HFr' : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
    assert (HM : forall x, mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x)
      by (intros x; apply HFr'; intros (rr & Hrr & Ha); cbn [ss_mem In] in Hrr;
          repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia | ]);
          destruct Hrr)
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOM := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation INV_EXIT := (inv_exit B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation INV_E_END := (inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation EPOST := (e_post B LLVMF_STK).
#[local] Notation ELOOP := (e_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation SEG_E_STMT := (seg_E_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_HW : In (VAL (A_OBJ 6), 36) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The image's constants in a state of the journal. *)
Lemma e_img : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W0) mem0) -> llvmf_img B G W' mem'.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ HR. apply HIMG.
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ | apply HRO; exact HR].
Qed.

(* reac_box_family_of's own table (object 17) holds the same three rows: its premise famof_tbl at 1, 2, 3. *)
Lemma e_tbl17 : forall (W : world SEGS) mem, llvmf_img B G W mem -> reac_box_family_of.famof_tbl W mem 1 2 3.
Proof.
intros W mem HI. destruct HI as (_ & _ & _ & _ & Hrow & _).
unfold reac_box_family_of.famof_tbl, reac_box_family_of.FAMOF_HWF.
split.
{ intros a Ha.
  replace a with (VAL (A_OBJ 17) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 17)))) by lia.
  rewrite (e_aview_garr8 SEGS (w_H W) mem (VAL (A_OBJ 17)) HW_ROWS (Z.to_nat (a - VAL (A_OBJ 17))) Hrow
    ltac:(cbn [length HW_ROWS]; lia)). discriminate. }
split; [lia|]. split.
{ apply (e_val4_garr8 SEGS _ _ HW_ROWS 0 1 _ Hrow); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia]. }
split; [lia|]. split.
{ apply (e_val4_garr8 SEGS _ _ HW_ROWS 12 2 _ Hrow); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia]. }
split; [lia|].
{ apply (e_val4_garr8 SEGS _ _ HW_ROWS 24 3 _ Hrow); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia]. }
Qed.

(* The call of reac_box_family_of at 0x81774 (return BASE + 0x1004), with the table's family fields 1, 2, 3. *)
Lemma e_famof_call : forall W ly S W0 mem0 md0 own lyc Sc memc mdc k (regsc : bvmap 5 word) sp0 mf p ch,
  ajournal SEGS B LLVMF_STK sp0 [] ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regsc = mf -> sp0 - 336 <= mf <= sp0 - 320 -> (mf - sp0) mod 16 = 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = Z_to_bv 64 (BASE + 0x1004) ->
  achain lyc (aview SEGS (w_H W) memc) mf (s0Z regsc) ch ->
  getr regsc 10 = w64 p -> 0 <= p < 2 ^ 64 -> p <> 0 -> reac_box_family_of.famof_box B lyc Sc W memc p ->
  reac_box_family_of.famof_tbl W memc 1 2 3 ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA IB_reac_box_family_of)) memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 r,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x1004)) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B LLVMF_STK sp0 [] ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    aregs_preserved regsc regs2 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - reac_box_family_of.REAC_BOX_FAMILY_OF_STK <= a < mf) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
    reac_box_family_of.famof_res (aview SEGS (w_H W) memc) p reac_box_family_of.FAMOF_HWF 1 2 3 r /\
    getr regs2 10 = Z_to_bv 64 (reac_box_family_of.famof_sx32 r)).
Proof.
intros W ly S W0 mem0 md0 own lyc Sc memc mdc k regsc sp0 mf p ch HJ Hsp Hmfb Hal Hgp Htp Hra Hch H10 Hp Hp0 Hbox Htbl.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
assert (HSTK1 : reac_box_family_of.REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity.
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
eapply SRr_mono.
{ apply (cl_callS B LAWS W regsc memc _ LLVMF_STK sp0 [] ly S W0 mem0 md0 own lyc Sc mdc k
    reac_box_family_of.REAC_BOX_FAMILY_OF_STK [] 0 (mf - sp0) (Z_to_bv 64 (BASE + 0x1004)) ch
    (fun ly' S' W' regs' mem' md' => ly' = lyc /\ S' = Sc /\ W' = W /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsc - reac_box_family_of.REAC_BOX_FAMILY_OF_STK <= a < spZ regsc) ->
        aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
      exists r, reac_box_family_of.famof_res (aview SEGS (w_H W) memc) p reac_box_family_of.FAMOF_HWF 1 2 3 r /\
        getr regs' 10 = Z_to_bv 64 (reac_box_family_of.famof_sx32 r)) HJ).
  - rewrite Hsp. lia.
  - exact Hal.
  - lia.
  - rewrite HSTK1. lia.
  - rewrite HSTK1. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (sp0 + (mf - sp0)) with mf by lia. exact Hch.
  - intros HPRE. rewrite (PSIG IB_reac_box_family_of AF_reac_box_family_of eq_refl).
    eapply SRr_mono; [exact (HFAM lyc Sc W regsc memc mdc ch p 1 2 3 HPRE H10 Hp (fun _ => Hbox) Htbl) |].
    cbv beta. intros W2 c2 _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & (-> & -> & -> & Hkeep & r & Hr & H10')).
    exists lyc, Sc, regs', mem', md'. split; [rewrite Hra; reflexivity|].
    split; [exact HJ'|]. split; [exact HP'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hkeep|]. exists r. split; [exact Hr | exact H10'].
  - intros a (rg & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HP2 & (-> & -> & -> & Hkeep & r & Hr & H10')).
split; [reflexivity|]. exists regs2, mem2, md2, r.
split; [reflexivity|]. split; [rewrite Z.add_0_r in HJ2; exact HJ2|]. split; [exact HP2|].
split; [rewrite Hsp in Hkeep; exact Hkeep|]. split; [exact Hr | exact H10'].
Qed.

(* The bcmp call at 0x817a4 (return BASE + 0x1034) for row j: x = &hw + 4, y = HW_TABLE + 4 + 12 j, n = 8. The
   result is 0 iff hw's eight bytes are row j's. *)
Lemma e_bcmp : forall W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (x : Z) (j : nat) (hwb : list byte) o,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  llvmf_img B G W memT -> (j < 3)%nat -> length hwb = 8%nat ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 (VAL (A_OBJ 6) + 4 + 12 * Z.of_nat j) -> getr regsT 12 = w64 8 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + 0x1034) ->
  0 <= x -> x + 8 <= 2 ^ 63 -> (forall a, x <= a < x + 8 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x 8 -> range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x 8 ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x 8 ->
  (forall n, (n < 8)%nat -> aview SEGS (w_H W) memT (x + Z.of_nat n) = Some (bv_unsigned (nth n hwb (Z_to_bv 8 0)))) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x1034)) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
    (v = w64 0 <-> map (fun b : byte => bv_unsigned b) hwb = SlotModel.HWT j) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k x j hwb o HJ HI Hj Hl Ha0 Ha1 Ha2 Hsp Hal Hneg Hbud
  Hgp Htp Hra Hx0 Hx63 Hxw Hxm Hxa Hxh Hxb.
pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HART & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
set (q := VAL (A_OBJ 6)) in *.
destruct HI as (_ & Hrow & Hq0 & Hq1 & _).
assert (Hty : forall n, (n < 36)%nat -> aview SEGS (w_H W) memT (q + Z.of_nat n) = Some (nth n HW_ROWS 0)).
{ intros n Hn. apply (e_aview_garr8 SEGS (w_H W) memT q HW_ROWS n Hrow). exact Hn. }
pose proof (ro_usable_glob SEGS B G lyc Sc W memT mdc q 36 (q + 4 + 12 * Z.of_nat j) 8 GM G_HW HART ltac:(lia) ltac:(lia))
  as HyRA.
pose proof (ro_hull SEGS B lyc Sc W memT mdc (q + 4 + 12 * Z.of_nat j) 8 IV HART ltac:(lia) ltac:(lia)
  ltac:(unfold IMG_HI; lia)) as HyH.
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W regsT memT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k x (q + 4 + 12 * Z.of_nat j) 8 o (Z_to_bv 64 (BASE + 0x1034)) HJ).
  - exact Ha0. - exact Ha1. - exact Ha2. - lia.
  - exact Hx0. - exact Hx63. - lia. - lia.
  - exact Hsp. - exact Hal. - exact Hneg. - exact Hbud.
  - exact Hgp. - exact Htp. - exact Hra. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite (Hxb (Z.to_nat (a - x)) ltac:(lia)). discriminate.
    + rewrite Hsp. intros Hc. apply (Hxw a Ha). rewrite HES in *. lia.
  - intros a Ha. split.
    + replace a with (q + Z.of_nat (Z.to_nat (a - q))) by lia. rewrite (Hty (Z.to_nat (a - q)) ltac:(lia)). discriminate.
    + rewrite Hsp, HES. lia.
  - exact Hxw.
  - intros a Ha. rewrite HES. lia.
  - exact Hxm.
  - unfold amem_range. left. lia.
  - exact Hxa.
  - intros _. exact Hxh.
  - exact HyRA.
  - intros _. exact HyH. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|].
split; [|split; [exact Hfr | exact Hpres]].
rewrite Hcmp.
rewrite <- (e_row_iff (aview SEGS (w_H W) memT) x q hwb j Hl Hj Hxb Hty).
split; intros H i Hi; rewrite (H i Hi); f_equal; lia.
Qed.

(* ---- the symbolic state at 0x81764 ------------------------------------------------------------------------ *)
(* Atom 32 = the shadow base, 33 = the frame SF, 34 = hw.have, 35 = SF's shadow address. Region 0: the machine
   frame's slots the segment loads (base x9 = mf; read-only); region 1: hw.have (SF + 432 .. 436, written at
   0x8176c); region 2: HW_TABLE's three family fields (read-only, values 1, 2, 3). *)
Definition SB_E : Z := 0x7fff8000.
Definition Bx_E : sv := SOff 32 0.
Definition Bspan_E : Z * Z := (SB_E, SB_E + 2 ^ 44 - 1).
Definition e_mf : YP09.region := YP09.mkRegion (Some 9%nat) 24 192 24 24
  [YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 432));
   YP09.mkChunk 160 (CVal 8 (SOff 35 0)); YP09.mkChunk 168 (CVal 8 (SOff 32 0));
   YP09.mkChunk 184 (CVal 8 (SOff 33 352))].
Definition e_hw : YP09.region := YP09.mkRegion (Some 33%nat) 432 436 432 436 [].
Definition e_tbl : YP09.region := YP09.mkRegion (Some (A_OBJ 6)) 0 36 0 0
  [YP09.mkChunk 0 (CVal 4 (SLit 1)); YP09.mkChunk 12 (CVal 4 (SLit 2)); YP09.mkChunk 24 (CVal 4 (SLit 3))].
Definition e_atoms : list (nat * afact) := [(32%nat, mkAF SB_E SB_E 0); (A_OBJ 6, mkAF IMG_LO IMG_TOP 3)].
Definition ss_e : sstate := mkSS 0xff0 sr_atoms [e_mf; e_hw; e_tbl] None (mkFacts e_atoms [] []).
Definition e_SHT : list shent := [mkSHE (A_OBJ 6) 0 36].

Theorem e_walk : ELOOP -> forall g pos mf ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2
    (4 * Z.of_nat (m_nrec g)) ->
  frames S2 = [(4, pos)] ->
  ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  id_at g pos (m_nrec g) W2 mem2 ->
  hw_live g pos mf (m_nrec g) W2 mem2 ->
  mf_hw g pos mf W2 mem2 -> val_mem SEGS (rd W2 mem2) (mf + 160) 8 (shadow_addr (SFa g pos)) ->
  mf_id g pos mf W2 mem2 -> sh_reg g pos regs2 ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0xff0) regs2 mem2 md2) (EPOST g pos mf ly2 S2 W2 regs2 mem2).
Proof.
intros HLOOP g pos mf ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC Hid Hhw V32 V160 Hmid Hsh.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vflag & HPRE & _).
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _ & HRS & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & F1 & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. Z.div_mod_to_equations. lia. }
(* the model *)
set (nr := m_nrec g) in *.
set (have := m_have g nr) in *.
set (hwb := m_hwb g nr) in *.
assert (Hhave : have = 0 \/ have = 1) by (unfold have, m_have; apply e_have01).
destruct Hhw as ((Hhwbytes & Hhwz & Hhwb) & Vhw0 & V24).
destruct Hid as (Hidbytes & Hidz & Hidb).
change (SFa g pos) with SF in Hhwbytes, Hhwz, Hhwb, Vhw0, Hidbytes, Hidz, Hidb, V32, V160, Hmid, Hsh.
unfold mf_hw in V32. unfold mf_id in Hmid. rename Hmid into V184.
(* the environment *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 SB_E; Z_to_bv 64 SF; Z_to_bv 64 have; Z_to_bv 64 sh])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 have)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sh)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 SB_E; Z_to_bv 64 SF; Z_to_bv 64 have; Z_to_bv 64 sh]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (E6 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
  by (apply (img_env_atomP E (A_OBJ 6) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U33 : bv_unsigned (ew E 33) = SF) by (rewrite E33; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
pose proof (pa_val_range (A_OBJ 6)) as Rg6.
assert (U6 : bv_unsigned (ew E (A_OBJ 6)) = VAL (A_OBJ 6)) by (rewrite E6; apply unsigned_lit_small; lia).
(* the image's rows *)
pose proof (e_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRS) as HI2.
pose proof HI2 as (_ & Hrow6 & Hq0 & Hq1 & _).
pose proof (proj1 (GM ly2 S2 W2 mem2 md2 (VAL (A_OBJ 6)) 36 G_HW HAR2)) as Hq8.
(* SF lies apart from the image *)
pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as HSFimg. rewrite EFa, HFB in HSFimg.
(* the symbolic state at 0x81764 *)
assert (HS : st_ok_pi SEGS VAL E ss_e
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xff0)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_e. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold e_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      * apply (chunk_ok_val SEGS E _ mf 24 8 (SOff 34 0) have);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hhave; lia | clear; lia | exact V24].
      * apply (chunk_ok_val SEGS E _ mf 32 8 (SOff 33 432) (SF + V_hw));
        [cbn [sv_denot]; rewrite E33, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia); reflexivity
        | unfold V_hw; clear - HSF0 HSF1 C1; lia | clear; lia | exact V32].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 35 0) sh);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hsh1 C1; lia | clear; lia | exact V160].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | clear; lia | exact V168].
      * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 352) (SF + V_id));
        [cbn [sv_denot]; rewrite E33, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia); reflexivity
        | unfold V_id; clear - HSF0 HSF1 C1; lia | clear; lia | exact V184].
    + unfold e_hw, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [clear - HSF0; lia|]. split; [clear - HSF1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat nr) (SF + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ho; lia))).
    + unfold e_tbl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U6. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
        apply (e_val4_garr8 SEGS _ _ HW_ROWS 0 1 _ Hrow6); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia].
      * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 12 4 (SLit 2) 2); [reflexivity | lia | lia |].
        apply (e_val4_garr8 SEGS _ _ HW_ROWS 12 2 _ Hrow6); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia].
      * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 24 4 (SLit 3) 3); [reflexivity | lia | lia |].
        apply (e_val4_garr8 SEGS _ _ HW_ROWS 24 3 _ Hrow6); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, e_mf, e_hw, e_tbl.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U6.
    split; [split; [|split; [|exact I]] | split; [split; [|exact I] | split; exact I]].
    + right. clear - HSF1 Hmf0. lia.
    + right. clear - Hq1 Hmf0 C1. lia.
    + clear - HSFimg Hq0 Hq1. lia.
  - unfold facts_ok, e_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [| split; exact I]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SB_E; lia).
      split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U6. split; [lia|]. split; [change (2 ^ 3) with 8; exact Hq8 | lia]. }
unfold cfg_at. change (w64 (BASE + 0xff0)) with (Z_to_bv 64 (BASE + 0xff0)).
(* ---- run 1: 0x81764 .. the call at 0x81774 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold ss_e in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; unfold e_mf, e_hw, e_tbl in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | | lia].
  rewrite U33 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. clear - Ha. lia. }
(* what run 1 kept: every byte outside the four bytes of hw.have *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SF + 432 <= a < SF + 436) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E (ss_mem ss_e) (w_H W2) mem2 (ms_mem ms) (fun x => SF + 432 <= x < SF + 436) HFr);
  [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr.
  cbn [ss_e ss_mem windows map e_mf e_hw e_tbl YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
  repeat (destruct Hin as [Eq | Hin];
    [ injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9, ?U33, ?U6 in Hr; clear - Hr; lia | ]).
  destruct Hin. }
(* hw.have is in the frame variable from here on *)
assert (VH : val_mem SEGS (rd W2 (ms_mem ms)) (SF + V_hw) 4 have).
{ lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_region_nth (segs := SEGS) Ev ssx msx 1%nat
      (YP09.mkRegion (Some 33%nat) 432 436 432 436 [YP09.mkChunk 432 (CVal 4 (SOff 34 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR1 end.
  destruct HR1 as (_ & _ & _ & HF1). cbn [ms_mem restrict] in HF1.
  pose proof (Forall_inv HF1) as HC1. cbn [YP09.r_base base_val] in HC1. rewrite U33 in HC1.
  exact (val_of_chunk_ok SEGS _ _ SF 432 4 (SOff 34 0) have HC1
    ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(clear - Hhave; lia) ltac:(clear; lia)). }
clear HF HFr HG.
(* the shadow of a frame variable is never one of the four bytes *)
assert (SHX : forall a, sh <= a < sh + 128 -> ~ (SF + 432 <= a < SF + 436)).
{ intros a Ha Hw. apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia
  | exact HSFapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | clear - Hw; lia]. }
(* the facts of the frame at the call state *)
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= 432 \/ 436 <= off) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W2 (ms_mem ms)) (SF + off) n v).
{ intros off n v H0 H1 Hd Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply KEEP1; clear - H0 H1 Hd Hkk HSF0 HSF1 C1; lia. }
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms)) a n v).
{ intros a n v H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP1; clear - H1 H2 Hkk Hmf0 Hmfb HSF0 HSF1 Hshi H47 C1; lia. }
assert (SHB : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W2 (ms_mem ms) (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_blk in *.
  apply (e_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) (ms_mem ms))
    SHADOW_OFF (SF + off) n); [|exact Hz].
  intros ii Hii. apply KEEP1.
  - unfold shadow_of_addr. clear - H0 H1 Hn Hii HSF0 HSF1 HSF64 C1. unfold SHADOW_OFF. Z.div_mod_to_equations. lia.
  - apply SHX. unfold shadow_of_addr. rewrite Esh.
    clear - H0 H1 Hn Hii HSF0 HSF1 HSF64 C1. unfold SHADOW_OFF. Z.div_mod_to_equations. lia. }
(* the image at the call state *)
pose proof (e_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRS) as HIc.
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
rewrite U33 in R10. rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in R8.
assert (Usp : spZ (ms_regs ms) = mf)
  by (unfold spZ; rewrite R2; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (Us0 : s0Z (ms_regs ms) = sp0)
  by (unfold s0Z; rewrite R8; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
(* the call chain: the entry's own frame record on top of the entry's chain *)
assert (HCH : exists ch, achain ly2 (aview SEGS (w_H W2) (ms_mem ms)) mf sp0 ch).
{ assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) [])
    by (apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]).
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))].
    apply (achain_push ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. rewrite KEEP1 by (clear - Ha HSF0 HSF1 Hceil Hslo HSTK' Has C1; lia).
      apply F1; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra].
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0].
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. Z.div_mod_to_equations. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch & Hchain).
pmkst HS.
(* ---- reac_box_family_of at 0x81774 ---- *)
eapply SRr_bind.
{ eapply (e_famof_call W2 (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 (ms_mem ms) _
    (4 * Z.of_nat nr) (ms_regs ms) sp0 mf (SF + V_id) ch HJ).
  - exact Usp.
  - exact Hmfb.
  - clear - Hmf32 Hsp0al. Z.div_mod_to_equations. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - rewrite Us0. exact Hchain.
  - unfold V_id. exact R10.
  - unfold V_id. clear - HSF0 HSF1 C1. lia.
  - unfold V_id. clear - HSF0. lia.
  - right. split; [|split].
    + exists 4, pos. split; [exact Hin4|]. split; [clear; lia|].
      split; [rewrite EFa; clear - HSF64; Z.div_mod_to_equations; lia|].
      rewrite EFa, HFB. unfold V_id. clear. lia.
    + unfold V_id. clear - HSF64. Z.div_mod_to_equations. lia.
    + apply (block_shadow_range (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (SF + V_id) N_id);
      [apply SHB; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidb]
      | clear; lia | unfold N_id; clear; lia].
  - apply (e_tbl17 W2 (ms_mem ms) HIc). }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & r & -> & HJ3 & HP3 & Hkeep3 & Hres3 & R10').
(* the library's result is FAM of id, which is the harness's fam_hw (SlotModel.rec_P7) *)
pose proof HIc as (_ & _ & _ & _ & Hrow17c & _).
assert (Hr : r = SlotModel.FAM (m_id g nr)).
{ apply (e_famof_FAM (aview SEGS (w_H W2) (ms_mem ms)) (SF + V_id) reac_box_family_of.FAMOF_HWF r (m_id g nr)).
  - unfold m_id. rewrite SlotModel.rec_id_length. reflexivity.
  - unfold V_id. clear - HSF0. lia.
  - intros n Hn. assert (Hl38 : length (m_id g nr) = 38%nat) by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
    rewrite KEEP1; [| unfold V_id; clear - Hn HSF0 HSF1 C1; lia | unfold V_id; clear - Hn; lia].
    rewrite (e_aview_garr8 SEGS (w_H W2) mem2 (SF + V_id) _ n Hidbytes) by (rewrite length_map, Hl38; exact Hn).
    f_equal. apply e_nth_map_bv. rewrite Hl38. exact Hn.
  - intros n Hn. unfold reac_box_family_of.FAMOF_HWF.
    exact (e_aview_garr8 SEGS (w_H W2) (ms_mem ms) _ HW_ROWS n Hrow17c ltac:(cbn [length HW_ROWS]; clear - Hn; lia)).
  - exact Hres3. }
assert (HF3 : 0 <= SlotModel.FAM (m_id g nr) <= 3) by apply e_FAM_range.
rewrite Hr, (e_sx32_small _ HF3) in R10'.
assert (EFAM : SlotModel.FAM (m_id g nr) = SlotModel.fam_hw have hwb) by exact (SlotModel.rec_P7 (e_pl g) nr).
(* what the call kept, and hw.have at mem3 *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
{ intros a Ha Hw. apply Hkeep3; [exact Ha|].
  unfold reac_box_family_of.REAC_BOX_FAMILY_OF_STK, reac_box_family_of.FAMOF_FRAME, ESTACK. clear - Hw. lia. }
(* back at 0x81778: the machine frame's region and the table's are kept; hw.have's region is dropped *)
prreg HS (10%bv : bv 5) Ra0c.
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 2]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
  - apply (e_region_kept_ro SEGS E (w_H W2) (ms_mem ms) mem3 9%nat mf); [exact U9|].
    intros a Ha. apply KEEP3; clear - Ha Hmf0 Hmfb Hshi H47 C1; lia.
  - apply (e_region_kept_ro SEGS E (w_H W2) (ms_mem ms) mem3 (A_OBJ 6) (VAL (A_OBJ 6))); [exact U6|].
    intros a Ha. apply KEEP3; clear - Ha Rg6 Hq0 Hq1 Hmf0 C1; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
prreg HS (10%bv : bv 5) Ha03.
(* the bytes from mem2 to mem3: outside the call's stack window and outside hw.have *)
assert (KEEPm3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SF + 432 <= a < SF + 436) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hh. rewrite (KEEP3 a Ha Hw). exact (KEEP1 a Ha Hh). }
assert (VH3 : val_mem SEGS (rd W2 mem3) (SF + V_hw) 4 have).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W2) (ms_mem ms) mem3 (SF + V_hw) (SF + V_hw) 4 have); [|exact VH].
  intros kk Hkk. apply KEEP3; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia. }
(* ---- run 2: 0x81778 x18 := a0, to the test of hw.have at 0x8177c ---- *)
paj_run_sh RUNP HS HJ3.
{ e_awr_ro. }
e_ro_eq HM4.
psrr_branch_pi RUNP BR HS.
- (* hw.have = 0: 0x817c4 a0 := 0, a4 := the shadow base, to the compare *)
  assert (Hh0 : have = 0).
  { pose proof Hhave as [H0 | H1]; [exact H0|]. exfalso.
    lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff 34 0)) _ = _ =>
      rewrite branch_eq_U, (U_atom Ev 34 have ltac:(rewrite ?ew_havoc_old by lia; exact E34) ltac:(clear - Hhave; lia))
        in Hc end.
    rewrite H1 in Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ3 0x107c.
  { e_awr_ro. }
  e_ro_eq HM5.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch type of HM4 with forall x, mrestrict _ ?m4 x = _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SF + 432 <= a < SF + 436) ->
    aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hw Hh; rewrite (aview_eq_of SEGS (w_H W2) m4 (ms_mem msF) a (HM5 _)),
        (aview_eq_of SEGS (w_H W2) mem3 m4 a (HM4 _)); exact (KEEPm3 a Ha Hw Hh));
  assert (VHF : val_mem SEGS (rd W2 (ms_mem msF)) (SF + V_hw) 4 have)
    by exact (e_val_eqm SEGS _ _ _ _ _ _ HM5 (e_val_eqm SEGS _ _ _ _ _ _ HM4 VH3))
  end end.
  prreg HS (18%bv : bv 5) P18. prreg HS (10%bv : bv 5) P10. prreg HS (14%bv : bv 5) P14.
  prreg HS (23%bv : bv 5) P23. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  pmkst HS;
  apply (e_tail B LLVMF_STK LAWS g pos mf ly2 S2 W2 regs2 mem2 (ms_regs msF) (ms_mem msF) _ 0 HJ3) end.
  + clear. lia.
  + rewrite P18, <- Ha03, R10', EFAM, Hh0. reflexivity.
  + rewrite P10. reflexivity.
  + rewrite P2. exact (EE 2%nat 2%bv eq_refl).
  + rewrite P3. exact (EE 3%nat 3%bv eq_refl).
  + rewrite P4. exact (EE 4%nat 4%bv eq_refl).
  + rewrite P8. exact (EE 8%nat 8%bv eq_refl).
  + rewrite P9. exact (EE 9%nat 9%bv eq_refl).
  + rewrite P25. exact (EE 25%nat 25%bv eq_refl).
  + rewrite P24. exact (EE 24%nat 24%bv eq_refl).
  + rewrite P23, (EE 23%nat 23%bv eq_refl). exact Hsh.
  + rewrite P14, E32. reflexivity.
  + exact VHF.
  + exact KEEPF.
- (* hw.have <> 0: the loop's set-up 0x81780 .. 0x81794, to the loop head *)
  assert (Hh1 : have <> 0).
  { intros H0.
    lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff 34 0)) _ = _ =>
      rewrite branch_eq_U, (U_atom Ev 34 have ltac:(rewrite ?ew_havoc_old by lia; exact E34) ltac:(clear - Hhave; lia))
        in Hc end.
    rewrite H0 in Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ3 0x1024.
  { e_awr_ro. }
  e_ro_eq HM5.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  lazymatch type of HM4 with forall x, mrestrict _ ?m4 x = _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SF + 432 <= a < SF + 436) ->
    aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hw Hh; rewrite (aview_eq_of SEGS (w_H W2) m4 (ms_mem msF) a (HM5 _)),
        (aview_eq_of SEGS (w_H W2) mem3 m4 a (HM4 _)); exact (KEEPm3 a Ha Hw Hh));
  assert (VHF : val_mem SEGS (rd W2 (ms_mem msF)) (SF + V_hw) 4 have)
    by exact (e_val_eqm SEGS _ _ _ _ _ _ HM5 (e_val_eqm SEGS _ _ _ _ _ _ HM4 VH3))
  end end.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
  pmkst HS;
  apply (HLOOP HSTK LAWS RO HRO G GM IV G_HW HIMG ABCMP (e_tail B LLVMF_STK) g pos mf ly2 S2 W2 regs2 mem2 0%nat
    (ms_regs msF) (ms_mem msF) _ HJ3 Hfrs HPRE Hmfb Hmf32) end.
  + clear. lia.
  + exact Hh1.
  + intros j' Hj'. clear - Hj'. lia.
  + exact Rsp.
  + exact Rs1.
  + exact Rs0.
  + exact Rgp.
  + exact Rtp.
  + rewrite P2. exact (EE 2%nat 2%bv eq_refl).
  + rewrite P3. exact (EE 3%nat 3%bv eq_refl).
  + rewrite P4. exact (EE 4%nat 4%bv eq_refl).
  + rewrite P8. exact (EE 8%nat 8%bv eq_refl).
  + rewrite P9. exact (EE 9%nat 9%bv eq_refl).
  + rewrite P25. exact (EE 25%nat 25%bv eq_refl).
  + rewrite P24. exact (EE 24%nat 24%bv eq_refl).
  + rewrite P18, <- Ha03, R10', EFAM. unfold SlotModel.fam_hw.
    destruct (Z.eqb_spec have 0) as [E0 | _]; [contradiction | reflexivity].
  + rewrite P19. reflexivity.
  + rewrite P20. change 247%nat with (A_OBJ 6). rewrite U6. unfold w64. f_equal. clear. lia.
  + rewrite P21. change 247%nat with (A_OBJ 6). rewrite E6. reflexivity.
  + rewrite P22, U33. reflexivity.
  + rewrite P23. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  + apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 _ (mf + 160) (mf + 160) 8 _); [|exact V160].
    intros kk Hkk. apply KEEPF; clear - Hkk Hmf0 Hmfb Hshi H47 HSF0 HSF1 C1; lia.
  + apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 _ (mf + 168) (mf + 168) 8 _); [|exact V168].
    intros kk Hkk. apply KEEPF; clear - Hkk Hmf0 Hmfb Hshi H47 HSF0 HSF1 C1; lia.
  + unfold bytes_at8 in *. apply (e_garr8_moved SEGS (w_H W2) (w_H W2) mem2 _ _ _); [|exact Hhwbytes].
    intros kk Hkk. rewrite length_map in Hkk. unfold m_hwb in Hkk. rewrite e_hwb_length in Hkk.
    apply KEEPF; unfold V_hw; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
  + unfold sh_blk in *. apply (e_block_shadow_moved (aview SEGS (w_H W2) mem2) _ SHADOW_OFF (SF + V_hw) N_hw);
    [|exact Hhwb].
    intros ii Hii. apply KEEPF.
    * unfold shadow_of_addr, V_hw, N_hw in *. clear - Hii HSF0 HSF1 HSF64 C1. unfold SHADOW_OFF.
      Z.div_mod_to_equations. lia.
    * unfold shadow_of_addr, V_hw, N_hw in *. clear - Hii HSF0 HSF1 HSF64 Hsh1 Esh Hmf0 C1. rewrite Esh in Hsh1.
      unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    * apply SHX. unfold shadow_of_addr, V_hw, N_hw in *. rewrite Esh. clear - Hii HSF0 HSF64. unfold SHADOW_OFF.
      Z.div_mod_to_equations. lia.
  + exact VHF.
  + exact KEEPF.
Qed.

(* The segment: the walk to 0x817f4 (e_walk, with the loop e_loop), then the boundary inv_E_end (e_fin). *)
Lemma seg_E : SEG_E_STMT.
Proof.
unfold seg_E_stmt.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hhw & Hbl & Hhwp & Hid3 & V160 & Hmid & Hsh & Hcur & R24).
eapply SRr_mono.
{ exact (e_walk (e_loop B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS) g pos mf ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC Hid Hhw Hhwp V160 Hmid Hsh). }
intros W3 c3 _ Hpost.
exact (e_fin B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
  arodata_okS HSTK LAWS AJ_NIL_IO g pos mf ly2 S2 W2 regs2 mem2 md2 W3 c3 Hfrs Hk MLE MOK HC Hid Hhw Hbl Hid3 Hmid
  Hcur R24 Hpost).
Qed.

Check (seg_E : SEG_E_STMT).
Print Assumptions seg_E.

End c.
End b.
End a.
