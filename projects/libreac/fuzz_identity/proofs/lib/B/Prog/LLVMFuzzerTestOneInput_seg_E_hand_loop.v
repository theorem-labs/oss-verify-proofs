(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses changed; 838 of its 952 lines of code are new or changed and 5951 lines of the source are left out. *)
(* e_loop of seg_E (LLVMFuzzerTestOneInput_seg_E_hand_stmt.v, e_loop_stmt): the harness's family loop over HW_TABLE
   (object 6), from its head 0x81798 (BASE + 0x1024) at row j. Each row: a2 := 8, a0 := &hw + 4, a1 := HW_TABLE + 4
   + 12 j, the bcmp at 0x817a4 (return BASE + 0x1034), the test of its result at 0x817a8. Equal: 0x817d0 .. 0x817e8,
   the shadow test of HW_TABLE + 12 j (a registered global: its cell is 0, so the report at 0x82670 is not reached)
   and a0 := the row's family field j + 1; 0x817ec x23 := the frame's shadow address; at the compare 0x817f0
   x18 = a0 = j + 1 = fam_cmp hw, and e_tail_stmt ends the run. Not equal: x19 -= 12, x20 += 12, and back to the
   head with row j + 1, or after row 2 to 0x817b8 (a0 := 0, a4 := the shadow base), 0x817ec and the compare with
   x18 = a0 = 0 = fam_cmp hw. The head's symbolic state is rebuilt from the registers' values (x19, x20, x21, x23
   set to the values the set-up 0x81780 .. 0x81794 gives them), so one proof serves the three rows. *)
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
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_E_hand_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_box_family_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma l_HWT_len : forall j, (j < 3)%nat -> length (SlotModel.HWT j) = 8%nat.
Proof. intros j Hj. destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia]. Qed.
(* Row j of the harness's table: the family field at 12 j, the eight hw bytes at 12 j + 4. *)
Lemma l_HWT_rows : forall j i, (j < 3)%nat -> (i < 8)%nat -> nth i (SlotModel.HWT j) 0 = nth (12 * j + 4 + i) HW_ROWS 0.
Proof.
intros j i Hj Hi.
destruct j as [|[|[|j]]]; [| | | lia]; (do 8 (destruct i as [|i]; [reflexivity|])); lia.
Qed.
Lemma l_l8 : forall l1 l2 : list Z, length l1 = 8%nat -> length l2 = 8%nat ->
  (forall i, (i < 8)%nat -> nth i l1 0 = nth i l2 0) -> l1 = l2.
Proof. intros l1 l2 H1 H2 H. apply nth_ext with (d := 0) (d' := 0); [lia|]. intros n Hn. apply H. lia. Qed.
Lemma l_nth_map_bv : forall (hw : list byte) n, (n < length hw)%nat ->
  nth n (map (fun b : byte => bv_unsigned b) hw) 0 = bv_unsigned (nth n hw (Z_to_bv 8 0)).
Proof.
intros hw n Hn. rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0))) by (rewrite length_map; lia).
apply map_nth.
Qed.
(* Eight bytes read at xa equal row j of the table at ta (both in the reader rdr) iff the bytes are HWT j. *)
Lemma l_row_iff : forall (rdr : reader) (xa ta : Z) (hw : list byte) (j : nat),
  length hw = 8%nat -> (j < 3)%nat ->
  (forall n, (n < 8)%nat -> rdr (xa + Z.of_nat n) = Some (bv_unsigned (nth n hw (Z_to_bv 8 0)))) ->
  (forall n, (n < 36)%nat -> rdr (ta + Z.of_nat n) = Some (nth n HW_ROWS 0)) ->
  ((forall i, 0 <= i < 8 -> rdr (xa + i) = rdr (ta + 12 * Z.of_nat j + 4 + i)) <->
   map (fun b : byte => bv_unsigned b) hw = SlotModel.HWT j).
Proof.
intros rdr xa ta hw j Hl Hj Hx Ht. split.
- intros H. apply l_l8; [rewrite length_map; exact Hl | apply l_HWT_len; exact Hj |].
  intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)).
  rewrite (Hx i Hi) in H.
  replace (ta + 12 * Z.of_nat j + 4 + Z.of_nat i) with (ta + Z.of_nat (12 * j + 4 + i)) in H by lia.
  rewrite (Ht (12 * j + 4 + i)%nat ltac:(lia)) in H.
  rewrite (l_HWT_rows j i Hj Hi), l_nth_map_bv by lia. congruence.
- intros H i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  assert (Hi' : (Z.to_nat i < 8)%nat) by lia. set (n := Z.to_nat i) in *.
  rewrite (Hx n Hi').
  replace (ta + 12 * Z.of_nat j + 4 + Z.of_nat n) with (ta + Z.of_nat (12 * j + 4 + n)) by lia.
  rewrite (Ht (12 * j + 4 + n)%nat ltac:(lia)). f_equal.
  rewrite <- (l_HWT_rows j n Hj Hi'), <- H, l_nth_map_bv by lia. reflexivity.
Qed.
Lemma l_fam_cmp_hit : forall (hw : list byte) j, (j < 3)%nat ->
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
Lemma l_fam_cmp_none : forall (hw : list byte),
  (forall j', (j' < 3)%nat -> map (fun b : byte => bv_unsigned b) hw <> SlotModel.HWT j') -> SlotModel.fam_cmp hw = 0.
Proof.
intros hw Hm. pose proof (Hm 0%nat ltac:(lia)) as M0. pose proof (Hm 1%nat ltac:(lia)) as M1.
pose proof (Hm 2%nat ltac:(lia)) as M2. cbn [SlotModel.HWT nth] in M0, M1, M2.
unfold SlotModel.fam_cmp. cbv zeta.
destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW1) as [E|_]; [contradiction|].
destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW2) as [E|_]; [contradiction|].
destruct (list_eq_dec Z.eq_dec _ reac_box_family_of_c.FAMOF_HW3) as [E|_]; [contradiction | reflexivity].
Qed.

Lemma l_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
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
Section h.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma l_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma l_aview_garr8 : forall H (m : word -> option byte) a l n,
  garr8 segs (mrestrict H m) a l -> (n < length l)%nat -> aview segs H m (a + Z.of_nat n) = Some (nth n l 0).
Proof.
intros H m a l n Hg Hn. destruct (Hg n Hn) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (nth n l 0) 256) by lia. reflexivity.
Qed.
(* A 4-byte value read from the bytes of a garr8 list at offset o. *)
Lemma l_val4_garr8 : forall mem a l o v b,
  garr8 segs mem a l -> (o + 4 <= length l)%nat -> b = a + Z.of_nat o ->
  (forall k, (k < 4)%nat -> YO0f.le_byte (nth (o + k) l 0) 1 0 = YO0f.le_byte v 4 k) ->
  val_mem segs mem b 4 v.
Proof.
intros mem a l o v b Hg Hl -> Hb k Hk. destruct (Hg (o + k)%nat ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite Nat2Z.inj_add, Z.add_assoc in Hv. rewrite Hv, (Hb k Hk). reflexivity.
Qed.
Lemma l_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma l_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi). Qed.
Lemma l_region_kept_ro : forall E H (m m2 : word -> option byte) n b lo hi wlo cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
  region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo wlo cs).
Proof.
intros E H m m2 n b lo hi wlo cs Hn Hav.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha; [|lia].
apply (mbyte_of_aview segs). apply Hav. exact Ha.
Qed.
Lemma l_val_eqm : forall H (m m' : word -> option byte) a n v,
  (forall x, mrestrict H m' x = mrestrict H m x) -> val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof. intros H m m' a n v HM Hv k Hk. pose proof (Hv k Hk) as Vk. unfold mbyte in *. rewrite HM. exact Vk. Qed.
End h.
Lemma l_denot_off : forall {fx : YK11.FPState} E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros fx E n v c Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity. Qed.
Lemma l_br_eq : forall {fx : YK11.FPState} E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = w64 0.
Proof.
intros fx E n v Hn Hb. rewrite branch_eq_U in Hb. apply Z.eqb_eq in Hb.
unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
apply bv_eq. exact Hb.
Qed.
Lemma l_br_ne : forall {fx : YK11.FPState} E n (v : word), ew E n = v ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> w64 0.
Proof.
intros fx E n v Hn Hb Hv. rewrite branch_eq_U in Hb. apply Z.eqb_neq in Hb. apply Hb.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity.
Qed.
Ltac l_bvc := unfold w64; first [reflexivity | apply bv_eq; rewrite ?Z_to_bv_unsigned; vm_compute; reflexivity].
(* The bcmp result's atom after a call: ew (havoc X K ws) (K + j) = the j-th clobbered register. *)
Ltac l_hv Hv :=
  repeat rewrite ew_ewset_other by lia;
  lazymatch goal with |- ew (havoc _ ?K _) ?n = _ =>
  let j := eval vm_compute in (n - K)%nat in
  change n with (K + j)%nat; rewrite (YN3v.ew_havoc_new _ K _ j (Z_to_bv 64 0)) by (cbn; lia);
  cbn [nth map CLOB]; exact Hv end.

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
#[local] Notation INV_E_END := (inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

#[local] Notation EPOST := (e_post B LLVMF_STK).
#[local] Notation ETAIL := (e_tail_stmt B LLVMF_STK).
#[local] Notation ELOOP := (e_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
Definition SB_L : Z := 0x7fff8000.
Definition Bx_L : sv := SOff 32 0.
Definition Bspan_L : Z * Z := (SB_L, SB_L + 2 ^ 44 - 1).
(* Atom 32 = the shadow base, 33 = the frame's shadow address. Region 0: mf+160 and mf+168 (read at 0x817ec and
   0x817bc / 0x817d8); region 1: HW_TABLE's three family fields. *)
Definition l_mf : YP09.region := YP09.mkRegion (Some 9%nat) 160 176 160 160
  [YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition l_tbl : YP09.region := YP09.mkRegion (Some (A_OBJ 6)) 0 36 0 0
  [YP09.mkChunk 0 (CVal 4 (SLit 1)); YP09.mkChunk 12 (CVal 4 (SLit 2)); YP09.mkChunk 24 (CVal 4 (SLit 3))].
Definition l_atoms : list (nat * afact) := [(32%nat, mkAF SB_L SB_L 0); (A_OBJ 6, mkAF IMG_LO IMG_TOP 3)].
Definition ss_l : sstate := mkSS 0x1024 sr_atoms [l_mf; l_tbl] None (mkFacts l_atoms [] []).
Definition l_SHT : list shent := [mkSHE (A_OBJ 6) 0 36].

Ltac l_awr_ro :=
  intros ?a (rr & Hrr & Ha); cbn [ss_mem In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi l_mf l_tbl] in Ha; clear - Ha; lia | ]);
  destruct Hrr.
Ltac l_ro_eq HM :=
  lazymatch goal with HFr' : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
    assert (HM : forall x, mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x)
      by (intros x; apply HFr'; intros (rr & Hrr & Ha); cbn [ss_mem In] in Hrr;
          repeat (destruct Hrr as [<- | Hrr];
            [cbn [YP09.r_base YP09.r_wlo YP09.r_whi l_mf l_tbl] in Ha; clear - Ha; lia | ]);
          destruct Hrr)
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section L.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_HW : In (VAL (A_OBJ 6), 36) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis ETAILH : ETAIL.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The image's constants in a state of the journal. *)
Lemma l_img : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W0) mem0) -> llvmf_img B G W' mem'.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ HR. apply HIMG.
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ | apply HRO; exact HR].
Qed.

(* The bcmp call at 0x817a4 (return BASE + 0x1034) for row j: x = &hw + 4, y = HW_TABLE + 4 + 12 j, n = 8. The
   result is 0 iff hw's eight bytes are row j's. *)
Lemma l_bcmp : forall W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (x : Z) (j : nat) (hwb : list byte) o,
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
{ intros n Hn. apply (l_aview_garr8 SEGS (w_H W) memT q HW_ROWS n Hrow). exact Hn. }
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
rewrite <- (l_row_iff (aview SEGS (w_H W) memT) x q hwb j Hl Hj Hxb Hty).
split; intros H i Hi; rewrite (H i Hi); f_equal; lia.
Qed.

Lemma l_loop : forall g pos mf ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 (j : nat) (regs : bvmap 5 word) mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem md
    (4 * Z.of_nat (m_nrec g)) ->
  frames S2 = [(4, pos)] -> EPRE g ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  (j < 3)%nat -> m_have g (m_nrec g) <> 0 ->
  (forall j', (j' < j)%nat -> map (fun b : byte => bv_unsigned b) (m_hwb g (m_nrec g)) <> SlotModel.HWT j') ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf -> getr regs2 8 = w64 (e_sp0 g) ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs 2 = getr regs2 2 -> getr regs 3 = getr regs2 3 -> getr regs 4 = getr regs2 4 ->
  getr regs 8 = getr regs2 8 -> getr regs 9 = getr regs2 9 -> getr regs 25 = getr regs2 25 ->
  getr regs 24 = getr regs2 24 ->
  getr regs 18 = w64 (SlotModel.fam_cmp (m_hwb g (m_nrec g))) ->
  getr regs 19 = w64 (- (12 * Z.of_nat j)) ->
  getr regs 20 = w64 (VAL (A_OBJ 6) + 4 + 12 * Z.of_nat j) ->
  getr regs 21 = w64 (VAL (A_OBJ 6)) ->
  getr regs 22 = w64 (SFa g pos + 436) ->
  getr regs 23 = w64 (-36) ->
  val_mem SEGS (rd W2 mem) (mf + 160) 8 (shadow_addr (SFa g pos)) ->
  val_mem SEGS (rd W2 mem) (mf + 168) 8 SHADOW_OFF ->
  bytes_at8 W2 mem (SFa g pos + V_hw + 4) (m_hwb g (m_nrec g)) ->
  sh_blk W2 mem (SFa g pos + V_hw) N_hw ->
  val_mem SEGS (rd W2 mem) (SFa g pos + V_hw) 4 (m_have g (m_nrec g)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SFa g pos + 432 <= a < SFa g pos + 436) ->
    aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1024) regs mem md) (EPOST g pos mf ly2 S2 W2 regs2 mem2).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 j.
remember (3 - j)%nat as t eqn:Ht. revert j Ht.
induction t as [|t IH]; intros j Ht regs mem md HJ Hfrs HPRE Hmfb Hmf32 Hj Hhave Hprior R2v R9v R8v R3v R4v
  Q2 Q3 Q4 Q8 Q9 Q25 Q24 R18 R19 R20 R21 R22 R23 V160 V168 Hhwbytes Hhwb VH KEEP.
{ exfalso. clear - Ht Hj. lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRS & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem md 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem md 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. Z.div_mod_to_equations. lia. }
set (nr := m_nrec g) in *. set (hwb := m_hwb g nr) in *.
assert (Hl8 : length hwb = 8%nat) by (unfold hwb, m_hwb; apply l_hwb_length).
pose proof (l_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRS) as HI0.
pose proof HI0 as (_ & Hrow6 & Hq0 & Hq1 & _).
pose proof (proj1 (GM ly2 S2 W2 mem md (VAL (A_OBJ 6)) 36 G_HW HAR2)) as Hq8.
pose proof (pa_val_range (A_OBJ 6)) as Rg6.
(* the shadow of a frame variable is never one of hw.have's bytes *)
assert (SHX : forall a, sh <= a < sh + 128 -> ~ (SF + 432 <= a < SF + 436)).
{ intros a Ha Hw. apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia
  | exact HSFapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | clear - Hw; lia]. }
(* the environment *)
remember (Eimg (Ereg regs [Z_to_bv 64 SB_L; Z_to_bv 64 sh])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB_L)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sh)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (E6 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
  by (apply (img_env_atomP E (A_OBJ 6) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Q9, R9v. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U6 : bv_unsigned (ew E (A_OBJ 6)) = VAL (A_OBJ 6)) by (rewrite E6; apply unsigned_lit_small; lia).
(* the symbolic state at the loop head *)
assert (HS0 : st_ok_pi SEGS VAL E ss_l
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1024)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_l. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold l_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 33 0) sh);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hsh1 C1; lia | clear; lia
        | exact V160].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; clear; lia
        | clear; lia | exact V168].
    + unfold l_tbl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U6. split; [clear - Rg6; lia|]. split; [clear - Hq1; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 0 4 (SLit 1) 1); [reflexivity | clear; lia | clear; lia |].
        apply (l_val4_garr8 SEGS _ _ HW_ROWS 0 1 _ Hrow6); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia].
      * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 12 4 (SLit 2) 2); [reflexivity | clear; lia | clear; lia |].
        apply (l_val4_garr8 SEGS _ _ HW_ROWS 12 2 _ Hrow6); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia].
      * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 24 4 (SLit 3) 3); [reflexivity | clear; lia | clear; lia |].
        apply (l_val4_garr8 SEGS _ _ HW_ROWS 24 3 _ Hrow6); [cbn; lia | lia | intros kk Hkk; do 4 (destruct kk as [|kk]; [reflexivity|]); lia].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, l_mf, l_tbl.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U6.
    split; [split; [|exact I] | split; [exact I | exact I]].
    right. clear - Hq1 Hmf0 C1. lia.
  - unfold facts_ok, l_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [| split; exact I]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SB_L; lia).
      split; [lia|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U6. split; [lia|]. split; [change (2 ^ 3) with 8; exact Hq8 | lia]. }
unfold cfg_at. change (w64 (BASE + 0x1024)) with (Z_to_bv 64 (BASE + 0x1024)).
destruct j as [|[|[|j]]]; [ | | | exfalso; clear - Hj; lia].
- (* row 0 *)
  pose proof (st_ok_pi_set_reg E _ _ 19%bv (SLit (0)) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R19; l_bvc)) as HSa.
  pose proof (st_ok_pi_set_reg E _ _ 20%bv (SOff (A_OBJ 6) 4) HSa ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite (l_denot_off E (A_OBJ 6) (VAL (A_OBJ 6)) 4 E6 Rg6), R20;
          unfold w64; f_equal; clear; lia)) as HSb.
  pose proof (st_ok_pi_set_reg E _ _ 21%bv (SOff (A_OBJ 6) 0) HSb ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite (l_denot_off E (A_OBJ 6) (VAL (A_OBJ 6)) 0 E6 Rg6), R21, Z.add_0_r;
          reflexivity)) as HSc.
  pose proof (st_ok_pi_set_reg E _ _ 23%bv (SLit (-36)) HSc ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R23; l_bvc)) as HS.
  clear HS0 HSa HSb HSc.
  (* to the bcmp call at 0x817a4 *)
  paj_run_shc RUNP RUNC HS HJ.
  { l_awr_ro. }
  l_ro_eq HMa.
  prreg HS (10%bv : bv 5) Ca0. prreg HS (11%bv : bv 5) Ca1. prreg HS (12%bv : bv 5) Ca2. prreg HS (1%bv : bv 5) Cra.
  prreg HS (2%bv : bv 5) Csp. prreg HS (3%bv : bv 5) Cgp. prreg HS (4%bv : bv 5) Ctp.
  change 247%nat with (A_OBJ 6) in Ca1. rewrite U6 in Ca1.
  rewrite (EE 22%nat 22%bv eq_refl), R22 in Ca0.
  rewrite (EE 2%nat 2%bv eq_refl), Q2, R2v in Csp. rewrite (EE 3%nat 3%bv eq_refl), Q3, R3v in Cgp.
  rewrite (EE 4%nat 4%bv eq_refl), Q4, R4v in Ctp.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) =>
    assert (UspC : spZ (ms_regs msC) = mf)
      by (unfold spZ; rewrite Csp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia) end.
  pmkst HS.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgs _ ?mm _) _) _ =>
    eapply (l_bcmp W2 rgs mm LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _
      (4 * Z.of_nat nr) (SF + 436) 0%nat hwb (mf - sp0) HJ) end.
    - exact (l_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRS).
    - clear; lia.
    - exact Hl8.
    - exact Ca0.
    - rewrite Ca1. unfold w64. f_equal. clear; lia.
    - rewrite Ca2. reflexivity.
    - rewrite UspC. clear; lia.
    - clear - Hmf32 Hsp0al. Z.div_mod_to_equations. lia.
    - clear - Hmfb. lia.
    - clear - Hmfb HSTK' Has HES. lia.
    - exact Cgp.
    - exact Ctp.
    - rewrite Cra. reflexivity.
    - clear - HSF0. lia.
    - clear - HSF1 C1. lia.
    - intros a Ha. clear - Ha HSF1 Hmf0 Hmfb HES C1. lia.
    - apply (amem_range_sub_app SF 1024 (SF + 436) 8 HSFapp); clear - HSF1; lia.
    - apply (block_shadow_range _ SHADOW_OFF (SF + V_hw) N_hw); [ | unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia].
      unfold sh_blk in Hhwb. apply (l_block_shadow_moved (aview SEGS (w_H W2) mem)); [|exact Hhwb].
      intros ii _. exact (aview_eq_of SEGS (w_H W2) mem _ _ (HMa _)).
    - apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 _ _ 4 pos (SF + 436) 8 (proj1 HJ) Hin4);
      rewrite ?EFa, ?HFB; clear; lia.
    - intros n Hn. rewrite (aview_eq_of SEGS (w_H W2) mem _ _ (HMa _)).
      replace (SF + 436 + Z.of_nat n) with (SF + V_hw + 4 + Z.of_nat n) by (unfold V_hw; clear; lia).
      rewrite (l_aview_garr8 SEGS (w_H W2) mem _ _ n Hhwbytes) by (rewrite length_map, Hl8; exact Hn).
      f_equal. apply l_nth_map_bv. rewrite Hl8. exact Hn. }
  cbv beta. intros W3 c3 _ (-> & regsB & memB & mdB & v & -> & HJB & HPB & HvB & HcmpB & HfrB & HpresB).
  clear HJ.
  (* back at 0x817a8: the two regions are kept *)
  jafter_call_keep_hi HS 512%nat regsB (mrestrict (w_H W2) memB) HPB [0; 1]%nat HS3.
  match type of HS3 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
    - apply (l_region_kept_ro SEGS E (w_H W2) _ memB 9%nat mf); [exact U9|].
      intros a Ha. apply HfrB; clear - Ha Hmf0 Hmfb Hshi H47 HES C1; lia.
    - apply (l_region_kept_ro SEGS E (w_H W2) _ memB (A_OBJ 6) (VAL (A_OBJ 6))); [exact U6|].
      intros a Ha. apply HfrB; clear - Ha Rg6 Hq1 Hmf0 HES C1; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regsB) CLOB) HEI ltac:(cbv; lia)) as HEIB.
  psrr_branch_pi RUNP BR HS.
  + (* the bcmp result is 0: row 0 is equal *)
    assert (HvJ : v = w64 0).
    { lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
        apply (l_br_eq Ev n v); [ l_hv HvB | exact Hc ] end. }
    apply HcmpB in HvJ. clear Hc.
    assert (HfJ : SlotModel.fam_cmp hwb = Z.of_nat 0 + 1)
      by (apply l_fam_cmp_hit; [clear; lia | exact Hprior | exact HvJ]).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (SHOK : sh_ok SEGS Bx_L l_SHT Ev (mrestrict (w_H W2) memB));
    [ unfold sh_ok, l_SHT; apply Forall_cons; [ | apply Forall_nil ];
      apply (shent_ok_of_range SEGS (w_H W2) memB Ev Bx_L (A_OBJ 6) (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 0 36
        (ro_usable_glob SEGS B G ly2 S2 W2 memB mdB (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 36 GM G_HW (proj1 HJB)
          ltac:(clear; lia) ltac:(clear; lia)));
      [ unfold U, Bx_L; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB_L; lia); reflexivity
      | exact (U_img_atom Ev HEIB (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
      | clear; lia | clear; lia
      | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold SHADOW_OFF; clear - Hxx Hq1; lia ]
    | ] end.
    (* the shadow test of HW_TABLE + 12 j and the family field, x23 := mf+160, to the compare *)
    paj_run_to_tok RUNTO HS HJB SHOK Bspan_L 0x107c.
    { l_awr_ro. }
    l_ro_eq HMc.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (AVL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem a)
    by (intros a Ha Hw; rewrite (aview_eq_of SEGS (w_H W2) memB (ms_mem msF) a (HMc _));
        rewrite (HfrB a Ha ltac:(rewrite HES; clear - Hw; lia));
        exact (aview_eq_of SEGS (w_H W2) mem _ a (HMa _)))
    end.
    prreg HS (18%bv : bv 5) P18. prreg HS (10%bv : bv 5) P10. prreg HS (14%bv : bv 5) P14.
    prreg HS (23%bv : bv 5) P23. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pmkst HS;
    apply (ETAILH LAWS g pos mf ly2 S2 W2 regs2 mem2 (ms_regs msF) (ms_mem msF) _ (Z.of_nat 0 + 1) HJB) end.
    * clear; lia.
    * rewrite P18, (EE 18%nat 18%bv eq_refl), R18, HfJ. reflexivity.
    * rewrite P10. l_bvc.
    * rewrite P2, (EE 2%nat 2%bv eq_refl). exact Q2.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact Q3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact Q4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact Q8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact Q9.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). exact Q25.
    * rewrite P24, (EE 24%nat 24%bv eq_refl). exact Q24.
    * rewrite P23, E33. reflexivity.
    * rewrite P14, E32. reflexivity.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (SF + V_hw) (SF + V_hw) 4 _); [|exact VH].
      intros kk Hkk. apply AVL; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * intros a Ha Hw Hh. rewrite (AVL a Ha ltac:(clear - Hw; lia)). exact (KEEP a Ha Hw Hh).
  + (* the bcmp result is not 0: row 0 is not equal *)
    assert (HnJ : map (fun b : byte => bv_unsigned b) hwb <> SlotModel.HWT 0%nat).
    { intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
        apply (l_br_ne Ev n v); [ l_hv HvB | exact Hc | apply HcmpB; exact Hrow ] end. }
    clear Hc.
    paj_run_to_sh RUNTOP HS HJB 0x1024.
    { l_awr_ro. }
    l_ro_eq HMc.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (AVL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem a)
    by (intros a Ha Hw; rewrite (aview_eq_of SEGS (w_H W2) memB (ms_mem msF) a (HMc _));
        rewrite (HfrB a Ha ltac:(rewrite HES; clear - Hw; lia));
        exact (aview_eq_of SEGS (w_H W2) mem _ a (HMa _)))
    end.
    prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pmkst HS;
    apply (IH (S 0%nat) ltac:(clear - Ht; lia) (ms_regs msF) (ms_mem msF) _ HJB Hfrs HPRE Hmfb Hmf32
      ltac:(clear; lia) Hhave) end.
    * intros j' Hj'. destruct (Nat.eq_dec j' 0%nat) as [-> | Hne]; [exact HnJ | apply Hprior; clear - Hj' Hne; lia].
    * exact R2v.
    * exact R9v.
    * exact R8v.
    * exact R3v.
    * exact R4v.
    * rewrite P2, (EE 2%nat 2%bv eq_refl). exact Q2.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact Q3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact Q4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact Q8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact Q9.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). exact Q25.
    * rewrite P24, (EE 24%nat 24%bv eq_refl). exact Q24.
    * rewrite P18, (EE 18%nat 18%bv eq_refl). exact R18.
    * rewrite P19. l_bvc.
    * rewrite P20. change 247%nat with (A_OBJ 6). rewrite U6. unfold w64. f_equal. clear. lia.
    * rewrite P21. change 247%nat with (A_OBJ 6). rewrite E6. reflexivity.
    * rewrite P22, (EE 22%nat 22%bv eq_refl). exact R22.
    * rewrite P23. l_bvc.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (mf + 160) (mf + 160) 8 _); [|exact V160].
      intros kk Hkk. apply AVL; clear - Hkk Hmf0 Hmfb Hshi H47 C1; lia.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (mf + 168) (mf + 168) 8 _); [|exact V168].
      intros kk Hkk. apply AVL; clear - Hkk Hmf0 Hmfb Hshi H47 C1; lia.
    * unfold bytes_at8 in *. apply (l_garr8_moved SEGS (w_H W2) (w_H W2) mem _ _ _); [|exact Hhwbytes].
      intros kk Hkk. rewrite length_map, Hl8 in Hkk. apply AVL; unfold V_hw; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * unfold sh_blk in *. apply (l_block_shadow_moved (aview SEGS (w_H W2) mem) _ SHADOW_OFF (SF + V_hw) N_hw);
      [|exact Hhwb].
      intros ii Hii. apply AVL.
      -- unfold shadow_of_addr, V_hw, N_hw in *. clear - Hii HSF0 HSF1 HSF64 C1. unfold SHADOW_OFF.
         Z.div_mod_to_equations. lia.
      -- unfold shadow_of_addr, V_hw, N_hw in *. clear - Hii HSF0 HSF1 HSF64 Hsh1 Esh Hmf0 C1. rewrite Esh in Hsh1.
         unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (SF + V_hw) (SF + V_hw) 4 _); [|exact VH].
      intros kk Hkk. apply AVL; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * intros a Ha Hw Hh. rewrite (AVL a Ha ltac:(clear - Hw; lia)). exact (KEEP a Ha Hw Hh).
- (* row 1 *)
  pose proof (st_ok_pi_set_reg E _ _ 19%bv (SLit (-12)) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R19; l_bvc)) as HSa.
  pose proof (st_ok_pi_set_reg E _ _ 20%bv (SOff (A_OBJ 6) 16) HSa ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite (l_denot_off E (A_OBJ 6) (VAL (A_OBJ 6)) 16 E6 Rg6), R20;
          unfold w64; f_equal; clear; lia)) as HSb.
  pose proof (st_ok_pi_set_reg E _ _ 21%bv (SOff (A_OBJ 6) 0) HSb ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite (l_denot_off E (A_OBJ 6) (VAL (A_OBJ 6)) 0 E6 Rg6), R21, Z.add_0_r;
          reflexivity)) as HSc.
  pose proof (st_ok_pi_set_reg E _ _ 23%bv (SLit (-36)) HSc ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R23; l_bvc)) as HS.
  clear HS0 HSa HSb HSc.
  (* to the bcmp call at 0x817a4 *)
  paj_run_shc RUNP RUNC HS HJ.
  { l_awr_ro. }
  l_ro_eq HMa.
  prreg HS (10%bv : bv 5) Ca0. prreg HS (11%bv : bv 5) Ca1. prreg HS (12%bv : bv 5) Ca2. prreg HS (1%bv : bv 5) Cra.
  prreg HS (2%bv : bv 5) Csp. prreg HS (3%bv : bv 5) Cgp. prreg HS (4%bv : bv 5) Ctp.
  change 247%nat with (A_OBJ 6) in Ca1. rewrite U6 in Ca1.
  rewrite (EE 22%nat 22%bv eq_refl), R22 in Ca0.
  rewrite (EE 2%nat 2%bv eq_refl), Q2, R2v in Csp. rewrite (EE 3%nat 3%bv eq_refl), Q3, R3v in Cgp.
  rewrite (EE 4%nat 4%bv eq_refl), Q4, R4v in Ctp.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) =>
    assert (UspC : spZ (ms_regs msC) = mf)
      by (unfold spZ; rewrite Csp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia) end.
  pmkst HS.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgs _ ?mm _) _) _ =>
    eapply (l_bcmp W2 rgs mm LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _
      (4 * Z.of_nat nr) (SF + 436) 1%nat hwb (mf - sp0) HJ) end.
    - exact (l_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRS).
    - clear; lia.
    - exact Hl8.
    - exact Ca0.
    - rewrite Ca1. unfold w64. f_equal. clear; lia.
    - rewrite Ca2. reflexivity.
    - rewrite UspC. clear; lia.
    - clear - Hmf32 Hsp0al. Z.div_mod_to_equations. lia.
    - clear - Hmfb. lia.
    - clear - Hmfb HSTK' Has HES. lia.
    - exact Cgp.
    - exact Ctp.
    - rewrite Cra. reflexivity.
    - clear - HSF0. lia.
    - clear - HSF1 C1. lia.
    - intros a Ha. clear - Ha HSF1 Hmf0 Hmfb HES C1. lia.
    - apply (amem_range_sub_app SF 1024 (SF + 436) 8 HSFapp); clear - HSF1; lia.
    - apply (block_shadow_range _ SHADOW_OFF (SF + V_hw) N_hw); [ | unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia].
      unfold sh_blk in Hhwb. apply (l_block_shadow_moved (aview SEGS (w_H W2) mem)); [|exact Hhwb].
      intros ii _. exact (aview_eq_of SEGS (w_H W2) mem _ _ (HMa _)).
    - apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 _ _ 4 pos (SF + 436) 8 (proj1 HJ) Hin4);
      rewrite ?EFa, ?HFB; clear; lia.
    - intros n Hn. rewrite (aview_eq_of SEGS (w_H W2) mem _ _ (HMa _)).
      replace (SF + 436 + Z.of_nat n) with (SF + V_hw + 4 + Z.of_nat n) by (unfold V_hw; clear; lia).
      rewrite (l_aview_garr8 SEGS (w_H W2) mem _ _ n Hhwbytes) by (rewrite length_map, Hl8; exact Hn).
      f_equal. apply l_nth_map_bv. rewrite Hl8. exact Hn. }
  cbv beta. intros W3 c3 _ (-> & regsB & memB & mdB & v & -> & HJB & HPB & HvB & HcmpB & HfrB & HpresB).
  clear HJ.
  (* back at 0x817a8: the two regions are kept *)
  jafter_call_keep_hi HS 512%nat regsB (mrestrict (w_H W2) memB) HPB [0; 1]%nat HS3.
  match type of HS3 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
    - apply (l_region_kept_ro SEGS E (w_H W2) _ memB 9%nat mf); [exact U9|].
      intros a Ha. apply HfrB; clear - Ha Hmf0 Hmfb Hshi H47 HES C1; lia.
    - apply (l_region_kept_ro SEGS E (w_H W2) _ memB (A_OBJ 6) (VAL (A_OBJ 6))); [exact U6|].
      intros a Ha. apply HfrB; clear - Ha Rg6 Hq1 Hmf0 HES C1; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regsB) CLOB) HEI ltac:(cbv; lia)) as HEIB.
  psrr_branch_pi RUNP BR HS.
  + (* the bcmp result is 0: row 1 is equal *)
    assert (HvJ : v = w64 0).
    { lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
        apply (l_br_eq Ev n v); [ l_hv HvB | exact Hc ] end. }
    apply HcmpB in HvJ. clear Hc.
    assert (HfJ : SlotModel.fam_cmp hwb = Z.of_nat 1 + 1)
      by (apply l_fam_cmp_hit; [clear; lia | exact Hprior | exact HvJ]).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (SHOK : sh_ok SEGS Bx_L l_SHT Ev (mrestrict (w_H W2) memB));
    [ unfold sh_ok, l_SHT; apply Forall_cons; [ | apply Forall_nil ];
      apply (shent_ok_of_range SEGS (w_H W2) memB Ev Bx_L (A_OBJ 6) (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 0 36
        (ro_usable_glob SEGS B G ly2 S2 W2 memB mdB (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 36 GM G_HW (proj1 HJB)
          ltac:(clear; lia) ltac:(clear; lia)));
      [ unfold U, Bx_L; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB_L; lia); reflexivity
      | exact (U_img_atom Ev HEIB (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
      | clear; lia | clear; lia
      | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold SHADOW_OFF; clear - Hxx Hq1; lia ]
    | ] end.
    (* the shadow test of HW_TABLE + 12 j and the family field, x23 := mf+160, to the compare *)
    paj_run_to_tok RUNTO HS HJB SHOK Bspan_L 0x107c.
    { l_awr_ro. }
    l_ro_eq HMc.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (AVL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem a)
    by (intros a Ha Hw; rewrite (aview_eq_of SEGS (w_H W2) memB (ms_mem msF) a (HMc _));
        rewrite (HfrB a Ha ltac:(rewrite HES; clear - Hw; lia));
        exact (aview_eq_of SEGS (w_H W2) mem _ a (HMa _)))
    end.
    prreg HS (18%bv : bv 5) P18. prreg HS (10%bv : bv 5) P10. prreg HS (14%bv : bv 5) P14.
    prreg HS (23%bv : bv 5) P23. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pmkst HS;
    apply (ETAILH LAWS g pos mf ly2 S2 W2 regs2 mem2 (ms_regs msF) (ms_mem msF) _ (Z.of_nat 1 + 1) HJB) end.
    * clear; lia.
    * rewrite P18, (EE 18%nat 18%bv eq_refl), R18, HfJ. reflexivity.
    * rewrite P10. l_bvc.
    * rewrite P2, (EE 2%nat 2%bv eq_refl). exact Q2.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact Q3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact Q4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact Q8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact Q9.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). exact Q25.
    * rewrite P24, (EE 24%nat 24%bv eq_refl). exact Q24.
    * rewrite P23, E33. reflexivity.
    * rewrite P14, E32. reflexivity.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (SF + V_hw) (SF + V_hw) 4 _); [|exact VH].
      intros kk Hkk. apply AVL; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * intros a Ha Hw Hh. rewrite (AVL a Ha ltac:(clear - Hw; lia)). exact (KEEP a Ha Hw Hh).
  + (* the bcmp result is not 0: row 1 is not equal *)
    assert (HnJ : map (fun b : byte => bv_unsigned b) hwb <> SlotModel.HWT 1%nat).
    { intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
        apply (l_br_ne Ev n v); [ l_hv HvB | exact Hc | apply HcmpB; exact Hrow ] end. }
    clear Hc.
    paj_run_to_sh RUNTOP HS HJB 0x1024.
    { l_awr_ro. }
    l_ro_eq HMc.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (AVL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem a)
    by (intros a Ha Hw; rewrite (aview_eq_of SEGS (w_H W2) memB (ms_mem msF) a (HMc _));
        rewrite (HfrB a Ha ltac:(rewrite HES; clear - Hw; lia));
        exact (aview_eq_of SEGS (w_H W2) mem _ a (HMa _)))
    end.
    prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pmkst HS;
    apply (IH (S 1%nat) ltac:(clear - Ht; lia) (ms_regs msF) (ms_mem msF) _ HJB Hfrs HPRE Hmfb Hmf32
      ltac:(clear; lia) Hhave) end.
    * intros j' Hj'. destruct (Nat.eq_dec j' 1%nat) as [-> | Hne]; [exact HnJ | apply Hprior; clear - Hj' Hne; lia].
    * exact R2v.
    * exact R9v.
    * exact R8v.
    * exact R3v.
    * exact R4v.
    * rewrite P2, (EE 2%nat 2%bv eq_refl). exact Q2.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact Q3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact Q4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact Q8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact Q9.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). exact Q25.
    * rewrite P24, (EE 24%nat 24%bv eq_refl). exact Q24.
    * rewrite P18, (EE 18%nat 18%bv eq_refl). exact R18.
    * rewrite P19. l_bvc.
    * rewrite P20. change 247%nat with (A_OBJ 6). rewrite U6. unfold w64. f_equal. clear. lia.
    * rewrite P21. change 247%nat with (A_OBJ 6). rewrite E6. reflexivity.
    * rewrite P22, (EE 22%nat 22%bv eq_refl). exact R22.
    * rewrite P23. l_bvc.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (mf + 160) (mf + 160) 8 _); [|exact V160].
      intros kk Hkk. apply AVL; clear - Hkk Hmf0 Hmfb Hshi H47 C1; lia.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (mf + 168) (mf + 168) 8 _); [|exact V168].
      intros kk Hkk. apply AVL; clear - Hkk Hmf0 Hmfb Hshi H47 C1; lia.
    * unfold bytes_at8 in *. apply (l_garr8_moved SEGS (w_H W2) (w_H W2) mem _ _ _); [|exact Hhwbytes].
      intros kk Hkk. rewrite length_map, Hl8 in Hkk. apply AVL; unfold V_hw; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * unfold sh_blk in *. apply (l_block_shadow_moved (aview SEGS (w_H W2) mem) _ SHADOW_OFF (SF + V_hw) N_hw);
      [|exact Hhwb].
      intros ii Hii. apply AVL.
      -- unfold shadow_of_addr, V_hw, N_hw in *. clear - Hii HSF0 HSF1 HSF64 C1. unfold SHADOW_OFF.
         Z.div_mod_to_equations. lia.
      -- unfold shadow_of_addr, V_hw, N_hw in *. clear - Hii HSF0 HSF1 HSF64 Hsh1 Esh Hmf0 C1. rewrite Esh in Hsh1.
         unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (SF + V_hw) (SF + V_hw) 4 _); [|exact VH].
      intros kk Hkk. apply AVL; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * intros a Ha Hw Hh. rewrite (AVL a Ha ltac:(clear - Hw; lia)). exact (KEEP a Ha Hw Hh).
- (* row 2 *)
  pose proof (st_ok_pi_set_reg E _ _ 19%bv (SLit (-24)) HS0 ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R19; l_bvc)) as HSa.
  pose proof (st_ok_pi_set_reg E _ _ 20%bv (SOff (A_OBJ 6) 28) HSa ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite (l_denot_off E (A_OBJ 6) (VAL (A_OBJ 6)) 28 E6 Rg6), R20;
          unfold w64; f_equal; clear; lia)) as HSb.
  pose proof (st_ok_pi_set_reg E _ _ 21%bv (SOff (A_OBJ 6) 0) HSb ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst]; rewrite (l_denot_off E (A_OBJ 6) (VAL (A_OBJ 6)) 0 E6 Rg6), R21, Z.add_0_r;
          reflexivity)) as HSc.
  pose proof (st_ok_pi_set_reg E _ _ 23%bv (SLit (-36)) HSc ltac:(discriminate)
    ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R23; l_bvc)) as HS.
  clear HS0 HSa HSb HSc.
  (* to the bcmp call at 0x817a4 *)
  paj_run_shc RUNP RUNC HS HJ.
  { l_awr_ro. }
  l_ro_eq HMa.
  prreg HS (10%bv : bv 5) Ca0. prreg HS (11%bv : bv 5) Ca1. prreg HS (12%bv : bv 5) Ca2. prreg HS (1%bv : bv 5) Cra.
  prreg HS (2%bv : bv 5) Csp. prreg HS (3%bv : bv 5) Cgp. prreg HS (4%bv : bv 5) Ctp.
  change 247%nat with (A_OBJ 6) in Ca1. rewrite U6 in Ca1.
  rewrite (EE 22%nat 22%bv eq_refl), R22 in Ca0.
  rewrite (EE 2%nat 2%bv eq_refl), Q2, R2v in Csp. rewrite (EE 3%nat 3%bv eq_refl), Q3, R3v in Cgp.
  rewrite (EE 4%nat 4%bv eq_refl), Q4, R4v in Ctp.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) =>
    assert (UspC : spZ (ms_regs msC) = mf)
      by (unfold spZ; rewrite Csp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia) end.
  pmkst HS.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgs _ ?mm _) _) _ =>
    eapply (l_bcmp W2 rgs mm LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _
      (4 * Z.of_nat nr) (SF + 436) 2%nat hwb (mf - sp0) HJ) end.
    - exact (l_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRS).
    - clear; lia.
    - exact Hl8.
    - exact Ca0.
    - rewrite Ca1. unfold w64. f_equal. clear; lia.
    - rewrite Ca2. reflexivity.
    - rewrite UspC. clear; lia.
    - clear - Hmf32 Hsp0al. Z.div_mod_to_equations. lia.
    - clear - Hmfb. lia.
    - clear - Hmfb HSTK' Has HES. lia.
    - exact Cgp.
    - exact Ctp.
    - rewrite Cra. reflexivity.
    - clear - HSF0. lia.
    - clear - HSF1 C1. lia.
    - intros a Ha. clear - Ha HSF1 Hmf0 Hmfb HES C1. lia.
    - apply (amem_range_sub_app SF 1024 (SF + 436) 8 HSFapp); clear - HSF1; lia.
    - apply (block_shadow_range _ SHADOW_OFF (SF + V_hw) N_hw); [ | unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia].
      unfold sh_blk in Hhwb. apply (l_block_shadow_moved (aview SEGS (w_H W2) mem)); [|exact Hhwb].
      intros ii _. exact (aview_eq_of SEGS (w_H W2) mem _ _ (HMa _)).
    - apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 _ _ 4 pos (SF + 436) 8 (proj1 HJ) Hin4);
      rewrite ?EFa, ?HFB; clear; lia.
    - intros n Hn. rewrite (aview_eq_of SEGS (w_H W2) mem _ _ (HMa _)).
      replace (SF + 436 + Z.of_nat n) with (SF + V_hw + 4 + Z.of_nat n) by (unfold V_hw; clear; lia).
      rewrite (l_aview_garr8 SEGS (w_H W2) mem _ _ n Hhwbytes) by (rewrite length_map, Hl8; exact Hn).
      f_equal. apply l_nth_map_bv. rewrite Hl8. exact Hn. }
  cbv beta. intros W3 c3 _ (-> & regsB & memB & mdB & v & -> & HJB & HPB & HvB & HcmpB & HfrB & HpresB).
  clear HJ.
  (* back at 0x817a8: the two regions are kept *)
  jafter_call_keep_hi HS 512%nat regsB (mrestrict (w_H W2) memB) HPB [0; 1]%nat HS3.
  match type of HS3 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]].
    - apply (l_region_kept_ro SEGS E (w_H W2) _ memB 9%nat mf); [exact U9|].
      intros a Ha. apply HfrB; clear - Ha Hmf0 Hmfb Hshi H47 HES C1; lia.
    - apply (l_region_kept_ro SEGS E (w_H W2) _ memB (A_OBJ 6) (VAL (A_OBJ 6))); [exact U6|].
      intros a Ha. apply HfrB; clear - Ha Rg6 Hq1 Hmf0 HES C1; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regsB) CLOB) HEI ltac:(cbv; lia)) as HEIB.
  psrr_branch_pi RUNP BR HS.
  + (* the bcmp result is 0: row 2 is equal *)
    assert (HvJ : v = w64 0).
    { lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
        apply (l_br_eq Ev n v); [ l_hv HvB | exact Hc ] end. }
    apply HcmpB in HvJ. clear Hc.
    assert (HfJ : SlotModel.fam_cmp hwb = Z.of_nat 2 + 1)
      by (apply l_fam_cmp_hit; [clear; lia | exact Hprior | exact HvJ]).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (SHOK : sh_ok SEGS Bx_L l_SHT Ev (mrestrict (w_H W2) memB));
    [ unfold sh_ok, l_SHT; apply Forall_cons; [ | apply Forall_nil ];
      apply (shent_ok_of_range SEGS (w_H W2) memB Ev Bx_L (A_OBJ 6) (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 0 36
        (ro_usable_glob SEGS B G ly2 S2 W2 memB mdB (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 36 GM G_HW (proj1 HJB)
          ltac:(clear; lia) ltac:(clear; lia)));
      [ unfold U, Bx_L; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB_L; lia); reflexivity
      | exact (U_img_atom Ev HEIB (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
      | clear; lia | clear; lia
      | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold SHADOW_OFF; clear - Hxx Hq1; lia ]
    | ] end.
    (* the shadow test of HW_TABLE + 12 j and the family field, x23 := mf+160, to the compare *)
    paj_run_to_tok RUNTO HS HJB SHOK Bspan_L 0x107c.
    { l_awr_ro. }
    l_ro_eq HMc.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (AVL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem a)
    by (intros a Ha Hw; rewrite (aview_eq_of SEGS (w_H W2) memB (ms_mem msF) a (HMc _));
        rewrite (HfrB a Ha ltac:(rewrite HES; clear - Hw; lia));
        exact (aview_eq_of SEGS (w_H W2) mem _ a (HMa _)))
    end.
    prreg HS (18%bv : bv 5) P18. prreg HS (10%bv : bv 5) P10. prreg HS (14%bv : bv 5) P14.
    prreg HS (23%bv : bv 5) P23. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pmkst HS;
    apply (ETAILH LAWS g pos mf ly2 S2 W2 regs2 mem2 (ms_regs msF) (ms_mem msF) _ (Z.of_nat 2 + 1) HJB) end.
    * clear; lia.
    * rewrite P18, (EE 18%nat 18%bv eq_refl), R18, HfJ. reflexivity.
    * rewrite P10. l_bvc.
    * rewrite P2, (EE 2%nat 2%bv eq_refl). exact Q2.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact Q3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact Q4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact Q8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact Q9.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). exact Q25.
    * rewrite P24, (EE 24%nat 24%bv eq_refl). exact Q24.
    * rewrite P23, E33. reflexivity.
    * rewrite P14, E32. reflexivity.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (SF + V_hw) (SF + V_hw) 4 _); [|exact VH].
      intros kk Hkk. apply AVL; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * intros a Ha Hw Hh. rewrite (AVL a Ha ltac:(clear - Hw; lia)). exact (KEEP a Ha Hw Hh).
  + (* the bcmp result is not 0: row 2 is not equal *)
    assert (HnJ : map (fun b : byte => bv_unsigned b) hwb <> SlotModel.HWT 2%nat).
    { intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = _ =>
        apply (l_br_ne Ev n v); [ l_hv HvB | exact Hc | apply HcmpB; exact Hrow ] end. }
    clear Hc.
    paj_run_to_sh RUNTOP HS HJB 0x107c.
    { l_awr_ro. }
    l_ro_eq HMc.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (AVL : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
      aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem a)
    by (intros a Ha Hw; rewrite (aview_eq_of SEGS (w_H W2) memB (ms_mem msF) a (HMc _));
        rewrite (HfrB a Ha ltac:(rewrite HES; clear - Hw; lia));
        exact (aview_eq_of SEGS (w_H W2) mem _ a (HMa _)))
    end.
    assert (Hnone : forall j', (j' < 3)%nat -> map (fun b : byte => bv_unsigned b) hwb <> SlotModel.HWT j').
    { intros j' Hj'. destruct (Nat.eq_dec j' 2) as [-> | Hne]; [exact HnJ | apply Hprior; clear - Hj' Hne; lia]. }
    prreg HS (18%bv : bv 5) P18. prreg HS (10%bv : bv 5) P10. prreg HS (14%bv : bv 5) P14.
    prreg HS (23%bv : bv 5) P23. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    pmkst HS;
    apply (ETAILH LAWS g pos mf ly2 S2 W2 regs2 mem2 (ms_regs msF) (ms_mem msF) _ 0 HJB) end.
    * clear; lia.
    * rewrite P18, (EE 18%nat 18%bv eq_refl), R18, (l_fam_cmp_none hwb Hnone). reflexivity.
    * rewrite P10. l_bvc.
    * rewrite P2, (EE 2%nat 2%bv eq_refl). exact Q2.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). exact Q3.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). exact Q4.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). exact Q8.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). exact Q9.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). exact Q25.
    * rewrite P24, (EE 24%nat 24%bv eq_refl). exact Q24.
    * rewrite P23, E33. reflexivity.
    * rewrite P14, E32. reflexivity.
    * apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem _ (SF + V_hw) (SF + V_hw) 4 _); [|exact VH].
      intros kk Hkk. apply AVL; unfold V_hw in *; clear - Hkk HSF0 HSF1 Hmf0 C1; lia.
    * intros a Ha Hw Hh. rewrite (AVL a Ha ltac:(clear - Hw; lia)). exact (KEEP a Ha Hw Hh).
Qed.
End L.

Lemma e_loop : ELOOP.
Proof.
unfold e_loop_stmt.
intros HSTK LAWS RO HRO G GM IV G_HW HIMG ABCMP ETAILH. intros.
eapply l_loop; eassumption.
Qed.

Check (e_loop : ELOOP).

End c.
End b.
End a.
