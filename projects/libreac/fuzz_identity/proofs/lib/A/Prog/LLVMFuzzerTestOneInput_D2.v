(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v; 1812 of its 1890 lines of code are new or changed and 502 lines of the source are left out. *)
(* Segment D2 of LLVMFuzzerTestOneInput's ASan walk: 0x80d04 to the four exits of the record switch.
   seg_D2 of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_D1_end (the third same_id compare has passed) to
   inv_caseV (0x80f20), inv_caseM (0x81170), inv_caseF (0x81208) or inv_tail (0x813b4).

   The code (internal path):
   - 0x80d04..0x80d90, the rest of same_id on `again` (SF+112) and `id` (SF+352): bcmp of the two model names
     (0x80d10, 17 bytes), the byte at 20, the halfwords at 22, 24, 26, bcmp of the two raw version blocks
     (0x80d70, 8 bytes), the byte at 36. Both structs hold the same bytes (m_id (S i)), so every compare holds.
   - 0x80d94, the ingest result: r = 0 goes to 0x80e1c, bcmp(before, id, 38) (an ignored record changes
     nothing), then the three "would have been accepted" checks (0x80e40..0x80ed8, 0x81368..0x813b0) and the
     join 0x813b4. r = 1 is the switch on the address: 0x1000 to 0x81170, 0x600 to 0x80edc (n >= 8, the
     has_reac_version byte, bcmp(id.raw, pl, 8) at 0x80f04, to 0x80f20), 0 to 0x80db8 (n >= 4, has_fw, the
     four digit checks of pl, to 0x81208).
   Every abort branch is refuted from the plain model of the harness (lib/Prog/SlotModel.v, RcIdentModel.v):
   the walk splits on the record's result and address before the switch and gives the engine the facts of
   each case. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YC4b.v turns lia's division / modulo handling off for every file that loads it; this file needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the plain model's facts the segment needs (lib/Prog/SlotModel.v, RcIdentModel.v) ----------------- *)
Module D2M.
Import SlotModel RcIdentModel.
Section m.
Variable inp : list byte.
Variable i : nat.
Lemma upd_len : forall l off bs, (off + length bs <= length l)%nat -> length (upd l off bs) = length l.
Proof. exact upd_length. Qed.
Lemma r01 : rec_r inp i = 0 \/ rec_r inp i = 1.
Proof. apply rec_r_range. Qed.
Lemma ignored : rec_r inp i = 0 -> rec_id inp (S i) = rec_id inp i.
Proof. intros H. cbn [rec_id]. apply ING_ignored. exact H. Qed.
Lemma raw_range : 0 <= rec_raw inp i <= 65535.
Proof.
unfold rec_raw, h_raw, h_lo, h_hi. pose proof (inb_range inp (rec_c inp i)). pose proof (inb_range inp (rec_c inp i + 1)). lia.
Qed.
Lemma addr_range : 0 <= rec_addr inp i <= 65535 /\
(rec_addr inp i <> 0 -> rec_addr inp i <> 0x600 -> rec_addr inp i <> 0x1000 -> 49152 <= rec_addr inp i).
Proof.
pose proof raw_range as R. unfold rec_addr, pick, ADDR_FIRMWARE, ADDR_REAC_VERSION, ADDR_MODEL_NAME.
destruct (Z.eqb_spec (rec_raw inp i / 16384) 0); [split; [lia | intros H; contradiction]|].
destruct (Z.eqb_spec (rec_raw inp i / 16384) 1); [split; [lia | intros _ H; contradiction]|].
destruct (Z.eqb_spec (rec_raw inp i / 16384) 2); [split; [lia | intros _ _ H; contradiction]|].
split; [exact R|]. intros _ _ _.
assert (0 <= rec_raw inp i / 16384) by (apply Z.div_pos; lia).
assert (3 <= rec_raw inp i / 16384) by lia.
pose proof (Z.mul_div_le (rec_raw inp i) 16384 ltac:(lia)). lia.
Qed.
Lemma accepted_addr : rec_r inp i = 1 -> rec_addr inp i = 0 \/ rec_addr inp i = 0x600 \/ rec_addr inp i = 0x1000.
Proof.
unfold rec_r, ING. intros H.
destruct (Z.eqb_spec (rec_addr inp i) ADDR_FIRMWARE) as [E|E]; [left; exact E|].
destruct (Z.eqb_spec (rec_addr inp i) ADDR_MODEL_NAME) as [E'|E']; [right; right; exact E'|].
destruct (Z.eqb_spec (rec_addr inp i) ADDR_REAC_VERSION) as [E''|E'']; [right; left; exact E''|].
cbn [fst] in H. discriminate H.
Qed.
Lemma k_len : length (rec_pl inp i) = Z.to_nat (rec_k inp i) /\ 0 <= rec_k inp i <= 255.
Proof. split; [apply rec_pl_length | apply rec_k_range]. Qed.
Lemma digits4 : forall p : list byte, all_digits (firstn 4 p) = true -> (4 <= length p)%nat ->
bz (nthb p 0) <= 9 /\ bz (nthb p 1) <= 9 /\ bz (nthb p 2) <= 9 /\ bz (nthb p 3) <= 9.
Proof.
intros p H Hl. destruct p as [|b0 [|b1 [|b2 [|b3 p]]]]; cbn [length] in Hl; try lia.
cbn [all_digits firstn forallb] in H. unfold nthb. cbn [nth].
repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end. lia.
Qed.
Lemma digits4_neg : forall p : list byte, all_digits (firstn 4 p) = false -> (4 <= length p)%nat ->
~ (bz (nthb p 0) <= 9 /\ bz (nthb p 1) <= 9 /\ bz (nthb p 2) <= 9 /\ bz (nthb p 3) <= 9).
Proof.
intros p H Hl (H0 & H1 & H2 & H3). destruct p as [|b0 [|b1 [|b2 [|b3 p]]]]; cbn [length] in Hl; try lia.
unfold nthb in *. cbn [nth] in *. cbn [all_digits firstn forallb] in H.
rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2), (proj2 (Z.leb_le _ _) H3) in H.
cbn in H. discriminate H.
Qed.
(* The firmware record accepted: four digits, and has_fw is set in the new identity. *)
Lemma fw_accepted : rec_r inp i = 1 -> rec_addr inp i = 0 ->
4 <= rec_k inp i /\
bz (nthb (rec_pl inp i) 0) <= 9 /\ bz (nthb (rec_pl inp i) 1) <= 9 /\
bz (nthb (rec_pl inp i) 2) <= 9 /\ bz (nthb (rec_pl inp i) 3) <= 9 /\
bz (nthb (rec_id inp (S i)) 2) = 1.
Proof.
intros Hr Ha. pose proof k_len as [Hk Hkr]. pose proof (rec_id_length inp i) as Hid.
unfold rec_r in Hr. cbn [rec_id]. rewrite Ha in *. unfold ING in *. cbn [Z.eqb Pos.eqb] in *.
unfold ADDR_FIRMWARE in *. cbn [Z.eqb] in *. unfold ing_firmware in *.
destruct ((4 <=? length (rec_pl inp i))%nat && all_digits (firstn 4 (rec_pl inp i)))%bool eqn:C;
[|cbn [fst] in Hr; discriminate Hr].
apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1.
destruct (digits4 _ C2 C1) as (D0 & D1 & D2 & D3).
split; [lia|]. split; [exact D0|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
cbn [snd]. unfold nthb. rewrite nth_upd_in.
- reflexivity.
- rewrite upd_len; [unfold ID_SIZE, OFF_HAS_FW in *; lia | cbn [length le16]; unfold ID_SIZE, OFF_FW in *; lia].
- unfold OFF_HAS_FW. cbn [length]. lia.
Qed.
(* The version record accepted: eight bytes, has_reac_version set, and the raw block is the payload's head. *)
Lemma ver_accepted : rec_r inp i = 1 -> rec_addr inp i = 0x600 ->
8 <= rec_k inp i /\ has_reac_version (rec_id inp (S i)) = 1 /\
raw (rec_id inp (S i)) = firstn 8 (rec_pl inp i).
Proof.
intros Hr Ha. pose proof k_len as [Hk Hkr]. pose proof (rec_id_length inp i) as Hid.
unfold rec_r in Hr. cbn [rec_id]. rewrite Ha in *. change 0x600 with ADDR_REAC_VERSION in *.
destruct (Nat.leb_spec 8 (length (rec_pl inp i))) as [L|L].
- destruct (ING_ver_long (rec_id inp i) (rec_pl inp i) Hid L) as (H1 & H2 & _). split; [lia|]. split; assumption.
- rewrite ING_ver_short in Hr by exact L. cbn [fst] in Hr. discriminate Hr.
Qed.
Lemma nth_firstn_lt : forall (l : list byte) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
induction l as [|x l IH]; intros n j d H.
- rewrite firstn_nil. reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma nth_skipn_add : forall (l : list byte) k j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
induction l as [|x l IH]; intros k j d.
- rewrite skipn_nil. generalize (k + j)%nat. intros m. destruct j, m; reflexivity.
- destruct k as [|k]; cbn [skipn Nat.add nth]; [reflexivity | apply IH].
Qed.
(* The version record accepted: id's raw block holds the payload's first eight bytes. *)
Lemma raw_nth : rec_r inp i = 1 -> rec_addr inp i = 0x600 -> forall j, (j < 8)%nat ->
nthb (rec_id inp (S i)) (28 + j) = nthb (rec_pl inp i) (0 + j).
Proof.
intros Hr Ha j Hj. destruct (ver_accepted Hr Ha) as (_ & _ & Hraw).
unfold raw, get, OFF_RAW, REAC_VER_LEN in Hraw.
pose proof (f_equal (fun l => nth j l (zb 0)) Hraw) as Hn. cbv beta in Hn.
rewrite nth_firstn_lt in Hn by exact Hj. rewrite nth_firstn_lt in Hn by exact Hj.
rewrite nth_skipn_add in Hn. unfold nthb. exact Hn.
Qed.
Lemma fw_ignored : rec_r inp i = 0 -> rec_addr inp i = 0 -> 4 <= rec_k inp i ->
~ (bz (nthb (rec_pl inp i) 0) <= 9 /\ bz (nthb (rec_pl inp i) 1) <= 9 /\
   bz (nthb (rec_pl inp i) 2) <= 9 /\ bz (nthb (rec_pl inp i) 3) <= 9).
Proof.
intros Hr Ha Hk4. pose proof k_len as [Hk Hkr].
unfold rec_r in Hr. rewrite Ha in Hr. unfold ING, ADDR_FIRMWARE in Hr. cbn [Z.eqb] in Hr. unfold ing_firmware in Hr.
assert (C1 : (4 <=? length (rec_pl inp i))%nat = true) by (apply Nat.leb_le; lia).
rewrite C1 in Hr. cbn [andb] in Hr.
destruct (all_digits (firstn 4 (rec_pl inp i))) eqn:C2; [cbn [fst] in Hr; discriminate Hr|].
apply digits4_neg; [exact C2 | lia].
Qed.
Lemma ver_ignored : rec_r inp i = 0 -> rec_addr inp i = 0x600 -> rec_k inp i < 8.
Proof.
intros Hr Ha. pose proof k_len as [Hk Hkr]. pose proof (rec_id_length inp i) as Hid.
unfold rec_r in Hr. rewrite Ha in Hr. change 0x600 with ADDR_REAC_VERSION in Hr.
destruct (Nat.leb_spec 8 (length (rec_pl inp i))) as [L|L]; [|lia].
rewrite ING_ver_dispatch in Hr. unfold ing_version in Hr.
destruct (Nat.leb_spec REAC_VER_LEN (length (rec_pl inp i))) as [E|E]; [cbn [fst] in Hr; discriminate Hr|].
unfold REAC_VER_LEN in E. lia.
Qed.
Lemma name_len_zero : forall p : list byte, (2 <= length p)%nat -> name_len p = 0%nat -> bz (nthb p 1) = 0.
Proof.
intros p Hl H. unfold name_len, NAME_CAP in H. cbv zeta in H.
destruct p as [|b0 [|b1 p]]; cbn [length] in Hl; try lia.
cbn [skipn] in H. unfold nthb. cbn [nth].
destruct (Nat.min (length (b0 :: b1 :: p) - 1) (17 - 1)) as [|n'] eqn:En; [cbn [length] in En; lia|].
cbn [firstn first_zero] in H.
destruct (Z.eqb_spec (bz b1) 0) as [Z0|Z0]; [exact Z0 | lia].
Qed.
Lemma name_ignored : rec_r inp i = 0 -> rec_addr inp i = 0x1000 -> 2 <= rec_k inp i ->
bz (nthb (rec_pl inp i) 1) = 0.
Proof.
intros Hr Ha Hk2. pose proof k_len as [Hk Hkr].
unfold rec_r in Hr. rewrite Ha in Hr. unfold ING, ADDR_FIRMWARE, ADDR_MODEL_NAME in Hr. cbn [Z.eqb] in Hr.
unfold ing_name in Hr. cbv zeta in Hr.
assert (C1 : (2 <=? length (rec_pl inp i))%nat = true) by (apply Nat.leb_le; lia).
rewrite C1 in Hr. cbn [andb] in Hr.
destruct (Nat.leb_spec 1 (name_len (rec_pl inp i))) as [W|W]; [cbn [fst] in Hr; discriminate Hr|].
apply name_len_zero; lia.
Qed.
(* The hardware block changes only with an accepted version record of eight bytes or more. *)
Lemma hw_kept : rec_addr inp i <> 0x600 \/ rec_r inp i = 0 ->
rec_have inp (S i) = rec_have inp i /\ rec_hwb inp (S i) = rec_hwb inp i.
Proof.
intros H. assert (E : rec_hw inp (S i) = rec_hw inp i).
{ cbn [rec_hw]. destruct (Z.eqb_spec (rec_addr inp i) ADDR_REAC_VERSION) as [Ea|Ea]; cbn [andb]; [|reflexivity].
destruct H as [H|H]; [unfold ADDR_REAC_VERSION in Ea; contradiction|].
pose proof (ver_ignored H Ea) as L. destruct (Z.leb_spec 8 (rec_k inp i)); [lia | reflexivity]. }
unfold rec_have, rec_hwb. rewrite E. split; reflexivity.
Qed.
Lemma hwb_len : (length (rec_hwb inp i) <= 8)%nat.
Proof.
assert (H : forall j, match rec_hw inp j with Some h => (length h <= 8)%nat | None => True end).
{ induction j as [|j IH]; cbn [rec_hw]; [exact I|].
match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota; [rewrite length_firstn; lia | exact IH]. }
unfold rec_hwb. specialize (H i). destruct (rec_hw inp i); [exact H | rewrite repeat_length; lia].
Qed.
End m.
End D2M.

(* ---- the symbolic state at 0x80d04 ----------------------------------------------------------------------- *)
(* Atoms: the registers are 0..31 (sr_atoms); 32 the shadow base; 33 the side-stack frame SF; 34 the payload
   copy pl; 35..39 the five fields of `again` and `id` the engine compares (the byte at 20, the halfwords at 22,
   24, 26, the byte at 36), one atom per field because both structs hold m_id (S i); 40 the cursor in mf+136;
   41 the record index in mf+160; 42..45 the payload's first four bytes. *)
Definition SB_D2 : Z := 0x7fff8000.
Definition Bx_D2 : sv := SOff 32 0.
Definition Bspan_D2 : Z * Z := (SB_D2, SB_D2 + 2 ^ 44 - 1).
Definition AF_D2 : Z := 0x5f8.
Definition AF_D2V : Z := 0x814.
Definition AF_D2M : Z := 0xa64.
Definition AF_D2F : Z := 0xafc.
Definition AF_D2T : Z := 0xca8.
(* The machine frame (base x9 = s1 = mf), the slots the segment reads; read-only. *)
Definition c8 (o : Z) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 v).
Definition mf_region_D2 : YP09.region :=
YP09.mkRegion (Some 9%nat) 40 192 0 0
[ c8 40 (SOff 33 192); c8 72 (SOff 33 288); c8 88 (SOff 33 32); c8 96 (SOff 33 140); c8 104 (SOff 33 115);
  c8 120 (SOff 33 380); c8 128 (SOff 33 355); c8 136 (SOff 40 0); c8 152 (SOff 34 0); c8 160 (SOff 41 0);
  c8 168 (SOff 33 112); c8 176 (SOff 32 0); c8 184 (SOff 33 352) ].
(* The side-stack frame (base SF): the compared fields of `again` (SF+112) and `id` (SF+352); read-only. *)
Definition sf_region_D2 : YP09.region :=
YP09.mkRegion (Some 33%nat) 112 390 0 0
[ YP09.mkChunk 132 (CVal 1 (SOff 35 0)); YP09.mkChunk 134 (CVal 2 (SOff 36 0));
  YP09.mkChunk 136 (CVal 2 (SOff 37 0)); YP09.mkChunk 138 (CVal 2 (SOff 38 0));
  YP09.mkChunk 148 (CVal 1 (SOff 39 0));
  YP09.mkChunk 372 (CVal 1 (SOff 35 0)); YP09.mkChunk 374 (CVal 2 (SOff 36 0));
  YP09.mkChunk 376 (CVal 2 (SOff 37 0)); YP09.mkChunk 378 (CVal 2 (SOff 38 0));
  YP09.mkChunk 388 (CVal 1 (SOff 39 0)) ].
Definition regions_D2 : smem := [mf_region_D2; sf_region_D2].
Definition facts_D2 : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB_D2 SB_D2 0);
          (33%nat, HPTR 6); (34%nat, HPTR 4);
          (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0); (38%nat, mkAF 0 65535 0);
          (39%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0);
          (45%nat, mkAF 0 255 0); (22%nat, mkAF 0 255 0); (25%nat, mkAF 0 255 0); (27%nat, mkAF 0 65535 0) ]
[] [].
Definition ss_D2 : sstate := mkSS AF_D2 sr_atoms regions_D2 None facts_D2.

(* The payload copy's byte 1 as the literal 0 (an ignored model-name record of two bytes or more). *)
Definition plr2_D2 : YP09.region := YP09.mkRegion (Some 34%nat) 0 2 0 0 [YP09.mkChunk 1 (CVal 1 (SLit 0))].
Definition ro_regions (rs : smem) : bool := forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs.
Lemma ro_nowr : forall E rs a, ro_regions rs = true -> ~ in_wrange E rs a.
Proof.
intros E rs a Hro (rg & Hin & Ha). unfold ro_regions in Hro. rewrite forallb_forall in Hro.
specialize (Hro rg Hin). apply Z.leb_le in Hro. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

(* ---- memory kept outside the bcmp window [mf - 2 ESTACK, mf) -------------------------------------------- *)
Definition d2_keep (W : world SEGS) (m0 m1 : word -> option byte) (mf : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a.
Lemma keep_refl : forall W m mf, d2_keep W m m mf.
Proof. intros W m mf a _ _. reflexivity. Qed.
Lemma keep_trans : forall W m0 m1 m2 mf, d2_keep W m0 m1 mf -> d2_keep W m1 m2 mf -> d2_keep W m0 m2 mf.
Proof. intros W m0 m1 m2 mf H1 H2 a Ha Hw. rewrite (H2 a Ha Hw). exact (H1 a Ha Hw). Qed.
Lemma keep_frame : forall W E rs m0 m1 m2 mf, ro_regions rs = true ->
frame_of E rs (rd W m1) (rd W m2) -> d2_keep W m0 m1 mf -> d2_keep W m0 m2 mf.
Proof.
intros W E rs m0 m1 m2 mf Hro HF HK a Ha Hw. rewrite <- (HK a Ha Hw). apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by lia. apply ro_nowr. exact Hro.
Qed.
Lemma keep_vm : forall W m0 m1 mf a n v, d2_keep W m0 m1 mf -> 0 <= mf <= 2 ^ 47 ->
((0 <= a /\ a + Z.of_nat n <= mf - 2 * ESTACK) \/ (mf <= a /\ a + Z.of_nat n <= 2 ^ 64)) ->
val_mem SEGS (rd W m0) a n v -> val_mem SEGS (rd W m1) a n v.
Proof.
intros W m0 m1 mf a n v HK H47 Ha Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m0 m1 a n v); [|exact Hv].
intros j Hj. apply HK; unfold ESTACK in *; destruct Ha as [[Ha1 Ha2] | [Ha1 Ha2]]; lia.
Qed.
Lemma keep_bytes : forall W m0 m1 mf a bs, d2_keep W m0 m1 mf -> mf <= 2 ^ 47 ->
0 <= a -> a + Z.of_nat (length bs) <= mf - 2 * ESTACK -> bytes_at8 W m0 a bs -> bytes_at8 W m1 a bs.
Proof.
intros W m0 m1 mf a bs HK H47 Ha Han Hb. unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hb).
intros x Hx. rewrite length_map in Hx. apply (mbyte_of_aview SEGS).
generalize dependent (Z.of_nat (length bs)). intros nz Han Hx. apply HK; unfold ESTACK in *; lia.
Qed.
Lemma keep_shadow_cell : forall W m0 m1 mf a j, d2_keep W m0 m1 mf -> alloc_ceiling + 2 * ESTACK <= mf ->
0 <= a <= 2 ^ 47 -> 0 <= j <= 2 ^ 44 ->
aview SEGS (w_H W) m1 (shadow_of_addr SHADOW_OFF a + j) = aview SEGS (w_H W) m0 (shadow_of_addr SHADOW_OFF a + j).
Proof.
intros W m0 m1 mf a j HK Hce Ha Hj. pose proof asan_consts as (C1 & _).
assert (A8 : 0 <= a / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
apply HK; unfold shadow_of_addr, SHADOW_OFF, ESTACK in *; lia.
Qed.
Lemma keep_blk : forall W m0 m1 mf a n, d2_keep W m0 m1 mf -> alloc_ceiling + 2 * ESTACK <= mf ->
0 <= a -> a + n <= 2 ^ 47 -> 0 <= n -> sh_blk W m0 a n -> sh_blk W m1 a n.
Proof.
intros W m0 m1 mf a n HK Hce Ha Han Hn Hb. unfold sh_blk in *.
apply (block_shadow_agree (aview SEGS (w_H W) m0) (aview SEGS (w_H W) m1) SHADOW_OFF a n); [|exact Hb].
intros j Hj. assert (J : (n + 7) / 8 <= 2 ^ 44 + 1) by (apply Z.div_le_upper_bound; lia).
apply (keep_shadow_cell W m0 m1 mf a j HK Hce); lia.
Qed.
Lemma keep_zero : forall W m0 m1 mf a n, d2_keep W m0 m1 mf -> alloc_ceiling + 2 * ESTACK <= mf ->
0 <= a -> a + n <= 2 ^ 47 -> 0 <= n -> sh_zero W m0 a n -> sh_zero W m1 a n.
Proof.
intros W m0 m1 mf a n HK Hce Ha Han Hn Hb j Hj. unfold sh_zero, zero_shadow in *.
assert (J : n / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
rewrite (keep_shadow_cell W m0 m1 mf a j HK Hce) by lia. exact (Hb j Hj).
Qed.
Lemma bytes_aview : forall W m a bs j, bytes_at8 W m a bs -> (j < length bs)%nat ->
aview SEGS (w_H W) m (a + Z.of_nat j) = Some (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof.
intros W m a bs j Hb Hj. unfold bytes_at8 in Hb.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
pose proof (garr8_mbyte SEGS _ _ _ j Hb Hj') as Hm. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by exact Hj'. rewrite map_nth.
unfold RcIdentModel.bz, RcIdentModel.nthb. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- an operand of a bcmp call: what abcmp_realizes asks of each range, outside the call's window ------- *)
Definition d2_opnd (W : world SEGS) (m : word -> option byte) (x n : Z) : Prop :=
0 <= x /\ x + n <= alloc_ceiling /\ 0 <= n < 2 ^ 32 /\
(forall a, x <= a < x + n -> aview SEGS (w_H W) m a <> None) /\
amem_range x n /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x n /\
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) x n).
Lemma opnd_keep : forall W m0 m1 mf x n, d2_keep W m0 m1 mf -> alloc_ceiling + 2 * ESTACK <= mf ->
d2_opnd W m0 x n -> d2_opnd W m1 x n.
Proof.
intros W m0 m1 mf x n HK Hce (H0 & H1 & H2 & H3 & H4 & H5 & H6). pose proof asan_consts as (C1 & C2 & _).
assert (HK' : forall s, 0 <= s < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= s < mf) ->
aview SEGS (w_H W) m1 s = aview SEGS (w_H W) m0 s) by exact HK.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [intros a Ha; rewrite (HK a) by (unfold ESTACK in *; lia); exact (H3 a Ha)|].
split; [exact H4|].
split; [apply (range_addressable_kept_win _ _ (mf - 2 * ESTACK) mf x n HK'); [unfold ESTACK in *; lia | lia | lia | exact H5]|].
intros Hn. apply (shadow_hull_vis_kept_win _ _ (mf - 2 * ESTACK) mf x n HK'); [unfold ESTACK in *; lia | lia | lia | exact Hn | exact (H6 Hn)].
Qed.

Section c.
(* The Section of LLVMFuzzerTestOneInput_inv.v, in the same order (seg_D2's arguments). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What the segment needs: the contract's window covers the bcmp interceptor's 2 ESTACK below the frame, the
   allocator's laws, the bcmp interceptor's contract, and cgif ACfh.v:162-164 for the fds and files. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
#[local] Notation AJ g pos ly2 S2 W2 mem2 md2 k :=
(ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 k).

Lemma d2_geom : forall g pos mf ly2 S2 W2 mem2 md2 k,
AJ g pos ly2 S2 W2 mem2 md2 k -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
alloc_ceiling + 2 * ESTACK <= mf /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\ 2 * ESTACK + 336 <= LLVMF_STK.
Proof.
intros g pos mf ly2 S2 W2 mem2 md2 k HJ Hmf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
unfold STK_LLVMF, ASTACK, ESTACK in *. lia.
Qed.
Lemma d2_sfa : forall g pos ly2 S2 W2 mem2 md2 k, AJ g pos ly2 S2 W2 mem2 md2 k -> frame_addr ly2 4 pos = SFa g pos.
Proof.
intros g pos ly2 S2 W2 mem2 md2 k HJ. destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & HF & _).
unfold SFa, frame_addr. rewrite HF. reflexivity.
Qed.

(* The bcmp call: the interceptor's contract in the journal form (YCbq aj_bcmp_at), on two equal ranges. *)
Lemma d2_bcmp_gen : forall g pos mf ly2 S2 W2 mem2 k (regsT : bvmap 5 word) memT mdT x y n raw,
AJ g pos ly2 S2 W2 memT mdT k ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
d2_keep W2 mem2 memT mf ->
spZ regsT = mf -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n ->
d2_opnd W2 mem2 x n -> d2_opnd W2 mem2 y n ->
(forall j, 0 <= j < n -> aview SEGS (w_H W2) mem2 (x + j) = aview SEGS (w_H W2) mem2 (y + j)) ->
SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
c3 = mkCfg (mkst regs3 raw mem3 (seg_rom SEGS)) md3 /\
AJ g pos ly2 S2 W2 mem3 md3 k /\ aregs_preserved regsT regs3 /\ getr regs3 10 = w64 0 /\
d2_keep W2 mem2 mem3 mf /\ d2_keep W2 memT mem3 mf /\
(forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem3 a)).
Proof.
intros g pos mf ly2 S2 W2 mem2 k regsT memT mdT x y n raw HJ Hmf Hm32 HK Hsp Hgp Htp Hra Hraw H10 H11 H12 Ox Oy Heq.
destruct (d2_geom g pos mf ly2 S2 W2 memT mdT k HJ Hmf) as (Hce & H47 & H16 & HST).
pose proof (opnd_keep W2 mem2 memT mf x n HK Hce Ox) as (X0 & X1 & X2 & X3 & X4 & X5 & X6).
pose proof (opnd_keep W2 mem2 memT mf y n HK Hce Oy) as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ho16 : (mf - e_sp0 g) mod 16 = 0).
{ pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
symmetry. apply (Z.mod_unique _ 16 (2 * (mf / 32) - e_sp0 g / 16) 0); lia. }
assert (Sx : src_ok SEGS W2 regsT memT x n).
{ intros a Ha. split; [exact (X3 a Ha)|]. rewrite Hsp. unfold ESTACK in *. lia. }
assert (Sy : src_ok SEGS W2 regsT memT y n).
{ intros a Ha. split; [exact (Y3 a Ha)|]. rewrite Hsp. unfold ESTACK in *. lia. }
assert (Bx : forall a, x <= a < x + n -> ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g)))
by (intros a Ha; unfold ESTACK in *; lia).
assert (By : forall a, y <= a < y + n -> ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g)))
by (intros a Ha; unfold ESTACK in *; lia).
eapply SRr_mono.
{ exact (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP W2 regsT memT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
(e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 mdT k x y n (mf - e_sp0 g) raw
HJ H10 H11 H12 X2 X0 ltac:(lia) Y0 ltac:(lia) ltac:(rewrite Hsp; lia) Ho16 ltac:(lia) ltac:(unfold ESTACK in *; lia)
Hgp Htp Hra Hraw Sx Sy Bx By X4 Y4 X5 X6 Y5 Y6). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP & Hv & Hcmp & Hfr & Hpres).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP|].
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros j Hj. rewrite (HK (x + j)) by (unfold ESTACK in *; lia). rewrite (HK (y + j)) by (unfold ESTACK in *; lia).
exact (Heq j Hj). }
split; [rewrite Hv; exact Hv0|].
assert (K3 : d2_keep W2 memT mem3 mf).
{ intros a Ha Hw. apply Hfr; [exact Ha|]. replace (e_sp0 g + (mf - e_sp0 g)) with mf by lia. exact Hw. }
split; [exact (keep_trans _ _ _ _ _ HK K3)|]. split; [exact K3 | exact Hpres].
Qed.

(* The bcmp operands in the side-stack frame: a range inside one frame variable whose shadow cells are set. *)
Lemma opnd_frame : forall g pos ly2 S2 W2 mem2 md2 k V bs off n,
AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] ->
bytes_at8 W2 mem2 (SFa g pos + V) bs -> sh_blk W2 mem2 (SFa g pos + V) (Z.of_nat (length bs)) ->
0 <= V -> V + Z.of_nat (length bs) <= 1024 -> V <= off -> off + n <= V + Z.of_nat (length bs) -> 0 <= n < 2 ^ 32 ->
d2_opnd W2 mem2 (SFa g pos + off) n.
Proof.
intros g pos ly2 S2 W2 mem2 md2 k V bs off n HJ Hfr Hb Hs HV0 HVl Ho Hon Hn.
pose proof HJ as (HAR & _). assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hf0 & Hfc & Happ).
rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 k HJ) in Hf0, Hfc, Happ.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite FB in Hfc, Happ.
split; [lia|]. split; [lia|]. split; [exact Hn|].
split.
{ intros a Ha. replace a with (SFa g pos + V + Z.of_nat (Z.to_nat (a - (SFa g pos + V)))) by lia.
rewrite (bytes_aview W2 mem2 _ bs _ Hb) by lia. discriminate. }
split; [apply (amem_range_sub_app (SFa g pos) 1024); [exact Happ | lia | lia | lia | lia]|].
split; [apply (block_shadow_range _ SHADOW_OFF (SFa g pos + V) (Z.of_nat (length bs))); [exact Hs | lia | lia]|].
intros Hn0. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos); [exact HAR | exact Hin | | | exact Hn0];
rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 k HJ); rewrite ?FB; lia.
Qed.
(* The payload copy as a bcmp operand: a prefix of a live heap block. *)
Lemma opnd_heap : forall ly2 S2 W2 mem2 md2 p kk bs n,
AR SEGS B ly2 S2 W2 mem2 md2 -> In (p, kk) (ablocks B ly2 S2) -> bytes_at8 W2 mem2 p bs -> Z.of_nat (length bs) = kk ->
0 <= n <= kk -> n < 2 ^ 32 -> d2_opnd W2 mem2 p n.
Proof.
intros ly2 S2 W2 mem2 md2 p kk bs n HAR Hin Hb Hl Hn Hn32.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p kk HAR Hin) as (H16 & H4096 & Hce & Happ & _ & _ & Hmax).
destruct (req_size_pos0 kk ltac:(lia)) as [Rq0 Rq1].
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (bytes_aview W2 mem2 _ bs _ Hb) by lia. discriminate. }
split; [apply (amem_range_sub_app p (req_size kk)); [exact Happ | lia | lia | lia | lia]|].
split; [apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 p kk); [exact HAR | exact Hin | lia | lia]|].
intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 p kk); [exact HAR | exact Hin | lia | lia | exact Hn0].
Qed.
Lemma hblocks_in : forall g ly2 S2 p kk, hblocks B g ly2 S2 [(p, kk)] -> In (p, kk) (ablocks B ly2 S2).
Proof.
intros g ly2 S2 p kk [Hp _]. apply (Permutation_in _ (Permutation_sym Hp)). left. reflexivity.
Qed.

(* ---- the entry: the symbolic state at 0x80d04 from the boundary's facts --------------------------------- *)
Definition d2_extra (sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3 : Z) : list word :=
[Z_to_bv 64 SB_D2; Z_to_bv 64 sf; Z_to_bv 64 pl; Z_to_bv 64 f20; Z_to_bv 64 f22; Z_to_bv 64 f24; Z_to_bv 64 f26;
 Z_to_bv 64 f36; Z_to_bv 64 cur; Z_to_bv 64 ii; Z_to_bv 64 b0; Z_to_bv 64 b1; Z_to_bv 64 b2; Z_to_bv 64 b3].
Lemma d2_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem mf sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3 k hf ad,
getr regs 9 = w64 mf -> 2 ^ 46 <= mf <= 2 ^ 47 -> mf mod 32 = 0 ->
4096 <= sf -> sf mod 64 = 0 -> sf + 1024 <= alloc_ceiling -> alloc_ceiling <= mf ->
4096 <= pl <= 140737479966720 -> pl mod 16 = 0 ->
0 <= f20 < 256 -> 0 <= f22 < 65536 -> 0 <= f24 < 65536 -> 0 <= f26 < 65536 -> 0 <= f36 < 256 ->
0 <= cur < 2 ^ 64 -> 0 <= ii < 2 ^ 64 ->
0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
getr regs 22 = w64 k -> 0 <= k <= 255 -> getr regs 25 = w64 hf -> 0 <= hf <= 255 ->
getr regs 27 = w64 ad -> 0 <= ad <= 65535 ->
val_mem SEGS (rd W mem) (mf + 40) 8 (sf + 192) -> val_mem SEGS (rd W mem) (mf + 72) 8 (sf + 288) ->
val_mem SEGS (rd W mem) (mf + 88) 8 (sf + 32) -> val_mem SEGS (rd W mem) (mf + 96) 8 (sf + 140) ->
val_mem SEGS (rd W mem) (mf + 104) 8 (sf + 115) -> val_mem SEGS (rd W mem) (mf + 120) 8 (sf + 380) ->
val_mem SEGS (rd W mem) (mf + 128) 8 (sf + 355) -> val_mem SEGS (rd W mem) (mf + 136) 8 cur ->
val_mem SEGS (rd W mem) (mf + 152) 8 pl -> val_mem SEGS (rd W mem) (mf + 160) 8 ii ->
val_mem SEGS (rd W mem) (mf + 168) 8 (sf + 112) -> val_mem SEGS (rd W mem) (mf + 176) 8 SB_D2 ->
val_mem SEGS (rd W mem) (mf + 184) 8 (sf + 352) ->
val_mem SEGS (rd W mem) (sf + 132) 1 f20 -> val_mem SEGS (rd W mem) (sf + 134) 2 f22 ->
val_mem SEGS (rd W mem) (sf + 136) 2 f24 -> val_mem SEGS (rd W mem) (sf + 138) 2 f26 ->
val_mem SEGS (rd W mem) (sf + 148) 1 f36 ->
val_mem SEGS (rd W mem) (sf + 372) 1 f20 -> val_mem SEGS (rd W mem) (sf + 374) 2 f22 ->
val_mem SEGS (rd W mem) (sf + 376) 2 f24 -> val_mem SEGS (rd W mem) (sf + 378) 2 f26 ->
val_mem SEGS (rd W mem) (sf + 388) 1 f36 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (d2_extra sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3))) ss_D2
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_D2)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3 k hf ad
H9 Hmf Hm32 Hsf0 Hsf64 Hsfc Hce Hpl Hpl16 R20 R22 R24 R26 R36 Rcur Rii Rb0 Rb1 Rb2 Rb3 H22 Hk H25 Hhf H27 Had
M40 M72 M88 M96 M104 M120 M128 M136 M152 M160 M168 M176 M184 A20 A22 A24 A26 A36 I20 I22 I24 I26 I36.
pose proof asan_consts as (C1 & _).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (d2_extra sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (d2_extra sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (d2_extra sf pl f20 f22 f24 f26 f36 cur ii b0 b1 b2 b3) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = getr regs r)
by (intros r; rewrite EL by (pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr; unfold A_TEXT; lia);
apply ew_Ereg_reg).
assert (E9 : ew E 9 = w64 mf) by (exact (eq_trans (ER (9%bv)) H9)).
assert (E22 : ew E 22 = w64 k) by (exact (eq_trans (ER (22%bv)) H22)).
assert (E25 : ew E 25 = w64 hf) by (exact (eq_trans (ER (25%bv)) H25)).
assert (E27 : ew E 27 = w64 ad) by (exact (eq_trans (ER (27%bv)) H27)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_D2) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 sf) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 pl) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 f20) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 f22) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 f24) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 f26) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = Z_to_bv 64 f36) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E 40 = Z_to_bv 64 cur) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 ii) by exact (EX 9%nat ltac:(lia)).
assert (E42 : ew E 42 = Z_to_bv 64 b0) by exact (EX 10%nat ltac:(lia)).
assert (E43 : ew E 43 = Z_to_bv 64 b1) by exact (EX 11%nat ltac:(lia)).
assert (E44 : ew E 44 = Z_to_bv 64 b2) by exact (EX 12%nat ltac:(lia)).
assert (E45 : ew E 45 = Z_to_bv 64 b3) by exact (EX 13%nat ltac:(lia)).
assert (U : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v)
by (intros n v Hn Hv; rewrite Hn; apply unsigned_lit_small; exact Hv).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
by (intros n v Hn Hv; cbn [base_val]; apply U; assumption).
assert (SV : forall n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c))
by (intros n v c Hn Hv; cbn [sv_denot]; rewrite (U n v Hn Hv); reflexivity).
unfold ss_D2, AF_D2. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold regions_D2, mf_region_D2, sf_region_D2, c8.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite (VB 9%nat mf E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val SEGS E _ mf 40 8 (SOff 33 192) (sf + 192)); [apply SV; [exact E33 | lia] | zside | zside | exact M40].
* apply (chunk_ok_val SEGS E _ mf 72 8 (SOff 33 288) (sf + 288)); [apply SV; [exact E33 | lia] | zside | zside | exact M72].
* apply (chunk_ok_val SEGS E _ mf 88 8 (SOff 33 32) (sf + 32)); [apply SV; [exact E33 | lia] | zside | zside | exact M88].
* apply (chunk_ok_val SEGS E _ mf 96 8 (SOff 33 140) (sf + 140)); [apply SV; [exact E33 | lia] | zside | zside | exact M96].
* apply (chunk_ok_val SEGS E _ mf 104 8 (SOff 33 115) (sf + 115)); [apply SV; [exact E33 | lia] | zside | zside | exact M104].
* apply (chunk_ok_val SEGS E _ mf 120 8 (SOff 33 380) (sf + 380)); [apply SV; [exact E33 | lia] | zside | zside | exact M120].
* apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 33 355) (sf + 355)); [apply SV; [exact E33 | lia] | zside | zside | exact M128].
* apply (chunk_ok_val SEGS E _ mf 136 8 (SOff 40 0) cur); [rewrite (SV 40%nat cur 0 E40 Rcur), Z.add_0_r; reflexivity | zside | zside | exact M136].
* apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 34 0) pl); [rewrite (SV 34%nat pl 0 E34 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact M152].
* apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 41 0) ii); [rewrite (SV 41%nat ii 0 E41 Rii), Z.add_0_r; reflexivity | zside | zside | exact M160].
* apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 33 112) (sf + 112)); [apply SV; [exact E33 | lia] | zside | zside | exact M168].
* apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) SB_D2); [rewrite (SV 32%nat SB_D2 0 E32 ltac:(unfold SB_D2; lia)), Z.add_0_r; reflexivity | unfold SB_D2; zside | zside | exact M176].
* apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 352) (sf + 352)); [apply SV; [exact E33 | lia] | zside | zside | exact M184].
+ rewrite (VB 33%nat sf E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val SEGS E _ sf 132 1 (SOff 35 0) f20); [rewrite (SV 35%nat f20 0 E35 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact A20].
* apply (chunk_ok_val SEGS E _ sf 134 2 (SOff 36 0) f22); [rewrite (SV 36%nat f22 0 E36 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact A22].
* apply (chunk_ok_val SEGS E _ sf 136 2 (SOff 37 0) f24); [rewrite (SV 37%nat f24 0 E37 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact A24].
* apply (chunk_ok_val SEGS E _ sf 138 2 (SOff 38 0) f26); [rewrite (SV 38%nat f26 0 E38 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact A26].
* apply (chunk_ok_val SEGS E _ sf 148 1 (SOff 39 0) f36); [rewrite (SV 39%nat f36 0 E39 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact A36].
* apply (chunk_ok_val SEGS E _ sf 372 1 (SOff 35 0) f20); [rewrite (SV 35%nat f20 0 E35 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact I20].
* apply (chunk_ok_val SEGS E _ sf 374 2 (SOff 36 0) f22); [rewrite (SV 36%nat f22 0 E36 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact I22].
* apply (chunk_ok_val SEGS E _ sf 376 2 (SOff 37 0) f24); [rewrite (SV 37%nat f24 0 E37 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact I24].
* apply (chunk_ok_val SEGS E _ sf 378 2 (SOff 38 0) f26); [rewrite (SV 38%nat f26 0 E38 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact I26].
* apply (chunk_ok_val SEGS E _ sf 388 1 (SOff 39 0) f36); [rewrite (SV 39%nat f36 0 E39 ltac:(lia)), Z.add_0_r; reflexivity | zside | zside | exact I36].
- apply pairwise_disjoint_of_extents. unfold regions_D2, mf_region_D2, sf_region_D2, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 9%nat mf E9) by lia. rewrite (VB 33%nat sf E33) by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. split; [split; [lia | exact I] | split; exact I].
- unfold facts_ok, facts_D2. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [| split; [exact I | exact I]]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite (U 9%nat mf E9) by lia. rewrite (U 32%nat SB_D2 E32) by (unfold SB_D2; lia).
rewrite (U 33%nat sf E33) by lia. rewrite (U 34%nat pl E34) by lia.
rewrite (U 35%nat f20 E35) by lia. rewrite (U 36%nat f22 E36) by lia. rewrite (U 37%nat f24 E37) by lia.
rewrite (U 38%nat f26 E38) by lia. rewrite (U 39%nat f36 E39) by lia.
rewrite (U 42%nat b0 E42) by lia. rewrite (U 43%nat b1 E43) by lia. rewrite (U 44%nat b2 E44) by lia.
rewrite (U 45%nat b3 E45) by lia. rewrite (U 22%nat k E22) by lia. rewrite (U 25%nat hf E25) by lia.
rewrite (U 27%nat ad E27) by lia.
change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SB_D2. repeat (split; [lia|]). lia.
Qed.

(* ---- the frame's bytes as the engine's chunks ------------------------------------------------------------ *)
Lemma bytes_vm1 : forall (W : world SEGS) m a bs j, bytes_at8 W m a bs -> (j < length bs)%nat ->
val_mem SEGS (rd W m) (a + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof.
intros W m a bs j Hb Hj. unfold bytes_at8 in Hb.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
destruct (Hb j Hj') as [Hv _].
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) in Hv by exact Hj'. rewrite map_nth in Hv. exact Hv.
Qed.
Lemma bytes_vm2 : forall (W : world SEGS) m a bs j, bytes_at8 W m a bs -> (S j < length bs)%nat ->
val_mem SEGS (rd W m) (a + Z.of_nat j) 2
(RcIdentModel.bz (RcIdentModel.nthb bs j) + 256 * RcIdentModel.bz (RcIdentModel.nthb bs (S j))).
Proof.
intros W m a bs j Hb Hj.
pose proof (bytes_vm1 W m a bs j Hb ltac:(lia)) as H0. pose proof (bytes_vm1 W m a bs (S j) Hb Hj) as H1.
pose proof (SlotModel.bz_range (RcIdentModel.nthb bs j)) as R0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb bs (S j))) as R1.
set (b0 := RcIdentModel.bz (RcIdentModel.nthb bs j)) in *. set (b1 := RcIdentModel.bz (RcIdentModel.nthb bs (S j))) in *.
intros kk Hkk. destruct kk as [|[|kk]]; [| | lia].
- rewrite (H0 0%nat ltac:(lia)). do 2 f_equal. unfold YO0f.le_byte. rewrite !Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536. lia.
- replace (a + Z.of_nat j + Z.of_nat 1) with (a + Z.of_nat (S j) + Z.of_nat 0) by lia.
rewrite (H1 0%nat ltac:(lia)). do 2 f_equal. unfold YO0f.le_byte.
rewrite Z.shiftr_0_r, (Z.shiftr_div_pow2 _ (8 * Z.of_nat 1)) by lia.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536. lia.
Qed.
Lemma bytes_vmA1 : forall (W : world SEGS) m a bs j x, bytes_at8 W m a bs -> (j < length bs)%nat ->
x = a + Z.of_nat j -> val_mem SEGS (rd W m) x 1 (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof. intros W m a bs j x Hb Hj ->. apply bytes_vm1; assumption. Qed.
Lemma bytes_vmA2 : forall (W : world SEGS) m a bs j x, bytes_at8 W m a bs -> (S j < length bs)%nat ->
x = a + Z.of_nat j -> val_mem SEGS (rd W m) x 2
(RcIdentModel.bz (RcIdentModel.nthb bs j) + 256 * RcIdentModel.bz (RcIdentModel.nthb bs (S j))).
Proof. intros W m a bs j x Hb Hj ->. apply bytes_vm2; assumption. Qed.
Lemma vm_val : forall m a n v w, v = w -> val_mem SEGS m a n v -> val_mem SEGS m a n w.
Proof. intros m a n v w -> H. exact H. Qed.
Lemma vm_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H kk Hk. rewrite (H kk Hk). unfold YO0f.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---- the boundary facts of the start, kept to an exit ---------------------------------------------------- *)
Ltac kvm HK :=
lazymatch goal with |- val_mem _ (mrestrict _ ?m1) ?a ?n ?v =>
eapply (keep_vm _ _ m1 _ a n v HK); [lia | first [left; split; lia | right; split; lia] | assumption] end.
Lemma d2_hw_keep : forall g pos j W2 mem2 mem3 mf, d2_keep W2 mem2 mem3 mf -> alloc_ceiling + 2 * ESTACK <= mf ->
0 <= mf <= 2 ^ 47 -> 4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
hw_at g pos j W2 mem2 -> hw_at g pos j W2 mem3.
Proof.
intros g pos j W2 mem2 mem3 mf HK Hce H47 Hsf0 Hsfc HW. pose proof asan_consts as (C1 & _).
unfold hw_at in *. destruct HW as (H1 & H2 & H3 & H4). unfold V_hw, N_hw in *. split; [kvm HK|]. split.
- eapply (keep_bytes W2 mem2 mem3 mf _ _ HK); [lia | lia | | exact H2].
pose proof (D2M.hwb_len (e_pl g) j) as L. unfold m_hwb. unfold ESTACK in *; lia.
- split; [apply (keep_zero W2 mem2 mem3 mf _ _ HK Hce); [lia | lia | lia | exact H3]|].
apply (keep_blk W2 mem2 mem3 mf _ _ HK Hce); [lia | lia | lia | exact H4].
Qed.
(* ecommon and P_body at an exit of the segment: the segment writes no byte outside the bcmp window, keeps the
   registers both name, and the journal gives the fds and files. *)
Lemma d2_exit_common : forall g pos mf i pl ly2 S2 W2 regs2 mem2 md2 k regs3 mem3 md3,
frames S2 = [(4, pos)] ->
ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf ly2 S2 W2 regs2 mem2 md2 ->
P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 ->
AJ g pos ly2 S2 W2 mem3 md3 k -> d2_keep W2 mem2 mem3 mf ->
getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 19 = getr regs2 19 ->
getr regs3 22 = getr regs2 22 ->
ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf ly2 S2 W2 regs3 mem3 md3 /\
P_body B g pos mf i pl ly2 S2 W2 regs3 mem3.
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 k regs3 mem3 md3 Hfr HEC HP HJ3 HK R2 R9 R8 R3 R4 R19 R22.
pose proof asan_consts as (C1 & _). assert (HES : ESTACK = 4096) by reflexivity.
destruct HEC as (E2 & E9 & E8 & Hmf & Hm32 & E3 & E4 & E19 & M80 & M192 & M176 & MRA & MS0 & MS24 & MS32 & MS40 &
MS48 & MS56 & MS64 & MS72 & MS80 & MS88 & MS96 & MS104 & Mfp & Mflag & Hpre & Hfds & Hfs & Hinp).
destruct (d2_geom g pos mf ly2 S2 W2 mem3 md3 k HJ3 Hmf) as (Hce & H47 & H16 & HST).
pose proof HJ3 as (HAR & _). assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem3 md3 4 pos HAR Hin) as (Hf0 & Hfc & _).
rewrite (d2_sfa g pos ly2 S2 W2 mem3 md3 k HJ3) in Hf0, Hfc.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite FB in Hfc.
destruct HP as (Hi & Hhb & Hpl & Hid & M112 & Hfix & Hmid & Hmag & M136 & M144 & M152 & M160 & E22 & Hcur).
pose proof (hblocks_in g ly2 S2 pl _ Hhb) as Hplin.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 pl _ HAR Hplin) as (_ & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
destruct (req_size_pos0 (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Rq].
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lpl.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Ifds Ifs].
pose proof Hpre as (_ & _ & _ & _ & Hpn & Hlen & _).
unfold mf_fixed, mf_id, mf_again, id_at in *.
destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
destruct Hid as (Ib & Iz & Is).
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid. unfold RcIdentModel.ID_SIZE in Lid.
split.
- unfold ecommon. rewrite R2, R9, R8, R3, R4, R19.
do 8 (split; [assumption|]).
do 18 (split; [kvm HK|]).
split; [exact Hpre|].
split; [intros fd; rewrite Ifds; reflexivity|].
split; [exact Ifs|].
destruct Hpn as [[Hn0 _] | [Hn0 Hpin]].
+ unfold bytes_at8, garr8. intros j Hj. rewrite length_map in Hj. lia.
+ assert (Hpin2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hhb as [Hpm _]. apply (Permutation_in _ (Permutation_sym Hpm)). right. exact Hpin. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 _ _ HAR Hpin2) as (_ & Hq4096 & Hqce & _ & _ & _ & _).
destruct (req_size_pos0 (e_n g) ltac:(lia)) as [_ Rq2].
eapply (keep_bytes W2 mem2 mem3 mf _ _ HK); [lia | lia | lia | exact Hinp].
- unfold P_body, mf_fixed, mf_id, mf_again, id_at. rewrite R22.
split; [exact Hi|]. split; [exact Hhb|].
split; [eapply (keep_bytes W2 mem2 mem3 mf _ _ HK); [lia | lia | lia | exact Hpl]|].
unfold V_id, N_id, m_id in *.
split; [split; [eapply (keep_bytes W2 mem2 mem3 mf _ _ HK); [lia | lia | lia | exact Ib]|]|].
{ split; [apply (keep_zero W2 mem2 mem3 mf _ _ HK); [lia | lia | lia | lia | exact Iz]|].
apply (keep_blk W2 mem2 mem3 mf _ _ HK); [lia | lia | lia | lia | exact Is]. }
split; [kvm HK|].
split; [do 8 (split; [kvm HK|]); kvm HK|].
do 6 (split; [kvm HK|]).
split; [exact E22 | exact Hcur].
Qed.
Lemma opnd_frame38 : forall g pos ly2 S2 W2 mem2 md2 k V bs off n,
AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] ->
bytes_at8 W2 mem2 (SFa g pos + V) bs -> length bs = 38%nat -> sh_blk W2 mem2 (SFa g pos + V) 38 ->
0 <= V -> V + 38 <= 1024 -> V <= off -> off + n <= V + 38 -> 0 <= n < 2 ^ 32 ->
d2_opnd W2 mem2 (SFa g pos + off) n.
Proof.
intros g pos ly2 S2 W2 mem2 md2 k V bs off n HJ Hfr Hb Hl Hs H1 H2 H3 H4 H5.
apply (opnd_frame g pos ly2 S2 W2 mem2 md2 k V bs off n HJ Hfr Hb); rewrite ?Hl; [exact Hs | lia | lia | lia | lia | lia].
Qed.
Lemma eq_bytes : forall (W : world SEGS) m a1 a2 bs1 bs2 (o1 o2 n : nat) x y,
bytes_at8 W m a1 bs1 -> bytes_at8 W m a2 bs2 ->
(o1 + n <= length bs1)%nat -> (o2 + n <= length bs2)%nat ->
(forall j, (j < n)%nat -> RcIdentModel.nthb bs1 (o1 + j) = RcIdentModel.nthb bs2 (o2 + j)) ->
x = a1 + Z.of_nat o1 -> y = a2 + Z.of_nat o2 ->
forall j, 0 <= j < Z.of_nat n -> aview SEGS (w_H W) m (x + j) = aview SEGS (w_H W) m (y + j).
Proof.
intros W m a1 a2 bs1 bs2 o1 o2 n x y Hb1 Hb2 L1 L2 Heq Hx Hy j Hj. subst x y.
replace (a1 + Z.of_nat o1 + j) with (a1 + Z.of_nat (o1 + Z.to_nat j)) by lia.
replace (a2 + Z.of_nat o2 + j) with (a2 + Z.of_nat (o2 + Z.to_nat j)) by lia.
rewrite (bytes_aview W m a1 bs1 _ Hb1) by lia. rewrite (bytes_aview W m a2 bs2 _ Hb2) by lia.
rewrite (Heq (Z.to_nat j)) by lia. reflexivity.
Qed.

(* ---- the payload copy in the symbolic state: its first n bytes as atoms 42.., and its shadow --------------- *)
Definition plr_D2 (n : nat) : YP09.region :=
YP09.mkRegion (Some 34%nat) 0 (Z.of_nat n) 0 0
(map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (42 + j) 0))) (seq 0 n)).
Lemma d2_add_pl : forall E ss ms (W : world SEGS) mem pl bs (n : nat) sf mf,
st_ok_pi SEGS VAL E ss ms -> ms_mem ms = mrestrict (w_H W) mem -> ss_mem ss = regions_D2 ->
bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 33) = sf -> bv_unsigned (ew E 34) = pl ->
(forall j, (j < n)%nat -> ew E (42 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb bs j))) ->
bytes_at8 W mem pl bs -> (n <= length bs)%nat -> (n <= 4)%nat -> 0 <= pl -> pl + 4 <= 2 ^ 64 ->
(pl + Z.of_nat n <= mf + 40 \/ mf + 192 <= pl) -> (pl + Z.of_nat n <= sf + 112 \/ sf + 390 <= pl) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (plr_D2 n :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms W mem pl bs n sf mf HS Hm Hss H9 H33 H34 HA Hb Hl Hn4 Hp0 Hp1 Dmf Dsf.
apply st_ok_pi_add_region; [exact HS | | | ].
- destruct n as [|[|[|[|[|n]]]]]; try lia; vm_compute; reflexivity.
- unfold region_ok, plr_D2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
apply (chunk_ok_val SEGS E _ pl (Z.of_nat j) 1 (SOff (42 + j) 0) (RcIdentModel.bz (RcIdentModel.nthb bs j))).
+ cbn [sv_denot]. rewrite (HA j ltac:(lia)), unsigned_lit_small by (pose proof (SlotModel.bz_range (RcIdentModel.nthb bs j)); lia).
rewrite Z.add_0_r. reflexivity.
+ pose proof (SlotModel.bz_range (RcIdentModel.nthb bs j)). cbn. lia.
+ cbn. lia.
+ rewrite Hm. exact (bytes_vmA1 W mem pl bs j (pl + Z.of_nat j) Hb ltac:(lia) eq_refl).
- rewrite Hss. unfold regions_D2, plr_D2, mf_region_D2, sf_region_D2. cbn [all_disjoint].
unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite H34, H9, H33.
split; [lia | split; [lia | exact I]].
Qed.
(* The payload copy's byte 1 as the literal 0 (an ignored model-name record of two bytes or more). *)
Lemma d2_add_pl2z : forall E ss ms (W : world SEGS) mem pl bs sf mf,
st_ok_pi SEGS VAL E ss ms -> ms_mem ms = mrestrict (w_H W) mem -> ss_mem ss = regions_D2 ->
bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 33) = sf -> bv_unsigned (ew E 34) = pl ->
bytes_at8 W mem pl bs -> (2 <= length bs)%nat -> RcIdentModel.bz (RcIdentModel.nthb bs 1) = 0 ->
0 <= pl -> pl + 4 <= 2 ^ 64 ->
(pl + 2 <= mf + 40 \/ mf + 192 <= pl) -> (pl + 2 <= sf + 112 \/ sf + 390 <= pl) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (plr2_D2 :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms W mem pl bs sf mf HS Hm Hss H9 H33 H34 Hb Hl H1 Hp0 Hp1 Dmf Dsf.
apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | | ].
- unfold region_ok, plr2_D2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ pl 1 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
rewrite Hm. pose proof (bytes_vmA1 W mem pl bs 1 (pl + 1) Hb ltac:(lia) eq_refl) as Hv. rewrite H1 in Hv. exact Hv.
- rewrite Hss. unfold regions_D2, plr2_D2, mf_region_D2, sf_region_D2. cbn [all_disjoint].
unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite H34, H9, H33.
split; [lia | split; [lia | exact I]].
Qed.
Lemma d2_sh_pl : forall E ly2 S2 (W : world SEGS) mem md pl kk n,
AR SEGS B ly2 S2 W mem md -> In (pl, kk) (ablocks B ly2 S2) ->
bv_unsigned (ew E 32) = SB_D2 -> bv_unsigned (ew E 34) = pl -> 0 <= n <= req_size kk ->
sh_ok SEGS Bx_D2 [mkSHE 34 0 n] E (mrestrict (w_H W) mem).
Proof.
intros E ly2 S2 W mem md pl kk n HAR Hin H32 H34 Hn. apply Forall_cons; [|apply Forall_nil].
eapply (shent_ok_of_block SEGS B LAWS ly2 S2 W mem md E Bx_D2 34 pl kk 0 n HAR Hin); [| |lia|lia].
- unfold Bx_D2. rewrite U_SOff, Z.add_0_r, H32, zcanon_id by (unfold SB_D2, M64; lia). reflexivity.
- rewrite U_SOff, Z.add_0_r, H34. apply zcanon_id.
pose proof (bv_unsigned_in_range 64 (ew E 34)) as Hr. change (bv_modulus 64) with M64 in Hr. rewrite H34 in Hr. lia.
Qed.
Lemma afact_val : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi He Hv Hl. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite He, unsigned_lit_small by exact Hv.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma w64_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_mod. cbv. discriminate. Qed.
(* The shadow address the version case computes at 0x80f18..0x80f1c, for the payload's byte 2. *)
Lemma d2_x11 : forall E pl, bv_unsigned (ew E 34) = pl -> bv_unsigned (ew E 32) = SB_D2 -> 0 <= pl -> pl + 2 < 2 ^ 64 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew E 34) + 2)) (Z_to_bv 64 3)) (ew E 32) =
w64 (shadow_addr (pl + 2)).
Proof.
intros E pl H34 H32 Hp0 Hp1.
set (v := SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 2) (SLit 3)) (SOff 32 0)).
assert (HX : sv_denot E v = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew E 34) + 2)) (Z_to_bv 64 3)) (ew E 32)).
{ subst v. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite <- HX. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E v)).
pose proof (match_x_core_denot Bx_D2 E v (SOff 34 2) eq_refl) as HM. unfold U in HM. rewrite HM.
unfold cell_x, Bx_D2. rewrite !U_SOff, Z.add_0_r, H32, H34, !zcanon_id by (unfold SB_D2, M64; lia).
unfold w64, shadow_addr. reflexivity.
Qed.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation Q_D2 g pos mf i pl :=
(fun W3 c3 =>
inv_caseV B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W3 c3 \/
inv_caseM B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W3 c3 \/
inv_caseF B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W3 c3 \/
inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W3 c3).

(* After a run with read-only regions: memory is kept, so the start's facts still hold. *)
Ltac d2_after_run :=
lazymatch goal with
| HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HK : d2_keep _ _ ?m1 _ |- _ =>
let K := fresh "KEEP" in
pose proof (keep_frame _ _ rs _ m1 m2 _ ltac:(vm_compute; reflexivity) HFr HK) as K; clear HK; rename K into HK
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A run to the segment's stop: the engine's token run, then the memory kept. *)
Ltac d2_run stop :=
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H _) _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_to_tok RUNTO HS HJ SHOK Bspan_D2 stop;
[ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exfalso; refine (ro_nowr _ _ a _ Ha); vm_compute; reflexivity
| d2_after_run ]
end.
(* Rewrite with every atom equation `ew E n = ...` in the hypothesis H (the environment is opaque). *)
Ltac d2_ews H := repeat match goal with HX : ew _ _ = _ |- _ => progress rewrite HX in H end.
Ltac d2_ewg := repeat match goal with HX : ew _ _ = _ |- _ => progress rewrite HX end.
(* The value of an atom below the havoc bound, from the start's atom equations. *)
Ltac d2_u := cbn [ew extK havoc Nat.ltb Nat.leb Nat.eqb Nat.sub]; rewrite ?ew_havoc_old by (cbv; lia);
d2_ewg; apply unsigned_lit_small; try unfold SB_D2; lia.
(* The payload copy's shadow entry, from the current journal. *)
Ltac d2_shpl :=
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
let HAR := fresh "HAR" in pose proof HJ as (HAR & _);
eapply (d2_sh_pl _ ly S W mem md); [exact HAR | eassumption | d2_u | d2_u | lia] end.
(* A bcmp call: the operands and their equality are the hypotheses OP*/EQ* the setup made. *)
Ltac d2_call WW :=
lazymatch goal with
| HS : st_ok _ ?E1 _ (restrict _ ?ms1), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HK : d2_keep _ _ _ _,
HEI : img_env _ _ ?E1, SH0 : sh_ok _ _ ?SHl _ _ |- _ =>
let A0 := fresh "A0" in let A1 := fresh "A1" in let A2 := fresh "A2" in let R1 := fresh "R1" in
let R2 := fresh "R2" in let R3 := fresh "R3" in let R4 := fresh "R4" in
prreg HS (10%bv : bv 5) A0; prreg HS (11%bv : bv 5) A1; prreg HS (12%bv : bv 5) A2;
prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
d2_ews A0; d2_ews A1; d2_ews R2; d2_ews R3; d2_ews R4;
rewrite ?unsigned_lit_small in A0 by lia; rewrite ?unsigned_lit_small in A1 by lia;
pmkst HS;
eapply SRr_bind;
[ eapply (d2_bcmp_gen _ _ _ _ _ _ _ _ (ms_regs ms1) (ms_mem ms1)); [exact HJ | eassumption | eassumption | exact HK
| unfold spZ; rewrite R2; apply unsigned_lit_small; lia | exact R3 | exact R4 | exact R1
| apply ret_ok_codeptr_v; [lia | reflexivity] | exact A0 | exact A1 | exact A2 | eassumption | eassumption | eassumption]
| let W3 := fresh "W3" in let c3 := fresh "c3" in let regs3 := fresh "regs3" in let mem3 := fresh "mem3" in
let md3 := fresh "md3" in let HJ3 := fresh "HJ3" in let HP3 := fresh "HP3" in let H103 := fresh "H103" in
let K3 := fresh "K3" in let K3' := fresh "K3'" in let Hpres3 := fresh "Hpres3" in let Hpp := fresh "Hpp" in
intros W3 c3 _ Hpp; destruct Hpp as (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H103 & K3 & K3' & Hpres3);
let HS2 := fresh "HS2" in let kk := run_K_hi HS in
let idxs := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (seq 0 (length (ss_mem ss))) end in
jafter_call_keep_hi HS kk regs3 (mrestrict (w_H WW) mem3) HP3 idxs HS2;
lazymatch type of HS2 with ?Qk -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Qk);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [ms_mem restrict];
(eapply region_kept_aview;
[ cbn [ew extK havoc Nat.ltb Nat.leb Nat.eqb Nat.sub]; rewrite ?ew_havoc_old by (cbv; lia);
d2_ewg; apply unsigned_lit_small; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply K3'; unfold ESTACK in *; lia
| exact Hpres3 ])
| specialize (HS2 HQ); clear HQ ] end;
rewrite <- restrict_mkst_fx in HS2;
let HEI2 := fresh "HEI" in
lazymatch type of HS2 with st_ok_pi _ _ ?E2 _ _ =>
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]) end;
let HP := fresh "HP" in
lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?ss0 ?ms0 =>
pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (10%bv : bv 5) 0 HS2 ltac:(cbn [ms_regs restrict mkst]; exact H103) eq_refl) as HP
end;
lazymatch type of HP with st_ok_pi _ _ _ ?ss1 _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HP end;
clear HS HS2 HJ HK A0 A1 A2 R1 R2 R3 R4 HP3 H103 K3' Hpres3;
repeat match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
rename HP into HS, HJ3 into HJ, K3 into HK;
let SHOK := fresh "SHOK" in
lazymatch type of HS with st_ok_pi _ _ ?E2 _ (restrict (w_H _) ?ms2) =>
assert (SHOK : sh_ok SEGS Bx_D2 SHl E2 (mrestrict (w_H WW) (ms_mem ms2))) by first [apply Forall_nil | d2_shpl] end ]
end.
(* Normalise the symbolic state; pin a register to a literal (Heq : getr regs r = w64 z); add a fact on an atom
   (Hv : ew E n = Z_to_bv 64 v; lia proves the range). *)
Ltac d2_norm :=
lazymatch goal with HS : st_ok_pi _ _ _ ?ss1 _ |- _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end.
Ltac d2_pin r z Heq :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
let HP := fresh "HP" in
pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (r : bv 5) z HS ltac:(cbn [ms_regs restrict mkst]; exact Heq) eq_refl) as HP;
clear HS; rename HP into HS end.
Ltac d2_fact n lo hi Hv :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
let HP := fresh "HP" in
pose proof (st_ok_pi_add_fact Ex ss0 ms0 n (mkAF lo hi 0) HS ltac:(eapply afact_val; [exact Hv | lia | lia])) as HP;
clear HS; rename HP into HS end.


(* ---- the four cases of the switch, one theorem each, and seg_D2 ------------------------------------------- *)
(* Case M: the model-name record; the walk stops at 0x81170, where seg_D4 starts. *)
Theorem d2_case_M : forall g pos mf i pl (W2 : world SEGS) c2,
inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W2 c2 ->
SlotModel.rec_r (e_pl g) i = 1 -> SlotModel.rec_addr (e_pl g) i = 0x1000 ->
SRr SEGS W2 c2 (Q_D2 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 HD Hr Ha.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo1 & Hmo2 & HEC & HPB & HW & SBb & SBa &
H21 & Bb & Ba & H27 & H23 & H25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HEC as (E2 & E9 & E8 & Hmf & Hm32 & E3 & E4 & E19 & M80 & M192 & M176 & _).
pose proof HPB as (Hi & Hhb & Hpl & Hid & M112 & Hfix & Hmid & Hmag & M136 & M144 & M152 & M160 & E22 & Hcur).
destruct (d2_geom g pos mf ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ Hmf) as (Hce & H47 & H16 & HST).
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hf0 & Hfc & _).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hal64 & _).
rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ) in Hf0, Hfc, Hal64.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite FB in Hfc.
pose proof (hblocks_in g ly2 S2 pl _ Hhb) as Hplin.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl _ HAR Hplin) as (Hpl16 & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
destruct (req_size_pos0 (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Rq].
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lpl.
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid.
pose proof (SlotModel.rec_id_length (e_pl g) i) as Lid0.
unfold RcIdentModel.ID_SIZE in Lid, Lid0.
unfold mf_fixed, mf_id, mf_again, id_at, m_id in *.
destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
destruct Hid as (Ib & Iz & Is).
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 132) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 148) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 134) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 136) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 138) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A26.
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 372) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 388) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 374) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 376) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 378) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I26.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 28) (SFa g pos + 140) ltac:(unfold V_again; lia) F96) as F96'.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 3) (SFa g pos + 115) ltac:(unfold V_again; lia) F104) as F104'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 28) (SFa g pos + 380) ltac:(unfold V_id; lia) F120) as F120'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 3) (SFa g pos + 355) ltac:(unfold V_id; lia) F128) as F128'.
pose proof (vm_mod64 _ _ _ M136) as M136'.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) as Rhf.
pose proof (proj1 (D2M.addr_range (e_pl g) i)) as Rad.
assert (HS : st_ok_pi SEGS VAL
(Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))))
ss_D2 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + AF_D2)) mem2 (seg_rom SEGS)))).
{ apply (d2_entry W2 regs2 mem2 mf (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _ (SlotModel.rec_k (e_pl g) i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) (SlotModel.rec_addr (e_pl g) i));
first [ assumption
| apply SlotModel.bz_range
| apply Z.mod_pos_bound; lia
| unfold ESTACK in *; lia
| match goal with |- context [RcIdentModel.bz ?b1 + 256 * RcIdentModel.bz ?b2] =>
pose proof (SlotModel.bz_range b1); pose proof (SlotModel.bz_range b2); lia end
| pose proof (SlotModel.nrec_range (e_pl g)); unfold m_nrec, SlotModel.nrecn in Hi; lia
| match goal with |- ?gg => fail 100 "ENTRY premise" gg end ]. }
assert (OP1x : d2_opnd W2 mem2 (SFa g pos + 115) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 115 17 HJ Hfr Ba Lid SBa); lia).
assert (OP1y : d2_opnd W2 mem2 (SFa g pos + 355) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 355 17 HJ Hfr Ib Lid Is); lia).
assert (OP2x : d2_opnd W2 mem2 (SFa g pos + 140) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 140 8 HJ Hfr Ba Lid SBa); lia).
assert (OP2y : d2_opnd W2 mem2 (SFa g pos + 380) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 380 8 HJ Hfr Ib Lid Is); lia).
assert (EQ1 : forall j, 0 <= j < 17 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 115 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 355 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 3 3 17 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
assert (EQ2 : forall j, 0 <= j < 8 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 140 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 380 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 28 28 8 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
remember (Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat ->
ew E n = ew (Ereg regs2 (d2_extra (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (ER2 : ew E 2 = getr regs2 2)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (ER3 : ew E 3 = getr regs2 3)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (ER4 : ew E 4 = getr regs2 4)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (ER8 : ew E 8 = getr regs2 8)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (ER9 : ew E 9 = getr regs2 9)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 9 9%bv eq_refl)).
assert (ER19 : ew E 19 = getr regs2 19)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 19 19%bv eq_refl)).
assert (ER22 : ew E 22 = getr regs2 22)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 22 22%bv eq_refl)).
assert (EE32 : ew E 32 = Z_to_bv 64 SB_D2) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE33 : ew E 33 = Z_to_bv 64 (SFa g pos)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE34 : ew E 34 = Z_to_bv 64 pl) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE35 : ew E 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE2 : ew E 2 = Z_to_bv 64 mf) by (rewrite ER2; exact E2).
assert (EE3 : ew E 3 = w64 (as_gp B)) by (rewrite ER3; exact E3).
assert (EE4 : ew E 4 = w64 (as_tp B)) by (rewrite ER4; exact E4).
assert (EE9 : ew E 9 = Z_to_bv 64 mf) by (rewrite ER9; exact E9).
clear EL HE.
assert (HK : d2_keep W2 mem2 mem2 mf) by apply keep_refl.
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 (BASE + 0x5f8)) with (Z_to_bv 64 (BASE + AF_D2)).
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (23%bv : bv 5) 1 HS ltac:(cbn [ms_regs restrict mkst]; rewrite H23, Hr; reflexivity) eq_refl) as HP;
clear HS; rename HP into HS end.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (27%bv : bv 5) 0x1000 HS ltac:(cbn [ms_regs restrict mkst]; rewrite H27, Ha; reflexivity) eq_refl) as HP;
clear HS; rename HP into HS end.
lazymatch goal with HS : st_ok_pi _ _ _ ?ss1 _ |- _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end.
d2_run AF_D2M. d2_call W2. d2_run AF_D2M. d2_call W2. d2_run AF_D2M.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22; prreg HS (20%bv : bv 5) X20;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22; rewrite EE35 in X20;
pmkst HS;
apply SRr_ret; right; left;
unfold inv_caseM, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [|split; [exact Hr|]; split; [exact Ha|]; exact X20];
destruct (D2M.hw_kept (e_pl g) i ltac:(left; rewrite Ha; discriminate)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
Qed.
(* Case Z: an ignored record. The engine runs the bcmp of before and id (equal: the record changes nothing),
   then the three would-be-accepted checks, and ends at the join 0x813b4. *)
Theorem d2_case_Z : forall g pos mf i pl (W2 : world SEGS) c2,
inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W2 c2 ->
SlotModel.rec_r (e_pl g) i = 0 ->
SRr SEGS W2 c2 (Q_D2 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 HD Hr.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo1 & Hmo2 & HEC & HPB & HW & SBb & SBa &
H21 & Bb & Ba & H27 & H23 & H25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HEC as (E2 & E9 & E8 & Hmf & Hm32 & E3 & E4 & E19 & M80 & M192 & M176 & _).
pose proof HPB as (Hi & Hhb & Hpl & Hid & M112 & Hfix & Hmid & Hmag & M136 & M144 & M152 & M160 & E22 & Hcur).
destruct (d2_geom g pos mf ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ Hmf) as (Hce & H47 & H16 & HST).
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hf0 & Hfc & _).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hal64 & _).
rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ) in Hf0, Hfc, Hal64.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite FB in Hfc.
pose proof (hblocks_in g ly2 S2 pl _ Hhb) as Hplin.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl _ HAR Hplin) as (Hpl16 & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
destruct (req_size_pos0 (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Rq].
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lpl.
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid.
pose proof (SlotModel.rec_id_length (e_pl g) i) as Lid0.
unfold RcIdentModel.ID_SIZE in Lid, Lid0.
unfold mf_fixed, mf_id, mf_again, id_at, m_id in *.
destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
destruct Hid as (Ib & Iz & Is).
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 132) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 148) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 134) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 136) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 138) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A26.
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 372) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 388) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 374) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 376) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 378) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I26.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 28) (SFa g pos + 140) ltac:(unfold V_again; lia) F96) as F96'.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 3) (SFa g pos + 115) ltac:(unfold V_again; lia) F104) as F104'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 28) (SFa g pos + 380) ltac:(unfold V_id; lia) F120) as F120'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 3) (SFa g pos + 355) ltac:(unfold V_id; lia) F128) as F128'.
pose proof (vm_mod64 _ _ _ M136) as M136'.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) as Rhf.
pose proof (proj1 (D2M.addr_range (e_pl g) i)) as Rad.
assert (HS : st_ok_pi SEGS VAL
(Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))))
ss_D2 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + AF_D2)) mem2 (seg_rom SEGS)))).
{ apply (d2_entry W2 regs2 mem2 mf (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _ (SlotModel.rec_k (e_pl g) i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) (SlotModel.rec_addr (e_pl g) i));
first [ assumption
| apply SlotModel.bz_range
| apply Z.mod_pos_bound; lia
| unfold ESTACK in *; lia
| match goal with |- context [RcIdentModel.bz ?b1 + 256 * RcIdentModel.bz ?b2] =>
pose proof (SlotModel.bz_range b1); pose proof (SlotModel.bz_range b2); lia end
| pose proof (SlotModel.nrec_range (e_pl g)); unfold m_nrec, SlotModel.nrecn in Hi; lia
| match goal with |- ?gg => fail 100 "ENTRY premise" gg end ]. }
assert (OP1x : d2_opnd W2 mem2 (SFa g pos + 115) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 115 17 HJ Hfr Ba Lid SBa); lia).
assert (OP1y : d2_opnd W2 mem2 (SFa g pos + 355) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 355 17 HJ Hfr Ib Lid Is); lia).
assert (OP2x : d2_opnd W2 mem2 (SFa g pos + 140) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 140 8 HJ Hfr Ba Lid SBa); lia).
assert (OP2y : d2_opnd W2 mem2 (SFa g pos + 380) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 380 8 HJ Hfr Ib Lid Is); lia).
assert (EQ1 : forall j, 0 <= j < 17 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 115 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 355 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 3 3 17 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
assert (EQ2 : forall j, 0 <= j < 8 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 140 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 380 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 28 28 8 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
remember (Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat ->
ew E n = ew (Ereg regs2 (d2_extra (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (ER2 : ew E 2 = getr regs2 2)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (ER3 : ew E 3 = getr regs2 3)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (ER4 : ew E 4 = getr regs2 4)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (ER8 : ew E 8 = getr regs2 8)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (ER9 : ew E 9 = getr regs2 9)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 9 9%bv eq_refl)).
assert (ER19 : ew E 19 = getr regs2 19)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 19 19%bv eq_refl)).
assert (ER22 : ew E 22 = getr regs2 22)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 22 22%bv eq_refl)).
assert (EE32 : ew E 32 = Z_to_bv 64 SB_D2) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE33 : ew E 33 = Z_to_bv 64 (SFa g pos)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE34 : ew E 34 = Z_to_bv 64 pl) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE35 : ew E 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE2 : ew E 2 = Z_to_bv 64 mf) by (rewrite ER2; exact E2).
assert (EE3 : ew E 3 = w64 (as_gp B)) by (rewrite ER3; exact E3).
assert (EE4 : ew E 4 = w64 (as_tp B)) by (rewrite ER4; exact E4).
assert (EE9 : ew E 9 = Z_to_bv 64 mf) by (rewrite ER9; exact E9).
assert (ER21 : ew E 21 = getr regs2 21)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 21 21%bv eq_refl)).
assert (ER25 : ew E 25 = getr regs2 25)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 25 25%bv eq_refl)).
assert (ER27 : ew E 27 = getr regs2 27)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 27 27%bv eq_refl)).
assert (EE36 : ew E 36 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE37 : ew E 37 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE38 : ew E 38 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE39 : ew E 39 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE40 : ew E 40 = Z_to_bv 64 ((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE41 : ew E 41 = Z_to_bv 64 (Z.of_nat i)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE42 : ew E 42 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE43 : ew E 43 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE44 : ew E 44 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE45 : ew E 45 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear EL HE.
assert (HK : d2_keep W2 mem2 mem2 mf) by apply keep_refl.
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 (BASE + 0x5f8)) with (Z_to_bv 64 (BASE + AF_D2)).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl _ 4 pos HAR Hplin Hin) as Dsep.
unfold zdisjoint in Dsep. cbn [fst snd] in Dsep. rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ), FB in Dsep.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)) as RB0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)) as RB1.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)) as RB2.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)) as RB3.
assert (EV22 : ew E 22 = Z_to_bv 64 (SlotModel.rec_k (e_pl g) i)) by (rewrite ER22; exact E22).
assert (EV27 : ew E 27 = Z_to_bv 64 (SlotModel.rec_addr (e_pl g) i)) by (rewrite ER27; exact H27).
assert (OPZx : d2_opnd W2 mem2 (SFa g pos + 32) 38)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 32 _ 32 38 HJ Hfr Bb Lid0 SBb); lia).
assert (OPZy : d2_opnd W2 mem2 (SFa g pos + 352) 38)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 352 38 HJ Hfr Ib Lid Is); lia).
assert (EQZ : forall j, 0 <= j < 38 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 32 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 352 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 0 0 38 _ _ Bb Ib);
[lia | lia | intros; rewrite (D2M.ignored (e_pl g) i Hr); reflexivity | unfold V_before; lia | unfold V_id; lia | lia]).
assert (P23 : getr regs2 23 = w64 0) by (rewrite H23, Hr; reflexivity).
d2_pin (23%bv : bv 5) 0 P23.
pose proof (proj2 (D2M.addr_range (e_pl g) i)) as Rad2.
destruct (Z.eq_dec (SlotModel.rec_addr (e_pl g) i) 0) as [Ha0|Ha0];
[| destruct (Z.eq_dec (SlotModel.rec_addr (e_pl g) i) 0x600) as [Ha6|Ha6];
   [| destruct (Z.eq_dec (SlotModel.rec_addr (e_pl g) i) 0x1000) as [Ha1|Ha1]]].
- (* address 0: the firmware record ignored *)
assert (P27 : getr regs2 27 = w64 0) by (rewrite H27, Ha0; reflexivity).
d2_pin (27%bv : bv 5) 0 P27.
destruct (Z_lt_le_dec (SlotModel.rec_k (e_pl g) i) 4) as [Hk4|Hk4].
+ (* fewer than four bytes *)
d2_fact 22%nat 0 3 EV22.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
+ (* four bytes or more, not all digits *)
d2_fact 22%nat 4 255 EV22.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
pose proof (d2_add_pl Ex ss0 ms0 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) 4 (SFa g pos) mf HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(rewrite EE9; apply unsigned_lit_small; lia)
ltac:(rewrite EE33; apply unsigned_lit_small; lia) ltac:(rewrite EE34; apply unsigned_lit_small; lia)
ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [exact EE42 | exact EE43 | exact EE44 | exact EE45 | lia]) Hpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(left; unfold ESTACK in *; lia)
ltac:(destruct Dsep; [left | right]; lia)) as HP; clear HS; rename HP into HS end.
clear SHOK.
assert (SHOK : sh_ok SEGS Bx_D2 [mkSHE 34 0 4] E (mrestrict (w_H W2) mem2))
by (eapply d2_sh_pl; [exact HAR | exact Hplin | rewrite EE32; apply unsigned_lit_small; unfold SB_D2; lia
| rewrite EE34; apply unsigned_lit_small; lia | lia]).
pose proof (D2M.fw_ignored (e_pl g) i Hr Ha0 Hk4) as NDG.
destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)) 9) as [D0|D0].
2: { d2_fact 42%nat 10 255 EE42.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
}
d2_fact 42%nat 0 9 EE42.
destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)) 9) as [D1|D1].
2: { d2_fact 43%nat 10 255 EE43.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
}
d2_fact 43%nat 0 9 EE43.
destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)) 9) as [D2|D2].
2: { d2_fact 44%nat 10 255 EE44.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
}
d2_fact 44%nat 0 9 EE44.
destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)) 9) as [D3|D3].
{ exfalso. exact (NDG (conj D0 (conj D1 (conj D2 D3)))). }
d2_fact 45%nat 10 255 EE45.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
- (* address 0x600: the version record ignored, fewer than eight bytes *)
assert (P27 : getr regs2 27 = w64 0x600) by (rewrite H27, Ha6; reflexivity).
d2_pin (27%bv : bv 5) 0x600 P27.
pose proof (D2M.ver_ignored (e_pl g) i Hr Ha6) as Hk8.
d2_fact 22%nat 0 7 EV22.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
- (* address 0x1000: the model-name record ignored *)
assert (P27 : getr regs2 27 = w64 0x1000) by (rewrite H27, Ha1; reflexivity).
d2_pin (27%bv : bv 5) 0x1000 P27.
destruct (Z_lt_le_dec (SlotModel.rec_k (e_pl g) i) 2) as [Hk2|Hk2].
+ d2_fact 22%nat 0 1 EV22.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
+ d2_fact 22%nat 2 255 EV22.
pose proof (D2M.name_ignored (e_pl g) i Hr Ha1 Hk2) as N1.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
pose proof (d2_add_pl2z Ex ss0 ms0 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) (SFa g pos) mf HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(rewrite EE9; apply unsigned_lit_small; lia)
ltac:(rewrite EE33; apply unsigned_lit_small; lia) ltac:(rewrite EE34; apply unsigned_lit_small; lia)
Hpl ltac:(lia) N1 ltac:(lia) ltac:(lia) ltac:(left; unfold ESTACK in *; lia)
ltac:(destruct Dsep; [left | right]; lia)) as HP; clear HS; rename HP into HS end.
clear SHOK.
assert (SHOK : sh_ok SEGS Bx_D2 [mkSHE 34 0 2] E (mrestrict (w_H W2) mem2))
by (eapply d2_sh_pl; [exact HAR | exact Hplin | rewrite EE32; apply unsigned_lit_small; unfold SB_D2; lia
| rewrite EE34; apply unsigned_lit_small; lia | lia]).
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
- (* any other address *)
pose proof (Rad2 Ha0 Ha6 Ha1) as Hhi.
d2_fact 27%nat 49152 65535 EV27.
d2_norm.
d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T. d2_call W2. d2_run AF_D2T.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (25%bv : bv 5) X25; prreg HS (21%bv : bv 5) X21;
rewrite EE40, w64_mod in X26; rewrite EE33, unsigned_lit_small in X24 by lia; rewrite EE34 in X25; rewrite EE41 in X21;
pmkst HS;
apply SRr_ret; right; right; right;
unfold inv_tail, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact X26 | split; [unfold V_before; exact X24 | split; [exact X25 | exact X21]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(right; exact Hr)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
Qed.


(* Case F: the firmware record accepted (four digits): the four digit checks pass, and the walk stops at
   0x81208, where seg_D5 starts. *)
Theorem d2_case_F : forall g pos mf i pl (W2 : world SEGS) c2,
inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W2 c2 ->
SlotModel.rec_r (e_pl g) i = 1 -> SlotModel.rec_addr (e_pl g) i = 0 ->
SRr SEGS W2 c2 (Q_D2 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 HD Hr Ha0.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo1 & Hmo2 & HEC & HPB & HW & SBb & SBa &
H21 & Bb & Ba & H27 & H23 & H25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HEC as (E2 & E9 & E8 & Hmf & Hm32 & E3 & E4 & E19 & M80 & M192 & M176 & _).
pose proof HPB as (Hi & Hhb & Hpl & Hid & M112 & Hfix & Hmid & Hmag & M136 & M144 & M152 & M160 & E22 & Hcur).
destruct (d2_geom g pos mf ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ Hmf) as (Hce & H47 & H16 & HST).
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hf0 & Hfc & _).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hal64 & _).
rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ) in Hf0, Hfc, Hal64.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite FB in Hfc.
pose proof (hblocks_in g ly2 S2 pl _ Hhb) as Hplin.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl _ HAR Hplin) as (Hpl16 & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
destruct (req_size_pos0 (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Rq].
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lpl.
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid.
pose proof (SlotModel.rec_id_length (e_pl g) i) as Lid0.
unfold RcIdentModel.ID_SIZE in Lid, Lid0.
unfold mf_fixed, mf_id, mf_again, id_at, m_id in *.
destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
destruct Hid as (Ib & Iz & Is).
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 132) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 148) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 134) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 136) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 138) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A26.
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 372) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 388) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 374) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 376) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 378) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I26.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 28) (SFa g pos + 140) ltac:(unfold V_again; lia) F96) as F96'.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 3) (SFa g pos + 115) ltac:(unfold V_again; lia) F104) as F104'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 28) (SFa g pos + 380) ltac:(unfold V_id; lia) F120) as F120'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 3) (SFa g pos + 355) ltac:(unfold V_id; lia) F128) as F128'.
pose proof (vm_mod64 _ _ _ M136) as M136'.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) as Rhf.
pose proof (proj1 (D2M.addr_range (e_pl g) i)) as Rad.
assert (HS : st_ok_pi SEGS VAL
(Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))))
ss_D2 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + AF_D2)) mem2 (seg_rom SEGS)))).
{ apply (d2_entry W2 regs2 mem2 mf (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _ (SlotModel.rec_k (e_pl g) i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) (SlotModel.rec_addr (e_pl g) i));
first [ assumption
| apply SlotModel.bz_range
| apply Z.mod_pos_bound; lia
| unfold ESTACK in *; lia
| match goal with |- context [RcIdentModel.bz ?b1 + 256 * RcIdentModel.bz ?b2] =>
pose proof (SlotModel.bz_range b1); pose proof (SlotModel.bz_range b2); lia end
| pose proof (SlotModel.nrec_range (e_pl g)); unfold m_nrec, SlotModel.nrecn in Hi; lia
| match goal with |- ?gg => fail 100 "ENTRY premise" gg end ]. }
assert (OP1x : d2_opnd W2 mem2 (SFa g pos + 115) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 115 17 HJ Hfr Ba Lid SBa); lia).
assert (OP1y : d2_opnd W2 mem2 (SFa g pos + 355) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 355 17 HJ Hfr Ib Lid Is); lia).
assert (OP2x : d2_opnd W2 mem2 (SFa g pos + 140) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 140 8 HJ Hfr Ba Lid SBa); lia).
assert (OP2y : d2_opnd W2 mem2 (SFa g pos + 380) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 380 8 HJ Hfr Ib Lid Is); lia).
assert (EQ1 : forall j, 0 <= j < 17 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 115 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 355 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 3 3 17 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
assert (EQ2 : forall j, 0 <= j < 8 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 140 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 380 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 28 28 8 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
remember (Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat ->
ew E n = ew (Ereg regs2 (d2_extra (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (ER2 : ew E 2 = getr regs2 2)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (ER3 : ew E 3 = getr regs2 3)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (ER4 : ew E 4 = getr regs2 4)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (ER8 : ew E 8 = getr regs2 8)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (ER9 : ew E 9 = getr regs2 9)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 9 9%bv eq_refl)).
assert (ER19 : ew E 19 = getr regs2 19)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 19 19%bv eq_refl)).
assert (ER22 : ew E 22 = getr regs2 22)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 22 22%bv eq_refl)).
assert (EE32 : ew E 32 = Z_to_bv 64 SB_D2) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE33 : ew E 33 = Z_to_bv 64 (SFa g pos)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE34 : ew E 34 = Z_to_bv 64 pl) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE35 : ew E 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE2 : ew E 2 = Z_to_bv 64 mf) by (rewrite ER2; exact E2).
assert (EE3 : ew E 3 = w64 (as_gp B)) by (rewrite ER3; exact E3).
assert (EE4 : ew E 4 = w64 (as_tp B)) by (rewrite ER4; exact E4).
assert (EE9 : ew E 9 = Z_to_bv 64 mf) by (rewrite ER9; exact E9).
assert (ER21 : ew E 21 = getr regs2 21)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 21 21%bv eq_refl)).
assert (ER25 : ew E 25 = getr regs2 25)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 25 25%bv eq_refl)).
assert (ER27 : ew E 27 = getr regs2 27)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 27 27%bv eq_refl)).
assert (EE36 : ew E 36 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE37 : ew E 37 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE38 : ew E 38 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE39 : ew E 39 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE40 : ew E 40 = Z_to_bv 64 ((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE41 : ew E 41 = Z_to_bv 64 (Z.of_nat i)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE42 : ew E 42 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE43 : ew E 43 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE44 : ew E 44 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE45 : ew E 45 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear EL HE.
assert (HK : d2_keep W2 mem2 mem2 mf) by apply keep_refl.
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 (BASE + 0x5f8)) with (Z_to_bv 64 (BASE + AF_D2)).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl _ 4 pos HAR Hplin Hin) as Dsep.
unfold zdisjoint in Dsep. cbn [fst snd] in Dsep. rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ), FB in Dsep.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)) as RB0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)) as RB1.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)) as RB2.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)) as RB3.
assert (EV22 : ew E 22 = Z_to_bv 64 (SlotModel.rec_k (e_pl g) i)) by (rewrite ER22; exact E22).
assert (EV27 : ew E 27 = Z_to_bv 64 (SlotModel.rec_addr (e_pl g) i)) by (rewrite ER27; exact H27).
destruct (D2M.fw_accepted (e_pl g) i Hr Ha0) as (Hk4 & D0 & D1 & D2 & D3 & HF2).
assert (P23 : getr regs2 23 = w64 1) by (rewrite H23, Hr; reflexivity).
d2_pin (23%bv : bv 5) 1 P23.
assert (P27 : getr regs2 27 = w64 0) by (rewrite H27, Ha0; reflexivity).
d2_pin (27%bv : bv 5) 0 P27.
assert (P25 : getr regs2 25 = w64 1) by (rewrite H25, HF2; reflexivity).
d2_pin (25%bv : bv 5) 1 P25.
d2_fact 22%nat 4 255 EV22.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
pose proof (d2_add_pl Ex ss0 ms0 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) 4 (SFa g pos) mf HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(rewrite EE9; apply unsigned_lit_small; lia)
ltac:(rewrite EE33; apply unsigned_lit_small; lia) ltac:(rewrite EE34; apply unsigned_lit_small; lia)
ltac:(intros j Hj; destruct j as [|[|[|[|j]]]]; [exact EE42 | exact EE43 | exact EE44 | exact EE45 | lia]) Hpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(left; unfold ESTACK in *; lia)
ltac:(destruct Dsep; [left | right]; lia)) as HP; clear HS; rename HP into HS end.
clear SHOK.
assert (SHOK : sh_ok SEGS Bx_D2 [mkSHE 34 0 4] E (mrestrict (w_H W2) mem2))
by (eapply d2_sh_pl; [exact HAR | exact Hplin | rewrite EE32; apply unsigned_lit_small; unfold SB_D2; lia
| rewrite EE34; apply unsigned_lit_small; lia | lia]).
d2_fact 42%nat 0 9 EE42.
d2_fact 43%nat 0 9 EE43.
d2_fact 44%nat 0 9 EE44.
d2_fact 45%nat 0 9 EE45.
d2_norm.
d2_run AF_D2F. d2_call W2. d2_run AF_D2F. d2_call W2. d2_run AF_D2F.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (21%bv : bv 5) X21; prreg HS (25%bv : bv 5) X25; prreg HS (15%bv : bv 5) X15; prreg HS (20%bv : bv 5) X20;
rewrite ER21 in X21; rewrite EE34 in X25; rewrite EE32 in X15; rewrite EE33, unsigned_lit_small in X20 by lia;
pmkst HS;
apply SRr_ret; right; right; left;
unfold inv_caseF, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [| split; [exact Hr | split; [exact Ha0 | split; [rewrite X21; exact H21 | split; [exact X25 | split; [exact X15 | unfold V_s; exact X20]]]]]];
destruct (D2M.hw_kept (e_pl g) i ltac:(left; rewrite Ha0; discriminate)) as [Hh1 Hh2];
unfold hw_at, m_have, m_hwb in *; rewrite Hh1, Hh2;
exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW)
end.
Qed.
(* Case V: the REAC-version record accepted (eight bytes): id's raw block equals the payload's head (the bcmp at
   0x80f04), and the walk stops at 0x80f20, where seg_D3 starts. *)
Theorem d2_case_V : forall g pos mf i pl (W2 : world SEGS) c2,
inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf i pl W2 c2 ->
SlotModel.rec_r (e_pl g) i = 1 -> SlotModel.rec_addr (e_pl g) i = 0x600 ->
SRr SEGS W2 c2 (Q_D2 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 HD Hr Ha6.
destruct HD as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo1 & Hmo2 & HEC & HPB & HW & SBb & SBa &
H21 & Bb & Ba & H27 & H23 & H25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HEC as (E2 & E9 & E8 & Hmf & Hm32 & E3 & E4 & E19 & M80 & M192 & M176 & _).
pose proof HPB as (Hi & Hhb & Hpl & Hid & M112 & Hfix & Hmid & Hmag & M136 & M144 & M152 & M160 & E22 & Hcur).
destruct (d2_geom g pos mf ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ Hmf) as (Hce & H47 & H16 & HST).
pose proof HJ as (HAR & _).
assert (Hin : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hf0 & Hfc & _).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR Hin) as (Hal64 & _).
rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ) in Hf0, Hfc, Hal64.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite FB in Hfc.
pose proof (hblocks_in g ly2 S2 pl _ Hhb) as Hplin.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl _ HAR Hplin) as (Hpl16 & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
destruct (req_size_pos0 (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Rq].
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lpl.
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid.
pose proof (SlotModel.rec_id_length (e_pl g) i) as Lid0.
unfold RcIdentModel.ID_SIZE in Lid, Lid0.
unfold mf_fixed, mf_id, mf_again, id_at, m_id in *.
destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
destruct Hid as (Ib & Iz & Is).
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 132) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 148) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 134) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 136) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 138) Ba ltac:(lia) ltac:(unfold V_again; lia)) as A26.
pose proof (bytes_vmA1 W2 mem2 _ _ 20 (SFa g pos + 372) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I20.
pose proof (bytes_vmA1 W2 mem2 _ _ 36 (SFa g pos + 388) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I36.
pose proof (bytes_vmA2 W2 mem2 _ _ 22 (SFa g pos + 374) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I22.
pose proof (bytes_vmA2 W2 mem2 _ _ 24 (SFa g pos + 376) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I24.
pose proof (bytes_vmA2 W2 mem2 _ _ 26 (SFa g pos + 378) Ib ltac:(lia) ltac:(unfold V_id; lia)) as I26.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 28) (SFa g pos + 140) ltac:(unfold V_again; lia) F96) as F96'.
pose proof (vm_val _ _ _ (SFa g pos + V_again + 3) (SFa g pos + 115) ltac:(unfold V_again; lia) F104) as F104'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 28) (SFa g pos + 380) ltac:(unfold V_id; lia) F120) as F120'.
pose proof (vm_val _ _ _ (SFa g pos + V_id + 3) (SFa g pos + 355) ltac:(unfold V_id; lia) F128) as F128'.
pose proof (vm_mod64 _ _ _ M136) as M136'.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) as Rhf.
pose proof (proj1 (D2M.addr_range (e_pl g) i)) as Rad.
assert (HS : st_ok_pi SEGS VAL
(Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))))
ss_D2 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + AF_D2)) mem2 (seg_rom SEGS)))).
{ apply (d2_entry W2 regs2 mem2 mf (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _ (SlotModel.rec_k (e_pl g) i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 2)) (SlotModel.rec_addr (e_pl g) i));
first [ assumption
| apply SlotModel.bz_range
| apply Z.mod_pos_bound; lia
| unfold ESTACK in *; lia
| match goal with |- context [RcIdentModel.bz ?b1 + 256 * RcIdentModel.bz ?b2] =>
pose proof (SlotModel.bz_range b1); pose proof (SlotModel.bz_range b2); lia end
| pose proof (SlotModel.nrec_range (e_pl g)); unfold m_nrec, SlotModel.nrecn in Hi; lia
| match goal with |- ?gg => fail 100 "ENTRY premise" gg end ]. }
assert (OP1x : d2_opnd W2 mem2 (SFa g pos + 115) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 115 17 HJ Hfr Ba Lid SBa); lia).
assert (OP1y : d2_opnd W2 mem2 (SFa g pos + 355) 17)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 355 17 HJ Hfr Ib Lid Is); lia).
assert (OP2x : d2_opnd W2 mem2 (SFa g pos + 140) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 112 _ 140 8 HJ Hfr Ba Lid SBa); lia).
assert (OP2y : d2_opnd W2 mem2 (SFa g pos + 380) 8)
by (apply (opnd_frame38 g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) 352 _ 380 8 HJ Hfr Ib Lid Is); lia).
assert (EQ1 : forall j, 0 <= j < 17 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 115 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 355 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 3 3 17 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
assert (EQ2 : forall j, 0 <= j < 8 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 140 + j) = aview SEGS (w_H W2) mem2 (SFa g pos + 380 + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 28 28 8 _ _ Ba Ib);
[lia | lia | intros; reflexivity | unfold V_again; lia | unfold V_id; lia | lia]).
remember (Eimg (Ereg regs2 (d2_extra (SFa g pos) pl
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36))
((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64) (Z.of_nat i)
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2))
(RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat ->
ew E n = ew (Ereg regs2 (d2_extra (SFa g pos) pl _ _ _ _ _ _ _ _ _ _ _)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (ER2 : ew E 2 = getr regs2 2)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (ER3 : ew E 3 = getr regs2 3)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (ER4 : ew E 4 = getr regs2 4)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (ER8 : ew E 8 = getr regs2 8)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (ER9 : ew E 9 = getr regs2 9)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 9 9%bv eq_refl)).
assert (ER19 : ew E 19 = getr regs2 19)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 19 19%bv eq_refl)).
assert (ER22 : ew E 22 = getr regs2 22)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 22 22%bv eq_refl)).
assert (EE32 : ew E 32 = Z_to_bv 64 SB_D2) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE33 : ew E 33 = Z_to_bv 64 (SFa g pos)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE34 : ew E 34 = Z_to_bv 64 pl) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE35 : ew E 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 20)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE2 : ew E 2 = Z_to_bv 64 mf) by (rewrite ER2; exact E2).
assert (EE3 : ew E 3 = w64 (as_gp B)) by (rewrite ER3; exact E3).
assert (EE4 : ew E 4 = w64 (as_tp B)) by (rewrite ER4; exact E4).
assert (EE9 : ew E 9 = Z_to_bv 64 mf) by (rewrite ER9; exact E9).
assert (ER21 : ew E 21 = getr regs2 21)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 21 21%bv eq_refl)).
assert (ER25 : ew E 25 = getr regs2 25)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 25 25%bv eq_refl)).
assert (ER27 : ew E 27 = getr regs2 27)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 27 27%bv eq_refl)).
assert (EE36 : ew E 36 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 22) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 23))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE37 : ew E 37 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 24) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 25))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE38 : ew E 38 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 26) +
 256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 27))) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE39 : ew E 39 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_id (e_pl g) (S i)) 36)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE40 : ew E 40 = Z_to_bv 64 ((e_p g + SlotModel.rec_body (e_pl g) i) mod 2 ^ 64))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE41 : ew E 41 = Z_to_bv 64 (Z.of_nat i)) by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE42 : ew E 42 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE43 : ew E 43 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE44 : ew E 44 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE45 : ew E 45 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)))
by (rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear EL HE.
assert (HK : d2_keep W2 mem2 mem2 mf) by apply keep_refl.
assert (SHOK : sh_ok SEGS Bx_D2 [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 (BASE + 0x5f8)) with (Z_to_bv 64 (BASE + AF_D2)).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl _ 4 pos HAR Hplin Hin) as Dsep.
unfold zdisjoint in Dsep. cbn [fst snd] in Dsep. rewrite (d2_sfa g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) HJ), FB in Dsep.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 0)) as RB0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 1)) as RB1.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 2)) as RB2.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) 3)) as RB3.
assert (EV22 : ew E 22 = Z_to_bv 64 (SlotModel.rec_k (e_pl g) i)) by (rewrite ER22; exact E22).
assert (EV27 : ew E 27 = Z_to_bv 64 (SlotModel.rec_addr (e_pl g) i)) by (rewrite ER27; exact H27).
destruct (D2M.ver_accepted (e_pl g) i Hr Ha6) as (Hk8 & HV1 & _).
unfold RcIdentModel.has_reac_version, RcIdentModel.OFF_HAS_VER in HV1.
assert (OPVy : d2_opnd W2 mem2 pl 8)
by (apply (opnd_heap ly2 S2 W2 mem2 md2 pl (SlotModel.rec_k (e_pl g) i) (SlotModel.rec_pl (e_pl g) i) 8 HAR Hplin Hpl);
[rewrite Lpl; apply Z2Nat.id; lia | lia | lia]).
assert (EQV : forall j, 0 <= j < 8 ->
aview SEGS (w_H W2) mem2 (SFa g pos + 380 + j) = aview SEGS (w_H W2) mem2 (pl + j))
by (intros j Hj; apply (eq_bytes W2 mem2 _ _ _ _ 28 0 8 _ _ Ib Hpl);
[lia | rewrite Lpl; lia | intros; apply (D2M.raw_nth (e_pl g) i Hr Ha6); lia | unfold V_id; lia | lia | lia]).
assert (P23 : getr regs2 23 = w64 1) by (rewrite H23, Hr; reflexivity).
d2_pin (23%bv : bv 5) 1 P23.
assert (P27 : getr regs2 27 = w64 0x600) by (rewrite H27, Ha6; reflexivity).
d2_pin (27%bv : bv 5) 0x600 P27.
d2_fact 22%nat 8 255 EV22.
d2_fact 39%nat 1 1 EE39.
d2_norm.
d2_run AF_D2V. d2_call W2. d2_run AF_D2V. d2_call W2. d2_run AF_D2V. d2_call W2. d2_run AF_D2V.
lazymatch goal with HS : st_ok_pi _ _ ?E1 _ (restrict _ ?ms1) |- _ =>
prreg HS (2%bv : bv 5) X2; prreg HS (9%bv : bv 5) X9; prreg HS (8%bv : bv 5) X8; prreg HS (3%bv : bv 5) X3;
prreg HS (4%bv : bv 5) X4; prreg HS (19%bv : bv 5) X19; prreg HS (22%bv : bv 5) X22;
rewrite ER2 in X2; rewrite ER9 in X9; rewrite ER8 in X8; rewrite ER3 in X3; rewrite ER4 in X4; rewrite ER19 in X19;
rewrite ER22 in X22;
prreg HS (25%bv : bv 5) X25; prreg HS (14%bv : bv 5) X14; prreg HS (10%bv : bv 5) X10; prreg HS (11%bv : bv 5) X11;
prreg HS (18%bv : bv 5) X18; prreg HS (26%bv : bv 5) X26; prreg HS (24%bv : bv 5) X24; prreg HS (20%bv : bv 5) X20;
rewrite EE34 in X25; rewrite EE32 in X14;
rewrite (d2_x11 E pl ltac:(rewrite EE34; apply unsigned_lit_small; lia)
ltac:(rewrite EE32; apply unsigned_lit_small; unfold SB_D2; lia) ltac:(lia) ltac:(lia)) in X11;
rewrite EE34, unsigned_lit_small in X10 by lia;
rewrite EE36 in X18; rewrite EE37 in X26; rewrite EE38 in X24; rewrite EE33, unsigned_lit_small in X20 by lia;
pmkst HS;
apply SRr_ret; left;
unfold inv_caseV, acut;
exists ly2, S2, (ms_regs ms1), (ms_mem ms1); eexists;
split; [reflexivity|]; split; [exact HJ|]; split; [exact Hfr|]; split; [exact Hk|]; split; [exact Hmo1|]; split; [exact Hmo2|];
destruct (d2_exit_common g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ (ms_regs ms1) (ms_mem ms1) _ Hfr HEC HPB HJ HK
X2 X9 X8 X3 X4 X19 X22) as [EC' PB'];
split; [exact EC'|]; split; [exact PB'|];
split; [exact (d2_hw_keep g pos i W2 mem2 (ms_mem ms1) mf HK Hce ltac:(lia) Hf0 Hfc HW) |];
split; [exact Hr|]; split; [exact Ha6|]; split; [exact X25|]; split; [exact X14|]; split; [exact X10|];
split; [exact X11|]; split; [exact X18|]; split; [exact X26|]; split; [exact X24|]; unfold V_ev; exact X20
end.
Qed.
(* seg_D2: the ingest result and the record's address decide the case (lib/Prog/SlotModel.v). *)
Theorem seg_D2_holds : seg_D2 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i pl W2 c2 HD.
destruct (D2M.r01 (e_pl g) i) as [Hr|Hr].
- exact (d2_case_Z g pos mf i pl W2 c2 HD Hr).
- destruct (D2M.accepted_addr (e_pl g) i Hr) as [Ha|[Ha|Ha]].
  + exact (d2_case_F g pos mf i pl W2 c2 HD Hr Ha).
  + exact (d2_case_V g pos mf i pl W2 c2 HD Hr Ha).
  + exact (d2_case_M g pos mf i pl W2 c2 HD Hr Ha).
Qed.
End c.
End b.
End a.
