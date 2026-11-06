(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module names changed; 1591 of its 1693 lines of code are new or changed and 1041 lines of the source are left out. *)
(* Segment D5 of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81208 .. 0x813b4): the firmware case of
   the record switch. seg_D5 of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_caseF to the join inv_tail.

   The code (internal path):
     0x81208..0x8126c  the four checked loads of pl[0..3] (each: shadow byte of the payload's first granule,
                       then the byte), the slow blocks 0x814c8..0x814f8 and the reports 0x824a8..0x824bc
     0x8126c..0x81294  pl[0]*1000 + pl[1]*100 + pl[2]*10 + pl[3] against id.fw_milli (x21)
     0x81298           sb zero,24(s3): `s` (SF+192, 8 bytes) is unpoisoned
     0x812a8           reac_identity_fw_str(id.fw_milli, s, 8)
     0x812b8           check_str(w, s, 8)
     0x812bc..0x81348  w = 5 and the five checks s[0..4] = '0'+pl[0], '.', '0'+pl[1..3], each on a checked
                       load of pl[j] and of s[j]
     0x81350..0x81364  `s` is re-poisoned (0xf8) and x26, x21, x24 are reloaded for the join at 0x813b4.

   Every abort branch is decided by a fact of the state: the four digit loads by the payload block's shadow
   (al_shadow: the first granule's shadow byte is 0 when 8 <= rec_k i, and rec_k i when 4 <= rec_k i < 8 --
   the walk splits on that once), the five string compares by the plain model of reac_identity_fw_str
   (lib/Prog/reac_identity_fw_str_c.v: FW v for v < 10000 is '0'+v/1000, '.', three digits), and the checked
   loads of `s` by the zero shadow byte the function itself writes at 0x81298. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require check_str reac_identity_fw_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require
SlotModel RcIdentModel IdentSpec reac_identity_fw_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's addresses need it (shadow_addr, / 8). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of an accepted firmware record ------------------------------------------------------ *)
Module D5M.
Import SlotModel RcIdentModel.
Lemma bz_zb : forall x, 0 <= x < 256 -> bz (zb x) = x.
Proof.
intros x Hx. unfold bz, zb. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma bz_range : forall b, 0 <= bz b < 256.
Proof.
intros b. unfold bz. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H.
Qed.
Lemma digits4 : forall p : list byte, all_digits (firstn 4 p) = true -> (4 <= length p)%nat ->
bz (nthb p 0) <= 9 /\ bz (nthb p 1) <= 9 /\ bz (nthb p 2) <= 9 /\ bz (nthb p 3) <= 9.
Proof.
intros p H Hl. destruct p as [|b0 [|b1 [|b2 [|b3 p]]]]; cbn [length] in Hl; try lia.
cbn [all_digits firstn forallb] in H. unfold nthb. cbn [nth].
repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H end. lia.
Qed.
(* An accepted firmware record: four digits in the payload, and the identity's fw_milli is their value. *)
Lemma fw_facts : forall inp i, rec_r inp i = 1 -> rec_addr inp i = ADDR_FIRMWARE ->
4 <= rec_k inp i /\
bz (nthb (rec_pl inp i) 0) <= 9 /\ bz (nthb (rec_pl inp i) 1) <= 9 /\
bz (nthb (rec_pl inp i) 2) <= 9 /\ bz (nthb (rec_pl inp i) 3) <= 9 /\
fw_milli (rec_id inp (S i)) = fw_value (rec_pl inp i).
Proof.
intros inp i Hr Ha.
pose proof (rec_k_range inp i) as Hkr. pose proof (rec_pl_length inp i) as Hlen.
pose proof (rec_id_length inp i) as Hid. unfold ID_SIZE in Hid.
unfold rec_r in Hr. cbn [rec_id]. rewrite Ha in *. unfold ING in *.
change ADDR_FIRMWARE with 0 in *. cbn [Z.eqb] in *. unfold ing_firmware in *.
destruct ((4 <=? length (rec_pl inp i))%nat && all_digits (firstn 4 (rec_pl inp i)))%bool eqn:C;
[|cbn [fst] in Hr; discriminate Hr].
apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1.
destruct (digits4 _ C2 C1) as (D0 & D1 & D2 & D3).
assert (Hk4 : 4 <= rec_k inp i) by lia.
split; [exact Hk4|]. split; [exact D0|]. split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
cbn [snd].
set (v := fw_value (rec_pl inp i)) in *.
assert (Hv : 0 <= v < 65536).
{ unfold v, fw_value. pose proof (bz_range (nthb (rec_pl inp i) 0)). pose proof (bz_range (nthb (rec_pl inp i) 1)).
  pose proof (bz_range (nthb (rec_pl inp i) 2)). pose proof (bz_range (nthb (rec_pl inp i) 3)). lia. }
assert (L1 : length (upd (rec_id inp i) OFF_FW (le16 v)) = 38%nat).
{ rewrite upd_length; [exact Hid | rewrite Hid; unfold OFF_FW; cbn [length le16]; lia]. }
unfold fw_milli, nthb.
rewrite (nth_upd_before (upd (rec_id inp i) OFF_FW (le16 v)) [zb 1] OFF_HAS_FW 0 (zb 0)
  ltac:(unfold OFF_HAS_FW; lia) ltac:(rewrite L1; unfold OFF_HAS_FW; lia)).
rewrite (nth_upd_before (upd (rec_id inp i) OFF_FW (le16 v)) [zb 1] OFF_HAS_FW 1 (zb 0)
  ltac:(unfold OFF_HAS_FW; lia) ltac:(rewrite L1; unfold OFF_HAS_FW; lia)).
rewrite (nth_upd_in (rec_id inp i) (le16 v) OFF_FW 0 (zb 0)
  ltac:(rewrite Hid; unfold OFF_FW; lia) ltac:(unfold OFF_FW; cbn [length le16]; lia)).
rewrite (nth_upd_in (rec_id inp i) (le16 v) OFF_FW 1 (zb 0)
  ltac:(rewrite Hid; unfold OFF_FW; lia) ltac:(unfold OFF_FW; cbn [length le16]; lia)).
unfold OFF_FW. cbn [Nat.sub nth le16].
rewrite !bz_zb by (apply Z.mod_pos_bound; lia).
pose proof (Z.div_mod v 256 ltac:(lia)) as Hd.
assert (v / 256 < 256) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= v / 256) by (apply Z.div_pos; lia).
rewrite (Z.mod_small (v / 256) 256) by lia. lia.
Qed.
(* The string reac_identity_fw_str prints for a four-digit value. *)
Lemma fw_bytes_digits : forall d0 d1 d2 d3,
0 <= d0 <= 9 -> 0 <= d1 <= 9 -> 0 <= d2 <= 9 -> 0 <= d3 <= 9 ->
reac_identity_fw_str_c.FW (d0 * 1000 + d1 * 100 + d2 * 10 + d3) =
[IdentSpec.dg d0; Z_to_bv 8 0x2e; IdentSpec.dg d1; IdentSpec.dg d2; IdentSpec.dg d3].
Proof.
intros d0 d1 d2 d3 H0 H1 H2 H3.
set (v := d0 * 1000 + d1 * 100 + d2 * 10 + d3) in *.
rewrite (reac_identity_fw_str_c.reac_identity_fw_str_c3_short v ltac:(unfold v; lia)).
assert (E0 : v / 1000 = d0) by (unfold v; Z.div_mod_to_equations; lia).
assert (Em : v mod 1000 = d1 * 100 + d2 * 10 + d3) by (unfold v; Z.div_mod_to_equations; lia).
rewrite E0, Em.
assert (E1 : (d1 * 100 + d2 * 10 + d3) / 100 = d1) by (Z.div_mod_to_equations; lia).
assert (E2 : (d1 * 100 + d2 * 10 + d3) / 10 mod 10 = d2) by (Z.div_mod_to_equations; lia).
assert (E3 : (d1 * 100 + d2 * 10 + d3) mod 10 = d3) by (Z.div_mod_to_equations; lia).
rewrite E1, E2, E3. reflexivity.
Qed.
Lemma fw_len_5 : forall v, 0 <= v < 10000 -> reac_identity_fw_str_c.L v = 5.
Proof.
intros v Hv. rewrite (proj2 (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v ltac:(lia))).
rewrite (proj2 (Z.ltb_lt v 10000)) by lia. reflexivity.
Qed.
Lemma dg_val : forall x, 0 <= x <= 9 -> bv_unsigned (IdentSpec.dg x) = 48 + x.
Proof.
intros x Hx. unfold IdentSpec.dg. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
End D5M.

(* ---- the symbolic state at 0x81208 ------------------------------------------------------------------------ *)
(* Atoms beyond the registers (0..31): 32..35 the payload's four digits, 36 the shadow cell of the payload's
   first granule (SHADOW_OFF + pl / 8), 37 pl / 8, 38 the record body's address (mf+136), 39 the record index
   (mf+160), 40 the address of `before` (mf+88). The aliases turn each (pl + j) >> 3 into atom 37 and the add
   of the shadow base into atom 36, so the four checked loads read one one-byte region. *)
Definition D5_SB : Z := 0x7fff8000.
Definition d5_mfr : YP09.region := YP09.mkRegion (Some 9%nat) 56 168 56 72
[YP09.mkChunk 88 (CVal 8 (SOff 40 0)); YP09.mkChunk 136 (CVal 8 (SOff 38 0));
 YP09.mkChunk 160 (CVal 8 (SOff 39 0))].
Definition d5_plr : YP09.region := YP09.mkRegion (Some 25%nat) 0 4 0 0
[YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0));
 YP09.mkChunk 2 (CVal 1 (SOff 34 0)); YP09.mkChunk 3 (CVal 1 (SOff 35 0))].
Definition d5_shr (v : sv) : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
Definition d5_fshr : YP09.region := YP09.mkRegion (Some 19%nat) 24 25 24 25 [].
(* `s` after reac_identity_fw_str wrote it: FW v and the NUL, for v = d0 d1 . d2 d3 (five digits). *)
Definition d5_sr : YP09.region := YP09.mkRegion (Some 20%nat) 0 6 0 0
[YP09.mkChunk 0 (CVal 1 (SOff 32 48)); YP09.mkChunk 1 (CVal 1 (SLit 46)); YP09.mkChunk 2 (CVal 1 (SOff 33 48));
 YP09.mkChunk 3 (CVal 1 (SOff 34 48)); YP09.mkChunk 4 (CVal 1 (SOff 35 48)); YP09.mkChunk 5 (CVal 1 (SLit 0))].
Definition d5_facts (klo khi : Z) : facts :=
mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (15%nat, mkAF D5_SB D5_SB 0);
         (25%nat, HPTR 4); (22%nat, mkAF klo khi 0); (21%nat, mkAF 0 9999 0);
         (32%nat, mkAF 0 9 0); (33%nat, mkAF 0 9 0); (34%nat, mkAF 0 9 0); (35%nat, mkAF 0 9 0)]
[]
[(SAlu ALU_SRL (SOff 25 0) (SLit 3), SOff 37 0); (SAlu ALU_SRL (SOff 25 1) (SLit 3), SOff 37 0);
 (SAlu ALU_SRL (SOff 25 2) (SLit 3), SOff 37 0); (SAlu ALU_SRL (SOff 25 3) (SLit 3), SOff 37 0);
 (SAlu ALU_ADD (SOff 37 0) (SOff 15 0), SOff 36 0)].
Definition d5_ss (v : sv) (klo khi : Z) : sstate :=
mkSS 0xafc sr_atoms [d5_mfr; d5_plr; d5_shr v; d5_fshr] None (d5_facts klo khi).
(* the sum the four digits build, as the engine leaves it at 0x81290 *)
Definition d5_sum : sv :=
SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 1000)) (SMd M_MUL (SOff 33 0) (SLit 100)))
(SMd M_MUL (SOff 34 0) (SLit 10))) (SOff 35 0).
Definition d5_extra (d0 d1 d2 d3 shc pl8 bod idx bef : Z) : list word :=
map (Z_to_bv 64) [d0; d1; d2; d3; shc; pl8; bod; idx; bef].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition d5_E (regs : bvmap 5 word) (d0 d1 d2 d3 shc pl8 bod idx bef : Z) : env :=
Eimg (Ereg regs (d5_extra d0 d1 d2 d3 shc pl8 bod idx bef)).

(* A granule whose shadow byte is 0 is addressable, byte by byte. *)
Lemma d5_ra_zero : forall (rd : Z -> option Z) (Bs p n : Z),
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> 0 <= n <= 8 -> range_addressable rd Bs p n.
Proof.
intros rd Bs p n H Hp Hn x Hx. exists 0. split; [|left; reflexivity].
rewrite <- H. f_equal. unfold shadow_of_addr. f_equal.
lia.
Qed.
Lemma d5_vm1 : forall H mem a v, aview SEGS H mem a = Some v -> 0 <= v < 256 ->
val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hz Hv j Hj. assert (j = 0%nat) by lia. subst j.
destruct (aview_byte SEGS H mem (a + Z.of_nat 0) v ltac:(rewrite Z.add_0_r; exact Hz)) as (b & Hb & Hbv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- Hbv. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma d5_aview1 : forall H mem a v, val_mem SEGS (mrestrict H mem) a 1 v -> 0 <= v < 256 ->
aview SEGS H mem a = Some v.
Proof. intros H mem a v Hv Hr. exact (aview_of_val_mem1 SEGS H mem a v Hv Hr). Qed.
(* A byte of a byte-list in memory, as a one-byte value. *)
Lemma d5_byte : forall (W : world SEGS) mem a (bs : list byte) j,
bytes_at8 W mem a bs -> (j < length bs)%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (a + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb bs j)) /\
0 <= RcIdentModel.bz (RcIdentModel.nthb bs j) < 256.
Proof.
intros W mem a bs j Hb Hj. unfold bytes_at8, garr8 in Hb.
destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
assert (Enth : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = RcIdentModel.bz (RcIdentModel.nthb bs j)).
{ unfold RcIdentModel.bz, RcIdentModel.nthb, RcIdentModel.zb.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth. reflexivity. }
rewrite Enth in Hv, Hr. split; [exact Hv | exact Hr].
Qed.

(* The frame-shadow region's window is the entry's own frame's shadow (awr_byte's frame case). *)
Lemma d5_awr_fsh : forall E (r : YP09.region) rs STK sp0 FP bl0 blc ly pos,
  YP09.r_base r = Some 19%nat -> bv_unsigned (ew E 19) = shadow_addr (frame_addr ly 4 pos) ->
  0 <= YP09.r_wlo r -> YP09.r_whi r <= 128 ->
  awr_ok E rs STK sp0 FP bl0 blc ly [(4, pos)] -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly [(4, pos)].
Proof.
intros E r rs STK sp0 FP bl0 blc ly pos Hb Hn Hlo Hhi H a (r' & [<- | Hin] & Ha).
- right. right. right. exists 4, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. change (fs_frame_bytes 4 / 8) with 128. lia.
- apply H. exists r'. auto.
Qed.
(* A region the call kept: its bytes, and its window's writability. *)
Lemma d5_rk : forall E (H H' : word -> bool) (m m' : word -> option byte) n lo hi wlo whi cs b,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m' a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H' m' a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m' n lo hi wlo whi cs b Hn Hk Hw. split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hk. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hw. exact Ha.
Qed.

(* The frame-shadow byte the walk wrote (a CVal 1 (SLit 0) chunk at offset 24 of the region based at x19). *)
Lemma d5_sh24 : forall E ss (ms : machine_state) (H : word -> bool) i (r : YP09.region) b,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some 19%nat ->
  In (YP09.mkChunk 24 (CVal 1 (SLit 0))) (YP09.r_chunks r) -> bv_unsigned (ew E 19) = b ->
  aview SEGS H (ms_mem ms) (b + 24) = Some 0.
Proof.
intros E ss ms H i r b HS Hn Hb Hin H19.
pose proof (st_ok_mem_ok SEGS E ss _ HS) as (_ & Hok & _).
pose proof (proj1 (Forall_forall _ _) Hok r (nth_error_In _ _ Hn)) as (_ & _ & _ & Hch).
pose proof (proj1 (Forall_forall _ _) Hch _ Hin) as Hc.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. rewrite Hb in Hb2. cbn [base_val] in Hb2. rewrite H19 in Hb2.
injection Hb1 as <-. cbn [ms_mem restrict] in Hb2. rewrite Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. reflexivity.
Qed.

(* ---- the state at 0x81208 ------------------------------------------------------------------------------- *)
Lemma d5_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem
(v : sv) (klo khi mf pl kk SF shv v21 d0 d1 d2 d3 bod idx : Z),
getr regs 9 = w64 mf -> getr regs 2 = w64 mf -> mf mod 32 = 0 ->
alloc_ceiling + 16384 <= mf -> mf + 320 <= 2 ^ 47 ->
getr regs 19 = w64 (shadow_addr SF) -> getr regs 15 = w64 SHADOW_OFF ->
getr regs 25 = w64 pl -> getr regs 22 = w64 kk -> getr regs 21 = w64 v21 ->
4096 <= SF -> SF + 1024 <= alloc_ceiling -> SF mod 64 = 0 ->
pl mod 16 = 0 -> 4096 <= pl -> pl + 4 <= alloc_ceiling -> (SF + 1024 <= pl \/ pl + 4 <= SF) ->
(pl + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= pl) -> (SF + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= SF) ->
klo <= kk <= khi -> 0 <= klo -> khi <= 255 ->
0 <= v21 <= 9999 -> 0 <= d0 <= 9 -> 0 <= d1 <= 9 -> 0 <= d2 <= 9 -> 0 <= d3 <= 9 ->
0 <= bod < 2 ^ 47 -> 0 <= idx < 2 ^ 47 -> 0 <= shv < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (mf + 88) 8 (SF + V_before) ->
val_mem SEGS (mrestrict (w_H W) mem) (mf + 136) 8 bod ->
val_mem SEGS (mrestrict (w_H W) mem) (mf + 160) 8 idx ->
(forall o, 56 <= o < 72 -> apresent (w_H W) mem (mf + o)) ->
apresent (w_H W) mem (shadow_addr SF + 24) ->
val_mem SEGS (mrestrict (w_H W) mem) pl 1 d0 ->
val_mem SEGS (mrestrict (w_H W) mem) (pl + 1) 1 d1 ->
val_mem SEGS (mrestrict (w_H W) mem) (pl + 2) 1 d2 ->
val_mem SEGS (mrestrict (w_H W) mem) (pl + 3) 1 d3 ->
val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr pl) 1 shv ->
sv_denot (d5_E regs d0 d1 d2 d3 (shadow_addr pl) (pl / 8) bod idx (SF + V_before)) v = Z_to_bv 64 shv ->
st_ok_pi SEGS VAL (d5_E regs d0 d1 d2 d3 (shadow_addr pl) (pl / 8) bod idx (SF + V_before))
(d5_ss v klo khi) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xafc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem v klo khi mf pl kk SF shv v21 d0 d1 d2 d3 bod idx
H9 H2 Hmf32 Hmfc Hmf47 H19 H15 H25 H22 H21 HSF0 HSF1 HSF64 Hpl16 Hpl0 Hplc Hsep Happ_pl Happ_SF
Hkk Hklo Hkhi Hv21 Hd0 Hd1 Hd2 Hd3 Hbod Hidx Hshv V88 V136 V160 Hwin Hfsh P0 P1 P2 P3 Psh Hvd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := d5_E regs d0 d1 d2 d3 (shadow_addr pl) (pl / 8) bod idx (SF + V_before)) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (d5_extra d0 d1 d2 d3 (shadow_addr pl) (pl / 8) bod idx (SF + V_before))) n)
  by (intros n Hn; subst E; unfold d5_E; apply Eimg_low; exact Hn).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite EL by (pose proof (bv_unsigned_in_range 5 r) as Q;
      change (bv_modulus 5) with 32 in Q; unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 d0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 d2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 d3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (shadow_addr pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (pl / 8)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 bod) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 idx) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (SF + V_before)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
unfold shadow_addr, SHADOW_OFF in *.
assert (Hpl8 : 0 <= pl / 8) by (apply Z.div_pos; lia).
assert (Hpl8h : pl / 8 <= 0xffffff00000) by (apply Z.div_le_upper_bound; lia).
assert (HSF8 : 0 <= SF / 8 <= 0xffffff00000)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
(* the payload's shadow granule is not the frame's shadow byte at +24 *)
assert (Hdisj : 0x7fff8000 + pl / 8 <> 0x7fff8000 + SF / 8 + 24).
{ intros Heq. assert (Hq : pl / 8 = SF / 8 + 24) by lia.
  assert (pl = SF + 192) by (Z.div_mod_to_equations; lia). lia. }
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
  by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
assert (U9 : base_val E (Some 9%nat) = mf)
  by (apply VB; [rewrite (ER 9%nat 9%bv eq_refl); exact H9 | lia]).
assert (U19 : base_val E (Some 19%nat) = 0x7fff8000 + SF / 8)
  by (apply VB; [rewrite (ER 19%nat 19%bv eq_refl); exact H19 | lia]).
assert (U25 : base_val E (Some 25%nat) = pl)
  by (apply VB; [rewrite (ER 25%nat 25%bv eq_refl); exact H25 | lia]).
assert (U36 : base_val E (Some 36%nat) = 0x7fff8000 + pl / 8) by (apply VB; [exact E36 | lia]).
assert (CH8 : forall off n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (mf + off) 8 w ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) mf (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off n w Hn Hw Hv. apply (chunk_ok_val SEGS E _ mf off 8 (SOff n 0) w);
  [cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hv]. }
assert (CH1 : forall (base off : Z) n w, ew E n = Z_to_bv 64 w -> 0 <= w < 256 ->
  val_mem SEGS (mrestrict (w_H W) mem) (base + off) 1 w ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0)))).
{ intros base off n w Hn Hw Hv. apply (chunk_ok_val SEGS E _ base off 1 (SOff n 0) w);
  [cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Hv]. }
unfold d5_ss. apply pa_entry_st_ok_full.
- subst E. unfold d5_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok, d5_mfr, d5_plr, d5_shr, d5_fshr;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply Hwin. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      -- apply (CH8 88 40%nat (SF + V_before) E40 ltac:(unfold V_before; lia) V88).
      -- apply (CH8 136 38%nat bod E38 ltac:(lia) V136).
      -- apply (CH8 160 39%nat idx E39 ltac:(lia) V160).
  + rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (CH1 pl 0 32%nat d0 E32 ltac:(lia)). rewrite Z.add_0_r. exact P0.
    * apply (CH1 pl 1 33%nat d1 E33 ltac:(lia) P1).
    * apply (CH1 pl 2 34%nat d2 E34 ltac:(lia) P2).
    * apply (CH1 pl 3 35%nat d3 E35 ltac:(lia) P3).
  + rewrite U36. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (0x7fff8000 + pl / 8) 0 1 v shv);
    [exact Hvd | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Psh].
  + rewrite U19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). replace (0x7fff8000 + SF / 8 + o) with (0x7fff8000 + SF / 8 + 24) by lia.
    exact Hfsh.
- apply pairwise_disjoint_of_extents.
  unfold d5_mfr, d5_plr, d5_shr, d5_fshr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U9, U19, U25, U36. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  assert (HSFpl : SF + 1024 <= pl \/ pl + 4 <= SF) by exact Hsep.
  repeat split; lia.
- unfold facts_ok, d5_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  assert (A9 : bv_unsigned (ew E 9) = mf) by (rewrite (ER 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (A2 : bv_unsigned (ew E 2) = mf) by (rewrite (ER 2%nat 2%bv eq_refl), H2; apply unsigned_lit_small; lia).
  assert (A15 : bv_unsigned (ew E 15) = D5_SB) by (rewrite (ER 15%nat 15%bv eq_refl), H15; reflexivity).
  assert (A25 : bv_unsigned (ew E 25) = pl) by (rewrite (ER 25%nat 25%bv eq_refl), H25; apply unsigned_lit_small; lia).
  assert (A22 : bv_unsigned (ew E 22) = kk) by (rewrite (ER 22%nat 22%bv eq_refl), H22; apply unsigned_lit_small; lia).
  assert (A21 : bv_unsigned (ew E 21) = v21) by (rewrite (ER 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
  assert (A32 : bv_unsigned (ew E 32) = d0) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (A33 : bv_unsigned (ew E 33) = d1) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (A34 : bv_unsigned (ew E 34) = d2) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (A35 : bv_unsigned (ew E 35) = d3) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (A36 : bv_unsigned (ew E 36) = 0x7fff8000 + pl / 8) by (rewrite E36; apply unsigned_lit_small; lia).
  assert (A37 : bv_unsigned (ew E 37) = pl / 8) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (ALs : forall j, 0 <= j <= 3 ->
    sv_denot E (SAlu ALU_SRL (SOff 25 j) (SLit 3)) = sv_denot E (SOff 37 0)).
  { intros j Hj. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, A25, A37.
    replace (Z.land (zcanon 3) 63) with 3 by reflexivity.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64. lia. }
  assert (ALadd : sv_denot E (SAlu ALU_ADD (SOff 37 0) (SOff 15 0)) = sv_denot E (SOff 36 0)).
  { apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, A37, A15, A36.
    unfold zcanon, M64, D5_SB. lia. }
  split; [|split; [exact I|]].
  + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite A9, A2, A15, A25, A22, A21, A32, A33, A34, A35.
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 4) with 16. unfold D5_SB.
    repeat split; lia.
  + repeat split;
    first [ exact I | exact (ALs 0 ltac:(lia)) | exact (ALs 1 ltac:(lia)) | exact (ALs 2 ltac:(lia))
          | exact (ALs 3 ltac:(lia)) | exact ALadd ].
Qed.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order (seg_D5's arguments). *)
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
(* What this segment needs of the contract's Section (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HCHK : check_str.tcheck_str_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

#[local] Notation EPRE g := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS g).
#[local] Notation MEV := (mo_malloc MT 256 + mo_free MT).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).

(* ---- what a call of this segment keeps: the machine stack from mf up, the frame but `s`, the frame's shadow,
   and every heap block of the call state ---- *)
Definition d5_ck (g : ectx) (pos mf : Z) (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
  (mf <= a < e_sp0 g) \/
  (SFa g pos <= a < SFa g pos + 1024 /\ ~ (SFa g pos + V_s <= a < SFa g pos + V_s + N_s)) \/
  (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) \/
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m).
Definition d5_kept (g : ectx) (pos mf : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  forall a, d5_ck g pos mf lyc Sc a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a.

Lemma d5_kept_of : forall g pos mf k lyc Sc (W : world SEGS) memc mdc (W3 : world SEGS) mem3 slo
  (E : Z -> Prop),
  AJ g pos lyc Sc W memc mdc k -> frames Sc = [(4, pos)] ->
  alloc_ceiling <= slo -> slo <= mf -> e_sp0 g <= 2 ^ 47 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < mf) -> ~ E a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W3) mem3 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid ps a, In (cid, ps) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, ps)) \/ in_zr a (shadow_addr (frame_addr lyc cid ps), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) ->
  (forall a, E a -> SFa g pos + V_s <= a < SFa g pos + V_s + N_s) ->
  d5_kept g pos mf lyc Sc W memc W3 mem3.
Proof.
intros g pos mf k lyc Sc W memc mdc W3 mem3 slo E HJ Hfrs Hslo Hslm H47 K1 K2 K4 HE.
pose proof HJ as (HAR & Hly & _).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
  by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF0 & HF1 & HFapp).
rewrite EFA in HF0, HF1, HFapp. change (fs_frame_bytes 4) with 1024 in HF1, HFapp.
pose proof asan_consts as (C1 & _).
assert (HFsh : shadow_addr (SFa g pos) + 128 <= SFa g pos \/ SFa g pos + 1024 <= shadow_addr (SFa g pos)).
{ destruct HFapp as (_ & [Hx | [Hx Hy]]); unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  [right | left]; Z.div_mod_to_equations; lia. }
unfold V_s, N_s in HE.
intros a [Ha | [Ha | [Ha | (b & m & Hb & Ha)]]].
- apply K1; [lia | lia | intros HEa; specialize (HE a HEa); lia].
- apply (K4 4 pos a Hin).
  + left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024. lia.
  + intros HEa. specialize (HE a HEa). unfold V_s, N_s in Ha. lia.
- apply (K4 4 pos a Hin).
  + right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4 / 8) with 128. lia.
  + intros HEa. specialize (HE a HEa). lia.
- replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); [lia|].
  replace (b + (a - b)) with a by lia. intros HEa. specialize (HE a HEa).
  apply (block_not_frame_zone SEGS B LAWS lyc Sc W memc mdc b m (a - b) 4 pos HAR Hb Hin); [lia|].
  left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4) with 1024.
  replace (b + (a - b)) with a by lia. lia.
Qed.

(* ---- what the whole segment keeps from its start state: the stack from mf up but the scratch slots, the
   frame but `s`, the frame's shadow but s's cell, and the heap blocks of the start state ---- *)
Definition d5_fz (g : ectx) (pos mf : Z) (bl : list (Z * Z)) (a : Z) : Prop :=
  (mf <= a < e_sp0 g /\ ~ (mf + 56 <= a < mf + 72)) \/
  (SFa g pos <= a < SFa g pos + 1024 /\ ~ (SFa g pos + V_s <= a < SFa g pos + V_s + N_s)) \/
  (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 /\ a <> shadow_addr (SFa g pos) + 24) \/
  (exists b m, In (b, m) bl /\ b <= a < b + req_size m).
Lemma d5_fz_ck : forall g pos mf bl lyc Sc a,
  (forall b m, In (b, m) bl -> In (b, m) (ablocks B lyc Sc)) -> d5_fz g pos mf bl a -> d5_ck g pos mf lyc Sc a.
Proof.
intros g pos mf bl lyc Sc a Hbl [[H1 _] | [[H1 H2] | [[H1 _] | (b & m & Hb & H1)]]].
- left. exact H1.
- right. left. split; assumption.
- right. right. left. exact H1.
- right. right. right. exists b, m. split; [apply Hbl; exact Hb | exact H1].
Qed.
Lemma d5_run_kept : forall E rs (H : word -> bool) (m m' : word -> option byte) mf shf,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
     (mf + 56 <= a < mf + 72) \/ a = shf + 24) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 56 <= a < mf + 72) -> a <> shf + 24 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' mf shf HF HW a Ha H1 H2.
apply (kept_of_frame E rs H m m' (fun x => (mf + 56 <= x < mf + 72) \/ x = shf + 24) HF HW a Ha).
intros [X | X]; [exact (H1 X) | exact (H2 X)].
Qed.
Lemma d5_vm_tr : forall (W W' : world SEGS) m m' (P : Z -> Prop) a (n : nat) v,
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall k, 0 <= k < Z.of_nat n -> P (a + k)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v.
Proof. intros W W' m m' P a n v HK HP Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros k Hk. apply HK, HP, Hk. Qed.
Lemma d5_g8_tr : forall (W W' : world SEGS) m m' (P : Z -> Prop) a l,
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall k, 0 <= k < Z.of_nat (length l) -> P (a + k)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' P a l HK HP Hg. apply (garr8_frame SEGS _ _ _ _ Hg). intros x Hx.
apply (mbyte_of_aview SEGS). apply HK. replace x with (a + (x - a)) by lia. apply HP. lia.
Qed.
Lemma d5_zs_tr : forall (W W' : world SEGS) m m' (P : Z -> Prop) a n,
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall i, 0 <= i < n / 8 -> P (shadow_of_addr SHADOW_OFF a + i)) ->
  zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> zero_shadow (aview SEGS (w_H W') m') SHADOW_OFF a n.
Proof. intros W W' m m' P a n HK HP Hz i Hi. rewrite HK by (apply HP; exact Hi). exact (Hz i Hi). Qed.
Lemma d5_bs_tr : forall (W W' : world SEGS) m m' (P : Z -> Prop) a n,
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall i, 0 <= i < (n + 7) / 8 -> P (shadow_of_addr SHADOW_OFF a + i)) ->
  block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> block_shadow (aview SEGS (w_H W') m') SHADOW_OFF a n.
Proof.
intros W W' m m' P a n HK HP Hb.
apply (block_shadow_agree (aview SEGS (w_H W) m) (aview SEGS (w_H W') m') SHADOW_OFF a n); [|exact Hb].
intros i Hi. apply HK, HP, Hi.
Qed.

Lemma d5_fz_out : forall g pos mf ly S (W : world SEGS) mem md a,
  AR SEGS B ly S W mem md -> In (4, pos) (frames S) -> frame_addr ly 4 pos = SFa g pos ->
  alloc_ceiling + 16384 <= mf -> e_sp0 g <= 2 ^ 47 ->
  d5_fz g pos mf (ablocks B ly S) a ->
  0 <= a < 2 ^ 64 /\ ~ (mf + 56 <= a < mf + 72) /\ a <> shadow_addr (SFa g pos) + 24.
Proof.
intros g pos mf ly S W mem md a HAR Hin EFA Hmf H47 Ha.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF0 & HF1 & HFapp).
rewrite EFA in HF0, HF1, HFapp. change (fs_frame_bytes 4) with 1024 in HF1, HFapp.
pose proof asan_consts as (C1 & _).
assert (HFsh : shadow_addr (SFa g pos) + 128 <= SFa g pos \/ SFa g pos + 1024 <= shadow_addr (SFa g pos)).
{ destruct HFapp as (_ & [Hx | [Hx Hy]]); unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  [right | left]; Z.div_mod_to_equations; lia. }
assert (HSb : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling).
{ unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
destruct Ha as [[H1 H2] | [[H1 H2] | [[H1 H2] | (b & m & Hb & H1)]]].
- split; [lia|]. split; [exact H2|]. lia.
- split; [lia|]. split; [lia|]. lia.
- split; [lia|]. split; [lia|]. exact H2.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbce & _).
  split; [lia|]. split; [lia|]. intros Heq.
  apply (block_not_frame_zone SEGS B LAWS ly S W mem md b m (a - b) 4 pos HAR Hb Hin); [lia|].
  right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 4 / 8) with 128.
  replace (b + (a - b)) with a by lia. lia.
Qed.

(* The meter after a program call: its post keeps the state's meter (HMT0). *)
Lemma d5_meter0 : forall S0 Sc S3 k,
  mo_le MT S0 Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  mo_le MT S0 S3 (k * MEV) /\ mo_ok MT S3 ((EV_LLVMF - k) * MEV).
Proof.
intros S0 Sc S3 k HMLE HMOK. pose proof (HMT0 Sc S3) as H0. split.
- replace (k * MEV) with (k * MEV + 0) by ring. exact (mo_le_trans MT MTL _ _ _ _ _ HMLE H0).
- apply (mo_ok_step MT MTL Sc S3 0 ((EV_LLVMF - k) * MEV)); [rewrite Z.add_0_l; exact HMOK | exact H0].
Qed.

Lemma d5_aview_present : forall (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> aview SEGS H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma d5_garr8_aview : forall (H : word -> bool) (mem : word -> option byte) a l j,
  garr8 SEGS (mrestrict H mem) a l -> (j < length l)%nat -> aview SEGS H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H mem a l j Hg Hj. destruct (Hg j Hj) as (Hv & Hr). specialize (Hv 0%nat ltac:(lia)).
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The call chain at a call the entry makes from its own frame (s0 = sp0 holds the entry's saved ra and s0). *)
Lemma d5_chain : forall g pos lyc Sc (W : world SEGS) memc mdc k mf,
  EPRE g -> AJ g pos lyc Sc W memc mdc k ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  val_mem SEGS (rd W memc) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  exists ch, achain lyc (aview SEGS (w_H W) memc) mf (e_sp0 g) ch.
Proof.
intros g pos lyc Sc W memc mdc k mf HPRE HJ Hmf Vra Vs0.
pose proof HPRE as (HFN & Hraz & _).
destruct HFN as (_ & _ & Hra40 & _ & _ & _ & _ & Hach & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
change (spZ (e_regs g)) with (e_sp0 g) in Hach.
destruct (Z_lt_le_dec (e_sp0 g) (ly_top lyc - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  assert (HRAr : 0 <= RA_LLVMF < 2 ^ 64).
  { rewrite <- Hraz. unfold raZ. pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  apply (achain_push lyc (aview SEGS (w_H (e_W g)) (e_mem g)) _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf).
  + apply (achain_ly_top (e_ly g)); [exact ETop | exact Hach].
  + rewrite ETop. clear - Htop1 H47. lia.
  + intros a Ha. exact (aview_above_of_journal B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] lyc Sc W memc mdc k HJ a Ha).
  + apply rdword_of_val_mem; [exact Vra | exact HRAr].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; exact Rs0r].
  + rewrite <- Hraz. exact Hra40.
  + clear - Hceil Hslo HSTK'. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmf. lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* The frame and the stack at a call of this segment. *)
Lemma d5_geo : forall g pos lyc Sc (W : world SEGS) memc mdc k mf,
  AJ g pos lyc Sc W memc mdc k -> frames Sc = [(4, pos)] -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  frame_addr lyc 4 pos = SFa g pos /\ In (4, pos) (frames Sc) /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  (forall a, SFa g pos <= a < SFa g pos + 1024 -> apresent (w_H W) memc a /\ ~ aowned B lyc Sc a) /\
  alloc_ceiling + 16384 <= mf /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\ 16720 <= LLVMF_STK.
Proof.
intros g pos lyc Sc W memc mdc k mf HJ Hfrs Hmf.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
assert (EFA : frame_addr lyc 4 pos = SFa g pos)
  by (unfold SFa, frame_addr; destruct Hly as (_ & _ & _ & _ & _ & EF & _); rewrite EF; reflexivity).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hin) as (HF0 & HF1 & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR Hin) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hin) as (_ & _ & HFpres & _).
rewrite EFA in HF0, HF1, HFapp, HF64, HFpres. change (fs_frame_bytes 4) with 1024 in *.
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
split; [exact EFA|]. split; [exact Hin|]. split; [exact HF0|]. split; [exact HF1|]. split; [exact HFapp|].
split; [exact HF64|]. split; [exact HFpres|].
split; [clear - Hmf Hceil Hslo HSTK'; lia|]. split; [clear - Hshi H47; lia|]. split; [exact Hsp0al|].
clear - HSTK'. lia.
Qed.

(* The payload block's first shadow granule, at any state of the journal. *)
Lemma d5_shcell : forall g pos lyc Sc (W : world SEGS) memc mdc k p n,
  AJ g pos lyc Sc W memc mdc k -> In (p, n) (ablocks B lyc Sc) -> 4 <= n <= 255 ->
  aview SEGS (w_H W) memc (shadow_addr p) = Some (if 8 <=? n then 0 else n).
Proof.
intros g pos lyc Sc W memc mdc k p n HJ Hin Hn.
pose proof HJ as (HAR & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ p n HAR Hin) as ((_ & _ & Hc) & _).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
pose proof (Hc 0 ltac:(rewrite Hrq; clear - Hn; lia)) as H0. rewrite Hrq, Z.add_0_r in H0.
change (shadow_addr p) with (shadow_of_addr SHADOW_OFF p). rewrite H0. f_equal.
destruct (Z.leb_spec 8 n); destruct (Z.ltb_spec 0 (n / 8)).
- reflexivity.
- exfalso. clear - H H1. Z.div_mod_to_equations. lia.
- exfalso. clear - H H1. Z.div_mod_to_equations. lia.
- apply Z.mod_small. lia.
Qed.
(* The same value read twice: a region over the payload's shadow cell is kept by any step of the journal. *)
Lemma d5_shcell_kept : forall g pos ly2 S2 (W2 : world SEGS) m2 md2 k ly3 S3 (W3 : world SEGS) m3 md3 k' p n,
  AJ g pos ly2 S2 W2 m2 md2 k -> AJ g pos ly3 S3 W3 m3 md3 k' ->
  In (p, n) (ablocks B ly2 S2) -> In (p, n) (ablocks B ly3 S3) -> 4 <= n <= 255 ->
  aview SEGS (w_H W3) m3 (shadow_addr p) = aview SEGS (w_H W2) m2 (shadow_addr p).
Proof.
intros. rewrite (d5_shcell g pos ly3 S3 W3 m3 md3 k' p n) by assumption.
rewrite (d5_shcell g pos ly2 S2 W2 m2 md2 k p n) by assumption. reflexivity.
Qed.

(* reac_identity_fw_str(v, s, 8) at 0x812a8: `s` is SF+192 in the entry's frame, its shadow byte is 0. *)
Lemma d5_fw_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k hs v retk
  (Q : world SEGS -> config -> Prop),
  AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] -> hblocks B g lyc Sc hs ->
  0 <= v < 10000 -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regsT 10 = w64 v -> getr regsT 11 = w64 (SFa g pos + V_s) -> getr regsT 12 = w64 8 ->
  getr regsT 2 = w64 mf ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 24) = Some 0 ->
  mo_le MT (e_S g) Sc (k * MEV) -> mo_ok MT Sc ((EV_LLVMF - k) * MEV) ->
  (forall W3 ly3 S3 regs3 mem3 md3, wle W W3 ->
   AJ g pos ly3 S3 W3 mem3 md3 k -> aregs_preserved regsT regs3 -> frames S3 = [(4, pos)] ->
   hblocks B g ly3 S3 hs -> Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
   d5_kept g pos mf lyc Sc W memT W3 mem3 ->
   mo_le MT (e_S g) S3 (k * MEV) -> mo_ok MT S3 ((EV_LLVMF - k) * MEV) ->
   getr regs3 10 = w64 5 ->
   garr8 SEGS (rd W3 mem3) (SFa g pos + V_s) (reac_identity_fw_str.fw_bytes v) ->
   SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_identity_fw_str)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k hs v retk Q HJ Hfrs Hbl Hv Hmf Hmf32 R10 R11 R12 Rsp Rra Hretk Hreven
  Hsh24 HMLE HMOK Hk.
destruct (d5_geo g pos lyc Sc W memT mdc k mf HJ Hfrs Hmf)
  as (EFA & Hin4 & HF0 & HF1 & HFapp & HF64 & HFpres & Hmf0 & Hsp47 & Hsp16 & HSTKv).
pose proof asan_consts as (C1 & _).
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf0 Hmf Hsp47 C1; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
set (SF := SFa g pos) in *.
assert (Hfn : reac_identity_fw_str.fw_n v = 6) by (apply reac_identity_fw_str.fw_n_short; lia).
assert (Ew : reac_identity_fw_str.fw_writes (SF + V_s) 8 = true).
{ unfold reac_identity_fw_str.fw_writes, V_s. rewrite (proj2 (Z.eqb_neq (SF + 192) 0)) by lia. reflexivity. }
eapply SRr_bind.
{ apply (HFWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k
    regsT v (SF + V_s) 8 HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - unfold V_s. clear - HF0 HF1 C1. lia.
  - lia.
  - rewrite Hspt. clear - Hmf32. lia.
  - rewrite Hspt. unfold reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK, reac_identity_fw_str.FW_FRAME, ESTACK.
    clear - Hmf HSTKv. lia.
  - rewrite Hspt. clear - Hmf. lia.
  - intros _. rewrite Hfn. unfold reac_identity_fw_str.fw_dest_ok. split; [|split].
    + intros a Ha. right. exists 4, pos. split; [exact Hin4|]. unfold frame_rng, in_zr. cbn [fst snd].
      rewrite EFA. change (fs_frame_bytes 4) with 1024. unfold V_s in Ha. lia.
    + intros a Ha. unfold V_s in Ha. destruct (HFpres a ltac:(lia)) as [Hp Hno].
      split; [|split; [exact Hp | split; [exact Hno|]]].
      * right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
        rewrite EFA. change (fs_frame_bytes 4) with 1024. lia.
      * rewrite Hspt. unfold ESTACK. clear - Ha HF1 Hmf0. lia.
    + apply d5_ra_zero; [| unfold V_s; clear - HF64; lia | lia].
      replace (shadow_of_addr SHADOW_OFF (SF + V_s)) with (shadow_addr SF + 24)
        by (unfold shadow_of_addr, shadow_addr, V_s; clear - HF64; lia).
      exact Hsh24. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfr3 & Hperm3 & Hres).
rewrite Rra.
destruct (d5_meter0 (e_S g) Sc S3 k HMLE HMOK) as [HMLE3 HMOK3].
assert (Hfrs3 : frames S3 = [(4, pos)]) by (rewrite Hfr3; exact Hfrs).
assert (Hbl3 : hblocks B g ly3 S3 hs).
{ destruct Hbl as [Hperm Hfa]. split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm] | exact Hfa]. }
rewrite Ew in Hres. destruct Hres as (Hr10 & Hg & HK).
apply (Hk W3 ly3 S3 regs3 mem3 md3 Hwle HJ3 HP3 Hfrs3 Hbl3 Hperm3); [| exact HMLE3 | exact HMOK3 | | exact Hg].
- destruct HK as (K1 & K2 & _ & K4 & _). rewrite Hspt in K1.
  apply (d5_kept_of g pos mf k lyc Sc W memT mdc W3 mem3 (mf - reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK)
    (fun a => SF + V_s <= a < SF + V_s + reac_identity_fw_str.fw_n v) HJ Hfrs);
  [ unfold reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK, reac_identity_fw_str.FW_FRAME, ESTACK; clear - Hmf0; lia
  | unfold reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK, reac_identity_fw_str.FW_FRAME, ESTACK; lia
  | exact Hsp47 | exact K1 | exact K2 | exact K4 |].
  intros a Ha. rewrite Hfn in Ha. unfold N_s. lia.
- rewrite Hr10. rewrite D5M.fw_len_5 by lia. reflexivity.
Qed.

(* check_str(5, s, 8) at 0x812b8 (afn_pre form, through YC85.cl_callS). *)
Lemma d5_cs_at : forall g pos mf (W : world SEGS) (regsT : bvmap 5 word) memT mdc lyc Sc k (l : list Z) retk
  (Q : world SEGS -> config -> Prop),
  EPRE g -> AJ g pos lyc Sc W memT mdc k -> frames Sc = [(4, pos)] ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  val_mem SEGS (rd W memT) (e_sp0 g - 8) 8 RA_LLVMF ->
  val_mem SEGS (rd W memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
  getr regsT 10 = w64 5 -> getr regsT 11 = w64 (SFa g pos + V_s) -> getr regsT 12 = w64 8 ->
  getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  length l = 5%nat -> Forall (fun b => b <> 0) l -> garr8 SEGS (rd W memT) (SFa g pos + V_s) (l ++ [0]) ->
  aview SEGS (w_H W) memT (shadow_addr (SFa g pos) + 24) = Some 0 ->
  (forall regs3 mem3 md3,
   AJ g pos lyc Sc W mem3 md3 k -> aregs_preserved regsT regs3 -> d5_kept g pos mf lyc Sc W memT W mem3 ->
   (forall a, SFa g pos <= a < SFa g pos + 1024 -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memT a) ->
   SRr SEGS W (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_check_str)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros g pos mf W regsT memT mdc lyc Sc k l retk Q HPRE HJ Hfrs Hmf Hmf32 Vra Vs0
  R10 R11 R12 Rsp Rs0 Rgp Rtp Rra Hretk Hreven Hll Hnz Hg Hsh24 Hk.
pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _).
destruct (d5_geo g pos lyc Sc W memT mdc k mf HJ Hfrs Hmf)
  as (EFA & Hin4 & HF0 & HF1 & HFapp & HF64 & HFpres & Hmf0 & Hsp47 & Hsp16 & HSTKv).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hmfr : 0 <= mf < 2 ^ 64) by (clear - Hmf0 Hmf Hsp47 C1; lia).
assert (Hspt : spZ regsT = mf) by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; exact Hmfr).
assert (Hs0t : s0Z regsT = e_sp0 g)
  by (unfold s0Z; rewrite Rs0; unfold w64, e_sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HBr : BASE + retk < 2 ^ 64) by (destruct HBASE as (HB0 & HB1 & _); clear - HB0 HB1 Hretk; lia).
assert (Hrat : raZ regsT = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
destruct (d5_chain g pos lyc Sc W memT mdc k mf HPRE HJ Hmf Vra Vs0) as (ch & Hach).
set (SF := SFa g pos) in *.
assert (Haro : aro_unowned SEGS B (aview SEGS (w_H W) memT)).
{ apply (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi).
  apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc W memT mdc k HJ).
  apply HRO. exact HROS. }
assert (Hll' : length (l ++ [0]) = 6%nat) by (rewrite length_app, Hll; reflexivity).
assert (Hok : 0 <= 5 -> check_str.tcheck_str_ok W regsT memT 5 (SF + V_s) 8).
{ intros _. unfold check_str.tcheck_str_ok, V_s.
  split; [lia|]. split; [clear - HF0; lia|].
  split.
  { pose proof (frm_off_imgP B lyc Sc W memT mdc 4 pos HAR Hin4) as Himg. rewrite EFA in Himg.
    change (fs_frame_bytes 4) with 1024 in Himg. fold SF in Himg. destruct Himg; [left | right]; lia. }
  split.
  { split; [lia|]. split.
    - intros i Hi. exists (nth (Z.to_nat i) (l ++ [0]) 0). split.
      + replace (SF + 192 + i) with (SF + 192 + Z.of_nat (Z.to_nat i)) by lia.
        apply d5_garr8_aview; [exact Hg | lia].
      + rewrite app_nth1 by lia. apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
    - intros _. replace (SF + 192 + 5) with (SF + 192 + Z.of_nat (length l)) by (rewrite Hll; lia).
      rewrite (d5_garr8_aview _ _ (SF + 192) (l ++ [0]) (length l) Hg ltac:(lia)).
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  split; [intros a Ha; rewrite Hspt; unfold check_str.CHECK_STR_STK, ESTACK; clear - Ha HF1 Hmf0; lia|].
  split; [apply (amem_range_sub_app SF 1024 (SF + 192) (5 + 1) HFapp HF1); lia|].
  split.
  { apply d5_ra_zero; [| clear - HF64; lia | lia].
    replace (shadow_of_addr SHADOW_OFF (SF + 192)) with (shadow_addr SF + 24)
      by (unfold shadow_of_addr, shadow_addr; clear - HF64; lia).
    exact Hsh24. }
  split.
  { apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memT mdc 4 pos (SF + 192) (5 + 1) HAR Hin4);
    rewrite ?EFA; change (fs_frame_bytes 4) with 1024; lia. }
  intros a Ha. apply d5_aview_present. apply (proj1 (HFpres a ltac:(clear - Ha HF64; lia))). }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W regsT memT (Z_to_bv 64 (BASE + AF_check_str)) LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g)
    (e_W g) (e_mem g) (e_md g) [(4, pos)] lyc Sc mdc k check_str.CHECK_STR_STK [] 0 (mf - e_sp0 g)
    (getr regsT 1) ch (fun ly' S' W' _ _ _ => ly' = lyc /\ S' = Sc /\ W' = W) HJ).
  - rewrite Hspt. ring.
  - pose proof (Z.div_mod mf 32 ltac:(lia)) as D1. pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D2.
    rewrite Hmf32, Z.add_0_r in D1. rewrite Hsp16, Z.add_0_r in D2.
    replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult.
  - clear - Hmf. lia.
  - unfold check_str.CHECK_STR_STK, ESTACK. lia.
  - unfold check_str.CHECK_STR_STK, ESTACK. clear - Hmf HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hretk | exact Hreven].
  - change (4096 <= raZ regsT). rewrite Hrat. clear - HBLO Hretk. lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by ring. rewrite Hs0t. exact Hach.
  - intros HPRE1. exact (HCHK lyc Sc W regsT memT mdc ch 5 (SF + V_s) 8 HPRE1 Haro R10 R11 R12
      ltac:(lia) ltac:(lia) Hok).
  - intros a (rg & [] & _). }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJ1 & HP3 & (-> & -> & ->)).
rewrite Rra in *. rewrite Z.add_0_r in HJ3.
replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJ1 by ring.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
apply (Hk regs3 mem3 md3 HJ3 HP3); [|
  intros a Ha; apply (F4 4 pos a Hin4);
  [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 4) with 1024;
   fold SF; exact Ha | intros (rg & [] & _)]].
apply (d5_kept_of g pos mf k lyc Sc W memT mdc W mem3 (mf - check_str.CHECK_STR_STK) (fun _ => False) HJ Hfrs);
  [unfold check_str.CHECK_STR_STK, ESTACK; clear - Hmf0; lia | unfold check_str.CHECK_STR_STK, ESTACK; lia
  | exact Hsp47 | | | | intros a []].
- intros a Ha1 Ha2 _. apply F1; [exact Ha1 | exact Ha2].
- intros b mm i Hb Hi _. apply (F2 b mm i Hb Hb Hi). intros (rg & [] & _).
- intros cid ps a Hcp Hr' _. apply (F4 cid ps a Hcp Hr'). intros (rg & [] & _).
Qed.

Local Ltac d5_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | (apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; apply Z.leb_le; reflexivity|])
  | (eapply d5_awr_fsh; [reflexivity | eassumption | cbn [YP09.r_wlo]; apply Z.leb_le; reflexivity
                          | cbn [YP09.r_whi]; apply Z.leb_le; reflexivity |])
  | (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | eassumption
      | cbn [YP09.r_wlo]; assumption | cbn [YP09.r_whi]; assumption |]) ].

Local Ltac d5_win U9 U19 :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wlo whi aa Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr | ]);
  try destruct Hin;
  first [ rewrite U9 in Hr; left; lia | rewrite U19 in Hr; right; lia | exfalso; lia ].

Theorem seg_D5_holds :
seg_D5 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS.
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (HPB & HHW & Hr1 & Haddr & R21 & R25 & R15 & R20).
destruct HPB as (Hi & Hbl & Hplb & Hid & V112 & Hfix & Hmid & Hmag & V136 & V144 & V152 & V160 & R22 & Hcur).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hmf47 : mf + 320 <= 2 ^ 47) by (clear - Hmfb Hshi H47; lia).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Happ_SF : SF + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= SF)
  by (destruct HSFapp as (_ & [Hx | [Hx Hy]]); unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
      [left | right]; lia).
(* ---- the record and its payload block ---- *)
set (inp := e_pl g) in *.
set (kk := SlotModel.rec_k inp i) in *.
assert (Hinpl : In (pl, kk) (ablocks B ly2 S2))
  by (destruct Hbl as [Hperm _]; apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl kk HAR2 Hinpl)
  as (Hpl16 & Hpl4096 & Hplce & Hplapp & Hplpres & _ & Hkmal).
destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 pl kk HAR2 Hinpl) as (Hplsh & Hplhull).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl kk 4 pos HAR2 Hinpl Hin4) as Hdf.
unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
(* ---- the model ---- *)
destruct (D5M.fw_facts inp i Hr1 Haddr) as (Hk4 & Hdg0 & Hdg1 & Hdg2 & Hdg3 & Hfwm).
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold kk in Hkr.
pose proof (SlotModel.rec_pl_length inp i) as Hpllen.
pose proof (SlotModel.nrec_range inp) as Hnr.
pose proof (SlotModel.rec_bounds inp i) as (_ & Hbod0 & Hbodk & _ & _ & Hcs).
assert (Hrq : req_size kk = kk) by (unfold req_size; destruct (Z.eqb_spec kk 0); lia).
rewrite Hrq in Hplce, Hplapp, Hplpres, Hdf.
assert (Happ_pl : pl + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= pl)
  by (destruct Hplapp as (_ & [Hx | [Hx Hy]]); unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
      [left | right]; lia).
assert (Hsep : SF + 1024 <= pl \/ pl + 4 <= SF) by (clear - Hdf Hk4; lia).
(* the four digits *)
set (d0 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 0)) in *.
set (d1 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 1)) in *.
set (d2 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2)) in *.
set (d3 := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3)) in *.
assert (Hplb4 : (4 <= length (SlotModel.rec_pl inp i))%nat) by (rewrite Hpllen; lia).
destruct (d5_byte W2 mem2 pl _ 0%nat Hplb ltac:(lia)) as (P0' & _).
destruct (d5_byte W2 mem2 pl _ 1%nat Hplb ltac:(lia)) as (P1 & _).
destruct (d5_byte W2 mem2 pl _ 2%nat Hplb ltac:(lia)) as (P2 & _).
destruct (d5_byte W2 mem2 pl _ 3%nat Hplb ltac:(lia)) as (P3 & _).
assert (P0 : val_mem SEGS (rd W2 mem2) pl 1 d0) by (rewrite <- (Z.add_0_r pl); exact P0').
replace (pl + Z.of_nat 1) with (pl + 1) in P1 by lia.
replace (pl + Z.of_nat 2) with (pl + 2) in P2 by lia.
replace (pl + Z.of_nat 3) with (pl + 3) in P3 by lia.
(* the record body's address and the index *)
pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
destruct HPRE' as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _). fold inp in Hlen.
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
assert (Hi64 : (Z.of_nat i < 64)%Z)
  by (unfold m_nrec, SlotModel.nrecn in Hi; fold inp in Hi; clear - Hi Hnr; lia).
assert (Hn0 : 0 < e_n g).
{ destruct Hinp as [[Hz _] | [[Hz _] _]]; [|exact Hz]. exfalso.
  unfold m_nrec in Hi. fold inp in Hi.
  assert (Hl0 : length inp = 0%nat) by (clear - Hlen Hz; lia).
  apply length_zero_iff_nil in Hl0.
  assert (Hz65 : SlotModel.nrecn [] = 0%nat) by (vm_compute; reflexivity).
  rewrite Hl0, Hz65 in Hi. lia. }
assert (Hpin : In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)))
  by (destruct Hinp as [[Hz _] | [_ Hx]]; [lia | exact Hx]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hpin) as (_ & Hp4096 & Hpce & _).
assert (Hbodb : 0 <= e_p g + SlotModel.rec_body inp i < 2 ^ 47).
{ assert (Hnl : SlotModel.nlen inp = e_n g) by (unfold SlotModel.nlen; rewrite Hlen; reflexivity).
  assert (Hrqn : req_size (e_n g) = e_n g) by (unfold req_size; destruct (Z.eqb_spec (e_n g) 0); lia).
  clear - Hbod0 Hbodk Hp4096 Hpce Hnl Hrqn C1 Hkr. lia. }
assert (Hidxb : 0 <= Z.of_nat i < 2 ^ 47) by (clear - Hi64; lia).
(* the frame's own bytes and the stack window are present *)
assert (Hwin : forall o, 56 <= o < 72 -> apresent (w_H W2) mem2 (mf + o)).
{ intros o Ho. apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
    (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) (mf + o) HJ
    ltac:(left; clear - Ho Hmfb HSTK' Has; lia))). }
assert (Hfsh : apresent (w_H W2) mem2 (shadow_addr SF + 24)).
{ apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
    (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) (shadow_addr SF + 24) HJ
    ltac:(right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
          unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear; lia))). }
(* the payload block's first shadow granule *)
destruct Hplsh as (Hpl8m & _ & Hshc).
pose proof (Hshc 0 ltac:(rewrite Hrq; clear - Hk4 Hkr; lia)) as Hsh0.
rewrite Hrq, Z.add_0_r in Hsh0.
assert (Hfw21 : RcIdentModel.fw_milli (m_id g (S i)) = d0 * 1000 + d1 * 100 + d2 * 10 + d3)
  by (unfold m_id; fold inp; rewrite Hfwm; unfold RcIdentModel.fw_value; reflexivity).
assert (Hd0b : 0 <= d0 <= 9)
  by (pose proof (D5M.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 0)); clear - Hdg0 H; lia).
assert (Hd1b : 0 <= d1 <= 9)
  by (pose proof (D5M.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 1)); clear - Hdg1 H; lia).
assert (Hd2b : 0 <= d2 <= 9)
  by (pose proof (D5M.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2)); clear - Hdg2 H; lia).
assert (Hd3b : 0 <= d3 <= 9)
  by (pose proof (D5M.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3)); clear - Hdg3 H; lia).
assert (Hv21b : 0 <= RcIdentModel.fw_milli (m_id g (S i)) <= 9999) by (rewrite Hfw21; lia).
destruct Hfix as (M32 & M40 & M48 & M72 & M88 & M96 & M104 & M120 & M128).
(* ---- the two shapes of the payload's first shadow byte ---- *)
destruct (Z_le_gt_dec 8 kk) as [HK8 | HK8].
{ assert (Psh : val_mem SEGS (rd W2 mem2) (shadow_addr pl) 1 0).
  { apply d5_vm1; [|lia]. change (shadow_addr pl) with (shadow_of_addr SHADOW_OFF pl). rewrite Hsh0. f_equal.
    destruct (Z.ltb_spec 0 (kk / 8)) as [Hx|Hx]; [reflexivity | exfalso; clear - HK8 Hx; lia]. }
  pose proof (d5_entry W2 regs2 mem2 (SLit 0) 8 255 mf pl kk SF 0
    (RcIdentModel.fw_milli (m_id g (S i))) d0 d1 d2 d3 (e_p g + SlotModel.rec_body inp i) (Z.of_nat i)
    Rs1 Rsp Hmf32 Hmf0 Hmf47 Rs3 R15 R25 R22 R21 HSF0 HSF1 HSF64 Hpl16 Hpl4096
    ltac:(clear - Hplce Hk4; lia) Hsep Happ_pl Happ_SF
    ltac:(clear - HK8 Hkr; lia) ltac:(lia) ltac:(lia) Hv21b Hd0b Hd1b Hd2b Hd3b Hbodb Hidxb ltac:(lia)
    M88 V136 V160 Hwin Hfsh P0 P1 P2 P3 Psh ltac:(cbn [sv_denot]; reflexivity)) as HS.
  set (E := d5_E regs2 d0 d1 d2 d3 (shadow_addr pl) (pl / 8) (e_p g + SlotModel.rec_body inp i) (Z.of_nat i)
    (SF + V_before)) in HS.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold d5_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
    by (intros n r Hn; subst E; unfold d5_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9d : bv_unsigned (ew E 9) = sp0 + (mf - sp0))
    by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; unfold w64; rewrite unsigned_lit_small by lia; ring).
  assert (U19 : bv_unsigned (ew E 19) = shadow_addr (frame_addr ly2 4 pos)).
  { rewrite (EE 19%nat 19%bv eq_refl), Rs3, EFa. unfold w64. apply unsigned_lit_small.
    fold SF. unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1. lia. }
  assert (Hd56 : - LLVMF_STK <= mf - sp0 + 56) by (clear - Hmfb HSTK' Has; lia).
  assert (Hd72 : mf - sp0 + 72 <= 0) by (clear - Hmfb; lia).
  unfold cfg_at. change (w64 (BASE + 0xafc)) with (Z_to_bv 64 (BASE + 0xafc)).
  (* ---- run 1: 0x81208 .. the compare of the digits' value with fw_milli at 0x81290 ---- *)
  assert (E32 : ew E 32 = Z_to_bv 64 d0)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 d1)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 d2)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 d3)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
  paj_run_sh RUNP HS HJ; [d5_awr|].
  rename HF into HFa1, HFr into HFr1, HG into HG1. cbn [ms_mem mkst] in HFr1.
  psrr_branch_pi RUNP BR HS.
  2: { exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. clear Hc.
       rewrite !U_SAlu, !U_SMd, !U_SOff, !U_SLit. cbn [zalu_raw zmd_raw].
       rewrite E32, E33, E34, E35, (EE 21%nat 21%bv eq_refl), R21. unfold w64.
       rewrite !unsigned_lit_small by lia. rewrite Hfw21. unfold zcanon, M64.
       clear - Hd0b Hd1b Hd2b Hd3b. lia. }
  (* ---- run 2: 0x81298 (`s` unpoisoned) .. the call of reac_identity_fw_str at 0x812a8 ---- *)
  paj_run_shc RUNP RUNC HS HJ; [d5_awr|].
  rename HF into HFa2, HFr into HFr2, HG into HG2.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in Q10. rewrite (EE 20%nat 20%bv eq_refl), R20 in Q11.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
  pose proof (d5_sh24 E _ _ (w_H W2) 3 _ (shadow_addr (frame_addr ly2 4 pos)) HS eq_refl eq_refl
    ltac:(cbn; left; reflexivity) U19) as Hsh24. rewrite EFa in Hsh24.
  pmkst HS. rewrite (PSIG IS_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
  apply (d5_fw_at g pos mf W2 _ _ _ ly2 S2 (4 * Z.of_nat i + 3) [(pl, kk)]
    (RcIdentModel.fw_milli (m_id g (S i))) 2976 _ HJ Hfrs Hbl ltac:(lia) Hmfb Hmf32 Q10 Q11 Q12 Q2 Q1
    ltac:(lia) ltac:(reflexivity) Hsh24 MLE MOK).
  intros W3 ly3 S3 regs3 mem3 md3 Hwle3 HJ3 HP3 Hfrs3 Hbl3 Hperm3 HK3 MLE3 MOK3 Hr10 Hfw.
  (* ---- back at 0x812ac: the four regions are kept ---- *)
  assert (Hinpl3 : In (pl, kk) (ablocks B ly3 S3))
    by (destruct Hbl3 as [Hperm _]; apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
  pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  assert (EFa3 : frame_addr ly3 4 pos = SF)
    by (unfold SF, SFa, frame_addr; destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _); rewrite EF3; reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite U9d; ring).
  assert (U25 : bv_unsigned (ew E 25) = pl)
    by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = shadow_addr pl)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs2 _ 4);
        apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?Qr -> _ => assert (HQ : Qr); [|specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (d5_rk E _ _ _ _ 9%nat _ _ _ _ _ mf U9).
      + intros a Ha. apply HK3. left. clear - Ha Hmfb. lia.
      + intros a Ha. apply Hpres3. clear - Ha Hmfb HSTK' Has. lia.
    - apply (d5_rk E _ _ _ _ 25%nat _ _ _ _ _ pl U25); [|intros a Ha; lia].
      intros a Ha. apply HK3. right. right. right. exists pl, kk. split; [exact Hinpl | rewrite Hrq; lia].
    - apply (d5_rk E _ _ _ _ 36%nat _ _ _ _ _ (shadow_addr pl) U36); [|intros a Ha; lia].
      intros a Ha. replace a with (shadow_addr pl) by lia.
      exact (d5_shcell_kept g pos ly2 S2 W2 _ _ _ ly3 S3 W3 mem3 md3 _ pl kk HJ HJ3 Hinpl Hinpl3 ltac:(lia)).
    - apply (d5_rk E _ _ _ _ 19%nat _ _ _ _ _ (shadow_addr SF)); [rewrite U19, EFa; reflexivity | |].
      + intros a Ha. apply HK3. right. right. left. fold SF. clear - Ha. lia.
      + intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
          (e_md g) [(4, pos)] ly3 S3 W3 mem3 md3 (4 * Z.of_nat i + 3) a HJ3
          ltac:(right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
                unfold in_zr; cbn [fst snd]; rewrite EFa3, HFB; clear - Ha; lia))). }
  rewrite <- restrict_mkst_fx in HS3.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
  (* ---- what the segment has kept so far ---- *)
  assert (U19s : bv_unsigned (ew E 19) = shadow_addr SF) by (rewrite U19, EFa; reflexivity).
  assert (HFsh : shadow_addr SF + 128 <= SF \/ SF + 1024 <= shadow_addr SF).
  { destruct HSFapp as (_ & [Hx | [Hx Hy]]);
    unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [right | left]; clear - Hx HSF0 HSF1 C1; Z.div_mod_to_equations; lia. }
  assert (HShb : 0 <= shadow_addr SF /\ shadow_addr SF + 128 <= alloc_ceiling)
    by (unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSF1 C1; Z.div_mod_to_equations; lia).
  assert (Hsp47 : sp0 <= 2 ^ 47) by (clear - Hshi H47; lia).
  assert (FK3 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    rewrite (HK3 a (d5_fz_ck g pos mf _ ly2 S2 a (fun b m H => H) Ha)).
    rewrite (d5_run_kept E _ (w_H W2) _ _ mf (shadow_addr SF) HFr2 ltac:(d5_win U9 U19s) a Ha1 Ha2 Ha3).
    exact (d5_run_kept E _ (w_H W2) _ _ mf (shadow_addr SF) HFr1 ltac:(d5_win U9 U19s) a Ha1 Ha2 Ha3). }
  (* ---- 0x812ac mv s5,a0: pin the result, then run 3 to the call of check_str at 0x812b8 ---- *)
  pose proof (ast_ok_pi_set_reg_fp (havoc E 512%nat (map (getr regs3) CLOB)) _ _ 10%bv (SLit 5) HS3
    ltac:(reflexivity) ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Hr10; reflexivity)) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4. clear HS3.
  assert (U9h : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 9) = sp0 + (mf - sp0))
    by (rewrite ew_havoc_old by (cbv; lia); exact U9d).
  assert (U19h : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 19) = shadow_addr SF)
    by (rewrite ew_havoc_old by (cbv; lia); exact U19s).
  assert (U9h' : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 9) = mf) by (rewrite U9h; ring).
  assert (U19h3 : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 19)
    = shadow_addr (frame_addr ly3 4 pos)) by (rewrite U19h, EFa3; reflexivity).
  paj_run_shc RUNP RUNC HS4 HJ3; [d5_awr|].
  rename HF into HFa3, HFr into HFr3, HG into HG3.
  assert (FK4 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    rewrite (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr3 ltac:(d5_win U9h' U19h) a Ha1 Ha2 Ha3).
    exact (FK3 a Ha). }
  assert (RK3 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    exact (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr3 ltac:(d5_win U9h' U19h) a Ha1 Ha2 Ha3). }
  assert (RK3f : forall a, SF <= a < SF + 1024 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. apply (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr3 ltac:(d5_win U9h' U19h) a);
    [clear - Ha HSF0 HSF1 C1; lia | clear - Ha HSF1 Hmf0; lia | clear - Ha HFsh; lia]. }
  (* ---- the call of check_str at 0x812b8 ---- *)
  assert (Efw : reac_identity_fw_str.fw_bytes (RcIdentModel.fw_milli (m_id g (S i)))
    = [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3; 0]).
  { unfold reac_identity_fw_str.fw_bytes. rewrite Hfw21.
    rewrite (D5M.fw_bytes_digits d0 d1 d2 d3 Hd0b Hd1b Hd2b Hd3b).
    cbn [map app]. rewrite !(D5M.dg_val) by assumption. reflexivity. }
  rewrite Efw in Hfw.
  assert (Hgs : garr8 SEGS (rd W3 (ms_mem ms1)) (SF + V_s) [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3; 0]).
  { apply (d5_g8_tr W3 W3 mem3 (ms_mem ms1) (fun a => SF <= a < SF + 1024) _ _ RK3f); [|exact Hfw].
    intros kz Hkz. cbn [length] in Hkz. unfold V_s. clear - Hkz. lia. }
  pose proof (d5_sh24 _ _ _ (w_H W3) 3 _ (shadow_addr (frame_addr ly3 4 pos)) HS4 eq_refl eq_refl
    ltac:(cbn; left; reflexivity) U19h3) as Hsh24b. rewrite EFa3 in Hsh24b.
  prreg HS4 (10%bv : bv 5) T10. prreg HS4 (11%bv : bv 5) T11. prreg HS4 (12%bv : bv 5) T12.
  prreg HS4 (2%bv : bv 5) T2. prreg HS4 (8%bv : bv 5) T8. prreg HS4 (3%bv : bv 5) T3.
  prreg HS4 (4%bv : bv 5) T4. prreg HS4 (1%bv : bv 5) T1.
  rewrite (EE 20%nat 20%bv eq_refl), R20 in T11. rewrite (EE 2%nat 2%bv eq_refl), Rsp in T2.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in T8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in T3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in T4.
  assert (Vra4 : val_mem SEGS (rd W3 (ms_mem ms1)) (sp0 - 8) 8 RA_LLVMF).
  { apply (d5_vm_tr W2 W3 mem2 (ms_mem ms1) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK4 x Hx))); [|exact Vra].
    intros kz Hkz. left. clear - Hkz Hmfb. cbn in Hkz. lia. }
  assert (Vs04 : val_mem SEGS (rd W3 (ms_mem ms1)) (sp0 - 16) 8 (s0Z (e_regs g))).
  { apply (d5_vm_tr W2 W3 mem2 (ms_mem ms1) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK4 x Hx))); [|exact Vs0].
    intros kz Hkz. left. clear - Hkz Hmfb. cbn in Hkz. lia. }
  pmkst HS4. rewrite (PSIG IS_check_str AF_check_str eq_refl).
  apply (d5_cs_at g pos mf W3 _ _ _ ly3 S3 (4 * Z.of_nat i + 3) [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3] 2992 _
    HPRE HJ3 Hfrs3 Hmfb Hmf32 Vra4 Vs04 T10 T11 T12 T2 T8 T3 T4 T1 ltac:(lia) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(repeat constructor; lia) Hgs Hsh24b).
  intros regs5 mem5 md5 HJ5 HP5 HK5 HKF5.
  (* ---- back at 0x812bc: the four regions are kept across check_str ---- *)
  assert (FK5 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a -> aview SEGS (w_H W3) mem5 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite (HK5 a (d5_fz_ck g pos mf _ ly3 S3 a
      (fun b m H => Permutation_in _ (Permutation_sym Hperm3) H) Ha)). exact (FK4 a Ha). }
  pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  jafter_call_keep_hi HS4 528%nat regs5 (mrestrict (w_H W3) mem5) HP5 [0%nat; 1%nat; 2%nat; 3%nat] HS5.
  match type of HS5 with ?Qr -> _ => assert (HQ : Qr); [|specialize (HS5 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (d5_rk _ _ _ _ _ 9%nat _ _ _ _ _ mf U9h').
      + intros a Ha. apply HK5. left. clear - Ha Hmfb. lia.
      + intros a Ha. apply Hpres5. clear - Ha Hmfb HSTK' Has. lia.
    - apply (d5_rk _ _ _ _ _ 25%nat _ _ _ _ _ pl);
      [rewrite ew_havoc_old by (cbv; lia); rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64;
       apply unsigned_lit_small; clear - Hpl4096 Hplce C1 Hkr; lia | | intros a Ha; lia].
      intros a Ha. apply HK5. right. right. right. exists pl, kk. split; [exact Hinpl3 | rewrite Hrq; lia].
    - apply (d5_rk _ _ _ _ _ 36%nat _ _ _ _ _ (shadow_addr pl));
      [rewrite ew_havoc_old by (cbv; lia); exact U36 | | intros a Ha; lia].
      intros a Ha. replace a with (shadow_addr pl) by lia.
      exact (d5_shcell_kept g pos ly3 S3 W3 _ _ _ ly3 S3 W3 mem5 md5 _ pl kk HJ3 HJ5 Hinpl3 Hinpl3 ltac:(lia)).
    - apply (d5_rk _ _ _ _ _ 19%nat _ _ _ _ _ (shadow_addr SF)); [exact U19h | |].
      + intros a Ha. apply HK5. right. right. left. fold SF. clear - Ha. lia.
      + intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
          (e_md g) [(4, pos)] ly3 S3 W3 mem5 md5 (4 * Z.of_nat i + 3) a HJ5
          ltac:(right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
                unfold in_zr; cbn [fst snd]; rewrite EFa3, HFB; clear - Ha; lia))). }
  rewrite <- restrict_mkst_fx in HS5.
  pose proof (img_env_havoc_hi _ 528%nat (map (getr regs5) CLOB) HEI3 ltac:(cbv; lia)) as HEI5.
  assert (U9i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 9)
    = sp0 + (mf - sp0)) by (rewrite ew_havoc_old by (cbv; lia); exact U9h).
  assert (U9i' : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 9)
    = mf) by (rewrite U9i; ring).
  assert (U19i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 19)
    = shadow_addr (frame_addr ly3 4 pos)) by (rewrite ew_havoc_old by (cbv; lia); exact U19h3).
  assert (U19i' : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 19)
    = shadow_addr SF) by (rewrite ew_havoc_old by (cbv; lia); exact U19h).
  (* the string `s` the formatter wrote, as a region of the state *)
  assert (Hgs5 : garr8 SEGS (rd W3 mem5) (SF + V_s) [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3; 0]).
  { apply (d5_g8_tr W3 W3 (ms_mem ms1) mem5 (fun a => SF <= a < SF + 1024) _ _
      ltac:(intros x Hx; exact (HKF5 x Hx))); [|exact Hgs].
    intros kz Hkz. cbn [length] in Hkz. unfold V_s. clear - Hkz HSF0 HSF1. lia. }
  assert (U20i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 20)
    = SF + V_s).
  { rewrite ew_havoc_old by (cbv; lia). rewrite ew_havoc_old by (cbv; lia).
    rewrite (EE 20%nat 20%bv eq_refl), R20. unfold w64. apply unsigned_lit_small.
    unfold V_s. clear - HSF0 HSF1 C1. lia. }
  pose proof (st_ok_pi_add_region _ _ _ d5_sr HS5 ltac:(vm_compute; reflexivity)) as HS6.
  match type of HS6 with ?Qa -> ?Qb -> _ => assert (HQa : Qa); [|assert (HQb : Qb); [|specialize (HS6 HQa HQb); clear HQa HQb]] end.
  { unfold YP09.region_ok, d5_sr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [ms_mem restrict base_val]. rewrite U20i.
    split; [clear - HSF0; unfold V_s; lia|]. split; [clear - HSF1 C1; unfold V_s; lia|].
    split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 0 1 (SOff 32 48) (48 + d0));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E32, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 0%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 1 1 (SLit 46) 46);
      [ reflexivity | cbn; lia | cbn; lia | exact (proj1 (Hgs5 1%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 2 1 (SOff 33 48) (48 + d1));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E33, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 2%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 3 1 (SOff 34 48) (48 + d2));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E34, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 3%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 4 1 (SOff 35 48) (48 + d3));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E35, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 4%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 5 1 (SLit 0) 0);
      [ reflexivity | cbn; lia | cbn; lia | exact (proj1 (Hgs5 5%nat ltac:(cbn; lia))) ]. }
  { assert (U25i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat
      (map (getr regs5) CLOB)) 25) = pl)
      by (rewrite !ew_havoc_old by (cbv; lia); rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64;
          apply unsigned_lit_small; clear - Hpl4096 Hplce C1 Hkr; lia).
    assert (U36i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat
      (map (getr regs5) CLOB)) 36) = shadow_addr pl)
      by (rewrite !ew_havoc_old by (cbv; lia); exact U36).
    assert (Hshpl : 0x7fff8000 <= shadow_addr pl /\ shadow_addr pl < 0x10007fff8000).
    { unfold shadow_addr, SHADOW_OFF. clear - Hpl4096 Hplce C1 Hkr. Z.div_mod_to_equations. lia. }
    assert (Hshsf : 0x7fff8000 <= shadow_addr SF /\ shadow_addr SF + 128 < 0x10007fff8000).
    { unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1. Z.div_mod_to_equations. lia. }
    apply all_disjoint_of_extents. cbn [ss_mem]. unfold d5_sr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20i, U9i', U25i, U36i, U19i'.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold V_s.
    split; [clear - HSF1 Hmf0; lia|]. split; [clear - Hsep HSF0; lia|].
    split; [clear - Hshpl Happ_SF HSF0 HSF1; lia|]. split; [clear - Hshsf Happ_SF HSF0 HSF1; lia | exact I]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6. clear HS5. rename HS6 into HS5.
  (* ---- run 4: 0x812bc .. the join at 0x813b4 ---- *)
  paj_run_to_sh RUNTOP HS5 HJ5 0xca8; [d5_awr|].
  rename HF into HFa4, HFr into HFr4, HG into HG4.
  assert (FK6 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    rewrite (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr4 ltac:(d5_win U9i' U19i') a Ha1 Ha2 Ha3).
    exact (FK5 a Ha). }
  (* the transporters for the boundary's facts *)
  assert (KMF : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 320 -> (o + Z.of_nat n <= 56 \/ 72 <= o) ->
    val_mem SEGS (rd W2 mem2) (mf + o) n v -> val_mem SEGS (rd W3 (ms_mem ms2)) (mf + o) n v).
  { intros o n v H0 H1 H2 Hv.
    apply (d5_vm_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hv].
    intros kz Hkz. left. clear - kz Hkz H0 H1 H2 Hmfb. lia. }
  assert (KSP : forall o (n : nat) v, - 104 <= o -> o + Z.of_nat n <= 0 ->
    val_mem SEGS (rd W2 mem2) (sp0 + o) n v -> val_mem SEGS (rd W3 (ms_mem ms2)) (sp0 + o) n v).
  { intros o n v H0 H1 Hv.
    apply (d5_vm_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hv].
    intros kz Hkz. left. clear - kz Hkz H0 H1 Hmfb. lia. }
  assert (KFR : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 1024 -> (o + Z.of_nat n <= 192 \/ 200 <= o) ->
    val_mem SEGS (rd W2 mem2) (SF + o) n v -> val_mem SEGS (rd W3 (ms_mem ms2)) (SF + o) n v).
  { intros o n v H0 H1 H2 Hv.
    apply (d5_vm_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hv].
    intros kz Hkz. right. left. fold SF. unfold V_s, N_s. clear - kz Hkz H0 H1 H2. lia. }
  assert (KFG : forall o l, 0 <= o -> o + Z.of_nat (length l) <= 1024 ->
    (o + Z.of_nat (length l) <= 192 \/ 200 <= o) ->
    garr8 SEGS (rd W2 mem2) (SF + o) l -> garr8 SEGS (rd W3 (ms_mem ms2)) (SF + o) l).
  { intros o l H0 H1 H2 Hg.
    apply (d5_g8_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hg].
    intros kz Hkz. right. left. fold SF. unfold V_s, N_s. clear - kz Hkz H0 H1 H2. lia. }
  assert (KFZ : forall o n, 200 <= o -> o + n <= 1024 -> 0 <= n ->
    sh_zero W2 mem2 (SF + o) n -> sh_zero W3 (ms_mem ms2) (SF + o) n).
  { intros o n H0 H1 Hn Hz. unfold sh_zero in *.
    apply (d5_zs_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hz].
    intros ii Hii. right. right. left. fold SF. unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
    split; [clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia
           | clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia]. }
  assert (KFB : forall o n, 200 <= o -> o + n <= 1024 -> 0 <= n ->
    sh_blk W2 mem2 (SF + o) n -> sh_blk W3 (ms_mem ms2) (SF + o) n).
  { intros o n H0 H1 Hn Hb. unfold sh_blk in *.
    apply (d5_bs_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hb].
    intros ii Hii. right. right. left. fold SF. unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
    split; [clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia
           | clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia]. }
  assert (KBG : forall b m l, In (b, m) (ablocks B ly2 S2) -> Z.of_nat (length l) <= req_size m ->
    garr8 SEGS (rd W2 mem2) b l -> garr8 SEGS (rd W3 (ms_mem ms2)) b l).
  { intros b m l Hb Hl Hg.
    apply (d5_g8_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hg].
    intros kz Hkz. right. right. right. exists b, m. split; [exact Hb | clear - kz Hkz Hl; lia]. }
  (* ---- the registers at the join ---- *)
  assert (E38 : ew E 38 = Z_to_bv 64 (e_p g + SlotModel.rec_body inp i))
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
  assert (E39 : ew E 39 = Z_to_bv 64 (Z.of_nat i))
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
  assert (E40 : ew E 40 = Z_to_bv 64 (SF + V_before))
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
  prreg HS5 (26%bv : bv 5) Z26. prreg HS5 (24%bv : bv 5) Z24. prreg HS5 (25%bv : bv 5) Z25.
  prreg HS5 (21%bv : bv 5) Z21. prreg HS5 (2%bv : bv 5) Z2. prreg HS5 (9%bv : bv 5) Z9.
  prreg HS5 (8%bv : bv 5) Z8. prreg HS5 (3%bv : bv 5) Z3. prreg HS5 (4%bv : bv 5) Z4.
  prreg HS5 (19%bv : bv 5) Z19. prreg HS5 (22%bv : bv 5) Z22.
  rewrite E38 in Z26. rewrite E40 in Z24. rewrite E39 in Z21.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Z2.
  rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Z9. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Z8.
  rewrite (EE 3%nat 3%bv eq_refl), Rgp in Z3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Z4.
  rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Z19. rewrite (EE 22%nat 22%bv eq_refl), R22 in Z22.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as [Efd Efs].
  (* ---- the boundary inv_tail at 0x813b4 ---- *)
  apply SRr_ret. unfold inv_tail, acut. pmkst HS5.
  exists ly3, S3, (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md5) mat2 md5).
  split; [reflexivity|].
  split; [exact HJ5|]. split; [exact Hfrs3|]. split; [exact Hk|].
  split; [exact MLE3|]. split; [exact MOK3|].
  destruct Hbl3 as [Hperm3' Hfa3].
  split.
  - unfold ecommon. change (e_sp0 g) with sp0. fold SF.
    split; [exact Z2|]. split; [exact Z9|]. split; [exact Z8|]. split; [exact Hmfb|]. split; [exact Hmf32|].
    split; [exact Z3|]. split; [exact Z4|]. split; [exact Z19|].
    split; [apply (KMF 80 8%nat); [lia | lia | right; lia | exact V80]|].
    split; [apply (KMF 192 8%nat); [lia | lia | right; lia | exact V192]|].
    split; [apply (KMF 176 8%nat); [lia | lia | right; lia | exact V176]|].
    split; [replace (sp0 - 8) with (sp0 + (-8)) by ring; apply (KSP (-8) 8%nat); [lia | lia | exact Vra]|].
    split; [replace (sp0 - 16) with (sp0 + (-16)) by ring; apply (KSP (-16) 8%nat); [lia | lia | exact Vs0]|].
    split; [replace (sp0 - 24) with (sp0 + (-24)) by ring; apply (KSP (-24) 8%nat); [lia | lia | exact W9]|].
    split; [replace (sp0 - 32) with (sp0 + (-32)) by ring; apply (KSP (-32) 8%nat); [lia | lia | exact W18]|].
    split; [replace (sp0 - 40) with (sp0 + (-40)) by ring; apply (KSP (-40) 8%nat); [lia | lia | exact W19]|].
    split; [replace (sp0 - 48) with (sp0 + (-48)) by ring; apply (KSP (-48) 8%nat); [lia | lia | exact W20]|].
    split; [replace (sp0 - 56) with (sp0 + (-56)) by ring; apply (KSP (-56) 8%nat); [lia | lia | exact W21]|].
    split; [replace (sp0 - 64) with (sp0 + (-64)) by ring; apply (KSP (-64) 8%nat); [lia | lia | exact W22]|].
    split; [replace (sp0 - 72) with (sp0 + (-72)) by ring; apply (KSP (-72) 8%nat); [lia | lia | exact W23]|].
    split; [replace (sp0 - 80) with (sp0 + (-80)) by ring; apply (KSP (-80) 8%nat); [lia | lia | exact W24]|].
    split; [replace (sp0 - 88) with (sp0 + (-88)) by ring; apply (KSP (-88) 8%nat); [lia | lia | exact W25]|].
    split; [replace (sp0 - 96) with (sp0 + (-96)) by ring; apply (KSP (-96) 8%nat); [lia | lia | exact W26]|].
    split; [replace (sp0 - 104) with (sp0 + (-104)) by ring; apply (KSP (-104) 8%nat); [lia | lia | exact W27]|].
    split; [apply (KMF 24 8%nat); [lia | lia | left; lia | exact Vmf24]|].
    split; [apply (KFR 1016 8%nat); [lia | lia | right; lia | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [rewrite Efs; reflexivity|].
    apply (KBG (e_p g) (e_n g)).
    + apply (Permutation_in _ (Permutation_sym (proj1 Hbl))). right. exact Hpin.
    + rewrite length_map. try fold inp. clear - Hlen Hn0. unfold req_size.
      destruct (Z.eqb_spec (e_n g) 0); lia.
    + exact Hinb.
  - split.
    + unfold P_body, id_at, mf_fixed, mf_id, mf_again. fold SF. fold inp. fold kk.
      split; [exact Hi|].
      split; [split; [exact Hperm3' | exact Hfa3]|].
      split; [apply (KBG pl kk); [exact Hinpl | rewrite length_map, SlotModel.rec_pl_length, Hrq; lia | exact Hplb]|].
      unfold id_at in Hid. destruct Hid as (Hidb & Hidz & Hidbk).
      split.
      { split; [apply (KFG V_id); [unfold V_id; lia | | unfold V_id, N_id; right; lia | exact Hidb]
               | split; [apply (KFZ V_id N_id); [unfold V_id; lia | unfold V_id, N_id; lia | unfold N_id; lia | exact Hidz]
                        | apply (KFB V_id N_id); [unfold V_id; lia | unfold V_id, N_id; lia | unfold N_id; lia | exact Hidbk]]].
        rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE. lia. }
      split; [apply (KMF 112 8%nat); [lia | lia | right; lia | exact V112]|].
      split.
      { split; [apply (KMF 32 8%nat); [lia | lia | left; lia | exact M32]|].
        split; [apply (KMF 40 8%nat); [lia | lia | left; lia | exact M40]|].
        split; [apply (KMF 48 8%nat); [lia | lia | left; lia | exact M48]|].
        split; [apply (KMF 72 8%nat); [lia | lia | right; lia | exact M72]|].
        split; [apply (KMF 88 8%nat); [lia | lia | right; lia | exact M88]|].
        split; [apply (KMF 96 8%nat); [lia | lia | right; lia | exact M96]|].
        split; [apply (KMF 104 8%nat); [lia | lia | right; lia | exact M104]|].
        split; [apply (KMF 120 8%nat); [lia | lia | right; lia | exact M120]|].
        apply (KMF 128 8%nat); [lia | lia | right; lia | exact M128]. }
      split; [apply (KMF 184 8%nat); [lia | lia | right; lia | exact Hmid]|].
      split; [apply (KMF 168 8%nat); [lia | lia | right; lia | exact Hmag]|].
      split; [apply (KMF 136 8%nat); [lia | lia | right; lia | exact V136]|].
      split; [apply (KMF 144 8%nat); [lia | lia | right; lia | exact V144]|].
      split; [apply (KMF 152 8%nat); [lia | lia | right; lia | exact V152]|].
      split; [apply (KMF 160 8%nat); [lia | lia | right; lia | exact V160]|].
      split; [exact Z22 | exact Hcur].
    + split.
      * unfold hw_at. fold SF. destruct HHW as (Hh1 & Hh2 & Hh3 & Hh4).
        split; [apply (KFR V_hw 4%nat); [unfold V_hw; lia | unfold V_hw; lia | unfold V_hw; right; lia | exact Hh1]|].
        split.
        { replace (SF + V_hw + 4) with (SF + (V_hw + 4)) by ring. apply (KFG (V_hw + 4));
          [unfold V_hw; lia | | unfold V_hw; right; lia |].
          - rewrite length_map. unfold m_hwb. try fold inp. unfold V_hw.
            assert (Hl8 : (length (SlotModel.rec_hwb inp (S i)) <= 8)%nat).
            { unfold SlotModel.rec_hwb. destruct (SlotModel.rec_hw inp (S i)) as [h|] eqn:Eh; [|cbn; lia].
              clear - Eh. revert h Eh. generalize (S i). induction n as [|n IH]; intros h Eh;
              cbn [SlotModel.rec_hw] in Eh; [discriminate|].
              destruct (_ && _) eqn:Cc; [|exact (IH h Eh)]. injection Eh as <-. rewrite length_firstn.
              apply andb_true_iff in Cc as [_ Cc]. apply Z.leb_le in Cc. rewrite SlotModel.rec_pl_length. lia. }
            lia.
          - replace (SF + (V_hw + 4)) with (SF + V_hw + 4) by ring. exact Hh2. }
        split; [apply (KFZ V_hw N_hw); [unfold V_hw; lia | unfold V_hw, N_hw; lia | unfold N_hw; lia | exact Hh3]|].
        apply (KFB V_hw N_hw); [unfold V_hw; lia | unfold V_hw, N_hw; lia | unfold N_hw; lia | exact Hh4].
      * split; [exact Z26|]. split; [fold SF; exact Z24|]. split; [exact Z25 | exact Z21]. }
{ assert (Psh : val_mem SEGS (rd W2 mem2) (shadow_addr pl) 1 kk).
  { apply d5_vm1; [|clear - Hk4 HK8; lia].
    change (shadow_addr pl) with (shadow_of_addr SHADOW_OFF pl). rewrite Hsh0. f_equal.
    destruct (Z.ltb_spec 0 (kk / 8)) as [Hx|Hx];
    [exfalso; clear - HK8 Hx Hk4; lia | clear - Hk4 HK8; Z.div_mod_to_equations; lia]. }
  pose proof (d5_entry W2 regs2 mem2 (SOff 22 0) 4 7 mf pl kk SF kk
    (RcIdentModel.fw_milli (m_id g (S i))) d0 d1 d2 d3 (e_p g + SlotModel.rec_body inp i) (Z.of_nat i)
    Rs1 Rsp Hmf32 Hmf0 Hmf47 Rs3 R15 R25 R22 R21 HSF0 HSF1 HSF64 Hpl16 Hpl4096
    ltac:(clear - Hplce Hk4; lia) Hsep Happ_pl Happ_SF
    ltac:(clear - HK8 Hk4; lia) ltac:(lia) ltac:(lia) Hv21b Hd0b Hd1b Hd2b Hd3b Hbodb Hidxb
    ltac:(clear - Hk4 HK8; lia)
    M88 V136 V160 Hwin Hfsh P0 P1 P2 P3 Psh
    ltac:(cbn [sv_denot]; unfold d5_E;
          rewrite (ew_Eimg_Ereg_nat regs2 (d5_extra d0 d1 d2 d3 (shadow_addr pl) (pl / 8)
            (e_p g + SlotModel.rec_body inp i) (Z.of_nat i) (SF + V_before)) 22%nat 22%bv eq_refl), R22, Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity)) as HS.
  set (E := d5_E regs2 d0 d1 d2 d3 (shadow_addr pl) (pl / 8) (e_p g + SlotModel.rec_body inp i) (Z.of_nat i)
    (SF + V_before)) in HS.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold d5_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
    by (intros n r Hn; subst E; unfold d5_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9d : bv_unsigned (ew E 9) = sp0 + (mf - sp0))
    by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; unfold w64; rewrite unsigned_lit_small by lia; ring).
  assert (U19 : bv_unsigned (ew E 19) = shadow_addr (frame_addr ly2 4 pos)).
  { rewrite (EE 19%nat 19%bv eq_refl), Rs3, EFa. unfold w64. apply unsigned_lit_small.
    fold SF. unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1. lia. }
  assert (Hd56 : - LLVMF_STK <= mf - sp0 + 56) by (clear - Hmfb HSTK' Has; lia).
  assert (Hd72 : mf - sp0 + 72 <= 0) by (clear - Hmfb; lia).
  unfold cfg_at. change (w64 (BASE + 0xafc)) with (Z_to_bv 64 (BASE + 0xafc)).
  (* ---- run 1: 0x81208 .. the compare of the digits' value with fw_milli at 0x81290 ---- *)
  assert (E32 : ew E 32 = Z_to_bv 64 d0)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 d1)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 d2)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 d3)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
  paj_run_sh RUNP HS HJ; [d5_awr|].
  rename HF into HFa1, HFr into HFr1, HG into HG1. cbn [ms_mem mkst] in HFr1.
  psrr_branch_pi RUNP BR HS.
  2: { exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. clear Hc.
       rewrite !U_SAlu, !U_SMd, !U_SOff, !U_SLit. cbn [zalu_raw zmd_raw].
       rewrite E32, E33, E34, E35, (EE 21%nat 21%bv eq_refl), R21. unfold w64.
       rewrite !unsigned_lit_small by lia. rewrite Hfw21. unfold zcanon, M64.
       clear - Hd0b Hd1b Hd2b Hd3b. lia. }
  (* ---- run 2: 0x81298 (`s` unpoisoned) .. the call of reac_identity_fw_str at 0x812a8 ---- *)
  paj_run_shc RUNP RUNC HS HJ; [d5_awr|].
  rename HF into HFa2, HFr into HFr2, HG into HG2.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in Q10. rewrite (EE 20%nat 20%bv eq_refl), R20 in Q11.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
  pose proof (d5_sh24 E _ _ (w_H W2) 3 _ (shadow_addr (frame_addr ly2 4 pos)) HS eq_refl eq_refl
    ltac:(cbn; left; reflexivity) U19) as Hsh24. rewrite EFa in Hsh24.
  pmkst HS. rewrite (PSIG IS_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
  apply (d5_fw_at g pos mf W2 _ _ _ ly2 S2 (4 * Z.of_nat i + 3) [(pl, kk)]
    (RcIdentModel.fw_milli (m_id g (S i))) 2976 _ HJ Hfrs Hbl ltac:(lia) Hmfb Hmf32 Q10 Q11 Q12 Q2 Q1
    ltac:(lia) ltac:(reflexivity) Hsh24 MLE MOK).
  intros W3 ly3 S3 regs3 mem3 md3 Hwle3 HJ3 HP3 Hfrs3 Hbl3 Hperm3 HK3 MLE3 MOK3 Hr10 Hfw.
  (* ---- back at 0x812ac: the four regions are kept ---- *)
  assert (Hinpl3 : In (pl, kk) (ablocks B ly3 S3))
    by (destruct Hbl3 as [Hperm _]; apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
  pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  assert (EFa3 : frame_addr ly3 4 pos = SF)
    by (unfold SF, SFa, frame_addr; destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _); rewrite EF3; reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite U9d; ring).
  assert (U25 : bv_unsigned (ew E 25) = pl)
    by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = shadow_addr pl)
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs2 _ 4);
        apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?Qr -> _ => assert (HQ : Qr); [|specialize (HS3 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (d5_rk E _ _ _ _ 9%nat _ _ _ _ _ mf U9).
      + intros a Ha. apply HK3. left. clear - Ha Hmfb. lia.
      + intros a Ha. apply Hpres3. clear - Ha Hmfb HSTK' Has. lia.
    - apply (d5_rk E _ _ _ _ 25%nat _ _ _ _ _ pl U25); [|intros a Ha; lia].
      intros a Ha. apply HK3. right. right. right. exists pl, kk. split; [exact Hinpl | rewrite Hrq; lia].
    - apply (d5_rk E _ _ _ _ 36%nat _ _ _ _ _ (shadow_addr pl) U36); [|intros a Ha; lia].
      intros a Ha. replace a with (shadow_addr pl) by lia.
      exact (d5_shcell_kept g pos ly2 S2 W2 _ _ _ ly3 S3 W3 mem3 md3 _ pl kk HJ HJ3 Hinpl Hinpl3 ltac:(lia)).
    - apply (d5_rk E _ _ _ _ 19%nat _ _ _ _ _ (shadow_addr SF)); [rewrite U19, EFa; reflexivity | |].
      + intros a Ha. apply HK3. right. right. left. fold SF. clear - Ha. lia.
      + intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
          (e_md g) [(4, pos)] ly3 S3 W3 mem3 md3 (4 * Z.of_nat i + 3) a HJ3
          ltac:(right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
                unfold in_zr; cbn [fst snd]; rewrite EFa3, HFB; clear - Ha; lia))). }
  rewrite <- restrict_mkst_fx in HS3.
  pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
  (* ---- what the segment has kept so far ---- *)
  assert (U19s : bv_unsigned (ew E 19) = shadow_addr SF) by (rewrite U19, EFa; reflexivity).
  assert (HFsh : shadow_addr SF + 128 <= SF \/ SF + 1024 <= shadow_addr SF).
  { destruct HSFapp as (_ & [Hx | [Hx Hy]]);
    unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [right | left]; clear - Hx HSF0 HSF1 C1; Z.div_mod_to_equations; lia. }
  assert (HShb : 0 <= shadow_addr SF /\ shadow_addr SF + 128 <= alloc_ceiling)
    by (unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSF1 C1; Z.div_mod_to_equations; lia).
  assert (Hsp47 : sp0 <= 2 ^ 47) by (clear - Hshi H47; lia).
  assert (FK3 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    rewrite (HK3 a (d5_fz_ck g pos mf _ ly2 S2 a (fun b m H => H) Ha)).
    rewrite (d5_run_kept E _ (w_H W2) _ _ mf (shadow_addr SF) HFr2 ltac:(d5_win U9 U19s) a Ha1 Ha2 Ha3).
    exact (d5_run_kept E _ (w_H W2) _ _ mf (shadow_addr SF) HFr1 ltac:(d5_win U9 U19s) a Ha1 Ha2 Ha3). }
  (* ---- 0x812ac mv s5,a0: pin the result, then run 3 to the call of check_str at 0x812b8 ---- *)
  pose proof (ast_ok_pi_set_reg_fp (havoc E 512%nat (map (getr regs3) CLOB)) _ _ 10%bv (SLit 5) HS3
    ltac:(reflexivity) ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Hr10; reflexivity)) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4. clear HS3.
  assert (U9h : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 9) = sp0 + (mf - sp0))
    by (rewrite ew_havoc_old by (cbv; lia); exact U9d).
  assert (U19h : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 19) = shadow_addr SF)
    by (rewrite ew_havoc_old by (cbv; lia); exact U19s).
  assert (U9h' : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 9) = mf) by (rewrite U9h; ring).
  assert (U19h3 : bv_unsigned (ew (havoc E 512%nat (map (getr regs3) CLOB)) 19)
    = shadow_addr (frame_addr ly3 4 pos)) by (rewrite U19h, EFa3; reflexivity).
  paj_run_shc RUNP RUNC HS4 HJ3; [d5_awr|].
  rename HF into HFa3, HFr into HFr3, HG into HG3.
  assert (FK4 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    rewrite (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr3 ltac:(d5_win U9h' U19h) a Ha1 Ha2 Ha3).
    exact (FK3 a Ha). }
  assert (RK3 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    exact (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr3 ltac:(d5_win U9h' U19h) a Ha1 Ha2 Ha3). }
  assert (RK3f : forall a, SF <= a < SF + 1024 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. apply (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr3 ltac:(d5_win U9h' U19h) a);
    [clear - Ha HSF0 HSF1 C1; lia | clear - Ha HSF1 Hmf0; lia | clear - Ha HFsh; lia]. }
  (* ---- the call of check_str at 0x812b8 ---- *)
  assert (Efw : reac_identity_fw_str.fw_bytes (RcIdentModel.fw_milli (m_id g (S i)))
    = [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3; 0]).
  { unfold reac_identity_fw_str.fw_bytes. rewrite Hfw21.
    rewrite (D5M.fw_bytes_digits d0 d1 d2 d3 Hd0b Hd1b Hd2b Hd3b).
    cbn [map app]. rewrite !(D5M.dg_val) by assumption. reflexivity. }
  rewrite Efw in Hfw.
  assert (Hgs : garr8 SEGS (rd W3 (ms_mem ms1)) (SF + V_s) [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3; 0]).
  { apply (d5_g8_tr W3 W3 mem3 (ms_mem ms1) (fun a => SF <= a < SF + 1024) _ _ RK3f); [|exact Hfw].
    intros kz Hkz. cbn [length] in Hkz. unfold V_s. clear - Hkz. lia. }
  pose proof (d5_sh24 _ _ _ (w_H W3) 3 _ (shadow_addr (frame_addr ly3 4 pos)) HS4 eq_refl eq_refl
    ltac:(cbn; left; reflexivity) U19h3) as Hsh24b. rewrite EFa3 in Hsh24b.
  prreg HS4 (10%bv : bv 5) T10. prreg HS4 (11%bv : bv 5) T11. prreg HS4 (12%bv : bv 5) T12.
  prreg HS4 (2%bv : bv 5) T2. prreg HS4 (8%bv : bv 5) T8. prreg HS4 (3%bv : bv 5) T3.
  prreg HS4 (4%bv : bv 5) T4. prreg HS4 (1%bv : bv 5) T1.
  rewrite (EE 20%nat 20%bv eq_refl), R20 in T11. rewrite (EE 2%nat 2%bv eq_refl), Rsp in T2.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in T8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in T3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in T4.
  assert (Vra4 : val_mem SEGS (rd W3 (ms_mem ms1)) (sp0 - 8) 8 RA_LLVMF).
  { apply (d5_vm_tr W2 W3 mem2 (ms_mem ms1) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK4 x Hx))); [|exact Vra].
    intros kz Hkz. left. clear - Hkz Hmfb. cbn in Hkz. lia. }
  assert (Vs04 : val_mem SEGS (rd W3 (ms_mem ms1)) (sp0 - 16) 8 (s0Z (e_regs g))).
  { apply (d5_vm_tr W2 W3 mem2 (ms_mem ms1) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK4 x Hx))); [|exact Vs0].
    intros kz Hkz. left. clear - Hkz Hmfb. cbn in Hkz. lia. }
  pmkst HS4. rewrite (PSIG IS_check_str AF_check_str eq_refl).
  apply (d5_cs_at g pos mf W3 _ _ _ ly3 S3 (4 * Z.of_nat i + 3) [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3] 2992 _
    HPRE HJ3 Hfrs3 Hmfb Hmf32 Vra4 Vs04 T10 T11 T12 T2 T8 T3 T4 T1 ltac:(lia) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(repeat constructor; lia) Hgs Hsh24b).
  intros regs5 mem5 md5 HJ5 HP5 HK5 HKF5.
  (* ---- back at 0x812bc: the four regions are kept across check_str ---- *)
  assert (FK5 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a -> aview SEGS (w_H W3) mem5 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite (HK5 a (d5_fz_ck g pos mf _ ly3 S3 a
      (fun b m H => Permutation_in _ (Permutation_sym Hperm3) H) Ha)). exact (FK4 a Ha). }
  pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  jafter_call_keep_hi HS4 528%nat regs5 (mrestrict (w_H W3) mem5) HP5 [0%nat; 1%nat; 2%nat; 3%nat] HS5.
  match type of HS5 with ?Qr -> _ => assert (HQ : Qr); [|specialize (HS5 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (d5_rk _ _ _ _ _ 9%nat _ _ _ _ _ mf U9h').
      + intros a Ha. apply HK5. left. clear - Ha Hmfb. lia.
      + intros a Ha. apply Hpres5. clear - Ha Hmfb HSTK' Has. lia.
    - apply (d5_rk _ _ _ _ _ 25%nat _ _ _ _ _ pl);
      [rewrite ew_havoc_old by (cbv; lia); rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64;
       apply unsigned_lit_small; clear - Hpl4096 Hplce C1 Hkr; lia | | intros a Ha; lia].
      intros a Ha. apply HK5. right. right. right. exists pl, kk. split; [exact Hinpl3 | rewrite Hrq; lia].
    - apply (d5_rk _ _ _ _ _ 36%nat _ _ _ _ _ (shadow_addr pl));
      [rewrite ew_havoc_old by (cbv; lia); exact U36 | | intros a Ha; lia].
      intros a Ha. replace a with (shadow_addr pl) by lia.
      exact (d5_shcell_kept g pos ly3 S3 W3 _ _ _ ly3 S3 W3 mem5 md5 _ pl kk HJ3 HJ5 Hinpl3 Hinpl3 ltac:(lia)).
    - apply (d5_rk _ _ _ _ _ 19%nat _ _ _ _ _ (shadow_addr SF)); [exact U19h | |].
      + intros a Ha. apply HK5. right. right. left. fold SF. clear - Ha. lia.
      + intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
          (e_md g) [(4, pos)] ly3 S3 W3 mem5 md5 (4 * Z.of_nat i + 3) a HJ5
          ltac:(right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
                unfold in_zr; cbn [fst snd]; rewrite EFa3, HFB; clear - Ha; lia))). }
  rewrite <- restrict_mkst_fx in HS5.
  pose proof (img_env_havoc_hi _ 528%nat (map (getr regs5) CLOB) HEI3 ltac:(cbv; lia)) as HEI5.
  assert (U9i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 9)
    = sp0 + (mf - sp0)) by (rewrite ew_havoc_old by (cbv; lia); exact U9h).
  assert (U9i' : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 9)
    = mf) by (rewrite U9i; ring).
  assert (U19i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 19)
    = shadow_addr (frame_addr ly3 4 pos)) by (rewrite ew_havoc_old by (cbv; lia); exact U19h3).
  assert (U19i' : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 19)
    = shadow_addr SF) by (rewrite ew_havoc_old by (cbv; lia); exact U19h).
  (* the string `s` the formatter wrote, as a region of the state *)
  assert (Hgs5 : garr8 SEGS (rd W3 mem5) (SF + V_s) [48 + d0; 46; 48 + d1; 48 + d2; 48 + d3; 0]).
  { apply (d5_g8_tr W3 W3 (ms_mem ms1) mem5 (fun a => SF <= a < SF + 1024) _ _
      ltac:(intros x Hx; exact (HKF5 x Hx))); [|exact Hgs].
    intros kz Hkz. cbn [length] in Hkz. unfold V_s. clear - Hkz HSF0 HSF1. lia. }
  assert (U20i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat (map (getr regs5) CLOB)) 20)
    = SF + V_s).
  { rewrite ew_havoc_old by (cbv; lia). rewrite ew_havoc_old by (cbv; lia).
    rewrite (EE 20%nat 20%bv eq_refl), R20. unfold w64. apply unsigned_lit_small.
    unfold V_s. clear - HSF0 HSF1 C1. lia. }
  pose proof (st_ok_pi_add_region _ _ _ d5_sr HS5 ltac:(vm_compute; reflexivity)) as HS6.
  match type of HS6 with ?Qa -> ?Qb -> _ => assert (HQa : Qa); [|assert (HQb : Qb); [|specialize (HS6 HQa HQb); clear HQa HQb]] end.
  { unfold YP09.region_ok, d5_sr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [ms_mem restrict base_val]. rewrite U20i.
    split; [clear - HSF0; unfold V_s; lia|]. split; [clear - HSF1 C1; unfold V_s; lia|].
    split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 0 1 (SOff 32 48) (48 + d0));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E32, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 0%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 1 1 (SLit 46) 46);
      [ reflexivity | cbn; lia | cbn; lia | exact (proj1 (Hgs5 1%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 2 1 (SOff 33 48) (48 + d1));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E33, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 2%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 3 1 (SOff 34 48) (48 + d2));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E34, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 3%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 4 1 (SOff 35 48) (48 + d3));
      [ cbn [sv_denot]; rewrite !ew_havoc_old by (cbv; lia); rewrite E35, unsigned_lit_small by lia;
        f_equal; lia | cbn; lia | cbn; lia | exact (proj1 (Hgs5 4%nat ltac:(cbn; lia))) ].
    - apply (chunk_ok_val SEGS _ _ (SF + V_s) 5 1 (SLit 0) 0);
      [ reflexivity | cbn; lia | cbn; lia | exact (proj1 (Hgs5 5%nat ltac:(cbn; lia))) ]. }
  { assert (U25i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat
      (map (getr regs5) CLOB)) 25) = pl)
      by (rewrite !ew_havoc_old by (cbv; lia); rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64;
          apply unsigned_lit_small; clear - Hpl4096 Hplce C1 Hkr; lia).
    assert (U36i : bv_unsigned (ew (havoc (havoc E 512%nat (map (getr regs3) CLOB)) 528%nat
      (map (getr regs5) CLOB)) 36) = shadow_addr pl)
      by (rewrite !ew_havoc_old by (cbv; lia); exact U36).
    assert (Hshpl : 0x7fff8000 <= shadow_addr pl /\ shadow_addr pl < 0x10007fff8000).
    { unfold shadow_addr, SHADOW_OFF. clear - Hpl4096 Hplce C1 Hkr. Z.div_mod_to_equations. lia. }
    assert (Hshsf : 0x7fff8000 <= shadow_addr SF /\ shadow_addr SF + 128 < 0x10007fff8000).
    { unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1. Z.div_mod_to_equations. lia. }
    apply all_disjoint_of_extents. cbn [ss_mem]. unfold d5_sr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20i, U9i', U25i, U36i, U19i'.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold V_s.
    split; [clear - HSF1 Hmf0; lia|]. split; [clear - Hsep HSF0; lia|].
    split; [clear - Hshpl Happ_SF HSF0 HSF1; lia|]. split; [clear - Hshsf Happ_SF HSF0 HSF1; lia | exact I]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6. clear HS5. rename HS6 into HS5.
  (* ---- run 4: 0x812bc .. the join at 0x813b4 ---- *)
  paj_run_to_sh RUNTOP HS5 HJ5 0xca8; [d5_awr|].
  rename HF into HFa4, HFr into HFr4, HG into HG4.
  assert (FK6 : forall a, d5_fz g pos mf (ablocks B ly2 S2) a ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. destruct (d5_fz_out g pos mf ly2 S2 W2 mem2 md2 a HAR2 Hin4 EFa Hmf0 Hsp47 Ha) as (Ha1 & Ha2 & Ha3).
    rewrite (d5_run_kept _ _ (w_H W3) _ _ mf (shadow_addr SF) HFr4 ltac:(d5_win U9i' U19i') a Ha1 Ha2 Ha3).
    exact (FK5 a Ha). }
  (* the transporters for the boundary's facts *)
  assert (KMF : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 320 -> (o + Z.of_nat n <= 56 \/ 72 <= o) ->
    val_mem SEGS (rd W2 mem2) (mf + o) n v -> val_mem SEGS (rd W3 (ms_mem ms2)) (mf + o) n v).
  { intros o n v H0 H1 H2 Hv.
    apply (d5_vm_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hv].
    intros kz Hkz. left. clear - kz Hkz H0 H1 H2 Hmfb. lia. }
  assert (KSP : forall o (n : nat) v, - 104 <= o -> o + Z.of_nat n <= 0 ->
    val_mem SEGS (rd W2 mem2) (sp0 + o) n v -> val_mem SEGS (rd W3 (ms_mem ms2)) (sp0 + o) n v).
  { intros o n v H0 H1 Hv.
    apply (d5_vm_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hv].
    intros kz Hkz. left. clear - kz Hkz H0 H1 Hmfb. lia. }
  assert (KFR : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 1024 -> (o + Z.of_nat n <= 192 \/ 200 <= o) ->
    val_mem SEGS (rd W2 mem2) (SF + o) n v -> val_mem SEGS (rd W3 (ms_mem ms2)) (SF + o) n v).
  { intros o n v H0 H1 H2 Hv.
    apply (d5_vm_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hv].
    intros kz Hkz. right. left. fold SF. unfold V_s, N_s. clear - kz Hkz H0 H1 H2. lia. }
  assert (KFG : forall o l, 0 <= o -> o + Z.of_nat (length l) <= 1024 ->
    (o + Z.of_nat (length l) <= 192 \/ 200 <= o) ->
    garr8 SEGS (rd W2 mem2) (SF + o) l -> garr8 SEGS (rd W3 (ms_mem ms2)) (SF + o) l).
  { intros o l H0 H1 H2 Hg.
    apply (d5_g8_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hg].
    intros kz Hkz. right. left. fold SF. unfold V_s, N_s. clear - kz Hkz H0 H1 H2. lia. }
  assert (KFZ : forall o n, 200 <= o -> o + n <= 1024 -> 0 <= n ->
    sh_zero W2 mem2 (SF + o) n -> sh_zero W3 (ms_mem ms2) (SF + o) n).
  { intros o n H0 H1 Hn Hz. unfold sh_zero in *.
    apply (d5_zs_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hz].
    intros ii Hii. right. right. left. fold SF. unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
    split; [clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia
           | clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia]. }
  assert (KFB : forall o n, 200 <= o -> o + n <= 1024 -> 0 <= n ->
    sh_blk W2 mem2 (SF + o) n -> sh_blk W3 (ms_mem ms2) (SF + o) n).
  { intros o n H0 H1 Hn Hb. unfold sh_blk in *.
    apply (d5_bs_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hb].
    intros ii Hii. right. right. left. fold SF. unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
    split; [clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia
           | clear - ii Hii H0 H1 Hn HSF64; Z.div_mod_to_equations; lia]. }
  assert (KBG : forall b m l, In (b, m) (ablocks B ly2 S2) -> Z.of_nat (length l) <= req_size m ->
    garr8 SEGS (rd W2 mem2) b l -> garr8 SEGS (rd W3 (ms_mem ms2)) b l).
  { intros b m l Hb Hl Hg.
    apply (d5_g8_tr W2 W3 mem2 (ms_mem ms2) (d5_fz g pos mf (ablocks B ly2 S2)) _ _
      ltac:(intros x Hx; exact (FK6 x Hx))); [|exact Hg].
    intros kz Hkz. right. right. right. exists b, m. split; [exact Hb | clear - kz Hkz Hl; lia]. }
  (* ---- the registers at the join ---- *)
  assert (E38 : ew E 38 = Z_to_bv 64 (e_p g + SlotModel.rec_body inp i))
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
  assert (E39 : ew E 39 = Z_to_bv 64 (Z.of_nat i))
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
  assert (E40 : ew E 40 = Z_to_bv 64 (SF + V_before))
    by (subst E; unfold d5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
  prreg HS5 (26%bv : bv 5) Z26. prreg HS5 (24%bv : bv 5) Z24. prreg HS5 (25%bv : bv 5) Z25.
  prreg HS5 (21%bv : bv 5) Z21. prreg HS5 (2%bv : bv 5) Z2. prreg HS5 (9%bv : bv 5) Z9.
  prreg HS5 (8%bv : bv 5) Z8. prreg HS5 (3%bv : bv 5) Z3. prreg HS5 (4%bv : bv 5) Z4.
  prreg HS5 (19%bv : bv 5) Z19. prreg HS5 (22%bv : bv 5) Z22.
  rewrite E38 in Z26. rewrite E40 in Z24. rewrite E39 in Z21.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Z25. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Z2.
  rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Z9. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Z8.
  rewrite (EE 3%nat 3%bv eq_refl), Rgp in Z3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Z4.
  rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Z19. rewrite (EE 22%nat 22%bv eq_refl), R22 in Z22.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as [Efd Efs].
  (* ---- the boundary inv_tail at 0x813b4 ---- *)
  apply SRr_ret. unfold inv_tail, acut. pmkst HS5.
  exists ly3, S3, (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md5) mat2 md5).
  split; [reflexivity|].
  split; [exact HJ5|]. split; [exact Hfrs3|]. split; [exact Hk|].
  split; [exact MLE3|]. split; [exact MOK3|].
  destruct Hbl3 as [Hperm3' Hfa3].
  split.
  - unfold ecommon. change (e_sp0 g) with sp0. fold SF.
    split; [exact Z2|]. split; [exact Z9|]. split; [exact Z8|]. split; [exact Hmfb|]. split; [exact Hmf32|].
    split; [exact Z3|]. split; [exact Z4|]. split; [exact Z19|].
    split; [apply (KMF 80 8%nat); [lia | lia | right; lia | exact V80]|].
    split; [apply (KMF 192 8%nat); [lia | lia | right; lia | exact V192]|].
    split; [apply (KMF 176 8%nat); [lia | lia | right; lia | exact V176]|].
    split; [replace (sp0 - 8) with (sp0 + (-8)) by ring; apply (KSP (-8) 8%nat); [lia | lia | exact Vra]|].
    split; [replace (sp0 - 16) with (sp0 + (-16)) by ring; apply (KSP (-16) 8%nat); [lia | lia | exact Vs0]|].
    split; [replace (sp0 - 24) with (sp0 + (-24)) by ring; apply (KSP (-24) 8%nat); [lia | lia | exact W9]|].
    split; [replace (sp0 - 32) with (sp0 + (-32)) by ring; apply (KSP (-32) 8%nat); [lia | lia | exact W18]|].
    split; [replace (sp0 - 40) with (sp0 + (-40)) by ring; apply (KSP (-40) 8%nat); [lia | lia | exact W19]|].
    split; [replace (sp0 - 48) with (sp0 + (-48)) by ring; apply (KSP (-48) 8%nat); [lia | lia | exact W20]|].
    split; [replace (sp0 - 56) with (sp0 + (-56)) by ring; apply (KSP (-56) 8%nat); [lia | lia | exact W21]|].
    split; [replace (sp0 - 64) with (sp0 + (-64)) by ring; apply (KSP (-64) 8%nat); [lia | lia | exact W22]|].
    split; [replace (sp0 - 72) with (sp0 + (-72)) by ring; apply (KSP (-72) 8%nat); [lia | lia | exact W23]|].
    split; [replace (sp0 - 80) with (sp0 + (-80)) by ring; apply (KSP (-80) 8%nat); [lia | lia | exact W24]|].
    split; [replace (sp0 - 88) with (sp0 + (-88)) by ring; apply (KSP (-88) 8%nat); [lia | lia | exact W25]|].
    split; [replace (sp0 - 96) with (sp0 + (-96)) by ring; apply (KSP (-96) 8%nat); [lia | lia | exact W26]|].
    split; [replace (sp0 - 104) with (sp0 + (-104)) by ring; apply (KSP (-104) 8%nat); [lia | lia | exact W27]|].
    split; [apply (KMF 24 8%nat); [lia | lia | left; lia | exact Vmf24]|].
    split; [apply (KFR 1016 8%nat); [lia | lia | right; lia | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [rewrite Efs; reflexivity|].
    apply (KBG (e_p g) (e_n g)).
    + apply (Permutation_in _ (Permutation_sym (proj1 Hbl))). right. exact Hpin.
    + rewrite length_map. try fold inp. clear - Hlen Hn0. unfold req_size.
      destruct (Z.eqb_spec (e_n g) 0); lia.
    + exact Hinb.
  - split.
    + unfold P_body, id_at, mf_fixed, mf_id, mf_again. fold SF. fold inp. fold kk.
      split; [exact Hi|].
      split; [split; [exact Hperm3' | exact Hfa3]|].
      split; [apply (KBG pl kk); [exact Hinpl | rewrite length_map, SlotModel.rec_pl_length, Hrq; lia | exact Hplb]|].
      unfold id_at in Hid. destruct Hid as (Hidb & Hidz & Hidbk).
      split.
      { split; [apply (KFG V_id); [unfold V_id; lia | | unfold V_id, N_id; right; lia | exact Hidb]
               | split; [apply (KFZ V_id N_id); [unfold V_id; lia | unfold V_id, N_id; lia | unfold N_id; lia | exact Hidz]
                        | apply (KFB V_id N_id); [unfold V_id; lia | unfold V_id, N_id; lia | unfold N_id; lia | exact Hidbk]]].
        rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE. lia. }
      split; [apply (KMF 112 8%nat); [lia | lia | right; lia | exact V112]|].
      split.
      { split; [apply (KMF 32 8%nat); [lia | lia | left; lia | exact M32]|].
        split; [apply (KMF 40 8%nat); [lia | lia | left; lia | exact M40]|].
        split; [apply (KMF 48 8%nat); [lia | lia | left; lia | exact M48]|].
        split; [apply (KMF 72 8%nat); [lia | lia | right; lia | exact M72]|].
        split; [apply (KMF 88 8%nat); [lia | lia | right; lia | exact M88]|].
        split; [apply (KMF 96 8%nat); [lia | lia | right; lia | exact M96]|].
        split; [apply (KMF 104 8%nat); [lia | lia | right; lia | exact M104]|].
        split; [apply (KMF 120 8%nat); [lia | lia | right; lia | exact M120]|].
        apply (KMF 128 8%nat); [lia | lia | right; lia | exact M128]. }
      split; [apply (KMF 184 8%nat); [lia | lia | right; lia | exact Hmid]|].
      split; [apply (KMF 168 8%nat); [lia | lia | right; lia | exact Hmag]|].
      split; [apply (KMF 136 8%nat); [lia | lia | right; lia | exact V136]|].
      split; [apply (KMF 144 8%nat); [lia | lia | right; lia | exact V144]|].
      split; [apply (KMF 152 8%nat); [lia | lia | right; lia | exact V152]|].
      split; [apply (KMF 160 8%nat); [lia | lia | right; lia | exact V160]|].
      split; [exact Z22 | exact Hcur].
    + split.
      * unfold hw_at. fold SF. destruct HHW as (Hh1 & Hh2 & Hh3 & Hh4).
        split; [apply (KFR V_hw 4%nat); [unfold V_hw; lia | unfold V_hw; lia | unfold V_hw; right; lia | exact Hh1]|].
        split.
        { replace (SF + V_hw + 4) with (SF + (V_hw + 4)) by ring. apply (KFG (V_hw + 4));
          [unfold V_hw; lia | | unfold V_hw; right; lia |].
          - rewrite length_map. unfold m_hwb. try fold inp. unfold V_hw.
            assert (Hl8 : (length (SlotModel.rec_hwb inp (S i)) <= 8)%nat).
            { unfold SlotModel.rec_hwb. destruct (SlotModel.rec_hw inp (S i)) as [h|] eqn:Eh; [|cbn; lia].
              clear - Eh. revert h Eh. generalize (S i). induction n as [|n IH]; intros h Eh;
              cbn [SlotModel.rec_hw] in Eh; [discriminate|].
              destruct (_ && _) eqn:Cc; [|exact (IH h Eh)]. injection Eh as <-. rewrite length_firstn.
              apply andb_true_iff in Cc as [_ Cc]. apply Z.leb_le in Cc. rewrite SlotModel.rec_pl_length. lia. }
            lia.
          - replace (SF + (V_hw + 4)) with (SF + V_hw + 4) by ring. exact Hh2. }
        split; [apply (KFZ V_hw N_hw); [unfold V_hw; lia | unfold V_hw, N_hw; lia | unfold N_hw; lia | exact Hh3]|].
        apply (KFB V_hw N_hw); [unfold V_hw; lia | unfold V_hw, N_hw; lia | unfold N_hw; lia | exact Hh4].
      * split; [exact Z26|]. split; [fold SF; exact Z24|]. split; [exact Z25 | exact Z21].
 }
Qed.

End c.

End b.
End a.
