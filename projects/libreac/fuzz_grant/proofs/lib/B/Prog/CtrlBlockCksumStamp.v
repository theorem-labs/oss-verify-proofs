(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_block_cksum_stamp on image B (fuzz_grant.asan-ubsan), written for libreac/fuzz_grant; its entry-state steps (the ew register facts and the val_mem facts of the 32 bytes of the block) are adapted from the proof of cmp_entry in proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* reac_ctrl_block_cksum_stamp (image B fuzz_grant.asan-ubsan 0x82554, 46 slots, GrantList.v:1777-1822): image A
   inlines this function into ctrl_finish, so there is no image-A walk of it; its donor is the outer-checksum half
   of lib/A/Prog/CtrlFinish.v. a0 = q, the caller's 32-byte control block (ctrl_finish passes p + 18 by the tail
   jump at 0x84094). The call sums the 31 bytes q[0..31) and stores the low byte of the negated sum at q + 31
   (lib/Prog/RcFin.v stamp32). It writes no other byte outside its own 16-byte frame and returns no value; it
   writes a byte of its caller's block, so the contract is the caller-journal form. Frame 16, no call.
   What this file carries over the donor's shape: the block is the 32 bytes at q (read [0,32), written only q+31);
   the shadow-base cell is object 35 (image A: 32); the image range is IMG_LO_B..IMG_TOP_B. The sum is a counted
   loop (li a4,31; bnez a4): the trip count is a literal, so one paj_run_tok unrolls the 31 passes; the four trap
   guards 0x8257c/0x82588/0x8258c/0x825d0 are decided inside the run from atom 10's facts (1 <= q <= 2^47-33, from
   0 < q and amem_range q 32); the two report branches 0x825c8 (load1) and 0x82608 (store1, the last slot, which
   falls into reac_ctrl_checksum_verify 0x8260c) are refuted inside the run from bks_SH over [q, q+32). No
   side-stack frame, so no live_ok obligation. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib YC1g GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RcFin RcModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The checksum arithmetic (mod 256) needs zify's euclidean-division flag true; this file sets it so itself,
   whatever its Require closure leaves. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- arithmetic of the 64-bit canonical form (CtrlFinish.v) ---------------------------------------------- *)
Lemma bks_zc_add_l : forall x y, zcanon (zcanon x + y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. apply Z.add_mod_idemp_l. lia. Qed.
Lemma bks_zc_add_r : forall x y, zcanon (x + zcanon y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. apply Z.add_mod_idemp_r. lia. Qed.
Lemma bks_zc_mul_m1 : forall b, zcanon (b * zcanon (-1)) = zcanon (- b).
Proof. intros b. unfold zcanon, M64. rewrite Z.mul_mod_idemp_r by lia. f_equal. ring. Qed.
Lemma bks_zc_mod256 : forall x, zcanon x mod 256 = x mod 256.
Proof.
intros x. unfold zcanon, M64. symmetry.
apply Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Ltac bks_zc_flat := rewrite ?bks_zc_mul_m1; repeat (rewrite ?bks_zc_add_l, ?bks_zc_add_r).
(* zcanon x differs from x by a multiple of 256 (256 divides 2^64). Replacing every zcanon by x + 256*k with a
   fresh k makes a checksum goal linear, so lia needs only the two outer mod 256 decompositions. *)
Lemma bks_zc_split256 : forall x, exists k, zcanon x = x + 256 * k.
Proof.
intros x. unfold zcanon, M64.
exists (- (x / 2 ^ 64) * 72057594037927936).
pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as Hd.
change (2 ^ 64) with 18446744073709551616 in *.
lia.
Qed.
Ltac bks_kill256 := repeat match goal with |- context [zcanon ?t] =>
let k := fresh "kz" in let Hk := fresh "Hkz" in
destruct (bks_zc_split256 t) as [k Hk]; rewrite Hk; clear Hk end.

(* ---- the model: RcFin.stamp32 changes byte 31 only ------------------------------------------------------- *)
Lemma bks_byte_range : forall (Bk : list byte) j, 0 <= bv_unsigned (nth j Bk (Z_to_bv 8 0)) < 256.
Proof. intros Bk j. pose proof (bv_unsigned_in_range 8 (nth j Bk (Z_to_bv 8 0))) as Hr. unfold bv_modulus in Hr. cbn in Hr. lia. Qed.
Lemma bks_nth_upd1 : forall (l : list byte) (kk : nat) (b d : byte) (j : nat),
(kk < length l)%nat -> (j < length l)%nat ->
nth j (Mem.upd_bytes l kk [b]) d = if (j =? kk)%nat then b else nth j l d.
Proof.
intros l kk b d j Hk Hj. unfold Mem.upd_bytes.
assert (Hfl : length (firstn kk l) = kk) by (apply firstn_length_le; lia).
destruct (Nat.eqb_spec j kk) as [->|Hne].
- rewrite app_nth2 by lia. rewrite Hfl, Nat.sub_diag. reflexivity.
- destruct (Nat.lt_ge_cases j kk) as [Hlt|Hge].
+ rewrite app_nth1 by lia.
rewrite <- (firstn_skipn kk l) at 2. rewrite app_nth1 by lia. reflexivity.
+ rewrite app_nth2 by lia. rewrite Hfl. cbn [app].
destruct (j - kk)%nat as [|q] eqn:Hq; [lia|]. cbn [nth].
rewrite <- (firstn_skipn (kk + 1)%nat l) at 2.
rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
rewrite firstn_length_le by lia. f_equal. lia.
Qed.
Definition bks_c31 (Bk : list byte) : Z := (- RcModel.psum Bk 31) mod 256.
Lemma bks_c31_range : forall Bk, 0 <= bks_c31 Bk < 256.
Proof. intros Bk. unfold bks_c31. apply Z.mod_pos_bound. lia. Qed.
Lemma bks_stamp_length : forall Bk, length Bk = 32%nat -> length (RcFin.stamp32 Bk) = 32%nat.
Proof. intros Bk HL. unfold RcFin.stamp32. rewrite Mem.upd_bytes_length by (cbn [length]; lia). exact HL. Qed.
Lemma bks_nth : forall (Bk : list byte) (j : nat), length Bk = 32%nat -> (j < 32)%nat ->
nth j (map bv_unsigned (RcFin.stamp32 Bk)) 0 =
if (j =? 31)%nat then bks_c31 Bk else bv_unsigned (nth j Bk (Z_to_bv 8 0)).
Proof.
intros Bk j HL Hj.
rewrite (nth_indep (map bv_unsigned (RcFin.stamp32 Bk)) 0 (bv_unsigned (Z_to_bv 8 0)))
by (rewrite map_length, (bks_stamp_length Bk HL); lia).
rewrite (map_nth bv_unsigned (RcFin.stamp32 Bk) (Z_to_bv 8 0) j).
unfold RcFin.stamp32. rewrite (bks_nth_upd1 Bk 31 _ (Z_to_bv 8 0) j) by lia.
destruct (Nat.eqb_spec j 31) as [->|H31]; [|reflexivity].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold bks_c31. apply Z.mod_mod. lia.
Qed.

(* ---- the symbolic state at the first slot -------------------------------------------------------------- *)
(* atom 32 is the shadow offset, atoms 33 .. 64 are the block's bytes q[0 .. 32). *)
Definition BKS_SB : Z := 0x7fff8000.
Definition BKS_CB : sv := SOff 32 0.
Definition BKSspan : Z * Z := (BKS_SB, BKS_SB + 2 ^ 44 - 1).
Definition bks_chunks : list YP09.chunk :=
Eval vm_compute in (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0))) (seq 0 32)).
(* read window [0, 32), write window [31, 32): the contract lets the call write q + 31 only *)
Definition bks_block : YP09.region := YP09.mkRegion (Some 10%nat) 0 32 31 32 bks_chunks.
Definition bks_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; bks_block ].
Definition bks_batoms : list (nat * afact) :=
Eval vm_compute in (map (fun j => ((33 + j)%nat, mkAF 0 255 0)) (seq 0 32)).
(* atom 10 is q: 0 < q, and amem_range q 32 puts q + 32 below 2^47 - 1. *)
Definition bks_facts : facts :=
mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (10%nat, mkAF 1 (2 ^ 47 - 33) 0) ::
(32%nat, mkAF BKS_SB BKS_SB 0) :: bks_batoms) [] [].
Definition ss_bks : sstate := mkSS AF_reac_ctrl_block_cksum_stamp sr_atoms bks_regions None bks_facts.
Definition bks_SH : list shent := [ mkSHE 10 0 32 ].
Definition bks_extra (Bk : list byte) : list word :=
Z_to_bv 64 BKS_SB :: map (fun b => Z_to_bv 64 (bv_unsigned b)) Bk.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head stays a section variable, as in GrantBContracts.v: no sink_head instance is in lib/B's Require
   closure. *)
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition BKS_P : Z := BASE + AF_reac_ctrl_block_cksum_stamp.
Definition EBK (regs : bvmap 5 word) (Bk : list byte) : env := Eimg (Ereg regs (bks_extra Bk)).

Lemma bks_val_mem1_of_chunk : forall (Ez : env) (m : word -> option byte) (q off : Z) (e : sv) (z : Z),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk off (CVal 1 e)) -> sv_denot Ez e = Z_to_bv 64 z ->
YI04.val_mem SEGS m (q + off) 1%nat (z mod 256).
Proof.
intros Ez m q off e z Hc Hz kk Hk.
assert (Hk0 : kk = 0%nat) by lia. subst kk.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
rewrite !Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2. f_equal.
unfold YP09.byte_of_word. rewrite Hz, Z_to_bv_unsigned.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite !Z.shiftr_0_r. rewrite !Z.mod_mod by lia.
symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Lemma bks_aview_of_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.

(* garr8 of the stamped block from the final region's chunks: offsets 0..30 are the original bytes (atoms
   33..63), offset 31 is the stored stamp byte e31 whose value mod 256 is bks_c31. *)
Lemma bks_garr8_close : forall (Ez : env) (m : word -> option byte) (q : Z) (Bk : list byte) (e31 : sv),
length Bk = 32%nat ->
(forall j, (j < 31)%nat -> sv_denot Ez (SOff (33 + j)%nat 0) = Z_to_bv 64 (bv_unsigned (nth j Bk (Z_to_bv 8 0)))) ->
(forall j, (j < 31)%nat -> YP09.chunk_ok SEGS Ez m q (YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j)%nat 0)))) ->
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk 31 (CVal 1 e31)) ->
(U Ez e31) mod 256 = bks_c31 Bk ->
garr8 SEGS m q (map bv_unsigned (RcFin.stamp32 Bk)).
Proof.
intros Ez m q Bk e31 HL Hden Hchk H31 H31v jj Hjj.
rewrite map_length, (bks_stamp_length Bk HL) in Hjj.
rewrite (bks_nth Bk jj HL Hjj). destruct (Nat.eqb_spec jj 31) as [->|Hne].
- split; [| pose proof (bks_c31_range Bk); lia].
pose proof (bks_val_mem1_of_chunk Ez m q 31 e31 (U Ez e31) H31 (denot_lit_U Ez e31)) as Hv.
rewrite H31v in Hv. replace (q + Z.of_nat 31) with (q + 31) by (cbn; lia). exact Hv.
- assert (Hj : (jj < 31)%nat) by lia.
split; [| pose proof (bks_byte_range Bk jj); lia].
pose proof (bks_val_mem1_of_chunk Ez m q (Z.of_nat jj) (SOff (33 + jj)%nat 0)
(bv_unsigned (nth jj Bk (Z_to_bv 8 0))) (Hchk jj Hj) (Hden jj Hj)) as Hv.
rewrite (Z.mod_small (bv_unsigned (nth jj Bk (Z_to_bv 8 0))) 256) in Hv
by (pose proof (bks_byte_range Bk jj); lia).
exact Hv.
Qed.

Section H.
Variable B : asyms.

Lemma bks_entry : forall (LAWS : AR_laws SEGS B) (TL : PALib B)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (Bk : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 q ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_block_cksum_stamp -> spZ regs <= sp0 ->
length Bk = 32%nat -> garr8 SEGS (mrestrict (w_H W) memc) q (map bv_unsigned Bk) ->
0 < q -> amem_range q 32 -> (q + 32 <= IMG_LO_B \/ IMG_TOP_B <= q) ->
(spZ regs <= q \/ q + 32 <= spZ regs - STK_reac_ctrl_block_cksum_stamp) ->
apresent (w_H W) memc (q + 31) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 32 ->
st_ok_pi SEGS VAL (EBK regs Bk) ss_bks (restrict (w_H W) (mkst regs (Z_to_bv 64 BKS_P) memc (seg_rom SEGS)))
/\ sh_ok SEGS BKS_CB bks_SH (EBK regs Bk) (mrestrict (w_H W) memc).
Proof.
intros LAWS TL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q Bk
HJ H10 Hal16 Hwlo Hwhi HLB HGB Hq0 Hamem Himg Hpsp Hq31 HRA.
pose proof (pal_got_shadow B TL) as HBgot. pose proof (pal_cell B TL) as HBcell.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_ctrl_block_cksum_stamp = 16) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR, Himg.
assert (Hqhi : q + 32 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem; lia).
rewrite restrict_mkst_fx.
set (E := EBK regs Bk).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (bks_extra Bk)) n)
by (intros n Hn; subst E; unfold EBK; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 BKS_SB)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs (bks_extra Bk) 0)).
assert (Eb : forall j, (j < 32)%nat -> ew E (33 + j)%nat = Z_to_bv 64 (bv_unsigned (nth j Bk (Z_to_bv 8 0)))).
{ intros j Hj. replace (33 + j)%nat with (32 + (1 + j))%nat by lia.
rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs (bks_extra Bk) (1 + j)).
unfold bks_extra. replace (1 + j)%nat with (Datatypes.S j) by lia. cbn [nth].
rewrite (nth_indep (map (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk) (Z_to_bv 64 0)
(Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) by (rewrite map_length; lia).
rewrite (map_nth (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk (Z_to_bv 8 0) j). reflexivity. }
assert (Eb' : forall j, (33 <= j < 65)%nat -> ew E j = Z_to_bv 64 (bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0)))).
{ intros j Hj. pose proof (Eb (j - 33)%nat ltac:(lia)) as Hq.
replace (33 + (j - 33))%nat with j in Hq by lia. exact Hq. }
assert (Vb : forall j, (j < 32)%nat ->
YI04.val_mem SEGS (mrestrict (w_H W) memc) (q + Z.of_nat j) 1%nat (bv_unsigned (nth j Bk (Z_to_bv 8 0)))).
{ intros j Hj. destruct (HGB j ltac:(rewrite map_length; lia)) as [Hv _].
rewrite (nth_indep (map bv_unsigned Bk) 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by (rewrite map_length; lia).
rewrite (map_nth bv_unsigned Bk (Z_to_bv 8 0) j) in Hv. exact Hv. }
assert (Ub : forall j, (33 <= j < 65)%nat -> bv_unsigned (ew E j) = bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0))).
{ intros j Hj. rewrite (Eb' j Hj). apply unsigned_lit_small. pose proof (bks_byte_range Bk (j - 33)). lia. }
assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
by (change 242%nat with (A_OBJ 1); subst E; unfold EBK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
by (change 276%nat with (A_OBJ 35); subst E; unfold EBK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_bks, BKS_P. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold bks_regions, bks_block, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
[cbn [sv_denot]; change (A_OBJ 35) with 276%nat; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 BKS_CB BKS_SB);
[cbn [sv_denot BKS_CB]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold BKS_SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 10%nat q E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); replace (q + o) with (q + 31) by lia; exact Hq31|].
unfold bks_chunks. apply Forall_forall. intros c Hc. vm_compute in Hc.
repeat (destruct Hc as [<- | Hc]); [.. | exfalso; exact Hc];
(lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SOff ?n 0))) =>
apply (chunk_ok_val SEGS E _ q off 1 (SOff n 0) (bv_unsigned (nth (n - 33) Bk (Z_to_bv 8 0))));
[ cbn [sv_denot]; rewrite (Eb' n ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bks_byte_range Bk (n - 33)); zside | zside
| pose proof (Vb (n - 33)%nat ltac:(lia)) as Hvv; cbn [Nat.sub Z.of_nat] in Hvv;
first [ exact Hvv
| (replace (q + off) with (q + Z.of_nat (n - 33)) by (cbn [Nat.sub Z.of_nat]; lia)); exact Hvv
| (rewrite Z.add_0_r in Hvv); exact Hvv ] ] end).
+ apply pairwise_disjoint_of_extents.
unfold bks_regions, bks_block, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat q E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hsp46 HcellR HgcD HgotR Himg Hpsp Hq0 Hqhi C1 C3 WS Hstk0. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
unfold bks_facts, bks_batoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, !unsigned_lit_small by (unfold BKS_SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat (rewrite Ub by lia). cbn [Nat.sub].
pose proof (bks_byte_range Bk 0). pose proof (bks_byte_range Bk 1). pose proof (bks_byte_range Bk 2).
pose proof (bks_byte_range Bk 3). pose proof (bks_byte_range Bk 4). pose proof (bks_byte_range Bk 5).
pose proof (bks_byte_range Bk 6). pose proof (bks_byte_range Bk 7). pose proof (bks_byte_range Bk 8).
pose proof (bks_byte_range Bk 9). pose proof (bks_byte_range Bk 10). pose proof (bks_byte_range Bk 11).
pose proof (bks_byte_range Bk 12). pose proof (bks_byte_range Bk 13). pose proof (bks_byte_range Bk 14).
pose proof (bks_byte_range Bk 15). pose proof (bks_byte_range Bk 16). pose proof (bks_byte_range Bk 17).
pose proof (bks_byte_range Bk 18). pose proof (bks_byte_range Bk 19). pose proof (bks_byte_range Bk 20).
pose proof (bks_byte_range Bk 21). pose proof (bks_byte_range Bk 22). pose proof (bks_byte_range Bk 23).
pose proof (bks_byte_range Bk 24). pose proof (bks_byte_range Bk 25). pose proof (bks_byte_range Bk 26).
pose proof (bks_byte_range Bk 27). pose proof (bks_byte_range Bk 28). pose proof (bks_byte_range Bk 29).
pose proof (bks_byte_range Bk 30). pose proof (bks_byte_range Bk 31).
repeat match goal with |- _ /\ _ => split end; unfold BKS_SB in *; lia.
- unfold sh_ok, bks_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E BKS_CB 10%nat q 32 q 0 32 HRA).
+ unfold U, BKS_CB. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold BKS_SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. change (Z.min 0 32) with 0 in Hx. change (Z.max 0 32) with 32 in Hx.
unfold amem_range, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
Qed.

Theorem pb_reac_ctrl_block_cksum_stamp : walk_reac_ctrl_block_cksum_stamp B.
Proof.
unfold walk_reac_ctrl_block_cksum_stamp, hyps_reac_ctrl_block_cksum_stamp, RT_LAWS, RT_PALIB.
intros [LAWS TL].
unfold tb_reac_ctrl_block_cksum_stamp_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q Bk
HJ Hra Hra4 Hgp Htp H10 Hal16 Hwlo Hwhi HLB HGB Hq0 Hamem Himg Hpsp HWR HRA.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_ret_at (PL := PL_grant) (PI := PI)) as RET.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (WS : STK_reac_ctrl_block_cksum_stamp = 16) by reflexivity.
assert (Hq31 : apresent (w_H W) memc (q + 31)) by exact (proj1 (proj2 (HWR (q + 31) ltac:(lia)))).
destruct (bks_entry LAWS TL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q Bk
HJ H10 Hal16 Hwlo Hwhi HLB HGB Hq0 Hamem Himg Hpsp Hq31 HRA) as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hqhi : q + 32 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem; lia).
pose proof Himg as Himg'. rewrite IMG_LO_B_val, IMG_TOP_B_val in Himg'.
remember (EBK regs Bk) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EBK; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (bks_extra Bk)) n)
by (intros n Hn; subst E; unfold EBK; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Eb : forall j, (j < 32)%nat -> ew E (33 + j)%nat = Z_to_bv 64 (bv_unsigned (nth j Bk (Z_to_bv 8 0)))).
{ intros j Hj. replace (33 + j)%nat with (32 + (1 + j))%nat by lia.
rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs (bks_extra Bk) (1 + j)).
unfold bks_extra. replace (1 + j)%nat with (Datatypes.S j) by lia. cbn [nth].
rewrite (nth_indep (map (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk) (Z_to_bv 64 0)
(Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) by (rewrite map_length; lia).
rewrite (map_nth (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk (Z_to_bv 8 0) j). reflexivity. }
assert (Eb' : forall j, (33 <= j < 65)%nat -> ew E j = Z_to_bv 64 (bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0)))).
{ intros j Hj. pose proof (Eb (j - 33)%nat ltac:(lia)) as Hq.
replace (33 + (j - 33))%nat with j in Hq by lia. exact Hq. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (bks_extra Bk)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; unfold EBK; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_ctrl_block_cksum_stamp)) with (Z_to_bv 64 BKS_P).
(* The whole body in one run: frame, save of ra, shadow base through GOT + cell, the 31 loop passes (each byte's
   instrumented check and the trap guards decided inside the run), the fourth guard, the check of q + 31, the
   store of the negated sum's low byte, and the return. *)
paj_run_tok RUN HS HJ SHOK BKSspan;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sq ?fp ?b0 ?bc ?lyq ?ownq =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sq fp b0 bc lyq ownq) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite Usp; lia | cbn; lia | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat q);
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HWR aa ltac:(lia)))
| apply awr_ok_nil] |].
(* the store is done; the walk is at the return *)
lazymatch goal with HS : st_ok_pi _ _ ?Ez ?ssx (restrict (w_H ?Wq) ?msy), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
assert (Eb2 : forall j, (33 <= j < 65)%nat -> ew Ez j = Z_to_bv 64 (bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0))))
by (intros jq Hjq; rewrite ?ew_ewset_other by lia; apply Eb'; lia);
assert (Hbq : base_val Ez (Some 10%nat) = q)
by (cbn [base_val]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia);
assert (Hden : forall j, (j < 31)%nat -> sv_denot Ez (SOff (33 + j)%nat 0) = Z_to_bv 64 (bv_unsigned (nth j Bk (Z_to_bv 8 0))))
by (intros j Hj; rewrite denot_lit_U; f_equal; apply (U_atom Ez (33 + j)%nat (bv_unsigned (nth j Bk (Z_to_bv 8 0))));
[ rewrite (Eb2 (33 + j)%nat ltac:(lia)); replace (33 + j - 33)%nat with j by lia; reflexivity
| pose proof (bks_byte_range Bk j); lia ]);
pose proof (st_ok_pi_region_nth Ez ssx (restrict (w_H Wq) msy) 3%nat _ HS ltac:(vm_compute; reflexivity)) as HRfin;
cbn [restrict ms_mem] in HRfin;
destruct HRfin as (_ & _ & _ & HCH);
pose proof (Forall_inv HCH) as H31;
pose proof (Forall_inv_tail HCH) as Htl0;
assert (Htl : Forall (YP09.chunk_ok SEGS Ez (mrestrict (w_H Wq) (ms_mem msy)) (base_val Ez (Some 10%nat)))
(map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j)%nat 0))) (seq 0 31))) by exact Htl0;
assert (Hchk : forall j, (j < 31)%nat -> YP09.chunk_ok SEGS Ez (mrestrict (w_H Wq) (ms_mem msy)) (base_val Ez (Some 10%nat))
(YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j)%nat 0))))
by (intros j Hj; apply (proj1 (Forall_forall _ _) Htl); apply in_map_iff; exists j; split; [reflexivity | apply in_seq; lia]);
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mq := fresh "mat" in intros mq;
split; [reflexivity|];
exists (ms_regs msy), (ms_mem msy); eexists;
split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJz|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ez _ _ regs (bks_extra Bk) HS);
[ split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; apply (proj1 HAE); lia | cbn [ed ewset]; apply (proj2 HAE)]
| vm_compute; reflexivity ]|];
split;
[ rewrite <- Hbq; eapply (bks_garr8_close Ez (mrestrict (w_H Wq) (ms_mem msy)) (base_val Ez (Some 10%nat)) Bk _ HLB Hden Hchk H31);
repeat (rewrite U_SAlu; cbn [zalu_raw]); repeat (rewrite U_SMd; cbn [zmd_raw]); rewrite ?U_SLit;
rewrite (U_atom Ez 33%nat _ (Eb2 33%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 0); lia));
rewrite (U_atom Ez 34%nat _ (Eb2 34%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 1); lia));
rewrite (U_atom Ez 35%nat _ (Eb2 35%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 2); lia));
rewrite (U_atom Ez 36%nat _ (Eb2 36%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 3); lia));
rewrite (U_atom Ez 37%nat _ (Eb2 37%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 4); lia));
rewrite (U_atom Ez 38%nat _ (Eb2 38%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 5); lia));
rewrite (U_atom Ez 39%nat _ (Eb2 39%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 6); lia));
rewrite (U_atom Ez 40%nat _ (Eb2 40%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 7); lia));
rewrite (U_atom Ez 41%nat _ (Eb2 41%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 8); lia));
rewrite (U_atom Ez 42%nat _ (Eb2 42%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 9); lia));
rewrite (U_atom Ez 43%nat _ (Eb2 43%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 10); lia));
rewrite (U_atom Ez 44%nat _ (Eb2 44%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 11); lia));
rewrite (U_atom Ez 45%nat _ (Eb2 45%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 12); lia));
rewrite (U_atom Ez 46%nat _ (Eb2 46%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 13); lia));
rewrite (U_atom Ez 47%nat _ (Eb2 47%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 14); lia));
rewrite (U_atom Ez 48%nat _ (Eb2 48%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 15); lia));
rewrite (U_atom Ez 49%nat _ (Eb2 49%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 16); lia));
rewrite (U_atom Ez 50%nat _ (Eb2 50%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 17); lia));
rewrite (U_atom Ez 51%nat _ (Eb2 51%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 18); lia));
rewrite (U_atom Ez 52%nat _ (Eb2 52%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 19); lia));
rewrite (U_atom Ez 53%nat _ (Eb2 53%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 20); lia));
rewrite (U_atom Ez 54%nat _ (Eb2 54%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 21); lia));
rewrite (U_atom Ez 55%nat _ (Eb2 55%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 22); lia));
rewrite (U_atom Ez 56%nat _ (Eb2 56%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 23); lia));
rewrite (U_atom Ez 57%nat _ (Eb2 57%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 24); lia));
rewrite (U_atom Ez 58%nat _ (Eb2 58%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 25); lia));
rewrite (U_atom Ez 59%nat _ (Eb2 59%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 26); lia));
rewrite (U_atom Ez 60%nat _ (Eb2 60%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 27); lia));
rewrite (U_atom Ez 61%nat _ (Eb2 61%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 28); lia));
rewrite (U_atom Ez 62%nat _ (Eb2 62%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 29); lia));
rewrite (U_atom Ez 63%nat _ (Eb2 63%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (bks_byte_range Bk 30); lia));
bks_zc_flat; unfold bks_c31; cbn [RcModel.psum Nat.sub]; bks_kill256; lia |];
let HM := fresh "HM" in
assert (HM : forall xx : word, ~ (spZ regs - STK_reac_ctrl_block_cksum_stamp <= bv_unsigned xx < spZ regs) ->
~ (q + 31 <= bv_unsigned xx < q + 32) -> mrestrict (w_H Wq) (ms_mem msy) xx = mrestrict (w_H Wq) memc xx);
[ intros xx HA HB; apply HFr; intros Hin; destruct Hin as (rr & Hrr & Hbb);
let l := eval vm_compute in (ss_mem ss_bks) in change (ss_mem ss_bks) with l in Hrr;
cbn [In] in Hrr; repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hbb;
rewrite ?Usp, ?E10 in Hbb; rewrite ?unsigned_lit_small in Hbb by lia; lia
| ];
unfold tcj_kept;
split;
[ intros aa Haa Hww Hee; apply bks_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros bb mm ii Hinb Hii Hee;
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb mm HAR Hinb) as (_ & Hb4096 & Hbceil & _);
apply bks_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros aa Hini _ _; pose proof (pa_img_range aa Hini) as Hir; rewrite IMG_LO_B_val, IMG_TOP_B_val in Hir;
apply bks_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros cid pos aa Hinf Hrr Hee;
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hinf) as (Hf0 & Hfc & _);
pose proof (fs_frame_bytes_nonneg cid) as Hfb;
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hs1;
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2;
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hs3;
unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
apply bks_aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; destruct Hrr as [Hrr|Hrr]; lia |];
split;
[ intros aa _ _ Hpr; exact (apresent_grows (w_H Wq) memc (ms_mem msy) aa HG Hpr) |];
intros aa Haa;
pose proof HJz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _);
apply Hpres2; lia
end.
Qed.

End H.
End F.
End D.
