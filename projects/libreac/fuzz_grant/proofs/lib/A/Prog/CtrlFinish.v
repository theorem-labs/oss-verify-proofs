(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_finish on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/YC20.v. *)
(* ctrl_finish (0x8339c) on fuzz_grant's ASan build: the call closes a control
   block. It reads three bytes of the static control-frame row (rec_off,
   rec_len, cksum at A_OBJ 18 + 18..20), sums the record it names and stamps the
   record's INNER checksum, then sums the block's first 31 bytes and stamps the
   OUTER checksum. The values are RcFin.fin of Pau's address-free model.

   The 32 bytes it reads and writes belong to the caller (reac_ctrl_stamp_headamp
   hands it reac_ctrl_build_grant_sweep's machine-stack scratch), so the contract
   is in cgif's caller-journal form (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365):
   the premise is the caller's journal, the right to write those bytes is a
   premise the caller supplies per byte, and the post extends the same journal.

   tcj_kept, twr_ok and tsrc_ok are this slice's shared shapes; the walks of
   ctrl_lay_block, reac_ctrl_stamp_headamp and reac_ctrl_build_grant_sweep take
   them from here. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RcFin RcModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma land127 : forall x, 0 <= x -> Z.land x 127 = x mod 128.
Proof. intros x Hx. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma zcanon_nonneg : forall x, 0 <= zcanon x.
Proof. intros x. unfold zcanon, M64. apply Z.mod_pos_bound. lia. Qed.
Lemma zc_add_l : forall x y, zcanon (zcanon x + y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. apply Z.add_mod_idemp_l. lia. Qed.
Lemma zc_add_r : forall x y, zcanon (x + zcanon y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. apply Z.add_mod_idemp_r. lia. Qed.
Lemma zc_sub_l : forall x y, zcanon (zcanon x - y) = zcanon (x - y).
Proof. intros x y. unfold zcanon, M64. apply Zminus_mod_idemp_l. Qed.
Lemma zc_sub_r : forall x y, zcanon (x - zcanon y) = zcanon (x - y).
Proof. intros x y. unfold zcanon, M64. apply Zminus_mod_idemp_r. Qed.
Lemma zc_mul_m1 : forall b, zcanon (b * zcanon (-1)) = zcanon (- b).
Proof.
intros b. unfold zcanon, M64. rewrite Z.mul_mod_idemp_r by lia. f_equal. ring.
Qed.
Lemma zc_mod128 : forall x, zcanon x mod 128 = x mod 128.
Proof.
intros x. unfold zcanon, M64. symmetry.
apply Zmod_div_mod; [lia | lia | exists (2 ^ 57); reflexivity].
Qed.
Lemma zc_mod256 : forall x, zcanon x mod 256 = x mod 256.
Proof.
intros x. unfold zcanon, M64. symmetry.
apply Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Lemma mod128_256 : forall x, (x mod 128) mod 256 = x mod 128.
Proof. intros x. apply Z.mod_small. pose proof (Z.mod_pos_bound x 128 ltac:(lia)). lia. Qed.
Ltac zc_flat := rewrite ?zc_mul_m1; repeat (rewrite ?zc_add_l, ?zc_add_r, ?zc_sub_l, ?zc_sub_r).
Lemma zc_split128 : forall x, exists k, x mod 18446744073709551616 = x + 128 * k.
Proof.
intros x. exists (- (x / 18446744073709551616) * 144115188075855872).
pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)). lia.
Qed.
Ltac kill64 := repeat match goal with
| |- context [?t mod 18446744073709551616] =>
let kq := fresh "kq" in let Hkq := fresh "Hkq" in
destruct (zc_split128 t) as [kq Hkq]; rewrite Hkq; clear Hkq
end.
Lemma zc_split256 : forall x, exists k, x mod 18446744073709551616 = x + 256 * k.
Proof.
intros x. exists (- (x / 18446744073709551616) * 72057594037927936).
pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)). lia.
Qed.
Ltac kill256 := repeat match goal with
| |- context [?t mod 18446744073709551616] =>
let kr := fresh "kr" in let Hkr := fresh "Hkr" in
destruct (zc_split256 t) as [kr Hkr]; rewrite Hkr; clear Hkr
end.
Ltac lits_a :=
change (2 ^ 64) with 18446744073709551616 in *; change (2 ^ 32) with 4294967296 in *;
change (2 ^ 31) with 2147483648 in *; change (2 ^ 63) with 9223372036854775808 in *.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* CTRL_FRAMES[CTRL_HEADAMP], 0x9c670, 24 bytes: the row this program passes. *)
Definition A_ROW : nat := 18%nat.
Definition SB : Z := 0x7fff8000.
(* Its own frame is 16 bytes; it calls nothing but the error path, and ESTACK is
   what the memory-checking runtime uses below sp. *)
Definition TCF_STK : Z := 16 + ESTACK.
Definition EV_CF : Z := 0.
Section e.
Variable B : asyms.
(* ---- the shape a call of this slice leaves ------------------------------- *)
(* What a call keeps: everything but its own stack window and the bytes E it is
   allowed to write (cgif lib/YC20.v:311-323). *)
Definition tcj_kept (STK : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(W2 : world SEGS) (mem2 : word -> option byte) (sp : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ E a ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - STK <= a < sp -> apresent (w_H W2) mem2 a).
(* The caller's right to let the call write [q, q + n): the byte is one the
   caller's own journal may change (cgif lib/YC20.v:358-359), it is there, it is
   not the memory-checking runtime's own, and it is not in the stack the
   runtime's wrappers use below sp. *)
Definition twr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS) (memc : word -> option byte)
(sp q n : Z) : Prop :=
forall a, q <= a < q + n ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp).
(* A range the call reads. *)
Definition tsrc_ok (W : world SEGS) (memc : word -> option byte) (sp q n : Z) : Prop :=
(forall a, q <= a < q + n -> aview SEGS (w_H W) memc a <> None /\ ~ (sp - ESTACK <= a < sp)) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q n /\
shadow_hull_vis (aview SEGS (w_H W) memc) q n /\ amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.
Lemma val_mem1_of_chunk : forall (Ez : env) (m : word -> option byte) (q off : Z) (e : sv) (z : Z),
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
Lemma aview_of_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.
Lemma nth_upd1 : forall (l : list byte) (kk : nat) (b d : byte) (j : nat),
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
Definition cf_c21 (Bk : list byte) : Z := (- RcFin.rsum Bk 16 5) mod 128.
Definition cf_B1 (Bk : list byte) : list byte := Mem.upd_bytes Bk 21 [Z_to_bv 8 (cf_c21 Bk)].
Definition cf_c31 (Bk : list byte) : Z := (- RcModel.psum (cf_B1 Bk) 31) mod 256.
Lemma nth_skipn_l : forall (l : list byte) (n kk : nat) (d : byte), nth kk (skipn n l) d = nth (n + kk) l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l kk d; [reflexivity|].
destruct l as [|x l]; cbn [skipn nth Nat.add]; [destruct kk; reflexivity | apply IH].
Qed.
Lemma cf_rsum : forall Bk, RcFin.rsum Bk 16 5 =
bv_unsigned (nth 16 Bk (Z_to_bv 8 0)) + bv_unsigned (nth 17 Bk (Z_to_bv 8 0)) +
bv_unsigned (nth 18 Bk (Z_to_bv 8 0)) + bv_unsigned (nth 19 Bk (Z_to_bv 8 0)) +
bv_unsigned (nth 20 Bk (Z_to_bv 8 0)).
Proof.
intros Bk. unfold RcFin.rsum. change (Z.to_nat 16) with 16%nat. change (Z.to_nat 5) with 5%nat.
cbn [RcModel.psum]. rewrite !nth_skipn_l. cbn [Nat.add]. lia.
Qed.
Lemma cf_c21_range : forall Bk, 0 <= cf_c21 Bk < 128.
Proof. intros Bk. unfold cf_c21. apply Z.mod_pos_bound. lia. Qed.
Lemma cf_c31_range : forall Bk, 0 <= cf_c31 Bk < 256.
Proof. intros Bk. unfold cf_c31. apply Z.mod_pos_bound. lia. Qed.
Lemma cf_B1_length : forall Bk, length Bk = 32%nat -> length (cf_B1 Bk) = 32%nat.
Proof. intros Bk HL. unfold cf_B1. rewrite Mem.upd_bytes_length by (cbn [length]; lia). exact HL. Qed.
Lemma cf_fin_nth : forall (Bk : list byte) (j : nat), length Bk = 32%nat -> (j < 32)%nat ->
nth j (RcFin.fin 2 16 6 Bk) (Z_to_bv 8 0) =
if (j =? 31)%nat then Z_to_bv 8 (cf_c31 Bk)
else if (j =? 21)%nat then Z_to_bv 8 (cf_c21 Bk) else nth j Bk (Z_to_bv 8 0).
Proof.
intros Bk j HL Hj.
unfold RcFin.fin, RcFin.stamp32, RcFin.rstamp, cf_c31, cf_B1, cf_c21. cbn [Z.eqb Pos.eqb].
change (Z.to_nat (16 + 6 - 1)) with 21%nat. change (6 - 1) with 5.
assert (HB1 : length (Mem.upd_bytes Bk 21 [Z_to_bv 8 ((- RcFin.rsum Bk 16 5) mod 128)]) = 32%nat)
by (rewrite Mem.upd_bytes_length by (cbn [length]; lia); exact HL).
rewrite (nth_upd1 _ 31 _ (Z_to_bv 8 0) j) by (rewrite HB1; lia).
destruct (Nat.eqb_spec j 31) as [->|Hne]; [reflexivity|].
rewrite (nth_upd1 Bk 21 _ (Z_to_bv 8 0) j) by lia. reflexivity.
Qed.
Lemma cf_fin_length : forall Bk, length Bk = 32%nat -> length (RcFin.fin 2 16 6 Bk) = 32%nat.
Proof.
intros Bk HL. unfold RcFin.fin. cbn [Z.eqb Pos.eqb]. unfold RcFin.stamp32, RcFin.rstamp.
rewrite Mem.upd_bytes_length; [rewrite Mem.upd_bytes_length; [exact HL | cbn [length]; lia]|].
cbn [length]. rewrite Mem.upd_bytes_length; [lia | cbn [length]; lia].
Qed.
Lemma cf_nth : forall (Bk : list byte) (j : nat), length Bk = 32%nat -> (j < 32)%nat ->
nth j (map bv_unsigned (RcFin.fin 2 16 6 Bk)) 0 =
if (j =? 31)%nat then cf_c31 Bk
else if (j =? 21)%nat then cf_c21 Bk else bv_unsigned (nth j Bk (Z_to_bv 8 0)).
Proof.
intros Bk j HL Hj.
assert (HF : length (RcFin.fin 2 16 6 Bk) = 32%nat).
{ unfold RcFin.fin. cbn [Z.eqb Pos.eqb]. unfold RcFin.stamp32, RcFin.rstamp.
rewrite Mem.upd_bytes_length; [rewrite Mem.upd_bytes_length; [exact HL | cbn [length]; lia]|].
cbn [length]. rewrite Mem.upd_bytes_length; [lia | cbn [length]; lia]. }
rewrite (nth_indep (map bv_unsigned (RcFin.fin 2 16 6 Bk)) 0 (bv_unsigned (Z_to_bv 8 0)))
by (rewrite map_length, HF; lia).
rewrite (map_nth bv_unsigned (RcFin.fin 2 16 6 Bk) (Z_to_bv 8 0) j).
rewrite (cf_fin_nth Bk j HL Hj).
destruct (Nat.eqb_spec j 31) as [->|H31];
[rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
pose proof (cf_c31_range Bk); apply Z.mod_small; lia|].
destruct (Nat.eqb_spec j 21) as [->|H21]; [|reflexivity].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
pose proof (cf_c21_range Bk). apply Z.mod_small. lia.
Qed.
Lemma cf_psum_B1 : forall Bk, length Bk = 32%nat ->
RcModel.psum (cf_B1 Bk) 31 = RcModel.psum Bk 31 - bv_unsigned (nth 21 Bk (Z_to_bv 8 0)) + cf_c21 Bk.
Proof.
intros Bk HL. unfold cf_B1.
cbn [RcModel.psum].
rewrite !(nth_upd1 Bk 21 (Z_to_bv 8 (cf_c21 Bk)) (Z_to_bv 8 0)) by lia.
cbn [Nat.eqb].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
pose proof (cf_c21_range Bk). rewrite (Z.mod_small (cf_c21 Bk) 256) by lia. lia.
Qed.
(* ---- the contract -------------------------------------------------------- *)
Definition tctrl_finish_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (p : Z) (Bk : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 (k + EV_CF) /\
aregs_preserved regs regs2 /\
garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18) (map bv_unsigned (RcFin.fin 2 16 6 Bk)) /\
tcj_kept TCF_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 18 <= a < p + 50).
Definition tctrl_finish_spec (a : Z) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p : Z) (Bk : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS rlo rhi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 p -> getr regs 11 = w64 (VAL (A_OBJ A_ROW)) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TCF_STK -> spZ regs <= sp0 ->
(* the row it reads: rec_off 16, rec_len 6, cksum 2 (CKSUM_RECORD) *)
garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_ROW) + 18) [16; 6; 2] ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ A_ROW) + 18) 3 ->
(* the caller's 32-byte control block at p + 18 *)
length Bk = 32%nat ->
garr8 SEGS (mrestrict (w_H W) memc) (p + 18) (map bv_unsigned Bk) ->
0 <= p -> p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 18) 32 ->
(forall x, p + 18 <= x < p + 50 -> ~ in_img SEGS x) ->
twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
(* the bytes are clear of the stack this call and the runtime's wrappers use *)
(spZ regs <= p + 18 \/ p + 50 <= spZ regs - TCF_STK) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
shadow_hull_vis (aview SEGS (w_H W) memc) (p + 18) 32 ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(tctrl_finish_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p Bk).
(* ---- the walk ------------------------------------------------------------ *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
(* Facts of the image alone: the GOT word of the shadow-base cell (object 1, in
   .got), the cell (object 32, a .bss cell: the last loaded segment's memory size
   covers .bss, so the cell is in the image but not in the read-only range) and
   the control-frame row are in the image, and the row is apart from the other
   two. GrantClose.v proves them at PI_grant from the segment list:
   grant_cf_gotimg, grant_cf_celimg, grant_cf_rowimg, grant_cf_rowsep. *)
Hypothesis HGOTimg : forall a, VAL (A_OBJ 1) <= a < VAL (A_OBJ 1) + 8 -> in_img SEGS a.
Hypothesis HCELimg : forall a, VAL (A_OBJ 32) <= a < VAL (A_OBJ 32) + 8 -> in_img SEGS a.
Hypothesis HROWimg : forall a, VAL (A_OBJ A_ROW) + 18 <= a < VAL (A_OBJ A_ROW) + 18 + 3 -> in_img SEGS a.
Hypothesis HROWsep :
(VAL (A_OBJ A_ROW) + 21 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ A_ROW) + 18) /\
(VAL (A_OBJ A_ROW) + 21 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= VAL (A_OBJ A_ROW) + 18).
Definition Bxc : sv := SOff 32 0.
Definition cf_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cf_chunks : list YP09.chunk :=
Eval vm_compute in (map (fun j => YP09.mkChunk (18 + Z.of_nat j) (CVal 1 (SOff (33 + j) 0))) (seq 0 32)).
Definition cf_block : YP09.region := YP09.mkRegion (Some 10%nat) 18 50 18 50 cf_chunks.
Definition cf_row : YP09.region :=
YP09.mkRegion (Some 11%nat) 18 21 0 0
[YP09.mkChunk 18 (CVal 1 (SLit 16)); YP09.mkChunk 19 (CVal 1 (SLit 6)); YP09.mkChunk 20 (CVal 1 (SLit 2))].
Definition cf_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; cf_row; cf_block ].
Definition cf_batoms : list (nat * afact) :=
Eval vm_compute in (map (fun j => ((33 + j)%nat, mkAF 0 255 0)) (seq 0 32)).
Definition cf_facts : facts :=
mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (10%nat, mkAF 0 (2 ^ 47 - 58) 0) ::
(32%nat, mkAF SB SB 0) :: (11%nat, mkAF IMG_LO IMG_TOP 0) :: cf_batoms) [] [].
Definition ss_cf : sstate := mkSS AF_ctrl_finish sr_atoms cf_regions None cf_facts.
Definition cf_SH : list shent := [ mkSHE 10 18 50; mkSHE 11 18 21 ].
Definition cf_extra (Bk : list byte) : list word :=
Z_to_bv 64 SB :: map (fun b => Z_to_bv 64 (bv_unsigned b)) Bk.
Definition EC (regs : bvmap 5 word) (Bk : list byte) : env := Eimg (Ereg regs (cf_extra Bk)).
Lemma cf_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p : Z) (Bk : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 p -> getr regs 11 = w64 (VAL (A_OBJ A_ROW)) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TCF_STK -> spZ regs <= sp0 ->
garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_ROW) + 18) [16; 6; 2] ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ A_ROW) + 18) 3 ->
length Bk = 32%nat ->
garr8 SEGS (mrestrict (w_H W) memc) (p + 18) (map bv_unsigned Bk) ->
0 <= p -> p + 50 <= 2 ^ 47 - 8 ->
(forall x, p + 18 <= x < p + 50 -> ~ in_img SEGS x) ->
(forall a, p + 18 <= a < p + 50 -> apresent (w_H W) memc a) ->
(spZ regs <= p + 18 \/ p + 50 <= spZ regs - TCF_STK) ->
amem_range (p + 18) 32 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
st_ok_pi SEGS VAL (EC regs Bk) ss_cf
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ctrl_finish)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxc cf_SH (EC regs Bk) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p Bk
HJ H10 H11 Hal16 Hwlo Hwhi HROW HRAR HLB HGB Hp0 Hphi Himg Hppr Hpsp0 Hamem HRA.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCF_STK = 4112) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 32%nat ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR. pose proof (pa_obj_img A_ROW ltac:(unfold A_ROW; lia)) as HrowR.
pose proof pa_B_ok as HBASE.
rewrite restrict_mkst_fx.
set (E := EC regs Bk).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cf_extra Bk)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (VAL (A_OBJ A_ROW))) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs (cf_extra Bk) 0)).
assert (Eb : forall j, (j < 32)%nat -> ew E (33 + j)%nat = Z_to_bv 64 (bv_unsigned (nth j Bk (Z_to_bv 8 0)))).
{ intros j Hj. replace (33 + j)%nat with (32 + (1 + j))%nat by lia.
rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs (cf_extra Bk) (1 + j)).
unfold cf_extra. replace (1 + j)%nat with (Datatypes.S j) by lia. cbn [nth].
rewrite (nth_indep (map (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk) (Z_to_bv 64 0)
(Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) by (rewrite map_length; lia).
rewrite (map_nth (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk (Z_to_bv 8 0) j). reflexivity. }
assert (Eb' : forall j, (33 <= j < 65)%nat -> ew E j = Z_to_bv 64 (bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0)))).
{ intros j Hj. pose proof (Eb (j - 33)%nat ltac:(lia)) as Hq.
replace (33 + (j - 33))%nat with j in Hq by lia. exact Hq. }
assert (Vb : forall j, (j < 32)%nat ->
YI04.val_mem SEGS (mrestrict (w_H W) memc) (p + 18 + Z.of_nat j) 1%nat (bv_unsigned (nth j Bk (Z_to_bv 8 0)))).
{ intros j Hj. destruct (HGB j ltac:(rewrite map_length; lia)) as [Hv _].
rewrite (nth_indep (map bv_unsigned Bk) 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by (rewrite map_length; lia).
rewrite (map_nth bv_unsigned Bk (Z_to_bv 8 0) j) in Hv. exact Hv. }
assert (Rb : forall j, (j < 32)%nat -> 0 <= bv_unsigned (nth j Bk (Z_to_bv 8 0)) < 256).
{ intros j Hj. pose proof (bv_unsigned_in_range 8 (nth j Bk (Z_to_bv 8 0))) as Hr.
unfold bv_modulus in Hr. cbn in Hr. lia. }
assert (Ub : forall j, (33 <= j < 65)%nat -> bv_unsigned (ew E j) = bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0))).
{ intros j Hj. rewrite (Eb' j Hj). apply unsigned_lit_small.
pose proof (Rb (j - 33)%nat ltac:(lia)). lia. }
destruct (HROW 0%nat ltac:(cbn; lia)) as [Mr0 _]. destruct (HROW 1%nat ltac:(cbn; lia)) as [Mr1 _].
destruct (HROW 2%nat ltac:(cbn; lia)) as [Mr2 _]. cbn [nth] in Mr0, Mr1, Mr2.
change (Z.of_nat 0) with 0 in Mr0. change (Z.of_nat 1) with 1 in Mr1. change (Z.of_nat 2) with 2 in Mr2.
rewrite Z.add_0_r in Mr0.
replace (VAL (A_OBJ A_ROW) + 18 + 1) with (VAL (A_OBJ A_ROW) + 19) in Mr1 by lia.
replace (VAL (A_OBJ A_ROW) + 18 + 2) with (VAL (A_OBJ A_ROW) + 20) in Mr2 by lia.
assert (E1g : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E32g : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hgap : forall q n, (forall a, q <= a < q + n -> in_img SEGS a) -> 0 < n ->
p + 50 <= q \/ q + n <= p + 18).
{ intros q n Hq Hn.
destruct (Z.le_gt_cases (p + 50) q) as [Hle|Hgt]; [left; exact Hle|]. right.
destruct (Z.le_gt_cases (q + n) (p + 18)) as [Hle2|Hgt2]; [exact Hle2|].
exfalso. apply (Himg (Z.max (p + 18) q)); [lia|]. apply Hq. lia. }
assert (Hpg1 : p + 50 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= p + 18)
by (apply (Hgap (VAL (A_OBJ 1)) 8 HGOTimg); lia).
assert (Hpg32 : p + 50 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= p + 18)
by (apply (Hgap (VAL (A_OBJ 32)) 8 HCELimg); lia).
assert (Hprow : p + 50 <= VAL (A_OBJ A_ROW) + 18 \/ VAL (A_OBJ A_ROW) + 21 <= p + 18)
by (pose proof (Hgap (VAL (A_OBJ A_ROW) + 18) 3 HROWimg ltac:(lia)); lia).
assert (Hpsp : p + 50 <= spZ regs - 16 \/ spZ regs <= p + 18) by (unfold TCF_STK, ESTACK in Hpsp0; lia).
destruct HROWsep as [Hrs1 Hrs2].
split.
- unfold ss_cf. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cf_regions, cf_block, cf_row, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E32g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E32g) by (pose proof (pa_val_range (A_OBJ 32)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 Bxc SB);
[cbn [sv_denot Bxc]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 11%nat (VAL (A_OBJ A_ROW)) E11) by (pose proof (pa_val_range (A_OBJ A_ROW)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ A_ROW)) 18 1 (SLit 16) 16);
[reflexivity | zside | zside | exact Mr0].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ A_ROW)) 19 1 (SLit 6) 6);
[reflexivity | zside | zside | exact Mr1].
-- apply (chunk_ok_val SEGS E _ (VAL (A_OBJ A_ROW)) 20 1 (SLit 2) 2);
[reflexivity | zside | zside | exact Mr2].
* rewrite (VB 10%nat p E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply Hppr; lia|].
unfold cf_chunks. apply Forall_forall. intros c Hc. vm_compute in Hc.
repeat (destruct Hc as [<- | Hc]); [.. | exfalso; exact Hc];
(lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SOff ?n 0))) =>
apply (chunk_ok_val SEGS E _ p off 1 (SOff n 0) (bv_unsigned (nth (n - 33) Bk (Z_to_bv 8 0))));
[ cbn [sv_denot]; rewrite (Eb' n ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Rb (n - 33)%nat ltac:(lia)); zside | zside
| pose proof (Vb (n - 33)%nat ltac:(lia)) as Hvv; cbn [Nat.sub Z.of_nat] in Hvv;
(replace (p + off) with (p + 18 + Z.of_nat (n - 33)) by (cbn [Nat.sub]; lia)); exact Hvv ] end).
+ apply pairwise_disjoint_of_extents.
unfold cf_regions, cf_block, cf_row, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat p E10) by lia.
rewrite (VB 11%nat (VAL (A_OBJ A_ROW)) E11) by (pose proof (pa_val_range (A_OBJ A_ROW)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E32g) by (pose proof (pa_val_range (A_OBJ 32)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hsp46 HcellR HgcD HgotR HrowR Hpg1 Hpg32 Hprow Hpsp Hrs1 Hrs2
Hp0 Hphi C1 C3 WS Hstk0. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
unfold cf_facts, cf_batoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SB; pose proof (pa_val_range (A_OBJ A_ROW)); lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite (Ub 33%nat ltac:(lia)). rewrite (Ub 34%nat ltac:(lia)). rewrite (Ub 35%nat ltac:(lia)). rewrite (Ub 36%nat ltac:(lia)). rewrite (Ub 37%nat ltac:(lia)). rewrite (Ub 38%nat ltac:(lia)). rewrite (Ub 39%nat ltac:(lia)). rewrite (Ub 40%nat ltac:(lia)). rewrite (Ub 41%nat ltac:(lia)). rewrite (Ub 42%nat ltac:(lia)). rewrite (Ub 43%nat ltac:(lia)). rewrite (Ub 44%nat ltac:(lia)). rewrite (Ub 45%nat ltac:(lia)). rewrite (Ub 46%nat ltac:(lia)). rewrite (Ub 47%nat ltac:(lia)). rewrite (Ub 48%nat ltac:(lia)). rewrite (Ub 49%nat ltac:(lia)). rewrite (Ub 50%nat ltac:(lia)). rewrite (Ub 51%nat ltac:(lia)). rewrite (Ub 52%nat ltac:(lia)). rewrite (Ub 53%nat ltac:(lia)). rewrite (Ub 54%nat ltac:(lia)). rewrite (Ub 55%nat ltac:(lia)). rewrite (Ub 56%nat ltac:(lia)). rewrite (Ub 57%nat ltac:(lia)). rewrite (Ub 58%nat ltac:(lia)). rewrite (Ub 59%nat ltac:(lia)). rewrite (Ub 60%nat ltac:(lia)). rewrite (Ub 61%nat ltac:(lia)). rewrite (Ub 62%nat ltac:(lia)). rewrite (Ub 63%nat ltac:(lia)). rewrite (Ub 64%nat ltac:(lia)).
cbn [Nat.sub].
pose proof (Rb 0%nat ltac:(lia)). pose proof (Rb 1%nat ltac:(lia)). pose proof (Rb 2%nat ltac:(lia)). pose proof (Rb 3%nat ltac:(lia)). pose proof (Rb 4%nat ltac:(lia)). pose proof (Rb 5%nat ltac:(lia)). pose proof (Rb 6%nat ltac:(lia)). pose proof (Rb 7%nat ltac:(lia)). pose proof (Rb 8%nat ltac:(lia)). pose proof (Rb 9%nat ltac:(lia)). pose proof (Rb 10%nat ltac:(lia)). pose proof (Rb 11%nat ltac:(lia)). pose proof (Rb 12%nat ltac:(lia)). pose proof (Rb 13%nat ltac:(lia)). pose proof (Rb 14%nat ltac:(lia)). pose proof (Rb 15%nat ltac:(lia)). pose proof (Rb 16%nat ltac:(lia)). pose proof (Rb 17%nat ltac:(lia)). pose proof (Rb 18%nat ltac:(lia)). pose proof (Rb 19%nat ltac:(lia)). pose proof (Rb 20%nat ltac:(lia)). pose proof (Rb 21%nat ltac:(lia)). pose proof (Rb 22%nat ltac:(lia)). pose proof (Rb 23%nat ltac:(lia)). pose proof (Rb 24%nat ltac:(lia)). pose proof (Rb 25%nat ltac:(lia)). pose proof (Rb 26%nat ltac:(lia)). pose proof (Rb 27%nat ltac:(lia)). pose proof (Rb 28%nat ltac:(lia)). pose proof (Rb 29%nat ltac:(lia)). pose proof (Rb 30%nat ltac:(lia)). pose proof (Rb 31%nat ltac:(lia)).
repeat match goal with |- _ /\ _ => split end; unfold SB in *; lia.
- unfold sh_ok, cf_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_range SEGS (w_H W) memc E Bxc 10%nat (p + 18) 32 p 18 50 HRA).
* unfold U, Bxc. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* lia.
* intros x Hx. change (Z.min 18 50) with 18 in Hx. change (Z.max 18 50) with 50 in Hx.
unfold amem_range, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
+ apply (shent_ok_of_range SEGS (w_H W) memc E Bxc 11%nat (VAL (A_OBJ A_ROW) + 18) 3 (VAL (A_OBJ A_ROW)) 18 21 HRAR).
* unfold U, Bxc. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
* unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (pose proof (pa_val_range (A_OBJ A_ROW)); lia). reflexivity.
* lia.
* lia.
* intros x Hx. change (Z.min 18 21) with 18 in Hx. change (Z.max 18 21) with 21 in Hx.
unfold SHADOW_OFF. lia.
Qed.
Theorem pb_ctrl_finish : tctrl_finish_spec (BASE + AF_ctrl_finish) pa_relro_lo pa_relro_hi.
Proof.
unfold tctrl_finish_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p Bk
HJ HROD Hra Hra4 Hgp Htp H10 H11 Hal16 Hwlo Hwhi HROW HRAR HLB HGB Hp0 Hphi Hamem Himg HWR HPSP HRA HHULL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (WS : TCF_STK = 4112) by reflexivity.
assert (Rb : forall j, (j < 32)%nat -> 0 <= bv_unsigned (nth j Bk (Z_to_bv 8 0)) < 256).
{ intros j Hj. pose proof (bv_unsigned_in_range 8 (nth j Bk (Z_to_bv 8 0))) as Hr.
unfold bv_modulus in Hr. cbn in Hr. lia. }
assert (Hppr : forall a, p + 18 <= a < p + 50 -> apresent (w_H W) memc a)
by (intros a Ha; exact (proj1 (proj2 (HWR a ltac:(lia))))).
destruct (cf_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p Bk
HJ H10 H11 Hal16 Hwlo Hwhi HROW HRAR HLB HGB Hp0 Hphi Himg Hppr HPSP Hamem HRA) as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
remember (EC regs Bk) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cf_extra Bk)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Eb : forall j, (j < 32)%nat -> ew E (33 + j)%nat = Z_to_bv 64 (bv_unsigned (nth j Bk (Z_to_bv 8 0)))).
{ intros j Hj. replace (33 + j)%nat with (32 + (1 + j))%nat by lia.
rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs (cf_extra Bk) (1 + j)).
unfold cf_extra. replace (1 + j)%nat with (Datatypes.S j) by lia. cbn [nth].
rewrite (nth_indep (map (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk) (Z_to_bv 64 0)
(Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) by (rewrite map_length; lia).
rewrite (map_nth (fun b : byte => Z_to_bv 64 (bv_unsigned b)) Bk (Z_to_bv 8 0) j). reflexivity. }
assert (Eb' : forall j, (33 <= j < 65)%nat -> ew E j = Z_to_bv 64 (bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0)))).
{ intros j Hj. pose proof (Eb (j - 33)%nat ltac:(lia)) as Hq.
replace (33 + (j - 33))%nat with j in Hq by lia. exact Hq. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cf_extra Bk)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; unfold EC; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_ctrl_finish)) with (Z_to_bv 64 (BASE + AF_ctrl_finish)).
paj_run_tok RUN HS HJ SHOK cf_span;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sq ?fp ?b0 ?bc ?lyq ?ownq =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sq fp b0 bc lyq ownq) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite Usp; lia | cbn; lia | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat p);
[reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HWR aa ltac:(lia)))
| apply awr_ok_nil] |].
lazymatch goal with HSz : st_ok_pi _ _ ?Ez ?ssx (restrict ?Hh ?msy), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
assert (Eb2 : forall j, (33 <= j < 65)%nat -> ew Ez j = Z_to_bv 64 (bv_unsigned (nth (j - 33) Bk (Z_to_bv 8 0))))
by (intros jq Hjq; rewrite ?ew_ewset_other by lia; apply Eb'; lia);
assert (Hb10 : base_val Ez (Some 10%nat) = p)
by (cbn [base_val]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia);
pose proof (st_ok_mem_ok SEGS Ez (abs_ss VAL ssx) (restrict Hh msy) HSz) as HMO;
cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
destruct HMO as (_ & HMO & _);
let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
apply Forall_inv_tail in HMO; apply Forall_inv_tail in HMO; apply Forall_inv_tail in HMO;
apply Forall_inv_tail in HMO; apply Forall_inv in HMO;
destruct HMO as (_ & _ & _ & HCH);
cbn [YP09.r_base] in HCH; rewrite Hb10 in HCH;
pose proof (Forall_inv HCH) as Hc31;
pose proof (Forall_inv (Forall_inv_tail HCH)) as Hc21;
cbn [YP09.c_off YP09.c_val] in Hc31, Hc21;
pose proof ((proj1 (Forall_forall _ _)) HCH) as HCA;
prreg HSz (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HSz eq_refl ltac:(vm_compute; reflexivity));
let mq := fresh "mat" in intros mq;
split; [reflexivity|];
exists (ms_regs msy), (ms_mem msy); eexists;
split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E1, Hra; reflexivity|];
split; [unfold EV_CF; rewrite Z.add_0_r; cbn [ms_mem];
apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJz|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cf_extra Bk) HSz);
[ split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; apply (proj1 HAE); lia
| cbn [ed ewset]; apply (proj2 HAE)]
| vm_compute; reflexivity ]|];
split;
[ intros jj Hjj;
destruct jj as [|jj]; [ rewrite (cf_nth Bk 0%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 18 (CVal 1 (SOff 33%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 18 (SOff 33%nat 0)
(bv_unsigned (nth 0 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 33%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 0 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 0%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 0) with (p + 18) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 0%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 1%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 19 (CVal 1 (SOff 34%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 19 (SOff 34%nat 0)
(bv_unsigned (nth 1 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 34%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 1 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 1%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 1) with (p + 19) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 1%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 2%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 20 (CVal 1 (SOff 35%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 20 (SOff 35%nat 0)
(bv_unsigned (nth 2 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 35%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 2 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 2%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 2) with (p + 20) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 2%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 3%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 21 (CVal 1 (SOff 36%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 21 (SOff 36%nat 0)
(bv_unsigned (nth 3 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 36%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 3 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 3%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 3) with (p + 21) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 3%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 4%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 22 (CVal 1 (SOff 37%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 22 (SOff 37%nat 0)
(bv_unsigned (nth 4 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 37%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 4 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 4%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 4) with (p + 22) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 4%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 5%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 23 (CVal 1 (SOff 38%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 23 (SOff 38%nat 0)
(bv_unsigned (nth 5 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 38%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 5 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 5%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 5) with (p + 23) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 5%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 6%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 24 (CVal 1 (SOff 39%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 24 (SOff 39%nat 0)
(bv_unsigned (nth 6 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 39%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 6 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 6%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 6) with (p + 24) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 6%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 7%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 25 (CVal 1 (SOff 40%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 25 (SOff 40%nat 0)
(bv_unsigned (nth 7 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 40%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 7 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 7%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 7) with (p + 25) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 7%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 8%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 26 (CVal 1 (SOff 41%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 26 (SOff 41%nat 0)
(bv_unsigned (nth 8 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 41%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 8 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 8%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 8) with (p + 26) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 8%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 9%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 27 (CVal 1 (SOff 42%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 27 (SOff 42%nat 0)
(bv_unsigned (nth 9 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 42%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 9 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 9%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 9) with (p + 27) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 9%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 10%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 28 (CVal 1 (SOff 43%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 28 (SOff 43%nat 0)
(bv_unsigned (nth 10 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 43%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 10 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 10%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 10) with (p + 28) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 10%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 11%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 29 (CVal 1 (SOff 44%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 29 (SOff 44%nat 0)
(bv_unsigned (nth 11 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 44%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 11 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 11%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 11) with (p + 29) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 11%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 12%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 30 (CVal 1 (SOff 45%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 30 (SOff 45%nat 0)
(bv_unsigned (nth 12 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 45%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 12 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 12%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 12) with (p + 30) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 12%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 13%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 31 (CVal 1 (SOff 46%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 31 (SOff 46%nat 0)
(bv_unsigned (nth 13 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 46%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 13 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 13%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 13) with (p + 31) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 13%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 14%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 32 (CVal 1 (SOff 47%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 32 (SOff 47%nat 0)
(bv_unsigned (nth 14 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 47%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 14 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 14%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 14) with (p + 32) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 14%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 15%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 33 (CVal 1 (SOff 48%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 33 (SOff 48%nat 0)
(bv_unsigned (nth 15 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 48%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 15 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 15%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 15) with (p + 33) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 15%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 16%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 34 (CVal 1 (SOff 49%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 34 (SOff 49%nat 0)
(bv_unsigned (nth 16 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 49%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 16 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 16%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 16) with (p + 34) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 16%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 17%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 35 (CVal 1 (SOff 50%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 35 (SOff 50%nat 0)
(bv_unsigned (nth 17 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 50%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 17 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 17%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 17) with (p + 35) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 17%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 18%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 36 (CVal 1 (SOff 51%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 36 (SOff 51%nat 0)
(bv_unsigned (nth 18 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 51%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 18 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 18%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 18) with (p + 36) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 18%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 19%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 37 (CVal 1 (SOff 52%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 37 (SOff 52%nat 0)
(bv_unsigned (nth 19 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 52%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 19 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 19%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 19) with (p + 37) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 19%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 20%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 38 (CVal 1 (SOff 53%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 38 (SOff 53%nat 0)
(bv_unsigned (nth 20 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 53%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 20 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 20%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 20) with (p + 38) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 20%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 21%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 39 _ _ Hc21 (denot_lit_U Ez _)) as Hvs;
match type of Hvs with YI04.val_mem _ _ _ _ (?zq mod 256) =>
assert (Hzs : zq mod 256 = cf_c21 Bk) by (repeat (rewrite U_SAlu; cbn [zalu_raw]); repeat (rewrite U_SMd; cbn [zmd_raw]);
rewrite ?U_SLit;
rewrite (U_atom Ez 49%nat _ (Eb2 49%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 16%nat ltac:(lia)); lia));
rewrite (U_atom Ez 50%nat _ (Eb2 50%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 17%nat ltac:(lia)); lia));
rewrite (U_atom Ez 51%nat _ (Eb2 51%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 18%nat ltac:(lia)); lia));
rewrite (U_atom Ez 52%nat _ (Eb2 52%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 19%nat ltac:(lia)); lia));
rewrite (U_atom Ez 53%nat _ (Eb2 53%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 20%nat ltac:(lia)); lia));
zc_flat; rewrite (land127 _ (zcanon_nonneg _));
rewrite zc_mod256, zc_mod128, mod128_256;
unfold cf_c21; rewrite cf_rsum; cbn [Nat.sub]; unfold zcanon, M64; lits_a; kill64; lia) end;
rewrite Hzs in Hvs; replace (p + 18 + Z.of_nat 21) with (p + 39) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvs
| pose proof (cf_c21_range Bk); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 22%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 40 (CVal 1 (SOff 55%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 40 (SOff 55%nat 0)
(bv_unsigned (nth 22 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 55%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 22 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 22%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 22) with (p + 40) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 22%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 23%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 41 (CVal 1 (SOff 56%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 41 (SOff 56%nat 0)
(bv_unsigned (nth 23 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 56%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 23 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 23%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 23) with (p + 41) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 23%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 24%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 42 (CVal 1 (SOff 57%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 42 (SOff 57%nat 0)
(bv_unsigned (nth 24 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 57%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 24 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 24%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 24) with (p + 42) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 24%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 25%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 43 (CVal 1 (SOff 58%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 43 (SOff 58%nat 0)
(bv_unsigned (nth 25 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 58%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 25 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 25%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 25) with (p + 43) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 25%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 26%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 44 (CVal 1 (SOff 59%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 44 (SOff 59%nat 0)
(bv_unsigned (nth 26 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 59%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 26 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 26%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 26) with (p + 44) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 26%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 27%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 45 (CVal 1 (SOff 60%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 45 (SOff 60%nat 0)
(bv_unsigned (nth 27 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 60%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 27 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 27%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 27) with (p + 45) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 27%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 28%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 46 (CVal 1 (SOff 61%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 46 (SOff 61%nat 0)
(bv_unsigned (nth 28 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 61%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 28 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 28%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 28) with (p + 46) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 28%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 29%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 47 (CVal 1 (SOff 62%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 47 (SOff 62%nat 0)
(bv_unsigned (nth 29 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 62%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 29 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 29%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 29) with (p + 47) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 29%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 30%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (HCA (YP09.mkChunk 48 (CVal 1 (SOff 63%nat 0))) ltac:(vm_compute; tauto)) as Hcj;
pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 48 (SOff 63%nat 0)
(bv_unsigned (nth 30 Bk (Z_to_bv 8 0))) Hcj
ltac:(cbn [sv_denot]; rewrite (Eb2 63%nat ltac:(lia)); cbn [Nat.sub];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as Hvj;
rewrite (Z.mod_small (bv_unsigned (nth 30 Bk (Z_to_bv 8 0))) 256) in Hvj
by (pose proof (Rb 30%nat ltac:(lia)); lia);
replace (p + 18 + Z.of_nat 30) with (p + 48) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvj
| pose proof (Rb 30%nat ltac:(lia)); lia ] | destruct jj as [|jj]; [ rewrite (cf_nth Bk 31%nat HLB ltac:(lia)); cbn [Nat.eqb];
split;
[ pose proof (val_mem1_of_chunk Ez (mrestrict Hh (ms_mem msy)) p 49 _ _ Hc31 (denot_lit_U Ez _)) as Hvs;
match type of Hvs with YI04.val_mem _ _ _ _ (?zq mod 256) =>
assert (Hzs : zq mod 256 = cf_c31 Bk) by (repeat (rewrite U_SAlu; cbn [zalu_raw]); repeat (rewrite U_SMd; cbn [zmd_raw]);
rewrite ?U_SLit;
rewrite (U_atom Ez 33%nat _ (Eb2 33%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 0%nat ltac:(lia)); lia));
rewrite (U_atom Ez 34%nat _ (Eb2 34%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 1%nat ltac:(lia)); lia));
rewrite (U_atom Ez 35%nat _ (Eb2 35%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 2%nat ltac:(lia)); lia));
rewrite (U_atom Ez 36%nat _ (Eb2 36%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 3%nat ltac:(lia)); lia));
rewrite (U_atom Ez 37%nat _ (Eb2 37%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 4%nat ltac:(lia)); lia));
rewrite (U_atom Ez 38%nat _ (Eb2 38%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 5%nat ltac:(lia)); lia));
rewrite (U_atom Ez 39%nat _ (Eb2 39%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 6%nat ltac:(lia)); lia));
rewrite (U_atom Ez 40%nat _ (Eb2 40%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 7%nat ltac:(lia)); lia));
rewrite (U_atom Ez 41%nat _ (Eb2 41%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 8%nat ltac:(lia)); lia));
rewrite (U_atom Ez 42%nat _ (Eb2 42%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 9%nat ltac:(lia)); lia));
rewrite (U_atom Ez 43%nat _ (Eb2 43%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 10%nat ltac:(lia)); lia));
rewrite (U_atom Ez 44%nat _ (Eb2 44%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 11%nat ltac:(lia)); lia));
rewrite (U_atom Ez 45%nat _ (Eb2 45%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 12%nat ltac:(lia)); lia));
rewrite (U_atom Ez 46%nat _ (Eb2 46%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 13%nat ltac:(lia)); lia));
rewrite (U_atom Ez 47%nat _ (Eb2 47%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 14%nat ltac:(lia)); lia));
rewrite (U_atom Ez 48%nat _ (Eb2 48%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 15%nat ltac:(lia)); lia));
rewrite (U_atom Ez 49%nat _ (Eb2 49%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 16%nat ltac:(lia)); lia));
rewrite (U_atom Ez 50%nat _ (Eb2 50%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 17%nat ltac:(lia)); lia));
rewrite (U_atom Ez 51%nat _ (Eb2 51%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 18%nat ltac:(lia)); lia));
rewrite (U_atom Ez 52%nat _ (Eb2 52%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 19%nat ltac:(lia)); lia));
rewrite (U_atom Ez 53%nat _ (Eb2 53%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 20%nat ltac:(lia)); lia));
rewrite (U_atom Ez 55%nat _ (Eb2 55%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 22%nat ltac:(lia)); lia));
rewrite (U_atom Ez 56%nat _ (Eb2 56%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 23%nat ltac:(lia)); lia));
rewrite (U_atom Ez 57%nat _ (Eb2 57%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 24%nat ltac:(lia)); lia));
rewrite (U_atom Ez 58%nat _ (Eb2 58%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 25%nat ltac:(lia)); lia));
rewrite (U_atom Ez 59%nat _ (Eb2 59%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 26%nat ltac:(lia)); lia));
rewrite (U_atom Ez 60%nat _ (Eb2 60%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 27%nat ltac:(lia)); lia));
rewrite (U_atom Ez 61%nat _ (Eb2 61%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 28%nat ltac:(lia)); lia));
rewrite (U_atom Ez 62%nat _ (Eb2 62%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 29%nat ltac:(lia)); lia));
rewrite (U_atom Ez 63%nat _ (Eb2 63%nat ltac:(lia)) ltac:(cbn [Nat.sub]; pose proof (Rb 30%nat ltac:(lia)); lia));
zc_flat; rewrite (land127 _ (zcanon_nonneg _)); rewrite zc_mod128;
match goal with |- context [?Zq mod 128] =>
replace (Zq mod 128) with (cf_c21 Bk)
by (unfold cf_c21; rewrite cf_rsum; cbn [Nat.sub]; unfold zcanon, M64; lits_a; kill64; lia) end;
zc_flat; rewrite zc_mod256;
unfold cf_c31; rewrite (cf_psum_B1 Bk HLB);
cbn [RcModel.psum Nat.sub]; unfold zcanon, M64; lits_a; kill256; lia) end;
rewrite Hzs in Hvs; replace (p + 18 + Z.of_nat 31) with (p + 49) by (cbn [Z.of_nat Pos.of_succ_nat]; lia); exact Hvs
| pose proof (cf_c31_range Bk); lia ] | rewrite map_length, (cf_fin_length Bk HLB) in Hjj; lia ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
| let HM := fresh "HM" in
assert (HM : forall xx : word, ~ (spZ regs - TCF_STK <= bv_unsigned xx < spZ regs) ->
~ (p + 18 <= bv_unsigned xx < p + 50) -> mrestrict Hh (ms_mem msy) xx = mrestrict Hh memc xx);
[ intros xx HA HB; apply HFr; intros Hin; destruct Hin as (rr & Hrr & Hbb);
let l := eval vm_compute in (ss_mem ss_cf) in change (ss_mem ss_cf) with l in Hrr;
cbn [In] in Hrr;
repeat (destruct Hrr as [Hrr | Hrr]); try (exfalso; exact Hrr); subst rr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hbb;
rewrite ?Usp, ?E10, ?E11 in Hbb;
rewrite ?unsigned_lit_small in Hbb by (pose proof (pa_val_range (A_OBJ A_ROW)); lia); lia
| ];
unfold tcj_kept;
split;
[ intros aa Haa Hww Hee; apply aview_of_eq; apply HM;
rewrite unsigned_lit_small by lia; lia |];
split;
[ intros bb mm ii Hin Hii Hee;
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb mm HAR Hin) as (_ & Hb4096 & Hbceil & _);
apply aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros aa Hin _ _; pose proof (pa_img_range aa Hin) as Hir;
apply aview_of_eq; apply HM; rewrite unsigned_lit_small by lia;
[lia | intros Hq; apply (Himg aa ltac:(lia)); exact Hin] |];
split;
[ intros cid pos aa Hin Hrr Hee;
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _);
pose proof (fs_frame_bytes_nonneg cid) as Hfb;
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hs1;
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2;
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hs3;
unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
apply aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; destruct Hrr as [Hrr|Hrr]; lia |];
split;
[ intros aa _ _ Hpr; exact (apresent_grows Hh memc (ms_mem msy) aa HG Hpr) |];
intros aa Haa;
pose proof HJz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _);
apply Hpres2; lia ]
end.
Qed.
End e.
End d.
End b.
