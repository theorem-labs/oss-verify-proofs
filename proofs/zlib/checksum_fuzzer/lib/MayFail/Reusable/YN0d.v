(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0d.v, with its module paths, addresses and numbers changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable segs : list Segment.
Lemma st_ok_region : forall E ss ms i r,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. pose proof (st_ok_mem_ok segs E ss ms HS) as (_ & Hok & _).
exact (proj1 (Forall_forall _ _) Hok r (nth_error_In _ _ Hi)).
Qed.
Lemma st_ok_chunk : forall E ss ms i r c,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> In c (r_chunks r) ->
chunk_ok segs E (ms_mem ms) (base_val E (r_base r)) c.
Proof.
intros E ss ms i r c HS Hi Hc. destruct (st_ok_region E ss ms i r HS Hi) as (_ & _ & _ & H).
exact (proj1 (Forall_forall _ _) H c Hc).
Qed.
Lemma st_ok_writable : forall E ss ms i r o,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> r_wlo r <= o < r_whi r ->
writable_at segs (ms_mem ms) (base_val E (r_base r) + o).
Proof.
intros E ss ms i r o HS Hi Ho. destruct (st_ok_region E ss ms i r HS Hi) as (_ & _ & H & _). apply H. exact Ho.
Qed.
Lemma chunk_bytes_cval : forall E m base off (w : N) v (val : Z),
chunk_ok segs E m base (mkChunk off (CVal w v)) ->
bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N w) = val mod 2 ^ (8 * Z.of_N w) ->
forall k, (k < N.to_nat w)%nat -> mbyte segs m (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte val (N.to_nat w) k)).
Proof.
intros E m base off w v val Hc Hv k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [c_off c_val cbyte] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb2. f_equal. unfold byte_of_word.
rewrite (YN01.le_byte_bv val (N.to_nat w) k Hk).
rewrite <- (YN2e.le_byte_bv (bv_unsigned (sv_denot E v)) (N.to_nat w) k Hk).
rewrite (YN01.le_byte_bv _ (N.to_nat w) k Hk). rewrite N_nat_Z. rewrite Hv. reflexivity.
Qed.
Lemma chunk_bytes_cval_exact : forall E m base off (w : N) v (val : Z),
chunk_ok segs E m base (mkChunk off (CVal w v)) -> sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
forall k, (k < N.to_nat w)%nat -> mbyte segs m (base + off + Z.of_nat k) = Some (Z_to_bv 8 (le_byte val (N.to_nat w) k)).
Proof.
intros E m base off w v val Hc Hv Hval k Hk. eapply chunk_bytes_cval; [exact Hc | | exact Hk].
rewrite Hv, u64_of_Z by exact Hval. reflexivity.
Qed.
Lemma chunk_bytes_czero : forall E m base off len,
chunk_ok segs E m base (mkChunk off (CZero len)) ->
forall i, 0 <= i < len -> mbyte segs m (base + off + i) = Some (Z_to_bv 8 0).
Proof.
intros E m base off len Hc i Hi. destruct (Hc i ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [c_off c_val cbyte] in Hb1, Hb2.
injection Hb1 as <-. exact Hb2.
Qed.
Lemma chunk_bytes_cdata : forall E m base off d len,
chunk_ok segs E m base (mkChunk off (CData d 0 len)) ->
forall k, Z.of_nat k < len -> mbyte segs m (base + off + Z.of_nat k) = nth_error (ed E d) k.
Proof.
intros E m base off d len Hc k Hk. destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [c_off c_val cbyte] in Hb1, Hb2.
rewrite Z.add_0_l, Nat2Z.id in Hb1. rewrite Hb2, <- Hb1. reflexivity.
Qed.
Lemma chunk_word_mem : forall E m base off v (val : Z),
chunk_ok segs E m base (mkChunk off (CVal 8 v)) -> sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
word_mem segs m (base + off) val.
Proof.
intros E m base off v val Hc Hv Hval k Hk. exact (chunk_bytes_cval_exact E m base off 8 v val Hc Hv Hval k Hk).
Qed.
End f.
Definition in_img1 (a : Z) : Prop := 0x10000 <= a < 0x51000.
Lemma in_img_img1 : forall a, in_img src0_msyms a -> in_img1 a.
Proof.
intros a [_ (s & Hs & Ha)].
assert (H : forallb (fun s : word * word => (0x10000 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x51000))
(segments_reserved src0segs) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H s Hs). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_img1. lia.
Qed.
Lemma in_img1_img : forall a, in_img1 a -> in_img src0_msyms a.
Proof.
intros a Ha. unfold in_img1 in Ha.
destruct (Z_lt_le_dec a 0x13000); [apply (covered_sound src0_msyms 0x10000 0x3000); [vm_compute; reflexivity | lia]|].
destruct (Z_lt_le_dec a 0x1e000); [apply (covered_sound src0_msyms 0x13000 0xb000); [vm_compute; reflexivity | lia]|].
destruct (Z_lt_le_dec a 0x1f000); [apply (covered_sound src0_msyms 0x1e000 0x1000); [vm_compute; reflexivity | lia]|].
apply (covered_sound src0_msyms 0x1f000 0x32000); [vm_compute; reflexivity | lia].
Qed.
Lemma writable_off_img_present : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img1 a -> writable_at src0segs m a -> present m a.
Proof.
intros m a Ha Hni Hw. unfold writable_at, wview in Hw. unfold present.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|]. exfalso.
destruct (find_segment src0segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|apply Hw; reflexivity].
pose proof (find_segment_in _ _ _ _ Ef) as Hin. pose proof (find_segment_range _ _ _ _ Ef) as Hr.
rewrite u64_of_Z in Hr by lia.
assert (H : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x51000)) src0segs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H seg Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hni. unfold in_img1. lia.
Qed.
Lemma mbyte_off_img : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img1 a -> mbyte src0segs m a = m (Z_to_bv 64 a).
Proof.
intros m a Ha Hni. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [reflexivity|].
destruct (seg_rom src0segs (Z_to_bv 64 a)) as [b|] eqn:Er; [|reflexivity]. exfalso.
unfold seg_rom, memory_read in Er.
destruct (find_segment src0segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [seg|] eqn:Ef; [|discriminate].
pose proof (find_segment_in _ _ _ _ Ef) as Hin. pose proof (find_segment_range _ _ _ _ Ef) as Hr.
rewrite u64_of_Z in Hr by lia.
assert (H : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x51000)) src0segs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H seg Hin). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hni. unfold in_img1. lia.
Qed.
Lemma lxor_ones_mod : forall u, 0 <= u < 2 ^ 64 -> (Z.lxor u (Z.ones 64)) mod 2 ^ 64 = 2 ^ 64 - 1 - u.
Proof.
intros u Hu. rewrite <- (not64_eq u Hu). unfold not64. rewrite <- Z.lxor_m1_r.
apply Z.bits_inj'. intros i Hi. rewrite !testbit_mod_pow2 by lia.
destruct (Z.ltb i 64) eqn:E; [|reflexivity].
rewrite !Z.lxor_spec. rewrite Z.ones_spec_low by (apply Z.ltb_lt in E; lia). rewrite Z.bits_m1 by lia. reflexivity.
Qed.
Lemma mapok_taken : forall a : bv 64, bv_unsigned a + 8 < 2 ^ 64 ->
branch_taken BC_NE (alu64 ALU_OR (Z_to_bv 64 0) (alu64 ALU_XOR a (Z_to_bv 64 (-1)))) (Z_to_bv 64 0) = true.
Proof.
intros a Ha. pose proof (u64_range a).
rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite !zalu64_sound, branch_ne, !u64_of_Z_mod.
unfold zalu64, zcanon, zalu_raw. change M64 with (2 ^ 64).
rewrite (Z.mod_small (bv_unsigned a)) by lia. change (-1 mod 2 ^ 64) with (Z.ones 64). change (0 mod 2 ^ 64) with 0.
rewrite Z.lor_0_l, lxor_ones_mod by lia. rewrite (Z.mod_small (2 ^ 64 - 1 - bv_unsigned a)) by lia.
rewrite (Z.mod_small (2 ^ 64 - 1 - bv_unsigned a)) by lia. change (0 mod 2 ^ 64) with 0.
apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
Qed.
Lemma sext32_val : forall w : bv 64, sext 64 (bv_extract 0 32 w) = Z_to_bv 64 (sx32 (bv_unsigned w)).
Proof. intros w. rewrite b_lw_val. apply vz_lw. Qed.
Lemma ctr_chunk_mod : forall ctr, 0 <= ctr < 2 ^ 32 ->
bv_unsigned (alu64 ALU_ADD (sext 64 (bv_extract 0 32 (Z_to_bv 64 ctr))) (Z_to_bv 64 1)) mod 2 ^ 32 = (ctr + 1) mod 2 ^ 32.
Proof.
intros ctr Hc. rewrite sext32_val, zalu64_sound, u64_of_Z_mod. unfold zalu64, zcanon, zalu_raw. change M64 with (2 ^ 64).
rewrite u64_of_Z by lia. rewrite mod64_mod32, mod64_mod32.
rewrite <- Zplus_mod_idemp_l, mod64_mod32, sx32_mod32, Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma ctr_word_mod : forall ctr, 0 <= ctr < 2 ^ 32 ->
bv_unsigned (alu64 ALU_ADD (sext 64 (bv_extract 0 32 (alu64 ALU_ADD (sext 64 (bv_extract 0 32 (Z_to_bv 64 ctr))) (Z_to_bv 64 1)))) (Z_to_bv 64 0)) mod 2 ^ 32
= (ctr + 1) mod 2 ^ 32.
Proof.
intros ctr Hc. rewrite (sext32_val (alu64 _ _ _)). rewrite zalu64_sound, u64_of_Z_mod. unfold zalu64, zcanon, zalu_raw. change M64 with (2 ^ 64).
rewrite mod64_mod32, mod64_mod32. change (0 mod 2 ^ 64) with 0. rewrite Z.add_0_r. rewrite mod64_mod32, sx32_mod32.
apply ctr_chunk_mod. exact Hc.
Qed.
Lemma land255_mod : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma mod32_mod256 : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> x mod 256 = y mod 256.
Proof.
intros x y H. rewrite (Znumtheory.Zmod_div_mod 256 (2 ^ 32) x); [| lia | lia | exists (2 ^ 24); reflexivity].
rewrite (Znumtheory.Zmod_div_mod 256 (2 ^ 32) y); [| lia | lia | exists (2 ^ 24); reflexivity]. rewrite H. reflexivity.
Qed.
Lemma bits_word : forall n, 0 <= n < 2 ^ 62 ->
alu64 ALU_OR (alu64 ALU_AND (Z_to_bv 64 (n + 4115)) (Z_to_bv 64 (-2048))) (Z_to_bv 64 4064) = Z_to_bv 64 (bits_enc 0 63 (page_round (n + IB + UNIT) / PGSZ)).
Proof.
intros n Hn. rewrite <- direct_bits_ok by lia. rewrite !zalu64_sound. f_equal.
unfold zalu64, zcanon, zalu_raw, direct_bits_machine. change M64 with (2 ^ 64). cbv zeta.
rewrite (add64_small n 4064) by lia. rewrite add64_small by lia. replace (n + 4064 + 51) with (n + 4115) by lia.
rewrite (Z.mod_small (n + 4115)) by lia. change ((-2048) mod 2 ^ 64) with (2 ^ 64 - 2048). change (4064 mod 2 ^ 64) with 4064.
pose proof (land_range64 (n + 4115) (2 ^ 64 - 2048) ltac:(lia) ltac:(lia)).
rewrite (Z.mod_small (Z.land _ _)) by lia. rewrite (Z.mod_small (Z.land _ _)) by lia.
pose proof (lor_range64 (Z.land (n + 4115) (2 ^ 64 - 2048)) 4064 ltac:(lia) ltac:(lia)).
rewrite Z.mod_small by lia. reflexivity.
Qed.
End e.
