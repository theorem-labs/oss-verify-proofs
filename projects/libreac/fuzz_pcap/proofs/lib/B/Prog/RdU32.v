(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: rd_u32 (fuzz_pcap.asan-ubsan 0x81c38, listing offset AF_rd_u32 = 0x14b0, 69
   instructions) on libreac v1.9.0's ASan+UBSan build: the contract of the code.

   rd_u32 of libreac's pcap_source.c (`rd_u32(p, swapped)`, :12-15) is a function of its own only in this build: the
   ASan build inlines it into pcap_source_next. Its only caller is pcap_source_next (0x815b8), at 0x81788, 0x817a8,
   0x817c8 and 0x817f0, with a0 = ph + 0, 4, 8, 12 (ph: the 16-byte record header in the caller's side-stack frame)
   and a1 = the stream's `swapped` field (`lw a1,0(s11)`, sign-extended).

   The released v1.8 UBSan proof of the same C function (proofs/libreac/fuzz_pcap/lib/U/Prog/rd_u32.v, contract
   rd_u32_c.v) proves a different body: 28 instructions without ASan. This body differs from instruction 0, so this is
   a new contract and walk, with the released files as the template for the UBSan guard decisions.

   THE CODE (capstone 5 on the pin, sha256 9e66f771f22a...).
   - 0x81c38 `addi sp,sp,-16`, 0x81c3c `sd ra,8(sp)`: a 16-byte frame on the machine stack, ra saved in it.
   - 0x81c40/0x81c44 `auipc a2 / ld a2`: the GOT word of the shadow base (object 1), 0x81c48 `ld a4,0(a2)`: the
     shadow base from its cell (object 15).
   - Byte 0: 0x81c4c..0x81c54 shadow byte of p (`srli`, `add`, `lb`), 0x81c58 `bnez` to the slow path 0x81d10
     (`andi a3,a0,7`; `blt a3,a2` back to 0x81c5c; else 0x81d18 `jal __asan_report_load1`).
   - UBSan guard G1: 0x81c5c `addi a2,zero,-1`, 0x81c60 `beq a0,a2` to the `unimp` at 0x81d0c (p + 1 wraps).
   - Byte 1: 0x81c64..0x81c70 shadow byte of p + 1, 0x81c74 `lbu a5,0(a0)` (the load of byte 0), 0x81c78 `bnez` to
     the slow path 0x81d1c (report call 0x81d28).
   - UBSan guard G2: 0x81c7c `addi a2,a0,3`, 0x81c80 `addi a3,zero,2`, 0x81c84 `bltu a2,a3` to the `unimp` (p + 2 or
     p + 3 wraps).
   - Byte 2: 0x81c88..0x81c94 shadow byte of p + 2, 0x81c98 `lbu a6,1(a0)`, 0x81c9c `bnez` to the slow path 0x81d2c
     (report call 0x81d38).
   - Byte 3: 0x81ca0..0x81ca8 shadow byte of p + 3, 0x81cac `lbu a0,2(a0)`, 0x81cb0 `bnez` to the slow path 0x81d3c
     (report call 0x81d48); 0x81cb8 `lbu a3,0(a2)` (byte 3).
   - The value: 0x81cb4..0x81ccc a0 := b0 | b1 << 8 | b2 << 16 | sext32(b3 << 24); 0x81cd0 `beqz a1` to the epilogue;
     else 0x81cd4..0x81cfc the byte swap, a0 := sext32(b0 << 24) | b1 << 16 | b2 << 8 | b3.
   - 0x81d00 `ld ra,8(sp)`, 0x81d04 `addi sp,sp,16`, 0x81d08 `ret`.
   It calls nothing but the four report functions on the slow paths, and the walk shows that those calls are not
   reached. It does not read the use-after-return flag (it takes no side-stack frame).

   THE CONTRACT is the kit's caller-journal form of lib/A/Prog/PcapSourceClose.v (tpcap_source_close_specX): the
   premise is the caller's journal, and the post extends the same journal, at the caller's layout and allocator state
   (so the allocator meter does not move) and with no allocator event. The statement is image-generic: it takes the
   segments `segs` as a parameter, never a PAImg instance (a Theorem Labs lane's ruling); the image has no other datum in it.
   The sink-head instance SK is explicit, because ajournal takes it (Reusable/YCbq.v:85, fp_spares).
   - The 4 bytes lie in a frame of the caller's state (`In (cid, pos) (frames Sc)`: pcap_source_next's ph is in its
     class-0 side-stack frame), they read b0..b3 (garr8), and their shadow marks them usable (range_addressable).
     Frames lie in [4096, alloc_ceiling) (YCbq frames_bounds), so p >= 4096 (no null) and p + 4 < 2 ^ 47 (no wrap).
     The pre also states, in lib/A/Stdio/PFreadISpec.v's form (:67 at d83ca9847f8), that the bytes are apart from
     every byte the call writes, the function's own frame [sp - 16, sp) (R1, a Theorem Labs lane).
   - The post: a0 = the sign-extended 32-bit value rd_u32_val of the bytes; the callee-saved registers and sp are kept;
     the call returns to ra; the world is the same; the 4 bytes still read b0..b3, and every byte outside the
     function's own 16-byte frame [sp - 16, sp) is unchanged (the only store is `sd ra,8(sp)` into that frame); the
     descriptor table and the file system are unchanged.

   THE WALK (pb_rd_u32X) is the kit's method of lib/A/Prog/PcapSourceClose.v over lib/B's listing: rd_entry builds the
   symbolic entry state (the frame, the shadow base's GOT word and cell, the 4 bytes as one chunk each, and the facts),
   one symbolic run (paj_run_tok) goes from 0x81c38 to the test of swapped at 0x81cd0, psrr_branch_tok splits there,
   and each arm runs to the `ret` at 0x81d08 (paj_ret_at). The value of a0 in each arm is RV_NOSWAP / RV_SWAP, whose
   denotation rv_noswap_val / rv_swap_val compute.
   - The UBSan guards are decided inside the first run, by the engine's interval test (Reusable/YP0e.v:932
     decide_cond2), from atom 10's fact p in [4096, 2 ^ 47 - 2 ^ 23] (rd_facts), which rd_entry proves from
     frames_bounds (Reusable/YCbq.v:447):
       0x81c60 `beq a0,-1`: decide_eq2 (YP0e.v:914): p's range is disjoint from 2 ^ 64 - 1, not taken;
       0x81c84 `bltu a0+3,2`: decide_ltu2 (YP0e.v:922, itv_lt :893): [p + 3, ...] lies above 2, not taken.
     Template: the released v1.8 UBSan proof lib/U/Prog/rd_u32.v (origin/ossv/recipes c8557374ad2e), where
     bytes_at_bound at :19 gives a0 + 4 <= 2 ^ 64 and the two `if_false` at :31 take the same two guards' false arms.
   - The four ASan checks (0x81c58, 0x81c78, 0x81c9c, 0x81cb0 `bnez` of the shadow byte of p, p + 1, p + 2, p + 3)
     are decided inside the same run: each shadow `lb` becomes a token (Reusable/YCbn.v:173 tok_load), and each `bnez`
     with its slow path (`andi u,x,7; blt u,k` back to the next instruction, YCbn.v:213 slow_block) is merged by
     PaShadow.v:38 (sha256 0c4d47929598; internal record) tok_branch_pi, because the 1-byte access is covered by the shadow entry rd_SH = [p, p + 4)
     (YCbn.v:133 covered). That entry's sh_ok (YCbn.v:358 shent_ok) is the premise range_addressable (shent_p_ok).
     The run leaves no shadow obligation, so the four __asan_report_load1 calls (0x81d18, 0x81d28, 0x81d38, 0x81d48)
     are not reached. Template: lib/A/Prog/PcapSourceClose.v cl_entry / shent_ps_ok (the same entry form, at 8
     bytes). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The function's own frame on the machine stack: 0x81c38 `addi sp,sp,-16`. *)
Definition RDU32_FRAME : Z := 16.

(* The little-endian value of 4 bytes (lib/Prog/pcap_source_struct_next.v's w32le, the model's reading of a header
   word), and rd_u32's value: the bytes in memory order when `swapped` is 0, else in reverse order (0x81cd0 `beqz a1`
   tests all 64 bits of a1). *)
Definition u32le (b0 b1 b2 b3 : Z) : Z := b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.
Definition rd_u32_val (sw b0 b1 b2 b3 : Z) : Z := if sw =? 0 then u32le b0 b1 b2 b3 else u32le b3 b2 b1 b0.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the contract, over the image's segments as a parameter ---------------------------------------------------- *)
Section s.
Variable segs : list Segment.
Variable B : asyms.

Definition trd_u32_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (p b0 b1 b2 b3 : Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists regs2 mem2 md2,
  W2 = W /\
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
  (* the same journal, at the caller's layout and allocator state, with no allocator event *)
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
  aregs_preserved regs regs2 /\
  getr regs2 10 = w64 (bv_swrap 32 (rd_u32_val (bv_unsigned (getr regs 11)) b0 b1 b2 b3)) /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  (* the 4 bytes are kept, and every byte outside the function's own frame is unchanged *)
  garr8 segs (rdW W mem2) p [b0; b1; b2; b3] /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RDU32_FRAME <= a < spZ regs) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a).

Definition trd_u32_specX (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p b0 b1 b2 b3 cid pos : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RDU32_FRAME -> spZ regs <= sp0 ->
  (* the 4 bytes: in a frame of the caller's state, apart from the function's own frame, readable, their shadow
     marked usable *)
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= p -> p + 4 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (p + 4 <= spZ regs - RDU32_FRAME \/ spZ regs <= p) ->
  garr8 segs (rdW W memc) p [b0; b1; b2; b3] ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF p 4 ->
  SRr segs W (cfg_at segs a regs memc mdc)
    (trd_u32_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b0 b1 b2 b3).

End s.

(* ---- the value: the two final a0 terms of the walk and what they denote ---------------------------------------- *)
(* The 24-bit value b0 | b1 << 8 | b2 << 16 (0x81cb4..0x81cc4) and sext32(b3 << 24) (0x81cc8 `slliw`), in the
   symbolic engine's terms over the byte atoms 33..36. *)
Definition RV_LO : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 33 0)) (SAlu ALU_SLL (SOff 35 0) (SLit 16)).
Definition RV_HI : sv := SAluw ALU_SLL (SOff 36 0) (SLit 24).
(* a0 at the `ret` when swapped = 0 (0x81ccc `or a0,a2,a3`) ... *)
Definition RV_NOSWAP : sv := SAlu ALU_OR RV_LO RV_HI.
(* ... and when it is not (0x81cd4..0x81cfc). *)
Definition RV_SWAP : sv :=
  SAlu ALU_OR
    (SAlu ALU_OR (SAluw ALU_SLL RV_LO (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND RV_NOSWAP (SLit 65280)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL RV_LO (SLit 16)) (SLit 8)) (SAluw ALU_SRL RV_HI (SLit 24))).

Lemma lor_lo_hi : forall x y n, 0 <= n -> 0 <= x < 2 ^ n -> y mod 2 ^ n = 0 -> Z.lor x y = x + y.
Proof.
intros x y n Hn Hx Hy.
assert (HL : Z.land x y = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 0) as [Hi|Hi]; [rewrite Z.testbit_neg_r by exact Hi; reflexivity|].
  destruct (Z.lt_ge_cases i n) as [Hin|Hin].
  - replace (Z.testbit y i) with false; [apply andb_false_r|].
    rewrite <- (Z.mod_pow2_bits_low y n i) by lia. rewrite Hy. symmetry. apply Z.bits_0.
  - replace (Z.testbit x i) with false; [reflexivity|].
    rewrite <- (Z.mod_small x (2 ^ n)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia. }
rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma land_65280 : forall x, 0 <= x -> Z.land x 65280 = 256 * ((x / 256) mod 256).
Proof.
intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
change 65280 with (Z.shiftl (Z.ones 8) 8). change 256 with (2 ^ 8).
rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftr_div_pow2 by lia.
destruct (Z.lt_ge_cases n 8) as [H8|H8].
- rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
- rewrite !Z.shiftl_spec by lia.
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec (n - 8) 8) as [Hl|Hl].
  + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia.
    replace (n - 8 + 8) with n by lia. apply andb_true_r.
  + rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma swrap32_cases : forall v, 0 <= v < 2 ^ 32 -> bv_swrap 32 v = if v <? 2 ^ 31 then v else v - 2 ^ 32.
Proof.
intros v Hv. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (2 ^ 31) with 2147483648 in *. change (2 ^ 32) with 4294967296 in *.
destruct (Z.ltb_spec v 2147483648); Z.div_mod_to_equations; lia.
Qed.

Lemma swrap32_mod : forall z, bv_swrap 32 z = bv_swrap 32 (z mod 2 ^ 32).
Proof. intros z. symmetry. exact (bv_swrap_wrap 32 z). Qed.

Section v.
Variable E : env.
Variables b0 b1 b2 b3 : Z.
Hypothesis H33 : ew E 33 = Z_to_bv 64 b0.
Hypothesis H34 : ew E 34 = Z_to_bv 64 b1.
Hypothesis H35 : ew E 35 = Z_to_bv 64 b2.
Hypothesis H36 : ew E 36 = Z_to_bv 64 b3.
Hypothesis R0 : 0 <= b0 < 256.
Hypothesis R1 : 0 <= b1 < 256.
Hypothesis R2 : 0 <= b2 < 256.
Hypothesis R3 : 0 <= b3 < 256.

Lemma U_RV_LO : U E RV_LO = b0 + 256 * b1 + 65536 * b2.
Proof.
unfold RV_LO. rewrite !U_SAlu, !U_SLit.
rewrite (U_atom E 33 b0 H33), (U_atom E 34 b1 H34), (U_atom E 35 b2 H35) by lia.
cbn [zalu_raw]. change (Z.land (zcanon 8) 63) with 8. change (Z.land (zcanon 16) 63) with 16.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
rewrite (zcanon_id (b1 * 256)) by (unfold M64; lia).
rewrite (Z.lor_comm (b1 * 256) b0), (lor_lo_hi b0 (b1 * 256) 8) by (change (2 ^ 8) with 256; try apply Z.mod_mul; lia).
rewrite (zcanon_id (b0 + b1 * 256)) by (unfold M64; lia).
rewrite (zcanon_id (b2 * 65536)) by (unfold M64; lia).
rewrite (lor_lo_hi (b0 + b1 * 256) (b2 * 65536) 16) by (change (2 ^ 16) with 65536; try apply Z.mod_mul; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* sext32(b3 << 24) as a 64-bit unsigned value *)
Definition rv_hi : Z := bv_wrap 64 (bv_swrap 32 (b3 * 16777216)).

Lemma rv_hi_eq : rv_hi = if b3 <? 128 then b3 * 16777216 else b3 * 16777216 - 4294967296 + 18446744073709551616.
Proof.
unfold rv_hi. rewrite swrap32_cases by lia. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
destruct (Z.ltb_spec b3 128); destruct (Z.ltb_spec (b3 * 16777216) 2147483648); try lia; Z.div_mod_to_equations; lia.
Qed.

Lemma U_RV_HI : U E RV_HI = rv_hi.
Proof.
unfold RV_HI. rewrite U_of_S, S_SAluw, U_SLit. rewrite (U_atom E 36 b3 H36) by lia.
cbn [zalu_raw]. change (Z.land (zcanon 24 mod 2 ^ 32) 31) with 24.
rewrite (Z.mod_small b3 (2 ^ 32)) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma U_RV_NOSWAP : U E RV_NOSWAP = b0 + 256 * b1 + 65536 * b2 + rv_hi.
Proof.
unfold RV_NOSWAP. rewrite U_SAlu. fold RV_LO RV_HI. rewrite U_RV_LO, U_RV_HI. cbn [zalu_raw].
pose proof rv_hi_eq as Hh.
rewrite (lor_lo_hi _ rv_hi 24).
- apply zcanon_id. unfold M64. destruct (b3 <? 128); lia.
- lia.
- change (2 ^ 24) with 16777216. lia.
- change (2 ^ 24) with 16777216. rewrite Hh. destruct (b3 <? 128).
  + apply Z.mod_mul. lia.
  + replace (b3 * 16777216 - 4294967296 + 18446744073709551616) with ((b3 - 256 + 1099511627776) * 16777216) by lia.
    apply Z.mod_mul. lia.
Qed.

Lemma rv_noswap_val : sv_denot E RV_NOSWAP = w64 (bv_swrap 32 (u32le b0 b1 b2 b3)).
Proof.
rewrite denot_lit_U, U_RV_NOSWAP. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
rewrite rv_hi_eq, swrap32_cases by (unfold u32le; lia). unfold u32le, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
destruct (Z.ltb_spec b3 128); destruct (Z.ltb_spec (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) 2147483648);
  try lia; Z.div_mod_to_equations; lia.
Qed.

Lemma U_RV_SWAP : U E RV_SWAP = bv_wrap 64 (bv_swrap 32 (b0 * 16777216)) + 65536 * b1 + 256 * b2 + b3.
Proof.
pose proof rv_hi_eq as Hh.
assert (Hs0 : bv_wrap 64 (bv_swrap 32 (b0 * 16777216)) =
  if b0 <? 128 then b0 * 16777216 else b0 * 16777216 - 4294967296 + 18446744073709551616).
{ rewrite swrap32_cases by lia. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
  destruct (Z.ltb_spec b0 128); destruct (Z.ltb_spec (b0 * 16777216) 2147483648); try lia; Z.div_mod_to_equations; lia. }
(* the four parts *)
assert (P1 : U E (SAluw ALU_SLL RV_LO (SLit 24)) = bv_wrap 64 (bv_swrap 32 (b0 * 16777216))).
{ rewrite U_of_S, S_SAluw, U_SLit, U_RV_LO. cbn [zalu_raw]. change (Z.land (zcanon 24 mod 2 ^ 32) 31) with 24.
  rewrite (Z.mod_small (b0 + 256 * b1 + 65536 * b2) (2 ^ 32)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_mod. symmetry. rewrite swrap32_mod. f_equal. change (2 ^ 24) with 16777216. change (2 ^ 32) with 4294967296.
  replace ((b0 + 256 * b1 + 65536 * b2) * 16777216) with (b0 * 16777216 + (b1 + 256 * b2) * 4294967296) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
assert (P2 : U E (SAlu ALU_SLL (SAlu ALU_AND RV_NOSWAP (SLit 65280)) (SLit 8)) = 65536 * b1).
{ rewrite !U_SAlu, !U_SLit, U_RV_NOSWAP. cbn [zalu_raw]. change (zcanon 65280) with 65280.
  change (Z.land (zcanon 8) 63) with 8.
  rewrite land_65280 by (destruct (b3 <? 128) eqn:?; rewrite Hh; lia).
  replace ((b0 + 256 * b1 + 65536 * b2 + rv_hi) / 256) with (b1 + 256 * (b2 + rv_hi / 65536)).
  - replace ((b1 + 256 * (b2 + rv_hi / 65536)) mod 256) with b1
      by (rewrite (Z.mul_comm 256 (b2 + rv_hi / 65536)), Z.mod_add, Z.mod_small by lia; reflexivity).
    rewrite (zcanon_id (256 * b1)) by (unfold M64; lia).
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite zcanon_id by (unfold M64; lia). lia.
  - assert (Hq : exists q, rv_hi = 16777216 * q /\ 0 <= q).
    { rewrite Hh. destruct (b3 <? 128).
      - exists b3. lia.
      - exists (b3 - 256 + 1099511627776). lia. }
    destruct Hq as (q & Hq & Hq0). rewrite Hq.
    replace (16777216 * q / 65536) with (256 * q)
      by (replace (16777216 * q) with ((256 * q) * 65536) by lia; rewrite Z.div_mul by lia; reflexivity).
    replace (b0 + 256 * b1 + 65536 * b2 + 16777216 * q) with (b0 + (b1 + 256 * (b2 + 256 * q)) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
assert (P3 : U E (SAlu ALU_SLL (SAlu ALU_SRL RV_LO (SLit 16)) (SLit 8)) = 256 * b2).
{ rewrite !U_SAlu, !U_SLit, U_RV_LO. cbn [zalu_raw].
  change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  replace (b0 + 256 * b1 + 65536 * b2) with ((b0 + 256 * b1) + b2 * 65536) by lia.
  rewrite Z.div_add, Z.div_small, Z.add_0_l by lia.
  rewrite (zcanon_id b2) by (unfold M64; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite zcanon_id by (unfold M64; lia). lia. }
assert (P4 : U E (SAluw ALU_SRL RV_HI (SLit 24)) = b3).
{ rewrite U_of_S, S_SAluw, U_SLit, U_RV_HI. cbn [zalu_raw]. change (Z.land (zcanon 24 mod 2 ^ 32) 31) with 24.
  assert (Hm : rv_hi mod 2 ^ 32 = b3 * 16777216).
  { rewrite Hh. change (2 ^ 32) with 4294967296. destruct (b3 <? 128).
    - apply Z.mod_small. lia.
    - replace (b3 * 16777216 - 4294967296 + 18446744073709551616) with (b3 * 16777216 + (4294967295) * 4294967296) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite Hm. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. rewrite Z.div_mul by lia.
  rewrite swrap32_cases by lia. change (2 ^ 31) with 2147483648. replace (b3 <? 2147483648) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
unfold RV_SWAP.
set (t1 := SAluw ALU_SLL RV_LO (SLit 24)) in *. set (t2 := SAlu ALU_SLL (SAlu ALU_AND RV_NOSWAP (SLit 65280)) (SLit 8)) in *.
set (t3 := SAlu ALU_SLL (SAlu ALU_SRL RV_LO (SLit 16)) (SLit 8)) in *. set (t4 := SAluw ALU_SRL RV_HI (SLit 24)) in *.
clearbody t1 t2 t3 t4.
rewrite !U_SAlu. rewrite P1, P2, P3, P4. cbn [zalu_raw].
assert (HQ0 : exists q0, bv_wrap 64 (bv_swrap 32 (b0 * 16777216)) = q0 * 16777216 /\ 0 <= q0 /\ q0 * 16777216 < 2 ^ 64).
{ rewrite Hs0. destruct (Z.ltb_spec b0 128).
  - exists b0. lia.
  - exists (b0 - 256 + 1099511627776). lia. }
destruct HQ0 as (q0 & HQ0 & Hq0 & Hq0'). rewrite HQ0.
rewrite (Z.lor_comm (256 * b2) b3), (lor_lo_hi b3 (256 * b2) 8)
  by (change (2 ^ 8) with 256; try (rewrite Z.mul_comm; apply Z.mod_mul); lia).
rewrite (Z.lor_comm (q0 * 16777216) (65536 * b1)), (lor_lo_hi (65536 * b1) (q0 * 16777216) 24)
  by (change (2 ^ 24) with 16777216; try apply Z.mod_mul; lia).
rewrite (zcanon_id (65536 * b1 + q0 * 16777216)) by (unfold M64; lia).
rewrite (zcanon_id (b3 + 256 * b2)) by (unfold M64; lia).
rewrite (Z.lor_comm (65536 * b1 + q0 * 16777216) (b3 + 256 * b2)).
rewrite (lor_lo_hi (b3 + 256 * b2) (65536 * b1 + q0 * 16777216) 16).
2: lia.
2: change (2 ^ 16) with 65536; lia.
2: { change (2 ^ 16) with 65536. replace (65536 * b1 + q0 * 16777216) with ((b1 + 256 * q0) * 65536) by lia.
     apply Z.mod_mul. lia. }
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma rv_swap_val : sv_denot E RV_SWAP = w64 (bv_swrap 32 (u32le b3 b2 b1 b0)).
Proof.
rewrite denot_lit_U, U_RV_SWAP. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
rewrite (swrap32_cases (u32le b3 b2 b1 b0)) by (unfold u32le; lia).
rewrite (swrap32_cases (b0 * 16777216)) by lia. unfold u32le, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
destruct (Z.ltb_spec (b0 * 16777216) 2147483648); destruct (Z.ltb_spec (b3 + 256 * b2 + 65536 * b1 + 16777216 * b0) 2147483648);
  try lia; Z.div_mod_to_equations; lia.
Qed.

End v.

(* ---- the walk over lib/B's listing --------------------------------------------------------------------------- *)
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).

(* Materialising the lazy vm backing keeps the descriptor table and the file system. *)
Lemma rd_wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. split; reflexivity. Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).

(* The symbolic state at the entry: the 16-byte stack frame, the shadow base's GOT word (object 1) and cell (object
   15), and the 4 bytes at p = a0 (atom 10), one chunk per byte (atoms 33..36). The facts: sp in the machine stack
   (atom 2), p in [4096, 2 ^ 47 - 2 ^ 23) (a frame below alloc_ceiling), the shadow base (atom 32), the bytes below
   256. The one shadow entry covers [p, p + 4). *)
Definition SB_RD : Z := 0x7fff8000.
Definition RBx : sv := SOff 32 0.
Definition RDspan : Z * Z := (SB_RD, SB_RD + 2 ^ 44 - 1).
Definition p_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0));
   YP09.mkChunk 2 (CVal 1 (SOff 35 0)); YP09.mkChunk 3 (CVal 1 (SOff 36 0))].
Definition rd_regions : smem := [stack_region RDU32_FRAME; got_regionP; bcell_regionP 32; p_region].
Definition rd_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 0); (32%nat, mkAF SB_RD SB_RD 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)] [] [].
Definition ss_rd : sstate := mkSS AF_rd_u32 sr_atoms rd_regions None rd_facts.
Definition rd_SH : list shent := [mkSHE 10 0 4].
Definition rd_extra (b0 b1 b2 b3 : Z) : list word := map (Z_to_bv 64) [SB_RD; b0; b1; b2; b3].

Lemma shent_p_ok : forall Ex (m : word -> option byte) p,
  U Ex RBx = SHADOW_OFF -> U Ex (SOff 10 0) = p ->
  (4096 <= p /\ (p + 4 <= kLowShadowBeg \/ kHighMemBeg <= p)) ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF p 4 ->
  sh_ok SEGS RBx rd_SH Ex m.
Proof.
intros Ex m p HB Hq Hz HR. unfold sh_ok, rd_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
- rewrite Z.add_0_r. exact HR.
- intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma rd_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p b0 b1 b2 b3 cid pos,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 p ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RDU32_FRAME -> spZ regs <= sp0 ->
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= p -> p + 4 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (p + 4 <= spZ regs - RDU32_FRAME \/ spZ regs <= p) ->
  garr8 SEGS (rdW W memc) p [b0; b1; b2; b3] ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 4 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (rd_extra b0 b1 b2 b3))) ss_rd
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rd_u32)) memc (seg_rom SEGS))) /\
  sh_ok SEGS RBx rd_SH (Eimg (Ereg regs (rd_extra b0 b1 b2 b3))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b0 b1 b2 b3 cid pos
  HJ H10 Hal16 Hwlo Hwhi Hin Hfa1 Hfa2 Hdisj Hga Hsh.
unfold RDU32_FRAME in Hwlo, Hdisj.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 15 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
pose proof (proj2 (Hga 0%nat ltac:(cbn; lia))) as Rb0. pose proof (proj2 (Hga 1%nat ltac:(cbn; lia))) as Rb1.
pose proof (proj2 (Hga 2%nat ltac:(cbn; lia))) as Rb2. pose proof (proj2 (Hga 3%nat ltac:(cbn; lia))) as Rb3.
cbn [nth] in Rb0, Rb1, Rb2, Rb3.
set (E := Eimg (Ereg regs (rd_extra b0 b1 b2 b3))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rd_extra b0 b1 b2 b3)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_RD) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 b1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 b2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 b3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 15) = Z_to_bv 64 (VAL (A_OBJ 15))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; unfold in_app in Hfapp; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HBV : forall j, (j < 4)%nat -> val_mem SEGS (rdW W memc) (p + Z.of_nat j) 1 (nth j [b0; b1; b2; b3] 0))
  by (intros j Hj; exact (proj1 (Hga j Hj))).
split.
- rewrite restrict_mkst_fx. unfold ss_rd. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rd_regions, stack_region, got_regionP, bcell_regionP, p_region, RDU32_FRAME.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold RDU32_FRAME in *. lia.
    * fold E. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 15)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * fold E. rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) Ecell) by (pose proof (pa_val_range (A_OBJ 15)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 RBx SB_RD);
      [cbn [sv_denot RBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_RD; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * fold E. rewrite (VB 10%nat p E10) by (unfold in_app in Hfapp; lia).
      split; [lia|]. split; [unfold in_app in Hfapp; lia|]. split; [intros o Ho; lia|].
      repeat constructor.
      -- apply (chunk_ok_val SEGS E _ p 0 1 (SOff 33 0) b0);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (HBV 0%nat ltac:(lia)).
      -- apply (chunk_ok_val SEGS E _ p 1 1 (SOff 34 0) b1);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (HBV 1%nat ltac:(lia)).
      -- apply (chunk_ok_val SEGS E _ p 2 1 (SOff 35 0) b2);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (HBV 2%nat ltac:(lia)).
      -- apply (chunk_ok_val SEGS E _ p 3 1 (SOff 36 0) b3);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (HBV 3%nat ltac:(lia)).
  + apply pairwise_disjoint_of_extents.
    unfold rd_regions, stack_region, got_regionP, bcell_regionP, p_region, extent_of_region, RDU32_FRAME.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) Ecell) by (pose proof (pa_val_range (A_OBJ 15)); lia).
    rewrite (VB 10%nat p E10) by (unfold in_app in Hfapp; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, in_app, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP, RDU32_FRAME in *.
    revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HcellR HgcD HgotR Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hfimg Hwlo Hwhi Hdisj HIE.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, U10, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB_RD; lia).
    try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold in_app in Hfapp.
    revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hal16 Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hwlo Hwhi Rb0 Rb1 Rb2 Rb3.
    clear. unfold SB_RD, RDU32_FRAME. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (shent_p_ok _ _ p).
  + unfold RBx. rewrite (U_atom _ 32 SB_RD E32) by (unfold SB_RD; lia). reflexivity.
  + rewrite (U_atom _ 10 p E10) by (unfold in_app in Hfapp; lia). reflexivity.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + rewrite <- (aview_rd_of SEGS). exact Hsh.
Qed.

Ltac rd_awr spv sp0v Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spv - sp0v);
    [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].

Ltac rd_frame_kept HF spv Usp UN :=
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spv - 16 <= a < spv) HF
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?Usp in HrrW; lia|]);
          destruct HinW)) as UN.

(* An env built from E by writes at slots >= 32 agrees with E below 32. *)
Ltac agree_down HA :=
  first
  [ exact HA
  | lazymatch goal with
    | |- env_agree ?k ?E0 (ewset ?X ?n ?v) =>
        apply (env_agree_trans k E0 X (ewset X n v));
        [ agree_down HA | apply (YP03.env_agree_le k n); [lia | apply env_agree_ewset] ]
    end ].

Ltac ew_down H := cbn [ew ewset Nat.eqb]; exact H.

Theorem pb_rd_u32X : trd_u32_specX SEGS B (BASE + AF_rd_u32).
Proof.
unfold trd_u32_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b0 b1 b2 b3 cid pos
  HJ Hraw H10 Hal16 Hwlo Hwhi Hin Hfa1 Hfa2 Hdisj Hga Hsh.
pose proof pa_segs_low as Hsegs.
pose proof (eq_refl RDU32_FRAME : RDU32_FRAME = 16) as HFR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
pose proof (proj2 (Hga 0%nat ltac:(cbn; lia))) as Rb0. pose proof (proj2 (Hga 1%nat ltac:(cbn; lia))) as Rb1.
pose proof (proj2 (Hga 2%nat ltac:(cbn; lia))) as Rb2. pose proof (proj2 (Hga 3%nat ltac:(cbn; lia))) as Rb3.
cbn [nth] in Rb0, Rb1, Rb2, Rb3.
destruct (rd_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b0 b1 b2 b3 cid pos
  HJ H10 Hal16 Hwlo Hwhi Hin Hfa1 Hfa2 Hdisj Hga Hsh) as [HS SHOK].
remember (Eimg (Ereg regs (rd_extra b0 b1 b2 b3))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rd_extra b0 b1 b2 b3)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 b1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 b2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 b3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (HAE : env_agree 32 (Ereg regs (rd_extra b0 b1 b2 b3)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_rd_u32)) with (Z_to_bv 64 (BASE + AF_rd_u32)).
(* The frame, the save of ra, the shadow base, the four shadow checks with their loads and the two UBSan guards,
   up to the test of swapped (0x81cd0 `beqz a1`). *)
paj_run_tok RUN HS HJ SHOK RDspan; [ rd_awr (spZ regs) sp0 Usp |].
rd_frame_kept HFr (spZ regs) Usp UN1. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (Usp1 : bv_unsigned (ew Ex 2) = spZ regs) by ew_down Usp;
  assert (E1_1 : ew Ex 1 = getr regs 1) by ew_down E1;
  assert (E1_11 : ew Ex 11 = getr regs 11) by ew_down E11;
  assert (E1_33 : ew Ex 33 = Z_to_bv 64 b0) by ew_down E33;
  assert (E1_34 : ew Ex 34 = Z_to_bv 64 b1) by ew_down E34;
  assert (E1_35 : ew Ex 35 = Z_to_bv 64 b2) by ew_down E35;
  assert (E1_36 : ew Ex 36 = Z_to_bv 64 b3) by ew_down E36;
  assert (HAE1 : env_agree 32 (Ereg regs (rd_extra b0 b1 b2 b3)) Ex) by agree_down HAE
end.
psrr_branch_tok RUN BR HS SHOK RDspan.
- (* swapped = 0: the epilogue *)
  rewrite branch_eq_U, U_SOff, U_SLit, E1_11, Z.add_0_r, zcanon_unsigned in Hc. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK RDspan; [ rd_awr (spZ regs) sp0 Usp1 |].
  rd_frame_kept HFr (spZ regs) Usp1 UN2. clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
              aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
  lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ssx (restrict _ ?msc) |- _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (rd_extra b0 b1 b2 b3)) E2) by agree_down HAE;
    pose proof (st_ok_pi_restrict_reg _ E2 ssx msc 1%bv HS) as R1;
    pose proof (st_ok_pi_restrict_reg _ E2 ssx msc 10%bv HS) as R10;
    let e1 := eval vm_compute in (sr_get (ss_regs ssx) 1%bv) in change (sr_get (ss_regs ssx) 1%bv) with e1 in R1;
    change (sr_get (ss_regs ssx) 10%bv) with RV_NOSWAP in R10;
    cbn [sv_denot] in R1; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1;
    assert (R1' : getr (ms_regs msc) 1 = getr regs 1) by (rewrite R1; ew_down E1);
    rewrite (rv_noswap_val E2 b0 b1 b2 b3 ltac:(ew_down E33) ltac:(ew_down E34) ltac:(ew_down E35)
               ltac:(ew_down E36) Rb0 Rb1 Rb2 Rb3) in R10;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold trd_u32_post;
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [reflexivity|];
    split; [cbn [ms_regs]; rewrite R1'; unfold YK0s.ret_ok in Hraw; rewrite Hraw; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E2 _ _ regs (rd_extra b0 b1 b2 b3) HS); [exact HAE2 | vm_compute; reflexivity]|];
    split; [rewrite R10; unfold rd_u32_val; rewrite Hc; reflexivity|];
    split; [repeat rewrite (proj1 (rd_wvb_fds_fs _ _ _)); reflexivity|];
    split; [repeat rewrite (proj2 (rd_wvb_fds_fs _ _ _)); reflexivity|];
    split;
    [ apply (garr8_frame SEGS (rdW W memc) _ _ _ Hga); intros a Ha; apply (mbyte_of_aview SEGS); apply UN;
      [cbn [length] in Ha; unfold in_app in Hfapp; lia | unfold RDU32_FRAME in *; cbn [length] in Ha; lia]
    | intros a Ha Hna; apply UN; [exact Ha | unfold RDU32_FRAME in Hna; exact Hna] ]
  end.
- (* swapped <> 0: the byte swap and the epilogue *)
  rewrite branch_eq_U, U_SOff, U_SLit, E1_11, Z.add_0_r, zcanon_unsigned in Hc. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK RDspan; [ rd_awr (spZ regs) sp0 Usp1 |].
  rd_frame_kept HFr (spZ regs) Usp1 UN2. clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
              aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
  lazymatch goal with HS : st_ok_pi _ _ ?E2 ?ssx (restrict _ ?msc) |- _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (rd_extra b0 b1 b2 b3)) E2) by agree_down HAE;
    pose proof (st_ok_pi_restrict_reg _ E2 ssx msc 1%bv HS) as R1;
    pose proof (st_ok_pi_restrict_reg _ E2 ssx msc 10%bv HS) as R10;
    let e1 := eval vm_compute in (sr_get (ss_regs ssx) 1%bv) in change (sr_get (ss_regs ssx) 1%bv) with e1 in R1;
    change (sr_get (ss_regs ssx) 10%bv) with RV_SWAP in R10;
    cbn [sv_denot] in R1; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1;
    assert (R1' : getr (ms_regs msc) 1 = getr regs 1) by (rewrite R1; ew_down E1);
    rewrite (rv_swap_val E2 b0 b1 b2 b3 ltac:(ew_down E33) ltac:(ew_down E34) ltac:(ew_down E35)
               ltac:(ew_down E36) Rb0 Rb1 Rb2 Rb3) in R10;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold trd_u32_post;
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [reflexivity|];
    split; [cbn [ms_regs]; rewrite R1'; unfold YK0s.ret_ok in Hraw; rewrite Hraw; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E2 _ _ regs (rd_extra b0 b1 b2 b3) HS); [exact HAE2 | vm_compute; reflexivity]|];
    split; [rewrite R10; unfold rd_u32_val; replace (bv_unsigned (getr regs 11) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc); reflexivity|];
    split; [repeat rewrite (proj1 (rd_wvb_fds_fs _ _ _)); reflexivity|];
    split; [repeat rewrite (proj2 (rd_wvb_fds_fs _ _ _)); reflexivity|];
    split;
    [ apply (garr8_frame SEGS (rdW W memc) _ _ _ Hga); intros a Ha; apply (mbyte_of_aview SEGS); apply UN;
      [cbn [length] in Ha; unfold in_app in Hfapp; lia | unfold RDU32_FRAME in *; cbn [length] in Ha; lia]
    | intros a Ha Hna; apply UN; [exact Ha | unfold RDU32_FRAME in Hna; exact Hna] ]
  end.
Qed.

End e.
End d.
End b.

(* The sink-head instance is explicit on every exported statement and theorem (a Theorem Labs lane, 21:57Z). *)
Arguments trd_u32_post {fx rc} SK.
Arguments trd_u32_specX {fx rc} SK.
Arguments pb_rd_u32X {fx rc} SK {PI}.

(* GUARD: SK must stay explicit. SK is passed by position; were it implicit again, the positional SK
   would land on the next argument and this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment) (B : asyms) (a : Z) =>
  trd_u32_specX (fx:=fx) (rc:=rc) SK segs B a : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  trd_u32_post (fx:=fx) (rc:=rc) SK).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pb_rd_u32X (fx:=fx) (rc:=rc) SK (PI:=PI)).
Print Assumptions pb_rd_u32X.
