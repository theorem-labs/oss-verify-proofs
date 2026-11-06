(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: rd32 of fuzz/fuzz_pcap.c:72-77 (libreac v1.9.0) on fuzz_pcap.asan-ubsan
   (pin sha256 9e66f771f22a..., 0x81060, size 0x118 = 70 instructions, listing offset AF_rd32 = 0x8d8 of
   lib/B/Prog/PcapList.v): the contract of the code (trd32_specX) and its walk (pb_rd32X).

   The C: `static uint32_t rd32(const uint8_t *p, int swap)` returns v = p[0] | p[1] << 8 | p[2] << 16 | p[3] << 24, or
   __builtin_bswap32(v) when swap is not zero. The ASan build (fuzz_pcap.asan) inlines it; the asan-ubsan build keeps
   it out of line and LLVMFuzzerTestOneInput calls it at 0x80a38, 0x80ba4, 0x80bf8, 0x80d58, 0x80d7c and 0x80fe0, always
   with p in the private copy of the input (file, file + at + {0, 4, 8, 12}, file + e + 8;
   pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record) row G7).

   The code (capstone disassembly of the pin): a 16-byte machine frame (0x81060 `addi sp,sp,-16`, 0x81064 `sd ra,8(sp)`),
   no ASan frame and no call except the four `__asan_report_load1` slow paths. Three UBSan guards branch to the `unimp`
   at 0x81138: 0x81068 `beqz a0` (p null), 0x8108c `beq a0,-1` (p + 1 wraps) and 0x810b0 `bltu a2(=p+3),2` (p + 2 or
   p + 3 wraps). The shadow base is loaded through the GOT word of object 1 (0x8106c `auipc`, 0x81070 `ld`) from its
   cell, object 15 (0x81074 `ld a4,0(a2)`). Each byte p + i (i = 0..3) has its own shadow check: the shadow byte load
   (0x81080, 0x8109c, 0x810c0, 0x810d4 `lb`) and its `bnez` (0x81084, 0x810a4, 0x810c8, 0x810dc) into a slow block
   (`andi _,x,7`; `blt` back; `jal __asan_report_load1`) at 0x8113c, 0x81148, 0x81158, 0x81168. The bytes are loaded
   by 0x810a0, 0x810c4, 0x810d8 and 0x810e4 `lbu`; 0x810e0 .. 0x810f8 form v (the last term by `slliw`, so a0 holds v
   sign-extended from bit 31), 0x810fc `beqz a1` keeps it, and otherwise 0x81100 .. 0x81128 swap the four bytes (again
   sign-extended from bit 31, by `slliw`). The function then restores ra (0x8112c), releases the frame and returns
   (0x81134). It reads no other memory and writes only its own frame word [sp - 8, sp). It does not read the
   use-after-return flag __asan_option_detect_stack_use_after_return (object 16, GOT word object 0): its only GOT
   load is object 1's (0x81070) and its only cell load object 15's (0x81074), so the walk has no region for objects 0
   and 16 and no premise on the flag's value.

   THE WALK (the kit's method of lib/A/Prog/PcapSourceClose.v: PaRun / PaShadow token runs over the lib/B listing,
   PcapPaLib's paj_run_tok / psrr_branch_tok / paj_ret_at). rd_entry builds the start state ss_rd and the shadow
   entry rd_SH = [mkSHE 10 0 4] from the pre. The first run goes from 0x81060 to the swap test 0x810fc and decides,
   with no obligation left:
     0x81068 `beqz a0` (null): decide_cond2 (Reusable/YP0e.v:932-936) -> decide_eq (Reusable/YP0m.v:665-666): p's fact
              [4096, alloc_ceiling - 4] is disjoint from 0, not taken; template lib/U/Prog/rd32f.v:31 (if_false, the
              premise bv_unsigned a0 <> 0 of rd32f_c.v);
     0x8108c `beq a0,a2(=-1)` (p + 1 wraps): the same range test, p's fact is disjoint from 2^64 - 1, not taken;
              template rd32f.v:32 (first if_false; rd_u32.v:31 first if_false, rd_u32.v:19 bytes_at_bound);
     0x810b0 `bltu a2(=p+3),a3(=2)`: decide_ltu's range test (Reusable/YP0m.v:675): p + 3 >= 4099, not taken;
              template rd32f.v:32 (second if_false; rd_u32.v:31 second if_false);
     0x81084, 0x810a4, 0x810c8, 0x810dc (the shadow checks of p .. p + 3): PaShadow's token branch (PaShadow.v:38 (sha256 0c4d47929598; internal record),
              Reusable/YCbn.v:213 slow_block matches each slow block's `andi _,x,7` / `blt` back) with need
              (Reusable/YCbn.v:150) covered by rd_SH, whose sh_ok rd_entry proves from the live block
              (Reusable/YCbq.v:2685 range_addressable_of_block, :2694 shent_ok_of_range); template: the kit's shadow
              entry of lib/A/Prog/PcapSourceClose.v (cl_SH :283, shent_ps_ok :332-342). The released U proofs have no
              ASan, so no U template exists for these.
   psrr_branch_tok then splits on 0x810fc `beqz a1`, a second run in each arm reaches the `ret`, and paj_ret_at closes
   the post; the value of a0 (RD_LE / RD_BE) is rd_U_le / rd_U_be.

   The contract is in the caller-journal form of lib/A/Prog/PcapSourceClose.v (tpcap_source_close_specX): the premise
   is the caller's journal, the post extends the same journal, here with the same layout, allocator state and event
   count (rd32 allocates nothing and takes no side-stack frame). It is image-generic (a Theorem Labs lane's ruling): the
   segments `segs`, the runtime's symbols `B` and the function's address `a` are parameters, and no PAImg instance
   appears; rd32 reads no read-only data, so the relro window is not a parameter. The sink-head instance SK is explicit
   (ajournal reads it through fp_spares), as in PcapSourceClose.v.

   The premise on p: the four bytes lie in a live heap block, In (b, n) (ablocks B lyc Sc) with b <= p and
   p + 4 <= b + n (the callers' fact for the input copy). AR's block laws then give everything the guards and the
   shadow checks need: 4096 <= b (so p <> 0, the null guard), b + req_size n <= alloc_ceiling (so p + 4 is far from
   2 ^ 64, the two wrap guards) and the block's shadow marks [b, b + n) addressable (YCbq.v range_addressable_of_block,
   the four shadow checks). Statement class R1 (a Theorem Labs lane, widened by a second lane): the bytes read are in a
   live block of the caller's current state (the live-block arm), every live block lies below alloc_ceiling
   (al_blocks) and the callee's frame [sp - RD32_FRAME, sp), the only bytes rd32 writes, lies in the caller's journal
   window, above alloc_ceiling (astk_ok), so the pre implies the bytes are disjoint from every byte the callee writes;
   the post keeps them (its last clause) and states memory unchanged outside the callee's frame.

   rule 24 (index v5, 2026-10-28T21:58:24Z): `proof-index rd32` rc=3 (0 named); rd_u32 and rd32f name the
   released v1.8 UBSan proofs lib/U/Prog/rd_u32.v and lib/U/Prog/rd32f.v (v1.8 ubsan rd32 at 0x131a8, RD32F of
   lib/U/Prog/rd32f_c.v:11, 29 instructions, no ASan). A Theorem Labs lane (22:25Z) CONFIRMED a new proof: the v1.9.0 asan-ubsan
   body differs from instruction 0. The released files are templates for the UBSan guard decisions (rd32f.v:31-32)
   and for the value (rd_u32_c.v rd_val: the same byte order and the same sign extension, bv_swrap 32). *)
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

(* The stack the call needs: its own 16-byte machine frame (0x81060 `addi sp,sp,-16`); it calls nothing. *)
Definition RD32_FRAME : Z := 16.

(* The value of the four bytes c0 .. c3 at p, as 0x810e0 .. 0x81128 compute it: little-endian when the 64-bit a1 is
   zero (0x810fc `beqz a1`), byte-swapped otherwise. The return register holds it sign-extended from bit 31. *)
Definition trd32_val (sw : word) (c0 c1 c2 c3 : Z) : Z :=
  if bv_eqb sw (Z_to_bv 64 0) then c0 + 256 * c1 + 65536 * c2 + 16777216 * c3
  else c3 + 256 * c2 + 65536 * c1 + 16777216 * c0.

(* ---- the value: the two register expressions the walk's runs leave in a0, and their values ------------------- *)
Lemma rd_land_disj : forall a b k q, 0 <= k -> 0 <= a < 2 ^ k -> b = q * 2 ^ k -> Z.land a b = 0.
Proof.
intros a b k q Hk Ha Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hik | Hik].
- replace (Z.testbit b i) with false; [apply andb_false_r|].
  subst b. symmetry. apply Z.mul_pow2_bits_low. lia.
- replace (Z.testbit a i) with false; [reflexivity|].
  rewrite <- (Z.mod_small a (2 ^ k)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma rd_lor_disj : forall a b k q, 0 <= k -> 0 <= a < 2 ^ k -> b = q * 2 ^ k -> Z.lor a b = a + b.
Proof.
intros a b k q Hk Ha Hb. pose proof (rd_land_disj a b k q Hk Ha Hb) as H0.
rewrite <- Z.lxor_lor by exact H0. symmetry. apply Z.add_nocarry_lxor. exact H0.
Qed.

Lemma rd_land_ff00 : forall x, Z.land x 65280 = (x / 2 ^ 8) mod 2 ^ 8 * 2 ^ 8.
Proof.
intros x. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec. change 65280 with (Z.shiftl (Z.ones 8) 8).
rewrite Z.mul_pow2_bits by lia. rewrite Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 8) as [H8 | H8].
- rewrite !(Z.testbit_neg_r _ (i - 8)) by lia. apply andb_false_r.
- destruct (Z.lt_ge_cases i 16) as [H16 | H16].
  + rewrite Z.ones_spec_low by lia. rewrite andb_true_r.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia. f_equal. lia.
  + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma rd_sx32 : forall z, 0 <= z < 2 ^ 32 ->
  zcanon (bv_swrap 32 z) = z + (if z <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32).
Proof.
intros z Hz. unfold zcanon, M64, bv_swrap, bv_wrap.
assert (EM : bv_modulus 32 = 2 ^ 32) by reflexivity. assert (EH : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
rewrite EM, EH.
destruct (Z.ltb_spec z (2 ^ 31)).
- rewrite (Z.mod_small (z + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
- replace ((z + 2 ^ 31) mod 2 ^ 32) with (z + 2 ^ 31 - 2 ^ 32) by (apply (Z.mod_unique _ _ 1); lia).
  replace ((z + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (z - 2 ^ 32 + 2 ^ 64)
    by (apply (Z.mod_unique _ _ (-1)); lia).
  lia.
Qed.

Lemma rd_swrap32_add : forall a k, bv_swrap 32 (a + 2 ^ 32 * k) = bv_swrap 32 a.
Proof.
intros a k. unfold bv_swrap, bv_wrap.
assert (EM : bv_modulus 32 = 2 ^ 32) by reflexivity. rewrite EM.
replace (a + 2 ^ 32 * k + bv_half_modulus 32) with (a + bv_half_modulus 32 + k * 2 ^ 32) by ring.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rd_swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap.
assert (EM : bv_modulus 32 = 2 ^ 32) by reflexivity. assert (EH : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
rewrite EM, EH. rewrite Z.mod_small by lia. lia.
Qed.

(* The symbolic values of the registers at the return, as the walk's runs leave them. *)
Definition RD_LO : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 33 0)) (SAlu ALU_SLL (SOff 35 0) (SLit 16)).
Definition RD_C3 : sv := SAluw ALU_SLL (SOff 36 0) (SLit 24).
Definition RD_LE : sv := SAlu ALU_OR RD_LO RD_C3.
Definition RD_BE : sv :=
  SAlu ALU_OR
    (SAlu ALU_OR (SAluw ALU_SLL RD_LO (SLit 24)) (SAlu ALU_SLL (SAlu ALU_AND RD_LE (SLit 65280)) (SLit 8)))
    (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL RD_LO (SLit 16)) (SLit 8)) (SAluw ALU_SRL RD_C3 (SLit 24))).

Section v.
Variable E : env.
Variables c0 c1 c2 c3 : Z.
Hypothesis H0 : ew E 33 = Z_to_bv 64 c0.
Hypothesis H1 : ew E 34 = Z_to_bv 64 c1.
Hypothesis H2 : ew E 35 = Z_to_bv 64 c2.
Hypothesis H3 : ew E 36 = Z_to_bv 64 c3.
Hypothesis R0 : 0 <= c0 < 256.
Hypothesis R1 : 0 <= c1 < 256.
Hypothesis R2 : 0 <= c2 < 256.
Hypothesis R3 : 0 <= c3 < 256.

Lemma rd_U_atoms : U E (SOff 33 0) = c0 /\ U E (SOff 34 0) = c1 /\ U E (SOff 35 0) = c2 /\ U E (SOff 36 0) = c3.
Proof. repeat split; apply U_atom; first [assumption | lia]. Qed.

Lemma rd_U_sll : forall n c k, ew E n = Z_to_bv 64 c -> 0 <= c < 256 -> 0 <= k < 63 -> c * 2 ^ k < 2 ^ 64 ->
  U E (SAlu ALU_SLL (SOff n 0) (SLit k)) = c * 2 ^ k.
Proof.
intros n c k Hn Hc Hk Hlt. rewrite U_SAlu, (U_atom E n c Hn) by lia. rewrite U_lit by lia. cbn [zalu_raw].
replace (Z.land k 63) with k
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia); lia.
Qed.

Lemma rd_U_lo : U E RD_LO = c0 + 2 ^ 8 * c1 + 2 ^ 16 * c2.
Proof.
destruct rd_U_atoms as (A0 & A1 & A2 & A3).
unfold RD_LO. rewrite U_SAlu. rewrite U_SAlu.
rewrite (rd_U_sll 34 c1 8 H1 R1) by lia. rewrite (rd_U_sll 35 c2 16 H2 R2) by lia. rewrite A0. cbn [zalu_raw].
rewrite (Z.lor_comm (c1 * 2 ^ 8) c0), (rd_lor_disj c0 (c1 * 2 ^ 8) 8 c1) by lia.
rewrite (zcanon_id (c0 + c1 * 2 ^ 8)) by (unfold M64; lia).
rewrite (rd_lor_disj (c0 + c1 * 2 ^ 8) (c2 * 2 ^ 16) 16 c2) by lia.
rewrite zcanon_id by (unfold M64; lia). ring.
Qed.

Definition rd_h (z : Z) : Z := if z <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32.

Lemma rd_U_c3 : U E RD_C3 = c3 * 2 ^ 24 + rd_h (c3 * 2 ^ 24).
Proof.
destruct rd_U_atoms as (A0 & A1 & A2 & A3).
unfold RD_C3. rewrite U_of_S, S_SAluw, A3, U_lit by lia. cbn [zalu_raw].
rewrite (Z.mod_small c3) by lia. change (24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
rewrite Z.shiftl_mul_pow2 by lia. rewrite <- zcanon_wrap. apply rd_sx32. lia.
Qed.

Lemma rd_U_le : U E RD_LE = zcanon (bv_swrap 32 (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3)).
Proof.
unfold RD_LE. rewrite U_SAlu, rd_U_lo, rd_U_c3. cbn [zalu_raw].
rewrite rd_sx32 by lia. unfold rd_h.
destruct (Z.ltb_spec (c3 * 2 ^ 24) (2 ^ 31)) as [Hc | Hc];
destruct (Z.ltb_spec (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3) (2 ^ 31)) as [Hv | Hv]; try lia.
- rewrite (rd_lor_disj _ _ 24 c3) by lia. rewrite zcanon_id by (unfold M64; lia); lia.
- rewrite (rd_lor_disj _ _ 24 (c3 + 2 ^ 40 - 2 ^ 8)) by lia. rewrite zcanon_id by (unfold M64; lia); lia.
Qed.

Lemma rd_U_be : U E RD_BE = zcanon (bv_swrap 32 (c3 + 256 * c2 + 65536 * c1 + 16777216 * c0)).
Proof.
pose proof rd_U_lo as ULO. pose proof rd_U_c3 as UC3. pose proof rd_U_le as ULE.
rewrite rd_sx32 in ULE by lia.
(* the high byte: c0 << 24, sign-extended from bit 31 *)
assert (X1 : U E (SAluw ALU_SLL RD_LO (SLit 24)) = c0 * 2 ^ 24 + rd_h (c0 * 2 ^ 24)).
{ rewrite U_of_S, S_SAluw, ULO, U_lit by lia. cbn [zalu_raw].
  rewrite (Z.mod_small (c0 + 2 ^ 8 * c1 + 2 ^ 16 * c2)) by lia.
  change (24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((c0 + 2 ^ 8 * c1 + 2 ^ 16 * c2) * 2 ^ 24) with (c0 * 2 ^ 24 + 2 ^ 32 * (c1 + 2 ^ 8 * c2)) by ring.
  rewrite rd_swrap32_add. rewrite <- zcanon_wrap. apply rd_sx32. lia. }
(* c1 << 16, from the AND with 0xff00 and the shift *)
assert (X2 : U E (SAlu ALU_SLL (SAlu ALU_AND RD_LE (SLit 65280)) (SLit 8)) = c1 * 2 ^ 16).
{ assert (XA : U E (SAlu ALU_AND RD_LE (SLit 65280)) = c1 * 2 ^ 8).
  { rewrite U_SAlu, ULE, U_lit by lia. cbn [zalu_raw]. rewrite rd_land_ff00.
    set (V := c0 + 256 * c1 + 65536 * c2 + 16777216 * c3).
    assert (EQ : (V + (if V <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32)) / 2 ^ 8 mod 2 ^ 8 = c1).
    { destruct (Z.ltb_spec V (2 ^ 31)) as [Hv | Hv].
      - replace ((V + 0) / 2 ^ 8) with (c1 + 2 ^ 8 * (c2 + 2 ^ 8 * c3)) by (apply (Z.div_unique _ _ _ c0); subst V; lia).
        symmetry. apply (Z.mod_unique _ _ (c2 + 2 ^ 8 * c3)); lia.
      - replace ((V + (2 ^ 64 - 2 ^ 32)) / 2 ^ 8) with (c1 + 2 ^ 8 * (c2 + 2 ^ 8 * c3 + 2 ^ 48 - 2 ^ 16))
          by (apply (Z.div_unique _ _ _ c0); subst V; lia).
        symmetry. apply (Z.mod_unique _ _ (c2 + 2 ^ 8 * c3 + 2 ^ 48 - 2 ^ 16)); lia. }
    rewrite EQ. rewrite zcanon_id by (unfold M64; lia); lia. }
  rewrite U_SAlu, XA, U_lit by lia. cbn [zalu_raw]. change (Z.land 8 63) with 8.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia); lia. }
(* c2 << 8, from the logical shift right by 16 and the shift left by 8 *)
assert (X3 : U E (SAlu ALU_SLL (SAlu ALU_SRL RD_LO (SLit 16)) (SLit 8)) = c2 * 2 ^ 8).
{ assert (XS : U E (SAlu ALU_SRL RD_LO (SLit 16)) = c2).
  { rewrite U_SAlu, ULO, U_lit by lia. cbn [zalu_raw]. change (Z.land 16 63) with 16.
    rewrite Z.shiftr_div_pow2 by lia.
    replace ((c0 + 2 ^ 8 * c1 + 2 ^ 16 * c2) / 2 ^ 16) with c2 by (apply (Z.div_unique _ _ _ (c0 + 2 ^ 8 * c1)); lia).
    rewrite zcanon_id by (unfold M64; lia); lia. }
  rewrite U_SAlu, XS, U_lit by lia. cbn [zalu_raw]. change (Z.land 8 63) with 8.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia); lia. }
(* c3, from the 32-bit logical shift right by 24 *)
assert (X4 : U E (SAluw ALU_SRL RD_C3 (SLit 24)) = c3).
{ rewrite U_of_S, S_SAluw, UC3, U_lit by lia. cbn [zalu_raw].
  replace ((c3 * 2 ^ 24 + rd_h (c3 * 2 ^ 24)) mod 2 ^ 32) with (c3 * 2 ^ 24).
  2:{ unfold rd_h. destruct (Z.ltb_spec (c3 * 2 ^ 24) (2 ^ 31)).
      - rewrite Z.add_0_r. symmetry. apply Z.mod_small. lia.
      - apply (Z.mod_unique _ _ (2 ^ 32 - 1)); lia. }
  change (24 mod 2 ^ 32) with 24. change (Z.land 24 31) with 24.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
  rewrite rd_swrap32_small by lia. rewrite <- zcanon_wrap. rewrite zcanon_id by (unfold M64; lia); lia. }
unfold RD_BE. rewrite U_SAlu. rewrite (U_SAlu E ALU_OR (SAluw _ _ _)). rewrite (U_SAlu E ALU_OR (SAlu ALU_SLL _ _)).
rewrite X1, X2, X3, X4. cbn [zalu_raw].
rewrite (Z.lor_comm (c2 * 2 ^ 8) c3), (rd_lor_disj c3 (c2 * 2 ^ 8) 8 c2) by lia.
rewrite (zcanon_id (c3 + c2 * 2 ^ 8)) by (unfold M64; lia).
rewrite rd_sx32 by lia.
assert (Hh : (rd_h (c0 * 2 ^ 24) = 0 /\ c0 < 128) \/ (rd_h (c0 * 2 ^ 24) = 2 ^ 64 - 2 ^ 32 /\ 128 <= c0))
  by (unfold rd_h; destruct (Z.ltb_spec (c0 * 2 ^ 24) (2 ^ 31)); lia).
destruct Hh as [[Eh Hc0] | [Eh Hc0]]; rewrite Eh.
- rewrite (Z.lor_comm (c0 * 2 ^ 24 + 0) (c1 * 2 ^ 16)), (rd_lor_disj (c1 * 2 ^ 16) (c0 * 2 ^ 24 + 0) 24 c0) by lia.
  rewrite (zcanon_id (c1 * 2 ^ 16 + (c0 * 2 ^ 24 + 0))) by (unfold M64; lia).
  rewrite (Z.lor_comm (c1 * 2 ^ 16 + (c0 * 2 ^ 24 + 0)) (c3 + c2 * 2 ^ 8)).
  rewrite (rd_lor_disj (c3 + c2 * 2 ^ 8) _ 16 (c1 + 2 ^ 8 * c0)) by lia.
  destruct (Z.ltb_spec (c3 + 256 * c2 + 65536 * c1 + 16777216 * c0) (2 ^ 31)); [|lia]. cbv iota.
  rewrite zcanon_id by (unfold M64; lia). lia.
- rewrite (Z.lor_comm (c0 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)) (c1 * 2 ^ 16)).
  rewrite (rd_lor_disj (c1 * 2 ^ 16) (c0 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)) 24 (c0 + 2 ^ 40 - 2 ^ 8)) by lia.
  rewrite (zcanon_id (c1 * 2 ^ 16 + (c0 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32)))) by (unfold M64; lia).
  rewrite (Z.lor_comm (c1 * 2 ^ 16 + (c0 * 2 ^ 24 + (2 ^ 64 - 2 ^ 32))) (c3 + c2 * 2 ^ 8)).
  rewrite (rd_lor_disj (c3 + c2 * 2 ^ 8) _ 16 (c1 + 2 ^ 8 * c0 + 2 ^ 48 - 2 ^ 16)) by lia.
  destruct (Z.ltb_spec (c3 + 256 * c2 + 65536 * c1 + 16777216 * c0) (2 ^ 31)); [lia|]. cbv iota.
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End v.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section s.
Variable segs : list Segment.
Variable B : asyms.

(* The post: the same world, the return to ra, the caller's journal at the same layout, allocator state and event
   count (so the meter, the blocks and the frames are unchanged), the callee-saved registers (sp among them)
   restored, a0 the value sign-extended from bit 31, the model changed only by the VM backing's materialisation,
   every byte outside the callee's frame [sp - RD32_FRAME, sp) unchanged, and the four bytes read kept (statement
   class R1: they lie in a live block, and every live block is below alloc_ceiling, the callee's frame above it). *)
Definition trd32_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (p : Z) (cs : list Z) (v : Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists regs2 mem2 md2,
  W2 = W /\
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
  aregs_preserved regs regs2 /\
  getr regs2 10 = w64 (bv_swrap 32 v) /\
  same_but_materialized mdc md2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD32_FRAME <= a < spZ regs) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
  garr8 segs (rdW W mem2) p cs.

(* The contract at the function's address a: a0 = p, a1 = the swap flag, the four bytes c0 .. c3 at p inside a live
   heap block of the caller's current state, and the callee's frame inside the caller's journal window. *)
Definition trd32_specX (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p b n c0 c1 c2 c3 : Z),
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RD32_FRAME -> spZ regs <= sp0 ->
  (* the four bytes, in a live block: the null and wrap guards and the shadow checks follow from AR *)
  In (b, n) (ablocks B lyc Sc) -> b <= p -> p + 4 <= b + n ->
  garr8 segs (rdW W memc) p [c0; c1; c2; c3] ->
  SRr segs W (cfg_at segs a regs memc mdc)
    (trd32_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p [c0; c1; c2; c3]
       (trd32_val (getr regs 11) c0 c1 c2 c3)).

End s.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).

Section e.
Variable B : asyms.

(* The symbolic start state at 0x81060: sp (atom 2) in [2^46, 2^47] 16-aligned, p (atom 10) in
   [4096, alloc_ceiling - 4], the shadow base (atom 32) and the four bytes (atoms 33 .. 36); the regions are the
   callee's frame [sp - 16, sp), the GOT word of object 1, its cell (object 15, holding the shadow base) and the four
   bytes at p (read-only); the shadow entry says [p, p + 4) is addressable. *)
Definition SB_RD : Z := 0x7fff8000.
Definition RBx : sv := SOff 32 0.
Definition RDspan : Z * Z := (SB_RD, SB_RD + 2 ^ 44 - 1).
Definition p_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0));
   YP09.mkChunk 2 (CVal 1 (SOff 35 0)); YP09.mkChunk 3 (CVal 1 (SOff 36 0))].
Definition rd_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32; p_region].
Definition rd_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (140737479966720 - 4) 0); (32%nat, mkAF SB_RD SB_RD 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)] [] [].
Definition ss_rd : sstate := mkSS AF_rd32 sr_atoms rd_regions None rd_facts.
Definition rd_SH : list shent := [mkSHE 10 0 4].
Definition rd_extra (c0 c1 c2 c3 : Z) : list word := map (Z_to_bv 64) [SB_RD; c0; c1; c2; c3].

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).

(* Statement class R1: the bytes read lie below the callee's frame, the only bytes rd32 writes. *)
Lemma rd32_bytes_below_frame : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp b n p,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= sp - RD32_FRAME -> In (b, n) (ablocks B lyc Sc) -> b <= p -> p + 4 <= b + n ->
  p + 4 <= sp - RD32_FRAME.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp b n p HJ Hw Hin Hbp Hpn.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hin) as (_ & _ & Hbceil & _ & _ & _ & Hn).
pose proof (req_size_pos0 n ltac:(lia)) as [_ Hrq]. lia.
Qed.

Lemma rd_garr8_4 : forall (m : word -> option byte) p c0 c1 c2 c3, garr8 SEGS m p [c0; c1; c2; c3] ->
  (val_mem SEGS m p 1 c0 /\ val_mem SEGS m (p + 1) 1 c1 /\ val_mem SEGS m (p + 2) 1 c2 /\ val_mem SEGS m (p + 3) 1 c3) /\
  (0 <= c0 < 256 /\ 0 <= c1 < 256 /\ 0 <= c2 < 256 /\ 0 <= c3 < 256).
Proof.
intros m p c0 c1 c2 c3 H.
destruct (H 0%nat ltac:(cbn; lia)) as [V0 R0]. destruct (H 1%nat ltac:(cbn; lia)) as [V1 R1].
destruct (H 2%nat ltac:(cbn; lia)) as [V2 R2]. destruct (H 3%nat ltac:(cbn; lia)) as [V3 R3].
cbn [nth] in V0, V1, V2, V3, R0, R1, R2, R3.
change (Z.of_nat 0) with 0 in V0. change (Z.of_nat 1) with 1 in V1.
change (Z.of_nat 2) with 2 in V2. change (Z.of_nat 3) with 3 in V3. rewrite Z.add_0_r in V0.
repeat split; first [assumption | lia].
Qed.

Lemma rd_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p b n c0 c1 c2 c3,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 p ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RD32_FRAME -> spZ regs <= sp0 ->
  In (b, n) (ablocks B lyc Sc) -> b <= p -> p + 4 <= b + n ->
  garr8 SEGS (rdW W memc) p [c0; c1; c2; c3] ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (rd_extra c0 c1 c2 c3))) ss_rd
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rd32)) memc (seg_rom SEGS))) /\
  sh_ok SEGS RBx rd_SH (Eimg (Ereg regs (rd_extra c0 c1 c2 c3))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b n c0 c1 c2 c3
  HJ H10 Hal16 Hwlo Hwhi Hin Hbp Hpn Hgb.
pose proof (rd32_bytes_below_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) b n p
  HJ Hwlo Hin Hbp Hpn) as Hbelow.
unfold RD32_FRAME in *.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hn).
pose proof (req_size_pos0 n ltac:(lia)) as [Hrq0 Hrq1].
pose proof (blk_off_imgP B lyc Sc W memc mdc b n HAR Hin) as Hboff. unfold off_img in Hboff.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 15 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 1)) as HgotV. pose proof (pa_val_range (A_OBJ 15)) as HcellV.
unfold pcap_img_end, YImgTop.IMG_TOP in HgotR, HcellR. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hboff.
destruct (rd_garr8_4 _ _ _ _ _ _ Hgb) as ((V0 & V1 & V2 & V3) & (B0 & B1 & B2 & B3)).
set (E := Eimg (Ereg regs (rd_extra c0 c1 c2 c3))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (rd_extra c0 c1 c2 c3)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_RD) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 c3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 15) = Z_to_bv 64 (VAL (A_OBJ 15))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
assert (VB : forall i v, ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some i) = v).
{ intros i v Hi Hv. cbn [base_val]. rewrite Hi. apply unsigned_lit_small. exact Hv. }
assert (Hchunk : forall (j : Z) (a : nat) (c : Z), ew E a = Z_to_bv 64 c -> 0 <= c < 256 ->
          val_mem SEGS (mrestrict (w_H W) memc) (p + j) 1 c ->
          YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) p (YP09.mkChunk j (CVal 1 (SOff a 0)))).
{ intros j a c Ha Hc Hv. apply (chunk_ok_val SEGS E _ p j 1 (SOff a 0) c);
  [cbn [sv_denot]; rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Hv]. }
split.
- rewrite restrict_mkst_fx. unfold ss_rd. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rd_regions, stack_region, got_regionP, bcell_regionP, p_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
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
    * fold E. rewrite (VB 10%nat p E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [apply (Hchunk 0 33%nat c0 E33 B0); rewrite Z.add_0_r; exact V0|].
      apply Forall_cons; [exact (Hchunk 1 34%nat c1 E34 B1 V1)|].
      apply Forall_cons; [exact (Hchunk 2 35%nat c2 E35 B2 V2)|].
      apply Forall_cons; [exact (Hchunk 3 36%nat c3 E36 B3 V3)|].
      apply Forall_nil.
  + apply pairwise_disjoint_of_extents.
    unfold rd_regions, stack_region, got_regionP, bcell_regionP, p_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 15) (VAL (A_OBJ 15)) Ecell) by (pose proof (pa_val_range (A_OBJ 15)); lia).
    rewrite (VB 10%nat p E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hceil C1 HcellR HgcD HgotR Hb4096 Hbceil Hrq1 Hboff Hbp Hpn Hwlo Hwhi Hbelow.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, U10, E32, E33, E34, E35, E36.
    rewrite !unsigned_lit_small by (unfold SB_RD; lia).
    try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 Hstk0 Hal16 Hb4096 Hbceil Hrq1 Hbp Hpn Hwlo Hwhi B0 B1 B2 B3.
    clear. unfold SB_RD. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, rd_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) memc E RBx 10%nat p 4 p 0 4).
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc b n p 4 HAR Hin ltac:(lia) ltac:(lia)).
  + unfold RBx. rewrite (U_atom _ 32 SB_RD E32) by (unfold SB_RD; lia). reflexivity.
  + rewrite (U_atom _ 10 p E10) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
Qed.

(* The write windows of the runs: only the callee's frame [sp - 16, sp), inside the caller's journal window. *)
Ltac rd_awr spv sp0v Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spv - sp0v);
    [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].

(* What a run keeps: every byte outside the callee's frame. *)
Ltac rd_frame_kept HF spv Usp UN :=
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spv - 16 <= a < spv) HF
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW; rewrite ?Usp in HrrW; lia|]);
          destruct HinW)) as UN.

(* An env the runs extend (ewset at the token slots, all >= 512) agrees with the entry env below 512. *)
Ltac rd_ew_old H := cbn [ew ewset Nat.eqb]; exact H.
Ltac rd_agree HAE :=
  split; [ intros ?i ?Hi; cbn [ew ewset];
           repeat match goal with |- context [Nat.eqb ?x ?m] => destruct (Nat.eqb_spec x m); [lia|] end;
           apply (proj1 HAE); assumption
         | cbn [ed ewset]; exact (proj2 HAE) ].

Lemma rd_w64_zcanon : forall z, Z_to_bv 64 (zcanon z) = w64 z.
Proof.
intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod.
Qed.

Theorem pb_rd32X : trd32_specX SEGS B (BASE + AF_rd32).
Proof.
unfold trd32_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b n c0 c1 c2 c3
  HJ Hraw H10 Hal16 Hwlo Hwhi Hin Hbp Hpn Hgb.
pose proof pa_segs_low as Hsegs.
pose proof (rd32_bytes_below_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) b n p
  HJ Hwlo Hin Hbp Hpn) as Hbelow.
destruct (rd_garr8_4 _ _ _ _ _ _ Hgb) as (_ & (B0 & B1 & B2 & B3)).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & Hshi & H47 & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hin) as (_ & Hb4096 & _).
destruct (rd_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b n c0 c1 c2 c3
  HJ H10 Hal16 Hwlo Hwhi Hin Hbp Hpn Hgb) as [HS SHOK].
unfold RD32_FRAME in *.
remember (Eimg (Ereg regs (rd_extra c0 c1 c2 c3))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (rd_extra c0 c1 c2 c3)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 c0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 c3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (HAE : env_agree 32 (Ereg regs (rd_extra c0 c1 c2 c3)) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_rd32)) with (Z_to_bv 64 (BASE + AF_rd32)).
(* The frame, the save of ra, the three UBSan guards, the shadow base and the four checked byte loads, up to the
   test of the swap flag at 0x810fc. *)
paj_run_tok RUN HS HJ SHOK RDspan; [ rd_awr (spZ regs) sp0 Usp |].
rd_frame_kept HFr (spZ regs) Usp UN1. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (X11 : ew Ex 11 = getr regs 11) by (rd_ew_old E11);
  assert (X33 : ew Ex 33 = Z_to_bv 64 c0) by (rd_ew_old E33);
  assert (X34 : ew Ex 34 = Z_to_bv 64 c1) by (rd_ew_old E34);
  assert (X35 : ew Ex 35 = Z_to_bv 64 c2) by (rd_ew_old E35);
  assert (X36 : ew Ex 36 = Z_to_bv 64 c3) by (rd_ew_old E36);
  assert (Usp1 : bv_unsigned (ew Ex 2) = spZ regs) by (rd_ew_old Usp);
  assert (HAE1 : env_agree 32 (Ereg regs (rd_extra c0 c1 c2 c3)) Ex) by (rd_agree HAE)
end.
psrr_branch_tok RUN BR HS SHOK RDspan.
- (* a1 = 0: v as loaded *)
  assert (Hsw : bv_eqb (getr regs 11) (Z_to_bv 64 0) = true)
    by (rewrite <- Hc; cbn [sv_denot]; rewrite X11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK RDspan; [ rd_awr (spZ regs) sp0 Usp1 |].
  rd_frame_kept HFr (spZ regs) Usp1 UN2. clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
              aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
  lazymatch goal with HS : st_ok_pi _ _ ?Ey ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1;
    pose proof (st_ok_pi_restrict_reg _ Ey ssx msc (10%bv : bv 5) HS) as R10;
    change (sr_get (ss_regs ssx) (10%bv : bv 5)) with RD_LE in R10;
    assert (Y33 : ew Ey 33 = Z_to_bv 64 c0) by (first [exact X33 | rd_ew_old X33]);
    assert (Y34 : ew Ey 34 = Z_to_bv 64 c1) by (first [exact X34 | rd_ew_old X34]);
    assert (Y35 : ew Ey 35 = Z_to_bv 64 c2) by (first [exact X35 | rd_ew_old X35]);
    assert (Y36 : ew Ey 36 = Z_to_bv 64 c3) by (first [exact X36 | rd_ew_old X36]);
    assert (HAE2 : env_agree 32 (Ereg regs (rd_extra c0 c1 c2 c3)) Ey) by (first [exact HAE1 | rd_agree HAE1]);
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold trd32_post;
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [reflexivity|];
    split; [cbn [ms_regs]; rewrite R1, E1, Hraw; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ey _ _ regs (rd_extra c0 c1 c2 c3) HS);
            [exact HAE2 | vm_compute; reflexivity]|];
    split; [rewrite R10, (denot_lit_U Ey RD_LE), (rd_U_le Ey c0 c1 c2 c3 Y33 Y34 Y35 Y36 B0 B1 B2 B3);
            unfold trd32_val; rewrite Hsw; apply rd_w64_zcanon|];
    split; [repeat rewrite wvb_collapse; apply same_but_materialized_wvb_any|];
    split; [exact UN|];
    apply (garr8_frame SEGS (rdW W memc) _ _ _ Hgb); intros a Ha; cbn [length] in Ha;
    apply (mbyte_of_aview SEGS); apply UN; lia
  end.
- (* a1 <> 0: v byte-swapped *)
  assert (Hsw : bv_eqb (getr regs 11) (Z_to_bv 64 0) = false)
    by (rewrite <- Hc; cbn [sv_denot]; rewrite X11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK RDspan; [ rd_awr (spZ regs) sp0 Usp1 |].
  rd_frame_kept HFr (spZ regs) Usp1 UN2. clear HF HFr HG.
  lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
              aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a)
      by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
  lazymatch goal with HS : st_ok_pi _ _ ?Ey ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1;
    pose proof (st_ok_pi_restrict_reg _ Ey ssx msc (10%bv : bv 5) HS) as R10;
    change (sr_get (ss_regs ssx) (10%bv : bv 5)) with RD_BE in R10;
    assert (Y33 : ew Ey 33 = Z_to_bv 64 c0) by (first [exact X33 | rd_ew_old X33]);
    assert (Y34 : ew Ey 34 = Z_to_bv 64 c1) by (first [exact X34 | rd_ew_old X34]);
    assert (Y35 : ew Ey 35 = Z_to_bv 64 c2) by (first [exact X35 | rd_ew_old X35]);
    assert (Y36 : ew Ey 36 = Z_to_bv 64 c3) by (first [exact X36 | rd_ew_old X36]);
    assert (HAE2 : env_agree 32 (Ereg regs (rd_extra c0 c1 c2 c3)) Ey) by (first [exact HAE1 | rd_agree HAE1]);
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    unfold trd32_post;
    exists (ms_regs msc), (ms_mem msc); eexists;
    split; [reflexivity|];
    split; [cbn [ms_regs]; rewrite R1, E1, Hraw; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ey _ _ regs (rd_extra c0 c1 c2 c3) HS);
            [exact HAE2 | vm_compute; reflexivity]|];
    split; [rewrite R10, (denot_lit_U Ey RD_BE), (rd_U_be Ey c0 c1 c2 c3 Y33 Y34 Y35 Y36 B0 B1 B2 B3);
            unfold trd32_val; rewrite Hsw; apply rd_w64_zcanon|];
    split; [repeat rewrite wvb_collapse; apply same_but_materialized_wvb_any|];
    split; [exact UN|];
    apply (garr8_frame SEGS (rdW W memc) _ _ _ Hgb); intros a Ha; cbn [length] in Ha;
    apply (mbyte_of_aview SEGS); apply UN; lia
  end.
Qed.

End e.
End d.
End b.

(* The sink-head instance is explicit on every exported statement and theorem (a Theorem Labs lane, 21:57Z). *)
Arguments trd32_post {fx rc} SK.
Arguments trd32_specX {fx rc} SK.
Arguments pb_rd32X {fx rc} SK {PI}.
Arguments rd_entry {fx rc} SK {PI}.
Arguments rd32_bytes_below_frame {rc} SK {PI}.

(* GUARD: SK must stay explicit. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment) (B : asyms) (a : Z) =>
  trd32_specX (fx:=fx) (rc:=rc) SK segs B a : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) =>
  pb_rd32X (fx:=fx) (rc:=rc) SK (PI:=PI)).
Print Assumptions pb_rd32X.
