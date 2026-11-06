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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/RdU32.v, with its module paths, module names and numbers changed; 71 of its 100 lines of code are new or changed and 580 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the two image-free
   facts the fit phase (lib/B/Prog/PcapSourceNextFitA.v, entry predicate lib/B/Prog/PcapSourceNextFitADefs.v) needs
   on the VLAN-tagged arm, stated so that neither names the image.

   Both are read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22a..., capstone 5; listing nxb-next.dis (sha256 7213b94e2690; internal record), slot table
   nxb-handoff.md (sha256 c02dc85fade1; internal record)), but only as the SHAPE of the fact: no address, no symbol and no table of either image enters
   the statements or the proofs, so this file Requires no module that carries one.

   1. fa_mm_bytes -- the byte-level effect of `jal __asan_memmove` at 0x81af4 (a0 = buf + 12 from `mv a0,a1`
      0x81aec, a1 = buf + 16 from `addi s4,s4,0x10` 0x81adc and `mv a1,s4` 0x81af0, a2 = zext32(incl - 16) from
      `addi a0,s6,-0x10` 0x81ae0 / `slli` / `srli` 0x81ae4, 0x81ae8): the record's tail moves down by 4 over the
      caller's buffer, so the first incl bytes become
        bytes 0 .. 11 (the header up to the VLAN tag), then bytes 16 .. incl - 1 (the tail), then the last 4
        bytes of the old content, which the move leaves where they were.
      The caller passes the whole 16-byte-or-longer record as `raw`; the two hypotheses are the move (the 12 .. 
      incl - 5 window reads what stood 4 bytes higher) and the frame (every other byte of the record is kept).

   2. fa_U_vid -- the two-byte vid assembly at 0x81abc .. 0x81acc: `slli a2,a2,8` 0x81abc on buf[14]
      (`addi a2,s4,0xe` 0x81a80, `lbu a2,0(a2)` 0x81aa8), `addi a4,zero,0xf` 0x81ac0 + `slli a4,a4,8` 0x81ac4 +
      `and a2,a2,a4` 0x81ac8 (the mask 0xf00), `or a2,a2,a3` 0x81acc with buf[15] (`addi a3,s4,0xf` 0x81a98,
      `lbu a3,0(a3)` 0x81ab4); `sh a2,0(a0)` 0x81ad4 stores it. The value is the model's
      ((buf[14] << 8) | buf[15]) & 0xfff, stated as (256 * b14 + b15) mod 4096.

   TAKEN FROM.
   - fa_mm_bytes: lib/A/Prog/YC88.v (image-free, owner a Theorem Labs lane's YC88 family) garr8_aview :51,
     garr8_aview_kept :62 and garr8_sub_x :97, over lib/Reusable/YI00.v garr8_app :55. No further text is new.
   - fa_U_vid: lib/Reusable/YI04.v U_atom :225, U_lit :235 and U_and_lit :239; lib/Reusable/YP0e.v U_SAlu :184 and
     zcanon_id :163; lib/Reusable/YO0b.v lor_add_high' :21 for the final `or`.
   - fa_land_3840 is lib/B/Prog/RdU32.v:178 land_65280 (a lemma of this unit) with the mask's width
     changed from 8 bits to 4, because the fit path masks with 0xf00 and rd_u32 masks with 0xff00; RdU32.v itself
     is not Required, since it carries this image's symbol table and this file must stay image-free. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YI04 YO0b.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YK04 YA0n YG0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC88.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The mask 0xf00 of `and a2,a2,a4` (0x81ac8): the port of lib/B/Prog/RdU32.v:175 at 4 mask bits. *)
Lemma fa_land_3840 : forall x, 0 <= x -> Z.land x 3840 = 2 ^ 8 * ((x / 2 ^ 8) mod 2 ^ 4).
Proof.
intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
change 3840 with (Z.shiftl (Z.ones 4) 8).
rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftr_div_pow2 by lia.
destruct (Z.lt_ge_cases n 8) as [H8|H8].
- rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
- rewrite !Z.shiftl_spec by lia.
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec (n - 8) 4) as [Hl|Hl].
  + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia.
    replace (n - 8 + 8) with n by lia. apply andb_true_r.
  + rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* THE MEMMOVE (0x81af4). raw is the record as it stood before the call (its length n = incl is the record's
   included length, which the header phase has shown to be at least 16 on this arm, since the VLAN test read
   buf[12] .. buf[15]). The first hypothesis is the move itself, the second is its frame: outside the written
   window [buf + 12, buf + n - 4) every byte of the record reads as it did. *)
Lemma fa_mm_bytes : forall segs (W : world segs) (m m' : word -> option byte) buf (raw : list Z) (n : nat),
  (16 <= n)%nat -> length raw = n ->
  garr8 segs (mrestrict (w_H W) m) buf raw ->
  (forall i, 0 <= i < Z.of_nat n - 16 ->
     aview segs (w_H W) m' (buf + 12 + i) = aview segs (w_H W) m (buf + 16 + i)) ->
  (forall a, buf <= a < buf + Z.of_nat n -> ~ (buf + 12 <= a < buf + Z.of_nat n - 4) ->
     aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  garr8 segs (mrestrict (w_H W) m') buf
    (firstn 12 raw ++ firstn (n - 16) (skipn 16 raw) ++ skipn (n - 4) raw).
Proof.
intros segs W m m' buf raw n Hn Hlen HG HMV HKP.
assert (L1 : length (firstn 12 raw) = 12%nat) by (rewrite length_firstn; lia).
assert (L2 : length (firstn (n - 16) (skipn 16 raw)) = (n - 16)%nat)
  by (rewrite length_firstn, length_skipn; lia).
assert (L3 : length (skipn (n - 4) raw) = 4%nat) by (rewrite length_skipn; lia).
(* bytes 0 .. 11: kept where they are *)
assert (G1 : garr8 segs (mrestrict (w_H W) m) buf (firstn 12 raw)).
{ pose proof (garr8_sub_x segs (mrestrict (w_H W) m) buf raw 0%nat 12%nat HG ltac:(lia)) as X.
  replace (buf + Z.of_nat 0) with buf in X by lia. exact X. }
assert (G1' : garr8 segs (mrestrict (w_H W) m') buf (firstn 12 raw)).
{ apply (garr8_aview_kept segs (w_H W) (w_H W) m m' buf (firstn 12 raw)); [|exact G1].
  intros a Ha. rewrite L1 in Ha. apply HKP; lia. }
(* bytes 16 .. n - 1: moved down to buf + 12 *)
assert (G2 : garr8 segs (mrestrict (w_H W) m) (buf + 16) (firstn (n - 16) (skipn 16 raw))).
{ pose proof (garr8_sub_x segs (mrestrict (w_H W) m) buf raw 16%nat (n - 16)%nat HG ltac:(lia)) as X.
  replace (buf + Z.of_nat 16) with (buf + 16) in X by lia. exact X. }
assert (G2' : garr8 segs (mrestrict (w_H W) m') (buf + 12) (firstn (n - 16) (skipn 16 raw))).
{ apply (garr8_aview segs (w_H W) (w_H W) m m' (buf + 16) (buf + 12)
    (firstn (n - 16) (skipn 16 raw))); [|exact G2].
  intros i Hi. rewrite L2 in Hi. apply HMV. lia. }
(* the last 4 bytes: below the written window, so kept *)
assert (G3 : garr8 segs (mrestrict (w_H W) m) (buf + (Z.of_nat n - 4)) (skipn (n - 4) raw)).
{ pose proof (garr8_sub_x segs (mrestrict (w_H W) m) buf raw (n - 4)%nat 4%nat HG ltac:(lia)) as X.
  rewrite firstn_all2 in X by (rewrite length_skipn; lia).
  replace (buf + Z.of_nat (n - 4)) with (buf + (Z.of_nat n - 4)) in X by lia. exact X. }
assert (G3' : garr8 segs (mrestrict (w_H W) m') (buf + (Z.of_nat n - 4)) (skipn (n - 4) raw)).
{ apply (garr8_aview_kept segs (w_H W) (w_H W) m m' (buf + (Z.of_nat n - 4)) (skipn (n - 4) raw)); [|exact G3].
  intros a Ha. rewrite L3 in Ha. apply HKP; lia. }
apply garr8_app. split; [exact G1'|]. rewrite L1.
apply garr8_app. split.
- replace (buf + Z.of_nat 12) with (buf + 12) by lia. exact G2'.
- rewrite L2. replace (buf + Z.of_nat 12 + Z.of_nat (n - 16)) with (buf + (Z.of_nat n - 4)) by lia. exact G3'.
Qed.

End a.

(* THE VID (0x81abc .. 0x81acc). Atom 40 is buf[14] and atom 41 is buf[15], each a zero-extended byte
   (`lbu`), so each is in [0, 256). *)
Lemma fa_U_vid : forall E b14 b15,
  ew E 40 = Z_to_bv 64 b14 -> ew E 41 = Z_to_bv 64 b15 ->
  0 <= b14 < 256 -> 0 <= b15 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SLit 3840)) (SOff 41 0))
    = (256 * b14 + b15) mod 4096.
Proof.
intros E b14 b15 H40 H41 R14 R15.
assert (A14 : U E (SOff 40 0) = b14) by (apply (U_atom E 40%nat b14 H40); lia).
assert (A15 : U E (SOff 41 0) = b15) by (apply (U_atom E 41%nat b15 H41); lia).
(* `slli a2,a2,8` *)
assert (S8 : U E (SAlu ALU_SLL (SOff 40 0) (SLit 8)) = 256 * b14).
{ rewrite U_SAlu, A14, U_lit by lia. cbn [zalu_raw].
  replace (Z.land 8 63) with 8 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite zcanon_id by (unfold M64; lia). lia. }
(* `and a2,a2,a4` with a4 = 0xf00 *)
assert (AN : U E (SAlu ALU_AND (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SLit 3840))
  = 2 ^ 8 * (b14 mod 2 ^ 4)).
{ rewrite U_and_lit by lia. rewrite S8. rewrite fa_land_3840 by lia.
  replace (256 * b14 / 2 ^ 8) with b14
    by (change (2 ^ 8) with 256; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  reflexivity. }
pose proof (Z.mod_pos_bound b14 (2 ^ 4) ltac:(lia)) as HM.
pose proof (Z.div_mod b14 (2 ^ 4) ltac:(lia)) as HD.
(* `or a2,a2,a3` *)
rewrite (U_SAlu E ALU_OR (SAlu ALU_AND (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SLit 3840)) (SOff 41 0)).
cbn [zalu_raw]. rewrite AN, A15.
rewrite (lor_add_high' b15 (b14 mod 2 ^ 4) 8) by lia.
rewrite zcanon_id by (unfold M64; lia).
replace (256 * b14 + b15) with (b15 + 2 ^ 8 * (b14 mod 2 ^ 4) + b14 / 2 ^ 4 * 4096) by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (b15 + 2 ^ 8 * (b14 mod 2 ^ 4)) 4096) by lia. reflexivity.
Qed.

(* GUARD: both facts are image-free, so neither carries a binder of the walk's framework: fa_mm_bytes takes the
   segments and the world it states, fa_U_vid takes only an env, and neither names {fx}, {rc}, SK or a PAImg. *)
Check (fa_mm_bytes, fa_U_vid).
