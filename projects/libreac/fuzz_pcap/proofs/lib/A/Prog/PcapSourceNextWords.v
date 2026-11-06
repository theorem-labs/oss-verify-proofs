(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 106 of its 137 lines of code are new or changed and 3526 lines of the source are left out. *)
(* pcap_source_next (0x8181c) on libreac v1.9.0: the word arithmetic of the record's 32-bit fields,
   in ONE image-free home, so that no walk file proves it twice.

   The twelve lemmas below were proved by the lib/A header phase, PcapSourceNextHdrB.v, and were
   copied once into PcapSourceNextFitABits.v under fab_* names. They are moved here under their
   ORIGINAL names, text unchanged; both files now Require this one. Any other walk on either image
   should use these rather than restate them: nothing here names an image, an address or a build.

   What is here: the 64-bit ALU views (nx_wrap64, nx_wrap32, nx_sll_u, nx_or_u, nx_and_u), the
   unsigned view of a sign-extended 32-bit value (nx_s32, nx_s32_lo), the 32-bit shift-right word
   form (nx_srlw_u), the two bit lemmas the assembly needs (nx_lor_add, nx_land_ff00), and the two
   byte-assembly results (nx_asm_lo64, the four bytes little-endian in 64 bits; nx_asm_sw64, the
   same word byte-swapped from the unswapped one). Also the two generic list lemmas the memmove
   argument needs (nx_nth_firstn_lt, nx_nth_skipn_add).

   The lemmas that stayed in PcapSourceNextHdrB.v are the ones the twelve do not need and no second
   file uses: nx_mod64_small, nx_srl_u, nx_sllw_u, nx_u_s32, nx_asm_lo, nx_asm_sw, nx_zext32. They
   are image-free too and can move here on request.

   TAKEN FROM
   - the twelve: PcapSourceNextHdrB.v:54..281 (owner: a Theorem Labs lane, on
     a working branch, first in cff93dd8aa1), statements and proofs unchanged.
   - nx_nth_firstn_lt, nx_nth_skipn_add: nth_firstn_lt, nth_skipn_add of the released
     proofs/libreac/fuzz_pcap/lib/Prog/pcap_source_next_lib.v:138,144 (owner: Theorem Labs,
     origin/ossv/recipes 5121fb8693, commit 84b1ffc6d7d), text unchanged, renamed. That file states
     them image-free as well, but Requiring it would pull lib/Lib Tac, Bytes and Arr, lib/MemNorm
     and lib/RoAdapt into every consumer of this file and would put its whole namespace (and its
     Ltac) into PcapSourceNextHdrB.v through the Export below; the two three-line lemmas are kept
     here instead to leave that file's namespace as it was. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the arithmetic of the record's 32-bit fields (0x819d4..0x81ab0, 0x81b40..0x81bb8) ---- *)

Lemma nx_wrap64 : forall z, bv_wrap 64 z = z mod 2 ^ 64.
Proof. intros z. reflexivity. Qed.
Lemma nx_wrap32 : forall z, bv_wrap 32 z = z mod 2 ^ 32.
Proof. intros z. reflexivity. Qed.

Lemma nx_sll_u : forall (a : word) k, 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SLL a (Z_to_bv 64 k)) = (bv_unsigned a * 2 ^ k) mod 2 ^ 64.
Proof.
  intros a k Hk. unfold alu64, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !nx_wrap64.
  rewrite (Z.mod_small k) by lia. change (63 mod 2 ^ 64) with (Z.ones 6).
  rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma nx_or_u : forall a b : word, bv_unsigned (alu64 ALU_OR a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. unfold alu64, alu. apply bv_or_unsigned. Qed.

Lemma nx_and_u : forall a b : word, bv_unsigned (alu64 ALU_AND a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. unfold alu64, alu. apply bv_and_unsigned. Qed.

(* The unsigned 64-bit view of a 32-bit value sign-extended. *)
Lemma nx_s32 : forall v, 0 <= v < 2 ^ 32 ->
  bv_swrap 32 v mod 2 ^ 64 = if v <? 2 ^ 31 then v else v + 2 ^ 64 - 2 ^ 32.
Proof.
  intros v Hv. unfold bv_swrap. rewrite nx_wrap32.
  change (bv_half_modulus 32) with (2 ^ 31).
  destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
    replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique (v + 2 ^ 31) (2 ^ 32) 1 (v + 2 ^ 31 - 2 ^ 32)) by lia.
    rewrite <- (Z.mod_unique (v + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) (2 ^ 64) (-1) (v + 2 ^ 64 - 2 ^ 32)) by lia.
    reflexivity.
Qed.

Lemma nx_srlw_u : forall (a : word) k, 0 <= k < 32 ->
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 a) (low32 (Z_to_bv 64 k)))) =
  bv_wrap 64 (bv_swrap 32 ((bv_unsigned a mod 2 ^ 32) / 2 ^ k)).
Proof.
  intros a k Hk. unfold sext, alu32, alu, low32.
  rewrite bv_sign_extend_unsigned. unfold bv_signed. f_equal. f_equal.
  rewrite bv_shiftr_unsigned, bv_and_unsigned, !bv_extract_unsigned, !Z_to_bv_unsigned, !nx_wrap32, !nx_wrap64.
  rewrite !Z.shiftr_0_r. rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 32)) by lia.
  change (31 mod 2 ^ 32) with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

(* An OR of two values with disjoint bits is their sum. *)
Lemma nx_lor_add : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> b mod 2 ^ n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low b n i Hlt), Hm, Z.bits_0. apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma nx_land_ff00 : forall a, 0 <= a -> Z.land a 65280 = (a / 256) mod 256 * 256.
Proof.
  intros a Ha.
  replace 65280 with (Z.shiftl (Z.ones 8) 8) by reflexivity.
  replace ((a / 256) mod 256 * 256) with (Z.shiftl (Z.land (Z.shiftr a 8) (Z.ones 8)) 8)
    by (rewrite Z.land_ones, Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; reflexivity).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.shiftl_spec by lia. rewrite Z.land_spec.
  destruct (Z.ltb_spec (i - 8) 0).
  - rewrite (Z.testbit_neg_r (Z.ones 8) (i - 8)) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftr_spec by lia. replace (i - 8 + 8) with i by lia.
    destruct (Z.ltb_spec (i - 8) 8);
      [rewrite Z.ones_spec_low by lia | rewrite Z.ones_spec_high by lia];
      destruct (Z.testbit a i); reflexivity.
Qed.

Lemma nx_s32_lo : forall v, 0 <= v < 2 ^ 31 -> bv_swrap 32 v mod 2 ^ 64 = v.
Proof. intros v Hv. rewrite nx_s32 by lia. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.

(* The record's orig_len (0x81a30..0x81a54, a3): the same bytes, the top one shifted in 64 bits. *)
Lemma nx_asm_lo64 : forall x0 x1 x2 x3,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  alu64 ALU_OR (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x1) (Z_to_bv 64 8)) (Z_to_bv 64 x0))
    (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x2) (Z_to_bv 64 16)) (alu64 ALU_SLL (Z_to_bv 64 x3) (Z_to_bv 64 24))) =
  Z_to_bv 64 (PSN.w32le x0 x1 x2 x3).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3. apply bv_eq.
  rewrite !nx_or_u, !nx_sll_u by lia. rewrite !Z_to_bv_unsigned, !nx_wrap64.
  rewrite !(Z.mod_small x0 (2 ^ 64)), (Z.mod_small x1 (2 ^ 64)), (Z.mod_small x2 (2 ^ 64)),
    (Z.mod_small x3 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (x1 * 2 ^ 8)), (Z.mod_small (x2 * 2 ^ 16)), (Z.mod_small (x3 * 2 ^ 24)) by lia.
  rewrite (Z.mod_small (PSN.w32le x0 x1 x2 x3)) by (unfold PSN.w32le; lia).
  rewrite (Z.lor_comm (x1 * 2 ^ 8) x0), (nx_lor_add x0 (x1 * 2 ^ 8) 8) by (first [apply Z.mod_mul; lia | lia]).
  rewrite (nx_lor_add (x2 * 2 ^ 16) (x3 * 2 ^ 24) 24) by (first [apply Z.mod_mul; lia | lia]).
  rewrite (nx_lor_add (x0 + x1 * 2 ^ 8) (x2 * 2 ^ 16 + x3 * 2 ^ 24) 16); [unfold PSN.w32le; lia | lia | lia | lia |].
  replace (x2 * 2 ^ 16 + x3 * 2 ^ 24) with ((x2 + x3 * 2 ^ 8) * 2 ^ 16) by ring. apply Z.mod_mul. lia.
Qed.

(* The byte-swapped orig_len (0x81a5c..0x81a7c), from the unswapped word O in a3. *)
Lemma nx_asm_sw64 : forall x0 x1 x2 x3,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  forall O : word, O = Z_to_bv 64 (PSN.w32le x0 x1 x2 x3) ->
  alu64 ALU_OR
    (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x0) (Z_to_bv 64 24))
       (alu64 ALU_SLL (alu64 ALU_AND O (Z_to_bv 64 65280)) (Z_to_bv 64 8)))
    (alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 x2) (Z_to_bv 64 8))
       (sext 64 (alu32 ALU_SRL (low32 O) (low32 (Z_to_bv 64 24))))) =
  Z_to_bv 64 (PSN.w32le x3 x2 x1 x0).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3 O EO. apply bv_eq.
  assert (UO : bv_unsigned O = PSN.w32le x0 x1 x2 x3)
    by (rewrite EO, Z_to_bv_unsigned, nx_wrap64; apply Z.mod_small; unfold PSN.w32le; lia).
  assert (A1 : Z.land (bv_unsigned O) 65280 = x1 * 256).
  { rewrite nx_land_ff00 by (rewrite UO; unfold PSN.w32le; lia). rewrite UO. unfold PSN.w32le.
    Z.div_mod_to_equations; lia. }
  assert (A3 : bv_unsigned O mod 2 ^ 32 / 2 ^ 24 = x3).
  { rewrite UO. unfold PSN.w32le. Z.div_mod_to_equations; lia. }
  rewrite !nx_or_u, !nx_sll_u, nx_and_u, nx_srlw_u by lia.
  rewrite A3. rewrite !Z_to_bv_unsigned, !nx_wrap64.
  replace (65280 mod 2 ^ 64) with 65280 by reflexivity. rewrite A1.
  rewrite !(Z.mod_small x0 (2 ^ 64)), (Z.mod_small x2 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (x0 * 2 ^ 24)), (Z.mod_small (x1 * 256 * 2 ^ 8)), (Z.mod_small (x2 * 2 ^ 8)) by lia.
  rewrite (nx_s32_lo x3) by lia. rewrite (Z.mod_small (PSN.w32le x3 x2 x1 x0)) by (unfold PSN.w32le; lia).
  unfold PSN.w32le.
  rewrite (Z.lor_comm (x2 * 2 ^ 8) x3), (nx_lor_add x3 (x2 * 2 ^ 8) 8) by (first [apply Z.mod_mul; lia | lia]).
  rewrite (Z.lor_comm (x0 * 2 ^ 24) (x1 * 256 * 2 ^ 8)), (nx_lor_add (x1 * 256 * 2 ^ 8) (x0 * 2 ^ 24) 24)
    by (first [apply Z.mod_mul; lia | lia]).
  rewrite (Z.lor_comm (x1 * 256 * 2 ^ 8 + x0 * 2 ^ 24) (x3 + x2 * 2 ^ 8)),
    (nx_lor_add (x3 + x2 * 2 ^ 8) (x1 * 256 * 2 ^ 8 + x0 * 2 ^ 24) 16); [lia | lia | lia | lia |].
  replace (x1 * 256 * 2 ^ 8 + x0 * 2 ^ 24) with ((x1 + x0 * 2 ^ 8) * 2 ^ 16) by ring. apply Z.mod_mul. lia.
Qed.

(* ---- the two generic list lemmas the memmove argument needs ---- *)

Lemma nx_nth_firstn_lt : forall (A : Type) (l : list A) n m d, (n < m)%nat -> nth n (firstn m l) d = nth n l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n m d H; destruct m as [|m]; cbn; try lia; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nx_nth_skipn_add : forall (A : Type) (l : list A) n m d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n m d; destruct m as [|m]; cbn; try reflexivity; [destruct n; reflexivity|].
  apply IH.
Qed.
