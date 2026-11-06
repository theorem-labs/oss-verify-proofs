(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 913 of its 952 lines of code are new or changed and 287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Open.v at 635914e101a0 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (SELS 0x81150 -> C 0x8127c / CL 0x82484, the slow block 0x82608, the
   constant at .rodata 0x10408), registers (s6 / s7 / s2 for role's s4 / s5 / s7; the capacity bound -0x4001 is s10 and
   what is left of the input is s8, for role's cells R+0xe0 and R+0xf8) and real-frame cells (at R+0xe0, the cursor
   R+0x100, -0x3ffd at R+0x130, the count R+0xf0, for role's R+0xa0 / 0xc8 / 0xe8 / 0xa8); the shadow byte's address,
   the input byte and the shadow byte are atoms 36 .. 38; rm_ / rl_ become rtm_ / rt_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Open.v at a66696a9b1d1 for the same unit's
   image B (fuzz_rate.asan-ubsan): image B's pcs (SELS 0x81210 -> C 0x813a0 / CL 0x824c0 through 0x82474 / 0x8247c, the
   slow block 0x825dc, the constant at .rodata 0x10418), registers (pp, &pp->len's shadow address and &e62 are loaded
   from the real-frame cells R+0x168 / R+0x170 / R+0x150, s2 = &pp->len, t1 = -0x4001, s4 = K, the cursor in s10, what
   is left in t4, s9 = 1) and real-frame cells (-0x3ffd at R+0x120, ~pp at R+0x108, the four cells R+0x98 .. R+0xb0
   and the count R+0x140 the piece writes); at is read from pp->len; the four UBSan trap branches of the two put32 and
   the one of the input read are decided by atom ranges (~pp is atom 36); pp, pp + at, at, ~pp, the shadow byte's
   address, the input byte and the shadow byte are atoms 33 .. 39; rtm_ / w5_ become rtmb_ / w5b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the params Struct's header and its pod count,
   SELS 0x81210 -> C 0x813a0 or CL 0x824c0, in LLVMFuzzerTestOneInput (pod.h:421-425, fuzz.h:37-43), as three core
   lemmas, one per exit: w5b_open_core_nil (in.n = 0, to 0x824c0), w5b_open_core_zero (count = fuzz_u8 % 33 = 0, to
   0x824c0) and w5b_open_core_pos (count <> 0, to 0x813a0). Proves no function (kind: segment lemma).

   THE CODE
     0x81210-0x81220  the check of pp->len through its shadow address in R+0x170 (`ld a0,0x170(s1); lbu a0,0(a0);
              beqz a0,+8; j report`); s6 := R+0x150 (&e62)
     0x81224-0x812a0  pod_put32(pp, 0): a6 = len (`ld a6,0(s2)`), a0 = len - 0x3ffd (R+0x120), a5 = pp + len (R+0x168);
              the capacity test `bltu a0,t1` (t1 = -0x4001, not taken: the condition op_cap1); the UBSan traps
              `bltu a6,0x4001` (0x81244) and `bgeu ~pp,a6` (0x81250, ~pp from R+0x108), both taken to the store; two
              covered checks, four `sb zero`, the check of pp->len
     0x812a4-0x81330  len + 4 into pp->len, the capacity test again (`bltu a2,t1`, not taken: op_cap2), the traps 0x812bc /
              0x812c8 on len + 4, pod_put32(pp, 14) at pp + len + 4, the check of pp->len, len += 4
     0x81334-0x81340  sd t0 -> R+0xb0, sd a4 -> R+0x98 (1), sd a5 -> R+0xa8 (pp + at), sd a6 -> R+0xa0 (at)
     0x81344  bnez t4 (in.n): if 0, `j 0x82474`: `li s9,0; j 0x824c0`
     0x8134c-0x81368  the UBSan trap `addi a0,s10,1; bltu s9,a0` (s9 = 1: taken), the check of the 1-byte load at the
              cursor s10, `lb a1,0(sh); beqz a1,+8; j 0x825dc`, with the slow block 0x825dc
              `andi a2,s10,7; bge a2,a1,report; j 0x8136c`
     0x8136c  lbu a1,0(s10); 0x81370-0x81374 auipc/ld a2 of the constant 0x07c1f07c1f07c1f1 at 0x10418
     0x81378-0x81384  mulhu/slli/or/sub: count = b mod 33; s9 = t4 - 1; sd a1,0x140(s1); 0x81390 bnez a1: if 0
              `j 0x8247c` (`mv s10,a0; j 0x824c0`), else 0x81398 `li a1,0`, `mv s10,a0` (cursor + 1) and 0x813a0.
   Every check on pp is covered by the shadow entries (33, 0x4000, 0x4008) and (34, 0, 16) (w5b_shent_blk); the R+0x170
   cell holds w5b_sh 33 0x4000, so the token engine reads its load as a covered shadow load.

   THE INPUT READ. The engine's token path cannot follow this check (its slow block is reached only by the `j`); so
   the shadow byte s of cur is a read-only region at atom 37 (the shadow address SHADOW_OFF + cur / 8, named by an
   f_alias entry), the `lb` is a region load, and the start facts carry the conditions the two branches need: s = 0
   (the `beqz` is taken) or 0 < s < 8 and cur mod 8 < s (the slow block's `bge` is not taken), both from saddr_ok
   cur s, which range_addressable cur 1 gives (rtmb_ra_cell, rtmb_ra_slow_bv). The count's `bnez` is decided by the
   condition b mod 33 = 0 or <> 0 of the exit. The input byte b is a read-only region at atom 26 (cur), the constant
   a base-free region of the image's bytes (img_region_ok_rom from rom_view); the two must be apart, so the case
   0x10418 <= cur < 0x10420 (the input inside the constant) is walked on its own with cur a literal: there b is the
   constant's byte, which is never 0 mod 33, so (b) is vacuous there and (c) reads b from the constant's region. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMemB RtPgW5KitB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the start states at 0x81210 ========================================
   atoms: 5 = |ps| (t0), 9 = R, 14 = 1 (a4), 26 = cur (s10), 27 = F + 0x20 (s11), 29 = in.n (t4), 32 = K, 33 = pp,
   34 = pp + at, 35 = at, 36 = ~pp (2^64 - 1 - pp), 37 = SHADOW_OFF + cur / 8, 38 = b, 39 = s. *)
Definition OP_C1 : Z := 18446744073709535231.  (* (-0x4001) mod 2^64 *)
Definition OP_C2 : Z := 18446744073709535235.  (* (-0x3ffd) mod 2^64 *)
Definition OP_K33 : Z := 558992244657865201.   (* 0x07c1f07c1f07c1f1, the 8 bytes at 0x10418 *)
(* s1 = R as sp, s2 = &pp->len, s4 = K, t1 = -0x4001, s9 = 1 *)
Definition op_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((18%bv : bv 5), SOff 33 0x4000); ((20%bv : bv 5), w5b_Bx);
   ((6%bv : bv 5), SLit OP_C1); ((25%bv : bv 5), SLit 1)].
(* no input left: t4 = 0 *)
Definition op_ov0 : list (bv 5 * sv) := op_ov ++ [((29%bv : bv 5), SLit 0)].
(* the input inside the constant: s10 = cj *)
Definition op_ovB (cj : Z) : list (bv 5 * sv) := op_ov ++ [((26%bv : bv 5), SLit cj)].
(* the real frame's cells R + 0x98 .. 0xb0 the piece writes (1, at, pp + at, the property index) *)
Definition op_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x98 0xb8 0x98 0xb8 [].
(* R + 0x108 (~pp) and R + 0x120 (-0x3ffd), with the write window [wlo, whi) (R + 0x140, the count, when the count
   byte is read) *)
Definition op_rB (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x108 0x148 wlo whi
   [YP09.mkChunk 0x108 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x120 (CVal 8 (SLit OP_C2))].
(* R + 0x150 (&e62 = F + 0x210 = s11 + 0x1f0), R + 0x168 (pp) and R + 0x170 (the shadow address of &pp->len) *)
Definition op_rC : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x150 0x178 0 0
   [YP09.mkChunk 0x150 (CVal 8 (SOff 27 0x1f0)); YP09.mkChunk 0x168 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x170 (CVal 8 (w5b_sh 33 0x4000))].
Definition op_len : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 35 0))].
Definition op_at : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 8 [].
Definition op_cell : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 39 0))].
Definition op_in : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition op_k : YP09.region := YP09.mkRegion None 0x10418 0x10420 0 0 [YP09.mkChunk 0x10418 (CImg 8)].
(* the input inside the constant (cur = 0x10418 + j): the shadow byte at K + 0x2083 *)
Definition op_cellB : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x2083 0x2084 0 0 [YP09.mkChunk 0x2083 (CVal 1 (SOff 39 0))].
(* the two capacity tests: len - 0x3ffd >= -0x4001 and len + 4 - 0x3ffd >= -0x4001, unsigned *)
Definition op_cap1 : acond := mkAC BC_GEU (SOff 35 (-16381)) (SLit OP_C1).
Definition op_cap2 : acond := mkAC BC_GEU (SOff 35 (-16377)) (SLit OP_C1).
(* the shadow byte: 0, or the slow block's `bge cur & 7, s` not taken *)
Definition op_slow : acond := mkAC BC_LT (SAlu ALU_AND (SOff 26 0) (SLit 7)) (SOff 39 0).
Definition op_s0 (s0 : bool) : afact := if s0 then mkAF 0 0 0 else mkAF 1 7 0.
Definition op_sc (s0 : bool) : acond := if s0 then mkAC BC_EQ (SOff 39 0) (SLit 0) else op_slow.
Definition op_scB (cj : Z) (s0 : bool) : acond :=
  if s0 then mkAC BC_EQ (SOff 39 0) (SLit 0) else mkAC BC_LT (SLit (cj mod 8)) (SOff 39 0).
(* count = b - ((q << 5) | q), q = mulhu(b, K33), as the engine forms it *)
Definition op_M : sv :=
  SAlu ALU_SUB (SOff 38 0)
    (SAlu ALU_OR (SAlu ALU_SLL (SMd M_MULHU (SOff 38 0) (SLit OP_K33)) (SLit 5)) (SMd M_MULHU (SOff 38 0) (SLit OP_K33))).
Definition op_mz (z : bool) : acond := mkAC (if z then BC_EQ else BC_NE) op_M (SLit 0).
Definition op_atoms0 : list (nat * afact) :=
  [(9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF W5B_SB W5B_SB 0);
   (33%nat, mkAF 4096 140737479966720 4); (34%nat, mkAF 4096 140737479966720 0); (35%nat, mkAF 16 5432 0);
   (36%nat, mkAF 18446603336229584895 18446744073709547519 0); (26%nat, mkAF 1 140737488355328 0)].
Definition op_atoms1 (s0 : bool) : list (nat * afact) :=
  op_atoms0 ++ [(29%nat, mkAF 1 140737488355328 0); (38%nat, mkAF 0 255 0); (39%nat, op_s0 s0)].
Definition op_atomsB (s0 : bool) : list (nat * afact) :=
  op_atoms0 ++ [(29%nat, mkAF 1 140737488355328 0); (39%nat, op_s0 s0)].
Definition op_alias0 : list (sv * sv) := [(SAlu ALU_ADD (SOff 33 0) (SOff 35 0), SOff 34 0)].
Definition op_alias1 : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 33 0) (SOff 35 0), SOff 34 0);
   (SAlu ALU_ADD (SAlu ALU_SRL (SOff 26 0) (SLit 3)) (SOff 32 0), SOff 37 0)].
Definition ss_op_nil : sstate :=
  mkSS 0x81210 (w5b_sr op_ov0) [op_rA; op_rB 0 0; op_rC; op_len; op_at] None
    (mkFacts op_atoms0 [op_cap1; op_cap2] op_alias0).
Definition ss_op_in (s0 z : bool) : sstate :=
  mkSS 0x81210 (w5b_sr op_ov) [op_rA; op_rB 0x140 0x148; op_rC; op_len; op_at; op_cell; op_in; op_k] None
    (mkFacts (op_atoms1 s0) [op_cap1; op_cap2; op_sc s0; op_mz z] op_alias1).
Definition ss_op_rom (cj : Z) (s0 : bool) : sstate :=
  mkSS 0x81210 (w5b_sr (op_ovB cj)) [op_rA; op_rB 0x140 0x148; op_rC; op_len; op_at; op_cellB; op_k] None
    (mkFacts (op_atomsB s0) [op_cap1; op_cap2; op_scB cj s0] op_alias0).
Definition op_SH : list shent := [mkSHE 33 0x4000 0x4008; mkSHE 34 0 16].
Definition op_extra0 (pp atv : Z) : list word :=
  [w64 W5B_SB; w64 pp; w64 (pp + atv); w64 atv; w64 (18446744073709551615 - pp)].
Definition op_extra1 (pp atv cur b s : Z) : list word :=
  op_extra0 pp atv ++ [w64 (shadow_of_addr SHADOW_OFF cur); w64 b; w64 s].

(* ======================================== arithmetic ======================================== *)
Lemma op_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma op_lnot : forall pp, 0 <= pp < 18446744073709551616 -> Z.lnot pp mod 2 ^ 64 = 18446744073709551615 - pp.
Proof.
intros pp Hp. replace (Z.lnot pp) with (- pp - 1) by (unfold Z.lnot; lia). change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos (- pp - 1) 18446744073709551616 (-1)); lia.
Qed.
Definition op_mod_fn (x : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_SUB x
    (zcanon (zalu_raw 63 64 ALU_OR
      (zcanon (zalu_raw 63 64 ALU_SLL (zcanon (zmd_raw 64 M_MULHU x (zcanon OP_K33))) (zcanon 5)))
      (zcanon (zmd_raw 64 M_MULHU x (zcanon OP_K33)))))).
Lemma op_mod_fn_ok : forall x, 0 <= x < 256 -> op_mod_fn x = x mod 33.
Proof.
intros x Hx.
assert (H : forallb (fun n => op_mod_fn (Z.of_nat n) =? Z.of_nat n mod 33) (seq 0 256) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
Lemma op_U_M : forall E b, ew E 38 = Z_to_bv 64 b -> 0 <= b < 256 -> U E op_M = b mod 33.
Proof.
intros E b H38 Hb. unfold op_M. rewrite !U_SAlu, !U_SMd, !U_SLit.
rewrite (U_atom E 38 b H38) by lia. exact (op_mod_fn_ok b Hb).
Qed.
Lemma op_cap1_ok : forall E atv, bv_unsigned (ew E 35) = atv -> 16 <= atv <= 5432 -> acond_ok E op_cap1.
Proof.
intros E atv H35 Ha. unfold acond_ok, op_cap1. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, U_SOff, H35, U_SLit.
rewrite (op_zc (atv + -16381) (-1) (atv - 16381 + 18446744073709551616)) by lia.
rewrite (op_zc OP_C1 0 OP_C1) by (unfold OP_C1; lia).
apply negb_true_iff, Z.ltb_ge. unfold OP_C1. lia.
Qed.
Lemma op_cap2_ok : forall E atv, bv_unsigned (ew E 35) = atv -> 16 <= atv <= 5432 -> acond_ok E op_cap2.
Proof.
intros E atv H35 Ha. unfold acond_ok, op_cap2. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, U_SOff, H35, U_SLit.
rewrite (op_zc (atv + -16377) (-1) (atv - 16377 + 18446744073709551616)) by lia.
rewrite (op_zc OP_C1 0 OP_C1) by (unfold OP_C1; lia).
apply negb_true_iff, Z.ltb_ge. unfold OP_C1. lia.
Qed.
Lemma op_mz_ok : forall E b (z : bool), ew E 38 = Z_to_bv 64 b -> 0 <= b < 256 ->
(if z then b mod 33 = 0 else b mod 33 <> 0) -> acond_ok E (op_mz z).
Proof.
intros E b z H38 Hb Hz. unfold acond_ok, op_mz. destruct z; cbn [ac_c ac_a ac_b].
- change (b mod 33 = 0) in Hz. rewrite branch_eq_U, (op_U_M E b H38 Hb), U_SLit, Hz. reflexivity.
- change (b mod 33 <> 0) in Hz. rewrite branch_ne_U, (op_U_M E b H38 Hb), U_SLit.
  change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hz.
Qed.
Lemma op_sc_ok : forall E cur s (s0 : bool), ew E 26 = Z_to_bv 64 cur -> ew E 39 = Z_to_bv 64 s ->
0 <= cur < 2 ^ 64 -> saddr_ok cur s -> (if s0 then s = 0 else s <> 0) -> acond_ok E (op_sc s0).
Proof.
intros E cur s s0 H26 H39 Hc Hok Hs. unfold acond_ok. destruct s0; cbn [op_sc ac_c ac_a ac_b].
- change (s = 0) in Hs. subst s. rewrite branch_eq_U, U_SOff, H39, U_SLit. reflexivity.
- change (s <> 0) in Hs. unfold op_slow. cbn [ac_c ac_a ac_b].
  destruct (rtmb_ra_slow cur s Hok Hs) as [Hs1 Hs2].
  assert (A1 : sv_denot E (SAlu ALU_AND (SOff 26 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
  { change (sv_denot E (SAlu ALU_AND (SOff 26 0) (SLit 7))) with
      (alu64 ALU_AND (sv_denot E (SOff 26 0)) (sv_denot E (SLit 7))).
    rewrite (w5b_den_off E 26 cur 0 H26) by lia. rewrite Z.add_0_r. apply alu_and7. unfold M64. lia. }
  rewrite A1, (w5b_den_off E 39 s 0 H39) by lia. rewrite Z.add_0_r.
  exact (rtmb_ra_slow_bv cur s Hok Hs).
Qed.
Lemma op_scB_ok : forall E cj s (s0 : bool), ew E 39 = Z_to_bv 64 s ->
saddr_ok cj s -> (if s0 then s = 0 else s <> 0) -> acond_ok E (op_scB cj s0).
Proof.
intros E cj s s0 H39 Hok Hs. unfold acond_ok. destruct s0; cbn [op_scB ac_c ac_a ac_b].
- change (s = 0) in Hs. subst s. rewrite branch_eq_U, U_SOff, H39, U_SLit. reflexivity.
- change (s <> 0) in Hs. destruct (rtmb_ra_slow cj s Hok Hs) as [Hs1 Hs2].
  rewrite (w5b_den_off E 39 s 0 H39) by lia. rewrite Z.add_0_r.
  exact (rtmb_ra_slow_bv cj s Hok Hs).
Qed.
(* the constant's eight bytes lie in the image's read-only segment *)
Lemma op_in_rom : forall a, 0x10418 <= a < 0x10420 -> in_rom rsegs a.
Proof.
intros a Ha. apply RtPgStepsB.in_rom_b_ok.
assert (Hi8 : a = 66584 \/ a = 66585 \/ a = 66586 \/ a = 66587 \/ a = 66588 \/ a = 66589 \/ a = 66590 \/ a = 66591)
by lia.
destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma op_img : forall a, 0x10418 <= a < 0x10420 -> in_img rsegs a.
Proof. intros a Ha. destruct (op_in_rom a Ha) as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
Lemma op_kbyte_mod : forall i, 0 <= i < 8 -> (Z.shiftr OP_K33 (8 * i) mod 256) mod 33 <> 0.
Proof.
intros i Hi. assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; intro H; discriminate H.
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* an input byte inside the constant is the constant's byte *)
Lemma op_rom_byte : forall (W : world rsegs) memc cur b,
rom_view rsegs W memc -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
0x10418 <= cur < 0x10420 -> b = Z.shiftr OP_K33 (8 * (cur - 0x10418)) mod 256.
Proof.
intros W memc cur b HR V Hb Hk.
pose proof (rtmb_val1_aview rsegs _ _ _ _ V Hb) as A.
pose proof (HR cur (op_in_rom cur Hk)) as Hv. rewrite A in Hv.
assert (Hall : forall i, 0 <= i < 8 ->
  option_map (fun x : byte => bv_unsigned x) (seg_rom rsegs (Z_to_bv 64 (0x10418 + i))) =
  Some (Z.shiftr OP_K33 (8 * i) mod 256)).
{ intros i Hi. assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity. }
specialize (Hall (cur - 0x10418) ltac:(lia)). replace (0x10418 + (cur - 0x10418)) with cur in Hall by lia.
rewrite Hall in Hv. injection Hv as Hv. exact Hv.
Qed.
End r.

Section e. Context {fx : YK11.FPState}.
(* the five registers every start state overrides hold their values *)
Lemma op_ov_ok : forall E regs extra R pp, E = Ereg regs extra ->
  ew E 9 = w64 R -> ew E 33 = w64 pp -> ew E 32 = Z_to_bv 64 W5B_SB ->
  0 <= R < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 63 ->
  getr regs 2 = w64 R -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 6 = w64 (-0x4001) -> getr regs 25 = w64 1 ->
  Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) op_ov.
Proof.
intros E regs extra R pp HE E9 E33 E32 HR Hp1 Hp2 H2 H18 H20 H6 H25. unfold op_ov.
apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite (w5b_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite (w5b_den_off E 33 pp 0x4000 E33) by lia. rewrite H18. reflexivity. }
apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] |].
{ cbn [fst snd]. unfold w5b_Bx. rewrite (w5b_den_off E 32 W5B_SB 0 E32) by (unfold W5B_SB; lia).
  rewrite Z.add_0_r, H20. reflexivity. }
apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite H6, denot_lit_U, U_SLit. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
  vm_compute. reflexivity. }
apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite H25, denot_lit_U, U_SLit. reflexivity. }
apply Forall_nil.
Qed.
End e.

(* ======================================== tactics of the posts ======================================== *)
Ltac op_inl := cbn [In]; repeat (first [left; reflexivity | right]).
(* the eight bytes pod_put32(0), pod_put32(14) wrote at pp + at, from the end state's one-byte chunks *)
Ltac op_bytes8 E Cat :=
  apply rtmb_bytes_aview; intros i Hi; rewrite length_app, !length_Z_to_le_bytes in Hi; unfold aview;
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | | lia];
  lazymatch goal with |- option_map _ (mbyte _ ?m (?base + Z.of_nat ?n)) = Some (bv_unsigned (nth _ ?l _)) =>
    let o := eval cbv in (Z.of_nat n) in
    let v := eval vm_compute in (bv_unsigned (nth n l (Z_to_bv 8 0))) in
    let HB := fresh "HB" in
    assert (HB : mbyte rsegs m (base + o) = Some (Z_to_bv 8 (U E (SLit v))));
    [ apply (w5b_mbyte_chunk1 rsegs E); apply Cat; op_inl |];
    change (base + Z.of_nat n) with (base + o); rewrite HB, U_SLit; reflexivity
  end.
(* the write windows of a start state: the real frame's cells on the stack, pp->len and pp + at in pp *)
Ltac op_awr R sp0 pp atv U9 U33 U34 Hpp Hfresh :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
    [ reflexivity | rewrite U9; lia | cbn [r_wlo r_whi]; lia | cbn [r_wlo r_whi]; lia | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat pp);
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (pp + atv));
    [ reflexivity | exact U34
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ].
(* the post up to its last clause: the cfg, the journal, the registers outside the clobber list, frames, blocks,
   I/O, meter, and every byte outside the start state's write windows (sr0, the start registers, from HR0) *)
Ltac op_post_frame E W memc HJ HR0 clob U9 U33 U34 MTL :=
  apply SRr_ret; unfold w5b_post;
  lazymatch type of HR0 with regs_ok _ ?sr0 _ =>
  lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  do 2 eexists; exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    let HRf := fresh "HRf" in pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
    exact (w5b_regs_kept E Ef 40 sr0 (ss_regs ssf) _ (ms_regs msf) clob HR0 HRf
             (env_agree_refl 40 E) ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w5b_same_io_wvb]|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hst := fresh "Hst" in let Hn := fresh "Hn" in
    intros a Ha Hst Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w5b_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33, ?U34 in Hb; apply Hn; cbv beta; lia | ]);
    destruct Hr
  | ]
  end end.
(* the chunks of the end state's regions over R + 0x98 .. 0xb8, R + 0x108 .. 0x148, pp->len and pp + at (its first,
   second, fourth and fifth) *)
Ltac op_chunks U9 U33 U34 :=
  lazymatch goal with HSf : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  let HM := fresh "HM" in pose proof HSf as (_ & _ & _ & _ & _ & _ & _ & (_ & HM & _) & _);
  cbn [ss_mem restrict ms_mem] in HM;
  let RrA := fresh "RrA" in let RrB := fresh "RrB" in let Rln := fresh "Rln" in let Rat := fresh "Rat" in
  apply Forall_cons_iff in HM as [RrA HM]; apply Forall_cons_iff in HM as [RrB HM];
  apply Forall_cons_iff in HM as [_ HM];
  apply Forall_cons_iff in HM as [Rln HM]; apply Forall_cons_iff in HM as [Rat _];
  destruct RrA as (_ & _ & _ & CrA); destruct RrB as (_ & _ & _ & CrB);
  destruct Rln as (_ & _ & _ & Cln); destruct Rat as (_ & _ & _ & Cat);
  cbn [r_chunks r_base base_val] in CrA, CrB, Cln, Cat;
  rewrite U9 in CrA, CrB; rewrite U33 in Cln; rewrite U34 in Cat;
  rewrite Forall_forall in CrA, CrB, Cln, Cat;
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _)
  end.
(* a cell of the end state's region: its chunk's value *)
Ltac op_cellv E C base off e v :=
  apply (val_of_chunk_ok rsegs E _ base off 8 e v);
  [ apply C; op_inl | | change (8 * Z.of_N 8) with 64; lia | lia ].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* pp is a block of the harness, apart from the image, so apart from the constant at 0x10418 *)
Lemma op_pp_k : forall ly S W mem md pp, AR rsegs B ly S W mem md -> In (pp, 19744) (ablocks B ly S) ->
pp + 19744 <= 0x10418 \/ 0x10420 <= pp.
Proof using LAWS.
intros ly S W mem md pp HAR Hin.
destruct (Z_le_gt_dec (pp + 19744) 0x10418) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec 0x10420 pp) as [H'|H']; [right; exact H'|]. exfalso.
apply (blk_img rsegs B LAWS ly S W mem md pp 19744 (Z.max pp 0x10418) HAR Hin).
- change (req_size 19744) with 19744. lia.
- apply op_img. lia.
Qed.

(* ======================================== (a) in.n = 0 ======================================== *)
Lemma w5b_open_core_nil : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp atv nps cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 nps -> getr regs 6 = w64 (-0x4001) -> getr regs 9 = w64 R ->
  getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 25 = w64 1 -> getr regs 26 = w64 cur -> getr regs 27 = w64 (F + 0x20) -> getr regs 29 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 -> 0 <= F -> F + 1024 <= 2 ^ 47 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nps <= 3 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  nl = 0 ->
  SRr rsegs W (cfg_at rsegs 0x81210 regs memc mdc)
    (w5b_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x824c0
      [10; 11; 12; 13; 15; 16; 22; 25]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x98 <= a < R + 0xb8))
      (fun W2 regs2 mem2 =>
        rtmb_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa0) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa8) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xb0) 8 nps /\
        getr regs2 25 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
  HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
  HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hnl0.
subst nl.
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh. clear Happ.
change (2 ^ 47) with 140737488355328 in H47, Hcn, HF1.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V120 by reflexivity.
rewrite (op_lnot pp ltac:(lia)) in V108.
assert (Hsh8 : 0 <= (pp + 0x4000) / 8 < 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (E := Ereg regs (op_extra0 pp atv)).
assert (E5 : ew E 5 = w64 nps) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E14 : ew E 14 = w64 1) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E26 : ew E 26 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = w64 (F + 0x20)) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 W5B_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 (18446744073709551615 - pp)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (HE : E = Ereg regs (op_extra0 pp atv)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5b_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 34 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = cur) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5B_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5B_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp + atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = 18446744073709551615 - pp) by (rewrite E36; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5b_sr op_ov0) regs).
{ apply (w5b_regs_ok E regs (op_extra0 pp atv)); [exact HE|]. unfold op_ov0. apply Forall_app. split.
  - exact (op_ov_ok E regs _ R pp HE E9 E33 E32 ltac:(lia) ltac:(lia) ltac:(lia) H2 H18 H20 H6 H25).
  - apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] | apply Forall_nil].
    cbn [fst snd]. rewrite H29, denot_lit_U, U_SLit. reflexivity. }
assert (HFK : facts_ok E (mkFacts op_atoms0 [op_cap1; op_cap2] op_alias0)).
{ split; [| split].
  - cbn [f_atoms op_atoms0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U26, U32, U33, U34, U35, U36.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap1_ok E atv U35 ltac:(lia)) |].
    split; [exact (op_cap2_ok E atv U35 ltac:(lia)) | exact I].
  - cbn [f_alias op_alias0 alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 33 pp E33), (U_atom E 35 atv E35), (U_atom E 34 (pp + atv) E34) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E ss_op_nil (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81210) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_nil.
  apply (w5b_entry rsegs _ _ regs (op_extra0 pp atv) E); [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_rA, op_rB, op_rC, op_len, op_at.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_nil]]]]].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 9 R);
        [exact U9 | lia | lia | intros o Ho; apply Hpres; lia | apply Forall_nil].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 36 0) (18446744073709551615 - pp));
          [ rewrite (w5b_den_off E 36 (18446744073709551615 - pp) 0 E36) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SLit OP_C2) OP_C2);
          [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V120 ].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (SOff 27 0x1f0) (F + 0x210));
          [ rewrite (w5b_den_off E 27 (F + 0x20) 0x1f0 E27) by lia; unfold w64; f_equal; lia
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V150 ].
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 33 0) pp);
          [ rewrite (w5b_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V168 ].
      * apply (chunk_ok_val rsegs E _ R 0x170 8 (w5b_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (w5b_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | unfold shadow_addr, SHADOW_OFF; change (8 * Z.of_N 8) with 64; lia | lia | exact V170 ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 35 0) atv);
        [ rewrite (w5b_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 34 (pp + atv));
        [ exact U34 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
  - unfold op_rA, op_rB, op_rC, op_len, op_at. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [r_base r_lo r_hi base_val]. rewrite U9, U33, U34. repeat split; try exact I; lia. }
unfold cfg_at. change (w64 0x81210) with (Z_to_bv 64 0x81210).
aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x824c0.
all: try (op_awr R sp0 pp atv U9 U33 U34 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 ([10; 11; 12; 13; 15; 16; 22; 25]%bv : list (bv 5)) U9 U33 U34 MTL.
all: op_chunks U9 U33 U34.
all: split; [op_bytes8 E Cat|].
all: split;
  [ op_cellv E Cln pp 0x4000 (SOff 35 8) (atv + 8); rewrite (w5b_den_off E 35 atv 8 E35) by lia; reflexivity |].
all: split; [ op_cellv E CrA R 0x98 (SOff 14 0) 1; rewrite (w5b_den_off E 14 1 0 E14) by lia; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xa0 (SOff 35 0) atv; rewrite (w5b_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xa8 (SOff 34 0) (pp + atv); rewrite (w5b_den_off E 34 (pp + atv) 0 E34) by lia;
    rewrite Z.add_0_r; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xb0 (SOff 5 0) nps; rewrite (w5b_den_off E 5 nps 0 E5) by lia; rewrite Z.add_0_r; reflexivity |].
all: transitivity (sv_denot E (SLit 0)); [ exact (HRf 25%bv) | reflexivity ].
Qed.

(* ===================== (b), (c) with the input outside the constant: one lemma, z the count's case ===================== *)
Lemma op_core_app : forall (z : bool) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp atv nps cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 nps -> getr regs 6 = w64 (-0x4001) -> getr regs 9 = w64 R ->
  getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 25 = w64 1 -> getr regs 26 = w64 cur -> getr regs 27 = w64 (F + 0x20) -> getr regs 29 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 -> 0 <= F -> F + 1024 <= 2 ^ 47 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nps <= 3 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> amem_range cur 1 -> ~ (0x10418 <= cur < 0x10420) ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R + 0x58 <= cur < R + 0x148) -> ~ (R + 0x150 <= cur < R + 0x180) ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
  (if z then b mod 33 = 0 else b mod 33 <> 0) ->
  SRr rsegs W (cfg_at rsegs 0x81210 regs memc mdc)
    (w5b_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if z then 0x824c0 else 0x813a0)
      [10; 11; 12; 13; 15; 16; 22; 25; 26]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x98 <= a < R + 0xb8) \/
        (R + 0x140 <= a < R + 0x148))
      (fun W2 regs2 mem2 =>
        rtmb_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa0) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa8) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xb0) 8 nps /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 (b mod 33) /\
        getr regs2 25 = w64 (nl - 1) /\ getr regs2 26 = w64 (cur + 1) /\ getr regs2 22 = w64 (F + 0x210) /\
        (z = false -> getr regs2 11 = w64 0))).
Proof using MTL LAWS.
intros z STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
  HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
  HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom Hamem Hrk Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hz.
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ. rewrite HPS in Hpp, Hfresh, Hc1.
change (2 ^ 47) with 140737488355328 in H47, Hcn, HF1.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V120 by reflexivity.
rewrite (op_lnot pp ltac:(lia)) in V108.
assert (Hsh8 : 0 <= (pp + 0x4000) / 8 < 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
destruct (rtmb_ra_cell _ _ _ Hra) as (s & Hs & Hok).
assert (Hs0e : exists s0 : bool, if s0 then s = 0 else s <> 0)
by (destruct (Z.eq_dec s 0); [exists true | exists false]; assumption).
destruct Hs0e as (s0 & Hs0).
assert (Hs8 : 0 <= s < 8).
{ destruct s0; [change (s = 0) in Hs0; lia | change (s <> 0) in Hs0; destruct (rtmb_ra_slow cur s Hok Hs0); lia]. }
pose proof (Z.mod_pos_bound b 33 ltac:(lia)) as Hb33.
assert (Hdiv : 0 <= cur / 8 < 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (E := Ereg regs (op_extra1 pp atv cur b s)).
assert (E5 : ew E 5 = w64 nps) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E14 : ew E 14 = w64 1) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E26 : ew E 26 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = w64 (F + 0x20)) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E29 : ew E 29 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 29 29%bv eq_refl); exact H29).
assert (E32 : ew E 32 = Z_to_bv 64 W5B_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 (18446744073709551615 - pp)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 (shadow_of_addr SHADOW_OFF cur)) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = w64 b) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = w64 s) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (HE : E = Ereg regs (op_extra1 pp atv cur b s)) by reflexivity. clearbody E.
set (sa := shadow_of_addr SHADOW_OFF cur) in *.
assert (Hsa : W5B_SB <= sa < W5B_SB + 17592186044416) by (subst sa; unfold shadow_of_addr, W5B_SB, SHADOW_OFF; lia).
assert (HshA : sa = shadow_of_addr SHADOW_OFF cur) by reflexivity. clearbody sa.
assert (Hsh : sh_ok rsegs w5b_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 34 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = cur) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U29 : bv_unsigned (ew E 29) = nl) by (rewrite E29; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5B_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5B_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp + atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = 18446744073709551615 - pp) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = sa) by (rewrite E37; apply unsigned_lit_small; unfold W5B_SB in Hsa; lia).
assert (U38 : bv_unsigned (ew E 38) = b) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E 39) = s) by (rewrite E39; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5b_sr op_ov) regs).
{ apply (w5b_regs_ok E regs (op_extra1 pp atv cur b s)); [exact HE|].
  exact (op_ov_ok E regs _ R pp HE E9 E33 E32 ltac:(lia) ltac:(lia) ltac:(lia) H2 H18 H20 H6 H25). }
assert (HFK : facts_ok E (mkFacts (op_atoms1 s0) [op_cap1; op_cap2; op_sc s0; op_mz z] op_alias1)).
{ split; [| split].
  - unfold op_atoms1. cbn [f_atoms op_atoms0 app atoms_ok]. unfold afact_ok.
    destruct s0; [change (s = 0) in Hs0 | change (s <> 0) in Hs0]; cbn [op_s0 af_lo af_hi af_al2];
    rewrite U9, U26, U32, U33, U34, U35, U36, U29, U38, U39;
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap1_ok E atv U35 ltac:(lia)) |].
    split; [exact (op_cap2_ok E atv U35 ltac:(lia)) |].
    split; [exact (op_sc_ok E cur s s0 E26 E39 ltac:(lia) Hok Hs0) |].
    split; [exact (op_mz_ok E b z E38 Hb Hz) | exact I].
  - cbn [f_alias op_alias1 alias_ok]. split; [| split; [| exact I]].
    + rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 33 pp E33), (U_atom E 35 atv E35), (U_atom E 34 (pp + atv) E34) by lia.
      apply zcanon_id. unfold M64. lia.
    + apply (shadow_decl_ok E 26 32 37 cur W5B_SB E26 ltac:(lia) E32).
      rewrite E37, HshA. reflexivity. }
assert (HS : st_ok rsegs E (ss_op_in s0 z) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81210) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_in.
  apply (w5b_entry rsegs _ _ regs (op_extra1 pp atv cur b s) E);
    [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_rA, op_rB, op_rC, op_len, op_at, op_cell, op_in, op_k.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 9 R);
        [exact U9 | lia | lia | intros o Ho; apply Hpres; lia | apply Forall_nil].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 36 0) (18446744073709551615 - pp));
          [ rewrite (w5b_den_off E 36 (18446744073709551615 - pp) 0 E36) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SLit OP_C2) OP_C2);
          [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V120 ].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (SOff 27 0x1f0) (F + 0x210));
          [ rewrite (w5b_den_off E 27 (F + 0x20) 0x1f0 E27) by lia; unfold w64; f_equal; lia
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V150 ].
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 33 0) pp);
          [ rewrite (w5b_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V168 ].
      * apply (chunk_ok_val rsegs E _ R 0x170 8 (w5b_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (w5b_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | unfold shadow_addr, SHADOW_OFF; change (8 * Z.of_N 8) with 64; lia | lia | exact V170 ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 35 0) atv);
        [ rewrite (w5b_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 34 (pp + atv));
        [ exact U34 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
    + apply (rtmb_cell_region rsegs E (w_H W) memc 37 sa s (SOff 39 0) U37 Hs);
        [ rewrite (w5b_den_off E 39 s 0 E39) by lia; rewrite Z.add_0_r; reflexivity
        | unfold W5B_SB in Hsa; lia | unfold W5B_SB in Hsa; lia ].
    + apply (rtmb_cell_region rsegs E (w_H W) memc 26 cur b (SOff 38 0) U26 (rtmb_val1_aview rsegs _ _ _ _ Vb Hb));
        [ rewrite (w5b_den_off E 38 b 0 E38) by lia; rewrite Z.add_0_r; reflexivity | lia | lia ].
    + apply (RtPgStepsB.img_region_ok_rom E W memc 0x10418 8); [exact Hrom | lia | lia | lia | vm_compute; reflexivity].
  - assert (Fpp_sa : pp + 19744 <= sa \/ sa + 1 <= pp).
    { clear - Happ Hsa C3. unfold in_app in Happ. rewrite C3 in Happ. unfold kLowShadowBeg in Happ.
      unfold W5B_SB in Hsa. lia. }
    assert (Fcur_sa : cur + 1 <= sa \/ sa + 1 <= cur).
    { clear - Hamem Hsa C3 C5. unfold amem_range in Hamem. rewrite C3, C5 in Hamem. unfold W5B_SB in Hsa. lia. }
    assert (Fpp_k : pp + 19744 <= 0x10418 \/ 0x10420 <= pp) by exact (op_pp_k lyc Sc W memc mdc pp HAR Hpp).
    clear Happ Hamem Hz Hs0 Hok.
    unfold op_rA, op_rB, op_rC, op_len, op_at, op_cell, op_in, op_k. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U33, U34, U26, U37.
    unfold W5B_SB in Hsa. repeat split; try exact I; lia. }
destruct s0, z.
all: unfold cfg_at; change (w64 0x81210) with (Z_to_bv 64 0x81210).
all: [> aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x824c0 | aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x813a0
 | aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x824c0 | aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x813a0 ].
all: try (op_awr R sp0 pp atv U9 U33 U34 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 ([10; 11; 12; 13; 15; 16; 22; 25; 26]%bv : list (bv 5)) U9 U33 U34 MTL.
all: op_chunks U9 U33 U34.
all: split; [op_bytes8 E Cat|].
all: split;
  [ op_cellv E Cln pp 0x4000 (SOff 35 8) (atv + 8); rewrite (w5b_den_off E 35 atv 8 E35) by lia; reflexivity |].
all: split; [ op_cellv E CrA R 0x98 (SOff 14 0) 1; rewrite (w5b_den_off E 14 1 0 E14) by lia; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xa0 (SOff 35 0) atv; rewrite (w5b_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xa8 (SOff 34 0) (pp + atv); rewrite (w5b_den_off E 34 (pp + atv) 0 E34) by lia;
    rewrite Z.add_0_r; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xb0 (SOff 5 0) nps; rewrite (w5b_den_off E 5 nps 0 E5) by lia; rewrite Z.add_0_r; reflexivity |].
all: split; [ op_cellv E CrB R 0x140 op_M (b mod 33); rewrite denot_lit_U, (op_U_M E b E38 Hb); reflexivity |].
all: split;
  [ transitivity (sv_denot E (SOff 29 (-1)));
    [ exact (HRf 25%bv) | rewrite (w5b_den_off E 29 nl (-1) E29) by lia; reflexivity ] |].
all: split;
  [ transitivity (sv_denot E (SOff 26 1));
    [ exact (HRf 26%bv) | rewrite (w5b_den_off E 26 cur 1 E26) by lia; reflexivity ] |].
all: split;
  [ transitivity (sv_denot E (SOff 27 0x1f0));
    [ exact (HRf 22%bv) | rewrite (w5b_den_off E 27 (F + 0x20) 0x1f0 E27) by lia; unfold w64; f_equal; lia ] |].
all: intros Hzf; first [ discriminate Hzf | transitivity (sv_denot E (SLit 0)); [exact (HRf 11%bv) | reflexivity] ].
Qed.

(* ===================== (c) with the input inside the constant: cur = 0x10418 + j, eight literal walks ===================== *)
Lemma op_core_rom : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp atv nps cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 nps -> getr regs 6 = w64 (-0x4001) -> getr regs 9 = w64 R ->
  getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 25 = w64 1 -> getr regs 26 = w64 cur -> getr regs 27 = w64 (F + 0x20) -> getr regs 29 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 -> 0 <= F -> F + 1024 <= 2 ^ 47 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nps <= 3 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> 0x10418 <= cur < 0x10420 ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
  SRr rsegs W (cfg_at rsegs 0x81210 regs memc mdc)
    (w5b_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x813a0
      [10; 11; 12; 13; 15; 16; 22; 25; 26]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x98 <= a < R + 0xb8) \/
        (R + 0x140 <= a < R + 0x148))
      (fun W2 regs2 mem2 =>
        rtmb_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa0) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa8) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xb0) 8 nps /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 (b mod 33) /\
        getr regs2 25 = w64 (nl - 1) /\ getr regs2 26 = w64 (cur + 1) /\ getr regs2 22 = w64 (F + 0x210) /\
        getr regs2 11 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
  HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
  HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom Hkin b Hnl0 Vb Hb Hra.
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ. rewrite HPS in Hpp, Hfresh.
change (2 ^ 47) with 140737488355328 in H47, Hcn, HF1.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V120 by reflexivity.
rewrite (op_lnot pp ltac:(lia)) in V108.
assert (Hsh8 : 0 <= (pp + 0x4000) / 8 < 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (op_rom_byte W memc cur b Hrom Vb Hb Hkin) as Hbv.
destruct (rtmb_ra_cell _ _ _ Hra) as (s & Hs & Hok).
assert (Hs0e : exists s0 : bool, if s0 then s = 0 else s <> 0)
by (destruct (Z.eq_dec s 0); [exists true | exists false]; assumption).
destruct Hs0e as (s0 & Hs0).
assert (Hs8 : 0 <= s < 8).
{ destruct s0; [change (s = 0) in Hs0; lia | change (s <> 0) in Hs0; destruct (rtmb_ra_slow cur s Hok Hs0); lia]. }
pose proof (Z.mod_pos_bound b 33 ltac:(lia)) as Hb33.
assert (Hc8 : cur / 8 = 8323) by (symmetry; apply (Z.div_unique cur 8 8323 (cur - 66584)); [left; lia | lia]).
assert (HsaB : shadow_of_addr SHADOW_OFF cur = W5B_SB + 0x2083) by (unfold shadow_of_addr; rewrite Hc8; reflexivity).
rewrite HsaB in Hs.
set (E := Ereg regs (op_extra1 pp atv cur b s)).
assert (E5 : ew E 5 = w64 nps) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E14 : ew E 14 = w64 1) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E26 : ew E 26 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = w64 (F + 0x20)) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E29 : ew E 29 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 29 29%bv eq_refl); exact H29).
assert (E32 : ew E 32 = Z_to_bv 64 W5B_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 (18446744073709551615 - pp)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E39 : ew E 39 = w64 s) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (HE : E = Ereg regs (op_extra1 pp atv cur b s)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5b_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 34 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = cur) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U29 : bv_unsigned (ew E 29) = nl) by (rewrite E29; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5B_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5B_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp + atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = 18446744073709551615 - pp) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E 39) = s) by (rewrite E39; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5b_sr (op_ovB cur)) regs).
{ apply (w5b_regs_ok E regs (op_extra1 pp atv cur b s)); [exact HE|]. unfold op_ovB. apply Forall_app. split.
  - exact (op_ov_ok E regs _ R pp HE E9 E33 E32 ltac:(lia) ltac:(lia) ltac:(lia) H2 H18 H20 H6 H25).
  - apply Forall_cons; [split; [apply w5b_nz; vm_compute; lia|] | apply Forall_nil].
    cbn [fst snd]. rewrite H26, denot_lit_U, U_SLit. unfold w64. rewrite zcanon_id by (unfold M64; lia).
    reflexivity. }
assert (HFK : facts_ok E (mkFacts (op_atomsB s0) [op_cap1; op_cap2; op_scB cur s0] op_alias0)).
{ split; [| split].
  - unfold op_atomsB. cbn [f_atoms op_atoms0 app atoms_ok]. unfold afact_ok.
    destruct s0; [change (s = 0) in Hs0 | change (s <> 0) in Hs0]; cbn [op_s0 af_lo af_hi af_al2];
    rewrite U9, U26, U32, U33, U34, U35, U36, U29, U39;
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap1_ok E atv U35 ltac:(lia)) |].
    split; [exact (op_cap2_ok E atv U35 ltac:(lia)) |].
    split; [exact (op_scB_ok E cur s s0 E39 Hok Hs0) | exact I].
  - cbn [f_alias op_alias0 alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 33 pp E33), (U_atom E 35 atv E35), (U_atom E 34 (pp + atv) E34) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E (ss_op_rom cur s0) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81210) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_rom.
  apply (w5b_entry rsegs _ _ regs (op_extra1 pp atv cur b s) E);
    [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_rA, op_rB, op_rC, op_len, op_at, op_cellB, op_k.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 9 R);
        [exact U9 | lia | lia | intros o Ho; apply Hpres; lia | apply Forall_nil].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SOff 36 0) (18446744073709551615 - pp));
          [ rewrite (w5b_den_off E 36 (18446744073709551615 - pp) 0 E36) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SLit OP_C2) OP_C2);
          [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V120 ].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (SOff 27 0x1f0) (F + 0x210));
          [ rewrite (w5b_den_off E 27 (F + 0x20) 0x1f0 E27) by lia; unfold w64; f_equal; lia
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V150 ].
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 33 0) pp);
          [ rewrite (w5b_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V168 ].
      * apply (chunk_ok_val rsegs E _ R 0x170 8 (w5b_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (w5b_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | unfold shadow_addr, SHADOW_OFF; change (8 * Z.of_N 8) with 64; lia | lia | exact V170 ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 35 0) atv);
        [ rewrite (w5b_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 34 (pp + atv));
        [ exact U34 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 32 W5B_SB 0x2083 0x2084);
        [exact U32 | unfold W5B_SB; lia | unfold W5B_SB; lia |].
      apply Forall_cons; [|apply Forall_nil].
      destruct (rtmb_aview_val1 rsegs _ _ _ _ Hs) as [Vs _].
      apply (chunk_ok_val rsegs E _ W5B_SB 0x2083 1 (SOff 39 0) s);
        [ rewrite (w5b_den_off E 39 s 0 E39) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia | exact Vs ].
    + apply (RtPgStepsB.img_region_ok_rom E W memc 0x10418 8); [exact Hrom | lia | lia | lia | vm_compute; reflexivity].
  - assert (Fpp_sa : pp + 19744 <= W5B_SB + 0x2083 \/ W5B_SB + 0x2084 <= pp).
    { clear - Happ C3. unfold in_app in Happ. rewrite C3 in Happ. unfold kLowShadowBeg in Happ. unfold W5B_SB. lia. }
    assert (Fpp_k : pp + 19744 <= 0x10418 \/ 0x10420 <= pp) by exact (op_pp_k lyc Sc W memc mdc pp HAR Hpp).
    clear Happ Hs0 Hok.
    unfold op_rA, op_rB, op_rC, op_len, op_at, op_cellB, op_k. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U32, U33, U34.
    unfold W5B_SB in *. repeat split; try exact I; lia. }
assert (Hcj : cur = 66584 \/ cur = 66585 \/ cur = 66586 \/ cur = 66587 \/ cur = 66588 \/ cur = 66589 \/
              cur = 66590 \/ cur = 66591) by lia.
destruct Hcj as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; destruct s0.
all: unfold cfg_at; change (w64 0x81210) with (Z_to_bv 64 0x81210).
all: aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x813a0.
all: try (op_awr R sp0 pp atv U9 U33 U34 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 ([10; 11; 12; 13; 15; 16; 22; 25; 26]%bv : list (bv 5)) U9 U33 U34 MTL.
all: op_chunks U9 U33 U34.
all: split; [op_bytes8 E Cat|].
all: split;
  [ op_cellv E Cln pp 0x4000 (SOff 35 8) (atv + 8); rewrite (w5b_den_off E 35 atv 8 E35) by lia; reflexivity |].
all: split; [ op_cellv E CrA R 0x98 (SOff 14 0) 1; rewrite (w5b_den_off E 14 1 0 E14) by lia; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xa0 (SOff 35 0) atv; rewrite (w5b_den_off E 35 atv 0 E35) by lia; rewrite Z.add_0_r; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xa8 (SOff 34 0) (pp + atv); rewrite (w5b_den_off E 34 (pp + atv) 0 E34) by lia;
    rewrite Z.add_0_r; reflexivity |].
all: split;
  [ op_cellv E CrA R 0xb0 (SOff 5 0) nps; rewrite (w5b_den_off E 5 nps 0 E5) by lia; rewrite Z.add_0_r; reflexivity |].
all: split;
  [ lazymatch type of CrB with context [YP09.mkChunk 0x140 (CVal 8 ?e)] =>
      op_cellv E CrB R 0x140 e (b mod 33); rewrite Hbv; reflexivity end |].
all: split;
  [ transitivity (sv_denot E (SOff 29 (-1)));
    [ exact (HRf 25%bv) | rewrite (w5b_den_off E 29 nl (-1) E29) by lia; reflexivity ] |].
all: split; [ etransitivity; [exact (HRf 26%bv) | reflexivity] |].
all: split;
  [ transitivity (sv_denot E (SOff 27 0x1f0));
    [ exact (HRf 22%bv) | rewrite (w5b_den_off E 27 (F + 0x20) 0x1f0 E27) by lia; unfold w64; f_equal; lia ] |].
all: etransitivity; [exact (HRf 11%bv) | reflexivity].
Qed.

(* ======================================== (b) count = 0 ======================================== *)
Lemma w5b_open_core_zero : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp atv nps cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 nps -> getr regs 6 = w64 (-0x4001) -> getr regs 9 = w64 R ->
  getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 25 = w64 1 -> getr regs 26 = w64 cur -> getr regs 27 = w64 (F + 0x20) -> getr regs 29 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 -> 0 <= F -> F + 1024 <= 2 ^ 47 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nps <= 3 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> amem_range cur 1 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R + 0x58 <= cur < R + 0x148) -> ~ (R + 0x150 <= cur < R + 0x180) ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 -> b mod 33 = 0 ->
  SRr rsegs W (cfg_at rsegs 0x81210 regs memc mdc)
    (w5b_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x824c0
      [10; 11; 12; 13; 15; 16; 22; 25; 26]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x98 <= a < R + 0xb8) \/
        (R + 0x140 <= a < R + 0x148))
      (fun W2 regs2 mem2 =>
        rtmb_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa0) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa8) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xb0) 8 nps /\
        getr regs2 25 = w64 (nl - 1) /\ getr regs2 26 = w64 (cur + 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
  HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
  HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom Hamem Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm.
destruct (Z_lt_le_dec cur 0x10418) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec cur 0x10420) as [Hhi|Hhi]].
2: { exfalso. apply (op_kbyte_mod (cur - 0x10418) ltac:(lia)).
     rewrite <- (op_rom_byte W memc cur b Hrom Vb Hb ltac:(lia)). exact Hm. }
all: eapply SRr_mono;
  [ exact (op_core_app true STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
      HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
      HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom Hamem ltac:(lia) Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm) |].
all: intros W' c' _ (ly2 & S2 & regs2 & mem2 & md2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 &
  (Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & _ & Q16 & Q17 & _)).
all: exists ly2, S2, regs2, mem2, md2.
all: exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
       (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 (conj Q16 Q17))))))))))))))).
Qed.

(* ======================================== (c) count <> 0 ======================================== *)
Lemma w5b_open_core_pos : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pp atv nps cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 nps -> getr regs 6 = w64 (-0x4001) -> getr regs 9 = w64 R ->
  getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 25 = w64 1 -> getr regs 26 = w64 cur -> getr regs 27 = w64 (F + 0x20) -> getr regs 29 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (Z.lnot pp mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 -> 0 <= F -> F + 1024 <= 2 ^ 47 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nps <= 3 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> amem_range cur 1 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R + 0x58 <= cur < R + 0x148) -> ~ (R + 0x150 <= cur < R + 0x180) ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 -> b mod 33 <> 0 ->
  SRr rsegs W (cfg_at rsegs 0x81210 regs memc mdc)
    (w5b_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x813a0
      [10; 11; 12; 13; 15; 16; 22; 25; 26]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x98 <= a < R + 0xb8) \/
        (R + 0x140 <= a < R + 0x148))
      (fun W2 regs2 mem2 =>
        rtmb_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa0) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa8) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xb0) 8 nps /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 (b mod 33) /\
        getr regs2 25 = w64 (nl - 1) /\ getr regs2 26 = w64 (cur + 1) /\ getr regs2 22 = w64 (F + 0x210) /\
        getr regs2 11 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
  HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
  HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom Hamem Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm.
destruct (Z_lt_le_dec cur 0x10418) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec cur 0x10420) as [Hhi|Hhi]].
2: { exact (op_core_rom STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
       HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
       HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom ltac:(lia) b Hnl0 Vb Hb Hra). }
all: eapply SRr_mono;
  [ exact (op_core_app false STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F pp atv nps cur nl
      HJ Hpp Hfresh H2 H5 H6 H9 H14 H18 H20 H25 H26 H27 H29 V108 V120 V150 V168 V170 Vlen
      HR16 HRlo HRhi HF0 HF1 Hat Hal Hnps Hnl Hcur Hcn Hrom Hamem ltac:(lia) Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm) |].
all: intros W' c' _ (ly2 & S2 & regs2 & mem2 & md2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 &
  (Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19)).
all: exists ly2, S2, regs2, mem2, md2.
all: exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
       (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 (conj Q15 (conj Q16 (conj Q17 (conj Q18
       (Q19 eq_refl))))))))))))))))))).
Qed.
End c.

Print Assumptions w5b_open_core_nil.
Print Assumptions w5b_open_core_zero.
Print Assumptions w5b_open_core_pos.
