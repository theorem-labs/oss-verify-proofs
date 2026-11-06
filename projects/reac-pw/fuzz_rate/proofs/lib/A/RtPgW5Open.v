(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 768 of its 825 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Open.v at 635914e101a0 for reac-pw/fuzz_rate's
   image A: module paths changed; rate's pcs (SELS 0x81150 -> C 0x8127c / CL 0x82484, the slow block 0x82608, the
   constant at .rodata 0x10408), registers (s6 / s7 / s2 for role's s4 / s5 / s7; the capacity bound -0x4001 is s10 and
   what is left of the input is s8, for role's cells R+0xe0 and R+0xf8) and real-frame cells (at R+0xe0, the cursor
   R+0x100, -0x3ffd at R+0x130, the count R+0xf0, for role's R+0xa0 / 0xc8 / 0xe8 / 0xa8); the shadow byte's address,
   the input byte and the shadow byte are atoms 36 .. 38; rm_ / rl_ become rtm_ / rt_. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the params Struct's header and its pod count,
   SELS 0x81150 -> C 0x8127c or CL 0x82484, in LLVMFuzzerTestOneInput (pod.h:421-425, fuzz.h:37-43), as three core
   lemmas, one per exit: w5_open_core_nil (in.n = 0, to 0x82484), w5_open_core_zero (count = fuzz_u8 % 33 = 0, to
   0x82484) and w5_open_core_pos (count <> 0, to 0x8127c). Proves no function (kind: segment lemma).

   THE CODE
     0x81150  ld s9,0x100(s1) (the cursor cur); bltu a0,s10 (a0 = at - 0x3ffd, s10 = -0x4001: the capacity test, not
              taken: the fact of atom 10)
     0x81158-0x811b0  pod_put32(pp, 0) at pp + at (two covered checks, four `sb zero`, the check of pp->len, len += 4)
     0x811b4-0x81228  the capacity test again (`ld a1,0x130(s1)`, `bltu a1,s10`, not taken: the condition op_cap) and
              pod_put32(pp, 14), len += 4
     0x8122c  bnez s8 (in.n): if 0, 0x81230 `j 0x82484`
     0x81234-0x81244  the check of the 1-byte load at cur, `lb t,0(sh); beqz t,+8; j 0x82608`, with the slow block
              0x82608 `andi a1,s9,7; bge a1,a0,report; j 0x81248`
     0x81248  lbu a0,0(s9); 0x8124c-0x81250 auipc/ld a1 of the constant 0x07c1f07c1f07c1f1 at 0x10408; s8 -= 1
     0x81258-0x81264  mulhu/slli/or/sub: count = b mod 33; s9 += 1; sd a1,0xf0(s1); 0x81270 bnez a1: if 0
              `j 0x82484`, else 0x81278 `mv a1,zero` and 0x8127c.
   Every check on pp is covered by the shadow entries (27, 0x4000, 0x4008) and (33, 0, 16) (w5_shent_blk).

   THE INPUT READ. The engine's token path cannot follow this check (its slow block is reached only by the `j`); so
   the shadow byte s of cur is a read-only region at atom 36 (the shadow address SHADOW_OFF + cur / 8, named by an
   f_alias entry), the `lb` is a region load, and the start facts carry the conditions the two branches need: s = 0
   (the `beqz` is taken) or 0 < s < 8 and cur mod 8 < s (the slow block's `bge` is not taken), both from saddr_ok
   cur s, which range_addressable cur 1 gives (rtm_ra_cell, rtm_ra_slow_bv). The count's `bnez` is decided by the
   condition b mod 33 = 0 or <> 0 of the exit. The input byte b is a read-only region at atom 35 (cur), the constant
   a base-free region of the image's bytes (img_region_ok_rom from rom_view); the two must be apart, so the case
   0x10408 <= cur < 0x10410 (the input inside the constant) is walked on its own with cur a literal: there b is the
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgW5Kit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the start states at 0x81150 ========================================
   atoms: 9 = R, 10 = at - 0x3ffd (wrapped), 24 = in.n (s8), 27 = pp, 32 = K, 33 = pp + at, 34 = at, 35 = cur,
   36 = SHADOW_OFF + cur / 8, 37 = b, 38 = s. *)
Definition OP_C1 : Z := 18446744073709535231.  (* (-0x4001) mod 2^64 *)
Definition OP_C2 : Z := 18446744073709535235.  (* (-0x3ffd) mod 2^64 *)
Definition OP_K33 : Z := 558992244657865201.   (* 0x07c1f07c1f07c1f1, the 8 bytes at 0x10408 *)
(* s1 = R as sp, s6 = the shadow address of &pp->len, s7 = &pp->len, s2 = K, s10 = -0x4001 *)
Definition op_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((22%bv : bv 5), w5_sh 27 0x4000); ((23%bv : bv 5), SOff 27 0x4000);
   ((18%bv : bv 5), w5_Bx); ((26%bv : bv 5), SLit OP_C1)].
(* no input left: s8 = 0 *)
Definition op_ov0 : list (bv 5 * sv) := op_ov ++ [((24%bv : bv 5), SLit 0)].
(* the real frame's cells R + 0xe0 (at) and R + 0x100 (the cursor, ec the value the cell holds), with the write
   window [wlo, whi) (R + 0xf0, the count, when the count byte is read) *)
Definition op_r1 (wlo whi : Z) (ec : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xe0 0x108 wlo whi
   [YP09.mkChunk 0xe0 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x100 (CVal 8 ec)].
(* R + 0x130: -0x3ffd, the second capacity test's addend *)
Definition op_r2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0 [YP09.mkChunk 0x130 (CVal 8 (SLit OP_C2))].
Definition op_len : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0))].
Definition op_at : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 8 [].
Definition op_cell : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition op_in : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition op_k : YP09.region := YP09.mkRegion None 0x10408 0x10410 0 0 [YP09.mkChunk 0x10408 (CImg 8)].
(* the input inside the constant (cur = 0x10408 + j): the shadow byte at K + 0x2081 *)
Definition op_cellB : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x2081 0x2082 0 0 [YP09.mkChunk 0x2081 (CVal 1 (SOff 38 0))].
(* the second capacity test: len + 4 - 0x3ffd >= -0x4001, unsigned *)
Definition op_cap : acond := mkAC BC_GEU (SOff 34 (-16377)) (SLit OP_C1).
(* the shadow byte: 0, or the slow block's `bge cur & 7, s` not taken *)
Definition op_slow : acond := mkAC BC_LT (SAlu ALU_AND (SOff 35 0) (SLit 7)) (SOff 38 0).
Definition op_s0 (s0 : bool) : afact := if s0 then mkAF 0 0 0 else mkAF 1 7 0.
Definition op_sc (s0 : bool) : acond := if s0 then mkAC BC_EQ (SOff 38 0) (SLit 0) else op_slow.
Definition op_scB (cj : Z) (s0 : bool) : acond :=
  if s0 then mkAC BC_EQ (SOff 38 0) (SLit 0) else mkAC BC_LT (SLit (cj mod 8)) (SOff 38 0).
(* count = b - ((q << 5) | q), q = mulhu(b, K33), as the engine forms it *)
Definition op_M : sv :=
  SAlu ALU_SUB (SOff 37 0)
    (SAlu ALU_OR (SAlu ALU_SLL (SMd M_MULHU (SOff 37 0) (SLit OP_K33)) (SLit 5)) (SMd M_MULHU (SOff 37 0) (SLit OP_K33))).
Definition op_mz (z : bool) : acond := mkAC (if z then BC_EQ else BC_NE) op_M (SLit 0).
Definition op_atoms0 : list (nat * afact) :=
  [(9%nat, mkAF 70368744177664 140737488355328 4); (10%nat, mkAF 18446744073709535251 18446744073709540667 0);
   (27%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF W5_SB W5_SB 0);
   (33%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 16 5432 0); (35%nat, mkAF 1 140737488355328 0)].
Definition op_atoms1 (s0 : bool) : list (nat * afact) :=
  op_atoms0 ++ [(24%nat, mkAF 1 140737488355328 0); (37%nat, mkAF 0 255 0); (38%nat, op_s0 s0)].
Definition op_atomsB (s0 : bool) : list (nat * afact) :=
  op_atoms0 ++ [(24%nat, mkAF 1 140737488355328 0); (38%nat, op_s0 s0)].
Definition op_alias0 : list (sv * sv) := [(SAlu ALU_ADD (SOff 27 0) (SOff 34 0), SOff 33 0)].
Definition op_alias1 : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 27 0) (SOff 34 0), SOff 33 0);
   (SAlu ALU_ADD (SAlu ALU_SRL (SOff 35 0) (SLit 3)) (SOff 32 0), SOff 36 0)].
Definition ss_op_nil : sstate :=
  mkSS 0x81150 (w5_sr op_ov0) [op_r1 0 0 (SOff 35 0); op_r2; op_len; op_at] None
    (mkFacts op_atoms0 [op_cap] op_alias0).
Definition ss_op_in (s0 z : bool) : sstate :=
  mkSS 0x81150 (w5_sr op_ov) [op_r1 0xf0 0xf8 (SOff 35 0); op_r2; op_len; op_at; op_cell; op_in; op_k] None
    (mkFacts (op_atoms1 s0) [op_cap; op_sc s0; op_mz z] op_alias1).
Definition ss_op_rom (cj : Z) (s0 : bool) : sstate :=
  mkSS 0x81150 (w5_sr op_ov) [op_r1 0xf0 0xf8 (SLit cj); op_r2; op_len; op_at; op_cellB; op_k] None
    (mkFacts (op_atomsB s0) [op_cap; op_scB cj s0] op_alias0).
Definition op_SH : list shent := [mkSHE 27 0x4000 0x4008; mkSHE 33 0 16].
Definition op_extra0 (pp atv cur : Z) : list word := [w64 W5_SB; w64 (pp + atv); w64 atv; w64 cur].
Definition op_extra1 (pp atv cur b s : Z) : list word :=
  op_extra0 pp atv cur ++ [w64 (shadow_of_addr SHADOW_OFF cur); w64 b; w64 s].

(* ======================================== arithmetic ======================================== *)
Lemma op_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma op_u_neg : forall x, -18446744073709551616 <= x < 0 ->
bv_unsigned (Z_to_bv 64 x) = x + 18446744073709551616.
Proof.
intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 (-1)); lia.
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
Lemma op_U_M : forall E b, ew E 37 = Z_to_bv 64 b -> 0 <= b < 256 -> U E op_M = b mod 33.
Proof.
intros E b H37 Hb. unfold op_M. rewrite !U_SAlu, !U_SMd, !U_SLit.
rewrite (U_atom E 37 b H37) by lia. exact (op_mod_fn_ok b Hb).
Qed.
Lemma op_cap_ok : forall E atv, bv_unsigned (ew E 34) = atv -> 16 <= atv <= 5432 -> acond_ok E op_cap.
Proof.
intros E atv H34 Ha. unfold acond_ok, op_cap. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, U_SOff, H34, U_SLit.
rewrite (op_zc (atv + -16377) (-1) (atv - 16377 + 18446744073709551616)) by lia.
rewrite (op_zc OP_C1 0 OP_C1) by (unfold OP_C1; lia).
apply negb_true_iff, Z.ltb_ge. unfold OP_C1. lia.
Qed.
Lemma op_mz_ok : forall E b (z : bool), ew E 37 = Z_to_bv 64 b -> 0 <= b < 256 ->
(if z then b mod 33 = 0 else b mod 33 <> 0) -> acond_ok E (op_mz z).
Proof.
intros E b z H37 Hb Hz. unfold acond_ok, op_mz. destruct z; cbn [ac_c ac_a ac_b].
- change (b mod 33 = 0) in Hz. rewrite branch_eq_U, (op_U_M E b H37 Hb), U_SLit, Hz. reflexivity.
- change (b mod 33 <> 0) in Hz. rewrite branch_ne_U, (op_U_M E b H37 Hb), U_SLit.
  change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hz.
Qed.
Lemma op_sc_ok : forall E cur s (s0 : bool), ew E 35 = Z_to_bv 64 cur -> ew E 38 = Z_to_bv 64 s ->
0 <= cur < 2 ^ 64 -> saddr_ok cur s -> (if s0 then s = 0 else s <> 0) -> acond_ok E (op_sc s0).
Proof.
intros E cur s s0 H35 H38 Hc Hok Hs. unfold acond_ok. destruct s0; cbn [op_sc ac_c ac_a ac_b].
- change (s = 0) in Hs. subst s. rewrite branch_eq_U, U_SOff, H38, U_SLit. reflexivity.
- change (s <> 0) in Hs. unfold op_slow. cbn [ac_c ac_a ac_b].
  destruct (rtm_ra_slow cur s Hok Hs) as [Hs1 Hs2].
  assert (A1 : sv_denot E (SAlu ALU_AND (SOff 35 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
  { change (sv_denot E (SAlu ALU_AND (SOff 35 0) (SLit 7))) with
      (alu64 ALU_AND (sv_denot E (SOff 35 0)) (sv_denot E (SLit 7))).
    rewrite (w5_den_off E 35 cur 0 H35) by lia. rewrite Z.add_0_r. apply alu_and7. unfold M64. lia. }
  rewrite A1, (w5_den_off E 38 s 0 H38) by lia. rewrite Z.add_0_r.
  exact (rtm_ra_slow_bv cur s Hok Hs).
Qed.
Lemma op_scB_ok : forall E cj s (s0 : bool), ew E 38 = Z_to_bv 64 s ->
saddr_ok cj s -> (if s0 then s = 0 else s <> 0) -> acond_ok E (op_scB cj s0).
Proof.
intros E cj s s0 H38 Hok Hs. unfold acond_ok. destruct s0; cbn [op_scB ac_c ac_a ac_b].
- change (s = 0) in Hs. subst s. rewrite branch_eq_U, U_SOff, H38, U_SLit. reflexivity.
- change (s <> 0) in Hs. destruct (rtm_ra_slow cj s Hok Hs) as [Hs1 Hs2].
  rewrite (w5_den_off E 38 s 0 H38) by lia. rewrite Z.add_0_r.
  exact (rtm_ra_slow_bv cj s Hok Hs).
Qed.
(* the constant's eight bytes lie in the image's read-only segment *)
Lemma op_in_rom : forall a, 0x10408 <= a < 0x10410 -> in_rom rsegs a.
Proof.
intros a Ha. apply RtPgSteps.in_rom_b_ok.
assert (Hi8 : a = 66568 \/ a = 66569 \/ a = 66570 \/ a = 66571 \/ a = 66572 \/ a = 66573 \/ a = 66574 \/ a = 66575)
by lia.
destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma op_img : forall a, 0x10408 <= a < 0x10410 -> in_img rsegs a.
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
0x10408 <= cur < 0x10410 -> b = Z.shiftr OP_K33 (8 * (cur - 0x10408)) mod 256.
Proof.
intros W memc cur b HR V Hb Hk.
pose proof (rtm_val1_aview rsegs _ _ _ _ V Hb) as A.
pose proof (HR cur (op_in_rom cur Hk)) as Hv. rewrite A in Hv.
assert (Hall : forall i, 0 <= i < 8 ->
  option_map (fun x : byte => bv_unsigned x) (seg_rom rsegs (Z_to_bv 64 (0x10408 + i))) =
  Some (Z.shiftr OP_K33 (8 * i) mod 256)).
{ intros i Hi. assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity. }
specialize (Hall (cur - 0x10408) ltac:(lia)). replace (0x10408 + (cur - 0x10408)) with cur in Hall by lia.
rewrite Hall in Hv. injection Hv as Hv. exact Hv.
Qed.
End r.

Section e. Context {fx : YK11.FPState}.
(* the five registers every start state overrides hold their values *)
Lemma op_ov_ok : forall E regs extra R pp, E = Ereg regs extra ->
  ew E 9 = w64 R -> ew E 27 = w64 pp -> ew E 32 = Z_to_bv 64 W5_SB ->
  0 <= R < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 63 ->
  getr regs 2 = w64 R -> getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
  getr regs 23 = w64 (pp + 0x4000) -> getr regs 26 = w64 (-0x4001) ->
  Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) op_ov.
Proof.
intros E regs extra R pp HE E9 E27 E32 HR Hp1 Hp2 H2 H18 H22 H23 H26. unfold op_ov.
apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite (w5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite (w5_den_sh E 27 pp 0x4000 E27 E32) by lia. rewrite H22. reflexivity. }
apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite (w5_den_off E 27 pp 0x4000 E27) by lia. rewrite H23. reflexivity. }
apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
{ cbn [fst snd]. unfold w5_Bx. rewrite (w5_den_off E 32 W5_SB 0 E32) by (unfold W5_SB; lia).
  rewrite Z.add_0_r, H18. reflexivity. }
apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] |].
{ cbn [fst snd]. rewrite H26, denot_lit_U, U_SLit. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
  vm_compute. reflexivity. }
apply Forall_nil.
Qed.
End e.

(* ======================================== tactics of the posts ======================================== *)
Ltac op_inl := cbn [In]; repeat (first [left; reflexivity | right]).
(* the eight bytes pod_put32(0), pod_put32(14) wrote at pp + at, from the end state's one-byte chunks *)
Ltac op_bytes8 E Cat :=
  apply rtm_bytes_aview; intros i Hi; rewrite length_app, !length_Z_to_le_bytes in Hi; unfold aview;
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | | lia];
  lazymatch goal with |- option_map _ (mbyte _ ?m (?base + Z.of_nat ?n)) = Some (bv_unsigned (nth _ ?l _)) =>
    let o := eval cbv in (Z.of_nat n) in
    let v := eval vm_compute in (bv_unsigned (nth n l (Z_to_bv 8 0))) in
    let HB := fresh "HB" in
    assert (HB : mbyte rsegs m (base + o) = Some (Z_to_bv 8 (U E (SLit v))));
    [ apply (w5_mbyte_chunk1 rsegs E); apply Cat; op_inl |];
    change (base + Z.of_nat n) with (base + o); rewrite HB, U_SLit; reflexivity
  end.
(* the write windows of a start state: the real frame's cells on the stack, pp->len and pp + at in pp *)
Ltac op_awr R sp0 pp atv U9 U27 U33 Hpp Hfresh :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
    [ reflexivity | rewrite U9; lia | cbn [r_wlo r_whi]; lia | cbn [r_wlo r_whi]; lia | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat pp);
    [ reflexivity | exact U27
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (pp + atv));
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ].
(* the post up to its last clause: the cfg, the journal, the registers outside the clobber list, frames, blocks,
   I/O, meter, and every byte outside the start state's write windows *)
Ltac op_post_frame E W memc HJ HR0 sr0 clob U9 U27 U33 MTL :=
  apply SRr_ret; unfold w5_post;
  lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  do 2 eexists; exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    let HRf := fresh "HRf" in pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
    exact (w5_regs_kept E Ef 40 sr0 (ss_regs ssf) _ (ms_regs msf) clob HR0 HRf
             (env_agree_refl 40 E) ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply w5_same_io_wvb]|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hst := fresh "Hst" in let Hn := fresh "Hn" in
    intros a Ha Hst Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (w5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U27, ?U33 in Hb; apply Hn; cbv beta; lia | ]);
    destruct Hr
  | ]
  end.
(* the chunks of the end state's regions over R + 0xe0, pp->len and pp + at (its first, third and fourth) *)
Ltac op_chunks U9 U27 U33 :=
  lazymatch goal with HSf : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  let HM := fresh "HM" in pose proof HSf as (_ & _ & _ & _ & _ & _ & _ & (_ & HM & _) & _);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rr1 := fresh "Rr1" in let Rln := fresh "Rln" in let Rat := fresh "Rat" in
  apply Forall_cons_iff in HM as [Rr1 HM]; apply Forall_cons_iff in HM as [_ HM];
  apply Forall_cons_iff in HM as [Rln HM]; apply Forall_cons_iff in HM as [Rat _];
  destruct Rr1 as (_ & _ & _ & Cr1); destruct Rln as (_ & _ & _ & Cln); destruct Rat as (_ & _ & _ & Cat);
  cbn [r_chunks r_base base_val] in Cr1, Cln, Cat;
  rewrite U9 in Cr1; rewrite U27 in Cln; rewrite U33 in Cat;
  rewrite Forall_forall in Cr1, Cln, Cat;
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _)
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* pp is a block of the harness, apart from the image, so apart from the constant at 0x10408 *)
Lemma op_pp_k : forall ly S W mem md pp, AR rsegs B ly S W mem md -> In (pp, 19744) (ablocks B ly S) ->
pp + 19744 <= 0x10408 \/ 0x10410 <= pp.
Proof using LAWS.
intros ly S W mem md pp HAR Hin.
destruct (Z_le_gt_dec (pp + 19744) 0x10408) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec 0x10410 pp) as [H'|H']; [right; exact H'|]. exfalso.
apply (blk_img rsegs B LAWS ly S W mem md pp 19744 (Z.max pp 0x10408) HAR Hin).
- change (req_size 19744) with 19744. lia.
- apply op_img. lia.
Qed.

(* ======================================== (a) in.n = 0 ======================================== *)
Lemma w5_open_core_nil : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
  getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 nl -> getr regs 26 = w64 (-0x4001) ->
  getr regs 27 = w64 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  nl = 0 ->
  SRr rsegs W (cfg_at rsegs 0x81150 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82484 [10; 11; 12; 25]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008))
      (fun W2 regs2 mem2 =>
        rtm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        getr regs2 25 = w64 cur)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
  HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn Hnl0.
subst nl.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh. clear Happ.
change (2 ^ 47) with 140737488355328 in H47, Hcn.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V130 by reflexivity.
set (E := Ereg regs (op_extra0 pp atv cur)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = w64 (atv - 0x3ffd)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 cur) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (HE : E = Ereg regs (op_extra0 pp atv cur)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = atv - 0x3ffd + 18446744073709551616) by (rewrite E10; apply op_u_neg; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + atv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = cur) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr op_ov0) regs).
{ apply (w5_regs_ok E regs (op_extra0 pp atv cur)); [exact HE|]. unfold op_ov0. apply Forall_app. split.
  - exact (op_ov_ok E regs _ R pp HE E9 E27 E32 ltac:(lia) ltac:(lia) ltac:(lia) H2 H18 H22 H23 H26).
  - apply Forall_cons; [split; [apply w5_nz; vm_compute; lia|] | apply Forall_nil].
    cbn [fst snd]. rewrite H24, denot_lit_U, U_SLit. reflexivity. }
assert (HFK : facts_ok E (mkFacts op_atoms0 [op_cap] op_alias0)).
{ split; [| split].
  - cbn [f_atoms op_atoms0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U10, U27, U32, U33, U34, U35.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap_ok E atv U34 ltac:(lia)) | exact I].
  - cbn [f_alias op_alias0 alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 pp E27), (U_atom E 34 atv E34), (U_atom E 33 (pp + atv) E33) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E ss_op_nil (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81150) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_nil.
  apply (w5_entry rsegs _ _ regs (op_extra0 pp atv cur) E); [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_r1, op_r2, op_len, op_at.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0xe0 8 (SOff 34 0) atv);
          [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Va0 ].
      * apply (chunk_ok_val rsegs E _ R 0x100 8 (SOff 35 0) cur);
          [ rewrite (w5_den_off E 35 cur 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc ].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x130 8 (SLit OP_C2) OP_C2);
        [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 33 (pp + atv));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
  - unfold op_r1, op_r2, op_len, op_at. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [r_base r_lo r_hi base_val]. rewrite U9, U27, U33. repeat split; try exact I; lia. }
unfold cfg_at. change (w64 0x81150) with (Z_to_bv 64 0x81150).
aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x82484.
all: try (op_awr R sp0 pp atv U9 U27 U33 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 (w5_sr op_ov0) ([10; 11; 12; 25]%bv : list (bv 5)) U9 U27 U33 MTL.
all: op_chunks U9 U27 U33.
all: split; [op_bytes8 E Cat|].
all: split;
  [ apply (val_of_chunk_ok rsegs E _ pp 0x4000 8 (SOff 34 8) (atv + 8));
    [ apply Cln; op_inl | rewrite (w5_den_off E 34 atv 8 E34) by lia; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |].
all: transitivity (sv_denot E (SOff 35 0));
  [ exact (HRf 25%bv) | rewrite (w5_den_off E 35 cur 0 E35) by lia; rewrite Z.add_0_r; reflexivity ].
Qed.

(* ===================== (b), (c) with the input outside the constant: one lemma, z the count's case ===================== *)
Lemma op_core_app : forall (z : bool) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
  getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 nl -> getr regs 26 = w64 (-0x4001) ->
  getr regs 27 = w64 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> amem_range cur 1 -> ~ (0x10408 <= cur < 0x10410) ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R + 0xe0 <= cur < R + 0x108) -> ~ (R + 0x130 <= cur < R + 0x138) ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
  (if z then b mod 33 = 0 else b mod 33 <> 0) ->
  SRr rsegs W (cfg_at rsegs 0x81150 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if z then 0x82484 else 0x8127c)
      [10; 11; 12; 24; 25]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf0 <= a < R + 0xf8))
      (fun W2 regs2 mem2 =>
        rtm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf0) 8 (b mod 33) /\
        getr regs2 24 = w64 (nl - 1) /\ getr regs2 25 = w64 (cur + 1) /\ (z = false -> getr regs2 11 = w64 0))).
Proof using MTL LAWS.
intros z STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
  HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
  Hrom Hamem Hrk Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hz.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ. rewrite HPS in Hpp, Hfresh, Hc1.
change (2 ^ 47) with 140737488355328 in H47, Hcn.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V130 by reflexivity.
destruct (rtm_ra_cell _ _ _ Hra) as (s & Hs & Hok).
assert (Hs0e : exists s0 : bool, if s0 then s = 0 else s <> 0)
by (destruct (Z.eq_dec s 0); [exists true | exists false]; assumption).
destruct Hs0e as (s0 & Hs0).
assert (Hs8 : 0 <= s < 8).
{ destruct s0; [change (s = 0) in Hs0; lia | change (s <> 0) in Hs0; destruct (rtm_ra_slow cur s Hok Hs0); lia]. }
pose proof (Z.mod_pos_bound b 33 ltac:(lia)) as Hb33.
assert (Hdiv : 0 <= cur / 8 < 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (E := Ereg regs (op_extra1 pp atv cur b s)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = w64 (atv - 0x3ffd)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E24 : ew E 24 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 cur) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 (shadow_of_addr SHADOW_OFF cur)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 b) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = w64 s) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (HE : E = Ereg regs (op_extra1 pp atv cur b s)) by reflexivity. clearbody E.
set (sa := shadow_of_addr SHADOW_OFF cur) in *.
assert (Hsa : W5_SB <= sa < W5_SB + 17592186044416) by (subst sa; unfold shadow_of_addr, W5_SB, SHADOW_OFF; lia).
assert (HshA : sa = shadow_of_addr SHADOW_OFF cur) by reflexivity. clearbody sa.
assert (Hsh : sh_ok rsegs w5_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = atv - 0x3ffd + 18446744073709551616) by (rewrite E10; apply op_u_neg; lia).
assert (U24 : bv_unsigned (ew E 24) = nl) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + atv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = cur) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = sa) by (rewrite E36; apply unsigned_lit_small; unfold W5_SB in Hsa; lia).
assert (U37 : bv_unsigned (ew E 37) = b) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = s) by (rewrite E38; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr op_ov) regs).
{ apply (w5_regs_ok E regs (op_extra1 pp atv cur b s)); [exact HE|].
  exact (op_ov_ok E regs _ R pp HE E9 E27 E32 ltac:(lia) ltac:(lia) ltac:(lia) H2 H18 H22 H23 H26). }
assert (HFK : facts_ok E (mkFacts (op_atoms1 s0) [op_cap; op_sc s0; op_mz z] op_alias1)).
{ split; [| split].
  - unfold op_atoms1. cbn [f_atoms op_atoms0 app atoms_ok]. unfold afact_ok.
    destruct s0; [change (s = 0) in Hs0 | change (s <> 0) in Hs0]; cbn [op_s0 af_lo af_hi af_al2];
    rewrite U9, U10, U27, U32, U33, U34, U35, U24, U37, U38;
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap_ok E atv U34 ltac:(lia)) |].
    split; [exact (op_sc_ok E cur s s0 E35 E38 ltac:(lia) Hok Hs0) |].
    split; [exact (op_mz_ok E b z E37 Hb Hz) | exact I].
  - cbn [f_alias op_alias1 alias_ok]. split; [| split; [| exact I]].
    + rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 27 pp E27), (U_atom E 34 atv E34), (U_atom E 33 (pp + atv) E33) by lia.
      apply zcanon_id. unfold M64. lia.
    + apply (shadow_decl_ok E 35 32 36 cur W5_SB E35 ltac:(lia) E32).
      rewrite E36, HshA. reflexivity. }
assert (HS : st_ok rsegs E (ss_op_in s0 z) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81150) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_in.
  apply (w5_entry rsegs _ _ regs (op_extra1 pp atv cur b s) E);
    [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_r1, op_r2, op_len, op_at, op_cell, op_in, op_k.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]].
    + apply (rtm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0xe0 8 (SOff 34 0) atv);
          [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Va0 ].
      * apply (chunk_ok_val rsegs E _ R 0x100 8 (SOff 35 0) cur);
          [ rewrite (w5_den_off E 35 cur 0 E35) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc ].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x130 8 (SLit OP_C2) OP_C2);
        [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 33 (pp + atv));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
    + apply (rtm_cell_region rsegs E (w_H W) memc 36 sa s (SOff 38 0) U36 Hs);
        [ rewrite (w5_den_off E 38 s 0 E38) by lia; rewrite Z.add_0_r; reflexivity
        | unfold W5_SB in Hsa; lia | unfold W5_SB in Hsa; lia ].
    + apply (rtm_cell_region rsegs E (w_H W) memc 35 cur b (SOff 37 0) U35 (rtm_val1_aview rsegs _ _ _ _ Vb Hb));
        [ rewrite (w5_den_off E 37 b 0 E37) by lia; rewrite Z.add_0_r; reflexivity | lia | lia ].
    + apply (RtPgSteps.img_region_ok_rom E W memc 0x10408 8); [exact Hrom | lia | lia | lia | vm_compute; reflexivity].
  - assert (Fpp_sa : pp + 19744 <= sa \/ sa + 1 <= pp).
    { clear - Happ Hsa C3. unfold in_app in Happ. rewrite C3 in Happ. unfold kLowShadowBeg in Happ.
      unfold W5_SB in Hsa. lia. }
    assert (Fcur_sa : cur + 1 <= sa \/ sa + 1 <= cur).
    { clear - Hamem Hsa C3 C5. unfold amem_range in Hamem. rewrite C3, C5 in Hamem. unfold W5_SB in Hsa. lia. }
    assert (Fpp_k : pp + 19744 <= 0x10408 \/ 0x10410 <= pp) by exact (op_pp_k lyc Sc W memc mdc pp HAR Hpp).
    clear Happ Hamem Hz Hs0 Hok.
    unfold op_r1, op_r2, op_len, op_at, op_cell, op_in, op_k. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U27, U33, U35, U36.
    unfold W5_SB in Hsa. repeat split; try exact I; lia. }
destruct s0, z.
all: unfold cfg_at; change (w64 0x81150) with (Z_to_bv 64 0x81150).
all: [> aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x82484 | aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x8127c
 | aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x82484 | aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x8127c ].
all: try (op_awr R sp0 pp atv U9 U27 U33 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 (w5_sr op_ov) ([10; 11; 12; 24; 25]%bv : list (bv 5)) U9 U27 U33 MTL.
all: op_chunks U9 U27 U33.
all: split; [op_bytes8 E Cat|].
all: split;
  [ apply (val_of_chunk_ok rsegs E _ pp 0x4000 8 (SOff 34 8) (atv + 8));
    [ apply Cln; op_inl | rewrite (w5_den_off E 34 atv 8 E34) by lia; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |].
all: split;
  [ apply (val_of_chunk_ok rsegs E _ R 0xf0 8 op_M (b mod 33));
    [ apply Cr1; op_inl | rewrite denot_lit_U, (op_U_M E b E37 Hb); reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |].
all: split;
  [ transitivity (sv_denot E (SOff 24 (-1)));
    [ exact (HRf 24%bv) | rewrite (w5_den_off E 24 nl (-1) E24) by lia; reflexivity ] |].
all: split;
  [ transitivity (sv_denot E (SOff 35 1));
    [ exact (HRf 25%bv) | rewrite (w5_den_off E 35 cur 1 E35) by lia; reflexivity ] |].
all: intros Hzf; first [ discriminate Hzf | transitivity (sv_denot E (SLit 0)); [exact (HRf 11%bv) | reflexivity] ].
Qed.

(* ===================== (c) with the input inside the constant: cur = 0x10408 + j, eight literal walks ===================== *)
Lemma op_core_rom : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
  getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 nl -> getr regs 26 = w64 (-0x4001) ->
  getr regs 27 = w64 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> 0x10408 <= cur < 0x10410 ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
  SRr rsegs W (cfg_at rsegs 0x81150 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x8127c [10; 11; 12; 24; 25]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf0 <= a < R + 0xf8))
      (fun W2 regs2 mem2 =>
        rtm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf0) 8 (b mod 33) /\
        getr regs2 24 = w64 (nl - 1) /\ getr regs2 25 = w64 (cur + 1) /\ getr regs2 11 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
  HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
  Hrom Hkin b Hnl0 Vb Hb Hra.
pose proof w5_wx as Hwx. pose proof w5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ. rewrite HPS in Hpp, Hfresh.
change (2 ^ 47) with 140737488355328 in H47, Hcn.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V130 by reflexivity.
pose proof (op_rom_byte W memc cur b Hrom Vb Hb Hkin) as Hbv.
destruct (rtm_ra_cell _ _ _ Hra) as (s & Hs & Hok).
assert (Hs0e : exists s0 : bool, if s0 then s = 0 else s <> 0)
by (destruct (Z.eq_dec s 0); [exists true | exists false]; assumption).
destruct Hs0e as (s0 & Hs0).
assert (Hs8 : 0 <= s < 8).
{ destruct s0; [change (s = 0) in Hs0; lia | change (s <> 0) in Hs0; destruct (rtm_ra_slow cur s Hok Hs0); lia]. }
pose proof (Z.mod_pos_bound b 33 ltac:(lia)) as Hb33.
assert (Hc8 : cur / 8 = 8321) by (symmetry; apply (Z.div_unique cur 8 8321 (cur - 66568)); [left; lia | lia]).
assert (HsaB : shadow_of_addr SHADOW_OFF cur = W5_SB + 0x2081) by (unfold shadow_of_addr; rewrite Hc8; reflexivity).
rewrite HsaB in Hs.
set (E := Ereg regs (op_extra1 pp atv cur b s)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = w64 (atv - 0x3ffd)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E24 : ew E 24 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = w64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 W5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 cur) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E38 : ew E 38 = w64 s) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (HE : E = Ereg regs (op_extra1 pp atv cur b s)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs w5_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 27 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (w5_shent_blk B LAWS lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = atv - 0x3ffd + 18446744073709551616) by (rewrite E10; apply op_u_neg; lia).
assert (U24 : bv_unsigned (ew E 24) = nl) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + atv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = cur) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = s) by (rewrite E38; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (w5_sr op_ov) regs).
{ apply (w5_regs_ok E regs (op_extra1 pp atv cur b s)); [exact HE|].
  exact (op_ov_ok E regs _ R pp HE E9 E27 E32 ltac:(lia) ltac:(lia) ltac:(lia) H2 H18 H22 H23 H26). }
assert (HFK : facts_ok E (mkFacts (op_atomsB s0) [op_cap; op_scB cur s0] op_alias0)).
{ split; [| split].
  - unfold op_atomsB. cbn [f_atoms op_atoms0 app atoms_ok]. unfold afact_ok.
    destruct s0; [change (s = 0) in Hs0 | change (s <> 0) in Hs0]; cbn [op_s0 af_lo af_hi af_al2];
    rewrite U9, U10, U27, U32, U33, U34, U35, U24, U38;
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap_ok E atv U34 ltac:(lia)) |].
    split; [exact (op_scB_ok E cur s s0 E38 Hok Hs0) | exact I].
  - cbn [f_alias op_alias0 alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 pp E27), (U_atom E 34 atv E34), (U_atom E 33 (pp + atv) E33) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E (ss_op_rom cur s0) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81150) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_rom.
  apply (w5_entry rsegs _ _ regs (op_extra1 pp atv cur b s) E);
    [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_r1, op_r2, op_len, op_at, op_cellB, op_k.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
    + apply (rtm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0xe0 8 (SOff 34 0) atv);
          [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact Va0 ].
      * apply (chunk_ok_val rsegs E _ R 0x100 8 (SLit cur) cur);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vc ].
    + apply (rtm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x130 8 (SLit OP_C2) OP_C2);
        [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 27 pp);
        [ exact U27 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (w5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (rtm_rw_region rsegs E (w_H W) memc 33 (pp + atv));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
    + apply (rtm_ro_region rsegs E (w_H W) memc 32 W5_SB 0x2081 0x2082); [exact U32 | unfold W5_SB; lia | unfold W5_SB; lia |].
      apply Forall_cons; [|apply Forall_nil].
      destruct (rtm_aview_val1 rsegs _ _ _ _ Hs) as [Vs _].
      apply (chunk_ok_val rsegs E _ W5_SB 0x2081 1 (SOff 38 0) s);
        [ rewrite (w5_den_off E 38 s 0 E38) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia | exact Vs ].
    + apply (RtPgSteps.img_region_ok_rom E W memc 0x10408 8); [exact Hrom | lia | lia | lia | vm_compute; reflexivity].
  - assert (Fpp_sa : pp + 19744 <= W5_SB + 0x2081 \/ W5_SB + 0x2082 <= pp).
    { clear - Happ C3. unfold in_app in Happ. rewrite C3 in Happ. unfold kLowShadowBeg in Happ. unfold W5_SB. lia. }
    assert (Fpp_k : pp + 19744 <= 0x10408 \/ 0x10410 <= pp) by exact (op_pp_k lyc Sc W memc mdc pp HAR Hpp).
    clear Happ Hs0 Hok.
    unfold op_r1, op_r2, op_len, op_at, op_cellB, op_k. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U27, U32, U33.
    unfold W5_SB in *. repeat split; try exact I; lia. }
assert (Hcj : cur = 66568 \/ cur = 66569 \/ cur = 66570 \/ cur = 66571 \/ cur = 66572 \/ cur = 66573 \/
              cur = 66574 \/ cur = 66575) by lia.
destruct Hcj as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; destruct s0.
all: unfold cfg_at; change (w64 0x81150) with (Z_to_bv 64 0x81150).
all: aj_run_to_tok w5_tbl_ok HS HJ Hsh w5_Bspan 0x8127c.
all: try (op_awr R sp0 pp atv U9 U27 U33 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 (w5_sr op_ov) ([10; 11; 12; 24; 25]%bv : list (bv 5)) U9 U27 U33 MTL.
all: op_chunks U9 U27 U33.
all: split; [op_bytes8 E Cat|].
all: split;
  [ apply (val_of_chunk_ok rsegs E _ pp 0x4000 8 (SOff 34 8) (atv + 8));
    [ apply Cln; op_inl | rewrite (w5_den_off E 34 atv 8 E34) by lia; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |].
all: split;
  [ lazymatch type of Cr1 with context [YP09.mkChunk 0xf0 (CVal 8 ?e)] =>
      apply (val_of_chunk_ok rsegs E _ R 0xf0 8 e (b mod 33));
      [ apply Cr1; op_inl | rewrite Hbv; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia ] end |].
all: split;
  [ transitivity (sv_denot E (SOff 24 (-1)));
    [ exact (HRf 24%bv) | rewrite (w5_den_off E 24 nl (-1) E24) by lia; reflexivity ] |].
all: split; [ etransitivity; [exact (HRf 25%bv) | reflexivity] |].
all: etransitivity; [exact (HRf 11%bv) | reflexivity].
Qed.

(* ======================================== (b) count = 0 ======================================== *)
Lemma w5_open_core_zero : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
  getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 nl -> getr regs 26 = w64 (-0x4001) ->
  getr regs 27 = w64 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> amem_range cur 1 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R + 0xe0 <= cur < R + 0x108) -> ~ (R + 0x130 <= cur < R + 0x138) ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 -> b mod 33 = 0 ->
  SRr rsegs W (cfg_at rsegs 0x81150 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82484 [10; 11; 12; 24; 25]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf0 <= a < R + 0xf8))
      (fun W2 regs2 mem2 =>
        rtm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf0) 8 0 /\
        getr regs2 24 = w64 (nl - 1) /\ getr regs2 25 = w64 (cur + 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
  HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
  Hrom Hamem Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm.
destruct (Z_lt_le_dec cur 0x10408) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec cur 0x10410) as [Hhi|Hhi]].
2: { exfalso. apply (op_kbyte_mod (cur - 0x10408) ltac:(lia)).
     rewrite <- (op_rom_byte W memc cur b Hrom Vb Hb ltac:(lia)). exact Hm. }
all: eapply SRr_mono;
  [ exact (op_core_app true STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
      HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
      Hrom Hamem ltac:(lia) Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm) |].
all: intros W' c' _ (ly2 & S2 & regs2 & mem2 & md2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 &
  (Q9 & Q10 & Q11 & Q12 & Q13 & _)).
all: exists ly2, S2, regs2, mem2, md2; rewrite Hm in Q11.
all: exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
       (conj Q9 (conj Q10 (conj Q11 (conj Q12 Q13)))))))))))).
Qed.

(* ======================================== (c) count <> 0 ======================================== *)
Lemma w5_open_core_pos : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 10 = w64 (atv - 0x3ffd) ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 22 = w64 (shadow_addr (pp + 0x4000)) ->
  getr regs 23 = w64 (pp + 0x4000) -> getr regs 24 = w64 nl -> getr regs 26 = w64 (-0x4001) ->
  getr regs 27 = w64 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 16 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x1e0 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 47 ->
  rom_view rsegs W memc -> amem_range cur 1 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R + 0xe0 <= cur < R + 0x108) -> ~ (R + 0x130 <= cur < R + 0x138) ->
  forall b, 0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 -> b mod 33 <> 0 ->
  SRr rsegs W (cfg_at rsegs 0x81150 regs memc mdc)
    (w5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x8127c [10; 11; 12; 24; 25]%bv
      (fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0xf0 <= a < R + 0xf8))
      (fun W2 regs2 mem2 =>
        rtm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf0) 8 (b mod 33) /\
        getr regs2 24 = w64 (nl - 1) /\ getr regs2 25 = w64 (cur + 1) /\ getr regs2 11 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
  HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
  Hrom Hamem Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm.
destruct (Z_lt_le_dec cur 0x10408) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec cur 0x10410) as [Hhi|Hhi]].
2: { exact (op_core_rom STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
       HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
       Hrom ltac:(lia) b Hnl0 Vb Hb Hra). }
all: eapply SRr_mono;
  [ exact (op_core_app false STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl
      HJ Hpp Hfresh H2 H9 H10 H18 H22 H23 H24 H26 H27 Va0 Vc V130 Vlen HR16 HRlo HRhi Hat Hal Hnl Hcur Hcn
      Hrom Hamem ltac:(lia) Hc1 Hc2 Hc3 b Hnl0 Vb Hb Hra Hm) |].
all: intros W' c' _ (ly2 & S2 & regs2 & mem2 & md2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 &
  (Q9 & Q10 & Q11 & Q12 & Q13 & Q14)).
all: exists ly2, S2, regs2, mem2, md2.
all: exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
       (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (Q14 eq_refl)))))))))))))).
Qed.
End c.

Print Assumptions w5_open_core_nil.
Print Assumptions w5_open_core_zero.
Print Assumptions w5_open_core_pos.
