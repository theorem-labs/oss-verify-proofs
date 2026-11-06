(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE STEP LAYER
   of segment L3 of LLVMFuzzerTestOneInput (entry 0x816cc), listing slots 94 .. 110 (+0x178 .. +0x1b8), for the
   segment proof lib/AU/Prog/Ent102L3B.v. No function is proved here and no cut is read: every lemma is stated over a
   register file, a memory and a model only, so this file does not depend on lib/AU/Ent102CutsB.v.
   THE B' TWIN of lib/A/Prog/Ent102L3ASteps.v (blob a2cae79c6316: Ent102L3ASteps.v (sha256 f6823236f0fe; internal record)), ported by
   port/a2b.py (sha256 f5113cbc90e503da) and then by hand: L := B_prog_listing, PL := PL_102_B. The B' slots 94 .. 111
   are A''s word for word but slot 100 (+0x190): A' 0xe3ccc583 `lbu a1,-0x1c4(s9)`, B' 0x590cc583 `lbu a1,0x590(s9)`
   (the same rd / rs1 / width, only the displacement differs), so l3_s_190 takes the B' displacement; every other
   lemma is A''s text.
   LISTING: lib/B/Listing_prog.v (blob 8bcc2c9e7809; a Theorem Labs lane's whole-program listing, slot k = byte offset 4k from
   the entry), through the PAListing PL_102_B of lib/B/Ent102PLB.v (blob e0348e1212c9); the image half stays generic
   ({PA : PAImg B_prog_listing}); lib/B/PAImg_prog.v is not loaded and nothing computes pa_val / pa_sigma (only the
   listing's own slots are computed).
   THE KIT TEXTS: none read here (lib/A/PRH_FnCheck.v only for the name PJ_ALLOC_BOUND; the kit's texts are generic over
   the listing class, so B' takes the same file).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L3 on image B' (reuse search: origin/main,
   origin/ossv/recipes, origin/ossv/candidates, origin/release/*, the internal lemma index and live heads, via
   `proof-index seg_L3_B LLVMFuzzerTestOneInput 0x81844 0x81884 0x81888`, index v5 built 2026-10-29T16:10:25Z,
   a Theorem Labs lane's internal file rule24-LL3B.txt: seg_L3_B 0 hits; LLVMFuzzerTestOneInput's 7 released
   fuzz_preset hits are the plain / ubsan contracts LLVMFuzzerTestOneInput_c.v, not an ASan #102 walk; the A' twin
   seg_L3_A is a Theorem Labs lane's, this file ports it). This file: the step lemmas of that segment only.
   TAKEN BY PATH (image-free; each restated under an l3_ name): l3_pc4 / l3_step_addi / l3_step_call and the tactics
   l3_regne / l3_fdc from lib/AU/Prog/Ent102L6BfLem.v l6f_pc4 / l6f_step_addi / l6f_step_call / l6f_regne / l6f_fdc;
   l3_step_sub / l3_step_lbu / l3_step_br_tk / l3_step_br_ft are their twins over YK14.v step_sub_at and YK11.v
   step_lbu / step_branch_tk_gen / step_branch_ft_gen.

   WHAT THE CODE DOES (lib/B/Listing_prog.v slots 94 .. 110; the lane's note, the internal file llvm-plan.md app. A):
     +0x178 mv s8,a0                 rc
     +0x17c jal fuzz_alloc_peak      (PCall, return site +0x180)
     +0x180 sub a0,a0,s6             peak - live
     +0x184 mv a1,s3                 size
     +0x188 jal check_bounded_alloc  (PCall, return site +0x18c)
     +0x18c jal fuzz_alloc_count     (PCall, return site +0x190)
     +0x190 lbu a1,0x590(s9)         g_own_ran_out (s9 = the PHi 4 value of slot 73)
     +0x194 bnez a1,+0x1bc           -> FREE
     +0x198 mv s9,a0                 the count after the reading
     +0x19c jal fuzz_alloc_ran_out   (PCall, return site +0x1a0)
     +0x1a0 bnez a0,+0x1bc           -> FREE
     +0x1a4 .. +0x1b0 mv a0,s4; mv a1,s3; mv a2,s8; mv a3,s5
     +0x1b4 jal check_as_written     (PCall, return site +0x1b8)
     +0x1b8 beqz a0,+0x2c8           (segment L4's first instruction; here for the lane that follows)
   NUMERALS: 0x178 .. 0x2c8 are LENGTHs (slot offsets from the entry, the cut file's EC_* differences, the same on both
   images); 0x28 / 0x1c / 0x110 are the branches' immediates (the listing's words, the same on both images); 0x590 is
   the load's displacement (B' slot 100); register indices are REG; 2 ^ 40 / 2 ^ 64 / 256 are the engine's code-span,
   word and byte ranges; 224 n + 16384 and PJ_ALLOC_BOUND are parse_noting's peak bound and the harness's request
   bound. No ADDRESS and no instruction word: every word is read from the listing. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Tactics: register disequality, the listing slot at an offset and its decoding (the word is read from the
      listing, the instruction is checked by vm_refl_bv), a call slot to a named callee. *)
Ltac l3_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Ltac l3_fd k ins Hpl Hd :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_102_B) k) in
  lazymatch r with
  | Some (PW ?w) =>
    assert (Hpl : plookup (@pl_tpi _ PL_102_B) k = Some (PW w)) by (vm_compute; reflexivity);
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (ins, 4%Z)) by vm_refl_bv
  | _ => fail "l3_fd: no plain word at offset" k
  end.
Ltac l3_fdc k s Hpl :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_102_B) k) in
  lazymatch r with
  | Some (PCall s ?rd) =>
    assert (Hpl : plookup (@pl_tpi _ PL_102_B) k = Some (PCall s rd)) by (vm_compute; reflexivity)
  | _ => fail "l3_fdc: no call slot to" s "at offset" k
  end.

(* ---------------------------------------------------------------------- *)
(* 2. Pure facts. *)
(* a register-plus-immediate address over a literal register value *)
Lemma l3_vaddi_lit : forall h i, v_addi (Z_to_bv 64 h) i = Z_to_bv 64 (h + i).
Proof.
intros h i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(* `sub a0,a0,s6` with s6 = 0 leaves a0 *)
Lemma l3_vsub0 : forall x : word, v_sub x (Z_to_bv 64 0) = x.
Proof.
intros x. unfold v_sub. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.sub_0_r.
apply Z_to_bv_bv_unsigned.
Qed.

(* the two outcomes of a `bnez` / `beqz` on a word value *)
Lemma l3_ceq0 : c_eq (Z_to_bv 64 0) (Z_to_bv 64 0) = true.
Proof. reflexivity. Qed.
Lemma l3_ceq_ne : forall o, 0 < o < 2 ^ 64 -> c_eq (Z_to_bv 64 o) (Z_to_bv 64 0) = false.
Proof.
intros o Ho. unfold c_eq, bv_eqb. rewrite unsigned_lit_small by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia.
Qed.

(* a byte value read back *)
Lemma l3_u8 : forall o, 0 <= o < 256 -> bv_unsigned (Z_to_bv 8 o) = o.
Proof.
intros o Ho. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Ho.
Qed.

(* parse_noting's peak bound is within the harness's request bound (PJ_ALLOC_BOUND n = 256 n + 20480) *)
Lemma l3_peak_bound : forall n, 0 <= n -> 224 * n + 16384 <= PRH_FnCheck.PJ_ALLOC_BOUND n.
Proof. intros n Hn. unfold PRH_FnCheck.PJ_ALLOC_BOUND. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The generic steps at a generic image: a plain slot (addi, sub, lbu, a conditional branch) and a `jal ra, f`
      call slot. *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PA : @PAImg rc B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
(* THE WORLD RELATION of the lane's SRrG (YA0nH; the free move: lane L3 crosses check_as_written, after
   check_no_overread's frees, so it runs at wle' segs RZ_cf, Ent102CutsB.v ec_laneR WLE'). Implicit: each step lemma
   reads it off its goal. A step keeps the world, so every proof is the plain one over YSRrG.SRrG_step. *)
Context {Rel : world SEGS -> world SEGS -> Prop}.

(* a one-byte read through a val_mem cell of width 1 *)
Lemma l3_rdn1 : forall (m : word -> option byte) a o, val_mem SEGS m a 1 o -> 0 <= o < 256 ->
  rdn SEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 o].
Proof.
intros m a o Hv Ho.
apply (mbytes_at_rdn SEGS m a [Z_to_bv 8 o]).
intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
specialize (Hv 0%nat ltac:(lia)). cbn [nth_error]. rewrite Hv. f_equal.
cbv beta delta [YO0f.le_byte YG0f.le_byte].
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma l3_pc4 : forall k, 0 <= k < 2 ^ 40 -> v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof.
intros k Hk. pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma l3_btgt : forall k i, 0 <= k < 2 ^ 40 -> 0 <= k + i < 2 ^ 40 ->
  btgt (Z_to_bv 64 (BASE + k)) i = Z_to_bv 64 (BASE + (k + i)).
Proof.
intros k i Hk Hki. pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
unfold btgt, v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma l3_step_addi : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs : bv 5) (imm : bv 12) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm v Hk Hpl Hd Hrd Hv HK.
pose proof (pa_fetch_pw (PL := PL_102_B) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_addi_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm v Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l3_pc4 k Hk). apply HK.
Qed.

Lemma l3_step_sub : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs1 rs2 : bv 5) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx (regupd regs rd v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 v Hk Hpl Hd Hrd Hv HK.
pose proof (pa_fetch_pw (PL := PL_102_B) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_sub_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 v Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l3_pc4 k Hk). apply HK.
Qed.

(* lbu: the byte at rs + imm in the restricted memory (the reader view of the world) *)
Lemma l3_step_lbu : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs : bv 5) (imm : bv 12) (b : byte),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx (regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
     (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm b Hk Hpl Hd Hrd Hr HK.
pose proof (pa_fetch_pw (PL := PL_102_B) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_lbu (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm b Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hr).
  lazymatch goal with |- context [bv_eqb rd ?z] => replace (bv_eqb rd z) with false by (symmetry; exact Hrd) end.
  reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l3_pc4 k Hk). apply HK.
Qed.

Lemma l3_step_br_tk : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k k' w : Z) c (rs1 rs2 : bv 5) (imm : bv 13),
  0 <= k < 2 ^ 40 -> 0 <= k' < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  k + bv_signed imm = k' ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k')) mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k k' w c rs1 rs2 imm Hk Hk' Hpl Hd Ht Hc HK.
pose proof (pa_fetch_pw (PL := PL_102_B) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_branch_tk_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
    (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l3_btgt k (bv_signed imm) Hk ltac:(lia)), Ht. apply HK.
Qed.

Lemma l3_step_br_ft : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) c (rs1 rs2 : bv 5) (imm : bv 13),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w c rs1 rs2 imm Hk Hpl Hd Hc HK.
pose proof (pa_fetch_pw (PL := PL_102_B) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_branch_ft_gen (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem)
    (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l3_pc4 k Hk). apply HK.
Qed.

(* `jal ra, f` over a PCall slot: the target is read off the certificate (YP0d.v cert_slot) *)
Lemma l3_step_call : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) (s : asym) (rd rd' : bv 5),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PCall s rd) -> rd = rd' ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx (regupd regs rd' (Z_to_bv 64 (BASE + (k + 4))))
     (Z_to_bv 64 (SIGMA s)) mem (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k s rd rd' Hk Hpl Erd HK. subst rd'.
pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- (@pl_tpi_eq _ PL_102_B) in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with decode_any _ = Some (Jal ?r ?im, _) => rename r into rdj; rename im into immj end.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd Hnz].
apply reg_eqb_eq in Hrd. subst rdj. apply Z.eqb_eq in Ht.
assert (Hrd0 : bv_eqb rd (0%bv : bv 5) = false).
{ destruct (bv_eqb rd (Z_to_bv 5 0)) eqn:E3; [discriminate Hnz|]. rewrite <- E3. unfold bv_eqb. reflexivity. }
pose proof (pa_fetch_ok (PI := PA) _ _ Hl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_jal_link (fx := fx) SEGS regs (Z_to_bv 64 (VAL A_TEXT + k)) (mrestrict (w_H W) mem)
    (YK11.seg_rom SEGS) (Z_to_bv 32 wz) rd immj Hf (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  lazymatch goal with |- context [bv_eqb rd ?z] => replace (bv_eqb rd z) with false by (symmetry; exact Hrd0) end.
  reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l3_pc4 k Hk).
  replace (btgt (Z_to_bv 64 (VAL A_TEXT + k)) (bv_signed immj)) with (Z_to_bv 64 (SIGMA s)).
  + apply HK.
  + unfold btgt, v_addi. rewrite unsigned_lit_small by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    rewrite <- Ht. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE LANE'S INSTRUCTIONS, one lemma each, at the listing offsets +0x178 .. +0x1b8. *)
#[local] Notation CF regs pc mem md := (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md).
#[local] Notation WV md X := (with_vm_backing (m_vm_lazy md) X md).

(* +0x178 `mv s8,a0` *)
Lemma l3_s_178 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 24 (getr regs 10)) (BASE + 0x17c) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x178) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x178 (OpImm ALU_ADD 24 10 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x178 _ 24 10 (Z_to_bv 12 0) (getr regs 10) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x17c `jal fuzz_alloc_peak` (return site +0x180) *)
Lemma l3_s_17c : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 1 (Z_to_bv 64 (BASE + 0x180))) (SIGMA AS_fuzz_alloc_peak) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x17c) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fdc 0x17c AS_fuzz_alloc_peak Hpl.
exact (l3_step_call W regs mem md Q 0x17c AS_fuzz_alloc_peak _ 1 ltac:(lia) Hpl ltac:(apply bv_eq; reflexivity) HK).
Qed.

(* +0x180 `sub a0,a0,s6` *)
Lemma l3_s_180 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 10 (v_sub (getr regs 10) (getr regs 22))) (BASE + 0x184) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x180) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x180 (Op ALU_SUB 10 10 22) Hpl Hd.
exact (l3_step_sub W regs mem md Q 0x180 _ 10 10 22 _ ltac:(lia) Hpl Hd eq_refl eq_refl HK).
Qed.

(* +0x184 `mv a1,s3` *)
Lemma l3_s_184 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 11 (getr regs 19)) (BASE + 0x188) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x184) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x184 (OpImm ALU_ADD 11 19 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x184 _ 11 19 (Z_to_bv 12 0) (getr regs 19) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x188 `jal check_bounded_alloc` (return site +0x18c) *)
Lemma l3_s_188 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W
     (CF (regupd regs 1 (Z_to_bv 64 (BASE + 0x18c))) (SIGMA AS_check_bounded_alloc) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x188) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fdc 0x188 AS_check_bounded_alloc Hpl.
exact (l3_step_call W regs mem md Q 0x188 AS_check_bounded_alloc _ 1 ltac:(lia) Hpl
  ltac:(apply bv_eq; reflexivity) HK).
Qed.

(* +0x18c `jal fuzz_alloc_count` (return site +0x190) *)
Lemma l3_s_18c : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W
     (CF (regupd regs 1 (Z_to_bv 64 (BASE + 0x190))) (SIGMA AS_fuzz_alloc_count) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x18c) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fdc 0x18c AS_fuzz_alloc_count Hpl.
exact (l3_step_call W regs mem md Q 0x18c AS_fuzz_alloc_count _ 1 ltac:(lia) Hpl ltac:(apply bv_eq; reflexivity) HK).
Qed.

(* +0x190 `lbu a1,0x590(s9)` (B' slot 100, 0x590cc583; A' had -0x1c4): s9 = h, and the one-byte cell at h + 0x590
   holds o (g_own_ran_out: ei_own gives pa_val (A_HI 4) + 0x590 = pi_g_own_ran_out at width 1, and prh_own the cell's
   val_mem) *)
Lemma l3_s_190 : forall (W : world SEGS) regs mem md Q h o,
  getr regs 25 = Z_to_bv 64 h ->
  val_mem SEGS (mrestrict (w_H W) mem) (h + 0x590) 1 o -> 0 <= o < 256 ->
  (forall X, SRrG SEGS Rel W (CF (regupd regs 11 (Z_to_bv 64 o)) (BASE + 0x194) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x190) mem md) Q.
Proof.
intros W regs mem md Q h o H25 Hv Ho HK.
l3_fd 0x190 (Load SZ1 false 11 25 (Z_to_bv 12 0x590)) Hpl Hd.
assert (Hr : rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs 25) (bv_signed (Z_to_bv 12 0x590))) 1%nat =
  Some [Z_to_bv 8 o]).
{ rewrite H25. change (bv_signed (Z_to_bv 12 0x590)) with 0x590. rewrite l3_vaddi_lit.
  exact (l3_rdn1 _ _ _ Hv Ho). }
refine (l3_step_lbu W regs mem md Q 0x190 _ 11 25 (Z_to_bv 12 0x590) (Z_to_bv 8 o) ltac:(lia) Hpl Hd eq_refl Hr _).
intros X. rewrite (l3_u8 o Ho). exact (HK X).
Qed.

(* +0x194 `bnez a1,+0x1bc`, taken (FREE) and not taken *)
Lemma l3_s_194_tk : forall (W : world SEGS) regs mem md Q,
  c_eq (getr regs 11) (Z_to_bv 64 0) = false ->
  (forall X, SRrG SEGS Rel W (CF regs (BASE + 0x1bc) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x194) mem md) Q.
Proof.
intros W regs mem md Q Hc HK.
l3_fd 0x194 (Branch BC_NE 11 0 (Z_to_bv 13 0x28)) Hpl Hd.
refine (l3_step_br_tk W regs mem md Q 0x194 0x1bc _ BC_NE 11 0 (Z_to_bv 13 0x28) ltac:(lia) ltac:(lia) Hpl Hd
  ltac:(vm_compute; reflexivity) _ HK).
change (getr regs 0) with (Z_to_bv 64 0). cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma l3_s_194_ft : forall (W : world SEGS) regs mem md Q,
  c_eq (getr regs 11) (Z_to_bv 64 0) = true ->
  (forall X, SRrG SEGS Rel W (CF regs (BASE + 0x198) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x194) mem md) Q.
Proof.
intros W regs mem md Q Hc HK.
l3_fd 0x194 (Branch BC_NE 11 0 (Z_to_bv 13 0x28)) Hpl Hd.
refine (l3_step_br_ft W regs mem md Q 0x194 _ BC_NE 11 0 (Z_to_bv 13 0x28) ltac:(lia) Hpl Hd _ HK).
change (getr regs 0) with (Z_to_bv 64 0). cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

(* +0x198 `mv s9,a0` *)
Lemma l3_s_198 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 25 (getr regs 10)) (BASE + 0x19c) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x198) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x198 (OpImm ALU_ADD 25 10 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x198 _ 25 10 (Z_to_bv 12 0) (getr regs 10) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x19c `jal fuzz_alloc_ran_out` (return site +0x1a0) *)
Lemma l3_s_19c : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W
     (CF (regupd regs 1 (Z_to_bv 64 (BASE + 0x1a0))) (SIGMA AS_fuzz_alloc_ran_out) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x19c) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fdc 0x19c AS_fuzz_alloc_ran_out Hpl.
exact (l3_step_call W regs mem md Q 0x19c AS_fuzz_alloc_ran_out _ 1 ltac:(lia) Hpl ltac:(apply bv_eq; reflexivity) HK).
Qed.

(* +0x1a0 `bnez a0,+0x1bc`, taken (FREE) and not taken *)
Lemma l3_s_1a0_tk : forall (W : world SEGS) regs mem md Q,
  c_eq (getr regs 10) (Z_to_bv 64 0) = false ->
  (forall X, SRrG SEGS Rel W (CF regs (BASE + 0x1bc) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1a0) mem md) Q.
Proof.
intros W regs mem md Q Hc HK.
l3_fd 0x1a0 (Branch BC_NE 10 0 (Z_to_bv 13 0x1c)) Hpl Hd.
refine (l3_step_br_tk W regs mem md Q 0x1a0 0x1bc _ BC_NE 10 0 (Z_to_bv 13 0x1c) ltac:(lia) ltac:(lia) Hpl Hd
  ltac:(vm_compute; reflexivity) _ HK).
change (getr regs 0) with (Z_to_bv 64 0). cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma l3_s_1a0_ft : forall (W : world SEGS) regs mem md Q,
  c_eq (getr regs 10) (Z_to_bv 64 0) = true ->
  (forall X, SRrG SEGS Rel W (CF regs (BASE + 0x1a4) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1a0) mem md) Q.
Proof.
intros W regs mem md Q Hc HK.
l3_fd 0x1a0 (Branch BC_NE 10 0 (Z_to_bv 13 0x1c)) Hpl Hd.
refine (l3_step_br_ft W regs mem md Q 0x1a0 _ BC_NE 10 0 (Z_to_bv 13 0x1c) ltac:(lia) Hpl Hd _ HK).
change (getr regs 0) with (Z_to_bv 64 0). cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

(* +0x1a4 `mv a0,s4` *)
Lemma l3_s_1a4 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 10 (getr regs 20)) (BASE + 0x1a8) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1a4) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x1a4 (OpImm ALU_ADD 10 20 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x1a4 _ 10 20 (Z_to_bv 12 0) (getr regs 20) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x1a8 `mv a1,s3` *)
Lemma l3_s_1a8 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 11 (getr regs 19)) (BASE + 0x1ac) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1a8) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x1a8 (OpImm ALU_ADD 11 19 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x1a8 _ 11 19 (Z_to_bv 12 0) (getr regs 19) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x1ac `mv a2,s8` *)
Lemma l3_s_1ac : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 12 (getr regs 24)) (BASE + 0x1b0) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1ac) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x1ac (OpImm ALU_ADD 12 24 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x1ac _ 12 24 (Z_to_bv 12 0) (getr regs 24) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x1b0 `mv a3,s5` *)
Lemma l3_s_1b0 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W (CF (regupd regs 13 (getr regs 21)) (BASE + 0x1b4) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1b0) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fd 0x1b0 (OpImm ALU_ADD 13 21 (Z_to_bv 12 0)) Hpl Hd.
refine (l3_step_addi W regs mem md Q 0x1b0 _ 13 21 (Z_to_bv 12 0) (getr regs 21) ltac:(lia) Hpl Hd eq_refl _ HK).
change (bv_signed (Z_to_bv 12 0)) with 0. apply YK11.v_addi_0.
Qed.

(* +0x1b4 `jal check_as_written` (return site +0x1b8) *)
Lemma l3_s_1b4 : forall (W : world SEGS) regs mem md Q,
  (forall X, SRrG SEGS Rel W
     (CF (regupd regs 1 (Z_to_bv 64 (BASE + 0x1b8))) (SIGMA AS_check_as_written) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1b4) mem md) Q.
Proof.
intros W regs mem md Q HK.
l3_fdc 0x1b4 AS_check_as_written Hpl.
exact (l3_step_call W regs mem md Q 0x1b4 AS_check_as_written _ 1 ltac:(lia) Hpl ltac:(apply bv_eq; reflexivity) HK).
Qed.

(* +0x1b8 `beqz a0,+0x2c8`, taken (r = 0) and not taken (FREE) *)
Lemma l3_s_1b8_tk : forall (W : world SEGS) regs mem md Q,
  c_eq (getr regs 10) (Z_to_bv 64 0) = true ->
  (forall X, SRrG SEGS Rel W (CF regs (BASE + 0x2c8) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1b8) mem md) Q.
Proof.
intros W regs mem md Q Hc HK.
l3_fd 0x1b8 (Branch BC_EQ 10 0 (Z_to_bv 13 0x110)) Hpl Hd.
refine (l3_step_br_tk W regs mem md Q 0x1b8 0x2c8 _ BC_EQ 10 0 (Z_to_bv 13 0x110) ltac:(lia) ltac:(lia) Hpl Hd
  ltac:(vm_compute; reflexivity) _ HK).
change (getr regs 0) with (Z_to_bv 64 0). exact Hc.
Qed.
Lemma l3_s_1b8_ft : forall (W : world SEGS) regs mem md Q,
  c_eq (getr regs 10) (Z_to_bv 64 0) = false ->
  (forall X, SRrG SEGS Rel W (CF regs (BASE + 0x1bc) mem (WV md X)) Q) ->
  SRrG SEGS Rel W (CF regs (BASE + 0x1b8) mem md) Q.
Proof.
intros W regs mem md Q Hc HK.
l3_fd 0x1b8 (Branch BC_EQ 10 0 (Z_to_bv 13 0x110)) Hpl Hd.
refine (l3_step_br_ft W regs mem md Q 0x1b8 _ BC_EQ 10 0 (Z_to_bv 13 0x110) ltac:(lia) Hpl Hd _ HK).
change (getr regs 0) with (Z_to_bv 64 0). exact Hc.
Qed.

End S.
