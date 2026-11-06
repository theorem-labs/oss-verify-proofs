(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/CJ/RL/GX/G_sn_write.v, with its module paths, module names and addresses changed; 60 of its 119 lines of code are new or changed and 391 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import G_memcpy G_fwritex.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import G_sn_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.StoreFast.
Import ListNotations.
Open Scope bv_scope.

Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.LiaClosure.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Open Scope Z_scope.

Ltac setreg2 v :=
  lazymatch goal with |- evt ?sg ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F' ?pc ?fc' ?rv ?mm ?ro) =>
    replace (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      with (mkR x1 v x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      by (f_equal; first [ reflexivity | rewrite <- (Z_to_bv_bv_unsigned v) at 2; f_equal; lia ])
  end.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_fwritex : CodeAtT img_segs (sym 0x17d50) (PROGAT_CODE_fwritex IMG)}.
  Context {RB_fwritex : RelCode (sym 0x17d50) 312}.
  Context {RB_sn_write : RelCode (sym 0x7f000300) 220}.
  Context {SPEC_sn_write : sn_write_contract}.
  Collection ImgHyps := IMG CODE_fwritex RB_fwritex RB_sn_write SPEC_sn_write.

Definition fwritex_w_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (f WEND WB bufp CK cs cn : Z) (pend src dst : list byte),
  a2 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a0) src ->
  bv_unsigned a1 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 32) [C8 (Z_to_bv 64 WEND)] ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 72) [C8 (Z_to_bv 64 (sym 0x7f000300))] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend ->
  (0 < WEND < 2^64) -> (WB + Z.of_nat (length pend) <= WEND) ->
  (WEND - (WB + Z.of_nat (length pend)) < Z.of_nat (length src)) ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  (0 <= cn < 2^64) -> (sn_k cn pend src < Z.of_nat (length dst)) ->
  stk img_segs m (bv_unsigned sp - 64) (bv_unsigned sp) -> (64 <= bv_unsigned sp) ->
  mem_inv img_segs m ->
  (f + 160 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= f + 32) ->
  (CK + 16 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= CK) ->
  (cs + Z.of_nat (length dst) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= cs) ->
  (WB + Z.of_nat (length pend) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= WB) ->
  (bv_unsigned a0 + Z.of_nat (length src) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0) ->
  (CK + 16 <= f + 40 \/ f + 160 <= CK) ->
  (cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs) ->
  (cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs) ->
  (WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB) ->
  (bv_unsigned a0 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a0) ->
  (bv_unsigned a0 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a0) ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x17d50)) fc None m (seg_rom img_segs)).

Lemma fwritex_w_ok : fwritex_w_stmt.
Proof.
  unfold fwritex_w_stmt.
  intros until dst. intros -> SRC LEN WEND' WPOS WBASE WRF BUF COOKIE CKC PEND HW1 HW2 HW3 DST HCN HK ST SPLO MI
    S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11.
  pose proof (rw_cells_bound _ _ _ _ WEND') as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB2. cbn [cells_size csize Nat.add] in FB2.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64); (CK, CK + 16);
                          (cs, cs + Z.of_nat (length dst))] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat ST.
  do 8 zstep.
  zstep. zstep. zstep. zstep. zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
  { exfalso. lia. }
  zstep. zstep. zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
  { exfalso. lia. }
  zstep. zstep. zstep. zstep.
  do 7 zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  setreg2 sp.
  replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in ST, MU by lia.
  unfold sn_write_contract in SPEC_sn_write.
  eapply evt_mono.
  { eapply (SPEC_sn_write) with (f := f) (WB := WB) (bufp := bufp) (CK := CK) (cs := cs) (cn := cn) (pend := pend) (src := src) (dst := dst);
      first [ reflexivity | eassumption | lia ]. }
  intros ms' P. unfold sn_write_post in P |- *.
  destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & E & MU2 & WM2 & MI2 & P).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m2.
  split; [exact E|]. split; [eapply munch_trans; [exact MU | exact MU2]|].
  split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. exact P.
Qed.

End Img.

Existing Class fwritex_w_stmt.
