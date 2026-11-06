(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/RL/G/G_fwritex.v, with its module paths and module names changed; 84 of its 175 lines of code are new or changed and 291 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require Import G_memcpy G_fwritex.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require Import CopyCall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.

Open Scope Z_scope.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_fwritex : CodeAtT img_segs (sym 0x17d50) (PROGAT_CODE_fwritex IMG)}.
  Context {RB_fwritex : RelCode (sym 0x17d50) 312}.
  Context {RN_B_memcpy_17d50 : RelNear (sym 0x17d50) (sym 0x21334)}.
  Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
  Context {SPEC_memcpy : memcpy_stack_contract copy_ready}.
  Collection ImgHyps := IMG CODE_fwritex RB_fwritex RN_B_memcpy_17d50 copy_ready SPEC_memcpy.

Definition fwritex_room_footprint (sp f D N : Z) : list ivl :=
  [(sp - SN_WRITE_DEPTH, sp); (D, D + N); (f + 40, f + 48)].

Definition fwritex_room_ready (m : word -> option byte) (sp f D S N : Z) : Prop :=
  forall m', munch (fwritex_room_footprint sp f D N) m m' -> wmono img_segs m m' -> copy_ready m' (sp - 64) D S N.

Definition fwritex_room_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch (fwritex_room_footprint (bv_unsigned sp) Fp (B + Z.of_nat (length content)) (Z.of_nat (length bs))) m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
    /\ bytes_at img_segs m' S bs.

Definition fwritex_room_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
  wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
  bytes_at img_segs m (bv_unsigned a0) bs ->
  Z.of_nat (length bs) = bv_unsigned a1 ->
  (length bs <= length junk)%nat ->
  stk img_segs m (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  SN_WRITE_DEPTH <= bv_unsigned sp ->
  fwritex_room_ready m (bv_unsigned sp) (bv_unsigned a2) (B + Z.of_nat (length content)) (bv_unsigned a0) (Z.of_nat (length bs)) ->
  (bv_unsigned a2 + 148 <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= bv_unsigned a2) ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= B) ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= bv_unsigned a0) ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
   \/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0) ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0) ->
  evt img_segs (fwritex_room_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x17d50)) fc None m (seg_rom img_segs)).

Definition memcpy_postS (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (Dst Src : Z) (n : nat) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(Dst, Dst + Z.of_nat n); (bv_unsigned sp - COPY_DEPTH, bv_unsigned sp)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - COPY_DEPTH) (bv_unsigned sp)
    /\ rw_cells img_segs m' Dst [CB n src]
    /\ bytes_at img_segs m' Src src.

Lemma memcpy_callS : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src : Z) (n : nat) (src junk : list byte),
  bv_unsigned a0 = Dst -> bv_unsigned a1 = Src -> bv_unsigned a2 = Z.of_nat n ->
  bytes_at img_segs m Src src -> length src = n ->
  rw_cells img_segs m Dst [CB n junk] ->
  (Src + Z.of_nat n <= Dst \/ Dst + Z.of_nat n <= Src) ->
  (Src + Z.of_nat n <= bv_unsigned sp - COPY_DEPTH \/ bv_unsigned sp <= Src) ->
  mem_inv img_segs m ->
  stk img_segs m (bv_unsigned sp - COPY_DEPTH) (bv_unsigned sp) ->
  copy_ready m (bv_unsigned sp) Dst Src (Z.of_nat n) ->
  evt img_segs (memcpy_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 Dst Src n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros HD HS HN SRC LEN DST SEP SSEP MI ST READY. subst Dst Src.
  eapply evt_mono.
  { eapply (SPEC_memcpy ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
      rewrite ?HN, ?Nat2Z.id; [exact SRC | exact LEN | exact DST | exact SEP | exact SSEP | exact MI | exact ST | exact READY]. }
  intros ms' P. unfold memcpy_stack_post in P. unfold memcpy_postS. rewrite HN, Nat2Z.id in P.
  destruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & ST' & DC & SC).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'. tauto.
Qed.

Lemma fwritex_room_ok : fwritex_room_stmt.
Proof.
  unfold fwritex_room_stmt.
  intros until bs. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST MI SPLO READY SEP1 SEP2 SEP3 SEP4 SEP5.
  unfold fwritex_room_ready, fwritex_room_footprint in READY.
  unfold SN_WRITE_DEPTH, COPY_DEPTH in *.
  pose_word_ranges.
  set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (S := bv_unsigned a0) in *.
  set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  pose proof (munch_refl [(bv_unsigned sp - (64 + 2240), bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb);
                          (Fp + 40, Fp + 48)] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  unfold FILE_cells in FC.
  carve_frame 64%nat ST.
  do 8 zstep.
  zstep. zstep. zstep. zstep.
  zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
  { exfalso. lia. }
  zstep. zstep.
  zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
  2:{ exfalso. lia. }
  zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
  2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
  zstep. zstep.
  apply (rw_cells_split_CB img_segs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
  cbn [mk_CB_cells app] in BUF.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
  cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
  apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
  cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.
  assert (LBb : length (firstn lb junk) = lb) by (rewrite length_firstn; lia).
  zstep.
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (memcpy_callS) with (Dst := B + Z.of_nat nc) (Src := S) (n := lb) (src := bs) (junk := firstn lb junk);
      [ rewrite ?unsigned_lit by lia; lia | rewrite ?unsigned_lit by lia; lia | rewrite ?unsigned_lit by lia; lia
      | exact SRC | reflexivity | exact BUFb | lia | rewrite unsigned_lit by lia; unfold COPY_DEPTH; lia | assumption
      | rewrite unsigned_lit by lia; unfold COPY_DEPTH; replace (bv_unsigned sp + -64 - 2240) with (bv_unsigned sp - (64 + 2240)) by lia; exact ST
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; eapply READY; [exact MU | exact WM] ]
    | intros ms P; unfold memcpy_postS, COPY_DEPTH in P; rewrite unsigned_lit in P by lia; revert ms P; post_call sg mm ]
  end.
  match goal with H : stk _ _ (?q + -64 - 2240) _ |- _ =>
    replace (q + -64 - 2240) with (q - (64 + 2240)) in H by lia; try clear ST; rename H into ST end.
  match goal with MC : rw_cells _ _ (B + Z.of_nat nc) [CB lb bs] |- _ => try clear BUFb; rename MC into BUFb end.
  rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
  zstep. zstep. zstep. zstep.
  try replace (0 + bv_unsigned a1) with (Z.of_nat lb) by lia.
  try replace (B + Z.of_nat nc + bv_unsigned a1) with (B + Z.of_nat (length (content ++ bs))) by (rewrite length_app; lia).
  do 9 zstep. release_frame FR ST (bv_unsigned sp).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUF : rw_cells img_segs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
    [ cbn [app]; apply (proj2 (rw_cells_app img_segs _ _ [_] _)); split; [ exact BUFa |];
      cbn [cells_size csize]; rewrite Nat.add_0_r;
      apply (proj2 (rw_cells_app img_segs _ _ [_] _)); split; [ exact BUFb |];
      cbn [cells_size csize]; rewrite Nat.add_0_r; exact BUFc
    | apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
      rewrite Nat.add_0_r, app_nil_r in BUF; clear BUFa BUFb BUFc ]
  end.
  apply evt_done. unfold fwritex_room_post, fwritex_room_footprint, SN_WRITE_DEPTH, COPY_DEPTH.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [ ms_eq | ].
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try (replace (bv_unsigned sp - (64 + 2240)) with (bv_unsigned sp + -64 - 2240) by lia; assumption).
  unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
  rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
  replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb)) with (B + Z.of_nat nc + Z.of_nat nj) by lia.
  try replace (B + Z.of_nat nc + bv_unsigned a1) with (B + (Z.of_nat nc + Z.of_nat lb)) in FC by lia.
  split; [exact FC|]. split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.

End Img.

Existing Class fwritex_room_stmt.
