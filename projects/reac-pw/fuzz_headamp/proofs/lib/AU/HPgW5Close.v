(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 465 of its 512 lines of code are new or changed and 364 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Close.v and RPgW5CloseP.v at 164759458cd
   (one file); module paths changed, the w5_ prefix renamed to hw5_ (the kit lib/AU/HPgW5Kit.v), rm_ -> hm_,
   rs_ -> hsu_ (the cut states of lib/AU/HPgSeg.v); the walk is image B's own code (its registers, its R-relative
   cells, its UBSan tests, the cursor and what is left in registers, not in a real-frame cell). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the params Struct's close,
   CL 0x82a18 -> LATCH 0x82ae4, in LLVMFuzzerTestOneInput (0x80c40; pod.h:434-438), the piece statement
   lib/AU/HPgSeg.v hsu_piece_W5_close_stmt at image B's record headamp_himg_B and builder pcs headamp_bld_B.
   Proves no function (kind: segment lemma).

   THE CODE
     0x82a18  ld a0,0x150(s1); lbu a0,0(a0); beqz a0 / j 0x83c2c   the check of the 8-byte load of pp->len
     0x82a28  a0 := 0x4001; t0 := R+0x98 (the property index); a5 := R+0x90 (pp + at); a6 := R+0x88 (at)
     0x82a3c  bltu a6,a0 (at < 0x4001) / j 0x83a14                  UBSan test, decided by at's range
     0x82a44  t3 := s10 (what is left); a0 := R+0xf0 (~pp); s10 := 1
     0x82a50  bgeu a0,a6 (~pp >= at) / j 0x83a14                    UBSan test, decided by the two ranges
     0x82a58  a7 := s5 (the cursor); the checks of the first and the last byte of the 4-byte store at pp + at
              (slow blocks 0x82b2c / 0x82b38); a1 := pp->len (ld a1,0(s2)); a4 := R+0x78 (pp + 0x400c)
     0x82a88  subw a0,a1,a6; addi a0,a0,-8 (len - at - 8); the four `sb` of it at pp + at
     0x82aac  a0 := R+0x140 (first); beqz a0 -> 0x82ae0
     0x82ab4  first: the check of pp + 0x400c (slow block 0x82ba4), a0 := R+0x50 (pp + 0x4010), has_params := s10 = 1;
              the check of pp + 0x4010 (slow block 0x82bb4), params_struct := 1
     0x82ae0  a3 := R+0x80 (seen = 1); end 0x82ae4
   Every check is on pp's bytes, covered by the shadow entries (pp, 0x4000, 0x4018) and (pp + at, 0, 16) of
   hw5_shent_blk; the error paths are not reached. first is 0 or 1 by the start state; the walk takes the two values
   as two runs, so `beqz` is decided.

   REGISTERS AND R-CELLS (the port to role's image B renames these). Read: s1 = R (x9), s2 = pp + 0x4000 (x18),
   s5 = the cursor (x21), s10 = what is left (x26), s11 = K (x27); the cells R+0x50 (pp + 0x4010), R+0x78
   (pp + 0x400c), R+0x80 (seen = 1), R+0x88 (at), R+0x90 (pp + at), R+0x98 (the property index), R+0xf0 (~pp),
   R+0x140 (first), R+0x150 (the shadow address of pp + 0x4000); pp->len at pp + 0x4000. Written: t0 (x5), a0 .. a7
   (x10 .. x17), s10 (x26), t3 (x28); the bytes pp + at .. pp + at + 4 and, when first = 1, pp + 0x400c ..
   pp + 0x4014. No R-relative cell is written.

   HOW. The core walk hw5_close_core starts the kit's engine at 0x82a18 over explicit facts: the registers as
   their own atoms (s2 pinned to pp + 0x4000 over the atom pp, s11 to the kit's shadow-offset atom 32), the extra
   atoms pp + at, at, len, pp, ~pp and the property index, the R-relative cells as one read-only region of base s1,
   pp's fields and pp + at as two regions with their write windows; the atoms' ranges decide the two UBSan tests.
   The piece lemma hw5_piece_close reads the cut CL, calls the core and rebuilds the cut LATCH: the journal and
   frame part (hw5_core_post), the (location, value) facts (kept, and t0, a3, a7, t3, s10 from the core's post),
   the frame's shadow (kept), the first block's image (Model.pc_buf_close and the two flag words when the Struct is
   the first params property: hw5_img_close_eq, hw5_img_gen) and the model facts (Model.props_loop's Struct arm,
   from the cut's tie of the count and the pods to the input). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW5Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the start state at 0x82a18: atoms 32 = K, 33 = pp + at, 34 = at, 35 = len, 36 = pp, 37 = ~pp, 38 = the
   property index ---- *)
Definition cl_ov : list (bv 5 * sv) := [((18%bv : bv 5), SOff 36 0x4000); ((27%bv : bv 5), hw5_Bx)].
Definition cl_slots (f : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x50 0x158 0 0
   [YP09.mkChunk 0x50 (CVal 8 (SOff 36 0x4010)); YP09.mkChunk 0x78 (CVal 8 (SOff 36 0x400c));
    YP09.mkChunk 0x80 (CVal 8 (SLit 1)); YP09.mkChunk 0x88 (CVal 8 (SOff 34 0));
    YP09.mkChunk 0x90 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 38 0));
    YP09.mkChunk 0xf0 (CVal 8 (SOff 37 0)); YP09.mkChunk 0x140 (CVal 8 (SLit f));
    YP09.mkChunk 0x150 (CVal 8 (hw5_sh 36 0x4000))].
Definition cl_fields (f : Z) : YP09.region :=
  YP09.mkRegion (Some 36%nat) 0x4000 0x4018 0x400c (0x400c + 8 * f)
   [YP09.mkChunk 0x4000 (CVal 8 (SOff 35 0))].
Definition cl_at : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
(* ~pp = 2^64 - pp - 1 for 4096 <= pp <= 0x7fffff800000 *)
Definition CL_NPLO : Z := 18446603336229584895.
Definition CL_NPHI : Z := 18446744073709547519.
Definition cl_facts : facts :=
  mkFacts [(9%nat, mkAF 70368744177664 140737488355328 5); (32%nat, mkAF HW5_SB HW5_SB 0);
           (33%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 16 5440 0); (35%nat, mkAF 16 5440 0);
           (36%nat, mkAF 4096 140737479966720 4); (37%nat, mkAF CL_NPLO CL_NPHI 0)]
   [] [].
Definition ss_cl (f : Z) : sstate := mkSS 0x82a18 (hw5_sr cl_ov) [cl_slots f; cl_fields f; cl_at] None cl_facts.
Definition cl_SH : list shent := [mkSHE 36 0x4000 0x4018; mkSHE 33 0 16].
Definition cl_extra (pp atv len np : Z) : list word :=
  [w64 HW5_SB; w64 (pp + atv); w64 atv; w64 len; w64 pp; Z_to_bv 64 (- pp - 1); w64 np].
Definition cl_clob : list (bv 5) := [5; 10; 11; 12; 13; 14; 15; 16; 17; 26; 28]%bv.

(* the value the four `sb` store: len - at - 8, as the engine computes it from `subw` and `addi` *)
Definition cl_X : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit 18446744073709551615)) (SLit (-8))) (SOff 35 0).
Lemma cl_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Section u. Context {fx : YK11.FPState}.
Lemma cl_U_X : forall E atv len, ew E 34 = Z_to_bv 64 atv -> ew E 35 = Z_to_bv 64 len ->
0 < atv < 2 ^ 32 -> 0 <= len < 2 ^ 32 -> atv + 8 <= len -> U E cl_X = len - atv - 8.
Proof.
intros E atv len H34 H35 Ha Hl Hal. unfold cl_X.
rewrite !U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 34 atv H34), (U_atom E 35 len H35), !U_SLit by lia.
rewrite (zcanon_id 18446744073709551615) by (unfold M64; lia).
rewrite (cl_zc (atv * 18446744073709551615) (atv - 1) (18446744073709551616 - atv)) by lia.
rewrite (cl_zc (-8) (-1) (18446744073709551616 - 8)) by lia.
rewrite (cl_zc (18446744073709551616 - atv + (18446744073709551616 - 8)) 1 (18446744073709551616 - atv - 8)) by lia.
apply (cl_zc _ 1); lia.
Qed.
Lemma cl_U_Xs : forall E atv len k, ew E 34 = Z_to_bv 64 atv -> ew E 35 = Z_to_bv 64 len ->
0 < atv < 2 ^ 32 -> 0 <= len < 2 ^ 32 -> atv + 8 <= len -> (k = 8 \/ k = 16 \/ k = 24) ->
U E (SAlu ALU_SRL cl_X (SLit k)) = Z.shiftr (len - atv - 8) k.
Proof.
intros E atv len k H34 H35 Ha Hl Hal Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite (cl_U_X E atv len) by assumption.
rewrite U_SLit.
assert (HL : Z.land (zcanon k) 63 = k) by (destruct Hk as [-> | [-> | ->]]; reflexivity).
rewrite HL.
assert (0 <= Z.shiftr (len - atv - 8) k <= len - atv - 8).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
apply zcanon_id. unfold M64. lia.
Qed.
(* an atom's denotation is the word the environment holds *)
Lemma cl_den0 : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
End u.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma hw5_close_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv len np fsv cur nl : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 9 = w64 R -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 21 = w64 cur ->
  getr regs 26 = w64 nl -> getr regs 27 = w64 SHADOW_OFF ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x50) 8 (pp + 0x4010) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (pp + 0x400c) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 1 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x88) 8 atv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 (pp + atv) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 np ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 fsv ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 8 <= len -> len <= 5440 -> (fsv = 0 \/ fsv = 1) -> 0 <= np < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs 0x82a18 regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82ae4 cl_clob
      (fun a => (pp + atv <= a < pp + atv + 4) \/ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4014))
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 (len - atv - 8)) /\
        getr regs2 5 = w64 np /\ getr regs2 13 = w64 1 /\ getr regs2 17 = w64 cur /\
        getr regs2 26 = w64 1 /\ getr regs2 28 = w64 nl /\
        (fsv = 1 -> hm_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Z_to_le_bytes 4 1) /\
                    hm_bytes rsegs (w_H W2) mem2 (pp + 0x4010) (Z_to_le_bytes 4 1)))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv len np fsv cur nl
  HJ Hpp Hfresh H9 H18 H21 H26 H27 V50 V78 V80 V88 V90 V98 Vf0 V140 V150 Vlen HR32 HRlo HRhi Hat Hal Hlen Hfst Hnp.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh.
assert (Hf01 : 0 <= fsv <= 1) by (destruct Hfst as [-> | ->]; lia).
assert (Hnpp : (- pp - 1) mod 2 ^ 64 = 2 ^ 64 - pp - 1).
{ rewrite <- (Z.mod_add (- pp - 1) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
set (E := Ereg regs (cl_extra pp atv len np)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E21 : ew E 21 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E26 : ew E 26 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 len) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (- pp - 1)) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = w64 np) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (HE : E = Ereg regs (cl_extra pp atv len np)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx cl_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 36 0x4000 0x4018 pp HAR Hpp E36);
      [lia | exact E32 | lia | lia | rewrite Hrq'; lia].
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 33 0 16 (pp + atv) HAR Hpp E33);
      [lia | exact E32 | lia | lia | rewrite Hrq'; lia]. }
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp + atv) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = len) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = pp) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = 2 ^ 64 - pp - 1) by (rewrite E37, Z_to_bv_unsigned; exact Hnpp).
assert (HR0 : regs_ok E (hw5_sr cl_ov) regs).
{ apply (hw5_regs_ok E regs (cl_extra pp atv len np)); [exact HE|]. unfold cl_ov.
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 36 pp 0x4000 E36) by lia. rewrite H18. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E cl_facts).
{ split; [| split; [exact I | exact I]].
  cbn [cl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33, U34, U35, U36, U37. unfold CL_NPLO, CL_NPHI.
  repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
                      | (change (2 ^ 4) with 16; assumption) | (change (2 ^ 5) with 32; assumption) ]. }
assert (HS : st_ok rsegs E (ss_cl fsv) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82a18) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_cl.
  apply (hw5_entry rsegs _ _ regs (cl_extra pp atv len np) E); [exact HE | exact HR0 | | | | exact HFK].
  - unfold cl_slots, cl_fields, cl_at. destruct Hfst as [-> | ->]; vm_compute; reflexivity.
  - unfold cl_slots, cl_fields, cl_at.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x50 8 (SOff 36 0x4010) (pp + 0x4010));
          [ rewrite (hw5_den_off E 36 pp 0x4010 E36) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V50 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x78 8 (SOff 36 0x400c) (pp + 0x400c));
          [ rewrite (hw5_den_off E 36 pp 0x400c E36) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V78 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x80 8 (SLit 1) 1);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V80 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x88 8 (SOff 34 0) atv);
          [ rewrite (hw5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V88 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x90 8 (SOff 33 0) (pp + atv));
          [ rewrite (hw5_den_off E 33 (pp + atv) 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V90 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x98 8 (SOff 38 0) np);
          [ rewrite (hw5_den_off E 38 np 0 E38) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V98 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 37 0) ((- pp - 1) mod 2 ^ 64));
          [ cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply Z_to_bv64_mod
          | rewrite Hnpp; change (8 * Z.of_N 8) with 64; lia | lia | exact Vf0 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x140 8 (SLit fsv) fsv);
          [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V140 ] |].
      apply Forall_cons;
        [ apply (chunk_ok_val rsegs E _ R 0x150 8 (hw5_sh 36 0x4000) (shadow_addr (pp + 0x4000) mod 2 ^ 64));
          [ rewrite (hw5_den_sh E 36 pp 0x4000 E36 E32) by lia; unfold w64; symmetry; apply Z_to_bv64_mod
          | pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia));
            change (8 * Z.of_N 8) with 64; lia
          | lia | exact V150 ] |].
      apply Forall_nil.
    + apply (hm_rw_region rsegs E (w_H W) memc 36 pp);
        [ exact U36 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 35 0) len);
        [ rewrite (hw5_den_off E 35 len 0 E35) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (hm_rw_region rsegs E (w_H W) memc 33 (pp + atv));
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
  - unfold cl_slots, cl_fields, cl_at; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [r_base r_lo r_hi base_val]; rewrite U9, U36, U33; repeat split; try exact I; lia. }
destruct Hfst as [-> | ->].
all: unfold cfg_at; change (w64 0x82a18) with (Z_to_bv 64 0x82a18).
all: aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x82ae4.
(* the write windows: pp + at and the two flag words in pp *)
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 36%nat pp);
    [ reflexivity | exact U36
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (pp + atv));
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ]).
(* the end state at 0x82ae4 *)
all: apply SRr_ret; unfold hw5_post.
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  exists lyc, Sc, (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
    exact (hw5_regs_kept E Ef 40 (hw5_sr cl_ov) (ss_regs ssf) regs (ms_regs msf) cl_clob HR0 HRf
             (env_agree_refl 40 E) ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply hw5_same_io_wvb]|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hst := fresh "Hst" in let Hn := fresh "Hn" in
    intros a Ha Hst Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (hw5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U36, ?U33 in Hb; apply Hn; cbv beta; lia | ]);
    destruct Hr
  | ] end.
(* what the piece wrote and computed, from the end state's regions and registers *)
all: lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  let HM := fresh "HM" in pose proof HSf as (_ & _ & _ & _ & _ & _ & _ & (_ & HM & _) & _);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rs := fresh "Rs" in let Rf := fresh "Rf" in let Ra := fresh "Ra" in
  apply Forall_cons_iff in HM as [Rs HM]; apply Forall_cons_iff in HM as [Rf HM];
  apply Forall_cons_iff in HM as [Ra _];
  let Cs := fresh "Cs" in let Cf := fresh "Cf" in let Ca := fresh "Ca" in
  destruct Rs as (_ & _ & _ & Cs); destruct Rf as (_ & _ & _ & Cf); destruct Ra as (_ & _ & _ & Ca);
  cbn [r_chunks r_base base_val] in Cs, Cf, Ca; rewrite U9 in Cs; rewrite U36 in Cf; rewrite U33 in Ca;
  rewrite Forall_forall in Cs, Cf, Ca;
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _)
  end.
all: assert (M0 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 0) = Some (Z_to_bv 8 (len - atv - 8))).
all: try (rewrite <- (cl_U_X E atv len E34 E35) by lia; apply (hw5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M1 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 1) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 8))).
all: try (rewrite <- (cl_U_Xs E atv len 8 E34 E35) by lia; apply (hw5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M2 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 2) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 16))).
all: try (rewrite <- (cl_U_Xs E atv len 16 E34 E35) by lia; apply (hw5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: assert (M3 : mbyte rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + atv + 3) =
  Some (Z_to_bv 8 (Z.shiftr (len - atv - 8) 24))).
all: try (rewrite <- (cl_U_Xs E atv len 24 E34 E35) by lia; apply (hw5_mbyte_chunk1 rsegs E);
          apply Ca; cbn [In]; repeat (first [left; reflexivity | right])).
all: split;
  [ apply hm_bytes_aview; intros i Hi; rewrite length_Z_to_le_bytes in Hi;
    rewrite hm_nth_le_bytes by lia; unfold aview;
    destruct i as [|[|[|[|i]]]]; [| | | | lia];
    [ change (Z.of_nat 0) with 0; rewrite M0; cbn [option_map]; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity
    | change (Z.of_nat 1) with 1; rewrite M1; reflexivity
    | change (Z.of_nat 2) with 2; rewrite M2; reflexivity
    | change (Z.of_nat 3) with 3; rewrite M3; reflexivity ]
  |].
all: split; [transitivity (sv_denot E (SOff 38 0)); [exact (HRf 5%bv) | exact (cl_den0 E 38 _ E38)] |].
all: split; [transitivity (sv_denot E (SLit 1)); [exact (HRf 13%bv) | reflexivity] |].
all: split; [transitivity (sv_denot E (SOff 21 0)); [exact (HRf 17%bv) | exact (cl_den0 E 21 _ E21)] |].
all: split; [transitivity (sv_denot E (SLit 1)); [exact (HRf 26%bv) | reflexivity] |].
all: split; [transitivity (sv_denot E (SOff 26 0)); [exact (HRf 28%bv) | exact (cl_den0 E 26 _ E26)] |].
all: intros Hf1; try discriminate Hf1; split; apply hm_bytes_of_val.
all: first
  [ apply (val_of_chunk_ok rsegs E _ pp 0x400c 4 (SLit 1) 1);
    [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ]
  | apply (val_of_chunk_ok rsegs E _ pp 0x4010 4 (SLit 1) 1);
    [ apply Cf; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | lia ] ].
Qed.
End c.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the model at the close ---- *)
Lemma hw5_wf_close : forall sh ps es, hsu_wf sh ps -> (length ps <= 2)%nat -> Forall ent_wf es ->
(length es <= 32)%nat -> hsu_wf sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]).
Proof.
intros sh ps es (Hs & Hk & He & Hl) H2 Hes Hn.
assert (HK : 0 <= POD_PROP_PARAMS < 2 ^ 32) by (unfold POD_PROP_PARAMS; split; [lia | apply Z.ltb_lt; reflexivity]).
split; [exact Hs|]. split.
- apply Forall_app. split; [exact Hk|]. constructor; [split; [exact HK | exact Hn] | constructor].
- split; [unfold all_ents in *; rewrite flat_map_app; cbn [flat_map snd]; rewrite app_nil_r;
          apply Forall_app; split; assumption|].
  rewrite length_app. cbn [length]. lia.
Qed.
Lemma hw5_seen_close : forall ps es, hsu_seen (ps ++ [(POD_PROP_PARAMS, PStruct es)]) = 1.
Proof.
intros ps es. unfold hsu_seen. rewrite existsb_app. cbn [existsb fst]. rewrite Z.eqb_refl. cbn [orb].
rewrite orb_true_r. reflexivity.
Qed.
Lemma hw5_loop_close : forall sh ps cnt es rest r, sh <> 7 ->
ps = fst (props_loop sh (length ps) (hsu_r0 rest)) -> hsu_pod_tie sh ps cnt es rest r -> Z.of_nat (length es) = cnt ->
(ps ++ [(POD_PROP_PARAMS, PStruct es)], r) =
props_loop sh (length (ps ++ [(POD_PROP_PARAMS, PStruct es)])) (hsu_r0 rest).
Proof.
intros sh ps cnt es rest r Hsh Hps (sel & c & r1 & r2 & Hs1 & Hc & Hcnt & Hm4 & Hb4 & He) Hlen.
rewrite length_app. cbn [length]. rewrite Nat.add_1_r. rewrite props_loop_S_end.
remember (props_loop sh (length ps) (hsu_r0 rest)) as pl eqn:EL. destruct pl as [ps0 r0].
cbn [fst snd] in Hps, Hs1. subst ps0. cbv beta iota.
unfold prop_step. rewrite <- Hs1. cbv beta iota.
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
replace (sel mod 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hm4).
rewrite Hb4. cbv beta iota. rewrite <- Hc. cbv beta iota.
rewrite <- Hcnt, <- Hlen, Nat2Z.id, He. reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hw5_piece_close : forall B MT, ameter_laws MT ->
  hsu_piece_W5_close_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros B MT MTL.
unfold hsu_piece_W5_close_stmt. intros cx POST rest i Hst HL.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hw5_pre_facts B cx _ Hpre) as
  (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp & FApp).
pose proof ASAN_CEIL_range as ([AC1 AC2] & _). unfold ASAN_CEIL in AC1, AC2.
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
assert (PB2' : e_pp (x_e cx) + 19744 <= alloc_ceiling) by (rewrite <- HPS; exact PB2).
unfold hsu_from_CL. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es r Hlen Hcut.
destruct Hcut as (Hcore & Hat & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen1 & Hps & Htie & Hsh & Hnp & Hpsnp & Hnp3 & Hsh7 &
  Hps2 & Hcnt & Hesw & Hescnt).
unfold hsu_at_cx in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walk takes ---- *)
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))).
{ rewrite <- (hw5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (hw5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
pose proof (hw5_at_reg _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hw5_in)) as A9.
pose proof (hw5_at_reg _ _ _ _ _ 18 (e_pp (x_e cx) + Layout.OFF_LEN) Hat ltac:(hw5_in)) as A18.
pose proof (hw5_at_reg _ _ _ _ _ 21 (hsu_cur rsegs cx rest r) Hat ltac:(hw5_in)) as A21.
pose proof (hw5_at_reg _ _ _ _ _ 26 (Z.of_nat (length r)) Hat ltac:(hw5_in)) as A26.
pose proof (hw5_at_reg _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(hw5_in)) as A27.
pose proof (hw5_at_cell _ _ _ _ _ 0x50 (e_pp (x_e cx) + Layout.OFF_PARAMS_STRUCT) Hat ltac:(hw5_in)) as V50.
pose proof (hw5_at_cell _ _ _ _ _ 0x78 (e_pp (x_e cx) + Layout.OFF_HAS_PARAMS) Hat ltac:(hw5_in)) as V78.
pose proof (hw5_at_cell _ _ _ _ _ 0x80 1 Hat ltac:(hw5_in)) as V80.
pose proof (hw5_at_cell _ _ _ _ _ 0x88 (hsu_at_of sh ps) Hat ltac:(hw5_in)) as V88.
pose proof (hw5_at_cell _ _ _ _ _ 0x90 (e_pp (x_e cx) + hsu_at_of sh ps) Hat ltac:(hw5_in)) as V90.
pose proof (hw5_at_cell _ _ _ _ _ 0x98 (Z.of_nat (length ps)) Hat ltac:(hw5_in)) as V98.
pose proof (hw5_at_cell _ _ _ _ _ 0xf0 (- e_pp (x_e cx) - 1) Hat ltac:(hw5_in)) as Vf0.
pose proof (hw5_at_cell _ _ _ _ _ 0x140 (hsu_first ps) Hat ltac:(hw5_in)) as V140.
pose proof (hw5_at_cell _ _ _ _ _ 0x150 (shadow_addr (e_pp (x_e cx) + Layout.OFF_LEN)) Hat ltac:(hw5_in)) as V150.
pose proof (hw5_plen_lo sh ps Hsh7) as Hplen.
pose proof (hw5_buf_open_len sh ps es) as Hbuf.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_open sh ps es Hv He Hesw) as [Hblen _].
set (len := Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))) in *.
assert (Hat16 : 16 <= hsu_at_of sh ps) by (unfold hsu_at_of; lia).
assert (Hal : hsu_at_of sh ps + 8 <= len) by (unfold hsu_at_of; lia).
assert (H5440 : len <= 5440) by lia.
pose proof (hw5_first_range ps) as Hfr.
assert (Hnp0 : 0 <= Z.of_nat (length ps) < 2 ^ 64) by lia.
rewrite Z.mod_small in V50 by (unfold Layout.OFF_PARAMS_STRUCT; lia).
rewrite Z.mod_small in V78 by (unfold Layout.OFF_HAS_PARAMS; lia).
rewrite Z.mod_small in V80 by lia.
rewrite Z.mod_small in V88 by lia.
rewrite Z.mod_small in V90 by lia.
rewrite Z.mod_small in V98 by lia.
rewrite Z.mod_small in V140 by lia.
assert (Hes32 : (length es <= 32)%nat) by lia.
pose proof (hw5_ents_bounds sh ps (Some es) Hwf (conj Hesw Hes32)) as (EB1 & EB2).
assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 len).
{ refine (hm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
(* ---- the core walk ---- *)
eapply SRr_bind.
{ change (cfg_at rsegs (bi_CL headamp_bld_B) regs2 mem2 md2) with (cfg_at rsegs 0x82a18 regs2 mem2 md2).
  exact (hw5_close_core B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps) len
    (Z.of_nat (length ps)) (hsu_first ps) (hsu_cur rsegs cx rest r) (Z.of_nat (length r))
    HJ Ppin2 Ppout A9 A18 A21 A26 A27 V50 V78 V80 V88 V90 V98 Vf0 V140 V150 Vlen RB3 RB1 RB2
    Hat16 Hal H5440 Hfr Hnp0). }
intros W3 c3 Hle Hpost.
assert (HEp : forall a, (e_pp (x_e cx) + hsu_at_of sh ps <= a < e_pp (x_e cx) + hsu_at_of sh ps + 4) \/
  (hsu_first ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4014) -> hsu_E1 rsegs headamp_himg_B cx a).
{ intros a [Ha|[_ Ha]]; right; unfold PP_SIZE; lia. }
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) cl_clob).
{ intros r0 [-> | [-> | ->]]; unfold cl_clob; hw5_notin. }
destruct (hw5_core_post B MT MTL cx (hsu_E1 rsegs headamp_himg_B cx) _ ly2 S2 W2 regs2 mem2 md2 0x82ae4 cl_clob _ W3 c3
  Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem & (Rsz & R5 & R13 & R17 & R26 & R28 & Rfl)).
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; lia).
(* every byte the piece did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ (e_pp (x_e cx) + hsu_at_of sh ps <= a < e_pp (x_e cx) + hsu_at_of sh ps + 4) ->
  ~ (hsu_first ps = 1 /\ e_pp (x_e cx) + 0x400c <= a < e_pp (x_e cx) + 0x4014) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. apply Hmem; [exact Ha | rewrite Hsp; exact H1 |]. intros [X|X]; auto. }
assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x220 ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
(* ---- the cut LATCH ---- *)
change (cfg_at rsegs 0x82ae4 regs3 mem3 md3) with (cfg_at rsegs (bi_LATCH headamp_bld_B) regs3 mem3 md3).
apply (HL ly3 S3 W3 regs3 mem3 md3 sh np (ps ++ [(POD_PROP_PARAMS, PStruct es)]) r);
  [rewrite length_app, Hlen; cbn [length]; lia|].
split; [exact Hcore3|].
split.
{ unfold hsu_fsh_at in *. eapply hm_fsh_kept; [exact Hfsh|]. intros j Hj.
  assert (LP0 : length (hsu_P0 headamp_himg_B) = 116%nat) by reflexivity. rewrite LP0 in Hj.
  pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)) as D1.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
  unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
  apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
split.
{ unfold hsu_pp_at.
  change (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh (ps ++ [(POD_PROP_PARAMS, PStruct es)]) None))).
  rewrite (hw5_img_close_eq sh ps es Hsh7). fold len.
  assert (LB1 : length (overwrite (pc_buf (PbCut sh ps (Some es))) (Z.to_nat (hsu_at_of sh ps))
      (le32 (len - hsu_at_of sh ps - 8))) = length (pc_buf (PbCut sh ps (Some es)))).
  { apply length_overwrite. rewrite length_le32. lia. }
  assert (Nb : hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (overwrite (pc_buf (PbCut sh ps (Some es)))
      (Z.to_nat (hsu_at_of sh ps)) (le32 (len - hsu_at_of sh ps - 8)))).
  { apply (hm_bytes_patch rsegs (w_H W2) mem2); [exact (hw5_img_buf _ _ _ _ _ _ _ _ _ Old) | | |].
    - rewrite Z2Nat.id by lia. exact Rsz.
    - rewrite length_le32. lia.
    - intros y Hy1 Hy2. rewrite length_le32 in Hy2. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
      intros [_ X]; lia. }
  apply (hw5_img_gen (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx)) (pc_buf (PbCut sh ps (Some es))) _ _
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
  - rewrite LB1. lia.
  - rewrite LB1. unfold POD_BUF_MAX. lia.
  - exact EB1.
  - exact EB2.
  - rewrite LB1. unfold OFF_LEN. eapply val_mem_kept; [|exact Vlen]. intros k0 Hk0. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *;
      try lia; intros [_ X]; lia.
  - destruct (Z.eqb_spec (hsu_first ps) 1) as [E|E].
    + rewrite orb_true_r. exact (proj1 (Rfl E)).
    + rewrite orb_false_r. refine (proj1 (hw5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
      intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
      intros [X _]; exact (E X).
  - destruct (Z.eqb_spec (hsu_first ps) 1) as [E|E].
    + rewrite orb_true_r. exact (proj2 (Rfl E)).
    + rewrite orb_false_r. refine (proj2 (hw5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
      intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia;
      intros [X _]; exact (E X).
  - intros y Hy. rewrite LB1 in Hy. unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
    apply Kp; unfold T_SEG_STK, ASTACK, PP_SIZE in *; try lia; intros [_ X]; lia. }
split; [exact Hin|]. split; [exact Hsuf|].
split; [apply hw5_wf_close; [exact Hwf | exact Hps2 | exact Hesw | lia]|].
split; [exact Hsh|]. split; [exact Hnp|].
split; [rewrite length_app; cbn [length]; lia|]. split; [exact Hnp3|].
split; [exact (hw5_loop_close sh ps cnt es rest r Hsh7 Hps Htie Hescnt)|].
unfold hsu_at_cx, hsu_at.
rewrite (hw5_seen_close ps es).
replace (Z.of_nat (length (ps ++ [(POD_PROP_PARAMS, PStruct es)])) - 1) with (Z.of_nat (length ps))
  by (rewrite length_app; cbn [length]; lia).
cbn [hsu_Rc1 hsu_Rc0 hsu_Kc app].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
all: first [ hw5_kept Hat Hkeep Kc | exact R5 | exact R13 | exact R17 | exact R26 | exact R28 ].
Qed.
End p.

Print Assumptions hw5_close_core.
Print Assumptions hw5_piece_close.
