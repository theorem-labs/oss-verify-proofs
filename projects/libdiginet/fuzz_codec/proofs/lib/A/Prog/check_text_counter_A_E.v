(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan, sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16): 0x80b44 -> the
   cut P1 at 0x80c4c (lib/A/PPgParseCx.v ss_P1). rule 24: no function proved (a segment of the walk).

   What changed against the donor, each read from the neutral excerpt of 0x80b44-0x80c48:
   - the function is a callee: the start is the contract's premises (PPgParseCx.v pp_pre, the caller's journal of
     pin_pre_kit) and the entry state ss_pp0 (pp_entry), not afn_pre / ajournal_init; every write of the walk is
     allowed by that journal (the save area lies in [sp0 - STK, sp0), the frame is in the journal's own list
     after the call).
   - 160-byte save area (`addi sp,sp,-0xa0` 0x80b44, `sd zero,0(sp)` at sp-160, ra .. s11 at sp-8 .. sp-104),
     `andi sp,sp,-0x20` at 0x80b84: sp1 = 32 * ((sp - 160) / 32) in [sp - 176, sp - 160] (donor: 192 / 208);
     the stack region is trimmed to the saves [-104, 0) (donor :228-234) and region 70 = [sp1+8, sp1+56) holds the
     spill of F at sp1+0x30 (donor :235-246 [16, 88)).
   - the GOT loads at 0x80b94-0x80ba8 (0x990a8 -> 0xa1600, the option word 1; 0x99050 -> 0xa15f8, SB into s3),
     `beqz a2` at 0x80bb0 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80bb4 / 0x80bb8 (RA
     0x80bbc): the class-0 call through aj_stack_malloc_atS with ASM0, its premises the call-site lemma
     pin_fs0_site below (count_cid 0 (frames Sc) < fs_frames 0 is the contract's premise).
   - the class-0 frame: 64 bytes, 8 shadow bytes, the flag pointer at F + 56 (donor class 1: 128 / 16 / F + 120).
   - 0x80bbc-0x80c48: `bnez s2` at 0x80bcc decided by HPTR 5 on F (the probe loop 0x80bd0-0x80be8 is not reached),
     `sd s11,0x30(s1)`, the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80b44, s4 = SB + F/8, the 8
     shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80c4c (the donor's size split has no
     counterpart here).
   - the hand-off is the continuation pp_from ss_P1 INV_P1 (PPgParseCx.v): the frame's shadow region made
     read-only, the four cell regions dropped, and the kept-memory fact (lib/Reusable/YCbq.v acall_kept, the
     form of proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParse.v at 6ebe35ba632) carried from the entry memory
     through every step (lib/A/PPgParseLib.v pz_kept_refl / pz_kept_run / pz_kept_trans / pz_kept_own). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse0.v, with its module paths changed; 330 of its 366 lines of code are new or changed and 357 lines of the source are left out. *)
(* check_text_counter's segment E (image A 0x83ce0 .. the ret at 0x83dcc; check_text_counter_A_inv.v seg_ctc_E):
   from cut C5 to cdc_post. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import check_text_counter_A_inv check_text_counter_A_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x83ce0 ----------------------------------------------------------------------------
   Atoms: 0..31 the registers at the cut (2 = sp1, 8 = the entry sp, 18 = 25 = F, 20 = seg, 24 = SB, 26 = SB + F / 8),
   32 = SB, 33 = the flag address FL, 34..46 = the entry values of ra, s0, s1, s2 .. s11 (the twelve saves).
   The loop's run (the token engine, which decides the shadow checks) starts with every write window empty: it
   writes nothing, and the engine checks shadow loads only when no window may write a shadow byte; the release's
   run (0x83d28 ..) then opens the windows of the frame's first word, its shadow and the flag byte (w = 8, 8, 1). *)
Definition c5_sg : YP09.region :=
  YP09.mkRegion (Some 20%nat) 8 24 0 0 (map (fun i => YP09.mkChunk (8 + Z.of_nat i) (CVal 1 (SLit 165))) (seq 0 16)).
Definition c5_fsh (w : Z) : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 w [].
Definition c5_fr (w : Z) : YP09.region := YP09.mkRegion (Some 25%nat) 0 64 0 w [YP09.mkChunk 56 (CVal 8 (SOff 33 0))].
Definition c5_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  (map (fun i => YP09.mkChunk (-8 - 8 * Z.of_nat i) (CVal 8 (SOff (34 + i) 0))) (seq 0 13)).
Definition c5_rs : smem := [c5_sg; c5_fsh 0; c5_fr 0; c5_sv].
Definition c5_atoms : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (25%nat, mkAF 4096 (2 ^ 47) 6);
   (26%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (33%nat, mkAF 4096 (2 ^ 47) 0)].
Definition c5_xs (regs : bvmap 5 word) (fl : Z) : list Z :=
  fl :: raZ regs :: map (fun r : bv 5 => bv_unsigned (getr regs r))
    [8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition c5_ss : sstate := mkSS CTC_C5 sr_atoms (cw_regs 0 ++ c5_rs) None (mkFacts (cw_atoms ++ c5_atoms) [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Variables SEG7TBL GLYPHA PERSA : Z.
Variable ROSTRS : list (Z * Z).

Lemma c5_xs_range : forall regs FL j, 0 <= FL < 2 ^ 64 -> (j < 14)%nat -> 0 <= nth j (c5_xs regs FL) 0 < 2 ^ 64.
Proof.
intros regs FL j HFL Hj. unfold c5_xs, raZ.
do 14 (destruct j as [|j]; [cbn [nth map]; first [exact HFL |
  lazymatch goal with |- 0 <= bv_unsigned ?x < _ =>
    let Hx := fresh in pose proof (bv_unsigned_in_range 64 x) as Hx; change (bv_modulus 64) with (2 ^ 64) in Hx; exact Hx end] |]).
lia.
Qed.
Lemma c5_start : forall ly2 S2 (W2 : world tfibsegs) (regs regs2 : bvmap 5 word) mem2 md2 sp F FL sg,
  AR tfibsegs B ly2 S2 W2 mem2 md2 ->
  getr regs2 2 = w64 (ctc_sp1 sp) -> getr regs2 8 = w64 sp -> getr regs2 20 = w64 sg ->
  getr regs2 25 = w64 F -> getr regs2 26 = w64 (SB + F / 8) ->
  2 ^ 46 + 256 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling + 256 <= sp ->
  4096 <= F -> F + 64 <= alloc_ceiling -> F mod 64 = 0 -> in_app F 64 -> off_img F 64 ->
  4096 <= FL -> FL < alloc_ceiling -> app_addr FL -> off_img FL 1 -> (FL + 1 <= F \/ F + 64 <= FL) ->
  in_app sg 24 -> off_img sg 24 ->
  (sg + 24 <= F \/ F + 64 <= sg) -> (sg + 24 <= FL \/ FL + 1 <= sg) ->
  (forall a, F <= a < F + 8 -> apresent (w_H W2) mem2 a) ->
  (forall i, 0 <= i < 8 -> apresent (w_H W2) mem2 (SB + F / 8 + i)) ->
  val_mem tfibsegs (rd W2 mem2) (F + 56) 8 FL ->
  garr8 tfibsegs (rd W2 mem2) (sg + 8) (repeat 165 16) ->
  (forall i, (i < 13)%nat -> val_mem tfibsegs (rd W2 mem2) (sp - 8 - 8 * Z.of_nat i) 8 (nth (1 + i) (c5_xs regs FL) 0)) ->
  st_ok tfibsegs (Ereg regs2 (cw_extra (c5_xs regs FL))) c5_ss
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 CTC_C5) mem2 (seg_rom tfibsegs))).
Proof.
intros ly2 S2 W2 regs regs2 mem2 md2 sp F FL sg HAR R2 R8 R20 R25 R26 Hsp Hsp16 Hspc HF0 HFc HF64 HFapp HFimg
  HL0 HLc HLapp HLimg HLF Hsgapp Hsgimg HsgF HsgL HFp HSp VFL Va5 Vsv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (xs := c5_xs regs FL) in *.
set (E := Ereg regs2 (cw_extra xs)).
assert (Hsp1 : sp - 192 <= ctc_sp1 sp <= sp - 160 /\ ctc_sp1 sp mod 32 = 0).
{ unfold ctc_sp1. pose proof (Z.mul_div_le (sp - 160) 32 ltac:(lia)) as M1.
  pose proof (Z.mul_succ_div_gt (sp - 160) 32 ltac:(lia)) as M2.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
set (sp1 := ctc_sp1 sp) in *.
assert (HF8 : F / 8 = 8 * (F / 64)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D at 1.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (HF8r : 512 <= F / 8 <= 2 ^ 44 - 8).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
assert (UB : forall (n : nat) (r : bv 5) z, Z.of_nat n = bv_unsigned r -> getr regs2 r = w64 z -> 0 <= z < 2 ^ 64 ->
  bv_unsigned (ew E n) = z).
{ intros n r z Hn Hr Hz. subst E. rewrite (cw_ew_reg regs2 xs n r Hn), Hr. unfold w64. apply unsigned_lit_small. exact Hz. }
assert (U2 : bv_unsigned (ew E 2) = sp1) by (apply (UB 2%nat 2%bv); [reflexivity | exact R2 | lia]).
assert (U8 : bv_unsigned (ew E 8) = sp) by (apply (UB 8%nat 8%bv); [reflexivity | exact R8 | lia]).
assert (Hsgb : 4096 <= sg /\ sg + 24 <= alloc_ceiling).
{ destruct Hsgapp as (Q0 & [Q1 | (Q1 & Q2)]); unfold kLowShadowBeg, ASAN_CEIL in *; lia. }
assert (U20 : bv_unsigned (ew E 20) = sg) by (apply (UB 20%nat 20%bv); [reflexivity | exact R20 | lia]).
assert (U25 : bv_unsigned (ew E 25) = F) by (apply (UB 25%nat 25%bv); [reflexivity | exact R25 | lia]).
assert (U26 : bv_unsigned (ew E 26) = SB + F / 8) by (apply (UB 26%nat 26%bv); [reflexivity | exact R26 | unfold SB; lia]).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (subst E; exact (cw_ew_x regs2 xs 0)).
assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Hsg0 : 4096 <= sg) by lia.
apply (cw_entry B TL LAWS CTC_C5 0 xs c5_rs c5_atoms ly2 S2 W2 regs2 mem2 md2 HAR (Z.le_refl 0)); fold E.
- unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
- unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia.
  destruct Hsp1 as (_ & Hm). pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hm, Z.add_0_r in D.
  rewrite D. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult.
- intros a Ha. lia.
- vm_compute. reflexivity.
- unfold c5_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, c5_sg, c5_fsh, c5_fr, c5_sv;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
    apply (chunk_ok_val tfibsegs E _ sg (8 + Z.of_nat i) 1 (SLit 165) 165); [reflexivity | zside | zside |].
    destruct (Va5 i ltac:(rewrite repeat_length; lia)) as (Hv & _).
    rewrite (nth_indep (repeat 165 16) 0 165) in Hv by (rewrite repeat_length; lia). rewrite nth_repeat in Hv.
    replace (sg + (8 + Z.of_nat i)) with (sg + 8 + Z.of_nat i) by lia. exact Hv.
  + rewrite U26. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable tfibsegs). apply HSp. lia.
  + rewrite U25. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs). apply HFp. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E _ F 56 8 (SOff 33 0) FL); [| zside | zside | exact VFL].
      cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
    pose proof (c5_xs_range regs FL (1 + i) ltac:(lia) ltac:(lia)) as Hr.
    apply (chunk_ok_val tfibsegs E _ sp (-8 - 8 * Z.of_nat i) 8 (SOff (34 + i) 0) (nth (1 + i) xs 0)).
    * cbn [sv_denot]. replace (34 + i)%nat with (33 + S i)%nat by lia. subst E. rewrite (cw_ew_x regs2 xs (S i)).
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * exact Hr.
    * zside.
    * replace (sp + (-8 - 8 * Z.of_nat i)) with (sp - 8 - 8 * Z.of_nat i) by lia. apply Vsv. lia.
- apply pairwise_disjoint_of_extents.
  unfold cw_regs, c5_rs, stack_region, got_region, bcell_region, c5_sg, c5_fsh, c5_fr, c5_sv, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U2, U8, U20, U25, U26.
  unfold A_GOT_shadow, A_shadow_glob.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, app_addr, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  repeat match goal with |- _ /\ _ => split end; lia.
- unfold c5_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U8, U20, U25, U26, U33. rewrite Z.pow_0_r, !Z.mod_1_r.
  change (2 ^ 4) with 16. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
  assert (M26 : (SB + F / 8) mod 8 = 0).
  { rewrite HF8. unfold SB. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia. apply Z_mod_mult. }
  unfold in_app, app_addr, SB in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

Local Ltac c5_sv SV j r Q := let H := fresh in pose proof (SV j r eq_refl) as H; cbn [Nat.add] in H; rewrite H in Q; clear H.
Theorem seg_ctc_E_holds : seg_ctc_E B MT SEG7TBL GLYPHA ROSTRS.
Proof.
unfold seg_ctc_E. intros g pos W2 c2 Hpre Hcut.
destruct g as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj].
unfold ctc_cut, ctc_P5, ctc_common, ctc_pre, x_sp, x_F, x_FL in *.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_q x_sg x_dt x_tb x_sj x_dj] in *.
destruct Hcut as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & Hab & Hnin & Hmo & Hio & HC & (s' & d' & Vs & Ls & Va5 & Vd & Hra8)).
destruct Hpre as (HE0 & H10 & HTB & HOq & HOsg & HOdt & H11 & HSG & HSJ & LSJ & H12 & HDT & HDJ & DJ1 & DJ2 & DJ3 & HIMG & HAG & HFR6).
pose proof HE0 as (HJc & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_counter HE0
  ltac:(unfold T_check_text_counter, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres0).
assert (TT : T_check_text_counter = 8384) by reflexivity. rewrite TT in Hceil, H46, Hpres0, Hwlo.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs2 & _).
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _).
assert (HfrsS2 : frames S2 = (0, pos) :: frames Sc) by (rewrite Hfrs2, Hfrsc; reflexivity).
destruct (ctc_frame_addr_eq B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ((0, pos) :: own) ly2 S2 W2 mem2 md2 k HJc HJ)
  as (Efa & Efl).
destruct (ctc_frame_facts B LAWS FFL ly2 S2 W2 mem2 md2 lyc Sc pos HAR HfrsS2 Efa Efl)
  as (HF0 & HFc & HF64 & HFapp & HFimg & HFp & HSp & HL0 & HLc & HLapp & HLimg & HLp & HLo & HLF).
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
pose proof HSG as (_ & _ & HSGd & _).
destruct (ctc_dst_facts B LAWS FFL ly2 S2 W2 mem2 md2 lyc Sc pos sg 24 HAR HfrsS2 Hnin Efa Efl Hab HSGd ltac:(lia))
  as (Hsgapp & Hsgimg & Hsgc & HsgF & HsgL & Hsgp).
destruct HC as (R2 & R9 & R8 & R3 & R4 & R18 & R19 & R20 & R21 & R24 & R25 & R26 &
  V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & VFLw).
change (fs_frame_bytes 0) with 64 in VFLw. replace (F + 64 - 8) with (F + 56) in VFLw by lia.
assert (Vsv : forall i, (i < 13)%nat -> val_mem tfibsegs (rd W2 mem2) (spZ regs - 8 - 8 * Z.of_nat i) 8 (nth (1 + i) (c5_xs regs FL) 0)).
{ intros i Hi. unfold c5_xs.
  do 13 (destruct i as [|i]; [cbn [nth map Nat.add];
    lazymatch goal with |- val_mem _ _ ?a 8 ?v =>
      lazymatch goal with H : val_mem _ _ ?a' 8 v |- _ => replace a with a' by lia; exact H end end |]).
  lia. }
pose proof (c5_start ly2 S2 W2 regs regs2 mem2 md2 (spZ regs) F FL sg HAR R2 R8 R20 R25 R26
  ltac:(lia) Hal16 ltac:(lia) HF0 HFc HF64 HFapp HFimg HL0 HLc HLapp HLimg HLF Hsgapp Hsgimg HsgF HsgL
  (fun a Ha => HFp a ltac:(lia)) HSp (val_mem_of_rdword tfibsegs _ _ _ _ VFLw) Va5 Vsv) as HS.
remember (Ereg regs2 (cw_extra (c5_xs regs FL))) as E eqn:HE.
assert (EE : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; rewrite HE; apply cw_ew_reg; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (rewrite HE; exact (cw_ew_x regs2 (c5_xs regs FL) 0)).
assert (E20 : ew E 20 = Z_to_bv 64 sg) by (rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 F) by (rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity).
assert (E26 : ew E 26 = Z_to_bv 64 (SB + F / 8)) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (24%bv : bv 5) (SOff 32 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, R24; reflexivity)) as HS1.
clear HS. rename HS1 into HS.
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (18%bv : bv 5) (SOff 25 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned, R18; reflexivity)) as HS1.
clear HS. rename HS1 into HS. norm_ss HS.
pose proof HSG as (_ & _ & _ & _ & _ & _ & HSGam & _).
assert (Hsg0 : 4096 <= sg) by (destruct Hsgapp as (Q & _); exact Q).
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 20 8 24] E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil]. change 24 with (8 + 16).
  apply (cw_shent_ra_off W2 mem2 E 20 sg 8 16 Hra8); [unfold amem_range in *; lia | lia | lia | lia | lia | exact E20 | exact E32]. }
unfold cfg_at. change (w64 CTC_C5) with (Z_to_bv 64 CTC_C5).
cw_keep_j0 HJ HJ0. pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
cw_run_to idtac 0x83d28.
{ unfold awr_ok. cw_kwr_ro. }
(* the loop wrote nothing: what the call keeps of its entry state carries over *)
rename ms into ms1. rename HJ into HJ1. rename HS into HS1.
lazymatch type of HFr with frame_of ?Ex ?rsx _ _ => assert (NW1 : forall a, in_wrange Ex rsx a -> False) by cw_kwr_ro end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W2) (ms_mem ms1) a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply (aview_eq_of tfibsegs). apply HFr. rewrite unsigned_lit_small by exact Ha. intros X. exact (NW1 a X). }
assert (HK1 : tcj_kept tfibsegs B T_check_text_counter lyc Sc W memc W2 (ms_mem ms1) (spZ regs)
  (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)).
{ apply (cw_kept_step B LAWS T_check_text_counter lyc Sc W memc mdc W2 mem2 (ms_mem ms1) (spZ regs) _ (fun _ => False)
    ltac:(rewrite TT; lia) HARc HK).
  - intros a Ha _. exact (KM1 a Ha).
  - intros a [].
  - intros a Hp. exact (apresent_grows _ _ _ a HG Hp). }
clear HF HFr HG.
(* open the windows of the release: the frame's shadow (region 4), the frame's first word (region 5), then the flag
   byte in front *)
pose proof HJ1 as (HAR1 & _).
destruct (ctc_frame_facts B LAWS FFL ly2 S2 W2 (ms_mem ms1) _ lyc Sc pos HAR1 HfrsS2 Efa Efl)
  as (_ & _ & _ & _ & _ & HFp1 & HSp1 & _ & _ & _ & _ & HLp1 & _ & _).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite HfrsS2; left; reflexivity).
lazymatch type of HS1 with st_ok _ ?Ex _ _ =>
  assert (X25 : ew Ex 25 = Z_to_bv 64 F) by (repeat rewrite ew_ewset_other by lia; exact E25);
  assert (X26 : ew Ex 26 = Z_to_bv 64 (SB + F / 8)) by (repeat rewrite ew_ewset_other by lia; exact E26);
  assert (X33 : ew Ex 33 = Z_to_bv 64 FL) by (repeat rewrite ew_ewset_other by lia; exact E33) end.
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (HSb : 0 <= SB + F / 8 < 2 ^ 64).
{ split; [apply Z.add_nonneg_nonneg; [unfold SB; lia | apply Z.div_pos; lia]|].
  assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia). unfold SB. lia. }
lazymatch type of HS1 with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx 4 _ HS1 eq_refl) as RG4;
  pose proof (st_ok_region_nth Ex ssx msx 5 _ HS1 eq_refl) as RG5 end.
lazymatch type of RG4 with region_ok _ ?Ex ?mx ?r =>
  pose proof (region_ok_rewindow tfibsegs Ex mx r 0 8 RG4
    ltac:(cbn [YP09.r_base base_val]; rewrite X26, unsigned_lit_small by exact HSb; intros o Ho;
          apply (apresent_writable tfibsegs); apply HSp1; lia)) as RG4' end.
lazymatch type of RG5 with region_ok _ ?Ex ?mx ?r =>
  pose proof (region_ok_rewindow tfibsegs Ex mx r 0 8 RG5
    ltac:(cbn [YP09.r_base base_val]; rewrite X25, unsigned_lit_small by exact HFb; intros o Ho;
          apply (apresent_writable tfibsegs); apply HFp1; lia)) as RG5' end.
lazymatch type of HS1 with st_ok _ ?Ex ?ssx ?msx => lazymatch type of RG4' with region_ok _ _ _ ?r' =>
  pose proof (ast_ok_set_region tfibsegs Ex ssx msx 4 _ r' HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity) RG4') as HS2 end end.
clear HS1. norm_ss HS2.
lazymatch type of HS2 with st_ok _ ?Ex ?ssx ?msx => lazymatch type of RG5' with region_ok _ _ _ ?r' =>
  pose proof (ast_ok_set_region tfibsegs Ex ssx msx 5 _ r' HS2 eq_refl eq_refl ltac:(vm_compute; reflexivity) RG5') as HS3 end end.
clear HS2. norm_ss HS3.
assert (HF8b : F / 8 + 8 <= 2 ^ 44) by (assert (F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; lia); lia).
assert (Hsp1r : spZ regs - 192 <= ctc_sp1 (spZ regs) <= spZ regs - 160).
{ unfold ctc_sp1. pose proof (Z.mul_div_le (spZ regs - 160) 32 ltac:(lia)).
  pose proof (Z.mul_succ_div_gt (spZ regs - 160) 32 ltac:(lia)). lia. }
assert (X33f : forall Ex, ew Ex 33 = Z_to_bv 64 FL -> ew Ex 33 = Z_to_bv 64 (flag_addr ly2 0 pos))
  by (intros Ex H; rewrite Efl; exact H).
lazymatch type of HS3 with st_ok _ ?Ex ?ssx ?msx =>
  assert (RFL : region_ok tfibsegs Ex (ms_mem msx) (cw_flag_region 33))
    by (eapply cw_flag_region_ok; [exact FFL | exact HAR1 | exact Hin2 | apply X33f; exact X33]);
  assert (DFL : all_disjoint Ex (cw_flag_region 33) (ss_mem ssx));
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, cw_flag_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    repeat rewrite ew_ewset_other by lia;
    rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), E20, E25, E26, E33, R2, R8;
    unfold w64; rewrite (unsigned_lit_small FL), (unsigned_lit_small sg), (unsigned_lit_small F), (unsigned_lit_small (SB + F / 8)),
      (unsigned_lit_small (spZ regs)), (unsigned_lit_small (ctc_sp1 (spZ regs))) by (unfold ctc_sp1 in *; lia);
    unfold A_GOT_shadow, A_shadow_glob, ctc_sp1, app_addr, off_img, in_app, YImgTop.IMG_LO, YImgTop.IMG_TOP,
      kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *;
    repeat match goal with |- _ /\ _ => split end; lia
  | pose proof (ast_ok_add_region tfibsegs Ex ssx msx (cw_flag_region 33) HS3 ltac:(vm_compute; reflexivity) RFL DFL) as HS4 ] end.
clear HS3. norm_ss HS4.
(* the release: 0x83d28 .. ret, the frame's shadow byte 4 := f8, F[0] := 0x45e0360e, the shadow := f5 x 8, the
   flag byte := 0 through the word at F + 56, the epilogue *)
lazymatch type of HS4 with st_ok _ ?Ex _ _ =>
  assert (Ufr : bv_unsigned (ew Ex 25) = frame_addr ly2 0 pos)
    by (repeat rewrite ew_ewset_other by lia; rewrite E25, Efa; apply unsigned_lit_small; exact HFb);
  assert (Ush : bv_unsigned (ew Ex 26) = shadow_addr (frame_addr ly2 0 pos))
    by (repeat rewrite ew_ewset_other by lia; rewrite E26, Efa; unfold shadow_addr; rewrite <- SB_SHADOW_OFF;
        apply unsigned_lit_small; exact HSb);
  assert (Ufl : bv_unsigned (ew Ex 33) = flag_addr ly2 0 pos)
    by (repeat rewrite ew_ewset_other by lia; rewrite E33, Efl; apply unsigned_lit_small; lia) end.
aj_run_flag_sh tfibtbl_lib_ok HS4 HJ1.
- lia.
- cbn [ss_mem]. apply (cw_awrf_flag_front _ (cw_flag_region 33) _ _ _ _ _ _ _ _ 33%nat (flag_addr ly2 0 pos) eq_refl Ufl);
    [cbn; lia | cbn; lia |].
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 0 pos 26%nat); [reflexivity | exact Ush | left; reflexivity | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |]
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 0 pos 25%nat); [reflexivity | exact Ufr | left; reflexivity | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |] ].
- flag0 E33 (Efl 0 pos).
- (* what the release wrote: the flag byte, the frame's shadow, the frame's first word *)
  lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    assert (XW : forall a, in_wrange Ex rsx a ->
      a = flag_addr ly2 0 pos \/ in_zr a (shadow_addr (frame_addr ly2 0 pos), fs_frame_bytes 0 / 8) \/
      in_zr a (frame_rng ly2 (0, pos))) end.
  { intros y (r & Hr & Hy); cbv beta in *.
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
    unfold frame_rng, in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64.
    repeat (destruct Hr as [<- | Hr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hy; rewrite ?Ufl, ?Ush, ?Ufr in Hy; lia | ]).
    destruct Hr. }
  assert (HK2 : tcj_kept tfibsegs B T_check_text_counter lyc Sc W memc W2 (ms_mem ms) (spZ regs)
    (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1)).
  { lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    apply (cw_kept_step B LAWS T_check_text_counter lyc Sc W memc mdc W2 (ms_mem ms1) (ms_mem ms) (spZ regs) _
      (in_wrange Ex rsx) ltac:(rewrite TT; lia) HARc HK1) end.
    - intros x Hx Hn. apply (aview_eq_of tfibsegs). apply HFr. rewrite unsigned_lit_small by exact Hx. exact Hn.
    - intros x Hx. right. right.
      apply (cw_fresh_frame B LAWS FFL ly2 S2 W2 (ms_mem ms1) _ lyc Sc 0 pos x HAR1 HfrsS2).
      + intros b m. split; intros Hin; [exact (Permutation_in _ Hab Hin) | exact (Permutation_in _ (Permutation_sym Hab) Hin)].
      + exact Efa.
      + destruct (XW x Hx) as [Hy | [Hy | Hy]]; [right; right; exact Hy | right; left; exact Hy | left; exact Hy].
    - intros x Hp. exact (apresent_grows _ _ _ x HG Hp). }
  (* the bytes of seg and dots: no window of either run *)
  pose proof HDT as (_ & _ & HDTd & _).
  destruct (ctc_dst_facts B LAWS FFL ly2 S2 W2 mem2 md2 lyc Sc pos dt 1 HAR HfrsS2 Hnin Efa Efl Hab HDTd ltac:(lia))
    as (Hdtapp & Hdtimg & Hdtc & HdtF & HdtL & _).
  assert (Hdt0 : 4096 <= dt) by (destruct Hdtapp as (Q & _); exact Q).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF8p : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (KO : forall x, (sg <= x < sg + 24 \/ dt <= x < dt + 1) ->
    mbyte tfibsegs (rd W2 (ms_mem ms)) x = mbyte tfibsegs (rd W2 mem2) x).
  { intros x Hx. apply (mbyte_of_aview tfibsegs).
    assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx Hsg0 Hsgc Hdt0 Hdtc C1; lia).
    rewrite <- (KM1 x Hx64). apply (aview_eq_of tfibsegs). apply HFr. rewrite unsigned_lit_small by exact Hx64.
    intros Hw. destruct (XW x Hw) as [Hy | [Hy | Hy]];
    unfold frame_rng, in_zr, shadow_addr in Hy; cbn [fst snd] in Hy; rewrite ?Efa, ?Efl in Hy;
    change (fs_frame_bytes 0 / 8) with 8 in Hy; change (fs_frame_bytes 0) with 64 in Hy; fold F FL in Hy.
    - clear - Hx Hy HsgL HdtL. lia.
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Hsgapp, Hdtapp, Hy.
      clear - Hx Hy Hsgapp Hdtapp HF8b HF8p. lia.
    - clear - Hx Hy HsgF HdtF. lia. }
  (* the registers at the ret: the saves, sp from s0, gp and tp untouched *)
  assert (SV : forall (j : nat) (r : bv 5), nth (1 + j) (c5_xs regs FL) 0 = bv_unsigned (getr regs r) ->
    ew E (34 + j) = getr regs r).
  { intros j r Hn. rewrite HE. replace (34 + j)%nat with (33 + (1 + j))%nat by lia. rewrite cw_ew_x, Hn.
    apply Z_to_bv_bv_unsigned. }
  rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
  rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
  rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23.
  rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
  c5_sv SV 0%nat (1%bv : bv 5) Q1. c5_sv SV 1%nat (8%bv : bv 5) Q8. c5_sv SV 2%nat (9%bv : bv 5) Q9. c5_sv SV 3%nat (18%bv : bv 5) Q18.
  c5_sv SV 4%nat (19%bv : bv 5) Q19. c5_sv SV 5%nat (20%bv : bv 5) Q20. c5_sv SV 6%nat (21%bv : bv 5) Q21. c5_sv SV 7%nat (22%bv : bv 5) Q22.
  c5_sv SV 8%nat (23%bv : bv 5) Q23. c5_sv SV 9%nat (24%bv : bv 5) Q24. c5_sv SV 10%nat (25%bv : bv 5) Q25. c5_sv SV 11%nat (26%bv : bv 5) Q26.
  c5_sv SV 12%nat (27%bv : bv 5) Q27.
  rewrite (EE 8%nat 8%bv eq_refl), R8 in Q2. unfold w64, spZ in Q2. rewrite Z_to_bv_bv_unsigned in Q2.
  rewrite (EE 3%nat 3%bv eq_refl), R3 in Q3. rewrite (EE 4%nat 4%bv eq_refl), R4 in Q4.
  destruct (cw_release_post MT MTF tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 (ms_mem ms) _ k 0 pos
    HJc HJ1 Hab Hmo) as (Hfr3 & Hperm3 & Hmo3).
  eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W2 _ _ _ _ _ HS4 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat1. unfold ctc_post, cdc_post. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc
    x_mdc x_k x_regs x_q x_sg x_dt x_tb x_sj x_dj ctc_E ctc_R].
  exists ly2, (stack_free_state 0 pos S2), (ms_regs ms), (ms_mem ms). eexists.
  split; [rewrite Q1, Hra; reflexivity|].
  split; [unfold EV_CDC; rewrite Z.add_0_r; apply (ajournal_materialize tfibsegs B LAWS tfib_segs_low); exact HJ1|].
  split; [apply aregs_preserved_eqs; assumption|].
  split; [exact Hfr3|]. split; [exact Hperm3|].
  split; [cw_io|]. split; [exact Hmo3|]. split; [exact HK2|].
  exists s', d'. split; [|split; [exact Ls|]].
  + apply (garr8_frame tfibsegs (rd W2 mem2)); [apply garr8_app; split; [exact Vs | rewrite Ls; exact Va5]|].
    intros x Hx. rewrite length_app, repeat_length, Ls in Hx. apply KO. left. cbn [x_sg] in Hx. lia.
  + intros kk Hkk. cbn [x_dt] in *. rewrite (KO (dt + Z.of_nat kk) ltac:(right; lia)). exact (Vd kk Hkk).
Qed.
End d.
End b.
