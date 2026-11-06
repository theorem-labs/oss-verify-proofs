(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh0.v:234-238 [Apache-2.0];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159. *)
(* sb_dec (fuzz_identity.asan-ubsan 0x835d0, listing offset AF_sb_dec = 0x2e5c), SEGMENT A: the prologue,
   the class-0 side-stack frame and the state at the cut BASE + 0x2f80 (0x836f4), in the
   continuation-passing form sbd_segA_spec.  Segment B (lib/B/Prog/SbDecSegB.v) consumes
   the exit predicate sbd_at1 this segment produces; segment C (lib/B/Prog/SbDecSegC.v) ends in
   tsb_dec_post.  The three segments chain into Theorem pb_sb_dec : tsb_dec_spec.
   The code this segment walks, from the neutral listing:
   - 0x835d0 addi sp,sp,-128, the probe store at sp0-128 and the twelve saves ra, s0 .. s10 at
     sp0-8 .. sp0-96;
   - 0x8360c andi sp,sp,-32: the 32-byte realignment, a fresh atom 60 = 32 * ((sp0 - 128) / 32)
     (the symbolic step is cgif's, lib/A/ACja.v:93-118);
   - 0x83638 the use-after-return flag test (the cell holds 1, AR_const_law: not taken), 0x83640 the
     class-0 side-stack frame allocation (64 bytes, flag word at F + 56, shadow [SHADOW_OFF + F/8, +8)
     zero after the call), and 0x83654 bnez taken: the allocation returns a frame, so the real-stack
     fallback 0x83658 .. 0x83670 is not reached;
   - 0x83674 .. 0x836f0: s2 = s7 = F, the frame's first three words, s8 := SHADOW_OFF + F/8,
     s9 := F + 32, s10 := ~(F + 32), the frame's shadow F1 F1 F1 F1 04 F3 F3 F3 (byte 4 = 04: the
     digit slot [F + 32, F + 36) is addressable) and the loop constants of segment B.
   The allocator event count and the live heap bytes do not change here: a class-0 stack frame counts no
   event (YG00.v:570-579) and adds no heap block. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ IdentBProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC1g YC1h YC45 YC85 IdentBFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC81 YC4b.
(* the callee's contract and the function's own contract (statement file) *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
(* the frozen cut predicate sbd_at1 *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import SbDecSegB.
(* The plain model of sb_dec (released): sb_dec_room / sb_dec_acc / sb_dec_D *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
(* The segment's contract: tsb_dec_spec's premises, in its order, and the cut BASE + 0x2f80 in the
   continuation form.  sbd_at1 is the frozen predicate of lib/B/Prog/SbDecSegB.v. *)
Definition sbd_segA_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b v md p cap n ov : Z)
    (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SB_DEC_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 b -> getr regs 11 = w64 v -> getr regs 12 = w64 md ->
  0 <= v < 2 ^ 31 -> (md = 1 \/ md = 2) ->
  b mod 8 = 0 -> 0 <= b -> b + 28 <= 2 ^ 63 -> (spZ regs <= b \/ b + 28 <= spZ regs - SB_DEC_STK) ->
  tsb_dec_rec_at lyc b ->
  val_mem SEGS (mrestrict (w_H W) memc) b 8 p -> val_mem SEGS (mrestrict (w_H W) memc) (b + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + 16) 8 n -> val_mem SEGS (mrestrict (w_H W) memc) (b + 24) 4 ov ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n -> n + 4 < 2 ^ 64 -> 0 <= ov < 2 ^ 32 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + 16) 12 ->
  (0 < sb_dec_c.sb_dec_room cap n ->
     0 < p /\ p + cap <= 2 ^ 63 /\
     tdst_ok B lyc Sc (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + n) (sb_dec_c.sb_dec_acc v md cap n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= b \/ b + 28 <= p + n) /\
     (p + n + sb_dec_c.sb_dec_acc v md cap n <= spZ regs - SB_DEC_STK \/ spZ regs <= p + n)) ->
  Z.of_nat (length (frames Sc)) <= 8 ->
  st_nev Sc + EV_SB_DEC <= EV_MAX -> blocks_bytes Sc + LIVE_SB_DEC <= LIVE_MAX ->
  (forall fpos S2 s1v (regs1 : bvmap 5 word) mem1 md1,
     sbd_at1 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b v md p cap n ov fpos S2 s1v regs1 mem1 md1 ->
     SRr SEGS W (cfg_at SEGS (BASE + 0x2f80) regs1 mem1 md1) Q) ->
  SRr SEGS W (cfg_at SEGS A_sb_dec regs memc mdc) Q.
(* ---- the walk ---------------------------------------------------------------------------------- *)
Section walk.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis PSIG : identb_prog_sig_ok.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* The entry symbolic state: the 128-byte stack frame the prologue writes, the two GOT slots and the two
   runtime cells the prologue reads (the shadow base and the use-after-return flag).  Atom 32 holds
   SHADOW_OFF, atom 33 the address of the use-after-return cell. *)
Definition sbd_ss0 : sstate := mkSS AF_sb_dec sr_atoms
  [stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (33%nat, mkAF IMG_LO IMG_TOP 2)] [] []).
Ltac sbd_nss HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss3 ?d =>
  let v := eval vm_compute in ss3 in change (st_ok_pi a b c v d) in HS end.
(* sp after 0x8360c andi sp,sp,-32 (the 32-byte realignment). *)
Lemma sbd_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma sbd_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite sbd_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sbd_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Theorem sbd_segA : sbd_segA_spec.
Proof.
unfold sbd_segA_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b v md p cap n ov Q
  HJc Hra0 Hra4 Hgp Htp Hal16 Hwlo Hwhi G10 G11 G12 Hv Hmd Hb8 Hb0 Hb63 Hbwin Hrec Vp Vcap Vn Vov
  Rp Rcap Rn0 Rn4 Rov HWRb HROOM Hfr8 Hev Hlive HCONT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SB_DEC_STK = 4256) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & F1c & F2c & F3c & F4c & _ & Hpresc & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 31 ltac:(lia)) as Hob31.
pose proof (pa_val_range (A_OBJ 0)) as VO0. pose proof (pa_val_range (A_OBJ 1)) as VO1.
pose proof (pa_val_range (A_OBJ 31)) as VO31.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
(* the layout of the call state has the same machine stack as the entry layout *)
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
assert (Hsplo : 2 ^ 46 <= spZ regs) by (clear - C1 Hceil Hslo Hwlo HSTK Hes; lia).
assert (Hsphi : spZ regs <= 2 ^ 47) by (clear - Hshi Hwhi H47; lia).
assert (Hacsp : alloc_ceiling <= spZ regs - SB_DEC_STK) by (clear - Hceil Hslo Hwlo; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r) by (intros k0 r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)]) E)
  by (subst E; split; [intros k0 Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n0 v0, ew E n0 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n0) = v0).
{ intros n0 v0 Hn0 Hv0. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv0. }
assert (UO0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite EO0; apply unsigned_lit_small; clear - VO0; lia).
assert (UO1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (rewrite EO1; apply unsigned_lit_small; clear - VO1; lia).
assert (UO31 : bv_unsigned (ew E (A_OBJ 31)) = VAL (A_OBJ 31)) by (rewrite EO31; apply unsigned_lit_small; clear - VO31; lia).
assert (U33 : bv_unsigned (ew E 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; clear - Huar; lia).
(* ---- the entry state ----------------------------------------------------------------------------- *)
assert (A2 : afact_ok E 2 (mkAF (2 ^ 46) (2 ^ 47) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
  split; [clear - Hsplo Hsphi; lia|]. split; [exact Hal16 | clear; lia]. }
assert (A33 : afact_ok E 33 (mkAF IMG_LO IMG_TOP 2)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33. change (2 ^ 2) with 4.
  split; [clear - Huar; lia|]. split; [exact Huar4 | clear; lia]. }
assert (RO_stk : region_ok SEGS E (mrestrict (w_H W) memc) (stack_region 128)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [clear - Hsplo; lia|]. split; [clear - Hsphi; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpresc. clear - Ho Hwlo Hwhi HSTK Hes; lia. }
assert (RO_got : region_ok SEGS E (mrestrict (w_H W) memc) got_regionP).
{ unfold region_ok, got_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UO1. split; [clear - VO1; lia|]. split; [clear - VO1 Hob1; lia|]. split; [intros o Ho; clear - Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
  [cbn [sv_denot]; rewrite EO31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - VO31; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot). }
assert (RO_cell : region_ok SEGS E (mrestrict (w_H W) memc) (bcell_regionP 32)).
{ unfold region_ok, bcell_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UO31. split; [clear - VO31; lia|]. split; [clear - VO31 Hob31; lia|]. split; [intros o Ho; clear - Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SOff 32 0) SHADOW_OFF);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell). }
assert (RO_uarg : region_ok SEGS E (mrestrict (w_H W) memc) (uar_got_regionP 33)).
{ unfold region_ok, uar_got_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UO0. split; [clear - VO0; lia|]. split; [clear - VO0 Hob0; lia|]. split; [intros o Ho; clear - Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Huar; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar). }
assert (RO_uarc : region_ok SEGS E (mrestrict (w_H W) memc) (uar_cell_regionP 33)).
{ unfold region_ok, uar_cell_regionP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U33. split; [clear - Huar; lia|]. split; [clear - Huar; lia|]. split; [intros o Ho; clear - Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
  [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar). }
assert (HS : st_ok_pi SEGS VAL E sbd_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sb_dec)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold sbd_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    first [exact RO_stk | exact RO_got | exact RO_cell | exact RO_uarg | exact RO_uarc].
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, UO1, UO31, UO0, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - Hsplo Hsphi Hsep Huar VO0 VO1 VO31 Hob0 Hob1 Hob31. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    repeat match goal with |- _ /\ _ => split end; first [exact A2 | exact A33 | exact I]. }
clear HE RO_stk RO_got RO_cell RO_uarg RO_uarc.
unfold cfg_at. change (w64 (BASE + AF_sb_dec)) with (Z_to_bv 64 (BASE + AF_sb_dec)).
time "runto" paj_run_to_sh RUNTOP HS HJc 0x2e9c.
{ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [ reflexivity
  | transitivity (spZ regs); [exact Usp | clear; lia]
  | cbn [YP09.r_wlo]; clear - Hwlo Hwhi HSTK Hes; lia
  | cbn [YP09.r_whi]; clear - Hwhi; lia
  | ];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|]);
  apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG.
pose proof HFr as HFr1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw.
  apply (kept_of_frame E (ss_mem sbd_ss0) (w_H W) memc (ms_mem ms)
    (fun x => spZ regs - 128 <= x < spZ regs) HFr1); [| exact Ha | exact Hw].
  intros bb wlo whi aa Hin Hr. unfold sbd_ss0 in Hin.
  cbn [ss_mem windows map stack_region got_regionP bcell_regionP uar_got_regionP uar_cell_regionP
       YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | [Eq | [Eq | [Eq | []]]]]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; rewrite ?Usp in Hr; clear - Hr; lia. }
assert (GROW1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms))) by exact HG.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
clear HF HFr HG HFr1.
(* 0x8360c andi sp,sp,-32: s1 = 32 * ((sp0 - 128) / 32), a fresh atom 60, 32-aligned. *)
set (s1v := 32 * ((spZ regs + -128) / 32)).
destruct (sbd_sp1_facts (spZ regs + -128) ltac:(clear - Hsplo; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hs1r & Hs1al & Hs1al16).
fold s1v in Hs1r, Hs1al, Hs1al16.
assert (Hs1 : spZ regs - 144 <= s1v <= spZ regs - 128) by (clear - Hs1r; lia). clear Hs1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_restrict_reg (w_H W) Ev ssx msx (2%bv : bv 5) HS) as R2;
  change (sr_get (ss_regs ssx) (2%bv : bv 5)) with (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) in R2;
  rewrite (sbd_denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned) ltac:(clear - Hsplo; lia) ltac:(clear - Hsphi; lia) ltac:(clear - Hsplo Hsphi; lia)) in R2;
  fold s1v in R2;
  pose proof (st_ok_pi_havoc_hi 60 Ev ssx (restrict (w_H W) msx) [Z_to_bv 64 s1v] HS ltac:(vm_compute; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
set (E1 := havoc E 60 [Z_to_bv 64 s1v]) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (AG1 : forall n0, (n0 < 60)%nat -> ew E1 n0 = ew E n0) by (intros n0 Hn0; apply ew_havoc_old; exact Hn0).
assert (AG1' : forall n0, (61 <= n0)%nat -> ew E1 n0 = ew E n0) by (intros n0 Hn0; apply ew_havoc_above; cbn; lia).
assert (E60 : ew E1 60 = Z_to_bv 64 s1v) by exact (ew_havoc_new E 60 [Z_to_bv 64 s1v] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp E1 ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hs1 Hsplo Hsphi; lia); reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact E1 ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by (clear - Hs1 Hsplo Hsphi; lia); change (2 ^ 5) with 32; clear - Hs1 Hsplo Hsphi Hs1al; lia)) as HS3
end.
clear HS. rename HS3 into HS. sbd_nss HS.
assert (VB1 : forall n0 v0, n0 <> 60%nat -> ew E n0 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E1 (Some n0) = v0).
{ intros n0 v0 Hne Hn0 Hv0. cbn [base_val]. destruct (Nat.lt_ge_cases n0 60) as [Hl | Hl].
  - rewrite (AG1 n0 Hl), Hn0. apply unsigned_lit_small. exact Hv0.
  - rewrite (AG1' n0 ltac:(clear - Hne Hl; lia)), Hn0. apply unsigned_lit_small. exact Hv0. }
assert (B60 : base_val E1 (Some 60%nat) = s1v) by (cbn [base_val]; rewrite E60; apply unsigned_lit_small; clear - Hs1 Hsplo Hsphi; lia).
assert (B2 : base_val E1 (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite (AG1 2%nat ltac:(lia)); exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let rs := eval cbn [ss_mem] in (ss_mem ssx) in
  lazymatch rs with ?r0 :: ?rest =>
  pose proof (st_ok_pi_submem E1 ssx (restrict (w_H W) msx) (trim_lo r0 (-96) :: rest) HS
    ltac:(cbn [ss_mem]; apply submem_keep; [apply subregion_trim_lo | apply submem_refl]) ltac:(vm_compute; reflexivity)) as HS3 end
end.
clear HS. rename HS3 into HS. sbd_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  assert (HD : all_disjoint E1 (YP09.mkRegion (Some 60%nat) 24 32 24 32 []) (ss_mem ssx)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi extent_of_region].
  rewrite B60, B2, (VB1 242%nat (VAL (A_OBJ 1)) ltac:(lia) EO1 ltac:(clear - VO1; lia)),
    (VB1 272%nat (VAL (A_OBJ 31)) ltac:(lia) EO31 ltac:(clear - VO31; lia)),
    (VB1 241%nat (VAL (A_OBJ 0)) ltac:(lia) EO0 ltac:(clear - VO0; lia)),
    (VB1 33%nat (as_uar_cell B) ltac:(lia) E33 ltac:(clear - Huar; lia)).
  clear - Hs1 Hsplo Hsphi Huar Hob0 Hob1 Hob31. time "hd" (repeat split; lia). }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_add_region E1 ssx (restrict (w_H W) msx) (YP09.mkRegion (Some 60%nat) 24 32 24 32 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst]; rewrite B60;
          split; [clear - Hs1 Hsplo; lia|]; split; [clear - Hs1 Hsphi; lia|]; split; [|constructor];
          intros o Ho; apply (apresent_writable SEGS); apply Hpres1; clear - Ho Hs1 Hwlo Hwhi HSTK Hes; lia) HD) as HS3
end.
clear HS. rename HS3 into HS. time "nss3" sbd_nss HS.
time "runshc" paj_run_shc RUNP RUNC HS HJc.
{ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (s1v - sp0));
  [ reflexivity
  | transitivity s1v; [exact B60 | clear; lia]
  | cbn [YP09.r_wlo]; clear - Hs1 Hwlo Hwhi HSTK Hes; lia
  | cbn [YP09.r_whi]; clear - Hs1 Hwhi; lia
  | ];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [ reflexivity
  | transitivity (spZ regs); [exact B2 | clear; lia]
  | cbn [YP09.r_wlo]; clear - Hwlo Hwhi HSTK Hes; lia
  | cbn [YP09.r_whi]; clear - Hwhi; lia
  | ];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|]);
  apply awr_ok_nil. }
pose proof HFr as HFr2.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hw.
  apply (kept_of_frame E1 _ (w_H W) (ms_mem ms) (ms_mem ms0)
    (fun x => spZ regs - SB_DEC_STK <= x < spZ regs) HFr2); [| exact Ha | exact Hw].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; rewrite ?B60, ?B2 in Hr;
    cbn [base_val] in Hr; clear - Hr Hs1 HSTK Hes; lia|]); destruct Hin. }
assert (KEEPpre : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw. rewrite (KEEP2 a Ha Hw). apply KEEP1; [exact Ha | clear - Hw HSTK Hes; lia]. }
assert (GROWpre : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)))
  by (eapply mem_grows_trans; [exact GROW1 | exact HG]).
clear HF HFr HG HFr2 KEEP1 KEEP2 GROW1.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
rewrite E60 in Rsp. rewrite (AG1 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Hgp in Rgp.
rewrite (AG1 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Htp in Rtp.
pmkst HS. rewrite (palf_sm0 B TLF).
pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (s1v - sp0) _ HJc) end.
  - unfold spZ at 1. rewrite Rsp, unsigned_lit_small by (clear - Hs1 Hsplo Hsphi; lia). clear; lia.
  - rewrite Zminus_mod, Hs1al16, Hsp0al. reflexivity.
  - clear - Hs1 Hwhi; lia.
  - rewrite Hes. clear - Hs1 Hwlo Hwhi HSTK Hes; lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [clear - Hra4; lia | reflexivity].
  - change (fs_frames 0) with 16384. clear - Hcnt Hfr8; lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
pose proof HK as (HKhi & HKblk & HKimg & HKfrm & HKpres & _).
let K := run_K_hi HS in idtac "K" K.
time "jak" (let K := run_K_hi HS in jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2).
lazymatch type of HS2 with ?Q0 -> _ => assert (HQ : Q0) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite B60; intros a Ha.
    + time "mb1" (apply (mbyte_of_aview SEGS); apply (proj1 HK); clear - Ha Hs1 Hes Hacsp Hsphi HSTK; lia).
    + time "pw1" (intros _; apply (apresent_writable SEGS); apply HJpres2; clear - Ha Hs1 Hwlo Hwhi HSTK Hes; lia).
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite B2; intros a Ha.
    + apply (mbyte_of_aview SEGS); apply (proj1 HK); clear - Ha Hs1 Hes Hacsp Hsphi HSTK; lia.
    + intros _. apply (apresent_writable SEGS). apply HJpres2. clear - Ha Hwlo Hwhi HSTK Hes; lia. }
time "jafter" specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
(* The class-0 frame the call returned, and its shadow. *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFa0 HFapp] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as HFimg.
destruct (frame_al64 SEGS B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng & HFLnum).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); clear - HF64 H; lia).
assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; clear - HF4096; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
assert (HFq8 : 8 * (F / 8) <= F < 8 * (F / 8) + 8)
  by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); clear - H H0; lia).
assert (HF8mod : F mod 8 = 0) by (rewrite HFq at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z_mod_mult).
time "setE2" set (E2v := havoc E1 512 (map (getr regs2) CLOB)) in HS.
assert (HEI2 : img_env VAL A_LIM E2v) by (apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (AG2 : forall n0, (n0 < 512)%nat -> ew E2v n0 = ew E1 n0) by (intros n0 Hn0; apply ew_havoc_old; exact Hn0).
assert (E516 : ew E2v 516 = Z_to_bv 64 F).
{ transitivity (getr regs2 (10%bv : bv 5));
  [exact (ew_havoc_new E1 512 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)) | rewrite Ha0; reflexivity]. }
time "hav528" (lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 E2v ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3
end).
clear HS. rename HS3 into HS.
time "setE3" set (E3v := havoc E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)]) in HS.
assert (HEI3 : img_env VAL A_LIM E3v) by (apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (AG3 : forall n0, (n0 < 528)%nat -> ew E3v n0 = ew E2v n0) by (intros n0 Hn0; apply ew_havoc_old; exact Hn0).
assert (E528 : ew E3v 528 = Z_to_bv 64 FL)
  by exact (ew_havoc_new E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E529 : ew E3v 529 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by exact (ew_havoc_new E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E32' : ew E3v 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (AG3 32%nat ltac:(lia)), (AG2 32%nat ltac:(lia)), (AG1 32%nat ltac:(lia)); exact E32).
assert (E516' : ew E3v 516 = Z_to_bv 64 F) by (rewrite (AG3 516%nat ltac:(lia)); exact E516).
assert (RF3 : bv_unsigned (ew E3v 516) = F) by (rewrite E516'; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
time "af516" (lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 516 (HPTR 6) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF3; change (2 ^ 6) with 64; clear - HF4096 HFceil C1 HF64; lia)) as HS3 end).
clear HS. rename HS3 into HS. sbd_nss HS.
time "af528" (lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 528 (HPTR 0) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528;
          rewrite (unsigned_lit_small FL) by (clear - HFLnum C1; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - HFLnum C1; lia)) as HS3 end).
clear HS. rename HS3 into HS. sbd_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 529 (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 17592186044416) 3) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SHADOW_OFF; clear - HF8lo HF8hi; lia); change (2 ^ 3) with 8; unfold SHADOW_OFF;
          split; [clear - HF8lo HF8hi; lia|]; split; [rewrite HF8; replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia; apply Z_mod_mult | clear; lia])) as HS3 end.
clear HS. rename HS3 into HS. sbd_nss HS.
time "alias" (lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_alias E3v ssv msv _ _ HS (shadow_decl_ok E3v 516 32 529 F SHADOW_OFF
    ltac:(rewrite <- RF3; symmetry; apply Z_to_bv_bv_unsigned) ltac:(clear - HF4096 HFceil C1; lia) E32' E529)) as HS3 end).
clear HS. rename HS3 into HS. time "nss6" sbd_nss HS.
(* The frame's 64 bytes (with the flag slot at F + 56) and its 8 shadow bytes, all zero after the allocation. *)
assert (B516 : base_val E3v (Some 516%nat) = F) by (cbn [base_val]; exact RF3).
assert (B529 : base_val E3v (Some 529%nat) = SHADOW_OFF + F / 8)
  by (cbn [base_val]; rewrite E529; apply unsigned_lit_small; unfold SHADOW_OFF; clear - HF8lo HF8hi; lia).
assert (B528 : base_val E3v (Some 528%nat) = FL)
  by (cbn [base_val]; rewrite E528; apply unsigned_lit_small; clear - HFLnum C1; lia).
assert (B2' : base_val E3v (Some 2%nat) = spZ regs)
  by (cbn [base_val]; rewrite (AG3 2%nat ltac:(lia)), (AG2 2%nat ltac:(lia)), (AG1 2%nat ltac:(lia)); exact Usp).
assert (B60' : base_val E3v (Some 60%nat) = s1v)
  by (cbn [base_val]; rewrite (AG3 60%nat ltac:(lia)), (AG2 60%nat ltac:(lia)), E60;
      apply unsigned_lit_small; clear - Hs1 Hsplo Hsphi; lia).
assert (ZS8 : val_mem SEGS (mrestrict (w_H W) mem2) (SHADOW_OFF + F / 8) 8 0).
{ apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz.
  replace (SHADOW_OFF + F / 8 + ii) with (SHADOW_OFF + F / 8 + ii) by reflexivity.
  apply Hz. change (64 / 8) with 8. clear - Hii; lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv _ =>
  assert (HDF : all_disjoint E3v (fframe_region 516 528 0 []) (ss_mem ssv)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, fframe_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite B516, B2', B60'. change (fs_frame_bytes 0) with 64.
  clear - HF4096 HFceil HFhigh Hs1 Hsplo Hsphi C1 Hacsp HSTK Hes.
  repeat split; lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv (restrict _ ?msv) =>
  pose proof (st_ok_pi_add_region E3v ssv (restrict (w_H W) msv) (fframe_region 516 528 0 []) HS eq_refl
    ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
          rewrite B516; change (fs_frame_bytes 0) with 64;
          split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFpres (F + o) ltac:(clear - Ho; lia)))
          | apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val SEGS E3v _ F 56 8 _ FL);
            [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | clear - HFLnum C1; zside | zside
            | replace (F + 56) with (F + 64 - 8) by (clear; lia); exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ]) HDF) as HS3
end.
clear HS. rename HS3 into HS. sbd_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv _ =>
  assert (HDS : all_disjoint E3v (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) (ss_mem ssv)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, fframe_region, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite B529, B516, B2', B60'. change (fs_frame_bytes 0 / 8) with 8. change (fs_frame_bytes 0) with 64.
  clear - HF4096 HFceil HFhigh HF8lo HF8hi HFapp HFq8 Hs1 Hsplo Hsphi C1 Hacsp HSTK Hes.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as [HFa | [HFa HFa2]].
  all: unfold SHADOW_OFF; repeat split; first [exact I | left; lia | right; lia]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv (restrict _ ?msv) =>
  pose proof (st_ok_pi_add_region E3v ssv (restrict (w_H W) msv) (fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
    ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
          rewrite B529; change (fs_frame_bytes 0 / 8) with 8;
          split; [clear - HF8lo; unfold SHADOW_OFF; lia|]; split; [clear - HF8hi; unfold SHADOW_OFF; lia|]; split;
          [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres;
            exact (proj1 (HFSpres o ltac:(change (64 / 8) with 8; clear - Ho; lia)))
          | apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val SEGS E3v _ (SHADOW_OFF + F / 8) 0 8 _ 0);
            [reflexivity | zside | zside | rewrite Z.add_0_r; exact ZS8] ]) HDS) as HS3
end.
clear HS. rename HS3 into HS. sbd_nss HS.
(* The frame bytes and the frame's shadow bytes are sb_dec's own (in_frames with (0, fpos) in own). *)
assert (SHF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
paj_run_to_sh RUNTOP HS HJ2 0x2f80.
{ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  apply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (SHADOW_OFF + F / 8)).
  { reflexivity. } { exact B529. }
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. unfold awr_byte. right; right; right. exists 0, fpos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (frame_addr lyc 0 fpos) with F. rewrite SHF. change (fs_frame_bytes 0 / 8) with 8. clear - Ha; lia. }
  apply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat F).
  { reflexivity. } { exact RF3. }
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. unfold awr_byte. right; right; right. exists 0, fpos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (frame_addr lyc 0 fpos) with F. change (fs_frame_bytes 0) with 64. clear - Ha; lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (s1v - sp0)).
  { reflexivity. } { transitivity s1v; [exact B60' | clear; lia]. } { cbn [YP09.r_wlo]. clear - Hs1 HSTK Hwlo Hwhi Hes; lia. }
  { cbn [YP09.r_whi]. clear - Hs1 Hwhi; lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)).
  { reflexivity. } { transitivity (spZ regs); [exact B2' | clear; lia]. } { cbn [YP09.r_wlo]. clear - HSTK Hwlo Hwhi Hes; lia. }
  { cbn [YP09.r_whi]. clear - Hwhi; lia. }
  apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG.
(* ---- the state at the cut ------------------------------------------------------------------------- *)
(* The frame and its shadow, as one predicate: the only bytes of the call state this segment changed
   outside its own stack window. *)
assert (INF : forall a, in_frames lyc [(0, fpos)] a <->
  (F <= a < F + 64 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8)).
{ intros a. split.
  - intros (cid & pos & [Eq | []] & Hr). injection Eq as <- <-.
    unfold in_zr in Hr. cbn [fst snd] in Hr. change (fs_frame_bytes 0) with 64 in Hr.
    change (frame_addr lyc 0 fpos) with F in Hr. rewrite SHF in Hr. change (64 / 8) with 8 in Hr. exact Hr.
  - intros Hr. exists 0, fpos. split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64.
    change (frame_addr lyc 0 fpos) with F. rewrite SHF. change (64 / 8) with 8. exact Hr. }
pose proof HFr as HFr3.
assert (KPOST : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
  ~ in_frames lyc [(0, fpos)] a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hw Hf.
  apply (kept_of_frame E3v _ (w_H W) mem2 (ms_mem ms1)
    (fun x => (spZ regs - SB_DEC_STK <= x < spZ regs) \/ in_frames lyc [(0, fpos)] x) HFr3);
  [| exact Ha | intros [Hx | Hx]; [exact (Hw Hx) | exact (Hf Hx)]].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map fframe_region fshadow_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  repeat (destruct Hin as [Eq | Hin];
    [ injection Eq as <- <- <-; rewrite ?B529, ?B516, ?B60', ?B2' in Hr; cbn [base_val] in Hr;
      first [ left; clear - Hr Hs1 HSTK Hes; lia
            | right; apply INF; clear - Hr; lia ] | ]);
  destruct Hin. }
assert (KEEPall : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SB_DEC_STK <= a < spZ regs) ->
  ~ in_frames lyc [(0, fpos)] a -> alloc_ceiling <= a ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw Hf Hc. rewrite (KPOST a Ha Hw Hf).
  rewrite (HKhi a ltac:(clear - Ha Hc; lia) ltac:(clear - Hw Hs1 HSTK Hes; lia)).
  apply KEEPpre; [exact Ha | exact Hw]. }
(* the block, image and frame bytes of the call state, which the stack-frame allocation kept too *)
assert (KEEPblk : forall b0 m0 i, In (b0, m0) (ablocks B lyc Sc) -> 0 <= i < req_size m0 ->
  ~ in_frames lyc [(0, fpos)] (b0 + i) ->
  aview SEGS (w_H W) (ms_mem ms1) (b0 + i) = aview SEGS (w_H W) memc (b0 + i)).
{ intros b0 m0 i Hin Hi Hf.
  destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b0 m0 HARc Hin) as (_ & H4096 & Hce & _ & _).
  rewrite (KPOST (b0 + i) ltac:(clear - H4096 Hce Hi C1; lia) ltac:(clear - H4096 Hce Hi Hacsp; lia) Hf).
  rewrite (HKblk b0 m0 i Hin Hi ltac:(intros []));
  apply KEEPpre; [clear - H4096 Hce Hi C1; lia | clear - H4096 Hce Hi Hacsp; lia]. }
assert (KEEPimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Hi Hns He. pose proof (Hsegs a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hrng.
  unfold kLowMemEnd in Hlow.
  rewrite (KPOST a ltac:(clear - Hlow; lia) ltac:(clear - Hlow Hacsp C1; lia)
    ltac:(intros Hf; apply INF in Hf; clear - Hf Hrng Hlow HFimg HF8lo HF8hi; unfold SHADOW_OFF in *; lia)).
  rewrite (HKimg a Hi Hns He).
  apply KEEPpre; [clear - Hlow; lia | clear - Hlow Hacsp C1; lia]. }
assert (KEEPfrm : forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ in_frames lyc [(0, fpos)] a ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros cid pos a Hin Hr Hf.
  destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos a HARc Hin Hr) as (Hzc & _).
  assert (Hb : 0 <= a < 2 ^ 64 /\ ~ (spZ regs - SB_DEC_STK <= a < spZ regs)).
  { destruct Hr as [Hr | Hr]; unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
    pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & Hfc & _);
    pose proof (fs_frame_bytes_nonneg cid) as Hfb;
    [ clear - Hr Hf0 Hfc Hzc Hacsp C1; lia
    | pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(clear - Hf0 Hfc Hfb C1 C4; lia)) as Hsb;
      clear - Hr Hsb Hzc Hacsp C1 C2 C5; unfold kLowMemEnd, kHighShadowEnd in *; lia ]. }
  destruct Hb as (Hb1 & Hb2).
  rewrite (KPOST a Hb1 Hb2 Hf). rewrite (HKfrm cid pos a Hin Hr ltac:(intros [])).
  apply KEEPpre; [exact Hb1 | exact Hb2]. }
assert (PRESall : forall a, apresent (w_H W) memc a -> alloc_ceiling <= a < 2 ^ 64 ->
  ~ (spZ regs - SB_DEC_STK <= a < spZ regs) -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Hp Ha Hw. eapply apresent_grows; [exact HG|].
  apply (HKpres a ltac:(clear - Ha; lia) ltac:(clear - Hw Hs1 HSTK Hes; lia)).
  eapply apresent_grows; [exact GROWpre | exact Hp]. }
(* the symbolic regions of the cut state, for the registers and the stored words *)
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) ms1) 0%nat _ HS eq_refl) as HRsh.
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) ms1) 1%nat _ HS eq_refl) as HRfr.
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) ms1) 3%nat _ HS eq_refl) as HRstk.
cbn [restrict ms_mem] in HRsh, HRfr, HRstk.
(* the registers at the cut *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (5%bv : bv 5) Q5. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
assert (AGE : forall n0, (n0 < 60)%nat -> ew E3v n0 = ew E n0)
  by (intros n0 Hn0; rewrite (AG3 n0 ltac:(lia)), (AG2 n0 ltac:(lia)); apply AG1; exact Hn0).
assert (E60' : ew E3v 60 = Z_to_bv 64 s1v) by (rewrite (AG3 60%nat ltac:(lia)), (AG2 60%nat ltac:(lia)); exact E60).
(* the atom equations the registers denote *)
rewrite E60' in Q2, Q9.
rewrite (AGE 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl) in Q3.
rewrite (AGE 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl) in Q4.
rewrite (AGE 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl) in Q8.
rewrite (AGE 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl), G10 in Q19.
rewrite (AGE 12%nat ltac:(lia)), (EE 12%nat 12%bv eq_refl), G12 in Q20.
rewrite (AGE 11%nat ltac:(lia)), (EE 11%nat 11%bv eq_refl), G11 in Q21.
rewrite (AGE 32%nat ltac:(lia)), E32 in Q22.
rewrite (AGE 27%nat ltac:(lia)), (EE 27%nat 27%bv eq_refl) in Q27.
rewrite E516' in Q18, Q23. rewrite E529 in Q24.
(* x25 = F + 32 and x26 = ~(F + 32), the released U_not_off (Reusable/YI08.v:183) *)
assert (Q25' : getr (ms_regs ms1) (25%bv : bv 5) = w64 (F + 32)).
{ rewrite Q25, RF3. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_restrict_reg (w_H W) E3v ssx msx (26%bv : bv 5) HS) as Q26raw;
  change (sr_get (ss_regs ssx) (26%bv : bv 5)) with (SAlu ALU_XOR (SOff 516 32) (SLit (-1))) in Q26raw
end.
cbn [ms_regs restrict mkst] in Q26raw.
assert (Q26' : getr (ms_regs ms1) (26%bv : bv 5) = w64 (2 ^ 64 - (F + 32) - 1)).
{ rewrite Q26raw, denot_lit_U. unfold w64. f_equal.
  rewrite (U_not_off E3v 516 F 32 E516' ltac:(clear - HF4096 HFceil C1; lia) ltac:(clear - HF4096 HFceil C1; lia)).
  clear - HF4096; lia. }
(* ---- the journal facts carried to the cut ---------------------------------------------------------- *)
assert (Hsec2 : sec_extents lyc S2 = sec_extents lyc Sc) by (rewrite ES2; reflexivity).
assert (Hchk2 : st_chunks S2 = st_chunks Sc) by (rewrite ES2; reflexivity).
assert (AOWN : forall a, aowned B lyc S2 a -> aowned B lyc Sc a).
{ intros a (HL & HR). split; [rewrite Hsec2 in HL; exact HL|].
  intros Hc. apply HR. destruct Hc as [(kk & Hin & Hst & Hr) | (cp & Hin & Hr)].
  - left. exists kk. rewrite Hchk2. split; [exact Hin | split; [exact Hst | exact Hr]].
  - right. exists cp. split; [rewrite Hfrs2; right; exact Hin | exact Hr]. }
assert (AWRm : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, fpos) :: own) a).
{ intros a Ha. rewrite Eab. destruct Ha as [H1 | [H1 | [H1 | (cid & pos & Hin & Hr)]]].
  - left; exact H1.
  - right; left; exact H1.
  - right; right; left; exact H1.
  - right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr]. }
(* the twelve saved words, from the stack region of the cut state *)
assert (SAVE : forall (j : nat) (off : Z), In (YP09.mkChunk off (CVal 8 (SOff j 0))) (YP09.r_chunks
    (YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0
      [YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
       YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
       YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
       YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
       YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
       YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))])) ->
  (j < 60)%nat -> forall (r : bv 5), Z.of_nat j = bv_unsigned r ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + off) 8 (bv_unsigned (getr regs r))).
{ intros j off Hin Hj r Hr.
  apply (field_of_region E3v _ 2%nat (spZ regs) _ (-96) 0 (-96) 0 off 8%N (SOff j 0) _ HRstk);
  [ exact B2' | exact Hin
  | cbn [sv_denot]; rewrite (AGE j Hj), (EE j r Hr), Z.add_0_r; reflexivity
  | pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hbr; change (bv_modulus 64) with (2 ^ 64) in Hbr;
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hbr; lia
  | zside ]. }
pmkst HS.
unfold cfg_at in HCONT. change (fun x : Z => w64 x) with (fun x : Z => Z_to_bv 64 x) in HCONT.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rr _ ?mm _) ?mdx) _ =>
  apply (HCONT fpos S2 s1v rr mm mdx) end.
unfold sbd_at1. fold F.
split; [exact HJ2|].
split; [exact Hfrs2|].
split; [exact Eab|].
split; [exact Hra0|].
split; [exact Hal16|].
split; [exact Hwlo|].
split; [exact Hwhi|].
split; [exact Hgp|].
split; [exact Htp|].
split; [exact Hra4|].
split; [exact Hv|].
split; [exact Hmd|].
split; [exact Hb8|].
split; [exact Hb0|].
split; [exact Hb63|].
split; [exact Hbwin|].
split; [exact Hrec|].
split; [exact Rp|].
split; [exact Rcap|].
split; [exact Rn0|].
split; [exact Rn4|].
split; [exact Rov|].
split; [clear - Hs1; lia|].
split; [clear - Hs1; lia|].
split; [exact Hs1al|].
(* the frame's last word still holds the flag address *)
split.
{ apply (rdword_of_val_mem SEGS (w_H W) (ms_mem ms1) (frame_addr lyc 0 fpos + 64 - 8) (flag_addr lyc 0 fpos)).
  - fold F. fold FL. replace (F + 64 - 8) with (F + 56) by (clear; lia).
    apply (field_of_region E3v _ 516%nat F _ 0 64 0 64 56 8%N (SOff 528 0) _ HRfr);
    [ exact B516
    | cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]
    | cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - HFLnum C1; zside | zside ].
  - fold FL. clear - HFLnum C1; lia. }
(* the registers at 0x836f4 *)
split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q8|].
split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
split; [exact Q13|]. split; [exact Q14|]. split; [exact Q15|].
split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|].
split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25'|]. split; [exact Q26'|]. split; [exact Q27|].
(* the twelve saved words *)
split; [exact (SAVE 1%nat (-8) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 1%bv eq_refl)|].
split; [exact (SAVE 8%nat (-16) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 8%bv eq_refl)|].
split; [exact (SAVE 9%nat (-24) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 9%bv eq_refl)|].
split; [exact (SAVE 18%nat (-32) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 18%bv eq_refl)|].
split; [exact (SAVE 19%nat (-40) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 19%bv eq_refl)|].
split; [exact (SAVE 20%nat (-48) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 20%bv eq_refl)|].
split; [exact (SAVE 21%nat (-56) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 21%bv eq_refl)|].
split; [exact (SAVE 22%nat (-64) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 22%bv eq_refl)|].
split; [exact (SAVE 23%nat (-72) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 23%bv eq_refl)|].
split; [exact (SAVE 24%nat (-80) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 24%bv eq_refl)|].
split; [exact (SAVE 25%nat (-88) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 25%bv eq_refl)|].
split; [exact (SAVE 26%nat (-96) ltac:(cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]) ltac:(lia) 26%bv eq_refl)|].
(* the frame's shadow byte 4 = 04: the four bytes [F + 32, F + 36) are addressable *)
split.
{ assert (HV4 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (SHADOW_OFF + F / 8 + 4) 1 4).
  { apply (field_of_region E3v _ 529%nat (SHADOW_OFF + F / 8) _ 0 8 0 8 4 1%N (SLit 4) _ HRsh);
    [ exact B529
    | cbn [YP09.r_chunks]; repeat first [left; reflexivity | right]
    | reflexivity | zside | zside ]. }
  unfold aview. rewrite <- (Z.add_0_r (SHADOW_OFF + F / 8 + 4)).
  change (SHADOW_OFF + F / 8 + 4 + 0) with (SHADOW_OFF + F / 8 + 4 + Z.of_nat 0).
  rewrite (HV4 0%nat ltac:(lia)). reflexivity. }
(* the struct sb, kept from memc *)
assert (BKEEP : forall off w0 x, 0 <= off -> off + Z.of_nat w0 <= 28 ->
  val_mem SEGS (mrestrict (w_H W) memc) (b + off) w0 x ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (b + off) w0 x).
{ intros off w0 x Hoff Hw0 Hval j Hj.
  rewrite <- (Hval j Hj). apply (mbyte_of_aview SEGS). apply KEEPall.
  - clear - Hb0 Hb63 Hoff Hw0 Hj; lia.
  - clear - Hbwin Hoff Hw0 Hj; lia.
  - intros Hf. apply INF in Hf.
    assert (Hin : ly_stk_lo ly <= b + off + Z.of_nat j) by (clear - Hrec Eslo Hoff Hw0 Hj; unfold tsb_dec_rec_at in Hrec; lia).
    clear - Hf Hin Hceil HFceil C1 HF8lo HF8hi HF4096. unfold SHADOW_OFF in *; lia.
  - clear - Hrec Eslo Hceil Hoff Hw0 Hj; unfold tsb_dec_rec_at in Hrec; lia. }
split; [rewrite <- (Z.add_0_r b) at 1; exact (BKEEP 0 8%nat p ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(rewrite Z.add_0_r; exact Vp))|].
split; [exact (BKEEP 8 8%nat cap ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) Vcap)|].
split; [exact (BKEEP 16 8%nat n ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) Vn)|].
split; [exact (BKEEP 24 4%nat ov ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) Vov)|].
(* the caller's right to write b + 16 .. b + 28, at the cut state *)
split.
{ intros a Ha. destruct (HWRb a Ha) as (Hw & Hp & Ho & Hns).
  split; [exact (AWRm a Hw)|].
  split.
  { apply PRESall; [exact Hp | clear - Hrec Eslo Hceil Ha Hb63; unfold tsb_dec_rec_at in Hrec; lia
    | clear - Hbwin Ha; lia]. }
  split; [intros Ho2; exact (Ho (AOWN a Ho2)) | exact Hns]. }
(* the buffer p[n ..] *)
split.
{ intros Hroom. destruct (HROOM Hroom) as (Hp0 & Hpcap & HDST & HRA & HWRp & Hpb & Hpsp).
  split; [exact Hp0|]. split; [exact Hpcap|]. split; [exact HDST|].
  (* re-derived at the cut: a block byte from the state's own invariant, a frame byte transported *)
  split.
  { intros x Hx.
    destruct (HDST x ltac:(clear - Hx; lia)) as [(b0 & m0 & Hin & Hr) | (cid & pos & Hin & Hr)].
    - exact (range_addressable_of_block SEGS B LAWS lyc S2 W (ms_mem ms1) _ b0 m0 x 1
        (proj1 HJ2) ltac:(rewrite Eab; exact Hin) ltac:(clear - Hr; lia) ltac:(clear - Hr; lia)
        x ltac:(clear - Hx; lia)).
    - destruct (HRA x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
      rewrite <- Hs.
      destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hal32 & _ & _ & _).
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & Hfc & _).
      destruct (frame_al64 SEGS B lyc Sc W memc mdc cid pos HARc Hin) as (_ & Hfb64 & H64).
      assert (Hal8 : frame_addr lyc cid pos mod 8 = 0) by (apply mod32_mod8; exact Hal32).
      assert (Hb8' : fs_frame_bytes cid mod 8 = 0).
      { pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(discriminate)) as D64. rewrite Hfb64, Z.add_0_r in D64.
        rewrite D64. replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by ring.
        apply Z_mod_mult. }
      unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
      pose proof (fs_frame_bytes_nonneg cid) as Hfb.
      pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(discriminate)) as Dq.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(discriminate)) as Dq2.
      assert (Hq1 : frame_addr lyc cid pos / 8 <= x / 8) by (apply Z.div_le_mono; clear - Hr; lia).
      assert (Hq2 : x / 8 < frame_addr lyc cid pos / 8 + fs_frame_bytes cid / 8)
        by (apply Z.div_lt_upper_bound; clear - Hr Hal8 Hb8' Dq Dq2 Hfb; lia).
      apply (KEEPfrm cid pos (shadow_of_addr SHADOW_OFF x) Hin).
      + right. clear - Hq1 Hq2. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia.
      + intros Hf. destruct Hf as (c0 & p0 & [Eq | []] & Hz0). injection Eq as <- <-.
        apply in_split in Hin as (l2 & l3 & El).
        apply (frames_zone_disj SEGS B LAWS lyc S2 W (ms_mem ms1) _ (0, fpos) (cid, pos) [] l2 l3
          (shadow_of_addr SHADOW_OFF x) (proj1 HJ2) ltac:(cbn [app]; rewrite Hfrs2, El; reflexivity) Hz0).
        right. clear - Hq1 Hq2. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia. }
  split.
  { intros a Ha. destruct (HWRp a Ha) as (Hw & Hp & Ho & Hns).
    split; [exact (AWRm a Hw)|].
    split.
    { destruct (HDST a Ha) as [(b0 & m0 & Hin & Hr) | (cid & pos & Hin & Hr)].
      - destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b0 m0 HARc Hin) as (_ & H4096 & Hce & Happ & _).
        pose proof (blk_off_imgP B lyc Sc W memc mdc b0 m0 HARc Hin) as Himg.
        eapply (apresent_transfer SEGS (w_H W) (w_H W) memc (ms_mem ms1) a);
        [ clear - Hr H4096 Hce C1; lia
        | intros Hi; pose proof (pa_img_range a Hi) as Hrng; clear - Hrng Himg Hr; lia
        | assert (Hk : aview SEGS (w_H W) (ms_mem ms1) (b0 + (a - b0)) = aview SEGS (w_H W) memc (b0 + (a - b0)))
            by (apply (KEEPblk b0 m0 (a - b0) Hin ltac:(clear - Hr; lia));
                intros Hf; destruct Hf as (c0 & p0 & [Eq | []] & Hz0); injection Eq as <- <-;
                exact (block_not_frame_zone SEGS B LAWS lyc S2 W (ms_mem ms1) _ b0 m0 (a - b0) 0 fpos (proj1 HJ2)
                  ltac:(rewrite Eab; exact Hin) Hfin2 ltac:(clear - Hr; lia) Hz0));
          replace (b0 + (a - b0)) with a in Hk by ring; exact Hk
        | exact Hp ].
      - destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & Hfc & _).
        pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HARc Hin) as Himg.
        pose proof (fs_frame_bytes_nonneg cid) as Hfb.
        unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
        eapply (apresent_transfer SEGS (w_H W) (w_H W) memc (ms_mem ms1) a);
        [ clear - Hr Hf0 Hfc C1; lia
        | intros Hi; pose proof (pa_img_range a Hi) as Hrng; clear - Hrng Himg Hr; lia
        | apply (KEEPfrm cid pos a Hin ltac:(left; unfold frame_rng, in_zr; cbn [fst snd]; clear - Hr; lia));
          intros Hf; destruct Hf as (c0 & p0 & [Eq | []] & Hz0); injection Eq as <- <-;
          apply in_split in Hin as (l2 & l3 & El);
          apply (frames_zone_disj SEGS B LAWS lyc S2 W (ms_mem ms1) _ (0, fpos) (cid, pos) [] l2 l3 a
            (proj1 HJ2) ltac:(cbn [app]; rewrite Hfrs2, El; reflexivity) Hz0);
          left; unfold frame_rng, in_zr; cbn [fst snd]; clear - Hr; lia
        | exact Hp ]. }
    split; [intros Ho2; exact (Ho (AOWN a Ho2)) | exact Hns]. }
  split; [exact Hpb | exact Hpsp]. }
(* what segment A kept *)
unfold tcj_kept. cbn beta.
split.
{ intros a Ha Hw Hf. apply KEEPall; [clear - Ha C1; lia | exact Hw | exact Hf | clear - Ha; lia]. }
split.
{ intros b0 m0 i Hin Hi Hf. exact (KEEPblk b0 m0 i Hin Hi Hf). }
split.
{ intros a Hi Hns He. exact (KEEPimg a Hi Hns He). }
split.
{ intros cid pos a Hin Hr Hf. exact (KEEPfrm cid pos a Hin Hr Hf). }
split.
{ intros a Ha Hw Hp. apply PRESall; [exact Hp | exact Ha | exact Hw]. }
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  intros a Ha. apply Hpres3. clear - Ha Hwlo Hwhi; lia. }
Qed.
End walk.
End h.
End f.
End d.
