(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgChk_check_cells_valid.v (this branch) for image B (fuzz_headamp.asan-ubsan): it walks image B's check_cells_valid 0x83fcc against the same text lib/A/HPgCSpec.v hd_check_cells_valid_specX on lib/AU/Img0U.v rsegs. Image B's GOT word 0x9c7f0 and cell 0xa5238; B's loop counts the byte offset a3 (out + a3 by an alias atom) and checks out + a3 against overflow (the UBSan trap bltu a4,a3 with a4 = ~out, decided from the facts of a4 and a3); the loop head is the trap check 0x83ffc. The segment-generic lemmas and tactics are imported from the image A file. *)
(* check_cells_valid 0x83fcc of fuzz_headamp.asan-ubsan (pinned sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94;
   addresses read on the unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff), 61 words:
     0x83fcc addi sp,sp,-0x10; sd ra,8(sp); 0x83fd4 blez a1,0x84098; a3 := 0; auipc a2; ld a2,-0x7ec(a2) (the GOT
       word 0x9c7f0, which holds the shadow-offset cell 0xa5238); a4 := ~a0; ld a5,0(a2); a6 := 3 a1; a7 := 0x2f; t0 := 2;
     loop 0x83ffc: bltu a4,a3,0x840ac (the UBSan pointer-overflow trap, `unimp`); a1 := a0 + a3;
       the shadow check of a1 + 1 (lb 0x84010; bnez -> 0x84070: andi t2,a2,7; blt t2,t1 -> back; j report), of a1
       (lb 0x84020), lbu a2 = out[j + 1]; lbu t1 = out[j]; 0x84030 bltu 0x2f,t1 -> 0x840a4 (abort);
       0x84034 bltu 2,a2 -> 0x840a4; beq a2,2: t1 := 0x37, else t1 := 1; the shadow check of a1 + 2 (lb 0x84054);
       lbu a1 = out[j + 2]; 0x84060 bltu t1,a1 -> 0x840a4; a3 += 3; 0x84068 bne a6,a3,0x83ffc; j 0x84098;
     0x84098 ld ra,8(sp); addi sp,sp,0x10; 0x840a0 ret; 0x840a4 jal __asan_handle_no_return; jal abort; 0x840ac unimp.
   WHY THE TRAP AND THE ABORT ARE UNREACHABLE: hd_app_rng gives 4096 <= out and out + 3 rc <= 0x7fffff800000, so a4 =
   2^64 - 1 - out is at least 2^64 - 1 - 0x7fffff800000 while a3 = 3 i < 3 (2^31 - 1): the facts of the cell's state
   decide `bltu a4,a3` not taken. The abort `bltu` are decided as on image A (p a literal, ch / v atoms with closed
   bounds); the three shadow checks are token loads (all three slow blocks have the blt form). THE LOOP: the invariant
   at 0x83ffc after i cells: a0 = out, a3 = 3 i, a4 = ~out, a5 = the shadow offset, a6 = 3 rc, a7 = 0x2f, t0 = 2, the
   frame and memory clauses of image A; the last cell holds a6 as a3 + 3, the others carry the condition a6 <> a3 + 3. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgChk_check_cells_valid.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image B: the function, its loop head (the trap check), its latch, its `ret`, the two cells it reads ---- *)
Definition A_CHECK_CELLS_VALID_B : Z := 0x83fcc.
Definition CVU_LOOP : Z := 0x83ffc.
Definition CVU_LATCH : Z := 0x84068.
Definition CVU_RET : Z := 0x840a0.
(* image B's GOT word of __asan_shadow_memory_dynamic_address and the cell itself (.symtab of the unstripped twin;
   the GOT word's file bytes hold 0xa5238) *)
Definition B_GOT_SHADOW : Z := 0x9c7f0.
Definition B_SHADOW_CELL : Z := 0xa5238.
(* the range of ~p for 4096 <= p <= 0x7fffff800000 *)
Definition NOT_LO : Z := 2 ^ 64 - 1 - 0x7fffff800000.
Definition NOT_HI : Z := 2 ^ 64 - 1 - 4096.
(* the 61 words 0x83fcc .. 0x840bc *)
Definition cvu_tbl : ctable := build_table rsegs A_CHECK_CELLS_VALID_B 61 TEmpty.
Lemma cvu_tbl_ok : table_ok rsegs cvu_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_CELLS_VALID_B. lia. Qed.
Lemma cvu_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma cvu_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
Lemma cvu_ret_word : clookup cvu_tbl CVU_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
(* `not` (xori -1) on a 64-bit value *)
Lemma cvu_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = (Z.lnot x) mod 2 ^ 64).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
replace (Z.lnot x) with (- x - 1) by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the entry state at 0x83fcc (A's facts cv_facts0, image B's .got word and cell) ---- *)
Definition cvu_got_region : YP09.region :=
  YP09.mkRegion None B_GOT_SHADOW (B_GOT_SHADOW + 8) 0 0 [YP09.mkChunk B_GOT_SHADOW (CVal 8 (SLit B_SHADOW_CELL))].
Definition cvu_cell_region : YP09.region :=
  YP09.mkRegion None B_SHADOW_CELL (B_SHADOW_CELL + 8) 0 0 [YP09.mkChunk B_SHADOW_CELL (CVal 8 (SOff 32 0))].
Definition cvu_regions0 : smem := [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 []; cvu_got_region; cvu_cell_region].
Definition cvu_ss0 (pos : bool) : sstate := mkSS A_CHECK_CELLS_VALID_B sr_atoms cvu_regions0 None (cv_facts0 pos).

(* ---- the entry state of one cell at the loop head 0x83ffc ---- *)
(* env slots 32 .. 35: the shadow offset, out + 3 i, the cell's channel and value bytes *)
Definition cvu_extra (xo ch v : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 xo; Z_to_bv 64 ch; Z_to_bv 64 v].
Definition cvu_ov (last : bool) : list (bv 5 * sv) :=
  [((15%bv : bv 5), SOff 32 0); ((17%bv : bv 5), SLit 47); ((5%bv : bv 5), SLit 2)]
  ++ (if last then [((16%bv : bv 5), SOff 13 3)] else []).
Definition cvu_cells (p : Z) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 3 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SLit p)); YP09.mkChunk 2 (CVal 1 (SOff 35 0))].
Definition cvu_facts (lim : Z) (last : bool) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 16) (2 ^ 47 - 16) 4); (13%nat, mkAF 0 (3 * (2 ^ 31 - 2)) 0);
           (14%nat, mkAF NOT_LO NOT_HI 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 0x7fffff800000 0); (34%nat, mkAF 0 47 0); (35%nat, mkAF 0 lim 0)]
          (if last then [] else [mkAC BC_NE (SOff 16 0) (SOff 13 3)])
          [(SAlu ALU_ADD (SOff 10 0) (SOff 13 0), SOff 33 0)].
Definition cvu_ss (p lim : Z) (last : bool) : sstate :=
  mkSS CVU_LOOP (cv_sr_of (cvu_ov last)) [cv_stk; cvu_cells p] None (cvu_facts lim last).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cvu_entry0 : forall (pos : bool) (W : world rsegs) regs memc rcc,
  (forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) B_GOT_SHADOW 8 B_SHADOW_CELL ->
  val_mem rsegs (mrestrict (w_H W) memc) B_SHADOW_CELL 8 SHADOW_OFF ->
  getr regs 11 = w64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 ->
  (if pos then 0 < rcc else rcc <= 0) ->
  st_ok rsegs (Ereg regs cv_extra0) (cvu_ss0 pos)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_CELLS_VALID_B) memc (seg_rom rsegs))).
Proof.
intros pos W regs memc rcc Hpres Hsp Hal Vgot Vcell H11 Hrc Hpos.
rewrite restrict_mkst_fx. unfold cvu_ss0.
assert (E2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E11 : ew (Ereg regs cv_extra0) 11 = Z_to_bv 64 rcc) by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew (Ereg regs cv_extra0) 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ew_Ereg_extra regs _ 0)).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold cvu_regions0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (region_ok_stack rsegs (Ereg regs cv_extra0) _ 2 (spZ regs) (-16) E2); [lia | lia |].
    intros a Ha. apply (apresent_writable rsegs). apply Hpres. lia.
  + unfold region_ok, cvu_got_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold B_GOT_SHADOW. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs (Ereg regs cv_extra0) _ 0 B_GOT_SHADOW 8 (SLit B_SHADOW_CELL) B_SHADOW_CELL);
      [reflexivity | unfold B_SHADOW_CELL; cbn; lia | lia | exact Vgot].
  + unfold region_ok, cvu_cell_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold B_SHADOW_CELL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs (Ereg regs cv_extra0) _ 0 B_SHADOW_CELL 8 (SOff 32 0) SHADOW_OFF);
      [rewrite (cv_denot_off (Ereg regs cv_extra0) 32 SHADOW_OFF 0 E32 HSB) by lia; rewrite Z.add_0_r; reflexivity
      | unfold SHADOW_OFF; cbn; lia | lia | exact Vcell].
- unfold cvu_regions0, cvu_got_region, cvu_cell_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold B_GOT_SHADOW, B_SHADOW_CELL. repeat split; lia.
- destruct pos; unfold cv_facts0; split; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + split; exact I.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + split; [|exact I]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite YO0c.branch_ge. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite !YO0c.lit64_unsigned. unfold YO0b.s64.
    destruct (Z.eq_dec rcc 0) as [->|Hn].
    * reflexivity.
    * replace (rcc mod 2 ^ 64) with (rcc + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
      change (0 mod 2 ^ 64) with 0.
      destruct (Z.ltb_spec (rcc + 2 ^ 64) (2 ^ 63)); [lia|]. destruct (Z.ltb_spec 0 (2 ^ 63)); [|lia].
      apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
End e.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.
(* image B's symbol record holds the shadow-offset GOT word and cell (both read by check_cells_valid at entry) *)
Hypothesis HBgot : as_got_shadow B = B_GOT_SHADOW.
Hypothesis HBcell : as_shadow_cell B = B_SHADOW_CELL.

Section loop.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (rcc o : Z) (cs : list Headamp.cell).
Hypothesis Hrc : 0 < rcc < 2 ^ 31.
Hypothesis Hlen : Z.of_nat (length cs) = rcc.
Hypothesis Hval : Forall Headamp.cell_valid cs.
Hypothesis Hg : garr8 rsegs (mrestrict (w_H W) memc) o (hd_zbytes (ha_cells_bytes cs)).
Hypothesis Hra : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o (3 * rcc).
Hypothesis Hoff : hd_off_stack regs T_check_STK o (3 * rcc).
Hypothesis Happ : hd_app_rng rsegs o (3 * rcc).
Hypothesis Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47.
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis Hrar : YK0s.ret_ok (getr regs 1).
Hypothesis H10 : getr regs 10 = w64 o.
Hypothesis H11 : getr regs 11 = w64 rcc.
Hypothesis HJ0 : ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hwlo : sp0 - STK <= spZ regs - 32.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hpres16 : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a.
Hypothesis Vgot : val_mem rsegs (mrestrict (w_H W) memc) B_GOT_SHADOW 8 B_SHADOW_CELL.
Hypothesis Vcell : val_mem rsegs (mrestrict (w_H W) memc) B_SHADOW_CELL 8 SHADOW_OFF.

Definition cvu_post : world rsegs -> config -> Prop :=
  hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True).

(* the loop head after i cells *)
Definition cvu_inv (i : Z) (regs_i : bvmap 5 word) (mem_i : word -> option byte) (md_i : Model) : Prop :=
  0 <= i < rcc /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem_i md_i k /\
  same_io mdc md_i /\
  getr regs_i 10 = w64 o /\ getr regs_i 13 = w64 (3 * i) /\ getr regs_i 14 = w64 (2 ^ 64 - 1 - o) /\
  getr regs_i 15 = w64 SHADOW_OFF /\ getr regs_i 16 = w64 (3 * rcc) /\
  getr regs_i 17 = w64 47 /\ getr regs_i 5 = w64 2 /\
  getr regs_i 2 = w64 (spZ regs - 16) /\ getr regs_i 1 = getr regs 1 /\
  (forall r, acallee_saved r -> r <> 2 -> getr regs_i (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  val_mem rsegs (mrestrict (w_H W) mem_i) (spZ regs - 8) 8 (raZ regs) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a).
Definition cvu_P (i : Z) (W' : world rsegs) (c : config) : Prop :=
  W' = W /\ exists regs_i mem_i md_i,
  c = mkCfg (mkst regs_i (Z_to_bv 64 CVU_LOOP) mem_i (seg_rom rsegs)) md_i /\ cvu_inv i regs_i mem_i md_i.

(* ---- the checked range, as the premises give it ---- *)
Lemma cvu_rng : 4096 <= o /\ o + 3 * rcc <= 0x7fffff800000.
Proof.
destruct Happ as ([H0 Hr] & _). pose proof ASAN_CEIL_range as [CR _].
unfold kLowShadowBeg, kHighMemBeg in Hr. lia.
Qed.
Lemma cvu_off : forall x, o <= x < o + 3 * rcc -> ~ (spZ regs - 32 <= x < spZ regs).
Proof. intros x Hx. exact (Hoff x Hx). Qed.
Lemma cvu_g_at : forall mem_i,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a) ->
  garr8 rsegs (mrestrict (w_H W) mem_i) o (hd_zbytes (ha_cells_bytes cs)).
Proof.
intros mem_i KE j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj.
pose proof cvu_rng as Hr.
apply (cv_val_kept _ memc mem_i _ 1 _ Hv). intros jj Hjj. assert (jj = 0%nat) by lia. subst jj.
apply KE; [lia|]. pose proof (cvu_off (o + Z.of_nat j) ltac:(lia)). lia.
Qed.
Lemma cvu_ra_at : forall mem_i,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a) ->
  range_addressable (aview rsegs (w_H W) mem_i) SHADOW_OFF o (3 * rcc).
Proof.
intros mem_i KE. apply (cv_ra_kept _ memc mem_i _ _ Hra). intros x Hx.
pose proof cvu_rng as Hr. unfold shadow_of_addr.
assert (Hq : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply KE; unfold SHADOW_OFF; lia.
Qed.

(* ---- the obligations of a cell's run: range_addressable (out + 3 i + c, 1) ---- *)
Lemma cvu_obl : forall i ch v regs_i mem_i md_i c,
  cvu_inv i regs_i mem_i md_i -> 0 <= c < 3 ->
  range_addressable (rd_of rsegs (mrestrict (w_H W) mem_i)) (U (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) cv_Bx)
    (U (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) (SOff 33 c)) 1.
Proof.
intros i ch v regs_i mem_i md_i c HI Hc.
destruct HI as (Hi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KE).
pose proof cvu_rng as Hr.
assert (E33 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 33 = Z_to_bv 64 (o + 3 * i)) by exact (ew_Ereg_extra regs_i _ 1).
rewrite (U_atom_off _ 33 (o + 3 * i) c E33) by lia.
eapply obl_of_range; [exact (cvu_ra_at mem_i KE) | | lia | lia].
unfold cv_Bx. apply (U_atom _ 32 SHADOW_OFF); [exact (ew_Ereg_extra regs_i _ 0) | unfold SHADOW_OFF; lia].
Qed.

(* ---- a cell's entry state ---- *)
Lemma cvu_it_entry : forall i ch p v lim (last : bool) regs_i mem_i md_i,
  cvu_inv i regs_i mem_i md_i ->
  nth_error cs (Z.to_nat i) = Some (ch, p, v) ->
  0 <= ch <= 47 -> 0 <= p <= 2 -> 0 <= v <= lim -> lim < 256 ->
  (if last then rcc - i = 1 else 2 <= rcc - i) ->
  st_ok rsegs (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) (cvu_ss p lim last)
    (restrict (w_H W) (mkst regs_i (Z_to_bv 64 CVU_LOOP) mem_i (seg_rom rsegs))).
Proof.
intros i ch p v lim last regs_i mem_i md_i HI Hnth Hch Hp Hv Hlim Hl.
destruct HI as (Hi & _ & _ & R10 & R13 & R14 & R15 & R16 & R17 & R5 & R2 & R1 & _ & Hslot & KE).
pose proof cvu_rng as Hr.
rewrite restrict_mkst_fx. unfold cvu_ss.
assert (E1 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 1 = getr regs 1) by (rewrite (ew_Ereg_nat regs_i _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 2 = Z_to_bv 64 (spZ regs - 16)) by (rewrite (ew_Ereg_nat regs_i _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 10 = Z_to_bv 64 o) by (rewrite (ew_Ereg_nat regs_i _ 10 10%bv eq_refl); exact R10).
assert (E13 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 13 = Z_to_bv 64 (3 * i)) by (rewrite (ew_Ereg_nat regs_i _ 13 13%bv eq_refl); exact R13).
assert (E14 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 14 = Z_to_bv 64 (2 ^ 64 - 1 - o)) by (rewrite (ew_Ereg_nat regs_i _ 14 14%bv eq_refl); exact R14).
assert (E16 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 16 = Z_to_bv 64 (3 * rcc)) by (rewrite (ew_Ereg_nat regs_i _ 16 16%bv eq_refl); exact R16).
assert (E32 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ew_Ereg_extra regs_i _ 0)).
assert (E33 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 33 = Z_to_bv 64 (o + 3 * i)) by (exact (ew_Ereg_extra regs_i _ 1)).
assert (E34 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 34 = Z_to_bv 64 ch) by (exact (ew_Ereg_extra regs_i _ 2)).
assert (E35 : ew (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) 35 = Z_to_bv 64 v) by (exact (ew_Ereg_extra regs_i _ 3)).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
pose proof (cvu_g_at mem_i KE) as Hgi.
assert (Hi3 : (3 * Z.to_nat i + 2 < length (hd_zbytes (ha_cells_bytes cs)))%nat).
{ unfold hd_zbytes. rewrite length_map, length_ha_cells_bytes. lia. }
destruct (cv_cell_bytes cs (Z.to_nat i) ch p v Hnth) as (B0 & B1 & B2).
destruct (Hgi (3 * Z.to_nat i)%nat ltac:(lia)) as [V0 _].
destruct (Hgi (3 * Z.to_nat i + 1)%nat ltac:(lia)) as [V1 _].
destruct (Hgi (3 * Z.to_nat i + 2)%nat ltac:(lia)) as [V2 _].
rewrite B0, Z.mod_small in V0 by lia. rewrite B1, Z.mod_small in V1 by lia. rewrite B2, Z.mod_small in V2 by lia.
apply entry_st_ok_full.
- apply cv_regs_ok. unfold cvu_ov.
  destruct last; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; split;
    try (let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  all: first
    [ rewrite (cv_denot_off _ 32 SHADOW_OFF 0 E32 HSB) by lia; rewrite Z.add_0_r; symmetry; exact R15
    | rewrite (cv_denot_off _ 13 (3 * i) 3 E13) by lia; rewrite R16; unfold w64; f_equal; lia
    | cbn [sv_denot]; symmetry; first [exact R17 | exact R5] ].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, cv_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (spZ regs - 16) 8 8 (SOff 1 0) (raZ regs)).
    * rewrite (cv_denot_off _ 1 (raZ regs) 0) by (first [rewrite E1; apply cv_bv_of | apply cv_u64 | pose proof (cv_u64 (getr regs 1)); unfold raZ; lia]).
      rewrite Z.add_0_r. reflexivity.
    * pose proof (cv_u64 (getr regs 1)). unfold raZ. cbn. lia.
    * lia.
    * replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia. exact Hslot.
  + unfold region_ok, cvu_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val rsegs _ _ (o + 3 * i) 0 1 (SOff 34 0) ch).
      { rewrite (cv_denot_off _ 34 ch 0 E34) by lia. rewrite Z.add_0_r. reflexivity. }
      { cbn. lia. } { lia. }
      { replace (o + 3 * i + 0) with (o + Z.of_nat (3 * Z.to_nat i)) by lia. exact V0. }
    * apply (chunk_ok_val rsegs _ _ (o + 3 * i) 1 1 (SLit p) p); [reflexivity | cbn; lia | lia |].
      replace (o + 3 * i + 1) with (o + Z.of_nat (3 * Z.to_nat i + 1)) by lia. exact V1.
    * apply (chunk_ok_val rsegs _ _ (o + 3 * i) 2 1 (SOff 35 0) v).
      { rewrite (cv_denot_off _ 35 v 0 E35) by lia. rewrite Z.add_0_r. reflexivity. }
      { cbn. lia. } { lia. }
      { replace (o + 3 * i + 2) with (o + Z.of_nat (3 * Z.to_nat i + 2)) by lia. exact V2. }
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, cv_stk, cvu_cells.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E33, !unsigned_lit_small by lia.
  pose proof (cvu_off (o + 3 * i) ltac:(lia)) as X0.
  split; [split; [lia | exact I] | split; exact I].
- unfold cvu_facts. split; [|split].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E13, E14, E32, E33, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold NOT_LO, NOT_HI.
    repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
  + destruct last; cbn [f_conds conds_ok]; [exact I|]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ne_U, (U_atom _ 16 (3 * rcc) E16), (U_atom_off _ 13 (3 * i) 3 E13) by lia.
    apply negb_true_iff. apply Z.eqb_neq. lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 10 o E10), (U_atom _ 13 (3 * i) E13), (U_atom _ 33 (o + 3 * i) E33) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.

(* ---- the loop head after the next cell ---- *)
Lemma cvu_next : forall i regs_i mem_i md_i ch v E' ss' ms' md',
  cvu_inv i regs_i mem_i md_i -> 2 <= rcc - i ->
  st_ok rsegs E' ss' (restrict (w_H W) ms') ->
  env_agree 36 (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) E' ->
  ss_pc ss' = CVU_LOOP -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 10 = SOff 10 0 -> sr_get (ss_regs ss') 13 = SOff 13 3 ->
  sr_get (ss_regs ss') 14 = SOff 14 0 -> sr_get (ss_regs ss') 15 = SOff 32 0 ->
  sr_get (ss_regs ss') 16 = SOff 16 0 -> sr_get (ss_regs ss') 17 = SLit 47 ->
  sr_get (ss_regs ss') 5 = SLit 2 ->
  sr_get (ss_regs ss') 2 = SOff 2 0 -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io md_i md' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem_i a) ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 CVU_LOOP) (ms_mem ms') (seg_rom rsegs) /\
  cvu_inv (i + 1) (ms_regs ms') (ms_mem ms') md'.
Proof.
intros i regs_i mem_i md_i ch v E' ss' ms' md' HI Hnl HS HA Hpc Hrv S10 S13 S14 S15 S16 S17 S5 S2 S1 Scs HJ' Hio' K'.
destruct HI as (Hi & _ & Hio & R10 & R13 & R14 & R15 & R16 & R17 & R5 & R2 & R1 & Rcs & Hslot & KE).
split; [rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv)|].
assert (HA0 := HA). destruct HA as [HA _].
assert (A : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs_i r).
{ intros n r Hn Hr'. rewrite HA by lia. exact (ew_Ereg_nat regs_i _ n r Hr'). }
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
assert (KEEP : forall (r : bv 5) n, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> sr_get (ss_regs ss') r = SOff n 0 ->
  getr (ms_regs ms') r = getr regs_i r).
{ intros r n Hn Hr' He. rewrite (RG _ _ He). cbn [sv_denot]. rewrite (A n r Hn Hr'), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
split; [lia|]. split; [exact HJ'|]. split; [exact (same_io_trans _ _ _ Hio Hio')|].
split; [rewrite (KEEP 10%bv 10%nat ltac:(lia) eq_refl S10); exact R10|].
split; [rewrite (RG _ _ S13), (cv_denot_off E' 13 (3 * i) 3 (eq_trans (A 13%nat 13%bv ltac:(lia) eq_refl) R13)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (KEEP 14%bv 14%nat ltac:(lia) eq_refl S14); exact R14|].
split; [rewrite (RG _ _ S15); cbn [sv_denot]; rewrite HA by lia; rewrite (ew_Ereg_extra regs_i _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (KEEP 16%bv 16%nat ltac:(lia) eq_refl S16); exact R16|].
split; [rewrite (RG _ _ S17); reflexivity|].
split; [rewrite (RG _ _ S5); reflexivity|].
split; [rewrite (KEEP 2%bv 2%nat ltac:(lia) eq_refl S2); exact R2|].
split; [rewrite (KEEP 1%bv 1%nat ltac:(lia) eq_refl S1); exact R1|].
split; [intros r Hcs Hr2; rewrite (cv_cs_kept _ _ _ _ _ _ 36 HS HA0 ltac:(lia) Scs r Hcs Hr2); exact (Rcs r Hcs Hr2)|].
split.
- apply (cv_val_kept _ mem_i (ms_mem ms') _ 8 _ Hslot). intros j Hj. apply K'. lia.
- intros a Ha Hn. rewrite (K' a Ha). exact (KE a Ha Hn).
Qed.

(* ---- the `ret` of the last cell: the contract's post ---- *)
Lemma cvu_leaf : forall i regs_i mem_i md_i ch v E' ss' ms' md',
  cvu_inv i regs_i mem_i md_i ->
  st_ok rsegs E' ss' (restrict (w_H W) ms') ->
  env_agree 36 (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) E' ->
  ss_pc ss' = CVU_RET -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 2 = SOff 2 16 -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io md_i md' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem_i a) ->
  SRr rsegs W (mkCfg ms' md') cvu_post.
Proof.
intros i regs_i mem_i md_i ch v E' ss' ms' md' HI HS HA Hpc Hrv S2 S1 Scs HJ' Hio' K'.
destruct HI as (Hi & _ & Hio & _ & _ & _ & _ & _ & _ & _ & R2 & R1 & Rcs & _ & KE).
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
assert (HA35 := HA). destruct HA as [HA _].
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
assert (G1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (RG _ _ S1). cbn [sv_denot]. rewrite HA by lia. rewrite (ew_Ereg_nat regs_i _ 1 1%bv eq_refl), R1, Z.add_0_r.
  apply Z_to_bv_bv_unsigned. }
assert (G2 : getr (ms_regs ms') 2 = getr regs 2).
{ rewrite (RG _ _ S2). rewrite (cv_denot_off E' 2 (spZ regs - 16) 16) by (first [rewrite HA by lia; rewrite (ew_Ereg_nat regs_i _ 2 2%bv eq_refl); exact R2 | lia]).
  replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
eapply (SRr_ret_at rsegs cvu_tbl cvu_tbl_ok cvu_wx W E' ss' ms' md' cvu_post HS Hrv); [rewrite Hpc; exact cvu_ret_word|].
intros mat'. unfold cvu_post, hd_post.
exists fx, lyc, Sc, (ms_regs ms'), (ms_mem ms'), (with_vm_backing (m_vm_lazy md') mat' md').
split; [rewrite G1, Hrar; reflexivity|].
split; [reflexivity|].
split; [exact (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ')|].
split.
{ intros r Hr. destruct (Z.eq_dec r 2) as [->|Hr2]; [exact G2|].
  rewrite (cv_cs_kept _ _ _ _ _ _ 36 HS HA35 ltac:(lia) Scs r Hr Hr2). exact (Rcs r Hr Hr2). }
split; [exact G1|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ Hio Hio') (same_io_wvb_cv _ _ _))|].
split; [apply mo_le_refl; exact MTL|].
split; [|exact I].
intros a Ha Hn _. rewrite (K' a Ha). apply KE; [exact Ha|]. clear - Hn. unfold T_check_STK in Hn. lia.
Qed.

(* ---- the loop head after the entry run ---- *)
Lemma cvu_inv0 : forall E' ss' ms' md',
  st_ok rsegs E' ss' (restrict (w_H W) ms') -> env_agree 33 (Ereg regs cv_extra0) E' ->
  ss_pc ss' = CVU_LOOP -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 10 = SOff 10 0 -> sr_get (ss_regs ss') 13 = SLit 0 ->
  sr_get (ss_regs ss') 14 = SAlu ALU_XOR (SOff 10 0) (SLit (-1)) -> sr_get (ss_regs ss') 15 = SOff 32 0 ->
  sr_get (ss_regs ss') 16 = SMd M_MUL (SOff 11 0) (SLit 3) -> sr_get (ss_regs ss') 17 = SLit 47 ->
  sr_get (ss_regs ss') 5 = SLit 2 ->
  sr_get (ss_regs ss') 2 = SOff 2 (-16) -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  nth_error (ss_mem ss') 0 = Some (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io mdc md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) memc a) ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 CVU_LOOP) (ms_mem ms') (seg_rom rsegs) /\
  cvu_inv 0 (ms_regs ms') (ms_mem ms') md'.
Proof.
intros E' ss' ms' md' HS HA Hpc Hrv S10 S13 S14 S15 S16 S17 S5 S2 S1 Scs Hm0 HJ' Hio' K'.
pose proof cvu_rng as Hr.
split; [rewrite <- Hpc; exact (st_ok_restrict_mkst rsegs _ _ _ _ HS Hrv)|].
assert (HA0 := HA). destruct HA as [HA _].
assert (A : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs r).
{ intros n r Hn Hr'. rewrite HA by lia. exact (ew_Ereg_nat regs _ n r Hr'). }
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
assert (KEEP : forall (r : bv 5) n, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> sr_get (ss_regs ss') r = SOff n 0 ->
  getr (ms_regs ms') r = getr regs r).
{ intros r n Hn Hr' He. rewrite (RG _ _ He). cbn [sv_denot]. rewrite (A n r Hn Hr'), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (A1 : ew E' 1 = Z_to_bv 64 (raZ regs)) by (rewrite (A 1%nat 1%bv ltac:(lia) eq_refl); apply cv_bv_of).
assert (A2 : ew E' 2 = Z_to_bv 64 (spZ regs)) by (rewrite (A 2%nat 2%bv ltac:(lia) eq_refl); apply cv_bv_of).
assert (A10 : ew E' 10 = Z_to_bv 64 o) by (rewrite (A 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (A11 : ew E' 11 = Z_to_bv 64 rcc) by (rewrite (A 11%nat 11%bv ltac:(lia) eq_refl); exact H11).
pose proof (cv_u64 (getr regs 1)) as Hra64.
split; [lia|]. split; [exact HJ'|]. split; [exact Hio'|].
split; [rewrite (KEEP 10%bv 10%nat ltac:(lia) eq_refl S10); exact H10|].
split; [rewrite (RG _ _ S13); reflexivity|].
split; [rewrite (RG _ _ S14), denot_lit_U; unfold w64; f_equal; rewrite U_SAlu; cbn [zalu_raw];
        rewrite (U_atom _ 10 o A10) by lia; rewrite U_SLit; change (zcanon (-1)) with (2 ^ 64 - 1);
        rewrite cvu_lxor_ones by lia; apply zcanon_id; unfold M64; lia|].
split; [rewrite (RG _ _ S15); cbn [sv_denot]; rewrite HA by lia; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RG _ _ S16), denot_lit_U; unfold w64; f_equal; rewrite U_SMd; cbn [zmd_raw];
        rewrite (U_atom _ 11 rcc A11) by lia; rewrite U_SLit; change (zcanon 3) with 3;
        unfold zcanon, M64; rewrite Z.mod_small by lia; lia|].
split; [rewrite (RG _ _ S17); reflexivity|].
split; [rewrite (RG _ _ S5); reflexivity|].
split; [rewrite (RG _ _ S2), (cv_denot_off E' 2 (spZ regs) (-16) A2) by lia; reflexivity|].
split; [rewrite (RG _ _ S1), (cv_denot_off E' 1 (raZ regs) 0 A1) by (unfold raZ; lia); rewrite Z.add_0_r; unfold raZ; apply Z_to_bv_bv_unsigned|].
split; [intros r Hcs Hr2; exact (cv_cs_kept _ _ _ _ _ _ 33 HS HA0 ltac:(lia) Scs r Hcs Hr2)|].
split; [|exact K'].
pose proof (cv_region_at E' ss' (restrict (w_H W) ms') 0 _ HS Hm0) as (_ & _ & _ & Hcs).
cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite A2, unsigned_lit_small in Hcs by lia.
apply Forall_inv in Hcs.
pose proof (val_of_chunk_ok rsegs E' _ (spZ regs) (-8) 8 (SOff 1 0) (raZ regs) Hcs) as Hv.
replace (spZ regs + -8) with (spZ regs - 8) in Hv by lia.
apply Hv.
- rewrite (cv_denot_off E' 1 (raZ regs) 0 A1) by (unfold raZ; lia). rewrite Z.add_0_r. reflexivity.
- unfold raZ. cbn. lia.
- lia.
Qed.

(* ---- one cell: the next loop head, or the `ret` after the last cell ---- *)
Ltac cvu_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ P LIM :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAE := fresh "HAE" in
  pose proof (cvu_it_entry i ch P v LIM true regs_i mem_i md_i HI0 Hnth ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia)) as HS;
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) (mrestrict (w_H W) mem_i)) by constructor;
  assert (HAE : env_agree 36 (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) (Ereg regs_i (cvu_extra (o + 3 * i) ch v))) by apply env_agree_refl;
  aj_run_tok cvu_tbl_ok HS HJ SHOK cv_Bspan;
  try solve [cbn [ms_mem mkst]; eapply cvu_obl; [exact HI0 | lia]];
  try solve [awr_ok_tac];
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem_i) (mrestrict _ (ms_mem ?msx)) |- _ =>
    let K1 := fresh "K1" in
    pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ mem_i mem_i (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_nowr)) as K1;
    eapply SRr_mono;
    [ eapply (cvu_leaf i regs_i mem_i md_i ch v _ _ msx _ HI0 HS);
      [ cv_agree HAE | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
      | exact HJ | apply same_io_wvb_cv | intros a Ha; exact (K1 a Ha (fun x => x)) ]
    | intros W'' c'' _ HQ; left; exact HQ ]
  end.
Ltac cvu_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl P LIM :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAE := fresh "HAE" in
  pose proof (cvu_it_entry i ch P v LIM false regs_i mem_i md_i HI0 Hnth ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia)) as HS;
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) (mrestrict (w_H W) mem_i)) by constructor;
  assert (HAE : env_agree 36 (Ereg regs_i (cvu_extra (o + 3 * i) ch v)) (Ereg regs_i (cvu_extra (o + 3 * i) ch v))) by apply env_agree_refl;
  aj_run_to_tok cvu_tbl_ok HS HJ SHOK cv_Bspan CVU_LATCH;
  try solve [cbn [ms_mem mkst]; eapply cvu_obl; [exact HI0 | lia]];
  try solve [awr_ok_tac];
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem_i) (mrestrict _ (ms_mem ?msx)) |- _ =>
    let K1 := fresh "K1" in
    pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ mem_i mem_i (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_nowr)) as K1;
    clear HFr;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
    aj_run_to_tok cvu_tbl_ok HS HJ SHOK cv_Bspan CVU_LOOP;
    try solve [awr_ok_tac];
    lazymatch goal with HFr2 : frame_of _ _ (mrestrict _ (ms_mem msx)) (mrestrict _ (ms_mem ?msy)) |- _ =>
      let K2 := fresh "K2" in
      pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ (ms_mem msx) (ms_mem msx) (ms_mem msy) (fun a _ _ => eq_refl) HFr2 ltac:(cv_nowr)) as K2;
      lazymatch goal with |- SRr _ _ (mkCfg _ ?mdy) _ =>
        let Hn := fresh "Hn" in
        assert (Hn : msy = mkst (ms_regs msy) (Z_to_bv 64 CVU_LOOP) (ms_mem msy) (seg_rom rsegs) /\
                     cvu_inv (i + 1) (ms_regs msy) (ms_mem msy) mdy);
        [ eapply (cvu_next i regs_i mem_i md_i ch v _ _ msy mdy HI0 Hl HS);
          [ cv_agree HAE | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
          | exact HJ | first [apply same_io_wvb_cv | eapply same_io_trans; apply same_io_wvb_cv]
          | intros a Ha; rewrite (K2 a Ha (fun x => x)); exact (K1 a Ha (fun x => x)) ]
        | apply SRr_ret; right; exists (i + 1); split; [lia|]; split; [reflexivity|];
          exists (ms_regs msy), (ms_mem msy), mdy; split; [f_equal; exact (proj1 Hn) | exact (proj2 Hn)] ]
      end
    end
  end.

Lemma cvu_step : forall i W' c, cvu_P i W' c ->
  SRr rsegs W' c (fun W'' c'' => cvu_post W'' c'' \/ exists i', 0 <= rcc - i' < rcc - i /\ cvu_P i' W'' c'').
Proof.
intros i W' c (-> & regs_i & mem_i & md_i & -> & HI0).
pose proof HI0 as (Hi & HJ & _).
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
assert (Hlt : (Z.to_nat i < length cs)%nat) by lia.
destruct (nth_error cs (Z.to_nat i)) as [[[ch p] v]|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
pose proof (proj1 (Forall_forall _ _) Hval _ (nth_error_In _ _ Hnth)) as Hcv.
unfold Headamp.cell_valid, Headamp.HA_CHANNELS, Headamp.HA_SENS, Headamp.HA_SENS_MAX in Hcv.
destruct Hcv as (Hch & Hp & Hv).
assert (Hp3 : p = 0 \/ p = 1 \/ p = 2) by lia.
destruct (Z.eq_dec (rcc - i) 1) as [Hl|Hl]; destruct Hp3 as [-> | [-> | ->]]; cbn in Hv.
- cvu_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ 0 1.
- cvu_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ 1 1.
- cvu_last_case i regs_i mem_i md_i ch v HI0 Hnth HJ 2 55.
- assert (Hl2 : 2 <= rcc - i) by lia. cvu_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl2 0 1.
- assert (Hl2 : 2 <= rcc - i) by lia. cvu_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl2 1 1.
- assert (Hl2 : 2 <= rcc - i) by lia. cvu_mid_case i regs_i mem_i md_i ch v HI0 Hnth HJ Hl2 2 55.
Qed.

Lemma cvu_loop : forall i regs_i mem_i md_i, cvu_inv i regs_i mem_i md_i ->
  SRr rsegs W (mkCfg (mkst regs_i (Z_to_bv 64 CVU_LOOP) mem_i (seg_rom rsegs)) md_i) cvu_post.
Proof.
intros i regs_i mem_i md_i HI.
apply (SRr_loopZ rsegs Z (fun i => rcc - i) cvu_P cvu_post cvu_step i W).
split; [reflexivity|]. exists regs_i, mem_i, md_i. split; [reflexivity | exact HI].
Qed.

(* ---- rc > 0: the entry run to the loop head, then the loop ---- *)
Lemma cvu_pos : SRr rsegs W (cfg_at rsegs A_CHECK_CELLS_VALID_B regs memc mdc) cvu_post.
Proof.
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
assert (B2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs cv_extra0) (mrestrict (w_H W) memc)) by constructor.
pose proof (cvu_entry0 true W regs memc rcc Hpres16 Hsp Hal16 Vgot Vcell H11 ltac:(lia) ltac:(cbn; lia)) as HS.
pose proof HJ0 as HJ.
unfold cfg_at. change (w64 A_CHECK_CELLS_VALID_B) with (Z_to_bv 64 A_CHECK_CELLS_VALID_B).
aj_run_to_tok cvu_tbl_ok HS HJ SHOK cv_Bspan CVU_LOOP; [cv_awr B2 | ].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
  pose proof (cv_kept_run (segs := rsegs) (fun a => spZ regs - 16 <= a < spZ regs) _ _ _ memc memc (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_kwr B2)) as K1;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    destruct (cvu_inv0 _ _ msx mdx HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl HJ (same_io_wvb_cv _ _ _) K1) as [Hshape HI];
    rewrite Hshape; exact (cvu_loop 0 _ _ _ HI)
  end
end.
Qed.
End loop.

Theorem hd_check_cells_valid_B : hd_check_cells_valid_specX rsegs B MT A_CHECK_CELLS_VALID_B.
Proof using MTL HBgot HBcell.
unfold hd_check_cells_valid_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc o cs
  (HJ & Hrar & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 Hrc Hpre.
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_check_STK in Hwlo.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBcell in Kcell. rewrite HBgot, HBcell in Kgot.
pose proof (val_mem_of_rdword rsegs _ _ _ _ Kgot) as Vgot.
pose proof (val_mem_of_rdword rsegs _ _ _ _ Kcell) as Vcell.
assert (Hpres16 : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
destruct (Z_lt_le_dec 0 rcc) as [Hpos | Hnpos].
- destruct (Hpre Hpos) as (Hlen & Hval & Ho0 & Ho63 & Hg & Hra & Hoff & Happ).
  assert (Hrc' : 0 < rcc < 2 ^ 31) by lia.
  eapply cvu_pos with (rcc := rcc) (o := o) (cs := cs); eassumption.
- assert (B2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs cv_extra0) (mrestrict (w_H W) memc)) by constructor.
  pose proof (cvu_entry0 false W regs memc rcc Hpres16 Hsp Hal16 Vgot Vcell H11 Hrc ltac:(cbn; lia)) as HS.
  unfold cfg_at. change (w64 A_CHECK_CELLS_VALID_B) with (Z_to_bv 64 A_CHECK_CELLS_VALID_B).
  aj_run_tok cvu_tbl_ok HS HJ SHOK cv_Bspan; [cv_awr B2 | ].
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (cv_kept_run (segs := rsegs) (fun a => spZ regs - 16 <= a < spZ regs) _ _ _ memc memc (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_kwr B2)) as K1;
    eapply (SRr_ret_at rsegs cvu_tbl cvu_tbl_ok cvu_wx W _ _ msx _ _ HS eq_refl); [vm_compute; reflexivity|];
    let mat' := fresh "mat" in intros mat';
    lazymatch goal with |- _ _ (mkCfg _ (with_vm_backing _ _ ?mdx)) =>
      red; exists fx, lyc, Sc, (ms_regs msx), (ms_mem msx), (with_vm_backing (m_vm_lazy mdx) mat' mdx);
      let S1 := fresh "S1" in
      lazymatch type of HS with st_ok _ _ ?ssx _ =>
        assert (S1 : sr_get (ss_regs ssx) 1%bv = SOff 1 0) by (vm_compute; reflexivity) end;
      assert (G1 : getr (ms_regs msx) 1 = getr regs 1)
        by (rewrite (st_ok_restrict_reg rsegs _ _ _ _ 1%bv HS), S1; cbn [sv_denot];
            rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned);
      split; [rewrite G1, Hrar; reflexivity|];
      split; [reflexivity|];
      split; [exact (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ)|];
      split; [eapply aregs_preserved_of_st_ok; [exact HS | apply env_agree_refl | vm_compute; reflexivity]|];
      split; [exact G1|];
      split; [reflexivity|];
      split; [apply Permutation_refl|];
      split; [first [apply same_io_wvb_cv | eapply same_io_trans; apply same_io_wvb_cv]|];
      split; [apply mo_le_refl; exact MTL|];
      split; [|exact I];
      intros a Ha Hn _; apply K1; [exact Ha | clear - Hn; unfold T_check_STK in Hn; lia]
    end
  end.
Qed.
End w.

Print Assumptions hd_check_cells_valid_B.
