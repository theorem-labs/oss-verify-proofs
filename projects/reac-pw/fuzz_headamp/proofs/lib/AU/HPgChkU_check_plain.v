(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgChk_check_plain.v (this branch) for image B (fuzz_headamp.asan-ubsan): it walks image B's check_plain 0x844cc against the same text lib/A/HPgCSpec.v hd_check_plain_specX on lib/AU/Img0U.v rsegs. Image B adds two UBSan pointer-overflow traps per pair (bltu ~out,j and bltu ~first,j), decided from the facts of ~out, ~first and j; the loop head is the first trap check 0x844fc. The state pieces cp_extra / cp_out / cp_first / cp_alias / cp_facts0 are image A's (segment-free), the segment-generic lemmas and tactics come from lib/A/HPgChk_check_cells_valid.v, image B's .got / cell regions from lib/AU/HPgChkU_check_cells_valid.v. *)
(* check_plain 0x844cc of fuzz_headamp.asan-ubsan (pinned sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94;
   addresses read on the unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff), 90 words:
     0x844cc addi sp,sp,-0x10; sd ra,8(sp); 0x844d4 bne a0,a1,0x84604 (abort); 0x844d8 blez a0,0x845f8;
     a5 := 0; auipc a1; ld a1,0x310(a1) (the GOT word 0x9c7f0 of the cell 0xa5238); ld a6,0(a1); a7 := ~a2 (~out);
       t0 := 3 a0; t1 := ~a3 (~first);
     loop 0x844fc: bltu a7,a5,0x8460c and 0x84500 bltu t1,a5,0x8460c (the UBSan traps, `unimp`); a0 := a2 + a5;
       the shadow check of a0 (lb 0x84510); a1 := a3 + a5; the shadow check of a1 (lb 0x84524); lbu a4 = out[j];
       lbu t2 = first[j]; 0x84534 bne a4,t2 -> abort; the same for j + 1 (lb 0x84544, 0x84558; 0x84568 bne) and
       j + 2 (lb 0x84578, 0x8458c; 0x8459c bne), every slow block of the blt form; a5 += 3;
       0x845a4 bne t0,a5,0x844fc; j 0x845f8;
     0x845f8 ld ra,8(sp); addi sp,sp,0x10; 0x84600 ret; 0x84604 jal __asan_handle_no_return; jal abort; 0x8460c unimp.
   WHY THE TRAPS AND THE ABORT ARE UNREACHABLE: hd_app_rng bounds out and first by [4096, 0x7fffff800000 - 3 rc], so
   ~out and ~first are at least 2^64 - 1 - 0x7fffff800000 while a5 = 3 i < 3 (2^31 - 1): the facts decide both traps
   not taken; the `bne` of the byte pairs and the entry `bne a0,a1` are decided as on image A. THE LOOP: the
   invariant at 0x844fc after i pairs: a2 = out, a3 = first, a5 = 3 i, a6 = the shadow offset, a7 = ~out, t0 = 3 rc,
   t1 = ~first, with image A's frame and memory clauses; the last pair holds t0 as a5 + 3, the others carry the
   condition t0 <> a5 + 3. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgChk_check_cells_valid HPgChk_check_plain.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgChkU_check_cells_valid.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image B: the function, its loop head (the first trap check), its latch, its `ret` ---- *)
Definition A_CHECK_PLAIN_B : Z := 0x844cc.
Definition CPU_LOOP : Z := 0x844fc.
Definition CPU_LATCH : Z := 0x845a4.
Definition CPU_RET : Z := 0x84600.
(* the 90 words 0x844cc .. 0x84630 *)
Definition cpu_tbl : ctable := build_table rsegs A_CHECK_PLAIN_B 90 TEmpty.
Lemma cpu_tbl_ok : table_ok rsegs cpu_tbl.
Proof. apply build_table_ok0. unfold A_CHECK_PLAIN_B. lia. Qed.
Lemma cpu_ret_word : clookup cpu_tbl CPU_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.

(* ---- the entry state at 0x844cc (image A's facts cp_facts0, image B's .got word and cell) ---- *)
Definition cpu_ss0 (pos : bool) : sstate :=
  mkSS A_CHECK_PLAIN_B (cv_sr_of [((11%bv : bv 5), SOff 10 0)]) cvu_regions0 None (cp_facts0 pos).

(* ---- the entry state of one cell pair at the loop head 0x844fc ---- *)
Definition cpu_ov (last : bool) : list (bv 5 * sv) :=
  [((16%bv : bv 5), SOff 32 0)] ++ (if last then [((5%bv : bv 5), SOff 15 3)] else []).
Definition cpu_facts (last : bool) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 16) (2 ^ 47 - 16) 4); (6%nat, mkAF NOT_LO NOT_HI 0);
           (15%nat, mkAF 0 (3 * (2 ^ 31 - 2)) 0); (17%nat, mkAF NOT_LO NOT_HI 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 0x7fffff800000 0); (34%nat, mkAF 4096 0x7fffff800000 0)]
          (if last then [] else [mkAC BC_NE (SOff 5 0) (SOff 15 3)]) cp_alias.
Definition cpu_ss (last : bool) : sstate :=
  mkSS CPU_LOOP (cv_sr_of (cpu_ov last)) [cv_stk; cp_out; cp_first] None (cpu_facts last).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cpu_entry0 : forall (pos : bool) (W : world rsegs) regs memc rcc,
  (forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) B_GOT_SHADOW 8 B_SHADOW_CELL ->
  val_mem rsegs (mrestrict (w_H W) memc) B_SHADOW_CELL 8 SHADOW_OFF ->
  getr regs 10 = w64 rcc -> getr regs 11 = w64 rcc -> - 2 ^ 31 <= rcc < 2 ^ 31 ->
  (if pos then 0 < rcc else rcc <= 0) ->
  st_ok rsegs (Ereg regs cv_extra0) (cpu_ss0 pos)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHECK_PLAIN_B) memc (seg_rom rsegs))).
Proof.
intros pos W regs memc rcc Hpres Hsp Hal Vgot Vcell H10 H11 Hrc Hpos.
rewrite restrict_mkst_fx. unfold cpu_ss0.
assert (E2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew (Ereg regs cv_extra0) 10 = Z_to_bv 64 rcc) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew (Ereg regs cv_extra0) 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ew_Ereg_extra regs _ 0)).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
apply entry_st_ok_full.
- apply cv_regs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split.
  + let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz.
  + cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact H11.
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
- destruct pos; unfold cp_facts0; split; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E10, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + split; exact I.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E32, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
  + split; [|exact I]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite YO0c.branch_ge. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
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
(* image A's symbol record holds the shadow-offset GOT word and cell (both read by check_plain at entry) *)
Hypothesis HBgot : as_got_shadow B = B_GOT_SHADOW.
Hypothesis HBcell : as_shadow_cell B = B_SHADOW_CELL.

Section loop.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (rcc o fp : Z) (w : list Z).
Hypothesis Hrc : 0 < rcc < 2 ^ 31.
Hypothesis Hlen : Z.of_nat (length w) = 3 * rcc.
Hypothesis Hgo : garr8 rsegs (mrestrict (w_H W) memc) o w.
Hypothesis Hgf : garr8 rsegs (mrestrict (w_H W) memc) fp w.
Hypothesis Hrao : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o (3 * rcc).
Hypothesis Hraf : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF fp (3 * rcc).
Hypothesis Hoffo : hd_off_stack regs T_check_STK o (3 * rcc).
Hypothesis Hofff : hd_off_stack regs T_check_STK fp (3 * rcc).
Hypothesis Happo : hd_app_rng rsegs o (3 * rcc).
Hypothesis Happf : hd_app_rng rsegs fp (3 * rcc).
Hypothesis Hapart : o + 3 * rcc <= fp \/ fp + 3 * rcc <= o.
Hypothesis Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47.
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis Hrar : YK0s.ret_ok (getr regs 1).
Hypothesis H10 : getr regs 10 = w64 rcc.
Hypothesis H11 : getr regs 11 = w64 rcc.
Hypothesis H12 : getr regs 12 = w64 o.
Hypothesis H13 : getr regs 13 = w64 fp.
Hypothesis HJ0 : ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hwlo : sp0 - STK <= spZ regs - 32.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hpres16 : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a.
Hypothesis Vgot : val_mem rsegs (mrestrict (w_H W) memc) B_GOT_SHADOW 8 B_SHADOW_CELL.
Hypothesis Vcell : val_mem rsegs (mrestrict (w_H W) memc) B_SHADOW_CELL 8 SHADOW_OFF.

Definition cpu_post : world rsegs -> config -> Prop :=
  hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
    (fun f => f = fx) (fun _ => False) (fun _ _ _ => True).

(* the loop head after i cell pairs *)
Definition cpu_inv (i : Z) (regs_i : bvmap 5 word) (mem_i : word -> option byte) (md_i : Model) : Prop :=
  0 <= i < rcc /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem_i md_i k /\
  same_io mdc md_i /\
  getr regs_i 12 = w64 o /\ getr regs_i 13 = w64 fp /\ getr regs_i 15 = w64 (3 * i) /\
  getr regs_i 16 = w64 SHADOW_OFF /\ getr regs_i 17 = w64 (2 ^ 64 - 1 - o) /\ getr regs_i 5 = w64 (3 * rcc) /\
  getr regs_i 6 = w64 (2 ^ 64 - 1 - fp) /\
  getr regs_i 2 = w64 (spZ regs - 16) /\ getr regs_i 1 = getr regs 1 /\
  (forall r, acallee_saved r -> r <> 2 -> getr regs_i (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  val_mem rsegs (mrestrict (w_H W) mem_i) (spZ regs - 8) 8 (raZ regs) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a).
Definition cpu_P (i : Z) (W' : world rsegs) (c : config) : Prop :=
  W' = W /\ exists regs_i mem_i md_i,
  c = mkCfg (mkst regs_i (Z_to_bv 64 CPU_LOOP) mem_i (seg_rom rsegs)) md_i /\ cpu_inv i regs_i mem_i md_i.

(* ---- the two checked ranges, as the premises give them ---- *)
Lemma cpu_rng : forall p, hd_app_rng rsegs p (3 * rcc) -> 4096 <= p /\ p + 3 * rcc <= 0x7fffff800000.
Proof.
intros p ([H0 Hr] & _). pose proof ASAN_CEIL_range as [CR _].
unfold kLowShadowBeg, kHighMemBeg in Hr. lia.
Qed.
Lemma cpu_g_at : forall p mem_i,
  hd_app_rng rsegs p (3 * rcc) -> hd_off_stack regs T_check_STK p (3 * rcc) ->
  garr8 rsegs (mrestrict (w_H W) memc) p w ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a) ->
  garr8 rsegs (mrestrict (w_H W) mem_i) p w.
Proof.
intros p mem_i Hap Hof Hg KE j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
pose proof (cpu_rng p Hap) as Hr.
apply (cv_val_kept _ memc mem_i _ 1 _ Hv). intros jj Hjj. assert (jj = 0%nat) by lia. subst jj.
apply KE; [lia|]. pose proof (Hof (p + Z.of_nat j) ltac:(lia)). unfold T_check_STK in *. lia.
Qed.
Lemma cpu_ra_at : forall p mem_i,
  hd_app_rng rsegs p (3 * rcc) ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p (3 * rcc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) mem_i a = aview rsegs (w_H W) memc a) ->
  range_addressable (aview rsegs (w_H W) mem_i) SHADOW_OFF p (3 * rcc).
Proof.
intros p mem_i Hap Hra KE. apply (cv_ra_kept _ memc mem_i _ _ Hra). intros x Hx.
pose proof (cpu_rng p Hap) as Hr. unfold shadow_of_addr.
assert (Hq : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply KE; unfold SHADOW_OFF; lia.
Qed.

(* ---- the six obligations of a pair's run: range_addressable (out + 3 i + c, 1), (first + 3 i + c, 1) ---- *)
Lemma cpu_obl : forall i regs_i mem_i md_i b0 b1 b2 (n : nat) c,
  cpu_inv i regs_i mem_i md_i -> (n = 33%nat \/ n = 34%nat) -> 0 <= c < 3 ->
  range_addressable (rd_of rsegs (mrestrict (w_H W) mem_i))
    (U (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) cv_Bx)
    (U (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) (SOff n c)) 1.
Proof.
intros i regs_i mem_i md_i b0 b1 b2 n c HI Hn Hc.
destruct HI as (Hi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KE).
pose proof (cpu_rng o Happo) as Hro. pose proof (cpu_rng fp Happf) as Hrf.
assert (HB : U (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) cv_Bx = SHADOW_OFF).
{ unfold cv_Bx. apply (U_atom _ 32 SHADOW_OFF); [exact (ew_Ereg_extra regs_i _ 0) | unfold SHADOW_OFF; lia]. }
assert (E33 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 33 = Z_to_bv 64 (o + 3 * i)) by exact (ew_Ereg_extra regs_i _ 1).
assert (E34 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 34 = Z_to_bv 64 (fp + 3 * i)) by exact (ew_Ereg_extra regs_i _ 2).
destruct Hn as [-> | ->].
- rewrite (U_atom_off _ 33 (o + 3 * i) c E33) by lia.
  eapply obl_of_range; [exact (cpu_ra_at o mem_i Happo Hrao KE) | exact HB | lia | lia].
- rewrite (U_atom_off _ 34 (fp + 3 * i) c E34) by lia.
  eapply obl_of_range; [exact (cpu_ra_at fp mem_i Happf Hraf KE) | exact HB | lia | lia].
Qed.

(* ---- a pair's entry state ---- *)
Lemma cpu_it_entry : forall i (last : bool) regs_i mem_i md_i,
  cpu_inv i regs_i mem_i md_i ->
  (if last then rcc - i = 1 else 2 <= rcc - i) ->
  st_ok rsegs (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) (nth (Z.to_nat (3 * i)) w 0)
                  (nth (Z.to_nat (3 * i + 1)) w 0) (nth (Z.to_nat (3 * i + 2)) w 0)))
    (cpu_ss last) (restrict (w_H W) (mkst regs_i (Z_to_bv 64 CPU_LOOP) mem_i (seg_rom rsegs))).
Proof.
intros i last regs_i mem_i md_i HI Hl.
destruct HI as (Hi & _ & _ & R12 & R13 & R15 & R16 & R17 & R5 & R6 & R2 & R1 & _ & Hslot & KE).
pose proof (cpu_rng o Happo) as Hro. pose proof (cpu_rng fp Happf) as Hrf.
set (b0 := nth (Z.to_nat (3 * i)) w 0). set (b1 := nth (Z.to_nat (3 * i + 1)) w 0). set (b2 := nth (Z.to_nat (3 * i + 2)) w 0).
pose proof (cpu_g_at o mem_i Happo Hoffo Hgo KE) as Gio. pose proof (cpu_g_at fp mem_i Happf Hofff Hgf KE) as Gif.
assert (Hj : forall j, 0 <= j < 3 -> (Z.to_nat (3 * i + j) < length w)%nat) by (intros j Hj0; lia).
assert (Hj0 : (Z.to_nat (3 * i) < length w)%nat) by lia.
destruct (Gio (Z.to_nat (3 * i)) Hj0) as [Vo0 Hb0].
destruct (Gio (Z.to_nat (3 * i + 1)) (Hj 1 ltac:(lia))) as [Vo1 Hb1].
destruct (Gio (Z.to_nat (3 * i + 2)) (Hj 2 ltac:(lia))) as [Vo2 Hb2].
destruct (Gif (Z.to_nat (3 * i)) Hj0) as [Vf0 _].
destruct (Gif (Z.to_nat (3 * i + 1)) (Hj 1 ltac:(lia))) as [Vf1 _].
destruct (Gif (Z.to_nat (3 * i + 2)) (Hj 2 ltac:(lia))) as [Vf2 _].
fold b0 b1 b2 in Vo0, Vo1, Vo2, Vf0, Vf1, Vf2, Hb0, Hb1, Hb2.
rewrite Z2Nat.id in Vo0, Vo1, Vo2, Vf0, Vf1, Vf2 by lia.
rewrite restrict_mkst_fx. unfold cpu_ss.
assert (E1 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 1 = getr regs 1)
  by (rewrite (ew_Ereg_nat regs_i _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 2 = Z_to_bv 64 (spZ regs - 16))
  by (rewrite (ew_Ereg_nat regs_i _ 2 2%bv eq_refl); exact R2).
assert (E12 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 12 = Z_to_bv 64 o)
  by (rewrite (ew_Ereg_nat regs_i _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 13 = Z_to_bv 64 fp)
  by (rewrite (ew_Ereg_nat regs_i _ 13 13%bv eq_refl); exact R13).
assert (E15 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 15 = Z_to_bv 64 (3 * i))
  by (rewrite (ew_Ereg_nat regs_i _ 15 15%bv eq_refl); exact R15).
assert (E5 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 5 = Z_to_bv 64 (3 * rcc))
  by (rewrite (ew_Ereg_nat regs_i _ 5 5%bv eq_refl); exact R5).
assert (E6 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 6 = Z_to_bv 64 (2 ^ 64 - 1 - fp))
  by (rewrite (ew_Ereg_nat regs_i _ 6 6%bv eq_refl); exact R6).
assert (E17 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 17 = Z_to_bv 64 (2 ^ 64 - 1 - o))
  by (rewrite (ew_Ereg_nat regs_i _ 17 17%bv eq_refl); exact R17).
assert (E32 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs_i _ 0).
assert (E33 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 33 = Z_to_bv 64 (o + 3 * i)) by exact (ew_Ereg_extra regs_i _ 1).
assert (E34 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 34 = Z_to_bv 64 (fp + 3 * i)) by exact (ew_Ereg_extra regs_i _ 2).
assert (E35 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 35 = Z_to_bv 64 b0) by exact (ew_Ereg_extra regs_i _ 3).
assert (E36 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 36 = Z_to_bv 64 b1) by exact (ew_Ereg_extra regs_i _ 4).
assert (E37 : ew (Ereg regs_i (cp_extra (o + 3 * i) (fp + 3 * i) b0 b1 b2)) 37 = Z_to_bv 64 b2) by exact (ew_Ereg_extra regs_i _ 5).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; lia).
apply entry_st_ok_full.
- apply cv_regs_ok. unfold cpu_ov.
  destruct last; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; split;
    try (let Hz := fresh "Hz" in intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  all: first
    [ rewrite (cv_denot_off _ 32 SHADOW_OFF 0 E32 HSB) by lia; rewrite Z.add_0_r; symmetry; exact R16
    | rewrite (cv_denot_off _ 15 (3 * i) 3 E15) by lia; rewrite R5; unfold w64; f_equal; lia ].
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, cv_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (spZ regs - 16) 8 8 (SOff 1 0) (raZ regs)).
    * rewrite (cv_denot_off _ 1 (raZ regs) 0) by (first [rewrite E1; apply cv_bv_of | apply cv_u64 | pose proof (cv_u64 (getr regs 1)); unfold raZ; lia]).
      rewrite Z.add_0_r. reflexivity.
    * pose proof (cv_u64 (getr regs 1)). unfold raZ. cbn. lia.
    * lia.
    * replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia. exact Hslot.
  + unfold region_ok, cp_out, cp_bytes. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val rsegs _ _ (o + 3 * i) 0 1 (SOff 35 0) b0); [rewrite (cv_denot_off _ 35 b0 0 E35) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      replace (o + 3 * i + 0) with (o + (3 * i)) by lia. exact Vo0.
    * apply (chunk_ok_val rsegs _ _ (o + 3 * i) 1 1 (SOff 36 0) b1); [rewrite (cv_denot_off _ 36 b1 0 E36) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      replace (o + 3 * i + 1) with (o + (3 * i + 1)) by lia. exact Vo1.
    * apply (chunk_ok_val rsegs _ _ (o + 3 * i) 2 1 (SOff 37 0) b2); [rewrite (cv_denot_off _ 37 b2 0 E37) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      replace (o + 3 * i + 2) with (o + (3 * i + 2)) by lia. exact Vo2.
  + unfold region_ok, cp_first, cp_bytes. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val rsegs _ _ (fp + 3 * i) 0 1 (SOff 35 0) b0); [rewrite (cv_denot_off _ 35 b0 0 E35) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      replace (fp + 3 * i + 0) with (fp + (3 * i)) by lia. exact Vf0.
    * apply (chunk_ok_val rsegs _ _ (fp + 3 * i) 1 1 (SOff 36 0) b1); [rewrite (cv_denot_off _ 36 b1 0 E36) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      replace (fp + 3 * i + 1) with (fp + (3 * i + 1)) by lia. exact Vf1.
    * apply (chunk_ok_val rsegs _ _ (fp + 3 * i) 2 1 (SOff 37 0) b2); [rewrite (cv_denot_off _ 37 b2 0 E37) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia |].
      replace (fp + 3 * i + 2) with (fp + (3 * i + 2)) by lia. exact Vf2.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, cv_stk, cp_out, cp_first.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E33, E34, !unsigned_lit_small by lia.
  pose proof (Hoffo (o + 3 * i) ltac:(lia)) as X0. pose proof (Hofff (fp + 3 * i) ltac:(lia)) as X1.
  unfold T_check_STK in X0, X1.
  split; [split; [lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; exact I]].
- unfold cpu_facts. split; [|split].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E6, E15, E17, E32, E33, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold NOT_LO, NOT_HI.
    repeat split; try lia; rewrite Zminus_mod, Hal16; reflexivity.
  + destruct last; cbn [f_conds conds_ok]; [exact I|]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ne_U, (U_atom _ 5 (3 * rcc) E5), (U_atom_off _ 15 (3 * i) 3 E15) by lia.
    apply negb_true_iff. apply Z.eqb_neq. lia.
  + cbn [f_alias cp_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 12 o E12), (U_atom _ 15 (3 * i) E15), (U_atom _ 33 (o + 3 * i) E33) by lia.
      apply zcanon_id. unfold M64. lia.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 13 fp E13), (U_atom _ 15 (3 * i) E15), (U_atom _ 34 (fp + 3 * i) E34) by lia.
      apply zcanon_id. unfold M64. lia.
Qed.

(* ---- the loop head after the next pair ---- *)
Lemma cpu_next : forall i regs_i mem_i md_i xe E' ss' ms' md',
  cpu_inv i regs_i mem_i md_i -> 2 <= rcc - i ->
  st_ok rsegs E' ss' (restrict (w_H W) ms') ->
  env_agree 38 (Ereg regs_i xe) E' ->
  ss_pc ss' = CPU_LOOP -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 12 = SOff 12 0 -> sr_get (ss_regs ss') 13 = SOff 13 0 ->
  sr_get (ss_regs ss') 15 = SOff 15 3 -> sr_get (ss_regs ss') 16 = SOff 32 0 ->
  sr_get (ss_regs ss') 17 = SOff 17 0 -> sr_get (ss_regs ss') 5 = SOff 5 0 ->
  sr_get (ss_regs ss') 6 = SOff 6 0 ->
  sr_get (ss_regs ss') 2 = SOff 2 0 -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io md_i md' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem_i a) ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 CPU_LOOP) (ms_mem ms') (seg_rom rsegs) /\
  cpu_inv (i + 1) (ms_regs ms') (ms_mem ms') md'.
Proof.
intros i regs_i mem_i md_i xe E' ss' ms' md' HI Hnl HS HA Hpc Hrv S12 S13 S15 S16 S17 S5 S6 S2 S1 E32 Scs HJ' Hio' K'.
destruct HI as (Hi & _ & Hio & R12 & R13 & R15 & R16 & R17 & R5 & R6 & R2 & R1 & Rcs & Hslot & KE).
pose proof (cpu_rng o Happo) as Hro.
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
split; [rewrite (KEEP 12%bv 12%nat ltac:(lia) eq_refl S12); exact R12|].
split; [rewrite (KEEP 13%bv 13%nat ltac:(lia) eq_refl S13); exact R13|].
split; [rewrite (RG _ _ S15), (cv_denot_off E' 15 (3 * i) 3 (eq_trans (A 15%nat 15%bv ltac:(lia) eq_refl) R15)) by lia; unfold w64; f_equal; lia|].
split; [rewrite (RG _ _ S16), (cv_denot_off E' 32 SHADOW_OFF 0 E32) by (unfold SHADOW_OFF; lia); rewrite Z.add_0_r; reflexivity|].
split; [rewrite (KEEP 17%bv 17%nat ltac:(lia) eq_refl S17); exact R17|].
split; [rewrite (KEEP 5%bv 5%nat ltac:(lia) eq_refl S5); exact R5|].
split; [rewrite (KEEP 6%bv 6%nat ltac:(lia) eq_refl S6); exact R6|].
split; [rewrite (KEEP 2%bv 2%nat ltac:(lia) eq_refl S2); exact R2|].
split; [rewrite (KEEP 1%bv 1%nat ltac:(lia) eq_refl S1); exact R1|].
split; [intros r Hcs Hr2; rewrite (cv_cs_kept _ _ _ _ _ _ 38 HS HA0 ltac:(lia) Scs r Hcs Hr2); exact (Rcs r Hcs Hr2)|].
split.
- apply (cv_val_kept _ mem_i (ms_mem ms') _ 8 _ Hslot). intros j Hj. apply K'. lia.
- intros a Ha Hn. rewrite (K' a Ha). exact (KE a Ha Hn).
Qed.

(* ---- the `ret` after the last pair: the contract's post ---- *)
Lemma cpu_leaf : forall i regs_i mem_i md_i xe E' ss' ms' md',
  cpu_inv i regs_i mem_i md_i ->
  st_ok rsegs E' ss' (restrict (w_H W) ms') ->
  env_agree 38 (Ereg regs_i xe) E' ->
  ss_pc ss' = CPU_RET -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 2 = SOff 2 16 -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io md_i md' ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) mem_i a) ->
  SRr rsegs W (mkCfg ms' md') cpu_post.
Proof.
intros i regs_i mem_i md_i xe E' ss' ms' md' HI HS HA Hpc Hrv S2 S1 Scs HJ' Hio' K'.
destruct HI as (Hi & _ & Hio & _ & _ & _ & _ & _ & _ & _ & R2 & R1 & Rcs & _ & KE).
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
assert (HA38 := HA). destruct HA as [HA _].
assert (RG : forall r e, sr_get (ss_regs ss') r = e -> getr (ms_regs ms') r = sv_denot E' e).
{ intros r e He. rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS), He. reflexivity. }
assert (G1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (RG _ _ S1). cbn [sv_denot]. rewrite HA by lia. rewrite (ew_Ereg_nat regs_i _ 1 1%bv eq_refl), R1, Z.add_0_r.
  apply Z_to_bv_bv_unsigned. }
assert (G2 : getr (ms_regs ms') 2 = getr regs 2).
{ rewrite (RG _ _ S2). rewrite (cv_denot_off E' 2 (spZ regs - 16) 16) by (first [rewrite HA by lia; rewrite (ew_Ereg_nat regs_i _ 2 2%bv eq_refl); exact R2 | lia]).
  replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
eapply (SRr_ret_at rsegs cpu_tbl cpu_tbl_ok cvu_wx W E' ss' ms' md' cpu_post HS Hrv); [rewrite Hpc; exact cpu_ret_word|].
intros mat'. unfold cpu_post, hd_post.
exists fx, lyc, Sc, (ms_regs ms'), (ms_mem ms'), (with_vm_backing (m_vm_lazy md') mat' md').
split; [rewrite G1, Hrar; reflexivity|].
split; [reflexivity|].
split; [exact (ajournal_materialize rsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ')|].
split.
{ intros r Hr. destruct (Z.eq_dec r 2) as [->|Hr2]; [exact G2|].
  rewrite (cv_cs_kept _ _ _ _ _ _ 38 HS HA38 ltac:(lia) Scs r Hr Hr2). exact (Rcs r Hr Hr2). }
split; [exact G1|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ Hio Hio') (same_io_wvb_cv _ _ _))|].
split; [apply mo_le_refl; exact MTL|].
split; [|exact I].
intros a Ha Hn _. rewrite (K' a Ha). apply KE; [exact Ha|]. clear - Hn. unfold T_check_STK in Hn. lia.
Qed.

(* ---- the loop head after the entry run ---- *)
Lemma cpu_inv0 : forall E' ss' ms' md',
  st_ok rsegs E' ss' (restrict (w_H W) ms') -> env_agree 33 (Ereg regs cv_extra0) E' ->
  ss_pc ss' = CPU_LOOP -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 12 = SOff 12 0 -> sr_get (ss_regs ss') 13 = SOff 13 0 ->
  sr_get (ss_regs ss') 15 = SLit 0 -> sr_get (ss_regs ss') 16 = SOff 32 0 ->
  sr_get (ss_regs ss') 17 = SAlu ALU_XOR (SOff 12 0) (SLit (-1)) -> sr_get (ss_regs ss') 5 = SMd M_MUL (SOff 10 0) (SLit 3) ->
  sr_get (ss_regs ss') 6 = SAlu ALU_XOR (SOff 13 0) (SLit (-1)) ->
  sr_get (ss_regs ss') 2 = SOff 2 (-16) -> sr_get (ss_regs ss') 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  nth_error (ss_mem ss') 0 = Some (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
  same_io mdc md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview rsegs (w_H W) (ms_mem ms') a = aview rsegs (w_H W) memc a) ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 CPU_LOOP) (ms_mem ms') (seg_rom rsegs) /\
  cpu_inv 0 (ms_regs ms') (ms_mem ms') md'.
Proof.
intros E' ss' ms' md' HS HA Hpc Hrv S12 S13 S15 S16 S17 S5 S6 S2 S1 Scs Hm0 HJ' Hio' K'.
pose proof (cpu_rng o Happo) as Hro.
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
assert (A10 : ew E' 10 = Z_to_bv 64 rcc) by (rewrite (A 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (A12 : ew E' 12 = Z_to_bv 64 o) by (rewrite (A 12%nat 12%bv ltac:(lia) eq_refl); exact H12).
assert (A13 : ew E' 13 = Z_to_bv 64 fp) by (rewrite (A 13%nat 13%bv ltac:(lia) eq_refl); exact H13).
pose proof (cpu_rng fp Happf) as Hrf.
pose proof (cv_u64 (getr regs 1)) as Hra64.
split; [lia|]. split; [exact HJ'|]. split; [exact Hio'|].
split; [rewrite (KEEP 12%bv 12%nat ltac:(lia) eq_refl S12); exact H12|].
split; [rewrite (KEEP 13%bv 13%nat ltac:(lia) eq_refl S13); exact H13|].
split; [rewrite (RG _ _ S15); reflexivity|].
split; [rewrite (RG _ _ S16); cbn [sv_denot]; rewrite HA by lia; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RG _ _ S17), denot_lit_U; unfold w64; f_equal; rewrite U_SAlu; cbn [zalu_raw];
        rewrite (U_atom _ 12 o A12) by lia; rewrite U_SLit; change (zcanon (-1)) with (2 ^ 64 - 1);
        rewrite cvu_lxor_ones by lia; apply zcanon_id; unfold M64; lia|].
split; [rewrite (RG _ _ S5), denot_lit_U; unfold w64; f_equal; rewrite U_SMd; cbn [zmd_raw];
        rewrite (U_atom _ 10 rcc A10) by lia; rewrite U_SLit; change (zcanon 3) with 3;
        unfold zcanon, M64; rewrite Z.mod_small by lia; lia|].
split; [rewrite (RG _ _ S6), denot_lit_U; unfold w64; f_equal; rewrite U_SAlu; cbn [zalu_raw];
        rewrite (U_atom _ 13 fp A13) by lia; rewrite U_SLit; change (zcanon (-1)) with (2 ^ 64 - 1);
        rewrite cvu_lxor_ones by lia; apply zcanon_id; unfold M64; lia|].
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

(* ---- one pair: the next loop head, or the `ret` after the last pair ---- *)
Ltac cpu_case i regs_i mem_i md_i HI0 HJ Hl LAST :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAE := fresh "HAE" in
  pose proof (cpu_it_entry i LAST regs_i mem_i md_i HI0 ltac:(cbv iota; lia)) as HS;
  lazymatch type of HS with st_ok _ ?E0 _ _ =>
    assert (SHOK : sh_ok rsegs cv_Bx [] E0 (mrestrict (w_H W) mem_i)) by constructor;
    assert (HAE : env_agree 38 E0 E0) by apply env_agree_refl
  end;
  lazymatch LAST with
  | true =>
    aj_run_tok cpu_tbl_ok HS HJ SHOK cv_Bspan;
    try solve [cbn [ms_mem mkst]; eapply cpu_obl; [exact HI0 | lia | lia]];
    try solve [awr_ok_tac];
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem_i) (mrestrict _ (ms_mem ?msx)) |- _ =>
      let K1 := fresh "K1" in
      pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ mem_i mem_i (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_nowr)) as K1;
      eapply SRr_mono;
      [ eapply (cpu_leaf i regs_i mem_i md_i _ _ _ msx _ HI0 HS);
        [ cv_agree HAE | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity
        | exact HJ | first [apply same_io_wvb_cv | eapply same_io_trans; apply same_io_wvb_cv]
        | intros a Ha; exact (K1 a Ha (fun x => x)) ]
      | intros W'' c'' _ HQ; left; exact HQ ]
    end
  | false =>
    aj_run_to_tok cpu_tbl_ok HS HJ SHOK cv_Bspan CPU_LATCH;
    try solve [cbn [ms_mem mkst]; eapply cpu_obl; [exact HI0 | lia | lia]];
    try solve [awr_ok_tac];
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem_i) (mrestrict _ (ms_mem ?msx)) |- _ =>
      let K1 := fresh "K1" in
      pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ mem_i mem_i (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_nowr)) as K1;
      clear HFr;
      repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
      aj_run_to_tok cpu_tbl_ok HS HJ SHOK cv_Bspan CPU_LOOP;
      try solve [awr_ok_tac];
      lazymatch goal with HFr2 : frame_of _ _ (mrestrict _ (ms_mem msx)) (mrestrict _ (ms_mem ?msy)) |- _ =>
        let K2 := fresh "K2" in
        pose proof (cv_kept_run (segs := rsegs) (fun _ => False) _ _ _ (ms_mem msx) (ms_mem msx) (ms_mem msy) (fun a _ _ => eq_refl) HFr2 ltac:(cv_nowr)) as K2;
        lazymatch goal with |- SRr _ _ (mkCfg _ ?mdy) _ =>
          let Hn := fresh "Hn" in
          assert (Hn : msy = mkst (ms_regs msy) (Z_to_bv 64 CPU_LOOP) (ms_mem msy) (seg_rom rsegs) /\
                       cpu_inv (i + 1) (ms_regs msy) (ms_mem msy) mdy);
          [ eapply (cpu_next i regs_i mem_i md_i _ _ _ msy mdy HI0 Hl HS);
            [ cv_agree HAE | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
            | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
            | lazymatch type of HAE with env_agree _ ?E0 _ =>
                lazymatch goal with |- ew ?E1 32 = _ =>
                  let HA2 := fresh "HA2" in
                  assert (HA2 : env_agree 38 E0 E1) by cv_agree HAE;
                  rewrite (proj1 HA2 32%nat ltac:(lia)); exact (ew_Ereg_extra regs_i _ 0)
                end end
            | vm_compute; reflexivity
            | exact HJ | first [apply same_io_wvb_cv | eapply same_io_trans; apply same_io_wvb_cv]
            | intros a Ha; rewrite (K2 a Ha (fun x => x)); exact (K1 a Ha (fun x => x)) ]
          | apply SRr_ret; right; exists (i + 1); split; [lia|]; split; [reflexivity|];
            exists (ms_regs msy), (ms_mem msy), mdy; split; [f_equal; exact (proj1 Hn) | exact (proj2 Hn)] ]
        end
      end
    end
  end.

Lemma cpu_step : forall i W' c, cpu_P i W' c ->
  SRr rsegs W' c (fun W'' c'' => cpu_post W'' c'' \/ exists i', 0 <= rcc - i' < rcc - i /\ cpu_P i' W'' c'').
Proof.
intros i W' c (-> & regs_i & mem_i & md_i & -> & HI0).
pose proof HI0 as (Hi & HJ & _).
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
destruct (Z.eq_dec (rcc - i) 1) as [Hl|Hl].
- cpu_case i regs_i mem_i md_i HI0 HJ Hl true.
- assert (Hl2 : 2 <= rcc - i) by lia. cpu_case i regs_i mem_i md_i HI0 HJ Hl2 false.
Qed.

Lemma cpu_loop : forall i regs_i mem_i md_i, cpu_inv i regs_i mem_i md_i ->
  SRr rsegs W (mkCfg (mkst regs_i (Z_to_bv 64 CPU_LOOP) mem_i (seg_rom rsegs)) md_i) cpu_post.
Proof.
intros i regs_i mem_i md_i HI.
apply (SRr_loopZ rsegs Z (fun i => rcc - i) cpu_P cpu_post cpu_step i W).
split; [reflexivity|]. exists regs_i, mem_i, md_i. split; [reflexivity | exact HI].
Qed.

(* ---- rc > 0: the entry run to the loop head, then the loop ---- *)
Lemma cpu_pos : SRr rsegs W (cfg_at rsegs A_CHECK_PLAIN_B regs memc mdc) cpu_post.
Proof.
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
assert (B2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs cv_extra0) (mrestrict (w_H W) memc)) by constructor.
pose proof (cpu_entry0 true W regs memc rcc Hpres16 Hsp Hal16 Vgot Vcell H10 H11 ltac:(lia) ltac:(cbn; lia)) as HS.
pose proof HJ0 as HJ.
unfold cfg_at. change (w64 A_CHECK_PLAIN_B) with (Z_to_bv 64 A_CHECK_PLAIN_B).
aj_run_to_tok cpu_tbl_ok HS HJ SHOK cv_Bspan CPU_LOOP; [cv_awr B2 | ].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
  pose proof (cv_kept_run (segs := rsegs) (fun a => spZ regs - 16 <= a < spZ regs) _ _ _ memc memc (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_kwr B2)) as K1;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    destruct (cpu_inv0 _ _ msx mdx HS (env_agree_refl _ _) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) eq_refl HJ (same_io_wvb_cv _ _ _) K1) as [Hshape HI];
    rewrite Hshape; exact (cpu_loop 0 _ _ _ HI)
  end
end.
Qed.
End loop.

Theorem hd_check_plain_B : hd_check_plain_specX rsegs B MT A_CHECK_PLAIN_B.
Proof using MTL HBgot HBcell.
unfold hd_check_plain_specX, hd_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rcc o fp w
  (HJ & Hrar & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) H10 H11 H12 H13 Hrc Hpre.
pose proof cvu_wx as Hwx. pose proof cvu_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_check_STK in Hwlo.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (al_const _ _ (AR_laws_ok rsegs B) _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HBcell in Kcell. rewrite HBgot, HBcell in Kgot.
pose proof (val_mem_of_rdword rsegs _ _ _ _ Kgot) as Vgot.
pose proof (val_mem_of_rdword rsegs _ _ _ _ Kcell) as Vcell.
assert (Hpres16 : forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpres; lia).
destruct (Z_lt_le_dec 0 rcc) as [Hpos | Hnpos].
- destruct (Hpre Hpos) as (Hlen & Ho0 & Ho63 & Hf0 & Hf63 & Hgo & Hgf & Hrao & Hraf & Hoffo & Hofff & Happo & Happf & Hapart).
  assert (Hrc' : 0 < rcc < 2 ^ 31) by lia.
  eapply cpu_pos with (rcc := rcc) (o := o) (fp := fp) (w := w); eassumption.
- assert (B2 : bv_unsigned (ew (Ereg regs cv_extra0) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (SHOK : sh_ok rsegs cv_Bx [] (Ereg regs cv_extra0) (mrestrict (w_H W) memc)) by constructor.
  pose proof (cpu_entry0 false W regs memc rcc Hpres16 Hsp Hal16 Vgot Vcell H10 H11 Hrc ltac:(cbn; lia)) as HS.
  unfold cfg_at. change (w64 A_CHECK_PLAIN_B) with (Z_to_bv 64 A_CHECK_PLAIN_B).
  aj_run_tok cpu_tbl_ok HS HJ SHOK cv_Bspan; [cv_awr B2 | ].
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (cv_kept_run (segs := rsegs) (fun a => spZ regs - 16 <= a < spZ regs) _ _ _ memc memc (ms_mem msx) (fun a _ _ => eq_refl) HFr ltac:(cv_kwr B2)) as K1;
    eapply (SRr_ret_at rsegs cpu_tbl cpu_tbl_ok cvu_wx W _ _ msx _ _ HS eq_refl); [vm_compute; reflexivity|];
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
      split; [exact (ajournal_materialize rsegs B (AR_laws_ok rsegs B) Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ)|];
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

Print Assumptions hd_check_plain_B.
