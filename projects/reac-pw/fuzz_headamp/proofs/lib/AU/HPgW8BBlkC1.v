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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 589 of its 629 lines of code are new or changed and 250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3b.v at c7151e1be458, ported to
   reac-pw/fuzz_rate image A: module paths and prefixes (RPg* -> RtPg*, rm_ -> rtm_, rl_ -> rt_, e_ -> q_) changed;
   rate's pcs, its shadow base s2 (x18), &pp->len in s7 (x23) and the shadow address of &pp->len in s6 (x22, pinned
   to its expression, as the code loads the shadow byte of pp->len through s6 and not through a cell); the Object
   header reads the shape and -0x3ffd from R+0xd8 and R+0x130; the start fact list has rate's five conjuncts; the
   image facts come from lib/A/RtPgSteps.v; the frame's shadow has 56 bytes. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW3b.v, with its module paths, module names, addresses and numbers changed; 206 of its 343 lines of code are new or changed and 492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3b.v at c7151e1be45 (its B7 piece,
   image A of fuzz_role) for reac-pw/fuzz_headamp's image B: B's own code walked again (s9 = pp, s11 = K, the
   UBSan tests, &pp->len and its shadow address read from R+0x138 / R+0x150, R+0xf8 written), the statement
   lib/AU/HPgSeg.v's; the helper lemmas reg_kept, chunk1 and b7_img taken with rm_ renamed to hm_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW3bB7.v; 118 of its 175 lines of code are new or changed and 286 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block C1 of the piece W8
   of the build (M01) of LLVMFuzzerTestOneInput 0x80c40, the statement hw8_blkC1_stmt of lib/AU/HPgW8BKit.v: from
   the return of pod_write_ent (0x8264c) with first = 1 to the entry of __asan_memcpy (0x51d8c), n_ent := n_ent + 1
   and the arguments of the record copy pp->ent[n_ent] = e62. Proves no function (kind: segment lemma).

   THE CODE (0x8264c .. 0x826bc, 29 words). a0 := R+0x140 = 1 (`beqz a0` 0x82654 not taken), a1 := R+0x158;
   a1 := R+0xe0 + s11, the shadow address of pp + 0x4d14 (the instrumented check `lb`, `bnez` 0x82664);
   a0 := R+0x120 = pp + 0x4d14, `lw` n_ent = kk; a2 := kk + 1 (`addiw`); the UBSan test `bge a2,a0` 0x82674 (no
   overflow); the check again (`lb`, `bnez` 0x82680); `sw a2` through R+0x120 (n_ent := kk + 1); the UBSan test
   `bltu a0,a1` 0x82690 (kk < 33); a0 := kk * 104 (`mul`); the UBSan test `bgeu a1,a0` 0x826a4 against R+0xd8 =
   ~(pp + 0x4014) (pp + 0x4014 + 104 kk does not wrap); a0 := R+0xd0 + a0 = pp + 0x4014 + 104 kk, a1 := s4,
   a2 := 104, `jal` 0x826bc to 0x51d8c (ra = 0x826c0). No UBSan trap (0x83a14) and no slow path of a check is
   reached.

   REGISTERS AND R-CELLS this file reads: s1 = R (x9), s4 = &e62 (x20), s7 = pp (x23), s11 = K (x27); R+0xd0
   (pp + 0x4014), R+0xd8 (~(pp + 0x4014)), R+0xe0 ((pp + 0x4d14) >> 3), R+0x120 (pp + 0x4d14), R+0x140 (first =
   1), R+0x158 (the pod index kk); n_ent at pp + 0x4d14. It writes ra, a0, a1, a2 (x1, x10 .. x12) and
   pp + 0x4d14 .. pp + 0x4d18.

   HOW. One run of the token engine (lib/Reusable/YCbn.v through YCbq.aj_run_to_tok, table hw8_tbl, stop at
   0x51d8c) over a symbolic state rebuilt from the statement's premises: the registers as their own atoms, kk as
   the extra atom 32 (range [0, 31]) and ~(pp + 0x4014) as the extra atom 33 (its range from pp's block bounds),
   the R-relative cells as one read-only region of base s1, n_ent as a region of base s7 whose write window is its
   4 bytes. The shadow base is s11 itself (its atom has the exact range [K, K]); R+0xe0 holds (pp + 0x4d14) >> 3
   in the engine's own form, so `add a1,a1,s11` forms the engine's shadow address and one shadow entry (pp's 19744
   bytes on s7) covers both checks. The store into pp is the journal's own through HPgBase.hd_fresh_awr. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgW8BKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the engine's context ===================================== *)
(* the shadow base is s11 (x27) *)
Definition hw8c_Bx : sv := SOff 27 0.
Definition hw8c_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* (pp + 0x4d14) >> 3 as the code keeps it in R+0xe0 *)
Definition hw8c_shx : sv := SAlu ALU_SRL (SOff 23 0x4d14) (SLit 3).
(* pp on s7 (19744 bytes) *)
Definition hw8c_SH : list shent := [mkSHE 23 0 19744].
Definition HW8C_PPHI : Z := 0x7fffff800000 - 19744.
(* R on the stack, pp in the heap, K, the pod index kk (the extra atom 32) and ~(pp + 0x4014) (the extra atom 33) *)
Definition hw8c_atoms : list (nat * afact) :=
[(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 0); (23%nat, mkAF 4096 HW8C_PPHI 0);
 (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 31 0);
 (33%nat, mkAF (2 ^ 64 - HW8C_PPHI - 0x4014 - 1) (2 ^ 64 - 4096 - 0x4014 - 1) 0)].
Definition hw8c_slot : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xd0 0x160 0 0
[YP09.mkChunk 0xd0 (CVal 8 (SOff 23 0x4014)); YP09.mkChunk 0xd8 (CVal 8 (SOff 33 0));
 YP09.mkChunk 0xe0 (CVal 8 hw8c_shx); YP09.mkChunk 0x120 (CVal 8 (SOff 23 0x4d14));
 YP09.mkChunk 0x140 (CVal 8 (SLit 1)); YP09.mkChunk 0x158 (CVal 8 (SOff 32 0))].
Definition hw8c_ne_r : YP09.region :=
YP09.mkRegion (Some 23%nat) 0x4d14 0x4d18 0x4d14 0x4d18 [YP09.mkChunk 0x4d14 (CVal 4 (SOff 32 0))].
Definition hw8c_ss : sstate :=
mkSS HW8_RA1 sr_atoms [hw8c_slot; hw8c_ne_r] None (mkFacts hw8c_atoms [] []).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section d.
Variable B : asyms.

(* ===================================== C1: 0x8264c -> 0x51d8c ===================================== *)
Lemma hw8_blkC1 : hw8_blkC1_stmt B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp kk HJ Hin Hout HR0 HR1
  R9 R23 R27 V140 V158 Ve0 V120 Vd8 Vd0 Vne Hkk.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hstk & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & Hppr & _).
rewrite Erq in Hppc, Happ, Hppr.
assert (Hnp : ((- pp - 0x4014 - 1) mod 2 ^ 64) = 2 ^ 64 - pp - 0x4014 - 1).
{ rewrite <- (Z.mod_add (- pp - 0x4014 - 1) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
set (E := Ereg regs [Z_to_bv 64 kk; Z_to_bv 64 (- pp - 0x4014 - 1)]).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 kk; Z_to_bv 64 (- pp - 0x4014 - 1)]) E) by apply env_agree_refl.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 kk) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew E 33 = Z_to_bv 64 (- pp - 0x4014 - 1)) by exact (ew_Ereg_extra regs _ 1).
assert (U32 : bv_unsigned (ew E 32) = kk) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = 2 ^ 64 - pp - 0x4014 - 1) by (rewrite E33, Z_to_bv_unsigned; exact Hnp).
assert (U9 : bv_unsigned (ew E 9) = R)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = pp)
  by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E23 : ew E 23 = Z_to_bv 64 pp) by (rewrite <- U23; symmetry; apply Z_to_bv_bv_unsigned).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite <- U27; symmetry; apply Z_to_bv_bv_unsigned).
(* the symbolic state at 0x8264c *)
assert (HS : st_ok rsegs E hw8c_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 HW8_RA1) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hw8c_ss. apply (entry_st_ok_full rsegs). all: fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, hw8c_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs E _ R 0xd0 8 (SOff 23 0x4014) ((pp + 0x4014) mod 2 ^ 64)); [| | cbn; lia | exact Vd0].
        -- cbn [sv_denot]. rewrite U23. symmetry. apply Z_to_bv64_mod.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
      * apply (chunk_ok_val rsegs E _ R 0xd8 8 (SOff 33 0) ((- pp - 0x4014 - 1) mod 2 ^ 64)); [| | cbn; lia | exact Vd8].
        -- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply Z_to_bv64_mod.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
      * apply (chunk_ok_val rsegs E _ R 0xe0 8 hw8c_shx (Z.shiftr (pp + 0x4d14) 3 mod 2 ^ 64)); [| | cbn; lia | exact Ve0].
        -- unfold hw8c_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
           rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, U23.
           change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
           rewrite (Z.mod_small (pp + 0x4d14)) by lia. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
      * apply (chunk_ok_val rsegs E _ R 0x120 8 (SOff 23 0x4d14) ((pp + 0x4d14) mod 2 ^ 64)); [| | cbn; lia | exact V120].
        -- cbn [sv_denot]. rewrite U23. symmetry. apply Z_to_bv64_mod.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
      * apply (chunk_ok_val rsegs E _ R 0x140 8 (SLit 1) 1); [reflexivity | | cbn; lia | exact V140].
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * apply (chunk_ok_val rsegs E _ R 0x158 8 (SOff 32 0) kk); [| | cbn; lia | exact V158].
        -- cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + unfold region_ok, hw8c_ne_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply (proj1 (Hppr (pp + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ pp 0x4d14 4 (SOff 32 0) kk); [| | cbn; lia | exact Vne].
      * cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hw8c_slot hw8c_ne_r]. rewrite U9, U23.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms hw8c_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U23, U27, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HW8C_PPHI, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs hw8c_Bx hw8c_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, hw8c_SH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart, hw8c_Bx; cbn [she_m she_lo she_hi];
  rewrite ?(U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 23 pp E23) by lia.
  split.
  - change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
    apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 HW8_RA1) with (Z_to_bv 64 HW8_RA1).
aj_run_to_tok hw8_tbl_ok HS HJ SHOK hw8c_Bspan HW8_MEMCPY.
{ (* the run writes n_ent only (pp is a block made since the journal's start) *)
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U23 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with (pp + (a - pp)) by lia.
  apply (hd_fresh_awr _ _ _ _ _ _ _ pp PP_SIZE); [exact Hin | exact Hout | rewrite Erq; lia]. }
(* ---- the state at 0x51d8c ---- *)
pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _). cbn [ss_mem] in HOK.
pose proof (Forall_inv (Forall_inv_tail HOK)) as (_ & _ & _ & Cn).
cbn [YP09.r_base YP09.r_chunks base_val] in Cn. rewrite U23 in Cn. clear HOK.
repeat rewrite Forall_cons_iff in Cn. destruct Cn as (Cne & _).
apply SRr_ret. unfold hw8_post. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [apply same_io_wvb|].
split; [eapply (regs_kept_of_st_ok rsegs E _ ms regs _ (w_H W) _ HS HAE); vm_compute; reflexivity|].
split.
{ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (rg & Hr & Hb).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U9, ?U23 in Hb; lia | ]).
  destruct Hr. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e1 := eval vm_compute in (sr_get (ss_regs ssf) (1%bv : bv 5)) in
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  let e11 := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
  let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (1%bv : bv 5)) with e1;
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
  change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e11;
  change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12 end.
split; [reflexivity|].
split.
{ rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. rewrite !U_SOff, U23, U32, Z.add_0_r.
  unfold zcanon, M64. rewrite (Z.mod_small 104) by lia. rewrite (Z.mod_small kk) by lia.
  rewrite (Z.mod_small (kk * 104)) by lia. rewrite (Z.mod_small (pp + 0x4014)) by lia.
  rewrite Z.mod_small by lia. lia. }
split.
{ cbn [sv_denot]. rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split; [reflexivity|].
exact (val_of_chunk_ok rsegs E _ pp 19732 4 (SOff 32 1) (kk + 1) Cne
  ltac:(cbn [sv_denot]; rewrite U32; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)).
Qed.
End d.
End b.

Print Assumptions hw8_blkC1.
