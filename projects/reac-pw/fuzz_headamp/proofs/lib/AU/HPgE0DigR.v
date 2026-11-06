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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths and module names changed; 220 of its 256 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 111d25b4415f (its engine runs o_run1a .. o_run4 and their plumbing) for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the code is rate's 24 words 0x81b6c .. 0x81bcc; the shadow token's base is s2 (atom 18) in place of s7; the entry goes to s8 (x24) in place of s9; the copy's destination is s6 (x22) in place of s4; the last run is rate's lone `j` to G 0x8150c (no `mv s9,s8`); RPgSteps / RPgMem / RPgCfgChanges are lib/A/RtPgSteps.v, RtPgMem.v and lib/A/RtPgW7bBase.v's w7_kept_run / w7_same_io_wvb; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddR.v, with its module paths, module names, addresses and numbers changed; 375 of its 437 lines of code are new or changed and 194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgEnt0DigW.v, with its module paths, module names, addresses and numbers changed; 119 of its 191 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0DigW.v at 97ea9c9eafa (its run 2, dg_run2);
   re-walked on image B's own code: image B's loop (the UBSan tests `bne a2,t0` and `bgeu a1,a0`, the slow blocks
   `andi; blt` of the two shadow checks of r, no check of the ch stores), its registers, its shadow base s11, the
   frame of class 4, and the R-cell R+0xc0 = ~&ch read by the pointer-overflow test as a read-only region whose value
   is a fresh atom with a range fact. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): run 2 of the walk of the DIG
   block of ent_build's case 0 (pod.h:239-245) in LLVMFuzzerTestOneInput 0x80c40, from 0x81a30 to 0x81af8: the decimal
   digits of v = c mod 64 into r[4], reversed into ch with the NUL at ch[n]. Proves no function (kind: segment lemma).

   HOW. A token run (YCbq.v aj_run_to_tok): r (s6 = F+0xe0) and ch (s2 = F+0xa0) are writable regions whose windows
   lie in application memory (lib/AU/HPgE0DigK.v dg_SH), the cell R+0xc0 (s1 = R) a read-only region holding the
   fresh atom 32 whose range [DG_KLO, DG_KHI] lets the engine decide `bgeu a1,a0` 0x81ae8 (a0 = n <= 2), and every
   shadow load of the two checks of r a token (E0Bx = s11 = K); each check's obligation is that byte of r addressable,
   which the frame's shadow with r in scope gives (HPgMem.hmu_B_ra_r: shadow byte 0x04, so bytes 0 .. 3 pass on the
   slow path 0x81a8c / 0x81ad0). The engine keeps no range for a `mulhu` result, so the run is done once per value
   of v (0 .. 63) with v a literal: every branch (`bne a2,t0` 0x81a30, `bltu t3,a5` 0x81a84, `bnez a1` 0x81ac8) is
   decided and every stored byte is a literal.
   Registers used: a2 (12) = 0, a6 (16) = v, a1 (11) = a7 (17) = s6 (22) = F+0xe0, t0 (5) = 4, t3 (28) = 9,
   t2 (7) = 10, s8 (24) = HSU_MULT10, s2 (18) = F+0xa0, s11 (27) = K, s1 (9) = R; R-cell R+0xc0. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgMem HPgSeg HPgE0Def HPgE0Base.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0DigK HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the value of R+0xc0 as a word: the fresh atom 32 of run 2's environment *)
Definition dg_kw (F : Z) : word := Z_to_bv 64 (2 ^ 64 - F - 0xa1).
Ltac dg_agree HAE := first [ exact HAE | apply dg_agree_step; [dg_agree HAE | apply Nat.leb_le; reflexivity] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ======================== run 2: 0x81a30 -> 0x81af8, one literal v at a time ======================== *)
Lemma dg_run2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) F pos R v,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0xe0) -> getr regs 18 = w64 (F + 0xa0) ->
getr regs 9 = w64 R -> F + 1024 <= R -> R + 0x220 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 ((- F - 0xa0 - 1) mod 2 ^ 64) ->
getr regs 12 = w64 0 -> getr regs 11 = w64 (F + 0xe0) -> getr regs 17 = w64 (F + 0xe0) ->
getr regs 5 = w64 4 -> getr regs 28 = w64 9 -> getr regs 7 = w64 10 -> getr regs 24 = w64 HSU_MULT10 ->
getr regs 16 = w64 v -> 0 <= v < 64 ->
hd_fsh rsegs (w_H W) memc F e0_PR ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81a30) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81af8 regs memc mdc dg_clob
  (fun a => (F + 0xa0 <= a < F + 0xb8) \/ (F + 0xe0 <= a < F + 0xe4))
  (fun _ mem2 => hm_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 v ++ [NUL]))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs F pos R v
  HJ Hown HF H27 H22 H18 H9 HFR HR47 HKc H12 H11 H17 H5 H28 H7 H24 H16 Hv Hfsh.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (dg_frame B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & HFpres & HFsh).
pose proof (dg_F8 F HF32) as HF8.
pose proof (dg_kval F HF4096 HFhi) as (Kv & Kr).
assert (A22 : (F + 0xe0) mod 32 = 0) by (rewrite Z.add_mod, HF32 by lia; reflexivity).
assert (A18 : (F + 0xa0) mod 32 = 0) by (rewrite Z.add_mod, HF32 by lia; reflexivity).
assert (E22 : ew (Ereg regs [dg_kw F]) 22 = Z_to_bv 64 (F + 0xe0))
  by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E18 : ew (Ereg regs [dg_kw F]) 18 = Z_to_bv 64 (F + 0xa0))
  by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E27 : ew (Ereg regs [dg_kw F]) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E9 : ew (Ereg regs [dg_kw F]) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew (Ereg regs [dg_kw F]) 32 = dg_kw F) by exact (ew_Ereg_extra regs [dg_kw F] 0).
assert (B22 : bv_unsigned (ew (Ereg regs [dg_kw F]) 22) = F + 0xe0)
  by (rewrite E22; apply unsigned_lit_small; unfold DG_FHI in HFhi; lia).
assert (B18 : bv_unsigned (ew (Ereg regs [dg_kw F]) 18) = F + 0xa0)
  by (rewrite E18; apply unsigned_lit_small; unfold DG_FHI in HFhi; lia).
assert (B9 : bv_unsigned (ew (Ereg regs [dg_kw F]) 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (B32 : bv_unsigned (ew (Ereg regs [dg_kw F]) 32) = 2 ^ 64 - F - 0xa1)
  by (rewrite E32; unfold dg_kw; apply unsigned_lit_small; unfold DG_FHI in HFhi; lia).
assert (D32 : sv_denot (Ereg regs [dg_kw F]) (SOff 32 0) = Z_to_bv 64 (2 ^ 64 - F - 0xa1)).
{ apply bv_eq. rewrite denot_SOff, B32, Z.add_0_r, unsigned_lit_small by (unfold DG_FHI in HFhi; lia).
  apply zcanon_id. unfold M64, DG_FHI in *. lia. }
assert (D22 : sv_denot (Ereg regs [dg_kw F]) (SOff 22 0) = getr regs 22)
  by exact (dg_agree_atom regs [dg_kw F] _ 22 22%bv (env_agree_refl _ _) ltac:(lia) eq_refl).
(* the entry state *)
assert (HS0 : st_ok rsegs (Ereg regs [dg_kw F]) ss_dg2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a30) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (hm_rw_region rsegs _ (w_H W) memc 22%nat (F + 0xe0) 0 4 0 4 []);
        [exact B22 | lia | unfold DG_FHI in HFhi; lia | | constructor].
      intros o Ho. apply HFpres. lia.
    + apply (hm_rw_region rsegs _ (w_H W) memc 18%nat (F + 0xa0) 0 24 0 24 []);
        [exact B18 | lia | unfold DG_FHI in HFhi; lia | | constructor].
      intros o Ho. apply HFpres. lia.
    + apply (hm_ro_region rsegs _ (w_H W) memc 9%nat R 0xc0 0xc8); [exact B9 | lia | lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 0xc0 8 (SOff 32 0) (2 ^ 64 - F - 0xa1));
        [exact D32 | change (8 * Z.of_N 8) with 64; unfold DG_FHI in HFhi; lia | cbn; lia |].
      rewrite <- Kv. exact HKc.
  - cbn [pairwise_disjoint all_disjoint dg_regions]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B22, B18, B9.
    split; [split; [right; lia | split; [left; lia | exact I]] | split; [split; [left; lia | exact I] | split; exact I]].
  - split; [|split; exact I].
    cbn [ss_dg2 dg_facts f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E27, B22, B18, B32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r, A22, A18.
    unfold SHADOW_OFF, E0SB, DG_FHI, DG_KLO, DG_KHI in *. repeat split; lia. }
(* the loop's constants and the two copies of &r, pinned; each pinned state is put back in record form, so that
   the nested projections of seven pins do not grow the state's term *)
pose proof (st_ok_pin_lit rsegs _ _ _ 12%bv 0 HS0 eq_refl H12) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_dg2] in HS1. clear HS0.
pose proof (st_ok_pin_sv rsegs _ _ _ 11%bv (SOff 22 0) HS1 eq_refl (eq_trans D22 (eq_trans H22 (eq_sym H11)))) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. clear HS1.
pose proof (st_ok_pin_sv rsegs _ _ _ 17%bv (SOff 22 0) HS2 eq_refl (eq_trans D22 (eq_trans H22 (eq_sym H17)))) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3. clear HS2.
pose proof (st_ok_pin_lit rsegs _ _ _ 5%bv 4 HS3 eq_refl H5) as HS4.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4. clear HS3.
pose proof (st_ok_pin_lit rsegs _ _ _ 28%bv 9 HS4 eq_refl H28) as HS5.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5. clear HS4.
pose proof (st_ok_pin_lit rsegs _ _ _ 7%bv 10 HS5 eq_refl H7) as HS6.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6. clear HS5.
pose proof (st_ok_pin_lit rsegs _ _ _ 24%bv HSU_MULT10 HS6 eq_refl H24) as HS7.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS7. clear HS6.
(* what every value's run shares *)
assert (SHOK : sh_ok rsegs E0Bx dg_SH (Ereg regs [dg_kw F]) (mrestrict (w_H W) memc)).
{ unfold dg_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc (Ereg regs [dg_kw F]) E0Bx 22 (F + 0xe0) 4 pos 0 4 _
      HAR Hin4).
    + unfold E0Bx. apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF; lia.
    + rewrite U_SOff, B22, Z.add_0_r. apply zcanon_id. unfold M64, DG_FHI in *; lia.
    + rewrite <- HF; lia.
    + lia.
    + rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia.
  - apply (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc (Ereg regs [dg_kw F]) E0Bx 18 (F + 0xa0) 4 pos 0 24 _
      HAR Hin4).
    + unfold E0Bx. apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF; lia.
    + rewrite U_SOff, B18, Z.add_0_r. apply zcanon_id. unfold M64, DG_FHI in *; lia.
    + rewrite <- HF; lia.
    + lia.
    + rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia. }
assert (Hawr : awr_ok (Ereg regs [dg_kw F]) dg_regions STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ unfold dg_regions.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat (F + 0xe0)); [reflexivity | exact B22 | | ].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). left. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (F + 0xa0)); [reflexivity | exact B18 | | ].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply (dg_awr_frame _ _ _ _ _ _ _ F pos a Hown HF). left. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat R); [reflexivity | exact B9 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
assert (Hkwr : forall a, in_wrange (Ereg regs [dg_kw F]) dg_regions a ->
  (F + 0xa0 <= a < F + 0xb8) \/ (F + 0xe0 <= a < F + 0xe4)).
{ intros a (r & Hr & Hb). cbn [dg_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?B22, ?B18, ?B9 in Hb; lia. }
assert (HoR : forall j, 0 <= j < 4 ->
  ob_holds rsegs E0Bx (Ereg regs [dg_kw F]) (mrestrict (w_H W) memc) (mkOB (SOff 22 j) 1)).
{ intros j Hj. unfold ob_holds; cbn [ob_x ob_n]. unfold E0Bx.
  rewrite (U_atom _ 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
  rewrite U_SOff, B22, zcanon_id by (unfold M64, DG_FHI in *; lia).
  replace (F + 0xe0 + j) with (F + HMU_R + j) by (unfold HMU_R; lia).
  exact (hmu_B_ra_r rsegs _ _ F true true false false true false false j 1 Hfsh HF8 ltac:(lia) ltac:(lia)). }
assert (Hpins : forall (rr : bv 5) ee,
  In (rr, ee) [((5%bv : bv 5), SLit 4); ((28%bv : bv 5), SLit 9); ((7%bv : bv 5), SLit 10);
               ((24%bv : bv 5), SLit HSU_MULT10)] ->
  forall Ev, sv_denot Ev ee = getr regs rr).
{ intros rr ee Hin Ev. cbn [In] in Hin.
  destruct Hin as [Heq|[Heq|[Heq|[Heq|[]]]]]; inversion Heq; subst; cbn [sv_denot];
  first [exact (eq_sym H5) | exact (eq_sym H28) | exact (eq_sym H7) | exact (eq_sym H24)]. }
assert (HAE : env_agree 32 (Ereg regs [dg_kw F]) (Ereg regs [dg_kw F])) by apply env_agree_refl.
clear - HS7 HJ SHOK Hawr Hkwr HoR Hpins HAE B18 Hwx Hsegs LAWS Hv H16.
(* one run per value of v *)
revert H16. pattern v. apply (dg_upto _ 64); [|exact Hv].
cbn [dg_all]. repeat split.
all: intros H16;
  lazymatch type of H16 with getr _ _ = w64 ?z =>
    pose proof (st_ok_pin_lit rsegs _ _ _ 16%bv z HS7 eq_refl H16) as HS;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS end;
  aj_run_to_tok dg_tbl_ok HS HJ SHOK E0Bspan 0x81af8;
  lazymatch goal with
  | |- range_addressable _ _ _ _ => refine (HoR _ _); lia
  | |- awr_ok _ _ _ _ _ _ _ _ _ => exact Hawr
  | |- SRr _ _ _ _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs [dg_kw F]) Ev) by dg_agree HAE end;
    eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | dg_io | | | exact HG | ];
    [ eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [dg_kw F] (w_H W) _ _ HS);
        [exact HA' | intros rr ee Hin; exact (Hpins rr ee Hin _) | vm_compute; reflexivity]
    | intros a Ha Hz; eapply (cb_kept_run _ _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr);
      [exact Hkwr | exact Ha | exact Hz]
    | rewrite <- (Z.add_0_r (F + 0xa0));
      apply (dg_bytes_of_st _ _ (w_H W) ms 1 18 (F + 0xa0) 0 _ HS);
      [ vm_compute; reflexivity | rewrite (proj1 HA' 18%nat ltac:(lia)); exact B18 ] ]
  end.
Qed.
End d.
End b.

Print Assumptions dg_run2.
