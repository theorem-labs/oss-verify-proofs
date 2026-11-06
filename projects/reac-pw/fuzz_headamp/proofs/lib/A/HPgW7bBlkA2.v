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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 148 of its 176 lines of code are new or changed and 262 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkA2.v at 1227c8ba2a69 for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the param table (0x9bbe0), HPFX (0x20fe0), the separators, the registers (the shadow offset in s2, the part pointer in s6, the saved cursor in s7, the part string in s8, n in s9), the frame window (R+0x158 .. R+0x178, the store check of R+0x160) and the frame bound (R + 0x1e0 <= 2^47) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkA2.v, with its module paths, addresses and numbers changed; 19 of its 175 lines of code are new or changed and 20 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): block A2 of the walk of
   LLVMFuzzerTestOneInput from 0x81a34 (lib/A/HPgW7bBase.v). Proves no function (kind: segment lemma).

   A2, 0x81a5c .. 0x81ac0 (pod.h:250-252, sep and parts[0..3]):
     slli s11,s11,0x38; bgez s11 -> 0x81a70; a1 = 0x21200 (""); j 0x81a78; 0x81a70: a1 = 0x21420 (".")
     a2 = 0x20f00; sd a2,0x140(s1); addi a2,s1,0x148; srli a2,a2,3; add a2,a2,s7; lbu a2,0(a2)
     ld a0,0(a0); beqz a2 -> 0x81aa0; j report
     0x81aa0: mv s5,s9; mv s8,zero; sd s4,0x148(s1); sd a1,0x150(s1); sd a0,0x158(s1)
     addi s4,s1,0x140; ld s9,0(s4); mv a0,s9; jal strlen 0x41b98
   The engine starts with a0 pinned to an extra atom (32, the param table entry's address W7_PTAB p) whose 8 bytes
   are a region with the entry's value (atom 33, pa), and the frame window [R+0x140, R+0x160) as a writable region
   based on s1 (atom 9). The `bgez` is decided by the fact on s11 (atom 27): [0, 127] or [128, 255] after a case
   split on bit 7 of p. The `lbu` / `beqz` / `j` triple is the instrumented check of the store to R+0x148; the
   token engine takes the fast arm on one shadow obligation, range_addressable of [R+0x148, R+0x150), which the
   lemma asks. A2 ends at the strlen entry with ra = 0x81ac4 and the four slots of the window stored. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the param table entry's address, A1's a0 at 0x81a5c: 0x9c180 + ((p & 7) << 3) *)
Definition W7_PTAB (p : Z) : Z := 0x9c180 + 8 * (p mod 8).

(* bit 7 of a byte *)
Lemma w7_b7 : forall p, 0 <= p < 256 -> Z.testbit p 7 = (128 <=? p).
Proof.
intros p Hp. destruct (Z.leb_spec 128 p) as [H|H].
- apply (proj2 (Z.testbit_true p 7 ltac:(lia))). change (2 ^ 7) with 128.
  rewrite <- (Z.div_unique p 128 1 (p - 128)) by lia. reflexivity.
- apply (proj2 (Z.testbit_false p 7 ltac:(lia))). change (2 ^ 7) with 128.
  rewrite Z.div_small by lia. reflexivity.
Qed.

(* the engine's start state at 0x81a5c: a0 is the extra atom 32 (the entry's address), the entry's 8 bytes hold the
   extra atom 33 (its value pa), the frame window [R+0x140, R+0x160) is writable; b7 is bit 7 of p *)
Definition a2_extra (p pa : Z) : list word := [w64 (W7_PTAB p); w64 pa].
Definition ss_A2 (b7 : bool) : sstate :=
mkSS W7_A2 (sr_set sr_atoms 10%bv (SOff 32 0))
[YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
 YP09.mkRegion (Some 9%nat) 0x140 0x160 0x140 0x160 []] None
(mkFacts [(23%nat, mkAF W7SB W7SB 0); (27%nat, if b7 then mkAF 128 255 0 else mkAF 0 127 0);
 (9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 0x1e0) 4); (32%nat, mkAF 0x9c180 0x9c1b8 3)] [] []).

(* the leaf's helpers: a register's value, and a slot of the window (the region based on atom 9), out of the engine's
   last state *)
Ltac a2_reg HS r :=
  rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
  lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end;
  cbn [sv_denot].
Ltac a2_field RG F9 od e v :=
  refine (w7_field _ _ 9%nat _ _ 320 352 320 352 od 8%N e v RG F9 _ _ _ _);
  [ cbv [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64)
  | lia ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

Lemma w7_A2_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p R pa b7,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 (W7_PTAB p) -> getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 p -> 0 <= p < 256 ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (W7_PTAB p) 8 pa -> 0 <= pa < 2 ^ 64 ->
(forall a, R + 0x140 <= a < R + 0x160 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
Z.testbit p 7 = b7 ->
st_ok rsegs (Ereg regs (a2_extra p pa)) (ss_A2 b7)
(restrict (w_H W) (mkst regs (Z_to_bv 64 W7_A2) memc (seg_rom rsegs))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p R pa b7 HJ H10 H23 H27 Hp H9 HR0 HR1 HR16 HPA Hpa HWIN Hb7.
assert (E9 : ew (Ereg regs (a2_extra p pa)) 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
assert (E23 : ew (Ereg regs (a2_extra p pa)) 23 = getr regs 23) by exact (ew_Ereg_nat regs _ 23 23%bv eq_refl).
assert (E27 : ew (Ereg regs (a2_extra p pa)) 27 = getr regs 27) by exact (ew_Ereg_nat regs _ 27 27%bv eq_refl).
assert (X32 : ew (Ereg regs (a2_extra p pa)) 32 = w64 (W7_PTAB p)) by exact (ew_Ereg_extra regs _ 0).
assert (X33 : ew (Ereg regs (a2_extra p pa)) 33 = w64 pa) by exact (ew_Ereg_extra regs _ 1).
assert (HPT : 0x9c180 <= W7_PTAB p <= 0x9c1b8) by (unfold W7_PTAB; pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
assert (B9 : bv_unsigned (ew (Ereg regs (a2_extra p pa)) 9) = R) by (rewrite E9, H9; unfold w64; apply unsigned_lit_small; lia).
assert (B32 : bv_unsigned (ew (Ereg regs (a2_extra p pa)) 32) = W7_PTAB p)
by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_A2. apply (entry_st_ok_full rsegs).
- apply YI04.regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. rewrite B32, Z.add_0_r. exact H10.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (W7_PTAB p) 0 8 (SOff 33 0) pa).
    * cbn [sv_denot]. rewrite X33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * rewrite Z.add_0_r. exact HPA.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply apresent_writable.
    eapply proj1. eapply (awr_byte_present rsegs B LAWS); [exact HJ | apply HWIN; lia].
- cbn [pairwise_disjoint all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B32, B9.
  split; [split; [left; lia | exact I] | split; exact I].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok.
  rewrite B9, B32, E23, E27, H23, H27. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  assert (HM : W7_PTAB p mod 8 = 0).
  { unfold W7_PTAB. replace (0x9c180 + 8 * (p mod 8)) with ((79920 + p mod 8) * 8) by ring. apply Z.mod_mul. lia. }
  rewrite w7_b7 in Hb7 by exact Hp.
  destruct b7; cbn [af_lo af_hi af_al2];
  [apply Z.leb_le in Hb7 | apply Z.leb_gt in Hb7];
  change (2 ^ 0) with 1; change (2 ^ 4) with 16; change (2 ^ 3) with 8; rewrite !Z.mod_1_r, HM, HR16;
  unfold SHADOW_OFF, W7SB; repeat split; lia.
Qed.

Lemma w7_A2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p R s4v cur pa,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 (W7_PTAB p) -> getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 p -> 0 <= p < 256 ->
getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
getr regs 20 = w64 s4v -> 0 <= s4v < 2 ^ 64 -> getr regs 25 = w64 cur ->
val_mem rsegs (mrestrict (w_H W) memc) (W7_PTAB p) 8 pa -> 0 <= pa < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (R + 0x148) 8 ->
(forall a, R + 0x140 <= a < R + 0x160 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7_A2) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_STRLEN regs memc mdc [1; 10; 11; 12; 20; 21; 24; 25; 27]%bv
(fun a => R + 0x140 <= a < R + 0x160)
(fun regs2 mem2 => getr regs2 1 = w64 W7_AFTER_STRLEN /\ getr regs2 10 = w64 0x20f00 /\ getr regs2 25 = w64 0x20f00 /\
 getr regs2 20 = w64 (R + 0x140) /\ getr regs2 21 = w64 cur /\ getr regs2 24 = w64 0 /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x140) 8 0x20f00 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x148) 8 s4v /\
 val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x150) 8 (w7_sep p) /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x158) 8 pa)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p R s4v cur pa
HJ H10 H23 H27 Hp H9 HR0 HR1 HR16 H20 Hs4 H25 HPA Hpa HRA HWIN.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E9 : ew (Ereg regs (a2_extra p pa)) 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
assert (E20 : ew (Ereg regs (a2_extra p pa)) 20 = getr regs 20) by exact (ew_Ereg_nat regs _ 20 20%bv eq_refl).
assert (E23 : ew (Ereg regs (a2_extra p pa)) 23 = getr regs 23) by exact (ew_Ereg_nat regs _ 23 23%bv eq_refl).
assert (E25 : ew (Ereg regs (a2_extra p pa)) 25 = getr regs 25) by exact (ew_Ereg_nat regs _ 25 25%bv eq_refl).
assert (X33 : ew (Ereg regs (a2_extra p pa)) 33 = w64 pa) by exact (ew_Ereg_extra regs _ 1).
assert (B9 : bv_unsigned (ew (Ereg regs (a2_extra p pa)) 9) = R) by (rewrite E9, H9; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs (a2_extra p pa)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (a2_extra p pa)) (Ereg regs (a2_extra p pa))) by apply env_agree_refl.
assert (HWR : forall b7 a, in_wrange (Ereg regs (a2_extra p pa)) (ss_mem (ss_A2 b7)) a -> R + 0x140 <= a < R + 0x160).
{ intros b7 a (r & Hin & Ha). cbn [ss_A2 ss_mem In] in Hin. destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | rewrite B9 in Ha; lia]. }
destruct (Z.testbit p 7) eqn:Hb7;
pose proof (w7_A2_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p R pa _
  HJ H10 H23 H27 Hp H9 HR0 HR1 HR16 HPA Hpa HWIN Hb7) as HS;
aj_run_to_tok w7_tbl_ok HS HJ SHOK W7Bspan 0x41b98.
(* goals 1-3: bit 7 set (the `bgez` falls through, sep = "" at 0x21200); 4-6: clear (taken, sep = "." at 0x21420).
   The shadow obligation of the store check, [R+0x148, R+0x150) *)
1,4: cbn [ms_mem mkst]; unfold W7Bx;
  rewrite (U_atom _ 23 SHADOW_OFF) by first [rewrite E23, H23; reflexivity | unfold SHADOW_OFF; lia];
  rewrite U_SOff, B9, zcanon_id by (unfold M64; lia); exact HRA.
(* the start state's regions: the entry (read only) and the window, writable by the hypothesis on it *)
1,3: unfold ss_A2; cbn [ss_mem];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply (w7_awr_cons _ _ _ _ _ _ _ _ _ _ 9%nat R);
  [reflexivity | exact B9 | cbn [YP09.r_wlo YP09.r_whi]; exact HWIN | apply awr_ok_nil].
(* the leaf: w7_post from the engine's last state at the strlen entry *)
all: eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply HPgSteps.same_io_wvb | | | exact HG | ].
1,4: eapply (w7_regs_kept _ _ ms regs (a2_extra p pa) (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
1,3: intros a Ha Hz;
  exact (kept_run (fun a => R + 0x140 <= a < R + 0x160) _ _ (w_H W) memc memc (ms_mem ms)
    (fun a _ _ => eq_refl) HFr (HWR _) a Ha Hz).
(* the result: ra, a0 = s9 = parts[0], s4 = &parts[0], s5 = the old s9, s8 = 0, and the four slots *)
all: cbv beta;
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
  let sepv := eval vm_compute in (sr_get (ss_regs ssv) (11%bv : bv 5)) in
  let r9 := eval vm_compute in (nth 1 (ss_mem ssv) (YP09.mkRegion None 0 0 0 0 [])) in
  assert (F9 : bv_unsigned (ew Ev 9) = R) by (rewrite ew_ewset_other by lia; exact B9);
  assert (F20 : ew Ev 20 = w64 s4v) by (rewrite ew_ewset_other by lia; rewrite E20; exact H20);
  assert (F25 : ew Ev 25 = w64 cur) by (rewrite ew_ewset_other by lia; rewrite E25; exact H25);
  assert (F33 : ew Ev 33 = w64 pa) by (rewrite ew_ewset_other by lia; exact X33);
  assert (RG : region_ok rsegs Ev (mrestrict (w_H W) (ms_mem msv)) r9)
  by exact (w7_region_nth Ev ssv (restrict (w_H W) msv) 1%nat r9 HS ltac:(vm_compute; reflexivity));
  split; [a2_reg HS (1%bv : bv 5); reflexivity|];
  split; [a2_reg HS (10%bv : bv 5); reflexivity|];
  split; [a2_reg HS (25%bv : bv 5); reflexivity|];
  split; [a2_reg HS (20%bv : bv 5); rewrite F9; reflexivity|];
  split; [a2_reg HS (21%bv : bv 5); rewrite F25, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|];
  split; [a2_reg HS (24%bv : bv 5); reflexivity|];
  split; [a2_field RG F9 320 (SLit 134912) 134912; [reflexivity | lia]|];
  split; [a2_field RG F9 328 (SOff 20 0) s4v; [rewrite F20, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | lia]|];
  split; [a2_field RG F9 336 sepv (w7_sep p); unfold w7_sep; rewrite Hb7; cbn beta iota; [reflexivity | lia]|];
  a2_field RG F9 344 (SOff 33 0) pa; [rewrite F33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | lia]
  end.
Qed.
End d.
End b.
Print Assumptions w7_A2_entry.
Print Assumptions w7_A2.
