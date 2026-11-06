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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 60 of its 87 lines of code are new or changed and 263 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkA.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the param table (0x9bbe0) and the shadow offset's register (s2, atom 18) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkA.v, with its module paths, addresses and numbers changed; 9 of its 85 lines of code are new or changed and 11 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): blocks A1 and A2 of the walk of
   LLVMFuzzerTestOneInput from 0x81a34 (lib/A/HPgW7bBase.v). Proves no function (kind: segment lemma).

   A1, 0x81a34 .. 0x81a58 (pod.h:250, `param[p % 8]`):
     andi a0,s11,7; auipc a1 / addi a1 = 0x9c180 (ent_headamp_key.param); slli a0,a0,3; add a0,a1,a0
     srli a1,a0,3; add a1,a1,s7; lbu a1,0(a1); beqz a1 -> 0x81a5c; j report
   The `lbu` / `beqz` / `j` triple is an instrumented check of the 8-byte table entry with no slow block: the
   engine's token (lib/Reusable/YCbn.v tok_load, tok_branch) takes the fast arm on one shadow obligation,
   range_addressable of the entry's 8 bytes, which the lemma asks. A1 ends at 0x81a5c with a0 the entry's address. *)
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

(* the entry's address as the engine builds it: 0x9c180 + ((p & 7) << 3) *)
Lemma w7_U_param : forall E p, ew E 27 = Z_to_bv 64 p -> 0 <= p < 256 ->
U E (SAlu ALU_ADD (SLit 639360) (SAlu ALU_SLL (SAlu ALU_AND (SOff 27 0) (SLit 7)) (SLit 3))) = 0x9c180 + 8 * (p mod 8).
Proof.
intros E p H Hp.
rewrite !U_SAlu, !U_SLit, (U_atom E 27 p H) by lia. cbn [zalu_raw].
change (zcanon 639360) with 639360. change (zcanon 7) with 7. change (zcanon 3) with 3.
replace (Z.land p 7) with (p mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hm.
rewrite (zcanon_id (p mod 8)) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (p mod 8 * 8)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================== A1: 0x81a34 -> 0x81a5c ======================== *)
Definition ss_A1 : sstate :=
mkSS 0x81a34 sr_atoms [] None (mkFacts [(23%nat, mkAF W7SB W7SB 0); (27%nat, mkAF 0 255 0)] [] []).

Lemma w7_A1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 p -> 0 <= p < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (0x9c180 + 8 * (p mod 8)) 8 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81a34) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_A2 regs memc mdc [10; 11]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (0x9c180 + 8 * (p mod 8)))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p HJ H23 H27 Hp HRA.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E23 : ew (Ereg regs []) 23 = getr regs 23) by exact (ew_Ereg_nat regs _ 23 23%bv eq_refl).
assert (E27 : ew (Ereg regs []) 27 = getr regs 27) by exact (ew_Ereg_nat regs _ 27 27%bv eq_refl).
assert (HS : st_ok rsegs (Ereg regs []) ss_A1 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a34) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_A1 f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E23, E27, H23, H27. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF, W7SB. repeat split; lia. }
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok w7_tbl_ok HS HJ SHOK W7Bspan 0x81a5c.
- (* the shadow obligation of the table entry *)
  cbn [ms_mem mkst]. unfold W7Bx.
  rewrite (U_atom _ 23 SHADOW_OFF) by first [rewrite E23, H23; reflexivity | unfold SHADOW_OFF; lia].
  rewrite (w7_U_param _ p) by (try rewrite E27, H27; first [reflexivity | lia]).
  exact HRA.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply HPgSteps.same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS).
    lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssv) (10%bv : bv 5)) in change (sr_get (ss_regs ssv) (10%bv : bv 5)) with e end.
    rewrite denot_lit_U. unfold w64. f_equal.
    apply w7_U_param; [rewrite ew_ewset_other by lia; rewrite E27, H27; reflexivity | exact Hp].
Qed.
End d.
End b.
Print Assumptions w7_A1.
