(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 64 of its 88 lines of code are new or changed and 302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBlkA.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the pcs, the param table (0x9bbe0) and the shadow offset's register (s2, atom 18) are rate's; RPgCfgChanges.same_io_wvb / kept_run are lib/A/RtPgW7bBase.v's w7_same_io_wvb / w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBlkA.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the param table (0x9bee0), p's register (s9, atom 25) and the shadow offset's register (s4, atom 20) are image B's; the block holds image B's UBSan pointer-overflow test of the entry's address (0x8161c / 0x81620), which the engine decides from p's atom range; lib/A/RtPgW7bBase.v is lib/AU/RtPgW7bBaseB.v; the prefix w7_ becomes w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): block A1 of the walk of
   LLVMFuzzerTestOneInput from 0x8160c (lib/AU/RtPgW7bBaseB.v). Proves no function (kind: segment lemma).

   A1, 0x8160c .. 0x8163c (pod.h:250, `param[p % 8]`):
     andi a0,s9,7; auipc a1 / addi a1 = 0x9bee0 (ent_headamp_key.param), with slli a0,a0,3 between them;
     not a2,a1; bgeu a2,a0 -> 0x81628; j 0x83098 (the UBSan trap: param + 8 (p & 7) does not wrap);
     add a0,a1,a0; srli a1,a0,3; add a1,a1,s4; lbu a1,0(a1); beqz a1 -> 0x81640; j report
   The trap test compares the literal ~0x9bee0 with (p & 7) << 3, whose range the engine computes from p's atom
   range [0, 255] (YP0e decide_cond2 over sv_ranges: [0, 56]), so it takes the fall-through arm by itself. The
   `lbu` / `beqz` / `j` triple is an instrumented check of the 8-byte table entry with no slow block: the engine's
   token (lib/Reusable/YCbn.v tok_load, tok_branch) takes the fast arm on one shadow obligation, range_addressable of
   the entry's 8 bytes, which the lemma asks. A1 ends at 0x81640 with a0 the entry's address. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* the entry's address as the engine builds it: 0x9bee0 + ((p & 7) << 3) *)
Lemma w7b_U_param : forall E p, ew E 25 = Z_to_bv 64 p -> 0 <= p < 256 ->
U E (SAlu ALU_ADD (SLit 638688) (SAlu ALU_SLL (SAlu ALU_AND (SOff 25 0) (SLit 7)) (SLit 3))) = 0x9bee0 + 8 * (p mod 8).
Proof.
intros E p H Hp.
rewrite !U_SAlu, !U_SLit, (U_atom E 25 p H) by lia. cbn [zalu_raw].
change (zcanon 638688) with 638688. change (zcanon 7) with 7. change (zcanon 3) with 3.
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

(* ======================== A1: 0x8160c -> 0x81640 ======================== *)
Definition ssb_A1 : sstate :=
mkSS 0x8160c sr_atoms [] None (mkFacts [(20%nat, mkAF W7B_SB W7B_SB 0); (25%nat, mkAF 0 255 0)] [] []).

Lemma w7b_A1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) p,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 p -> 0 <= p < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (0x9bee0 + 8 * (p mod 8)) 8 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x8160c) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_A2 regs memc mdc [10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (0x9bee0 + 8 * (p mod 8)))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p HJ H20 H25 Hp HRA.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E20 : ew (Ereg regs []) 20 = getr regs 20) by exact (ew_Ereg_nat regs _ 20 20%bv eq_refl).
assert (E25 : ew (Ereg regs []) 25 = getr regs 25) by exact (ew_Ereg_nat regs _ 25 25%bv eq_refl).
assert (HS : st_ok rsegs (Ereg regs []) ssb_A1 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8160c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ssb_A1 f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E20, E25, H20, H25. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF, W7B_SB. repeat split; lia. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok w7b_tbl_ok HS HJ SHOK W7B_span 0x81640.
- (* the shadow obligation of the table entry *)
  cbn [ms_mem mkst]. unfold W7B_Bx.
  rewrite (U_atom _ 20 SHADOW_OFF) by first [rewrite E20, H20; reflexivity | unfold SHADOW_OFF; lia].
  rewrite (w7b_U_param _ p) by (try rewrite E25, H25; first [reflexivity | lia]).
  exact HRA.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr (fun a Hw => match Hw with ex_intro _ r (conj Hin _) => match Hin with end end) a Ha Hz).
  + rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS).
    lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssv) (10%bv : bv 5)) in change (sr_get (ss_regs ssv) (10%bv : bv 5)) with e end.
    rewrite denot_lit_U. unfold w64. f_equal.
    apply w7b_U_param; [rewrite ew_ewset_other by lia; rewrite E25, H25; reflexivity | exact Hp].
Qed.
End d.
End b.

Print Assumptions w7b_U_param.
Print Assumptions w7b_A1.
