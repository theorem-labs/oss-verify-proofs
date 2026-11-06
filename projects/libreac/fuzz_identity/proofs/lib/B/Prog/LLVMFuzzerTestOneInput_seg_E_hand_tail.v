(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:2300-2306, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_I.v, with its addresses changed; 49 of its 113 lines of code are new or changed and 3097 lines of the source are left out. *)
(* e_tail of seg_E (LLVMFuzzerTestOneInput_seg_E_hand_stmt.v, e_tail_stmt): the compare at 0x817f0 (BASE + 0x107c,
   bne x18, a0 to the abort at 0x82614) with x18 = a0 = fam is not taken, and the run is at 0x817f4 (BASE + 0x1080)
   with nothing written: e_post holds. The symbolic state at 0x817f0 has no region; x10 is set to x18's atom, so
   the engine decides the compare (decide_eq on two equal values). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_E_hand_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_box_family_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOM := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation INV_E_END := (inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

#[local] Notation EPOST := (e_post B LLVMF_STK).

Lemma e_tail : e_tail_stmt B LLVMF_STK.
Proof.
unfold e_tail_stmt.
intros LAWS g pos mf ly2 S2 W2 regs2 mem2 regs mem md fam HJ Hfam R18 R10 Q2 Q3 Q4 Q8 Q9 Q25 Q24 R23 R14 VH KEEP.
pose (RUNP := SRr_run_pi_AJ B LAWS).
pose proof pa_B_ok as HBASE.
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS0 : st_ok_pi SEGS VAL E (mkSS 0x107c sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x107c)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
(* x10 holds x18's value: the compare at 0x817f0 is decided by the engine *)
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x107c (sr_set sr_atoms 10%bv (SOff 18 0)) [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x107c)) mem (seg_rom SEGS)))).
{ apply (st_ok_pi_set_reg E _ _ 10%bv (SOff 18 0) HS0); [discriminate|].
  cbn [ms_regs restrict mkst sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 18%nat 18%bv eq_refl), R18, R10.
  reflexivity. }
clear HS0.
unfold cfg_at. change (w64 (BASE + 0x107c)) with (Z_to_bv 64 (BASE + 0x107c)).
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr & _). destruct Hr. }
(* nothing was written *)
assert (HM : forall x, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem x)
  by (intros x; apply HFr; intros (r & Hr & _); destruct Hr).
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (25%bv : bv 5) P25. prreg HS (24%bv : bv 5) P24.
prreg HS (23%bv : bv 5) P23. prreg HS (14%bv : bv 5) P14.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
rewrite (EE 25%nat 25%bv eq_refl) in P25. rewrite (EE 24%nat 24%bv eq_refl) in P24.
rewrite (EE 23%nat 23%bv eq_refl) in P23. rewrite (EE 14%nat 14%bv eq_refl) in P14.
pmkst HS.
apply SRr_ret. unfold e_post.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
split; [reflexivity|].
split; [exact HJ|].
split.
{ intros a Ha Hw Hh. rewrite (aview_eq_of SEGS (w_H W2) mem (ms_mem ms) a (HM _)). exact (KEEP a Ha Hw Hh). }
split.
{ intros kk Hkk. pose proof (VH kk Hkk) as Vk. unfold mbyte in *. rewrite HM. exact Vk. }
rewrite P2, P3, P4, P8, P9, P25, P24, P23, P14.
split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q8|]. split; [exact Q9|].
split; [exact Q25|]. split; [exact Q24|]. split; [exact R23 | exact R14].
Qed.

End c.
End b.
End a.
