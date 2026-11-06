(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnregI. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnreg OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnregI.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition drv_unreg_globs : list (Z * Z) :=
  [(0x22ae0, 0x20); (0x22b00, 0x20); (0x22b20, 0x40); (0x22b60, 0x20); (0x26940, 0x60);
   (0x269a0, 0x60); (0x26a00, 0x20); (0x26a20, 0x60); (0x26a80, 0x40)]%Z.
Definition drv_unreg_tab : unreg_tab :=
  {| ut_dtor := ut_dtor both_unreg_tab; ut_base := ut_base both_unreg_tab; ut_pt := ut_pt both_unreg_tab;
     ut_g_start := ut_g_start both_unreg_tab; ut_g_stop := ut_g_stop both_unreg_tab; ut_p_start := ut_p_start both_unreg_tab;
     ut_globs := drv_unreg_globs;
     ut_p_flag := ut_p_flag both_unreg_tab; ut_g_aflags := ut_g_aflags both_unreg_tab; ut_p_aflags := ut_p_aflags both_unreg_tab;
     ut_p_mu := ut_p_mu both_unreg_tab; ut_g_pgsz := ut_g_pgsz both_unreg_tab; ut_c_inited := ut_c_inited both_unreg_tab;
     ut_c_ro := ut_c_ro both_unreg_tab; ut_str := ut_str both_unreg_tab |}.

Section FPGen.
Context {fx : FPState}.

Lemma drv_unreg_tab_ok : unreg_tab_ok BSEGS drv_unreg_tab.
Proof. destruct both_unreg_tab_ok. constructor; assumption. Qed.

Theorem drv_dtor_run : forall mem rom (sp ra vflag : word) (cpm : byte) (midend : word) (thr : Z) (pg ro : word) regs,
  unregH BSEGS drv_unreg_tab mem sp ra vflag cpm midend thr pg ro ->
  getr regs 1 = ra -> getr regs 2 = sp ->
  exists r mem',
    msteps BSEGS (mkst regs (0xc5cd0 : word) mem rom) (mkst r ra mem' rom)
    /\ regs_agree (fun x => In x unreg_clob) regs r
    /\ (forall x : word,
          (U x < U sp - 272 \/ U sp <= U x)%Z -> (U x < 0x10ba70 \/ 0x10ba70 + 8 <= U x)%Z ->
          (U x < 0x10ab00 \/ 0x10ab00 + 8 <= U x)%Z -> (U x < 0x7fff8000 \/ 0x8fff8000 <= U x)%Z -> mem' x = mem x)
    /\ (forall x : word,
          (0x7fff8000 <= U x < 0x8fff8000)%Z ->
          Forall (fun bs => U x < zshad (fst bs) \/ zshad (fst bs) + snd bs / 8 <= U x)%Z ((0x10a8c0, 64 * 9)%Z :: drv_unreg_globs) ->
          mem' x = mem x)
    /\ rdn BSEGS mem' (Z_to_bv 64 0x10ba70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn BSEGS mem' (Z_to_bv 64 0x10ab00) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ mem_grows mem mem'.
Proof.
  intros mem rom sp ra vflag cpm midend thr pg ro regs PRE R1 R2.
  destruct (unreg_globals_run BSEGS drv_unreg_tab drv_unreg_tab_ok mem rom sp ra vflag cpm midend thr pg ro regs PRE R1 R2) as (r & RUN & AG).
  exists r, (ug_final drv_unreg_tab mem sp ra pg regs).
  split; [exact RUN|]. split; [exact AG|].
  split; [exact (ug_final_outside BSEGS drv_unreg_tab drv_unreg_tab_ok mem sp ra vflag cpm midend thr pg ro regs PRE)|].
  split; [exact (ug_final_band BSEGS drv_unreg_tab drv_unreg_tab_ok mem sp ra vflag cpm midend thr pg ro regs PRE)|].
  destruct (ug_final_mu BSEGS drv_unreg_tab drv_unreg_tab_ok mem sp ra vflag cpm midend thr pg ro regs PRE) as [MU FL].
  split; [exact MU|]. split; [exact FL|].
  exact (ug_final_grows BSEGS drv_unreg_tab drv_unreg_tab_ok mem sp ra vflag cpm midend thr pg ro regs PRE).
Qed.
End FPGen.
