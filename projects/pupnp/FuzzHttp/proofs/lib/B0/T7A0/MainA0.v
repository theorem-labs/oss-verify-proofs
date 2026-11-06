(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim DriverSim StdioShape.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ NodesLZSound.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS RealizeS2 SeamA0 A0Prog TopA0 AssembleA0 DriverModelA.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C RF_mainA_T RF_mainA_post RDriverA_seams RDriverA_parser RF_mainA PostA0 F_fwrite F_vfprintf.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section MainA0.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Variable PZ : mem -> Prop.
  Variable H_MAIN_A0 : ProcInput -> ExecEntry -> machine_state -> Model -> Prop.

  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Hypothesis AC : am_contracts FI AI (JA FI AI).

  Let BSR : forall s LB m b, RHEAP_A FI AI s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b) := am_block_shread FI AI.

  Hypothesis MCI : memcpy_i_stmt.
  Hypothesis MSI : memset_i_stmt.
  Hypothesis SNI : strnlen_i_stmt.
  Hypothesis RDF : read_front_stmt.
  Hypothesis RDB : read_back_stmt.
  Hypothesis FWF : fwrite_front_stmt.
  Hypothesis FWB : fwrite_back_stmt.
  Hypothesis VPF : vprintf_front_stmt.
  Hypothesis VPB : vprintf_back_stmt.
  Hypothesis VFF : vfprintf_front_stmt.
  Hypothesis VFB : vfprintf_back_stmt.
  Hypothesis FPS : forall fmt flen, fprintf_s_front_stmt fmt flen.
  Hypothesis FP4 : fprintf_u_front_stmt.
  Hypothesis FPB : fprintf_back_stmt.
  Hypothesis DT : asan_dtor_stmt.

  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Hypothesis FZ : fuzz_one_stmtA FI AI (JA FI AI) PZ.

  Hypothesis GLUE : forall inp en msF mo,
    valid_input inp -> valid_entry imgA0 en inp -> alloc_ceiling = LO (en_sp en) -> H_MAIN_A0 inp en msF mo ->
    exists g, INVA (mkCfg msF mo) g
         /\ rat_mainA FI AI PZ (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (restrict (g_H g) msF) g
         /\ entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  #[using="MCI MSI SNI FPS FP4 FPB"] Lemma FPR : @fprintf_diag_stmt HC ASt.
  Proof. exact (fprintf_diag_proof MCI MSI SNI FPS FP4 FPB). Qed.
  #[using="FWF FWB"] Lemma FWR : @fwrite_diagA_stmt HC ASt.
  Proof. exact (fwrite_diagA_proof fwrite_diag_proof towrite_proof FWF FWB). Qed.
  #[using="MCI MSI SNI VPF VPB VFF VFB"] Lemma EMIT : emit_printf_stmt aget_so aset_so.
  Proof. exact (emit_printf_proof aget_so aset_so aget_set aset_set MCI MSI SNI VPF VPB VFF VFB). Qed.
  #[using="DT"] Lemma EXK : forall TID, 0 < TID < 2^31 -> exit_k_stmtA TID.
  Proof. intros TID HT. exact (exit_k_proofA TID HT DT). Qed.

  Definition H_MAIN_HC (inp : ProcInput) (en : ExecEntry) (ms : machine_state) (mo : Model) : Prop :=
    H_MAIN_A0 inp en ms mo /\ alloc_ceiling = LO (en_sp en).

  Definition QLEAF (inp : ProcInput) (en : ExecEntry) (r : exc (at_parser (ptr:=unit) * ASt)) (msF : machine_state) (a : gst) : Prop :=
    match r with
    | Ok p => QPARSER FI AI PZ (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (fst p) (snd p) (restrict (g_H a) msF) a
    | Unr => True
    end.

  #[using="HG FI AI PZ AMS AC BSR MCI MSI SNI RDF RDB FWF FWB VPF VPB VFF VFB FPS FP4 FPB DT PZ_agree FZ GLUE"] Theorem main_realizesA : MAIN H_MAIN_HC RSVA.
  Proof.
    refine (AssembleA0.main_realizes RSVA H_MAIN_HC gst VA INVA ATNA GOODA VA_meq VA_fs NODE_A _ QLEAF _ _).
    -   intros ms mo a [HF HZ]. exists (strip_vm (VA a mo)).
      pose proof (lf_minv _ _ _ _ _ HF) as (M & _). pose proof (lf_halt _ _ _ _ _ HF) as Hh.
      split; [unfold meq, VA; rewrite m_fds_strip_vm, m_fs_strip_vm; split; reflexivity|].
      split; [exact M| rewrite m_halted_strip_vm; unfold VA; rewrite m_halted_perase; exact Hh].
    -   intros inp en ms mo VI VE [HM CEIL].
      destruct (GLUE inp en ms mo VI VE CEIL HM) as (g & HINV & RM & ESF).
      pose proof VI as (VARGV & VENVP & _).
      assert (VSP : valid_sp (en_sp en)).
      { pose proof (valid_input_va_size _ VI) as Hsv48. destruct en as [sp brk mb dr]. rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE. cbn [imgA0] in VE. cbn. exact (proj1 VE). }
      exists g. split; [exact HINV|].
      pose proof (main_djM FI AI AMS PZ PZ_agree (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)
                    VSP CEIL VARGV ESF AC FPR EXK FWR MCI RDF RDB BSR _ g RM) as DJ.
      pose proof (DJ ms (proj1 (proj2 HINV)) eq_refl) as HI.     cbv beta in HI.
      eapply implS_mono; [exact HI|]. intros [|[ap so]] ms' a'; cbn [QLEAF fst snd]; intros H; exact H.
    -   intros inp en ap so ms a mo HQ [HF [HZ HV]] HFa HB.     cbn [QLEAF fst snd] in HQ.
      pose proof HQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (VSP & CEIL & ESF) & _).
      eapply (leaf_realizesA FI AI AMS PZ PZ_agree (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)
                VSP CEIL ESF AC FZ EMIT EXK ap so _ a ms mo HQ); [| exact HFa].
      split; [exact HZ|]. split; [reflexivity| split; [exact HF| split; [exact HZ| exact HV]]].
  Qed.
End MainA0.
