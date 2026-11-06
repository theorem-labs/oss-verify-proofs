(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesUG AsanNodesUGSoundG BothUnregWalk BothPlanImages SumsBothSpecs BothMemset.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma both_ug_wf : ug_wf UGN.UG_BOTH = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_ug_recs : forallb rec_okb (UGN.ug_glob UGN.UG_BOTH) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_ug_fills : forallb (fun f : Z * Z => (Z.leb (UGN.ug_hlo UGN.UG_BOTH) (fst f) && Z.leb (fst f + snd f) (UGN.ug_hhi UGN.UG_BOTH))%bool) (UGN.ug_fills UGN.UG_BOTH) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma both_ug_spec : ug_spec BSEGS BOTH UGN.UG_BOTH.
Proof.
  intros mem rom regs Hrd Hst R1 R20 R27 R10 R11 R12 R8 RR.
  (* [comment removed for export] *)
  cbn [UGN.ug_regs UGN.UG_BOTH] in RR.
  apply Forall_cons_iff in RR as [G9 RR]. apply Forall_cons_iff in RR as [G18 RR]. apply Forall_cons_iff in RR as [G23 RR].
  apply Forall_cons_iff in RR as [G25 RR]. apply Forall_cons_iff in RR as [G26 _]. cbn [fst snd] in G9, G18, G23, G25, G26.
  (* [comment removed for export] *)
  unfold UGN.ug_reads in Hrd. apply Forall_app in Hrd as [Hcells Htab].
  cbn [UGN.ug_cells UGN.UG_BOTH] in Hcells.
  apply Forall_cons_iff in Hcells as [Cms Hcells]. apply Forall_cons_iff in Hcells as [Crg Hcells]. apply Forall_cons_iff in Hcells as [Ccp Hcells].
  apply Forall_cons_iff in Hcells as [Csh Hcells]. apply Forall_cons_iff in Hcells as [Cin Hcells]. apply Forall_cons_iff in Hcells as [Cthr _].
  destruct (ug_loop rom (UGN.ug_hlo UGN.UG_BOTH) (UGN.ug_hhi UGN.UG_BOTH) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              (UGN.ug_glob UGN.UG_BOTH) (UGN.ug_tab UGN.UG_BOTH) mem regs
              ltac:(discriminate) both_ug_recs ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              ltac:(apply Forall_forall; intros f Hin; pose proof (proj1 (forallb_forall _ _) both_ug_fills f Hin) as Hb; cbn beta in Hb;
                    apply andb_prop in Hb as [B1 B2]; apply Z.leb_le in B1; apply Z.leb_le in B2; split; assumption)
              Htab (conj Cin (conj Ccp (conj Crg (conj Csh (conj Cthr Cms))))) Hst)
    as (regs' & RUN & S8 & S20 & S27 & FR); try assumption.
  all: try (first [exact R10 | exact R12 | exact R8 | exact R11 | exact G9 | exact G18 | exact G23 | exact G25 | exact G26]).
  { rewrite R1. apply bv_eq. vm_compute. reflexivity. }
  exists regs'. split; [|split; [|split; [|split]]].
  - replace (Z_to_bv 64 (x_memset BOTH)) with ms_entry by (apply bv_eq; vm_compute; reflexivity).
    replace (Z_to_bv 64 (UGN.ug_exit UGN.UG_BOTH)) with (0x41f50 : word)%bv by (apply bv_eq; vm_compute; reflexivity).
    exact RUN.
  - rewrite S8. f_equal.
  - rewrite S20. f_equal.
  - exact S27.
  - intros r Hr0 Hnot. apply FR; intros ->; apply Hnot; cbv; auto 20.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AsanNode.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.
Variable FS0 : Fs.Fs.

Theorem both_ug_ext_sound : ext_stmt BSEGS BOTH nx0 LIMIT (UGN.xn BSEGS BOTH nx0 UGN.UG_BOTH) SINV argH FS0.
Proof.
  eapply (ug_xn_sound BSEGS BOTH nx0 UGN.UG_BOTH LIMIT); try eassumption;
    first [ exact both_wx | exact both_in_hull | exact both_hull_ok | exact both_segs_wr | exact both_ug_spec | exact both_ug_wf | idtac ].
Qed.
End AsanNode.
