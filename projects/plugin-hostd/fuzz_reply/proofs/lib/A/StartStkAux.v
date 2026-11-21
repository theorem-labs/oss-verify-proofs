From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03 YA0j YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB12 AB1h StartStkAuxG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require PlanRegen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AB01r.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
(* Every hand-off state of the start-up run at CONFIG_RSEQ flag r (A/AB01r.v, computed in the build) covers the
   auxv vector and the 16 AT_RANDOM bytes of the flag-r layout: the premise stk_aux_chk of StartStkAuxG's presence
   lemmas, by vm_compute over each flag's states.  plugin-hostd/fuzz_command's A/StartStkAux.v, with its
   A/CmdStartInst.v membership lemma and its A/CmdStartCert.v stk_aux_chk_of over A/AB01r.v directly (this unit has
   no start-data class). *)
Lemma tfib_holes_stkaux :
(forallb (stk_aux_chk 0) (AB01r.HS_tfib_list_r 0) && forallb (stk_aux_chk 1) (AB01r.HS_tfib_list_r 1))%bool = true.
Proof. vm_compute. reflexivity. Qed.
(* A hand-off state of flag r is one of flag r's states (A/AB01r.v HS_tfib_r, HS_tfib_list_r). *)
Lemma HS_tfib_r_In_r : forall r h ch, AB01r.HS_tfib_r r h = Some ch -> In ch (AB01r.HS_tfib_list_r r).
Proof.
intros r h ch H. unfold AB01r.HS_tfib_r, PlanRegen.hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (AB01r.HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _]. unfold AB01r.HS_tfib_list_r. exact (in_map snd _ _ F).
Qed.
Lemma stk_aux_chk_of : forall b h ch,
AB01r.HS_tfib_r (rseq_z b) h = Some ch -> stk_aux_chk (rseq_z b) ch = true.
Proof.
intros b h ch Hh. pose proof tfib_holes_stkaux as H. apply andb_prop in H as [H0 H1].
pose proof (HS_tfib_r_In_r _ h ch Hh) as Hin.
destruct b; cbn [rseq_z] in *; [exact (proj1 (forallb_forall _ _) H1 ch Hin) | exact (proj1 (forallb_forall _ _) H0 ch Hin)].
Qed.
