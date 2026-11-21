From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YK11 PlanRegen.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB12 YB1h YB01r StartStkAuxG.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
(* Every hand-off state of the start-up certificate at each CONFIG_RSEQ flag r (AB01r's [HS_tfib_list_r r])
   covers the auxv vector and the 16 AT_RANDOM bytes: the premise [stk_aux_chk r] of
   StartStkAuxG.stk_aux_present, by vm_compute over both flags' lists. *)
Lemma tfib_holes_stkaux : forallb (stk_aux_chk 0) (HS_tfib_list_r 0) = true
/\ forallb (stk_aux_chk 1) (HS_tfib_list_r 1) = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma stkaux_In_r : forall r h ch, HS_tfib_r r h = Some ch ->
In ch (HS_tfib_list_r (if Z.eqb r 1 then 1 else 0)).
Proof.
intros r h ch H. unfold HS_tfib_r, PlanRegen.hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _].
unfold HS_tfib_list_r, HSL_r in F |- *.
destruct (Z.eqb r 1); exact (in_map snd _ _ F).
Qed.
(* At the run's own flag, [rseq_z b] for the kernel build's [kb_rseq]. *)
Lemma stkaux_of : forall b h ch, HS_tfib_r (rseq_z b) h = Some ch -> stk_aux_chk (rseq_z b) ch = true.
Proof.
intros b h ch H. pose proof (stkaux_In_r _ h ch H) as Hin. destruct tfib_holes_stkaux as [H0 H1].
destruct b; cbn [rseq_z Z.eqb] in Hin |- *.
- exact (proj1 (forallb_forall _ _) H1 ch Hin).
- exact (proj1 (forallb_forall _ _) H0 ch Hin).
Qed.
