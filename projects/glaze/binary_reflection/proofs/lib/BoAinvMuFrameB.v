(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvConstRw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvMuFrameA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvConstRw3.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition MU_A : Z := 0x104e30.
Definition mu_rows_ok (mu : Z) (cs : list (Z * nat * Z)) : Prop :=
  Forall (fun c : Z * nat * Z => fst (fst c) + Z.of_nat (snd (fst c)) <= mu \/ mu + 8 <= fst (fst c) \/ c = (mu, 8%nat, 0)) cs.

(* [comment removed for export] *)
Definition mu_rows_okb (mu : Z) (cs : list (Z * nat * Z)) : bool :=
  forallb (fun c : Z * nat * Z => (fst (fst c) + Z.of_nat (snd (fst c)) <=? mu) || (mu + 8 <=? fst (fst c))
                                  || ((fst (fst c) =? mu) && Nat.eqb (snd (fst c)) 8 && (snd c =? 0))) cs.
Lemma mu_rows_ok_of_b : forall mu cs, mu_rows_okb mu cs = true -> mu_rows_ok mu cs.
Proof.
  intros mu cs H. unfold mu_rows_okb in H. rewrite forallb_forall in H. apply Forall_forall. intros [[a n] v] Hc. pose proof (H _ Hc) as Hb. cbn [fst snd] in *.
  apply orb_true_iff in Hb as [Hb | Hb]; [apply orb_true_iff in Hb as [Hb | Hb]|].
  - left. apply Z.leb_le in Hb. exact Hb.
  - right; left. apply Z.leb_le in Hb. exact Hb.
  - right; right. apply andb_true_iff in Hb as [Hb Hv]. apply andb_true_iff in Hb as [Ha Hn].
    apply Z.eqb_eq in Ha. apply Nat.eqb_eq in Hn. apply Z.eqb_eq in Hv. subst. reflexivity.
Qed.

Section MuA.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = asan_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp asan_addrs.
  Hypothesis K_rows : mu_rows_ok MU_A (bt_consts bt).

End MuA.
End AsAinvMuFrameA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvConstRw3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvConstRw3 AsAinvMuFrameA.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition MU_B : Z := 0x10ba70.

Section MuB.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BT_IA : bt_ia bt = both_addrs.
  Hypothesis BT_TLSFS : bt_tls_fs bt = ia_tp both_addrs.
  Hypothesis K_rows : mu_rows_ok MU_B (bt_consts bt).

End MuB.
