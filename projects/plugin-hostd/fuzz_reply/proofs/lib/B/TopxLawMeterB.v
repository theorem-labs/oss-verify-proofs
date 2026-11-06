(* Image B's meter frame law MO_FR at KF-COUNT #4's text (a Theorem Labs lane's ruling 09:32Z, the same line in every A and B
   file: `Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.`), for the B top lib/B/W_LLVMFuzzerTestOneInput_top_x.v.
   The names match image A's lib/A/TopxLawMeter.v (a Theorem Labs lane; a Theorem Labs lane's ruling 12:27Z), and the generic
   one takes KF-COUNT step 3's `_m` suffix (a Theorem Labs lane / a Theorem Labs lane / a Theorem Labs lane, agreed 12:57Z):
   - topx_MO_FR: that text at the instance meter ameter_triv (Reusable/YCbp.v: mo_le is True), as A's topx_MO_FR.
     The instance plugs it: MO_FR := topx_MO_FR.
   - topx_MO_FR_m: the same text generic in the meter (KF-COUNT #7): for any MT with the meter laws (ameter_laws,
     Reusable/YC5d.v) whose mo_le does not see a set_fs on its right (mo_fs_inv), from mo_le_refl.  set_fs
     (Reusable/YG00.v) rebuilds the state with every field but st_fs unchanged, st_secs included, so a meter that reads
     no st_fs meets mo_fs_inv; at the counting meter MT_sec the plug is topx_MO_FR_m MT_sec MLAW_sec MFS_sec.
   Requires only Reusable files (no image name occurs in the text).
   proves no function (kind: model lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG00 YG0d YC5d YCbp YM05.
Open Scope Z_scope.

(* KF-COUNT #4: top_x's MO_FR at the instance meter ameter_triv (A's TopxLawMeter.topx_MO_FR) *)
Lemma topx_MO_FR : forall s f, mo_le ameter_triv s (set_fs f s) 0.
Proof. intros s f. exact I. Qed.
(* the window's earlier name for the same lemma (6bf6c172f46), kept as a corollary (W8: an old name stays at
   ameter_triv) *)
Lemma topx_MO_FR_triv : forall s f, mo_le ameter_triv s (set_fs f s) 0.
Proof. exact topx_MO_FR. Qed.

(* a set_fs on the right of mo_le is invisible to the meter *)
Definition mo_fs_inv (MT : ameter_ops) : Prop :=
  forall s s' f m, mo_le MT s s' m -> mo_le MT s (set_fs f s') m.

Lemma mo_fs_inv_triv : mo_fs_inv ameter_triv.
Proof. intros s s' f m _. exact I. Qed.

Section m.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MFS : mo_fs_inv MT.

(* KF-COUNT #4 + #7: the same text at the meter Variable *)
Lemma topx_MO_FR_m : forall s f, mo_le MT s (set_fs f s) 0.
Proof. intros s f. apply MFS. exact (mo_le_refl MT MLAW s). Qed.
End m.

Print Assumptions topx_MO_FR.
Print Assumptions topx_MO_FR_m.
