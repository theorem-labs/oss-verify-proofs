From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
Open Scope Z_scope.

Definition G_REC : Z := 0x34028.
Definition REC_SC : Z := 0x33ff0.

Definition g_rec_rep (segs : list Segment) (L : layout) (A : astate) (mem : word -> option byte) (R : rstate)
    (O : list (Z * Z)) : Prop :=
  rec_rep segs G_REC REC_SC L A mem R O.

Definition g_rec_G1 (segs : list Segment) (L : layout) (A : astate) (mem : word -> option byte) : Prop :=
  rec_G1 segs G_REC REC_SC L A mem.

Lemma g_rec_layout : G_REC mod 8 = 0 /\ REC_SC mod 8 = 0 /\ iv_apart G_REC REC_SIZE REC_SC SC_SIZE.
Proof. unfold G_REC, REC_SC, iv_apart, REC_SIZE, SC_SIZE. split; [reflexivity|]. split; [reflexivity|]. lia. Qed.
