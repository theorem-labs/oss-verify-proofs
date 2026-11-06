From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB.
Import ListNotations.
Local Open Scope Z_scope.

(* Glue for the slot's SR walk: a Kind A run (on the normalized memory) inside the walk, register reads of mkR
   states, and the memory transports of a run back to the real memory. *)

Lemma getr_mkR_val : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31,
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31 in
  getr R 1 = x1 /\ getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
  getr R 10 = x10 /\ getr R 11 = x11 /\ getr R 12 = x12 /\
  getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
  getr R 23 = x23 /\ getr R 24 = x24 /\ getr R 25 = x25 /\ getr R 26 = x26 /\ getr R 27 = x27.
Proof. intros. repeat split; reflexivity. Qed.

Section Bridge.
Context {fx : FPState}.

Lemma sr_run : forall regs pc mem md (P : config -> Prop) (Q : machine_state -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R F' pc' fc' m0, s0 = MS R F' pc' fc' None m0 (seg_rom rsegs)) ->
  (forall R F' pc' fc' m0 regs' mem',
     Q (MS R F' pc' fc' None m0 (seg_rom rsegs)) -> mem_rel rsegs mem' m0 -> ro_same rsegs mem mem' ->
     (forall r, getr regs' r = getr R r) ->
     SR rsegs (mkCfg (@mkst (mkFP F' fc') regs' pc' mem' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md P Q Hh Hl RO EV SHAPE K.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO | exact EV]. }
  intros ms' (can & (s0 & Q0 & REL & ROS) & EQ).
  destruct (SHAPE s0 Q0) as (R & F' & pc' & fc' & m0 & ->).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
  remember (ms_mem can) as mc eqn:Emc. subst can. clear Emc.
  destruct (@eqv_mkst (mkFP F' fc') R F' pc' fc' mc (seg_rom rsegs) ms' EQ eq_refl eq_refl) as (R' & -> & X).
  apply (K R F' pc' fc' m0 R' mc Q0 HR ROS).
  intros r. exact (KindBGlue.kb_getr_eqv R R' X r).
Qed.

End Bridge.
