(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2 Require Import T_Src2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit InitLib RootSrc2.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan SI.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module InitSrc2.

Lemma root_eq : T_Src2.ROOT2 =
  SS (s_pc ROOT_Src2) (s_rf ROOT_Src2) (s_ff ROOT_Src2) (s_resv ROOT_Src2) (s_regs ROOT_Src2) (s_facts ROOT_Src2) ROOT_OPS ROOT_PRIV (s_next ROOT_Src2).
Proof. reflexivity. Qed.

Definition SEGTOP : Z := 16777216.
Lemma segs_top : InitLib.segs_below SEGS SEGTOP = true. Proof. vm_compute. reflexivity. Qed.
Lemma segtop_low : SEGTOP <= 0x7fff7f800000. Proof. cbv. discriminate. Qed.
Lemma phA : Z.of_N (ph_addr PH) = 65600. Proof. reflexivity. Qed.
Lemma phE : Z.of_N (ph_ent PH) = 56. Proof. reflexivity. Qed.
Lemma phN : Z.of_N (ph_num PH) = 10. Proof. reflexivity. Qed.

Section Entry.
Variables (sp : word) (argv envp : list (list byte)) (uid hwcap : word) (draw : EntryDraw) (xb : int -> list byte).
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hhw : valid_hwcap hwcap.
Hypothesis Hargc2 : length argv = 2%nat.

Definition E0 : env := InitLib.E0 sp argv envp uid hwcap draw xb.

Local Ltac CLOSE := first [eassumption | exact PH | exact SEGS | exact PC | exact SEGTOP].

Lemma facts_ok : facts_hold E0 FACTS0.
Proof.
  pose proof segs_top as Hsegs. pose proof segtop_low as Htop. pose proof phA as HA. pose proof phE as HE. pose proof phN as HN.
  unfold E0, FACTS0, facts_hold. repeat apply Forall_cons; try apply Forall_nil.
  - unshelve (eapply InitLib.f_rnd_align); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_auxv); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_rnd8); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_a0); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_rnd); CLOSE.
  - unshelve (eapply InitLib.f_sp_range); CLOSE.
  - unshelve (eapply InitLib.f_sp_align); CLOSE.
  - unshelve (eapply InitLib.f_win2); CLOSE.
  - unshelve (eapply InitLib.f_win3); CLOSE.
  - unshelve (eapply InitLib.f_win5); CLOSE.
  - unshelve (eapply InitLib.f_win6); CLOSE.
  - unshelve (eapply InitLib.f_hwcap); CLOSE.
  - unshelve (eapply InitLib.f_win10); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_a1); CLOSE.
  - unshelve (eapply InitLib.f_envp2); CLOSE.
  - unshelve (eapply InitLib.f_auxv); CLOSE.
  - unshelve (eapply InitLib.f_size8_lo); CLOSE.
  - unshelve (eapply InitLib.f_size8_hi); CLOSE.
  - unshelve (eapply InitLib.f_size9_lo); CLOSE.
  - unshelve (eapply InitLib.f_size9_hi); CLOSE.
  - unshelve (eapply InitLib.f_size10_lo); CLOSE.
  - unshelve (eapply InitLib.f_size10_hi); CLOSE.
  - unshelve (eapply InitLib.f_a0_end); CLOSE.
  - unshelve (eapply InitLib.f_a1_end); CLOSE.
  - unshelve (eapply InitLib.f_win12); CLOSE.
  - unshelve (eapply InitLib.f_align12); CLOSE.
  - unshelve (eapply InitLib.f_12_le_5); CLOSE.
  - unshelve (eapply InitLib.f_end5_12); CLOSE.
  - unshelve (eapply InitLib.f_sp_le_12); CLOSE.
  - unshelve (eapply InitLib.f_end12); CLOSE.
  - unshelve (eapply InitLib.f_12_le_10); CLOSE.
  - unshelve (eapply InitLib.f_end10_12); CLOSE.
Qed.

Theorem root_st_ok : forall (OPS : optable) model, plain_table OPS -> mfacts model ->
  st_ok SEGS OPS E0 ROOT_Src2 (init_machine_state SEGS PC PH sp draw argv envp uid hwcap) model.
Proof.
  intros OPS model PL Hmf.
  change ROOT_Src2 with (SS 126036%uint63 (InitLib.RFc) (InitLib.FFc) RNone (InitLib.REGS_F) FACTS0 [] [] 64%uint63).
  pose proof segs_top as Hsegs. pose proof segtop_low as Htop. pose proof phA as HA. pose proof phE as HE. pose proof phN as HN.
  pose proof facts_ok as HF. unfold E0 in *.
  unshelve (eapply InitLib.st_ok_F); first [eassumption | reflexivity | exact PH | exact SEGS | exact PC | exact SEGTOP].
Qed.

End Entry.

Theorem init_ok : forall (OPS : optable) (inp : ProcInput) sp brk0 mb draw lim (xb : int -> list byte),
  plain_table OPS -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_hwcap (in_hwcap inp) -> in_va_size inp = Sv48 ->
  length (in_argv inp) = 2%nat ->
  valid_entry (mkImage SEGS PC PH) (mkEntry sp brk0 mb draw) inp ->
  let E := E0 sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw xb in
  InitLib.PB_STD (eb E) /\ InitLib.PB_ARG1 (eb E) /\
    st_ok SEGS OPS E ROOT_Src2 (cfg_ms (init_config SEGS PC PH sp brk0 mb draw lim inp))
                               (cfg_model (init_config SEGS PC PH sp brk0 mb draw lim inp)).
Proof.
  intros OPS inp sp brk0 mb draw lim xb PL Hva Hve Hhw Hsz Hfam Hen.
  apply (proj1 (valid_entry_sv48 _ _ _ Hsz)) in Hen. destruct Hen as (Hsp & _ & _ & Hfit).
  cbv zeta. split; [|split].
  - unshelve (eapply InitLib.PB_E0); first [eassumption | exact PH | exact SEGS | exact PC | exact draw].
  - unshelve (eapply InitLib.PB1_E0); first [eassumption | exact PH | exact SEGS | exact PC | exact draw].
  - apply root_st_ok; try assumption. split; reflexivity.
Qed.

End InitSrc2.
