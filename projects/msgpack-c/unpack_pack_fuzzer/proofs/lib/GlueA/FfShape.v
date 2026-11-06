(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib ValP.
Open Scope Z_scope.
Unset Lia Cache.

Definition ff_post (st : sstate) (RT : r5) (kf shf : int) (h2 : list sv) : sstate :=
  SS (PrimInt63.add (s_pc st) 8%uint63) (rf_set (s_rf st) RT (VP (s_next st) wzero)) (s_ff st) (s_resv st)
     (IMap.remove shf (IMap.remove kf (s_regs st))) (s_facts st) (set_op HEAP_ID h2 (s_ops st)) (s_priv st)
     (PrimInt63.add (s_next st) 1%uint63).

Lemma setr_nz : forall st r v, r5_eqb r X0 = false ->
  setr st r v = SS (s_pc st) (rf_set (s_rf st) r v) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Proof. intros st r v H. destruct r; try reflexivity. discriminate H. Qed.

Lemma ff_apply_shape : forall RF RT OFF st sts, ActrB.fake_free_apply RF RT OFF st = Some sts ->
  exists kf shf hargs wnl i0 rsh h1 h2,
    s_resv st = RNone /\ getr st RF = VP kf wzero /\ ActrA.aheap_windows st = Some (hargs, wnl)
    /\ ActrB.find_twin (s_facts st) kf = Some shf
    /\ heap_find_window hargs (VP kf wzero) = Some (i0, VL (wlit OFF), VL ActrB.K_FRAME)
    /\ IMap.find shf (s_regs st) = Some rsh /\ fresh_ok st = true /\ r5_eqb RT X0 = false
    /\ ActrA.afree_ok_k ActrB.K_FRAME ActrB.K_FTWIN st wnl kf shf = true
    /\ ActrA.stack_room_g st 0%uint63 = true /\ ActrA.sp_floor_ok st hargs = true
    /\ rg_lo rsh = 0%uint63 /\ (exists lent kdt, CtrA.win_lookup wnl shf = Some (lent, kdt) /\ known_eq (s_facts st) (rg_hi rsh) lent = true)
    /\ ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.K_FRAME = Some h1
    /\ ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.K_FTWIN = Some h2
    /\ sts = [ff_post st RT kf shf h2].
Proof.
  intros RF RT OFF st sts H. unfold ActrB.fake_free_apply in H.
  destruct (s_resv st) eqn:RV; try discriminate H.
  destruct (getr st RF) as [|kf z| | | | | | | | |] eqn:GR; try discriminate H.
  destruct (ActrA.aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (ActrB.find_twin (s_facts st) kf) as [shf|] eqn:FT; [|discriminate H].
  destruct (heap_find_window hargs (VP kf wzero)) as [[[i0 len] kd]|] eqn:FW; [|discriminate H].
  destruct (IMap.find shf (s_regs st)) as [rsh|] eqn:FR; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  destruct (ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.K_FRAME) as [h1|] eqn:H1; [|discriminate H].
  destruct (ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.K_FTWIN) as [h2|] eqn:H2; [|discriminate H].
  unfold fresh in H. cbv zeta in H. injection H as <-.
  apply weqb_eq in CK. subst z. apply sv_eqb_eq in Q6. apply sv_eqb_eq in Q5. subst kd len. apply negb_true_iff in Q4.
  apply Uint63.eqb_correct in Q0.
  destruct (CtrA.win_lookup wnl shf) as [[lent kdt]|] eqn:WLT; [|discriminate Q].
  exists kf, shf, hargs, wnl, i0, rsh, h1, h2. repeat (split; [reflexivity || assumption|]).
  split; [exists lent, kdt; split; [exact WLT| exact Q]|]. repeat (split; [reflexivity || assumption|]).
  rewrite (setr_nz _ RT _ Q4). unfold ff_post, setpc, set_ops, setregs, set_next. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. reflexivity.
Qed.

Lemma find_window_In : forall n ws kf l sz kdw wnl,
  find_window n ws (VP kf wzero) = Some (l, sz, VL kdw) -> weqb kdw wzero = false ->
  CtrA.nonstack_windows n ws = Some wnl -> In (kf, sz, kdw) wnl.
Proof.
  induction n as [|n IH]; intros ws kf l sz kdw wnl FW KZ NW; [discriminate FW|].
  destruct ws as [|l0 [|sz0 [|kd0 ws']]]; try discriminate FW. cbn [find_window] in FW. cbn [CtrA.nonstack_windows] in NW.
  destruct kd0 as [kd0| | | | | | | | | |]; try discriminate NW.
  destruct (CtrA.nonstack_windows n ws') as [l1|] eqn:NW1; [|discriminate NW].
  destruct (sv_eqb l0 (VP kf wzero)) eqn:EQ.
  - injection FW as <- <- <-. apply sv_eqb_eq in EQ. subst l0. rewrite KZ in NW. rewrite weqb_refl in NW. cbn [andb] in NW.
    match type of NW with (if ?c then _ else _) = _ => destruct c; [|discriminate NW] end. injection NW as <-. left. reflexivity.
  - specialize (IH ws' kf l sz kdw l1 FW KZ NW1).
    destruct (weqb kd0 wzero); [injection NW as <-; exact IH|].
    destruct l0 as [|k o| | | | | | | | |]; try discriminate NW.
    match type of NW with (if ?c then _ else _) = _ => destruct c; [|discriminate NW] end. injection NW as <-. right. exact IH.
Qed.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import ActrB.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib ValP.
Open Scope Z_scope.
Unset Lia Cache.

Definition ff_post (st : sstate) (RT : r5) (kf shf : int) (h2 : list sv) : sstate :=
  SS (PrimInt63.add (s_pc st) 8%uint63) (rf_set (s_rf st) RT (VP (s_next st) wzero)) (s_ff st) (s_resv st)
     (IMap.remove shf (IMap.remove kf (s_regs st))) (s_facts st) (set_op HEAP_ID h2 (s_ops st)) (s_priv st)
     (PrimInt63.add (s_next st) 1%uint63).

Lemma setr_nz : forall st r v, r5_eqb r X0 = false ->
  setr st r v = SS (s_pc st) (rf_set (s_rf st) r v) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Proof. intros st r v H. destruct r; try reflexivity. discriminate H. Qed.

Lemma ff_apply_shape : forall RF RT OFF st sts, ActrB.TwinB.ActrB.fake_free_apply RF RT OFF st = Some sts ->
  exists kf shf hargs wnl i0 rsh h1 h2,
    s_resv st = RNone /\ getr st RF = VP kf wzero /\ ActrA.aheap_windows st = Some (hargs, wnl)
    /\ ActrB.TwinB.ActrB.find_twin (s_facts st) kf = Some shf
    /\ heap_find_window hargs (VP kf wzero) = Some (i0, VL (wlit OFF), VL ActrB.TwinB.ActrB.K_FRAME)
    /\ IMap.find shf (s_regs st) = Some rsh /\ fresh_ok st = true /\ r5_eqb RT X0 = false
    /\ ActrA.afree_ok_k ActrB.TwinB.ActrB.K_FRAME ActrB.TwinB.ActrB.K_FTWIN st wnl kf shf = true
    /\ ActrA.stack_room_g st 0%uint63 = true /\ ActrA.sp_floor_ok st hargs = true
    /\ rg_lo rsh = 0%uint63 /\ (exists lent kdt, CtrA.win_lookup wnl shf = Some (lent, kdt) /\ known_eq (s_facts st) (rg_hi rsh) lent = true)
    /\ ActrB.TwinB.ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.TwinB.ActrB.K_FRAME = Some h1
    /\ ActrB.TwinB.ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.TwinB.ActrB.K_FTWIN = Some h2
    /\ sts = [ff_post st RT kf shf h2].
Proof.
  intros RF RT OFF st sts H. unfold ActrB.TwinB.ActrB.fake_free_apply in H.
  destruct (s_resv st) eqn:RV; try discriminate H.
  destruct (getr st RF) as [|kf z| | | | | | | | |] eqn:GR; try discriminate H.
  destruct (ActrA.aheap_windows st) as [[hargs wnl]|] eqn:AW; [|discriminate H].
  destruct (ActrB.TwinB.ActrB.find_twin (s_facts st) kf) as [shf|] eqn:FT; [|discriminate H].
  destruct (heap_find_window hargs (VP kf wzero)) as [[[i0 len] kd]|] eqn:FW; [|discriminate H].
  destruct (IMap.find shf (s_regs st)) as [rsh|] eqn:FR; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  destruct (ActrB.TwinB.ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.TwinB.ActrB.K_FRAME) as [h1|] eqn:H1; [|discriminate H].
  destruct (ActrB.TwinB.ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.TwinB.ActrB.K_FTWIN) as [h2|] eqn:H2; [|discriminate H].
  unfold fresh in H. cbv zeta in H. injection H as <-.
  apply weqb_eq in CK. subst z. apply sv_eqb_eq in Q6. apply sv_eqb_eq in Q5. subst kd len. apply negb_true_iff in Q4.
  apply Uint63.eqb_correct in Q0.
  destruct (CtrA.win_lookup wnl shf) as [[lent kdt]|] eqn:WLT; [|discriminate Q].
  exists kf, shf, hargs, wnl, i0, rsh, h1, h2. repeat (split; [reflexivity || assumption|]).
  split; [exists lent, kdt; split; [exact WLT| exact Q]|]. repeat (split; [reflexivity || assumption|]).
  rewrite (setr_nz _ RT _ Q4). unfold ff_post, setpc, set_ops, setregs, set_next. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]. reflexivity.
Qed.

Lemma find_window_In : forall n ws kf l sz kdw wnl,
  find_window n ws (VP kf wzero) = Some (l, sz, VL kdw) -> weqb kdw wzero = false ->
  CtrA.nonstack_windows n ws = Some wnl -> In (kf, sz, kdw) wnl.
Proof.
  induction n as [|n IH]; intros ws kf l sz kdw wnl FW KZ NW; [discriminate FW|].
  destruct ws as [|l0 [|sz0 [|kd0 ws']]]; try discriminate FW. cbn [find_window] in FW. cbn [CtrA.nonstack_windows] in NW.
  destruct kd0 as [kd0| | | | | | | | | |]; try discriminate NW.
  destruct (CtrA.nonstack_windows n ws') as [l1|] eqn:NW1; [|discriminate NW].
  destruct (sv_eqb l0 (VP kf wzero)) eqn:EQ.
  - injection FW as <- <- <-. apply sv_eqb_eq in EQ. subst l0. rewrite KZ in NW. rewrite weqb_refl in NW. cbn [andb] in NW.
    match type of NW with (if ?c then _ else _) = _ => destruct c; [|discriminate NW] end. injection NW as <-. left. reflexivity.
  - specialize (IH ws' kf l sz kdw l1 FW KZ NW1).
    destruct (weqb kd0 wzero); [injection NW as <-; exact IH|].
    destruct l0 as [|k o| | | | | | | | |]; try discriminate NW.
    match type of NW with (if ?c then _ else _) = _ => destruct c; [|discriminate NW] end. injection NW as <-. right. exact IH.
Qed.
End TwinB.
