(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the memory overlay stays empty over a window that no
   writable segment covers -- the vDSO text pages of the run.  At 727298f3 the run maps the vDSO
   pair read-only ([Run.vdso_segments], Run.v:290-306, "r--"), and the model refuses every write
   the process could make there:
     - a store needs [RiscvSemantics.store_ok] (RiscvSemantics.v:697-705), which asks the writable
       view [wview] (:616-628) at every byte, and [wview] is [None] off the overlay unless a
       writable segment holds the byte; the interpreter stores only after that check
       ([interp_eff_accesses]'s [EStore] arm, :1020-1033);
     - a system call's output buffers are checked against the same view
       ([State.in_wmem], State.v:663-674);
     - [Run.apply_effect] (Run.v:176-189) writes exactly the effect's declared ranges.
   This file proves the store half for any segment list ([vclean] kept by [step], [msteps] and
   [evt]) and the effect half for an effect with no writes and no copies whose zero-filled ranges
   miss the window ([nret_clean]); [eff_unmaps] only erases.  It names nothing of a binary, so a
   unit that reads the vDSO through ordinary loads copies it whole. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec StoreOk.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec ITree.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Clean.
  Variable segs : list Segment.
  Variables vlo vhi : Z.
  (* no writable segment of [segs] holds a byte of the window *)
  Hypothesis Hnw : forall (x : word) s, vlo <= bv_unsigned x < vhi ->
    find_segment segs (bv_unsigned x) 1 = Some s -> seg_writable s = false.

  Definition vclean (m : word -> option byte) : Prop :=
    forall x : word, vlo <= bv_unsigned x < vhi -> m x = None.

  Lemma wview_none_of_clean : forall m x, vclean m -> vlo <= bv_unsigned x < vhi -> wview segs m x = None.
  Proof.
    intros m x C Hx. unfold wview. rewrite (C x Hx).
    destruct (find_segment segs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnw x s Hx E). reflexivity.
  Qed.

  Lemma wview_none_mem : forall m x, wview segs m x = None -> m x = None.
  Proof. intros m x H. unfold wview in H. destruct (m x); [discriminate H| reflexivity]. Qed.

  (* a store that [store_ok] admits leaves every byte outside the writable view alone *)
  Lemma write_to_mem_keep : forall bs m a x,
    store_ok segs m a (length bs) = true -> wview segs m x = None -> write_to_mem m a bs x = m x.
  Proof.
    induction bs as [|b bs IH]; intros m a x Hs Hx; [reflexivity|].
    cbn [length store_ok] in Hs. cbn [write_to_mem].
    destruct (wview segs m a) as [b0|] eqn:Ea; [|discriminate Hs].
    assert (Nxa : x <> a) by (intros ->; rewrite Hx in Ea; discriminate Ea).
    rewrite IH.
    - cbv beta. rewrite (bv_eqb_neq x a Nxa). reflexivity.
    - eapply store_ok_mono; [| exact Hs].
      intros y Hy. cbv beta. destruct (bv_eqb y a); [discriminate| exact Hy].
    - unfold wview in Hx |- *. cbv beta. rewrite (bv_eqb_neq x a Nxa). exact Hx.
  Qed.

  Lemma interp_keep : forall t m rep x,
    interp_eff_accesses segs t m = MachineOk rep -> wview segs m x = None ->
    wview segs (snd (access_value _ rep)) x = None.
  Proof.
    induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m rep x Hi Hx; revert Hi;
      cbn [interp_eff_accesses]; try (intros Hi; discriminate Hi).
    - intros Hi. injection Hi as <-. exact Hx.
    - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|].
      2: (repeat match goal with |- context [if ?b then _ else _] => destruct b end); intros Hi; discriminate Hi.
      match goal with |- context [interp_eff_accesses ?s ?t ?mm] =>
        destruct (interp_eff_accesses s t mm) as [r| |] eqn:E end; intros Hi; cbv beta iota in Hi; try discriminate Hi.
      injection Hi as <-. cbn [access_value]. exact (IH _ m r x E Hx).
    - destruct (store_ok segs m a (width_bytes n)) eqn:Hs; [| intros Hi; discriminate Hi].
      match goal with |- context [interp_eff_accesses ?s ?t ?mm] =>
        destruct (interp_eff_accesses s t mm) as [r| |] eqn:E end; intros Hi; cbv beta iota in Hi; try discriminate Hi.
      injection Hi as <-. cbn [access_value]. apply (IH _ r x E).
      unfold wview in Hx |- *.
      rewrite (write_to_mem_keep (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a x);
        [exact Hx | rewrite length_Z_to_le_bytes; exact Hs | unfold wview; exact Hx].
  Qed.

  Lemma fetch_failure_not_ok : forall m a st, fetch_failure segs m a <> MachineOk st.
  Proof.
    intros m a st. unfold fetch_failure. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
  Qed.

  Lemma decode_keep : forall st w rep x, decode_exec_accesses segs st w = MachineOk rep ->
    wview segs (ms_mem st) x = None -> wview segs (ms_mem (access_value _ rep)) x = None.
  Proof.
    intros st w rep x H Hx. revert H. unfold decode_exec_accesses.
    destruct (is_ecall w); [intros H; injection H as <-; exact Hx|].
    destruct (decode_any w) as [[i isz]|].
    2: destruct (is_defined_illegal w); intros H; discriminate H.
    match goal with |- context [interp_eff_accesses ?s ?t ?mm] =>
      destruct (interp_eff_accesses s t mm) as [r| |] eqn:E end; intros H; cbv beta iota in H; try discriminate H.
    pose proof (interp_keep _ _ r x E Hx) as K.
    destruct r as [[c m'] acc]. cbn [access_value snd] in K, H.
    injection H as <-. cbn [ms_mem]. exact K.
  Qed.

  Lemma step_keep : forall ms ms' x, RiscvSemantics.step segs ms = MachineOk ms' ->
    wview segs (ms_mem ms) x = None -> wview segs (ms_mem ms') x = None.
  Proof.
    intros ms ms' x H Hx. revert H. unfold RiscvSemantics.step, drop_access_report, step_accesses.
    destruct (fetch_word segs (ms_pc ms)) as [w|].
    2: destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
    3: destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
    4: destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) as [st| |] eqn:Ef;
         [exfalso; exact (fetch_failure_not_ok _ _ _ Ef) | intros H; discriminate H | intros H; discriminate H].
    all: destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; intros H; cbv beta iota in H; try discriminate H;
         injection H as <-; exact (decode_keep _ _ rep x E Hx).
  Qed.

  Lemma step_clean : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' ->
    vclean (ms_mem ms) -> vclean (ms_mem ms').
  Proof.
    intros ms ms' H C x Hx. apply wview_none_mem.
    exact (step_keep ms ms' x H (wview_none_of_clean _ x C Hx)).
  Qed.

  Lemma msteps_clean : forall ms ms', Exec.msteps segs ms ms' -> vclean (ms_mem ms) -> vclean (ms_mem ms').
  Proof.
    intros ms ms' H. induction H as [ms | ms ms1 ms2 [_ Hs] _ IH]; intros C; [exact C|].
    apply IH. exact (step_clean _ _ Hs C).
  Qed.

  Lemma evt_clean : forall (P : machine_state -> Prop) ms, Exec.evt segs P ms -> vclean (ms_mem ms) ->
    Exec.evt segs (fun ms' => P ms' /\ vclean (ms_mem ms')) ms.
  Proof.
    intros P ms (ms' & Hm & HP) C. exists ms'. split; [exact Hm|]. split; [exact HP| exact (msteps_clean _ _ Hm C)].
  Qed.

  (** The effect half: zero-filled ranges that miss the window, no writes, no copies. *)
  Definition range_off (z : word * word) : Prop :=
    bv_unsigned (fst z) + bv_unsigned (snd z) <= vlo \/ vhi <= bv_unsigned (fst z).

  Lemma zeros_cover_off : forall zs x, vlo <= bv_unsigned x < vhi -> Forall range_off zs ->
    zeros_cover zs x = false.
  Proof.
    intros zs x Hx H. unfold zeros_cover. induction H as [|z zs Hz _ IH]; [reflexivity|].
    cbn [existsb]. rewrite IH, Bool.orb_false_r.
    unfold range_off in Hz. apply Bool.andb_false_iff.
    destruct Hz as [Hz|Hz]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
  Qed.

  Lemma nret_clean : forall ms eff,
    eff_writes eff = [] -> eff_copies eff = [] -> Forall range_off (eff_zeros eff) ->
    vclean (ms_mem ms) -> vclean (ms_mem (ITree.nret ms eff)).
  Proof.
    intros ms eff Hw Hc Hz C x Hx. unfold ITree.nret, advance_past_svc, apply_effect. cbn [ms_mem].
    rewrite Hw, Hc. cbn [apply_writes apply_copies].
    pose proof (zeros_cover_off _ x Hx Hz) as Zx. revert Zx.
    try change (ms_mem (set_reg ms 10 (eff_ret eff))) with (ms_mem ms).
    unfold apply_zeros, apply_unmaps.
    destruct (eff_zeros eff) as [|z zs]; destruct (eff_unmaps eff) as [|u us]; cbv beta; intros Zx;
      rewrite ?Zx; try (destruct (zeros_cover (u :: us) x)); first [reflexivity | exact (C x Hx)].
  Qed.
End Clean.
