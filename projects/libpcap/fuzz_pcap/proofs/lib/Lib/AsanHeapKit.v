(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SpinAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.DivergeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AsanAcctShape.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanPlacement.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require StdioSymDrive EntryGlue. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require NodesFs__Lib. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanBlock__Lib. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.NodesFs__Lib.NodesMm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBlock__Lib.AsanBlock.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance asanheapkit_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mem_denot_nil : forall E m, mem_denot E m [] = m.
Proof. reflexivity. Qed.

Lemma munrestrict_mrestrict_self : forall H M, munrestrict H M (mrestrict H M) = M.
Proof. intros H M. extensionality a. unfold munrestrict, mrestrict. destruct (H a); reflexivity. Qed.

Lemma munrestrict_denot_nil : forall H E M, munrestrict H M (mem_denot E (mrestrict H M) []) = M.
Proof. intros. rewrite mem_denot_nil. apply munrestrict_mrestrict_self. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_ok_join1 : forall vals ebs sr R (ra : reg),
  sr_vars_lt (length vals) sr = true -> ra <> 0%bv ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  regs_ok (Env (vals_ev (vals ++ [getr R ra])) ebs) (sr_upd sr (ridx ra) (EVar (length vals))) R.
Proof.
  intros vals ebs sr R ra Hv Ha HR.
  apply (regs_ok_upd1 _ sr R R ra); [apply env_app_regs; assumption | exact Ha | | intros; reflexivity].
  cbn [edenot ev]. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
Qed.

Lemma know_ok_join : forall segs vals ebs M kn (c : word),
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ [c])) ebs) M kn.
Proof. intros. apply env_app_know; assumption. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac model_next HS HL Hh :=
  lazymatch type of HS with
  | same_but_materialized ?m ?m' =>
      first [ apply (sbm_lazy_cover m m' HS) in HL | fail "model_next: HL" ];
      first [ rewrite <- (sbm_halted m m' HS) in Hh | fail "model_next: Hh" ];
      clear HS; try clear m
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section GapVar.
  Variable L : list (word * word).
  Variables nZ FLOOR CEIL : Z.
  Hypothesis HnZ : 0 <= nZ.
  Hypothesis Hfloor : 0 < FLOOR /\ FLOOR mod page_size = 0.
  Hypothesis Hceil : CEIL < 2 ^ 64.

  Definition scan_invV (c : Z) : Prop :=
    c mod page_size = 0 /\ FLOOR <= c /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= CEIL.

  Definition gap_atV (c : Z) : Prop :=
    c mod page_size = 0 /\ FLOOR <= c /\ c + nZ <= CEIL /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  #[using="HnZ Hfloor Hceil"] Lemma scan_ok_or_stepV : forall c, scan_invV c ->
    gap_atV c \/ exists c', scan_invV c' /\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply u_small; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u_small; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      set (c' := page_round_up_Z (B + S)).
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil.page_round_up_Z_ge_all (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095).
      { unfold c', page_round_up_Z, page_size. pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil.page_round_up_Z_aligned'|]. split; lia.
  Qed.

  #[using="HnZ Hfloor Hceil"] Lemma scanV : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_invV c -> exists g, gap_atV g.
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_stepV c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia]. exists c. exact Hok.
    - destruct (scan_ok_or_stepV c Hinv) as [Hok|(c' & Hinv' & Hlt)]; [exists c; exact Hok|].
      apply (IH c'); [lia|exact Hinv'].
  Qed.

  (* [comment removed for export] *)
  #[using="HnZ Hfloor Hceil"] Theorem free_gap_between : FLOOR + nZ + gap_weight nZ (List.filter (live_at FLOOR) L) <= CEIL ->
    exists g, g mod page_size = 0 /\ FLOOR <= g /\ g + nZ <= CEIL /\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros Hslack. destruct (scanV _ FLOOR (le_n _) ltac:(split; [exact (proj2 Hfloor) | split; [lia | exact Hslack]])) as (g & Hg).
    exists g. exact Hg.
  Qed.
End GapVar.

(* [comment removed for export] *)
Theorem grant_exists_between : forall (m : Model) nZ FLOOR,
  0 < nZ -> 0 < FLOOR -> FLOOR mod page_size = 0 ->
  FLOOR + nZ + gap_weight nZ (List.filter (live_at FLOOR) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na_pin m a nZ = true.
Proof.
  intros m nZ FLOOR HnZ Hf Hfa Hslack.
  pose proof (alloc_top_room (m_vmmaps m)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  pose proof (gap_weight_nonneg nZ (List.filter (live_at FLOOR) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) ltac:(lia)) as W0.
  destruct (free_gap_between (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) nZ FLOOR (alloc_top (m_vmmaps m))
              ltac:(lia) (conj Hf Hfa) ltac:(lia) Hslack) as (g & Hal & Hfl & Hc & Hfree).
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin. rewrite u_small by lia.
  unfold page_size in Hal |- *. rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite (proj2 (Z.ltb_lt 0 g)) by lia.
  rewrite (proj2 (Z.leb_le _ _) Hc). rewrite Hfree. reflexivity.
Qed.
