(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec.

Module StreamExec.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require PropExec CatSim CatExec SeqExec.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SeqExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_below : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  (bv_unsigned a < bv_unsigned buf)%Z ->
  write_to_mem mem buf data a = mem a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros data mem buf a Hnw Ha.
  rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros data mem buf a Ha.
  rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply write_to_mem_above. lia.
  - apply write_to_mem_below; [exact Hnb | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs data mem buf Hnw.
  rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc sv mem rom ret buf data.
  destruct data as [|b rest]; [|apply adv_apply_write].
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes
       delivered_writes write_to_mem].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.
End WithFP1.
End StreamExec.


Module WallSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require SimInv.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim PropExec SeqExec CatExec.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SimInv OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SeqExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
#[using="Type"] Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A l H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n bs Hn. unfold len_word, nat_to_word.
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

#[using="Type"] Lemma u_len_word_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n bs Hn Hlen.
  rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
                                unfold two_pow_64; lia).
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat ->
  v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
  unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p n bs Hn Hlen. unfold v_add.
  rewrite u_len_word_firstn by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat_Z : forall (p : word) (k : nat),
  (Z.of_nat k < 2^64)%Z ->
  p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros p k Hk. apply bv_eq.
  rewrite bv_add_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_small
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_sub_len_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n bs Hn Hlen. apply bv_eq.
  rewrite v_sub_small
    by (rewrite u_len_word_firstn by assumption;
        rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
  rewrite u_len_word_firstn by assumption.
  rewrite !len_word_unsigned
    by (unfold two_pow_64; rewrite ?length_skipn; lia).
  rewrite length_skipn. lia.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' rest k H; induction H; [auto|].
  intro Hw. eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms k H.
  remember ([] : list byte) as rest eqn:Hrest.
  induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
  - exists ms. split; [apply mst_refl | exact Hk].
  - subst rest. cbn in Hnb. lia.
  - destruct (IH Hrest) as (ms'' & Hm & Hk).
    exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma sstep_to_wall_inv : forall ms rest k model evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length rest)%nat /\
    evs = map (WriteEv ch) (firstn n rest) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model) /\
    to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
      (skipn n rest) k.
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
  revert Hbm.
  destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont]. intro Hbm.
  destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
              Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
  exists n. repeat split; try assumption.
  apply (Hcont n Hn1 Hn2).
Qed.

#[using="Hfd32"] Lemma to_wall_no_error_sstep : forall ms rest k model evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  ~ sstep segs (mkCfg ms model) evs SError.
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
  destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
    as (n & _ & _ & _ & Hst & _).
  discriminate Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wall_star_admits_mut : forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros model tr_k Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm Hk.
    destruct (IH (length rest) Hnb (Nat.le_refl _)
                (buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (map (WriteEv ch) (firstn (length rest) rest)
              ++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
      by (rewrite firstn_all, skipn_all; reflexivity).
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn (length rest) rest))
                  [(ms_gpr ms 1, length rest)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, length rest)]
                (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
             (map (WriteEv ch) (firstn (length rest) rest)));
      [exact Hh | exact Hsvc | | exact Hh |].
    eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
    rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* [comment removed for export] *)
    intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
    destruct (IH Hbm Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wall_star_admits : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

#[using="Hfd32"] Lemma to_wall_tail_star_admits : forall ms rest k,
  to_wall_tail ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wall_star_only_mut : forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T)).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros model T Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
    subst evs. inversion Hc2; subst c2.
    pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
    rewrite <- (firstn_skipn n rest) at 2.
    rewrite map_app, <- app_assoc.
    apply is_prefix_app_mono. exact Hp.
  - (* [comment removed for export] *)
    intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
      as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm HK tr2 c Hstar2).
Qed.

#[using="Hfd32"] Lemma to_wall_star_only : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv ch) rest ++ T).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
  exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fd ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None;
                   ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
                        (v_addi pc 4) mem rom)
       (skipn n rest) k) ->
  to_wall {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
             ms_svc_pending := Some (getr regs 17); ms_resv := None;
             ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    rest k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k rest regs pc mem rom H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  eapply twl_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wall_k_ex_mut :
  (forall ms rest k, to_wall ms rest k -> exists ms', k ms')
  /\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof. LiaFast.lf_pins LiaFast.u0.
  apply (to_wall_mutind
           (fun ms rest k => exists ms', k ms')
           (fun ms rest k => exists ms', k ms')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH.
    exact (IH (length rest) Hnb (Nat.le_refl _)).
  - intros ms k Hk. exists ms. exact Hk.
  - intros ms rest k Hnb Hw IH. exact IH.
  - intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

#[using="Type"] Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof. LiaFast.lf_pins LiaFast.u0. exact (proj2 to_wall_k_ex_mut). Qed.

#[using="Type"] Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
  to_wallexit bufs code ms ->
  Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
  destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
  destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
  exact (IH code ms' Hk).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
  - exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply msteps_to_wall_tail; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wall_exec_mut : forall model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o)).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros model Q Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK.
    assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
    apply exec_step; [exact Hh | | |].
    + (* [comment removed for export] *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv ch) (firstn (length rest) rest)));
        [exact Hh | exact Hsvc | | exact Hh |].
      * eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & _ & _ & _ & Habs & _).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & Hn1 & Hn2 & -> & Hc' & _).
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
      intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
      rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
  - (* [comment removed for export] *)
    intros ms k Hk Hbm HK.
    eapply exec_conseq; [exact (HK ms Hk) |].
    intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
  - apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * cbn beta. rewrite app_nil_r. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma to_wexit_nil_exec : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

(* [comment removed for export] *)
#[using="Hfd32"] Lemma to_wallexit_exec : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
                 /\ exits_with code tr o).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
  - cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
  - destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq;
      [exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
                Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
    intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wallexit_star_admits : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  exists c, star segs (mkCfg ms model)
              (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c.
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
#[using="Hfd32"] Lemma to_wallexit_no_other_exit : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall code', code' <> code ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne (eq_sym Hx')).
Qed.

#[using="Hfd32"] Lemma to_wallexit_trace_unique : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
  ~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & o & Hm & Heq & _).
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
  apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.

#[using="Hfd32"] Lemma to_wallexit_not_silent : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
  destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.

#[using="Hfd32"] Lemma to_wallexit_star_only : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
    as (tr' & o & _ & HQ).
  cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hfd32"] Lemma to_wallexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof. LiaFast.lf_pins (fun (Hfd32 : LiaFast.U) => LiaFast.u0).
  intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
#[using="Type"] Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
                 /\ exits_with code tr o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
  cbn [omni_run]. unfold init_config.
  exact (to_wallexit_exec segs fd ch Hfd32 bufs code _
           (init_model (segments_reserved segs) brk0 mb sp lim inp)
           eq_refl eq_refl Hfdc Hbm Hw).
Qed.

#[using="Type"] Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

#[using="Type"] Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wall_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wallexit source_segs (Z_to_bv 64 1) bufs code
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_wallexit target_segs (Z_to_bv 64 1) bufs code
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  bufs_modeled bufs ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
    by (split; reflexivity).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
    by (split; reflexivity).
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wall_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wallexit source_segs (Z_to_bv 64 1) bufs code
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_wallexit target_segs (Z_to_bv 64 1) bufs code
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  bufs_modeled bufs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code inp Hsource Htarget Hbm.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp))
    by (split; reflexivity).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved target_segs) abrk amb asp alim inp))
    by (split; reflexivity).
  split.
  { apply no_error_run_modeled.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
             HfdS Hbm Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd alim inp bufs code
               HfdT Hbm Htarget tr).
    reflexivity.
  - cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd alim inp bufs code
             HfdT Hbm Htarget).
Qed.
End WithFP1.
End WallSim.

Module StreamSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require SimInv.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SimInv OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.WallSim.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_arg1_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_read : forall segs ms x8 model o,
  bv_unsigned x8 = 63%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.

Lemma in_arg2_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.

Lemma in_wmem_sys_input : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof.
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_fs_with_stdin : forall s m, m_fs (with_stdin s m) = m_fs m.
Proof. reflexivity. Qed.

Lemma m_halted_with_stdin : forall s m, m_halted (with_stdin s m) = m_halted m.
Proof. reflexivity. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_stdin : forall s m,
  m_vm_lazy (with_stdin s m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  m_halted model = None /\
  m_vm_lazy model = [].

Lemma init_M_loop : forall reserved brk0 mb sp lim inp,
  M_loop (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp. repeat split. Qed.

(* [comment removed for export] *)
Lemma M_loop_take : forall k model,
  M_loop model ->
  M_loop (with_stdin (snd (stream_take (m_stdin model) k)) model).
Proof. intros k model (H0 & H1 & Hh & Hlazy). repeat split; assumption. Qed.

Lemma M_loop_fd1chan : forall model, M_loop model -> fd1chan model.
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

Lemma wseg_ok_read_aux : forall segs n a ms,
  wseg_ok segs a n = true ->
  exists w, read_bytes_aux (ms_writable_byte segs ms) a n = Some w.
Proof.
  intros segs n; induction n as [|n IH]; intros a ms H.
  - exists []. reflexivity.
  - cbn [wseg_ok] in H.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
    apply andb_true_iff in H as [H Hrec].
    apply andb_true_iff in H as [Hwr Hbyte].
    destruct (segment_byte_at (seg_bytes seg)
                (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
      [|discriminate].
    destruct (IH (a + 1) ms Hrec) as [w Hw].
    cbn [read_bytes_aux].
    assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
    { unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
      - eexists; reflexivity.
      - rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
    destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.

Lemma wseg_ok_wdef : forall segs (a len : word) ms,
  wseg_ok segs a (word_to_nat len) = true ->
  exists w, read_bytes_map (ms_writable_byte segs ms) a len = Some w.
Proof.
  intros segs a len ms H. rewrite read_bytes_map_eq.
  apply wseg_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read0_wmem1 : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 w,
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  exists w1, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
               (Z_to_bv 64 1) = Some w1.
Proof.
  intros cnt Hcnt segs ms x8 w Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w);
    [rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; lia | exact Hw].
Qed.

(* [comment removed for export] *)
Lemma read0_wmem_need : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 w s,
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  exists wn, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
               (len_word (fst (stream_take_z s (rw_count_clamp cnt)))) = Some wn.
Proof.
  intros cnt Hcnt segs ms x8 w s Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
  rewrite stream_take_z_eq.
  pose proof (stream_take_length (Z.to_nat (rw_count_clamp cnt)) s) as Hlen.
  pose proof (rw_count_clamp_range cnt) as Hcl.
  unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
    unfold bv_modulus, MAX_RW_COUNT in *; cbn [Z.of_N] in *;
    [ | pose proof (bv_unsigned_in_range 64 cnt) ]; unfold rw_count_clamp in *; lia.
Qed.

Lemma read0_check_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (Z_to_bv 64 0) [] []) model
    = CheckOk model [].
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  rewrite Heof. cbv beta iota.
  unfold check_ret_only. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma read0_check_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
              (map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  (* [comment removed for export] *)
  destruct (m_stdin model) as [|b0 s0] eqn:Hs.
  { exfalso. rewrite stream_take_nil_of_eof in Hpre. subst bs. cbn in Hlo. lia. }
  cbv beta iota.
  rewrite Hw1. cbv beta iota.
  rewrite Hwn. cbv beta iota.
  rewrite !bv_eqb_refl.
  rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length bs))) Hlo).
  rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)).
  rewrite (proj2 (Z.leb_le (Z.of_nat (length bs)) (bv_unsigned cnt)) Hhi).
  rewrite (proj2 (listN_eqb_eq _ _) Hpre).
  rewrite <- (in_wmem_sys_input segs ms x8) in Hw.
  assert (Hlek : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
  { unfold len_word. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hhi | lia]. }
  rewrite (wmem_ok_of_full _ _ _ _ _ Hw Hlek).
  reflexivity.
Qed.

Lemma read0_ok_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_eof; eassumption.
Qed.

Lemma read0_ok_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
        (map (ReadEv (Z_to_bv 64 0)) bs)).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_bytes; eassumption.
Qed.

(* [comment removed for export] *)
Lemma read0_ok_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model buf w eff model' evs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
   model' = model /\ evs = [])
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\
        (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        eff = mkEffect (len_word bs) [(buf, bs)] [] /\
        model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
  intros cnt Hcnt segs ms x8 model buf w eff model' evs
         Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w) as [w1 Hw1];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hw1.
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model)) as [wn Hwn];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hwn.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg1, Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  - (* [comment removed for export] *)
    apply check_ret_only_ok_iff in Hspec.
    destruct Hspec as (-> & -> & ->). left. auto.
  - (* [comment removed for export] *)
    rewrite Hw1 in Hspec. cbv beta iota in Hspec.
    rewrite Hwn in Hspec. cbv beta iota in Hspec.
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a bs] [|w2 ws]]; [discriminate| |discriminate].
    destruct zs as [|z zs]; [|discriminate].
    destruct us as [|u us]; [|discriminate].
    destruct cs as [|c cs]; [|discriminate].
    destruct copyins as [|copyin copyins]; [|discriminate].
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp cnt)%Z
              && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
              && wmem_ok (sys_input segs ms x8) buf (len_word bs)) eqn:Hb;
      try rewrite Hb in Hspec; [|discriminate].
    inversion Hspec; subst.
    apply andb_true_iff in Hb as [Hb _].
    apply andb_true_iff in Hb as [Hb HE].
    apply andb_true_iff in Hb as [Hb HD].
    apply andb_true_iff in Hb as [Hb HC].
    apply andb_true_iff in Hb as [HA HB].
    apply bv_eqb_eq in HA; subst a.
    apply bv_eqb_eq in HB; subst ret.
    apply Z.leb_le in HC. apply Z.leb_le in HD.
    rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)) in HD.
    apply listN_eqb_eq in HE.
    right. exists bs. repeat split; try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read0_no_unmodeled : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply (check_read_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hw1 in Hspec. cbv beta iota in Hspec.
  rewrite Hwn in Hspec. cbv beta iota in Hspec. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_read_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall segs ms model buf x8 w evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  sstep segs (mkCfg ms model) evs st ->
  (m_stdin model = IEof /\ evs = [] /\
   st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\
        (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs /\
        st = SNext (mkCfg
               (advance_past_svc (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                           model))).
Proof.
  intros cnt Hcnt segs ms model buf x8 w evs st
         Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(Hs & Heff & Hm & Hevs) | (bs & Hlo & Hhi & Hpre & Heff & Hm & Hevs)];
        subst eff model' evs0
    end.
    + match goal with
      | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
          inversion Hmat; subst model''
      end.
      left. rewrite apply_effect_no_write.
      split; [exact Hs | split; reflexivity].
    + match goal with
      | Hmat : materialize_model_accesses
                   (with_stdin ?s model) _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy (with_stdin s model) _)
            in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy);
          inversion Hmat; subst model''
      end.
      right. exists bs. repeat split; try assumption; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
      subst model';
      [ rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy
                   (with_stdin (snd (stream_take (m_stdin model) (length bs))) model) _)
          in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy) ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model'; [|rewrite m_halted_with_stdin in H6]; congruence
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model';
        [ rewrite (m_killed_of_m_halted_none model Hh) in H6
        | rewrite (m_killed_of_m_halted_none _
                     (eq_trans (m_halted_with_stdin _ model) Hh)) in H6 ];
        discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (read0_no_unmodeled _ Hcnt segs ms x8 model w Hno Hfd Hg0 eq_refl Hw
               Haok H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

(* [comment removed for export] *)
Lemma chunks_app : forall cnt s l1 s1 l2 s2,
  chunks cnt s l1 s1 -> chunks cnt s1 l2 s2 -> chunks cnt s (l1 ++ l2) s2.
Proof.
  intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
  induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros l2 s2 H2; cbn [app]; [exact H2|].
  eapply chunks_cons; eauto.
Qed.

Lemma chunks_split : forall cnt l1 l2 s s2,
  chunks cnt s (l1 ++ l2) s2 ->
  exists s1, chunks cnt s l1 s1 /\ chunks cnt s1 l2 s2.
Proof.
  intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
  - exists s. split; [constructor | exact H].
  - inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
    destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
    exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.

(* [comment removed for export] *)
Lemma chunks_single_inv : forall cnt s bs s',
  chunks cnt s [bs] s' ->
  (1 <= Z.of_nat (length bs))%Z /\
  (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
  fst (stream_take s (length bs)) = bs /\
  s' = snd (stream_take s (length bs)).
Proof.
  intros cnt s bs s' H.
  inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
  inversion HC; subst.
  repeat split; assumption || reflexivity.
Qed.

(* [comment removed for export] *)
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
  map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

(* [comment removed for export] *)
Definition iter_ev (bs : list byte) : list event :=
  iter_ev_ch (Z_to_bv 64 0) bs.

(* [comment removed for export] *)
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr : list event) : Prop :=
  exists blocks s',
    chunks cnt s blocks s' /\
    is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).

(* [comment removed for export] *)
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Lemma stream_traces_ch_prefix_closed : forall rch cnt fs s tr tr',
  stream_traces_ch rch cnt fs s tr -> is_prefix tr' tr ->
  stream_traces_ch rch cnt fs s tr'.
Proof.
  intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
  exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.

Lemma stream_traces_prefix_closed : forall cnt fs s tr tr',
  stream_traces cnt fs s tr -> is_prefix tr' tr -> stream_traces cnt fs s tr'.
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
(* [comment removed for export] *)
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

(* [comment removed for export] *)
Definition lh_next (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH ms'.

(* [comment removed for export] *)
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs lh_next.

(* [comment removed for export] *)
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

(* [comment removed for export] *)
Definition ReadPend (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z ->
     (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     to_wr bs (advance_past_svc (apply_effect ms
        (mkEffect (len_word bs) [(buf, bs)] [])))).

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma msteps_to_wr : forall bs ms ms',
  msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms ms' H; induction H; [auto|].
  intro Hwr. eapply twr_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wr_wall_tail : forall bs ms,
  to_wr bs ms -> to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - destruct HWP as [Hnb Hw]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

#[using="Type"] Lemma msteps_to_rd : forall ms ms',
  msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

(* [comment removed for export] *)
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

#[using="H_LH"] Lemma lh_next_to_rd : forall ms, lh_next ms -> to_rd ms.
Proof. LiaFast.lf_pins (fun (H_LH : LiaFast.U) => LiaFast.u0).
  intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_rd_star : forall ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd ms ->
  exists msR, ReadPend msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model Hh Hlazy Hrd.
  induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma to_wr_star : forall bs ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_wr bs ms ->
  exists msW, WrPend bs msW /\
    star segs (mkCfg ms model) [] (mkCfg msW model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms model Hh Hlazy Hwr.
  induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - exists ms. split; [exact HWP | apply star_refl].
  - destruct IH as (msW & HWP & Hstar).
    exists msW. split; [exact HWP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma stream_star_admits : forall s blocks s',
  chunks cnt s blocks s' ->
  forall ms model,
  M_loop model -> m_stdin model = s -> to_rd ms ->
  exists c, star segs (mkCfg ms model)
              (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)) c.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros ms model HM Hst Hrd; pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - (* [comment removed for export] *)
    cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* [comment removed for export] *)
      destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & _).
      destruct (to_exit_star_admits segs (Z_to_bv 64 0)
                  (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex)
        as [c Hstar2].
      exists c.
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok. eapply (read0_ok_eof cnt Hcnt); eassumption.
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      cbn [eof_tail].
      replace [ExitEv (Z_to_bv 64 0) (m_fs model)]
        with (([] : list event)
                ++ ([] ++ [ExitEv (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255))
                             (m_fs model)]))
        by (rewrite band0_255; reflexivity).
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* [comment removed for export] *)
      cbn [eof_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* [comment removed for export] *)
    destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hwr.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { apply (sstep_syscall segs msR model x8
               (mkEffect (len_word bs) [(buf, bs)] []) model' model'
               (map (ReadEv (Z_to_bv 64 0)) bs));
        [exact Hh | exact Hsvc | | exact Hh' |].
      - unfold model'. rewrite <- Hst. rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
        eapply (read0_ok_bytes cnt Hcnt); try eassumption.
        rewrite Hst. exact Hpre.
      - rewrite (materialize_model_accesses_no_lazy model' _ (proj2 (proj2 (proj2 HM')))).
        reflexivity. }
    assert (Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model')
      by (apply fd1chan_fdchan; exact Hfd1).
    assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (Hcont : forall ms', lh_next ms' ->
              exists c, star segs (mkCfg ms' model')
                (flat_map iter_ev blocks ++ eof_tail s'' (m_fs model')) c).
    { intros ms' Hlh.
      apply (IH ms' model' HM' Hst' (lh_next_to_rd ms' Hlh)). }
    destruct (to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1)
                fd32_1 advB bs lh_next (to_wr_wall_tail bs advB Hwr) Hbmbs
                model' _ Hh' (proj2 (proj2 (proj2 HM'))) Hfdc' Hcont) as [c Hstar1].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar1.
    cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
    rewrite <- !app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ map (WriteEv (Z_to_bv 64 1)) bs
               ++ flat_map iter_ev blocks ++ eof_tail s'' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (map (WriteEv (Z_to_bv 64 1)) bs
                          ++ (flat_map iter_ev blocks
                                ++ eof_tail s'' (m_fs model)))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma star_loop_only : forall c0 tr c', star segs c0 tr c' ->
  forall ms model, c0 = mkCfg ms model -> M_loop model ->
  (to_rd ms ->
     exists blocks s', chunks cnt (m_stdin model) blocks s' /\
       is_prefix tr (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)))
  /\ (forall bs, (1 <= length bs)%nat -> buf_modeled bs ->
     to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next ->
     exists blocks s',
       chunks cnt (m_stdin model) blocks s' /\
       is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs
                       ++ flat_map iter_ev blocks
                       ++ eof_tail s' (m_fs model))).
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros ms model Heq HM; subst.
  - (* [comment removed for export] *)
    split.
    + intros _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
    + intros bs _ _ _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    split.
    + (* [comment removed for export] *)
      intro Hrd. destruct Hrd as [ms (buf & x8 & HRP) | ms ms' Hsvc Hstep Hrd'].
      * (* [comment removed for export] *)
        destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- (* [comment removed for export] *)
           destruct (to_exit_star_only segs (Z_to_bv 64 0)
                       (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
                       Hh Hlazy Hex tr2 c3 Hstar) as [-> | ->].
           ++ exists [], (m_stdin model).
              split; [constructor | apply is_prefix_nil].
           ++ exists [], (m_stdin model).
              split; [constructor|].
              rewrite Hs, band0_255. cbn [flat_map app eof_tail].
              apply is_prefix_refl.
        -- (* [comment removed for export] *)
           assert (Hnb : (1 <= length bs)%nat) by lia.
           assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
           destruct (proj2 (IH _ _ eq_refl (M_loop_take (length bs) model HM)) bs
                       Hnb Hbmbs (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)))
             as (blocks & s' & HCb & Hp).
           exists (bs :: blocks), s'.
           split; [eapply chunks_cons; eassumption|].
           cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
           rewrite <- !app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* [comment removed for export] *)
        destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                    Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj1 (IH _ model eq_refl HM) Hrd').
    + (* [comment removed for export] *)
      intros bs Hnb Hbm Hwt.
      inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* [comment removed for export] *)
        cbn in Hnb. lia.
      * (* [comment removed for export] *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & Hevs & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* [comment removed for export] *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           destruct (proj1 (IH _ model eq_refl HM)
                       (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)))
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite firstn_all.
           apply is_prefix_app_mono. exact Hp.
        -- (* [comment removed for export] *)
           assert (Hnb' : (1 <= length (skipn n bs))%nat)
             by (rewrite length_skipn; lia).
           destruct (proj2 (IH _ model eq_refl HM) (skipn n bs) Hnb'
                       (buf_modeled_skipn n bs Hbm) Hwt2)
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite <- (firstn_skipn n bs) at 2.
           rewrite map_app, <- app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* [comment removed for export] *)
        destruct (sstep_instr_inv segs ms model msS' evs (SNext c2)
                    Hlazy HsvcS HstepS Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj2 (IH _ model eq_refl HM) bs Hnb Hbm Hwt').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\
     (to_rd (cfg_ms c)
      \/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
           to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
  \/ on_path segs (Z_to_bv 64 0) c.

#[using="Hcnt H_LH"] Lemma sinv_step : forall c evs c',
  sinv c -> sstep segs c evs (SNext c') -> sinv c'.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs
                    (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hex].
        -- left. cbn. split; [apply M_loop_take; exact HM|].
           right. exists bs. split; [lia|].
           split; [unfold buf_modeled; lia|].
           exact (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)).
      * destruct (sstep_instr_inv segs ms model ms1 evs
                    (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM | left; exact Hrd'].
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* [comment removed for export] *)
        cbn in Hnb. lia.
      * (* [comment removed for export] *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & _ & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* [comment removed for export] *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           left. cbn. split; [exact HM|].
           left. exact (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)).
        -- (* [comment removed for export] *)
           left. cbn. split; [exact HM|].
           right. exists (skipn n bs).
           split; [rewrite length_skipn; lia|].
           split; [apply buf_modeled_skipn; exact Hbm | exact Hwt2].
      * destruct (sstep_instr_inv segs ms model msS' evs
                    (SNext (mkCfg ms' model')) Hlazy HsvcS HstepS Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM|].
        right. exists bs.
        split; [exact Hnb | split; [exact Hbm | exact Hwt']].
  - right. eapply on_path_step; eauto.
Qed.

#[using="Hcnt"] Lemma sinv_no_error : forall c evs, sinv c -> ~ sstep segs c evs SError.
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0).
  intros [ms model] evs Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
      * destruct (sstep_instr_inv segs ms model ms1 evs SError
                    Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * cbn in Hnb. lia.
      * exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                 ms bs lh_next model evs Hh Hlazy Hfdc Hbm Hwl Hss).
      * destruct (sstep_instr_inv segs ms model msS' evs SError
                    Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
Qed.

#[using="Hcnt H_LH"] Lemma star_sinv : forall c tr c', sinv c -> star segs c tr c' -> sinv c'.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0). exact (star_inv segs sinv sinv_step). Qed.

#[using="Hcnt H_LH"] Lemma to_rd_no_error : forall ms model,
  M_loop model -> to_rd ms -> ~ reaches_error segs (mkCfg ms model).
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros ms model HM Hrd.
  apply (inv_no_reaches_error segs sinv sinv_step sinv_no_error).
  left; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma stream_obs_iff : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> stream_traces cnt (in_fs inp) (in_stdin inp) tr.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp Hrd tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
  set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (proj1 (star_loop_only _ _ _ Hstar ms0 model0 eq_refl HM0) Hrd)
      as (blocks & s' & HC & Hp').
    rewrite Hst0 in HC. rewrite Hfs0 in Hp'.
    apply (stream_traces_prefix_closed cnt fs0 stdin0 tr'); [|exact Hp].
    exists blocks, s'. split; assumption.
  - intros (blocks & s' & HC & Hp).
    destruct (stream_star_admits stdin0 blocks s' HC ms0 model0 HM0 Hst0 Hrd)
      as [c Hstar].
    rewrite Hfs0 in Hstar.
    exists (flat_map iter_ev blocks ++ eof_tail s' fs0), c.
    split; assumption.
Qed.

#[using="Hcnt H_LH"] Lemma stream_no_error : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp Hrd.
  apply to_rd_no_error; [apply init_M_loop | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma to_rd_coexec : forall ms model,
  M_loop model -> to_rd ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros ms model HM Hrd.
  apply (inv_coexec segs sinv sinv_step sinv_no_error). left; cbn; auto.
Qed.

#[using="Hcnt H_LH"] Lemma stream_omni_corun : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_corun]. unfold init_config.
  apply to_rd_coexec; [apply init_M_loop | exact Hrd].
Qed.

#[using="Hcnt H_LH"] Lemma stream_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp,
  to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (stream_traces cnt (in_fs inp) (in_stdin inp)).
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_cosafe].
  apply cosafe_obs_iff.
  - intros t t' Ht Hp. eapply stream_traces_prefix_closed; eauto.
  - intros tr Hobs. apply (stream_obs_iff pc ph sp brk0 mb rnd lim inp Hrd). exact Hobs.
Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stream_omni_strong_equiv :
  forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
  (forall ms, rLH ms -> to_rd source_segs rLH cnt ms) ->
  (forall ms, aLH ms -> to_rd target_segs aLH cnt ms) ->
  to_rd source_segs rLH cnt (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_rd target_segs aLH cnt (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp HrLH HaLH Hr Ha.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp Hr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr tr).
    rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha tr).
    reflexivity.
  - exact (stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha).
Qed.

Lemma stream_strong_equiv :
  forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  forall source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
  (forall ms, rLH ms -> to_rd source_segs rLH cnt ms) ->
  (forall ms, aLH ms -> to_rd target_segs aLH cnt ms) ->
  to_rd source_segs rLH cnt (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_rd target_segs aLH cnt (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp HrLH HaLH Hr Ha.
  split.
  { apply no_error_run_modeled.
    apply (stream_no_error source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr). }
  right. split.
  - intro tr. cbn.
    rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr tr).
    rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha tr).
    reflexivity.
  - cbn. apply (stream_no_error target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha).
Qed.
End StreamSim.

Module AllocSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require SimInv.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require PropExec CatSim CatExec.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SimInv OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.WallSim.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma u_add_small : forall a b : word,
  (bv_unsigned a + bv_unsigned b < 2 ^ 64)%Z ->
  bv_unsigned (a + b) = (bv_unsigned a + bv_unsigned b)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a b H. rewrite bv_add_unsigned, bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). pose proof (u64_range b). lia.
Qed.

#[using="Type"] Lemma word_add_0_r : forall a : word, a + Z_to_bv 64 0 = a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intro a. apply bv_eq.
  rewrite bv_add_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r, bv_wrap64_mod. apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_sub_cancel : forall r t : word, r + t - r = t.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r t. apply bv_eq.
  rewrite bv_sub_unsigned, bv_add_unsigned, !bv_wrap64_mod.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned r + bv_unsigned t - bv_unsigned r)%Z
    with (bv_unsigned t) by lia.
  apply Z.mod_small. apply u64_range.
Qed.

#[using="Type"] Lemma word_neq0_unsigned : forall r : word,
  r <> Z_to_bv 64 0 -> (bv_unsigned r <> 0)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r Hne Hu. apply Hne. apply bv_eq. rewrite Hu. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat_S : forall (a : word) k,
  (a + 1) + nat_to_word k = a + nat_to_word (S k).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a k. apply bv_eq. unfold nat_to_word.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
  fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
              && Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
           then Some (Z_to_bv 8 0) else mem a.

#[using="Type"] Lemma apply_zeros_nil : forall mem, apply_zeros mem [] = mem.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma apply_zeros_one : forall mem b l,
  apply_zeros mem [(b, l)] = zmem mem b l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem b l. apply functional_extensionality. intro a.
  unfold apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
  rewrite orb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma zmem_out : forall mem b l a,
  (bv_unsigned a < bv_unsigned b \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  zmem mem b l a = mem a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem b l a Hd. unfold zmem.
  destruct Hd as [Hd | Hd].
  - assert (E : (bv_unsigned b <=? bv_unsigned a)%Z = false) by (apply Z.leb_gt; lia).
    rewrite E. reflexivity.
  - assert (E : (bv_unsigned a <? bv_unsigned b + bv_unsigned l)%Z = false)
      by (apply Z.ltb_ge; lia).
    rewrite E, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_zmem_out : forall segs mem b l (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned l <= bv_unsigned a)%Z ->
  rdn segs (zmem mem b l) a n = rdn segs mem a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs mem b l a n Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply zmem_out. lia.
Qed.

#[using="Type"] Lemma rdn_zmem_in1 : forall segs mem b l (a : word),
  (bv_unsigned b <= bv_unsigned a < bv_unsigned b + bv_unsigned l)%Z ->
  rdn segs (zmem mem b l) a 1 = Some [Z_to_bv 8 0].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs mem b l a [Hlo Hhi]. cbn [rdn]. unfold zmem.
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_app : forall {bs1 bs2 : list byte} m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word (length bs1)) bs2.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs1 as [|b bs1 IH]; intros bs2 m a.
  - cbn [app wbytes length].
    replace (a + nat_to_word 0) with a; [reflexivity|].
    symmetry. exact (word_add_0_r a).
  - cbn [app wbytes length].
    rewrite IH, word_add_nat_S. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma with_vmmaps_fds : forall h m, m_fds (with_vmmaps h m) = m_fds m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_fs : forall h m, m_fs (with_vmmaps h m) = m_fs m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_vm : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma with_vmmaps_lazy : forall h m,
  m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma fd1chan_with_vmmaps : forall h m, fd1chan m -> fd1chan (with_vmmaps h m).
Proof. LiaFast.lf_pins LiaFast.u0. intros h m H. unfold fd1chan in *. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fd1chan_forget_vm_ranges : forall ranges m,
  fd1chan m -> fd1chan (forget_vm_ranges ranges m).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ranges as [|[a n] ranges IH]; intros m H; cbn [forget_vm_ranges].
  - exact H.
  - apply IH. unfold fd1chan, vm_forget_range, with_vm_backing in *.
    cbn [m_fds m_fd] in *. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_brk : forall regs pc x8 mem rom r zs,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] zs))
  = mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc x8 mem rom r zs.
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma in_sysno_sys_input214 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma in_arg0_sys_input214 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma syscall_spec_brk : forall segs ms x8 model o,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input214, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Definition vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] None None None.

Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
  Mmap.brk_grow_ok (vm_model h) req r.

(* [comment removed for export] *)
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Mmap.brk_r_ok (vm_model h) req r = true.

(* [comment removed for export] *)
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
  Mmap.brk_r_ok m req r = true.

(* [comment removed for export] *)
Definition brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r.

(* [comment removed for export] *)
#[using="Type"] Lemma fd1chan_brk_model : forall req r m,
  fd1chan m -> fd1chan (brk_model req r m).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req r m H. unfold brk_model, with_brk_next. cbv zeta.
  apply fd1chan_forget_vm_ranges, fd1chan_with_vmmaps, H.
Qed.

#[using="Type"] Lemma check_brk_ok_inv : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  eff = mkEffectU (eff_ret eff) []
          (brk_zeros req (eff_ret eff) (vm_brk (m_vmmaps m)))
          (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps m))) [] []
  /\ evs = []
  /\ brk_resolution_ok m req (eff_ret eff)
  /\ m' = brk_model req (eff_ret eff) m.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req [r ws zs us cs copyins] m m' evs H.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (Mmap.brk_r_ok m req r) eqn:HR; [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZ;
    [|cbn [andb] in H; discriminate].
  destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HU;
    [|cbn [andb] in H; discriminate].
  cbn [andb] in H.
  apply listNN_eqb_eq in HZ. subst zs.
  apply listNN_eqb_eq in HU. subst us.
  inversion H; clear H; subst.
  cbn [eff_ret]. unfold brk_resolution_ok, brk_model.
  repeat split; try reflexivity. exact HR.
Qed.

#[using="Type"] Lemma check_brk_ok_intro : forall req r m,
  brk_resolution_ok m req r ->
  check_brk req (mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
                              (brk_unmaps r (vm_brk (m_vmmaps m))) [] []) m
  = CheckOk (brk_model req r m) [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req r m HR. unfold brk_resolution_ok in HR.
  unfold check_brk. rewrite HR.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  unfold brk_model. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_ok_iff : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 214%Z ->
  (syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) <->
   (eff = mkEffectU (eff_ret eff) []
            (brk_zeros (ms_gpr ms 0) (eff_ret eff) (vm_brk (m_vmmaps model)))
            (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model))) [] []
    /\ evs = []
    /\ brk_resolution_ok model (ms_gpr ms 0) (eff_ret eff)
    /\ model' = brk_model (ms_gpr ms 0) (eff_ret eff) model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model eff model' evs Hno. split.
  - intro H. apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
    apply check_brk_complete_ok in H.
    apply check_brk_ok_inv in H. exact H.
  - intros (Heff & -> & Hok & ->).
    apply (proj2 (syscall_spec_brk _ _ _ _ _ Hno)). apply check_brk_sound_ok.
    rewrite Heff at 1. cbn [eff_ret].
    apply check_brk_ok_intro. exact Hok.
Qed.

#[using="Type"] Lemma brk_ok_intro : forall segs ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  brk_resolution_ok model (ms_gpr ms 0) r ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
        (brk_model (ms_gpr ms 0) r model) []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model r Hno Hok.
  apply (brk_ok_iff segs ms x8 model _ _ _ Hno). cbn [eff_ret]. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 214%Z ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model Hno H.
  apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
  apply (check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in H.
  unfold check_brk in H.
  destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (Z_to_bv 64 0)
            && listNN_eqb []
                 (brk_zeros (ms_gpr ms 0) (Z_to_bv 64 0) (vm_brk (m_vmmaps model)))
            && listNN_eqb []
                 (brk_unmaps (Z_to_bv 64 0) (vm_brk (m_vmmaps model))));
    discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_receptive : forall segs ms x8 model,
  bv_unsigned x8 = 214%Z ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model Hno.
  pose (r := vm_brk (m_vmmaps model)).
  exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                        (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
         (brk_model (ms_gpr ms 0) r model).
  apply brk_ok_intro; [exact Hno|].
  unfold brk_resolution_ok, Mmap.brk_r_ok, r. cbv zeta.
  destruct (w_is0 (ms_gpr ms 0)
            || Z.ltb (bv_unsigned (ms_gpr ms 0))
                     (bv_unsigned (min_brk (m_vmmaps model)))).
  - apply bv_eqb_refl.
  - destruct (Z.ltb (bv_unsigned (ms_gpr ms 0))
                    (bv_unsigned (vm_brk (m_vmmaps model)))).
    + rewrite bv_eqb_refl, orb_true_r. reflexivity.
    + rewrite bv_eqb_refl, orb_true_r, andb_true_l.
      unfold brk_grow_ok, Mmap.brk_grow_ok.
      now rewrite Z.ltb_irrefl, andb_false_r.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_zeros_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_zeros req r old =
    brk_page_range (page_round_up_Z (bv_unsigned old))
                   (page_round_up_Z (bv_unsigned r)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grants_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_grants req r old = [(old, r - old)].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

#[using="Type"] Lemma brk_zeros_query : forall r old, brk_zeros (Z_to_bv 64 0) r old = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r old. unfold brk_zeros, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma brk_grants_query : forall r old, brk_grants (Z_to_bv 64 0) r old = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r old. unfold brk_grants, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

#[using="Type"] Lemma brk_zeros_keep : forall req old, brk_zeros req old old = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req old. unfold brk_zeros, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma brk_grants_keep : forall req old, brk_grants req old old = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req old. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros old. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
  unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_query : forall h r,
  r = vm_brk h -> brk_unmaps r (vm_brk h) = [].
Proof. LiaFast.lf_pins LiaFast.u0. intros h r ->. apply brk_unmaps_keep. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_unmaps_grow : forall r old,
  (bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r old H. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
  assert (E : (page_round_up_Z (bv_unsigned r)
               <? page_round_up_Z (bv_unsigned old))%Z = false)
    by (apply Z.ltb_ge, page_round_up_Z_mono, H).
  unfold brk_page_range. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grow_ok_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  brk_grow_ok h req r
  = ((if (page_round_up_Z (bv_unsigned (vm_brk h))
          <? page_round_up_Z (bv_unsigned r))%Z
      then (page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
           && region_free (vm_reserved h ++ vm_maps h)
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (vm_brk h))))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                             - page_round_up_Z (bv_unsigned (vm_brk h))))
      else true)
     && (vm_backed_bytes h + bv_unsigned (r - vm_brk h) <=? vm_limit h)%Z)%bool.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros h req r Hreq H0 Hlt.
  assert (Hmaps : m_vmmaps (vm_model h) = h) by reflexivity.
  assert (Hbacked : vm_backing_used (vm_model h) = vm_backed_bytes h).
  { unfold vm_backing_used, vm_model.
    cbv [mkModel m_vmmaps m_vm m_vm_lazy m_vm_materialized
         vmst_lazy vmst_materialized].
    change ((live_bytes (vm_backed_maps h) + 0)%Z =
            live_bytes (vm_backed_maps h)).
    apply Z.add_0_r. }
  unfold brk_grow_ok, Mmap.brk_grow_ok, Mmap.brk_budget_ok.
  rewrite Hmaps, Hbacked.
  assert (E2 : (0 <? bv_unsigned (vm_brk h))%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned (vm_brk h) <? bv_unsigned r)%Z = true)
    by (apply Z.ltb_lt; lia).
  rewrite E2, E3. reflexivity.
Qed.

#[using="Type"] Lemma brk_grow_ok_keep : forall h req,
  brk_grow_ok h req (vm_brk h) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros h req. unfold brk_grow_ok, Mmap.brk_grow_ok.
  cbv [vm_model mkModel m_vmmaps m_vm vm_backing_used m_vm_lazy
       m_vm_materialized vmst_lazy vmst_materialized].
  cbn [vmst_maps vm_backed_bytes maps_subtract_all].
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma page_round_up_Z_aligned : forall z,
  (0 <= z)%Z -> (z mod page_size = 0)%Z -> page_round_up_Z z = z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
  replace (z + 4096 - 1)%Z with
    (4095 + (z / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma page_round_up_Z_bounds : forall z,
  (0 <= z)%Z ->
  (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma round8_le_page_round : forall z,
  (0 <= z)%Z ->
  ((((z + 7) / 8) * 8) <= page_round_up_Z z)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz. unfold page_round_up_Z.
  pose proof (Z.div_mod (z + 7) 8 ltac:(lia)) as H8.
  pose proof (Z.mod_pos_bound (z + 7) 8 ltac:(lia)) as H8mod.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hp.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hpmod.
  assert (H8ceil :
    (z <= ((z + 7) / 8) * 8 <= z + 7)%Z) by lia.
  assert (Hpceil :
    (z <= ((z + 4096 - 1) / 4096) * 4096)%Z) by lia.
  set (q8 := ((z + 7) / 8)%Z) in *.
  set (qp := ((z + 4096 - 1) / 4096)%Z) in *.
  assert (Hq : (q8 <= 512 * qp)%Z) by lia.
  change (q8 * 8 <= qp * 4096)%Z.
  lia.
Qed.

#[using="Type"] Lemma round8_le_page_grant : forall old n,
  (0 <= old)%Z -> (0 <= n)%Z ->
  (old mod page_size = 0)%Z ->
  ((((n + 7) / 8) * 8) <= page_round_up_Z (old + n) - old)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros old n Hold Hn Hmod.
  unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod old 4096 ltac:(lia)) as Holddiv.
  replace (old + n + 4096 - 1)%Z with
    ((n + 4096 - 1) + (old / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  pose proof (round8_le_page_round n Hn).
  unfold page_round_up_Z in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_prefix : forall maps b small big,
  (bv_unsigned small <= bv_unsigned big)%Z ->
  region_free maps b big = true -> region_free maps b small = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree;
    [reflexivity|].
  cbn [region_free] in Hfree |- *.
  apply andb_true_iff in Hfree as [Hhead Htail].
  apply andb_true_iff. split; [|eapply IH; eassumption].
  apply negb_true_iff in Hhead. apply negb_true_iff.
  unfold iv_overlap in Hhead |- *.
  apply andb_false_iff in Hhead. apply andb_false_iff.
  destruct Hhead as [Hhead|Hhead]; [left|right];
    apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_grow_ok_aligned_grow : forall h req r,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
  (bv_unsigned (vm_brk h) mod page_size = 0)%Z ->
  brk_grow_ok h req r
  = (((page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
      && region_free (vm_reserved h ++ vm_maps h) (vm_brk h)
           (Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
                        - bv_unsigned (vm_brk h))))
     && (vm_backed_bytes h + bv_unsigned (r - vm_brk h) <=? vm_limit h)%Z)%bool.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros h req r Hreq Hpos Hlt Halign.
  rewrite brk_grow_ok_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk h))) by lia.
  assert (Hround : (bv_unsigned (vm_brk h)
                    < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  replace (Z_to_bv 64 (bv_unsigned (vm_brk h))) with (vm_brk h).
  - reflexivity.
  - symmetry. apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma brk_zeros_aligned_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  (bv_unsigned old mod page_size = 0)%Z ->
  brk_zeros req r old =
    [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros req r old Hreq Hpos Hlt Halign.
  rewrite brk_zeros_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
  unfold brk_page_range.
  assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_aligned_grant_ok :
  forall (res : list (word * word)) (r w g : word) (top ceil : Z),
  bv_unsigned (r + w) = (bv_unsigned r + bv_unsigned w)%Z ->
  bv_unsigned (r + w) = top ->
  g = Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r) ->
  (ceil + page_size < 2 ^ 64)%Z ->
  (page_round_up_Z (bv_unsigned (r + w)) <= ceil)%Z ->
  region_free res r
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                 - bv_unsigned r)) = true ->
     bv_unsigned g = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z
  /\ (bv_unsigned w <= bv_unsigned g)%Z
  /\ (bv_unsigned r + bv_unsigned g <= ceil)%Z
  /\ (top <= ceil)%Z
  /\ region_free res r w = true
  /\ region_free res r g = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros res r w g top ceil Hnowrap Htop Hg Hacp Hceil Hfree.
  pose proof (u64_range r). pose proof (u64_range w).
  pose proof (page_round_up_Z_bounds (bv_unsigned (r + w))
                (proj1 (u64_range (r + w)))).
  assert (Hps : (0 < page_size)%Z) by (vm_compute; reflexivity).
  (* [comment removed for export] *)
  assert (Hu : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
                 bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. apply Z.mod_small.
    split; [exact Hlo | exact Hhi]. }
  assert (HgU : bv_unsigned g
                = (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z)
    by (subst g; apply Hu; lia).
  repeat split; rewrite ?HgU; try lia.
  (* [comment removed for export] *)
  - apply (region_free_prefix res r w
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite Hu by lia; lia | exact Hfree].
  - apply (region_free_prefix res r g
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
                          - bv_unsigned r)));
      [rewrite HgU, Hu by lia; lia | exact Hfree].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
    : Prop :=
  r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
  (t = Z_to_bv 64 0 \/
   (((if (page_round_up_Z (bv_unsigned r)
          <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
      then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            <=? top)%Z
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z
                               (bv_unsigned r + bv_unsigned t)
                              + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (bv_unsigned t <=? lim)%Z)%bool = true)).

(* [comment removed for export] *)
Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
    (bufs : list (list byte))
    (r : word) : (list (list byte) * word) -> Prop :=
  fun o => (o = ([], Z_to_bv 64 4)
            /\ (r = Z_to_bv 64 0
                \/ (2 ^ 64 <= bv_unsigned r + bv_unsigned t)%Z
                \/ t <> Z_to_bv 64 0))
        \/ (growable reserved lim top t r /\ o = (bufs, Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
    : (list (list byte) * word) -> Prop :=
  fun o => (r2 = want /\ o = (bufs, Z_to_bv 64 0))
        \/ (r2 <> want /\ o = ([], Z_to_bv 64 4)).

(* [comment removed for export] *)
#[using="Type"] Lemma brk_r_ok_query_iff : forall h r,
  brk_r_ok h (Z_to_bv 64 0) r <-> r = vm_brk h.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros h r. unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  unfold w_is0. rewrite bv_eqb_refl. cbn [orb].
  apply bv_eqb_eq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reserved_top_above : forall reserved (r : Z),
  (reserved_top reserved <= r)%Z ->
  Forall (fun p : word * word =>
            (bv_unsigned (fst p) + bv_unsigned (snd p) <= r)%Z) reserved.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction reserved as [|[a sz] l IH]; intros r Hr; cbn [reserved_top] in *.
  - constructor.
  - constructor; [cbn [fst snd]; lia | apply IH; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_above_top : forall reserved (lo n : word),
  (reserved_top reserved <= bv_unsigned lo)%Z ->
  region_free reserved lo n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction reserved as [|[a sz] l IH]; intros lo n Hr;
    cbn [reserved_top] in *; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_above : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p)
                    <= bv_unsigned lo)%Z) l ->
  region_free l lo n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_below : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned lo + bv_unsigned n
                    <= bv_unsigned (fst p))%Z) l ->
  region_free l lo n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned a <? bv_unsigned lo + bv_unsigned n)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E, andb_false_r. cbn [negb andb]. apply IH. exact Hl.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma growable_aligned_grow : forall reserved lim top (t r : word),
  (bv_unsigned r mod page_size = 0)%Z ->
  (reserved_top reserved <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (bv_unsigned t <= lim)%Z ->
  ((if (page_round_up_Z (bv_unsigned r)
        <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
    then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
          <=? top)%Z
         && region_free reserved
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
              (Z_to_bv 64 (page_round_up_Z
                             (bv_unsigned r + bv_unsigned t)
                            + page_size - page_round_up_Z (bv_unsigned r)))
    else true)
   && (bv_unsigned t <=? lim)%Z)%bool = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
  pose proof (proj1 (u64_range r)) as Hr0.
  rewrite (page_round_up_Z_aligned (bv_unsigned r)); [|lia|exact Halign].
  assert (Hru := page_round_up_Z_bounds
    (bv_unsigned r + bv_unsigned t) ltac:(lia)).
  assert (Hltpage :
    (bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z)
    by lia.
  rewrite (proj2 (Z.ltb_lt _ _) Hltpage).
  apply andb_true_iff. split; [apply andb_true_iff; split|].
  - apply Z.leb_le. lia.
  - rewrite Z_to_bv_bv_unsigned. apply region_free_above_top. exact Htop.
  - apply Z.leb_le. exact Hlim.
Qed.

#[using="Type"] Lemma brk_aslr_max_val : brk_aslr_max = 1073741824%Z.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_model_next_query : forall h r,
  r = vm_brk h ->
  brk_model_next h (Z_to_bv 64 0) r
  = mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h)
      (vm_start_brk h) r (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros h r ->. unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r.
  rewrite brk_grants_query, brk_unmaps_keep. reflexivity.
Qed.

#[using="Type"] Lemma brk_model_query : forall r m,
  r = vm_brk (m_vmmaps m) ->
  brk_model (Z_to_bv 64 0) r m
  = with_vmmaps
      (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
        (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m)) r
        (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
        (vm_init_sp (m_vmmaps m))) m.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros r m ->. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  rewrite brk_model_next_query by reflexivity. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_r_ok_grow_iff : forall reserved lim s r maps noaccess mb sp req r2,
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned s <= bv_unsigned req)%Z ->
  (bv_unsigned r <= bv_unsigned req)%Z ->
  (brk_r_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 <->
   (r2 = req \/ r2 = r)
   /\ brk_grow_ok (mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 = true).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros reserved lim s r maps noaccess mb sp req r2 Hpos Hs Hreq.
  unfold brk_r_ok, Mmap.brk_r_ok.
  cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    apply Z.eqb_neq. lia. }
  rewrite E0.
  assert (Hmin : (bv_unsigned req <?
                   bv_unsigned (min_brk (mkVmMapsFull reserved maps noaccess s r lim mb sp)))%Z
                 = false).
  { apply Z.ltb_ge. unfold min_brk. cbn [vm_start_brk]. lia. }
  cbn [vmst_maps]. rewrite Hmin. cbn [orb vm_brk].
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned r)) ltac:(lia)).
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma T1_iff_T2 : forall reserved lim s (mb sp : word) t bufs r,
  r <> Z_to_bv 64 0 -> (bv_unsigned s <= bv_unsigned r)%Z ->
  (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z ->
  forall o, T1 reserved lim (bv_unsigned sp - stack_max_size) t bufs r o <->
    (exists r2, brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                /\ T2 (r + t) bufs r2 o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros reserved lim s mb sp t bufs r Hr0 Hs Hnw o.
  pose proof (u64_range r) as Hur. pose proof (u64_range t) as Hut.
  pose proof (word_neq0_unsigned r Hr0) as Hur0.
  assert (Huadd : bv_unsigned (r + t) = (bv_unsigned r + bv_unsigned t)%Z)
    by (apply u_add_small; exact Hnw).
  assert (Hwant0 : r + t <> Z_to_bv 64 0).
  { intro He. apply (f_equal bv_unsigned) in He.
    rewrite Huadd in He.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
  assert (Bridge : forall r2,
             brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 <->
             (r2 = r + t \/ r2 = r)
             /\ brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
                = true)
    by (intro r2; apply brk_r_ok_grow_iff with (maps := []) (noaccess := []); lia).
  split.
  - intros [[-> Hcase] | [Hg ->]].
    + (* [comment removed for export] *)
      assert (Ht0 : t <> Z_to_bv 64 0)
        by (destruct Hcase as [Hc | [Hc | Hc]]; [congruence | lia | exact Hc]).
      pose proof (word_neq0_unsigned t Ht0) as Hut0.
      exists r. split.
      * apply Bridge. split; [right; reflexivity|].
        exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)).
      * right. split; [| reflexivity].
        intro He. apply (f_equal bv_unsigned) in He.
        rewrite Huadd in He. lia.
    + (* [comment removed for export] *)
      destruct Hg as (_ & _ & Hb).
      exists (r + t). split.
      * apply Bridge. split; [left; reflexivity|].
        destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz].
        { assert (Ht0 : t = Z_to_bv 64 0)
            by (apply bv_eq; rewrite Hz; reflexivity).
          rewrite Ht0, word_add_0_r.
          exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) r). }
        destruct Hb as [Hb | Hb];
          [exfalso; apply Hz; rewrite Hb; reflexivity |].
        rewrite brk_grow_ok_grow;
          cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes];
          [| exact Hwant0 | lia | lia].
        rewrite app_nil_r, word_add_sub_cancel, Huadd, Z.add_0_l.
        exact Hb.
      * left. split; reflexivity.
  - intros (r2 & Hrok & Hb).
    apply Bridge in Hrok. destruct Hrok as (Hcase & Hgrow).
    destruct Hb as [[-> ->] | [Hne ->]].
    + (* [comment removed for export] *)
      right. split; [| reflexivity].
      split; [exact Hr0 | split; [exact Hnw |]].
      destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz];
        [left; apply bv_eq; rewrite Hz; reflexivity | right].
      rewrite brk_grow_ok_grow in Hgrow;
        cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes] in *;
        [| exact Hwant0 | lia | lia].
      rewrite app_nil_r, word_add_sub_cancel, Huadd, Z.add_0_l in Hgrow.
      exact Hgrow.
    + (* [comment removed for export] *)
      left. split; [reflexivity |].
      right. right.
      intro Ht0. subst t.
      rewrite word_add_0_r in Hne, Hcase.
      destruct Hcase as [Hc | Hc]; exact (Hne Hc).
Qed.

#[using="Type"] Lemma T2_fail_iff : forall want bufs r2,
  r2 <> want -> forall o, T2 want bufs r2 o <-> o = ([], Z_to_bv 64 4).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros want bufs r2 Hne o. unfold T2. tauto.
Qed.

#[using="Type"] Lemma T2_succ_iff : forall want bufs o,
  T2 want bufs want o <-> o = (bufs, Z_to_bv 64 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros want bufs o. unfold T2. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

(* [comment removed for export] *)
#[using="Type"] Lemma tou_msteps : forall ms ms' model U,
  msteps segs ms ms' -> to_outcomes ms' model U -> to_outcomes ms model U.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' model U H; induction H; [auto|].
  intro Ht. eapply tou_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma forget_vm_ranges_frame : forall ranges model,
  m_halted (forget_vm_ranges ranges model) = m_halted model /\
  m_fs (forget_vm_ranges ranges model) = m_fs model /\
  m_fds (forget_vm_ranges ranges model) = m_fds model /\
  (m_vm_lazy model = [] -> m_vm_lazy (forget_vm_ranges ranges model) = []).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction ranges as [|[a n] ranges IH]; intros model; cbn [forget_vm_ranges].
  - auto.
  - specialize (IH (vm_forget_range (bv_unsigned a)
      (bv_unsigned a + bv_unsigned n) model)).
    destruct IH as (Hhalt & Hfs & Hfds & Hlazy).
    unfold vm_forget_range, with_vm_backing in Hhalt, Hfs, Hfds, Hlazy.
    cbn [m_halted m_fs m_fds m_vm_lazy] in Hhalt, Hfs, Hfds, Hlazy.
    repeat split; try assumption.
    intro Hempty. apply Hlazy. rewrite Hempty. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_step_shape : forall ms x8 model eff model' evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  bv_unsigned x8 = 214%Z ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\ m_halted model' = None /\ m_fs model' = m_fs model
  /\ m_fds model' = m_fds model
  /\ m_vm_lazy model' = m_vm_lazy model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms x8 model eff model' evs Hh Hlazy Hno Hs.
  apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs.
  destruct Hs as (_ & -> & _ & ->).
  unfold brk_model, with_brk_next. cbv zeta.
  destruct (forget_vm_ranges_frame
    (brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model)))
    (with_vmmaps
      (brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff_ret eff)) model))
    as (Hhalt & Hfs & Hfds & Hlazy').
  repeat split.
  - rewrite Hhalt. unfold with_vmmaps. cbn [m_halted]. exact Hh.
  - rewrite Hfs. unfold with_vmmaps. reflexivity.
  - rewrite Hfds. unfold with_vmmaps. reflexivity.
  - rewrite Hlazy. apply Hlazy'.
    unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlazy.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_brk_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  sstep segs (mkCfg ms model) evs st ->
  exists eff model',
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
    evs = [] /\
    st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    assert (Hx : x0 = x8) by congruence; subst x0.
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno H3)
      as (He & _ & _ & _ & Hlazy').
    subst evs.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)) in H7.
    inversion H7; subst model''.
    exists eff, model'; auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
        as (He & _ & _ & _ & Hlazy'); subst evs0;
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hhalt : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      congruence
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hkill : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
      assert (Hhn : m_halted model' = None) by congruence;
      rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | Hsvc' : ms_svc_pending ms = Some ?x,
      Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
  wevents (fst o) ++ [ExitEv (snd o) fs].

(* [comment removed for export] *)
Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
  fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.

#[using="Type"] Lemma to_outcomes_exec : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  OmniRun.exec segs (mkCfg ms model) (outcomes_post (m_fs model) U).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - (* [comment removed for export] *)
    eapply exec_conseq;
      [exact (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
                Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) |].
    intros tr o (Heq & Hx). exists (bufs, code).
    split; [apply HU; reflexivity |].
    split; [unfold outcome_trace; cbn [fst snd]; rewrite <- wevents_ch_fd1; exact Heq |].
    cbn [snd]. exact Hx.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
  - (* [comment removed for export] *)
    apply exec_step; [exact Hh | | |].
    + destruct (brk_receptive segs ms x8 model Hno) as (eff & model' & Hspec).
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & _ & _ & Hlazy').
      eexists; eexists.
      apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)). reflexivity.
    + intros evs Hss.
      destruct (sstep_brk_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & _ & _ & Habs). discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_brk_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hss)
        as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
      destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy)) |].
      intros tr o (out & Hout & Heq & Hx). exists out.
      split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
      split; [| exact Hx].
      cbn [app]. unfold outcome_trace in Heq |- *. rewrite Hfs in Heq. exact Heq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_outcomes_no_other_exit : forall ms model U,
  to_outcomes ms model U -> m_halted model = None -> m_vm_lazy model = [] ->
  forall code', (forall o, U o -> snd o <> code') ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U Hto Hh Hlazy code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & Hout & _ & Hx)); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne out Hout Hx').
Qed.

#[using="Type"] Lemma to_outcomes_not_silent : forall ms model U,
  to_outcomes ms model U -> m_halted model = None -> m_vm_lazy model = [] ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U Hto Hh Hlazy Hc.
  destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
    as (tr & [c' | c'] & Hm & (out & _ & Heq & Hx)); [| destruct Hx].
  destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  subst tr. unfold outcome_trace in Hnil.
  destruct (wevents (fst out)); discriminate Hnil.
Qed.

#[using="Type"] Lemma to_outcomes_star_only : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists o, U o /\ is_prefix tr (outcome_trace (m_fs model) o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U Hto Hh Hlazy tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy) Hstar))
    as (tr' & o & _ & (out & Hout & Heq & _)).
  exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma to_outcomes_star_admits : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  forall o, U o ->
    exists c, star segs (mkCfg ms model) (outcome_trace (m_fs model) o) c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy o Ho.
  - (* [comment removed for export] *)
    apply HU in Ho. subst o.
    unfold outcome_trace; cbn [fst snd].
    rewrite <- wevents_ch_fd1.
    eapply (to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1);
      [exact Hh | exact Hlazy | exact (fd1chan_fdchan model Hfd)
      | exact Hbm | exact Hte].
  - (* [comment removed for export] *)
    destruct (IH Hh Hlazy o Ho) as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model) o) by reflexivity.
    eapply star_step; [|exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - (* [comment removed for export] *)
    apply HU in Ho.
    destruct Ho as (eff & model' & evs & Hspec & Ht).
    destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno Hspec)
      as (Hevs & Hh' & Hfs & _ & Hlazy'). subst evs.
    destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) o Ht)
      as [c Hstar].
    exists c.
    replace (outcome_trace (m_fs model) o)
      with ([] ++ outcome_trace (m_fs model') o)
      by (unfold outcome_trace; rewrite Hfs; reflexivity).
    eapply star_step; [|exact Hstar].
    apply (sstep_syscall segs ms model x8 eff model' model' []);
      try assumption.
    rewrite (materialize_model_accesses_no_lazy _ _
      (eq_trans Hlazy' Hlazy)).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_outcomes_no_error : forall ms model U,
  to_outcomes ms model U ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ~ reaches_error segs (mkCfg ms model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U Hto Hh Hlazy. apply exec_no_error.
  eapply exec_conseq; [exact (to_outcomes_exec ms model U Hto Hh Hlazy) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma tou_brk_r : forall ms model x8 (T' : word -> (list (list byte) * word) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 214%Z ->
  (forall r,
     brk_resolution_ok model (ms_gpr ms 0) r ->
     to_outcomes
       (advance_past_svc (apply_effect ms
          (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                          (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])))
       (brk_model (ms_gpr ms 0) r model)
       (T' r)) ->
  (forall o, U o <->
     (exists r, brk_resolution_ok model (ms_gpr ms 0) r /\ T' r o)) ->
  to_outcomes ms model U.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 T' U Hsvc Hno Hcont HU.
  apply (tou_brk ms model x8 (fun eff _ => T' (eff_ret eff)) U);
    [exact Hsvc | exact Hno | |].
  - intros eff model' evs Hspec.
    apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    pose proof (Hcont (eff_ret eff) Hok) as H.
    rewrite <- Heff in H. exact H.
  - intro o. rewrite HU. split.
    + intros (r & Hok & Ht).
      exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                            (brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
             (brk_model (ms_gpr ms 0) r model), [].
      split; [apply brk_ok_intro; [exact Hno | exact Hok] | exact Ht].
    + intros (eff & model' & evs & Hspec & Ht).
      apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
      destruct Hspec as (_ & _ & Hok & _).
      exists (eff_ret eff). auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tou_wexit_eq : forall ms model bufs code,
  fd1chan model ->
  to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
  bufs_modeled bufs ->
  to_outcomes ms model (fun o => o = (bufs, code)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bufs code Hfd Hte Hbm.
  apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm | tauto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tou_equiv : forall ms model U V,
  to_outcomes ms model U ->
  (forall o, V o <-> U o) ->
  to_outcomes ms model V.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model U V Hto; revert V.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros V HV.
  - apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm |].
    intro o. rewrite (HV o). apply HU.
  - eapply tou_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
  - apply (tou_brk ms model x8 T V); [exact Hsvc | exact Hno | |].
    + intros eff model' evs Hspec. exact (Hcont eff model' evs Hspec).
    + intro o. rewrite (HV o). apply HU.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_omni_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
              (init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (outcomes_post (in_fs inp) U).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto.
  cbn [omni_run]. unfold init_config.
  exact (to_outcomes_exec segs _ _ U Hto eq_refl eq_refl).
Qed.

#[using="Type"] Lemma alloc_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
              (init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
    <-> exists o, U o /\ is_prefix tr (outcome_trace (in_fs inp) o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
  unfold init_config.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
    by reflexivity.
  assert (Hlazy : m_vm_lazy
      (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
  assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp)
    by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_outcomes_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
      as (o & Ho & Hp').
    exists o. split; [exact Ho|].
    rewrite Hfs in Hp'. eapply is_prefix_trans; eauto.
  - intros (o & Ho & Hp).
    destruct (to_outcomes_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
    rewrite Hfs in Hstar.
    exists (outcome_trace (in_fs inp) o), c. split; assumption.
Qed.

#[using="Type"] Lemma alloc_no_error_run : forall segs pc ph sp brk0 mb rnd lim inp U,
  to_outcomes segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
              (init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
  eapply exec_conseq; [exact (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
  intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
  to_outcomes source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U ->
  to_outcomes target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
    intros tr o (out & _ & _ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         U inp,
  to_outcomes source_segs
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U ->
  to_outcomes target_segs
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved target_segs) abrk amb asp alim inp) U ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    U inp Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
    rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
    reflexivity.
  - cbn. apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
End WithFP1.
End AllocSim.

Module MmapSim.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require SimInv.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require PropExec CatSim CatExec SeqExec.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SimInv OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SeqExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma v_srli_div : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
  bv_unsigned (v_srli x sh) = (bv_unsigned x / 2 ^ sh)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x sh Hsh. unfold v_srli.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (u64_range x) as Hx.
  assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
    by (apply Z.div_le_upper_bound; nia).
  assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            [Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  rewrite <- N_to_le_bytes_1_small.
  apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                          (a v : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
  rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
                           (a : word) (b : byte),
  wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|x bs IH]; intros m a b.
  - cbn [app wbytes length]. rewrite word_add_0. reflexivity.
  - cbn [app wbytes length].
    rewrite IH. f_equal.
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

#[using="Type"] Lemma zfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  zfill a n m x = m x.
Proof. LiaFast.lf_pins LiaFast.u0. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_zfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (zfill a n m) x k = rdn segs m x k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps m))
               (map_remove (vm_maps (m_vmmaps m)) addr)
               (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr)
                  (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

Definition mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
               ((a, n) :: vm_maps (m_vmmaps m))
               (vm_noaccess (m_vmmaps m))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

#[using="Type"] Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. LiaFast.lf_pins LiaFast.u0. intros addr n m H. exact H. Qed.
#[using="Type"] Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
#[using="Type"] Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
#[using="Type"] Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. LiaFast.lf_pins LiaFast.u0. intros a n m H. exact H. Qed.
#[using="Type"] Lemma mmap_model_lazy : forall a n m,
  m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_ok_unpack : forall hint m a n,
  grant_ok hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H.
  destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H5.
  auto 7.
Qed.

#[using="Type"] Lemma region_free_cons : forall (b s : word) r (lo n : word),
  region_free ((b, s) :: r) lo n = true ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
  /\ region_free r lo n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b s r lo n H. cbn [region_free] in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [|exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  apply andb_false_iff in H1.
  destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_args_ok_gates : forall ms,
  mmap_args_ok ms ->
  mmap_off_aligned_b (ms_gpr ms 5) = true /\
  mmap_anon_b (ms_gpr ms 3) = true /\
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms (H1 & H2 & H3 & H4 & H5).
  split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
  split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
  ms_gpr ms 1 <> Z_to_bv 64 0 /\
  (bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (page_round_up (ms_gpr ms 1)) = true.

(* [comment removed for export] *)
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

(* [comment removed for export] *)
#[using="Type"] Lemma syscall_spec_munmap : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if w_is0 r
           && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model eff (Hal & Hlen & Hnw & Hhas).
  unfold check_munmap.
  rewrite (proj2 (Z.eqb_eq _ _) Hal).
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  cbn [negb orb]. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.

#[using="Type"] Lemma munmap_ok : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model Hno Ha.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  unfold munmap_eff, w_is0. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

#[using="Type"] Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = munmap_eff ms /\
  model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model
  /\ evs = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply check_munmap_complete_ok in Hspec.
  rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?]|]; try discriminate.
  destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
  destruct (w_is0 r
            && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
    eqn:HC; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in HC as [Hr Hus].
  unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
  apply listNN_eqb_eq in Hus; subst us.
  unfold munmap_eff. auto.
Qed.

#[using="Type"] Lemma munmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model Hno Ha Hspec.
  apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
  destruct (w_is0 (Z_to_bv 64 0)
            && listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma syscall_spec_mmap : forall segs ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
         (ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

#[using="Type"] Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. LiaFast.lf_pins LiaFast.u0. left. reflexivity. Qed.

#[using="Type"] Lemma mmap_errno_range : forall e,
  In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.

#[using="Type"] Lemma mmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 222%Z -> mmap_args_ok ms -> In e mmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model e Hno Ha HIn.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok hint model a n = true ->
  errno_ret_in mmap_errnos a = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hint model a n Hn Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

#[using="Type"] Lemma mmap_succ_ok : forall segs ms x8 model a,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model a Hno Ha Hg.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
  unfold check_mmap. cbv beta.
  rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
  rewrite (grant_not_errno (ms_gpr ms 0) model a
             (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
    [ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
      | exact Hg ].
  unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
  destruct Hg as [[[[H1 H2] H3] H4] H5].
  rewrite Hflags.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
  rewrite H1, H2, H3, H4, H5.
  unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
  reflexivity.
Qed.

#[using="Type"] Lemma mmap_ok_inv : forall segs ms x8 model eff model' evs,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
      /\ model' = model) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
      /\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
      /\ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model eff model' evs Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  destruct Ha as (_ & _ & Hflags & _ & _).
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply check_mmap_complete_ok in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  rewrite Hflags in Hspec.
  assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
    by (vm_compute; reflexivity).
  unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
  rewrite Hnr in Hspec.
  destruct eff as [r ws zs us cs copyins].
  cbv beta iota zeta in Hspec.
  destruct ws as [|w ws]; [|discriminate].
  destruct us as [|u us]; [|discriminate].
  destruct cs as [|c cs]; [|discriminate].
  destruct copyins as [|copyin copyins]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
    cbv beta iota in Hspec.
  - destruct zs as [|z zs]; [|discriminate].
    inversion Hspec; subst.
    split; [reflexivity|]. left.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    exists e. auto.
  - destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
              && (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
              && region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
                   (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
              && (vm_backing_used model
                  + page_round_up_Z (bv_unsigned (ms_gpr ms 1))
                  <=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
      rewrite ?Hcond in Hspec.
    2:{ rewrite andb_false_l in Hspec. discriminate. }
    destruct (listNN_eqb zs
                [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
      rewrite ?Hzs in Hspec.
    2:{ rewrite andb_false_r in Hspec. discriminate. }
    cbn [andb] in Hspec.
    apply listNN_eqb_eq in Hzs. subst zs.
    inversion Hspec; subst.
    split; [reflexivity|]. right.
    exists r. split; [|split].
    + unfold grant_ok. exact Hcond.
    + unfold page_round_up. reflexivity.
    + reflexivity.
Qed.

#[using="Type"] Lemma mmap_no_unmodeled : forall segs ms x8 model,
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs ms x8 model Hno Ha Hspec.
  destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
  apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
  apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_mmap in Hspec. cbv beta in Hspec.
  rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
  cbv beta iota zeta in Hspec.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  rewrite E in Hspec. cbv beta iota in Hspec.
  match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffect a [] [(a, n)]))
  = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
  fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
              && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
           then None else m x.

#[using="Type"] Lemma unfill_out : forall a n m (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  unfill a n m x = m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a n m x Hx. unfold unfill.
  destruct Hx as [Hx | Hx].
  - rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
    rewrite andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma rdn_unfill_out : forall segs a n m (x : word) k,
  (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  (bv_unsigned x + Z.of_nat k <= bv_unsigned a
   \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  rdn segs (unfill a n m) x k = rdn segs m x k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros y Hy. apply unfill_out. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma adv_munmap : forall regs pc sv mem rom a n,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc sv mem rom a n.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
               = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd.
  rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
    (1 <= length buf)%nat ->
    twm_pend ms model buf bufs code ->
    twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(* [comment removed for export] *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
         (skipn n rest) bufs code) ->
    twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
    twm ms model bufs code ->
    twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
    (1 <= length rest)%nat ->
    twm_pend ms model rest bufs code ->
    twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm_tail ms' model rest bufs code ->
    twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
  with twm_pend_min := Minimality for twm_pend Sort Prop
  with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

#[using="Type"] Lemma msteps_twm : forall ms ms' model bufs code,
  msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' model bufs code H; induction H; [auto|].
  intro Hw. eapply twm_step; eauto.
Qed.

#[using="Type"] Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
  msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
  twm_tail ms model rest bufs code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' model rest bufs code H; induction H; [auto|].
  intro Hw. eapply twmt_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma twm_write_ret : forall regs pc mem rom model buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
       model (skipn n buf) bufs code) ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model (buf :: bufs) code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twm_write; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
       model (skipn n rest) bufs code) ->
  twm_tail {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
              ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
              ms_mem := mem; ms_rom := rom |}
    model rest bufs code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply twmt_more; [exact Hnb|].
  eapply twmp_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
  bv_unsigned (getr regs 17) = 215%Z ->
  reg_get regs 10 = a ->
  reg_get regs 11 = nlen ->
  (bv_unsigned a mod page_size = 0)%Z ->
  nlen <> Z_to_bv 64 0 ->
  (bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
  twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
            (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bufs code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  eapply twm_munmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn. auto.
  - unfold munmap_eff, ms_gpr. cbn [ms_regs].
    rewrite E10, E11, Ha, Hn.
    rewrite adv_munmap. exact Hcont.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model [] c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model c H17 H10 Hc.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply twm_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_munmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
      subst eff model' evs0
    end.
    match goal with
    | Hmat : materialize_model_accesses
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
      rewrite (materialize_model_accesses_no_lazy _ _
        (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
      inversion Hmat; subst
    end.
    split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (Heff & Hm & Hevs); subst eff model' evs0;
      rewrite (materialize_model_accesses_no_lazy _ _
        (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hm & _);
      subst model';
      assert (Hhn : m_halted
                      (munmap_model (ms_gpr ms 0)
                         (page_round_up (ms_gpr ms 1)) model) = None)
        by (rewrite munmap_model_halted; exact Hh);
      rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.

Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
    (fs : Fs.Fs) : post :=
  fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
              /\ exits_with code tr o.

#[using="Type"] Lemma twm_exec_mut :
  (forall ms model bufs code, twm ms model bufs code ->
     bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
  /\ (forall ms model rest bufs code, twm_pend ms model rest bufs code ->
     buf_modeled rest -> bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
  /\ (forall ms model rest bufs code, twm_tail ms model rest bufs code ->
     buf_modeled rest -> bufs_modeled bufs ->
     m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
     OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))).
Proof. LiaFast.lf_pins LiaFast.u0.
  apply (twm_mutind
    (fun ms model bufs code =>
       bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
    (fun ms model rest bufs code =>
       buf_modeled rest -> bufs_modeled bufs ->
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
  - (* [comment removed for export] *)
    intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
  - (* [comment removed for export] *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hbm Hh Hlazy Hfd.
    assert (Hh' : m_halted
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
      by (rewrite munmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan
                     (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
      by (apply munmap_model_fd1chan; exact Hfd).
    apply (exec_step_only segs _ _ []
             (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
    + apply (sstep_syscall segs ms model x8 (munmap_eff ms)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
               (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
      * exact Hh.
      * exact Hsvc.
      * apply munmap_ok; [exact Hno | exact Hargs].
      * exact Hh'.
      * apply materialize_model_accesses_no_lazy.
        exact (munmap_model_no_lazy _ _ _ Hlazy).
    + intros evs st Hss.
      exact (sstep_munmap_inv ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss).
    + eapply exec_conseq;
        [exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
      intros tr o (Heq & Hx). split; [| exact Hx].
      cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
  - (* [comment removed for export] *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
  - (* [comment removed for export] *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
      intros tr o (Heq & Hx). split; [| exact Hx].
      rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
      rewrite map_app, <- !app_assoc. reflexivity.
  - (* [comment removed for export] *)
    intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
    eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
    intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
  - (* [comment removed for export] *)
    intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
    exact (IH Hbr Hbm Hh Hlazy Hfd).
  - (* [comment removed for export] *)
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma twm_exec : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.

#[using="Type"] Lemma twm_star_admits : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

#[using="Type"] Lemma twm_star_only : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & Heq & _).
  rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tmw : machine_state -> Model -> list (list byte) -> word
                -> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (forall e, In e mmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
           (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    tmw ms' model bf cf bs cs ->
    tmw ms model bf cf bs cs.

#[using="Type"] Lemma msteps_tmw : forall ms ms' model bf cf bs cs,
  msteps segs ms ms' -> tmw ms' model bf cf bs cs -> tmw ms model bf cf bs cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' model bf cf bs cs H; induction H; [auto|].
  intro Hw. eapply tmw_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmw_mmap_rec : forall regs pc mem rom model bf cf bs cs,
  bv_unsigned (getr regs 17) = 222%Z ->
  reg_get regs 11 <> Z_to_bv 64 0 ->
  reg_get regs 12 = Z_to_bv 64 3 ->
  reg_get regs 13 = Z_to_bv 64 34 ->
  reg_get regs 14 = Z_to_bv 64 (-1) ->
  reg_get regs 15 = Z_to_bv 64 0 ->
  (forall e, In e mmap_errnos ->
     twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) ->
  (forall a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true ->
     twm (mkst (regupd regs 10 a) (v_addi pc 4)
               (zfill a (page_round_up (reg_get regs 11)) mem) rom)
         (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) ->
  (exists a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) ->
  tmw {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
         ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
         ms_mem := mem; ms_rom := rom |}
      model bf cf bs cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
    Hfail Hsucc Hex.
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
  assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
  assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
  eapply tmw_mmap.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
    rewrite E11, E12, E13, E14, E15.
    auto.
  - intros e HIn. rewrite adv_set. apply Hfail; assumption.
  - intros a Hg. rewrite adv_mmap_grant.
    unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
    apply Hsucc. exact Hg.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma sstep_mmap_inv : forall ms model x8 evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\
  ((exists e, In e mmap_errnos /\
      st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
   (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
      st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
      subst evs0
    end.
    split; [reflexivity|].
    destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
    + left. exists e.
      match goal with
      | Hmat : materialize_model_accesses model _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
        inversion Hmat; subst
      end.
      split; [assumption |].
      rewrite apply_effect_no_write. reflexivity.
    + match goal with
      | Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
        inversion Hmat; subst
      end.
      right. exists a. auto.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
        as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy _ _
          (eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
      [ rewrite Hh in H6; discriminate
      | rewrite mmap_model_halted, Hh in H6; discriminate ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
      destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
      [ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
      | assert (Hhn : m_halted
                        (mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
          by (rewrite mmap_model_halted; exact Hh);
        rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tmw_post (bf : list (list byte)) (cf : word) (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) : post :=
  fun tr o => (tr = wevents bf ++ [ExitEv cf fs] /\ exits_with cf tr o)
              \/ (tr = wevents bs ++ [ExitEv cs fs] /\ exits_with cs tr o).

#[using="Type"] Lemma tmw_exec : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  OmniRun.exec segs (mkCfg ms model) (tmw_post bf cf bs cs (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH];
    intros Hbf Hbs Hh Hlazy Hfd.
  - (* [comment removed for export] *)
    apply exec_step; [exact Hh | | |].
    + eexists; eexists.
      apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model []).
      * exact Hh.
      * exact Hsvc.
      * apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos].
      * exact Hh.
      * apply materialize_model_accesses_no_lazy. exact Hlazy.
    + intros evs Hss.
      destruct (sstep_mmap_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hss)
        as (_ & [(e & _ & Habs) | (a & _ & Habs)]); discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_mmap_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hss)
        as (-> & [(e & He & Hc') | (a & Hg & Hc')]); injection Hc' as ->.
      * (* [comment removed for export] *)
        eapply exec_conseq; [exact (twm_exec _ _ _ _ (Hfail e He) Hbf Hh Hlazy Hfd) |].
        intros tr o (Heq & Hx). left. split; [cbn [app]; exact Heq | exact Hx].
      * (* [comment removed for export] *)
        set (n := page_round_up (ms_gpr ms 1)) in *.
        assert (Hh' : m_halted (mmap_model a n model) = None)
          by (rewrite mmap_model_halted; exact Hh).
        assert (Hfd' : fd1chan (mmap_model a n model))
          by (apply mmap_model_fd1chan; exact Hfd).
        eapply exec_conseq;
          [exact (twm_exec _ _ _ _ (Hsucc a Hg) Hbs Hh'
                    (eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') |].
        intros tr o (Heq & Hx). right. split; [| exact Hx].
        cbn [app]. rewrite Heq, mmap_model_fs. reflexivity.
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbf Hbs Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma tmw_star_admits_fail : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bf ++ [ExitEv cf (m_fs model)]) c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
  - destruct (twm_star_admits _ _ _ _ (Hfail ENOMEM ENOMEM_in_mmap_errnos)
                Hbm Hh Hlazy Hfd) as [c Hstar].
    rewrite <- apply_effect_no_write in Hstar.
    exists c.
    replace (wevents bf ++ [ExitEv cf (m_fs model)])
      with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] [])
             model model []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos].
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
    exists c.
    replace (wevents bf ++ [ExitEv cf (m_fs model)])
      with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma tmw_star_admits_succ : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  exists c, star segs (mkCfg ms model) (wevents bs ++ [ExitEv cs (m_fs model)]) c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
  - destruct Hex as [a Hg].
    set (n := page_round_up (ms_gpr ms 1)) in *.
    assert (Hh' : m_halted (mmap_model a n model) = None)
      by (rewrite mmap_model_halted; exact Hh).
    assert (Hfd' : fd1chan (mmap_model a n model))
      by (apply mmap_model_fd1chan; exact Hfd).
    destruct (twm_star_admits _ _ _ _ (Hsucc a Hg) Hbm Hh'
                (eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') as [c Hstar].
    rewrite mmap_model_fs in Hstar.
    exists c.
    replace (wevents bs ++ [ExitEv cs (m_fs model)])
      with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
             (mmap_model a n model) (mmap_model a n model) []).
    + exact Hh.
    + exact Hsvc.
    + apply mmap_succ_ok; [exact Hno | exact Hargs | exact Hg].
    + exact Hh'.
    + apply materialize_model_accesses_no_lazy.
      exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
  - destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
    exists c.
    replace (wevents bs ++ [ExitEv cs (m_fs model)])
      with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
Definition two_traces (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) (tr : list event) : Prop :=
  is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
  is_prefix tr (wevents bs ++ [ExitEv cs fs]).

#[using="Type"] Lemma tmw_star_only : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    two_traces bf cf bs cs (m_fs model) tr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar))
    as (tr' & o & _ & [(Heq & _) | (Heq & _)]); [left | right];
    rewrite <- Heq; apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma tmw_no_error : forall ms model bf cf bs cs,
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  ~ reaches_error segs (mkCfg ms model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hh Hlazy Hfd Hte Hbf Hbs. apply exec_no_error.
  eapply exec_conseq; [exact (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) |].
  intros tr o [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twm_exec_not_errors : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ OmniRun.exec segs (mkCfg ms model) OmniRun.errors.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm)
    as (_ & Hx).
  exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

#[using="Type"] Lemma twm_exec_code_unique : forall ms model bufs code,
  twm ms model bufs code ->
  bufs_modeled bufs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  forall code', OmniRun.exec segs (mkCfg ms model) (exits_with code') -> code' = code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex.
  destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as ->. reflexivity.
Qed.

#[using="Type"] Lemma tmw_exec_not_errors : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ OmniRun.exec segs (mkCfg ms model) OmniRun.errors.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  destruct (exec_sound _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) _ _ Hm)
    as [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmw_exec_not_fail_only : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bs ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ is_prefix (wevents bs ++ [ExitEv cs (m_fs model)]) (wevents bf ++ [ExitEv cf (m_fs model)]) ->
  ~ OmniRun.exec segs (mkCfg ms model) (twm_post bf cf (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd Hnp Hex.
  destruct (tmw_star_admits_succ ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd) as (c & Hstar).
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
  apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma tmw_exec_not_succ_only : forall ms model bf cf bs cs,
  tmw ms model bf cf bs cs ->
  bufs_modeled bf ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
  ~ is_prefix (wevents bf ++ [ExitEv cf (m_fs model)]) (wevents bs ++ [ExitEv cs (m_fs model)]) ->
  ~ OmniRun.exec segs (mkCfg ms model) (twm_post bs cs (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd Hnp Hex.
  destruct (tmw_star_admits_fail ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd) as (c & Hstar).
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
  apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma two_traces_prefix_closed : forall bf cf bs cs fs tr tr',
  two_traces bf cf bs cs fs tr -> is_prefix tr' tr -> two_traces bf cf bs cs fs tr'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bf cf bs cs fs tr tr' [H | H] Hp;
    [left | right]; eapply is_prefix_trans; eauto.
Qed.

#[using="Type"] Lemma mmap_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
  tmw segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> two_traces bf cf bs cs (in_fs inp) tr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs tr.
  unfold init_config in *.
  set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None) by reflexivity.
  assert (Hlazy : m_vm_lazy
      (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
  assert (Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp)) by reflexivity.
  assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (tmw_star_only segs ms _ bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd
                  tr' c Hstar) as H2.
    rewrite Hfs in H2.
    eapply two_traces_prefix_closed; eauto.
  - intros [Hp | Hp].
    + destruct (tmw_star_admits_fail segs ms _ bf cf bs cs Hte Hbf Hh Hlazy Hfd)
        as [c Hstar].
      rewrite Hfs in Hstar.
      exists (wevents bf ++ [ExitEv cf (in_fs inp)]), c. split; assumption.
    + destruct (tmw_star_admits_succ segs ms _ bf cf bs cs Hte Hbs Hh Hlazy Hfd)
        as [c Hstar].
      rewrite Hfs in Hstar.
      exists (wevents bs ++ [ExitEv cs (in_fs inp)]), c. split; assumption.
Qed.

#[using="Type"] Lemma mmap_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
  tmw segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs.
  unfold init_config.
  apply (tmw_no_error segs _ (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs);
    [reflexivity | reflexivity | reflexivity | exact Hte | exact Hbf | exact Hbs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma mmap_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
  tmw segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (tmw_post bf cf bs cs (in_fs inp)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs.
  cbn [omni_run]. unfold init_config.
  exact (tmw_exec segs _ _ bf cf bs cs Hte Hbf Hbs eq_refl eq_refl eq_refl).
Qed.

#[using="Type"] Lemma mmap_omni_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
  tmw source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) bf cf bs cs ->
  tmw target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp
    Hsource Htarget Hbf Hbs.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
                Hsource Hbf Hbs) |].
    intros tr o [(_ & Hx) | (_ & Hx)];
      exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
               Hsource Hbf Hbs tr).
    rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs
               Htarget Hbf Hbs tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs
             Htarget Hbf Hbs).
Qed.

#[using="Type"] Lemma mmap_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
  tmw source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) bf cf bs cs ->
  tmw target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs ->
  bufs_modeled bf -> bufs_modeled bs ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp
    Hsource Htarget Hbf Hbs.
  split.
  { apply no_error_run_modeled.
    apply (mmap_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
             Hsource Hbf Hbs). }
  right. split.
  - intro tr. cbn.
    rewrite (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
               Hsource Hbf Hbs tr).
    rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
               Htarget Hbf Hbs tr).
    reflexivity.
  - cbn. apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
                  Htarget Hbf Hbs).
Qed.
End WithFP1.
End MmapSim.


Module DrainSim.
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require SimInv.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require PropExec CatSim CatExec SeqExec.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SimInv OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SeqExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.WallSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

#[using="Type"] Lemma procs_app : forall bs1 bs2 a,
  procs a (bs1 ++ bs2) =
  match procs a bs1 with Some a' => procs a' bs2 | None => None end.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs1 as [|b bs1 IH]; intros bs2 a; [reflexivity|].
  cbn [procs app]. destruct (f a b); [apply IH | reflexivity].
Qed.
End Proc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_ok (cnt : word) (bs : list byte) : Prop :=
  (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z.

(* [comment removed for export] *)
Definition reads_ch (rch : word) (blocks : list (list byte)) : list event :=
  flat_map (fun bs => map (ReadEv rch) bs) blocks.

Lemma reads_ch_cons : forall rch bs blocks,
  reads_ch rch (bs :: blocks) = map (ReadEv rch) bs ++ reads_ch rch blocks.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition reads (blocks : list (list byte)) : list event :=
  reads_ch (Z_to_bv 64 0) blocks.

Lemma reads_cons : forall bs blocks,
  reads (bs :: blocks) = map (ReadEv (Z_to_bv 64 0)) bs ++ reads blocks.
Proof. exact (reads_ch_cons (Z_to_bv 64 0)). Qed.

Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.

(* [comment removed for export] *)
Definition out_tail (s : InputStream) (a : A) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition drain_from_ch (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  (exists blocks s' a',
     chunks cnt s blocks s' /\
     procs f a (concat blocks) = Some a' /\
     is_prefix tr (reads_ch rch blocks ++ out_tail s' a' fs))
  \/ (exists blocks bs s' a',
     chunks cnt s (blocks ++ [bs]) s' /\
     procs f a (concat blocks) = Some a' /\
     procs f a' bs = None /\
     is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [ExitEv ec fs])).

(* [comment removed for export] *)
Definition drain_from (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  drain_from_ch (Z_to_bv 64 0) a fs s tr.

#[using="Type"] Lemma drain_from_ch_prefix : forall rch a fs s tr tr',
  drain_from_ch rch a fs s tr -> is_prefix tr' tr -> drain_from_ch rch a fs s tr'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rch a fs s tr tr' [ (blocks & s' & a' & HC & Hp & Hpref)
                           | (blocks & bs & s' & a' & HC & Hp & Hn & Hpref) ] Hp'.
  - left. exists blocks, s', a'.
    split; [exact HC | split; [exact Hp | eapply is_prefix_trans; eauto]].
  - right. exists blocks, bs, s', a'.
    split; [exact HC | split; [exact Hp |
    split; [exact Hn | eapply is_prefix_trans; eauto]]].
Qed.

#[using="Type"] Lemma drain_from_prefix : forall a fs s tr tr',
  drain_from a fs s tr -> is_prefix tr' tr -> drain_from a fs s tr'.
Proof. LiaFast.lf_pins LiaFast.u0. exact (drain_from_ch_prefix (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_nil : forall rch a fs s, drain_from_ch rch a fs s [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rch a fs s. left. exists [], s, a.
  split; [constructor | split; [reflexivity | apply is_prefix_nil]].
Qed.

#[using="Type"] Lemma drain_from_nil : forall a fs s, drain_from a fs s [].
Proof. LiaFast.lf_pins LiaFast.u0. exact (drain_from_ch_nil (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma drain_from_ch_out : forall rch a fs tr,
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
  drain_from_ch rch a fs IEof tr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rch a fs tr Hp. left. exists [], IEof, a.
  split; [constructor | split; [reflexivity | exact Hp]].
Qed.

#[using="Type"] Lemma drain_from_out : forall a fs tr,
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]) ->
  drain_from a fs IEof tr.
Proof. LiaFast.lf_pins LiaFast.u0. exact (drain_from_ch_out (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_block : forall rch a a1 fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = Some a1 ->
  drain_from_ch rch a1 fs (snd (stream_take s (length bs))) tr ->
  drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rch a a1 fs s bs tr Hlo Hhi Hpre Hs
    [ (blocks & s' & a' & HC & Hp & Hpref)
    | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
  - left. exists (bs :: blocks), s', a'.
    split; [eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
  - right. exists (bs :: blocks), bsE, s', a'.
    split; [change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE]));
            eapply chunks_cons; eassumption |].
    split; [cbn [concat]; rewrite procs_app, Hs; exact Hp |].
    split; [exact Hn |].
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_ch_cons, <- app_assoc.
    apply is_prefix_app_mono. exact Hpref.
Qed.

#[using="Type"] Lemma drain_from_block : forall a a1 fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = Some a1 ->
  drain_from a1 fs (snd (stream_take s (length bs))) tr ->
  drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. LiaFast.lf_pins LiaFast.u0. exact (drain_from_ch_block (Z_to_bv 64 0)). Qed.

#[using="Type"] Lemma drain_from_ch_err : forall rch a fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = None ->
  is_prefix tr [ExitEv ec fs] ->
  drain_from_ch rch a fs s (map (ReadEv rch) bs ++ tr).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rch a fs s bs tr Hlo Hhi Hpre Hn Hp. right.
  exists [], bs, (snd (stream_take s (length bs))), a.
  split; [cbn [app]; eapply chunks_cons;
          try eassumption; constructor |].
  split; [reflexivity |].
  split; [exact Hn |].
  cbn [app]. unfold reads_ch. cbn [flat_map]. rewrite app_nil_r.
  apply is_prefix_app_mono. exact Hp.
Qed.

#[using="Type"] Lemma drain_from_err : forall a fs s bs tr,
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take s (length bs)) = bs ->
  procs f a bs = None ->
  is_prefix tr [ExitEv ec fs] ->
  drain_from a fs s (map (ReadEv (Z_to_bv 64 0)) bs ++ tr).
Proof. LiaFast.lf_pins LiaFast.u0. exact (drain_from_ch_err (Z_to_bv 64 0)). Qed.

End Traces.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd1chan_with_stdin : forall s m, fd1chan m -> fd1chan (with_stdin s m).
Proof. intros s m H. exact H. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.

(* [comment removed for export] *)
Definition lh_next (a : A) (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH a ms'.

(* [comment removed for export] *)
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).

(* [comment removed for export] *)
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

(* [comment removed for export] *)
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
  exists buf x8,
  ms_svc_pending ms = Some x8 /\
  bv_unsigned x8 = 63%Z /\
  ms_gpr ms 0 = Z_to_bv 64 0 /\
  ms_gpr ms 1 = buf /\
  ms_gpr ms 2 = cnt /\
  (exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
             = Some w) /\
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true /\
  to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
  (* [comment removed for export] *)
  buf_modeled (out a) /\
  (forall bs,
     (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
     match procs f a bs with
     | Some a' => lh_next a'
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     | None => to_exit segs ec
         (advance_past_svc (apply_effect ms
            (mkEffect (len_word bs) [(buf, bs)] [])))
     end).

(* [comment removed for export] *)
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

#[using="Type"] Lemma msteps_to_rd : forall a ms ms',
  msteps segs ms ms' -> to_rd a ms' -> to_rd a ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_out : forall bs ms ms',
  msteps segs ms ms' -> to_out bs ms' -> to_out bs ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms ms' H; induction H; [auto|].
  intro Ho. eapply tout_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_out_wall_tail : forall bs ms,
  to_out bs ms ->
  to_wall_tail segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms H;
    induction H as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH].
  - apply twt_done. exact Hte.
  - destruct HWF as [Hnb Hwl]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

#[using="H_LH"] Lemma lh_next_to_rd : forall a ms, lh_next a ms -> to_rd a ms.
Proof. LiaFast.lf_pins (fun (H_LH : LiaFast.U) => LiaFast.u0).
  intros a ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_rd_star : forall a ms model,
  m_halted model = None -> m_vm_lazy model = [] -> to_rd a ms ->
  exists msR, ReadPend a msR /\
    star segs (mkCfg ms model) [] (mkCfg msR model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a ms model Hh Hlazy Hrd.
  induction Hrd as [a ms HRP | a ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma msteps_star : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  star segs (mkCfg ms model) [] (mkCfg ms' model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' model Hh Hlazy H. induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
  - apply star_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms1 model) | exact IH];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_out_star_admits : forall bs ms model,
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  to_out bs ms -> buf_modeled bs ->
  exists c, star segs (mkCfg ms model)
              (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]) c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH]; intro Hbm.
  - cbn [map app].
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms model Hh Hlazy Hte) as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 |].
    intros ms' Hex.
    destruct (to_exit_star_admits segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex)
      as [c Hstar].
    exists c. rewrite band0_255 in Hstar. exact Hstar.
  - destruct (IH Hbm) as [c Hstar]. exists c.
    replace (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
      with ([] ++ (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]))
      by reflexivity.
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma to_out_star_only : forall bs ms model,
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  to_out bs ms -> buf_modeled bs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs ms model Hfd1 Hh Hlazy Ho Hbm. revert Hbm.
  induction Ho as [ms Hte | bs ms HWF | bs ms ms' Hsvc Hstep Ho IH];
    intros Hbm tr c Hstar.
  - cbn [map app].
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms model Hh Hlazy Hte tr c Hstar)
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - destruct HWF as (Hnb & Hwl).
    eapply (to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
              ms bs _ Hwl Hbm model);
      [exact Hh | exact Hlazy | apply fd1chan_fdchan; exact Hfd1 | | exact Hstar].
    intros ms' tr' c' Hex Hstar'.
    destruct (to_exit_star_only segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex tr' c' Hstar')
      as [-> | ->].
    + apply is_prefix_nil.
    + rewrite band0_255. apply is_prefix_refl.
  - inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst; [apply is_prefix_nil|].
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm tr2 _ Hstar2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt"] Lemma read0_check_eof_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (Z_to_bv 64 0) [] []) model
    = CheckOk model [].
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.read0_check_eof cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_eof_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  m_stdin model = IEof ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.read0_ok_eof cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_check_bytes_cnt : forall ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  check_read (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
              (map (ReadEv (Z_to_bv 64 0)) bs).
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.read0_check_bytes cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_bytes_cnt : forall ms x8 model w bs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
        (map (ReadEv (Z_to_bv 64 0)) bs)).
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.read0_ok_bytes cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_ok_inv_cnt : forall ms x8 model buf w eff model' evs,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
   model' = model /\ evs = [])
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        eff = mkEffect (len_word bs) [(buf, bs)] [] /\
        model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.read0_ok_inv cnt Hcnt). Qed.

#[using="Hcnt"] Lemma read0_no_err_cnt : forall ms x8 model w,
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.read0_no_unmodeled cnt Hcnt). Qed.

#[using="Hcnt"] Lemma sstep_read_inv_cnt : forall ms model buf x8 w evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  sstep segs (mkCfg ms model) evs st ->
  (m_stdin model = IEof /\ evs = [] /\
   st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
  \/ (exists bs,
        (1 <= Z.of_nat (length bs))%Z /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
        fst (stream_take (m_stdin model) (length bs)) = bs /\
        evs = map (ReadEv (Z_to_bv 64 0)) bs /\
        st = SNext (mkCfg
               (advance_past_svc (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])))
               (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                           model))).
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0). apply (StreamSim.sstep_read_inv cnt Hcnt). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Hcnt"] Lemma drain_read_step : forall bs ms model buf x8 w,
  M_loop model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf ->
  ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  access_okb buf (bv_unsigned cnt) = true ->
  (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
  fst (stream_take (m_stdin model) (length bs)) = bs ->
  sstep segs (mkCfg ms model) (map (ReadEv (Z_to_bv 64 0)) bs)
    (SNext (mkCfg (advance_past_svc (apply_effect ms
                     (mkEffect (len_word bs) [(buf, bs)] [])))
                  (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                              model))).
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0).
  intros bs ms model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi Hpre.
  pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  apply (sstep_syscall segs ms model x8
           (mkEffect (len_word bs) [(buf, bs)] [])
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
           (map (ReadEv (Z_to_bv 64 0)) bs));
    [exact Hh | exact Hsvc | | exact Hh |].
  - rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
    apply read0_ok_bytes_cnt with (w := w); assumption.
  - rewrite (materialize_model_accesses_no_lazy _ _).
    + reflexivity.
    + rewrite m_vm_lazy_with_stdin. exact Hlazy.
Qed.

#[using="Hcnt H_LH"] Lemma drain_star_admits_ok : forall s blocks s',
  chunks cnt s blocks s' ->
  forall a a' ms model,
  M_loop model -> m_stdin model = s -> to_rd a ms ->
  procs f a (concat blocks) = Some a' ->
  exists c, star segs (mkCfg ms model)
              (reads blocks ++ out_tail out s' a' (m_fs model)) c.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' ms model HM Hst Hrd Hp;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    unfold reads, reads_ch. cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* [comment removed for export] *)
      destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & _).
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok.
          exact (read0_ok_eof_cnt msR x8 model w Hno Hfd0 Hst Hg0 Hg2 Hw
                   Haok).
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      destruct (to_out_star_admits (out a) _ model Hfd1 Hh Hlazy Hout Hobm) as [c Hstar2].
      exists c. cbn [out_tail].
      replace (map (WriteEv (Z_to_bv 64 1)) (out a)
                 ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])
        with (([] : list event)
                ++ ([] ++ (map (WriteEv (Z_to_bv 64 1)) (out a)
                             ++ [ExitEv (Z_to_bv 64 0) (m_fs model)])))
        by reflexivity.
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* [comment removed for export] *)
      cbn [out_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* [comment removed for export] *)
    cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' advB model' HM' Hst' Hrd1 Hp) as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads blocks ++ out_tail out s'' a' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads blocks ++ out_tail out s'' a' (m_fs model))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

#[using="Hcnt Hec H_LH"] Lemma drain_star_admits_err : forall s blocks s1,
  chunks cnt s blocks s1 ->
  forall a a' bsE ms model,
  M_loop model -> m_stdin model = s -> to_rd a ms ->
  procs f a (concat blocks) = Some a' ->
  (1 <= Z.of_nat (length bsE))%Z -> (Z.of_nat (length bsE) <= bv_unsigned cnt)%Z ->
  fst (stream_take s1 (length bsE)) = bsE ->
  procs f a' bsE = None ->
  exists c, star segs (mkCfg ms model)
              (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)]) c.
Proof. LiaFast.lf_pins (fun (Hcnt Hec H_LH : LiaFast.U) => LiaFast.u0).
  intros s blocks s1 HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn;
    pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - cbn [concat procs] in Hp. injection Hp as <-.
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bsE HloE HhiE) as Hcont.
    rewrite Hn in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bsE) [(buf, bsE)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bsE))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (Hlazy' : m_vm_lazy model' = [])
      by (unfold model'; rewrite m_vm_lazy_with_stdin; exact Hlazy).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bsE)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bsE msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                HloE HhiE); rewrite Hst; exact HpreE. }
    destruct (to_exit_star_admits segs ec advB model' Hh' Hlazy' Hcont) as [c Hstar2].
    rewrite land_255_small in Hstar2 by exact Hec.
    change (m_fs model') with (m_fs model) in Hstar2.
    exists c.
    cbn [app]. unfold reads, reads_ch. cbn [flat_map]. rewrite app_nil_r.
    replace (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bsE ++ [ExitEv ec (m_fs model)]))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar2].
  - cbn [concat] in Hp. rewrite procs_app in Hp.
    destruct (procs f a bs) as [a1|] eqn:Hp1; [|discriminate].
    destruct (to_rd_star a ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hcont.
    rewrite Hp1 in Hcont.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { unfold advB, model'. rewrite <- Hst.
      eapply (drain_read_step bs msR model buf x8 w HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok
                Hlo Hhi); rewrite Hst; exact Hpre. }
    destruct Hcont as (msL & Hms & HLa1).
    pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
    destruct (IH a1 a' bsE advB model' HM' Hst' Hrd1 Hp HloE HhiE HpreE Hn)
      as [c Hstar3].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar3.
    change ((bs :: blocks) ++ [bsE]) with (bs :: (blocks ++ [bsE])).
    rewrite reads_cons, <- app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)])))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt Hec H_LH"] Lemma star_drain_only : forall c0 tr c', star segs c0 tr c' ->
  forall a ms model, c0 = mkCfg ms model -> M_loop model -> to_rd a ms ->
  drain_from cnt f out ec a (m_fs model) (m_stdin model) tr.
Proof. LiaFast.lf_pins (fun (Hcnt Hec H_LH : LiaFast.U) => LiaFast.u0).
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros a ms model Heq HM Hrd; subst.
  - apply drain_from_nil.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms' Hsvc Hstep Hrd'].
    + (* [comment removed for export] *)
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs (SNext c2)
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * (* [comment removed for export] *)
        pose proof (to_out_star_only (out a) _ model Hfd1 Hh Hlazy Hout Hobm
                      tr2 c3 Hstar) as Hpref.
        cbn [app]. rewrite Hs. apply drain_from_out. exact Hpref.
      * (* [comment removed for export] *)
        pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           pose proof (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)) as Hrd1.
           apply drain_from_block with (a1 := a1);
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           exact (IH a1 _ _ eq_refl (M_loop_take (length bs) model HM) Hrd1).
        -- apply drain_from_err;
             [exact Hlo | exact Hhi | exact Hpre | exact Hp1 |].
           destruct (to_exit_star_only segs ec _
                       (with_stdin (snd (stream_take (m_stdin model) (length bs)))
                                   model) Hh ltac:(rewrite m_vm_lazy_with_stdin; exact Hlazy)
                       Hcont tr2 c3 Hstar)
             as [-> | ->].
           ++ apply is_prefix_nil.
           ++ change (m_fs (with_stdin
                              (snd (stream_take (m_stdin model) (length bs)))
                              model)) with (m_fs model).
              rewrite land_255_small by exact Hec. apply is_prefix_refl.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                  Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
      subst evs. inversion Hc2; subst c2. cbn [app].
      exact (IH a _ model eq_refl HM Hrd').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dinv (c : config) : Prop :=
  (M_loop (cfg_model c) /\ exists a, to_rd a (cfg_ms c))
  \/ (fd1chan (cfg_model c) /\ m_halted (cfg_model c) = None /\
      m_vm_lazy (cfg_model c) = [] /\
      exists rest, buf_modeled rest /\
        to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) rest
          (to_exit segs (Z_to_bv 64 0)))
  \/ on_path segs (Z_to_bv 64 0) c
  \/ on_path segs ec c.

#[using="Type"] Lemma wall_out_dinv_step : forall rest ms model evs ms' model',
  fd1chan model -> m_halted model = None -> m_vm_lazy model = [] ->
  buf_modeled rest ->
  to_wall_tail segs (Z_to_bv 64 1) ms rest (to_exit segs (Z_to_bv 64 0)) ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg ms' model')) ->
  dinv (mkCfg ms' model').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss.
  assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
    by (apply fd1chan_fdchan; exact Hfd1).
  revert Hbm.
  inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                  | msS msS' restS kS HsvcS HstepS Ht']; subst; intro Hbm.
  - (* [comment removed for export] *)
    right. right. left.
    apply (on_path_step segs (Z_to_bv 64 0) (mkCfg ms model) evs); [|exact Hss].
    left. repeat split; assumption.
  - (* [comment removed for export] *)
    destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                ms rest _ model evs (SNext (mkCfg ms' model'))
                Hh Hlazy Hfdc Hbm Hwl Hss) as (n & Hn1 & Hn2 & _ & Hc2 & Ht2).
    inversion Hc2; subst.
    right. left. cbn. repeat split; try assumption.
    exists (skipn n rest).
    split; [apply buf_modeled_skipn; exact Hbm | exact Ht2].
  - (* [comment removed for export] *)
    destruct (sstep_instr_inv segs ms model msS' evs (SNext (mkCfg ms' model'))
                Hlazy HsvcS HstepS Hss) as [_ Hc2].
    inversion Hc2; subst.
    right. left. cbn. repeat split; try assumption.
    exists rest. split; [exact Hbm | exact Ht'].
Qed.
#[using="Hcnt H_LH"] Lemma dinv_step : forall c evs c',
  dinv c -> sstep segs c evs (SNext c') -> dinv c'.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs
                  (SNext (mkCfg ms' model'))
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
        inversion Hc2; subst.
      * right. left. cbn. repeat split; try assumption.
        exists (out a).
        split; [exact Hobm | exact (to_out_wall_tail _ _ Hout)].
      * pose proof (Hbytes bs Hlo Hhi) as Hcont.
        destruct (procs f a bs) as [a1|] eqn:Hp1.
        -- destruct Hcont as (msL & Hms & HLa1).
           left. cbn. split; [apply M_loop_take; exact HM|].
           exists a1. exact (msteps_to_rd a1 _ _ Hms (H_LH _ _ HLa1)).
        -- right. right. right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hcont].
    + destruct (sstep_instr_inv segs ms model ms1 evs
                  (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
      inversion Hc2; subst.
      left. cbn. split; [exact HM |]. exists a. exact Hrd'.
  - exact (wall_out_dinv_step rest ms model evs ms' model' Hfd1 Hh Hlazy Hbm Ht Hss).
  - right. right. left. eapply on_path_step; eauto.
  - right. right. right. eapply on_path_step; eauto.
Qed.

#[using="Hcnt"] Lemma dinv_no_error : forall c evs, dinv c -> ~ sstep segs c evs SError.
Proof. LiaFast.lf_pins (fun (Hcnt : LiaFast.U) => LiaFast.u0).
  intros [ms model] evs Hinv Hss.
  destruct Hinv as
    [[HM (a & Hrd)] | [[Hfd1 [Hh [Hlazy (rest & Hbm & Ht)]]] | [Hop | Hop]]];
    cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    destruct Hrd as [a ms (buf & x8 & HRP) | a ms ms1 Hsvc Hstep Hrd'].
    + destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hout & Hobm & Hbytes).
      destruct (sstep_read_inv_cnt ms model buf x8 w evs SError
                  Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
        as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
    + destruct (sstep_instr_inv segs ms model ms1 evs SError
                  Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
  - assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    inversion Ht as [msD kD HkD | msM restM kM HnbM Hwl
                    | msS msS' restS kS HsvcS HstepS Ht']; subst.
    + eapply (on_path_no_error segs (Z_to_bv 64 0) (mkCfg ms model));
        [left; repeat split; assumption | exact Hss].
    + exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               ms rest _ model evs Hh Hlazy Hfdc Hbm Hwl Hss).
    + destruct (sstep_instr_inv segs ms model msS' evs SError
                  Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
  - eapply on_path_no_error; eauto.
Qed.

#[using="Hcnt H_LH"] Lemma star_dinv : forall c tr c', dinv c -> star segs c tr c' -> dinv c'.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0). exact (star_inv segs dinv dinv_step). Qed.

#[using="Hcnt H_LH"] Lemma to_rd_no_error : forall a ms model,
  M_loop model -> to_rd a ms -> ~ reaches_error segs (mkCfg ms model).
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros a ms model HM Hrd.
  apply (inv_no_reaches_error segs dinv dinv_step dinv_no_error).
  left; cbn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt Hec H_LH"] Lemma drain_obs_iff : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp) tr.
Proof. LiaFast.lf_pins (fun (Hcnt Hec H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
  set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    pose proof (star_drain_only _ _ _ Hstar a0 ms0 model0 eq_refl HM0 Hrd) as Hd.
    rewrite Hst0, Hfs0 in Hd.
    eapply drain_from_prefix; eauto.
  - intros [ (blocks & s' & a' & HC & Hp & Hpref)
           | (blocks & bsE & s' & a' & HC & Hp & Hn & Hpref) ].
    + destruct (drain_star_admits_ok _ blocks s' HC a0 a' ms0 model0
                  HM0 Hst0 Hrd Hp) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
    + destruct (chunks_split _ blocks [bsE] _ _ HC) as (s1 & HC1 & HC2).
      destruct (chunks_single_inv _ _ _ _ HC2) as (HloE & HhiE & HpreE & _).
      destruct (drain_star_admits_err _ blocks s1 HC1 a0 a' bsE ms0 model0
                  HM0 Hst0 Hrd Hp HloE HhiE HpreE Hn) as [c Hstar].
      rewrite Hfs0 in Hstar.
      eexists; exists c; split; [exact Hstar | exact Hpref].
Qed.

#[using="Hcnt H_LH"] Lemma drain_no_error : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd.
  apply (to_rd_no_error a0); [apply init_M_loop | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma to_rd_coexec : forall a ms model,
  M_loop model -> to_rd a ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros a ms model HM Hrd.
  apply (inv_coexec segs dinv dinv_step dinv_no_error).
  left; cbn. split; [exact HM | exists a; exact Hrd].
Qed.

#[using="Hcnt H_LH"] Lemma drain_omni_corun : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof. LiaFast.lf_pins (fun (Hcnt H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_corun]. unfold init_config.
  apply (to_rd_coexec a0); [apply init_M_loop | exact Hrd].
Qed.

#[using="Hcnt Hec H_LH"] Lemma drain_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp a0,
  to_rd a0 (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (drain_from cnt f out ec a0 (in_fs inp) (in_stdin inp)).
Proof. LiaFast.lf_pins (fun (Hcnt Hec H_LH : LiaFast.U) => LiaFast.u0).
  intros pc ph sp brk0 mb rnd lim inp a0 Hrd. cbn [omni_cosafe].
  apply cosafe_obs_iff.
  - (* [comment removed for export] *)
    intros t t' Ht Hp.
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd).
    eapply obs_trace_prefix_closed; [| exact Hp].
    apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Ht.
  - intros tr Hobs. apply (drain_obs_iff pc ph sp brk0 mb rnd lim inp a0 Hrd). exact Hobs.
Qed.

End Drain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma drain_omni_strong_equiv :
  forall (A : Type) (cnt : word) (f : A -> byte -> option A)
         (out : A -> list byte) (ec : word) (a0 : A)
         source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
  (bv_unsigned ec < 256)%Z ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall a ms, rLH a ms -> to_rd source_segs cnt f out ec rLH a ms) ->
  (forall a ms, aLH a ms -> to_rd target_segs cnt f out ec aLH a ms) ->
  to_rd source_segs cnt f out ec rLH a0
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_rd target_segs cnt f out ec aLH a0
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp Hec Hcnt HrLH HaLH Hr Ha.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (drain_omni_corun source_segs cnt Hcnt f out ec rLH HrLH
                rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr tr).
    rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha tr).
    reflexivity.
  - exact (drain_omni_corun target_segs cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha).
Qed.

Lemma drain_strong_equiv :
  forall (A : Type) (cnt : word) (f : A -> byte -> option A)
         (out : A -> list byte) (ec : word) (a0 : A)
         source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
  (bv_unsigned ec < 256)%Z ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  (forall a ms, rLH a ms -> to_rd source_segs cnt f out ec rLH a ms) ->
  (forall a ms, aLH a ms -> to_rd target_segs cnt f out ec aLH a ms) ->
  to_rd source_segs cnt f out ec rLH a0
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  to_rd target_segs cnt f out ec aLH a0
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros A cnt f out ec a0 source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp Hec Hcnt HrLH HaLH Hr Ha.
  split.
  { apply no_error_run_modeled.
    apply (drain_no_error source_segs cnt Hcnt f out ec rLH HrLH
             rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr). }
  right. split.
  - intro tr. cbn.
    rewrite (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
               rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr tr).
    rewrite (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
               apc aph asp abrk amb arnd alim inp a0 Ha tr).
    reflexivity.
  - cbn.
    apply (drain_no_error target_segs cnt Hcnt f out ec aLH HaLH
             apc aph asp abrk amb arnd alim inp a0 Ha).
Qed.
End DrainSim.

Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SeqExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.WallSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.StepTac.DrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.

Import ListNotations.

Module ClfME.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require PropExec CatSim CatExec SeqExec.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require CatSim.
Import OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.PropExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.SeqExec OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim.
Import ListNotations.
Local Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Instance clfme_fx : FPState := fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.

(* [comment removed for export] *)
Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc mem rom x8 r. unfold epend.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
  intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap_small
    by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Local Notation ME code c := (must_exit_at_cfg forced_only_cfg segs code c) (only parsing).

(* [comment removed for export] *)
#[using="Type"] Lemma not_spurious_uninjected : forall cfg ms x8 model eff,
  injected_arm (bv_unsigned x8) = None ->
  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cfg ms x8 model eff Hn. apply spurious_refusal_family_on.
  unfold injected_family_off. change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma me_step : forall code ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  ME code (mkCfg ms' model) ->
  ME code (mkCfg ms model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros code ms ms' model Hh Hlazy Hsvc Hstep Hme.
  apply must_exit_at_cfg_running.
  - exact Hh.
  - exists [], (SNext (mkCfg ms' model)). apply sstep_cfg_instr; [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros evs Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_instr_inv segs _ _ _ _ _ Hlazy Hsvc Hstep Hss) as [_ Hst]. discriminate.
  - intros evs c' Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_instr_inv segs _ _ _ _ _ Hlazy Hsvc Hstep Hss) as [_ Hst].
    injection Hst as Hc. subst c'. exact Hme.
Qed.

#[using="Type"] Lemma me_msteps : forall code ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ME code (mkCfg ms' model) ->
  ME code (mkCfg ms model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros code ms ms' model Hh Hlazy Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intros Hme; [exact Hme|].
  eapply me_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hme].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma me_sys : forall code regs pc mem rom model w,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  ME code (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
  ME code (mkCfg (mkst regs pc mem rom) model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros code regs pc mem rom model w Hh Hlazy HF HE Hme.
  eapply me_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hme].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma me_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  ME (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (mkCfg ms model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 Hh Hsvc Hx8.
  apply must_exit_at_cfg_running.
  - exact Hh.
  - do 2 eexists. eapply sstep_cfg_exit; [exact Hh | exact Hsvc | | apply m_halted_with_halted
                                         | apply m_killed_with_halted].
    apply exit_dispatch_ok. rewrite in_sysno_sys_input. exact Hx8.
  - intros evs Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_exit_inv segs _ _ _ _ _ Hh Hsvc Hx8 Hss) as [_ Hst]. discriminate.
  - intros evs c' Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_exit_inv segs _ _ _ _ _ Hh Hsvc Hx8 Hss) as [_ Hst].
    injection Hst as Hc. subst c'. apply must_exit_at_cfg_halted; cbn [cfg_model].
    + apply m_halted_with_halted.
    + apply m_killed_with_halted.
Qed.

#[using="Type"] Lemma me_exit_lit : forall regs pc mem rom model (code : Z),
  m_halted model = None -> is_exit_no (getr regs 17) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  ME (Z_to_bv 64 code) (mkCfg (epend regs pc mem rom (getr regs 17)) model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model code Hh Hx8 Ha0 Hc.
  rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply me_exit; [exact Hh | reflexivity | exact Hx8].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma me_exit_at : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  ME (Z_to_bv 64 code) (mkCfg (mkst regs pc mem rom) model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  eapply me_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply me_exit_lit; [exact Hh | | exact H10 | exact Hc].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma syscall_spec_96 : forall ms x8 m o, bv_unsigned x8 = 96%Z ->
  syscall_spec (sys_input segs ms x8) m o <-> set_tid_address_spec (sys_input segs ms x8) m o.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms x8 m o E; unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma set_tid_fresh_ok : forall i m eff m' evs,
  m_tid m = None ->
  set_tid_address_spec i m (Ok eff m' evs) <->
  exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z
            /\ eff = mkEffect t [] [] /\ m' = with_tid t m /\ evs = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i m eff m' evs Htid. unfold set_tid_address_spec.
  rewrite bind_get_model. rewrite Htid.
  unfold set_tid, ret_only, bind, choose, modify, pure. split.
  - intros H. sys_destruct.
    match goal with |- exists t, _ /\ mkEffect ?x [] [] = _ /\ _ => exists x end.
    repeat split; try assumption; reflexivity.
  - intros (t & Ht & -> & -> & ->).
    exists t, m, [], []. split; [exists t; split; [exact Ht | reflexivity]|]. split; [|reflexivity].
    exists tt, (with_tid t m), [], []. split; [reflexivity|]. split; reflexivity.
Qed.

#[using="Type"] Lemma set_tid_fresh_unmodeled : forall i m,
  m_tid m = None -> ~ set_tid_address_spec i m Unmodeled.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i m Htid H. unfold set_tid_address_spec in H.
  rewrite bind_get_model in H. rewrite Htid in H.
  unfold set_tid, ret_only, bind, choose, modify, pure in H. sys_destruct.
Qed.

#[using="Type"] Lemma with_tid_halted' : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. LiaFast.lf_pins LiaFast.u0. intros t m. destruct m; reflexivity. Qed.
#[using="Type"] Lemma with_tid_lazy' : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. LiaFast.lf_pins LiaFast.u0. intros t m. destruct m; reflexivity. Qed.

#[using="Type"] Lemma me_set_tid : forall code regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     ME code (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model))) ->
  ME code (mkCfg (mkst regs pc mem rom) model).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros code regs pc mem rom model w HF HE Hh Hlazy H17 Htid Hk.
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; reflexivity).
  eapply me_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hsvc : ms_svc_pending ms = Some (getr regs 17)) by reflexivity.
  assert (Hns : forall eff, ~ spurious_refusal_cfg forced_only_cfg (sys_input segs ms (getr regs 17)) model eff).
  { intro eff. apply not_spurious_uninjected. rewrite Hno. reflexivity. }
  assert (Hlz' : forall t, m_vm_lazy (with_tid t model) = []) by (intro t; rewrite with_tid_lazy'; exact Hlazy).
  apply must_exit_at_cfg_running.
  - exact Hh.
  - exists [], (SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 1) [] [])))
                          (with_tid (Z_to_bv 64 1) model))).
    eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | | apply Hns | rewrite with_tid_halted'; exact Hh
                              | apply materialize_model_accesses_no_lazy; apply Hlz'].
    apply (proj2 (syscall_spec_96 ms _ model _ Hno)). apply set_tid_fresh_ok; [exact Htid|].
    exists (Z_to_bv 64 1). split; [split; vm_compute; reflexivity | auto].
  - intros evs Hss. inversion Hss; subst;
      match goal with
      | H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1
      | H1 : ms_svc_pending ms = Some ?y |- _ =>
          rewrite Hsvc in H1; injection H1; intro; subst y
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          apply (proj1 (syscall_spec_96 ms _ model _ Hno)) in Hs;
          apply set_tid_fresh_ok in Hs as (t & _ & -> & -> & ->); [| exact Htid];
          rewrite (materialize_model_accesses_no_lazy _ _ (Hlz' t)) in Hm; discriminate Hm
      end.
    + match goal with
      | Hs : syscall_spec _ _ Unmodeled |- _ =>
          apply (proj1 (syscall_spec_96 ms _ model _ Hno)) in Hs;
          exact (set_tid_fresh_unmodeled _ _ Htid Hs)
      end.
  - intros evs c' Hss. inversion Hss; subst;
      match goal with
      | H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1
      | H1 : ms_svc_pending ms = Some ?y |- _ =>
          rewrite Hsvc in H1; injection H1; intro; subst y
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
          apply (proj1 (syscall_spec_96 ms _ model _ Hno)) in Hs;
          apply set_tid_fresh_ok in Hs as (t & Ht & -> & -> & ->); [| exact Htid];
          rewrite (materialize_model_accesses_no_lazy _ _ (Hlz' t)) in Hm; injection Hm as <-
      end.
      subst ms. rewrite adv_eff_ret_epend. apply Hk. exact Ht.
    + exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hc : m_halted ?m1 = Some _ |- _ =>
          apply (proj1 (syscall_spec_96 ms _ model _ Hno)) in Hs;
          apply set_tid_fresh_ok in Hs as (t & _ & -> & -> & ->); [| exact Htid];
          rewrite with_tid_halted', Hh in Hc; discriminate Hc
      end.
    + exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hk2 : m_killed ?m1 = Some _ |- _ =>
          apply (proj1 (syscall_spec_96 ms _ model _ Hno)) in Hs;
          apply set_tid_fresh_ok in Hs as (t & _ & -> & -> & ->); [| exact Htid];
          rewrite (m_killed_of_m_halted_none _ (eq_trans (with_tid_halted' t model) Hh)) in Hk2;
          discriminate Hk2
      end.
Qed.

End WithSegs.
End ClfME.

Module Hoare.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

#[using="Type"] Lemma at_0 : forall base, at_ base 0 = base.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma at_btgt : forall base d e, btgt (at_ base d) e = at_ base (d + e).
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold btgt. apply at_addi. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma at_lit : forall (base : word) (d : Z) (a : word),
  Z_to_bv 64 (bv_unsigned base + d) = a -> at_ base d = a.
Proof. LiaFast.lf_pins LiaFast.u0. intros. assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. LiaFast.lf_pins LiaFast.u0. exact at_addi. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_succ_shift : forall (a : word) (i : Z),
  Z_to_bv 64 (bv_unsigned (a + 1) + i) = Z_to_bv 64 (bv_unsigned a + (1 + i)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a i. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. LiaFast.lf_pins LiaFast.u0. intros a. exact (at_0 a). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

#[using="Type"] Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. LiaFast.lf_pins LiaFast.u0. intros C regs r _. reflexivity. Qed.

#[using="Type"] Lemma mem_agree_refl : forall W m, mem_agree W m m.
Proof. LiaFast.lf_pins LiaFast.u0. intros W m x _. reflexivity. Qed.

#[using="Type"] Lemma regs_agree_trans : forall C regs1 regs2 regs3,
  regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. LiaFast.lf_pins LiaFast.u0. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

#[using="Type"] Lemma mem_agree_trans : forall W m1 m2 m3,
  mem_agree W m1 m2 -> mem_agree W m2 m3 -> mem_agree W m1 m3.
Proof. LiaFast.lf_pins LiaFast.u0. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

#[using="Type"] Lemma regs_agree_mono : forall (C C' : regset) regs regs',
  (forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. LiaFast.lf_pins LiaFast.u0. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

#[using="Type"] Lemma mem_agree_mono : forall (W W' : memset) m m',
  (forall x, W x -> W' x) -> mem_agree W m m' -> mem_agree W' m m'.
Proof. LiaFast.lf_pins LiaFast.u0. intros W W' m m' Hsub H x Hx. apply H. intro; apply Hx, Hsub; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
  C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

#[using="Type"] Lemma mem_agree_wbytes : forall (W : memset) m m' a bs,
  (forall i, (0 <= i < Z.of_nat (length bs))%Z -> W (Z_to_bv 64 (bv_unsigned a + i))) ->
  mem_agree W m m' -> mem_agree W m (wbytes m' a bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' a bs. revert m' a.
  induction bs as [|b bs IH]; intros m' a Hin H; cbn [wbytes] in *; [exact H|].
  assert (Ha : W a).
  { specialize (Hin 0%Z ltac:(cbn [length]; lia)). rewrite at_self in Hin. exact Hin. }
  apply IH.
  - intros i Hi. rewrite u_succ_shift. apply Hin. cbn [length] in *. lia.
  - intros x Hx. cbn beta. destruct (bv_eqb x a) eqn:Heq.
    + exfalso. apply Hx. unfold bv_eqb in Heq. apply Z.eqb_eq, bv_eq in Heq.
      subst x. exact Ha.
    + apply H, Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop :=
  forall regs mem rom, P regs mem rom ->
    exists regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      /\ Q regs' mem' rom
      /\ regs_agree C regs regs'
      /\ mem_agree W mem mem'.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_intro : forall segs C W P a b Q,
  (forall regs mem rom, P regs mem rom ->
     exists regs' mem',
       msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
       /\ Q regs' mem' rom
       /\ regs_agree C regs regs'
       /\ mem_agree W mem mem') ->
  triple segs C W P a b Q.
Proof. LiaFast.lf_pins LiaFast.u0. intros; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma triple_skip : forall segs C W P a, triple segs C W P a a P.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W P a regs mem rom HP.
  exists regs, mem. split; [apply mst_refl|].
  split; [exact HP|]. split; [apply regs_agree_refl|apply mem_agree_refl].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_seq : forall segs C1 W1 C2 W2 P Q R a b c,
  triple segs C1 W1 P a b Q ->
  triple segs C2 W2 Q b c R ->
  triple segs (fun r => C1 r \/ C2 r) (fun x => W1 x \/ W2 x) P a c R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C1 W1 C2 W2 P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|]. split.
  - eapply regs_agree_trans;
      [ eapply regs_agree_mono; [|exact Hr1]
      | eapply regs_agree_mono; [|exact Hr2] ]; auto.
  - eapply mem_agree_trans;
      [ eapply mem_agree_mono; [|exact Hm1]
      | eapply mem_agree_mono; [|exact Hm2] ]; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_conseq : forall segs C C' W W' P P' Q Q' a b,
  triple segs C W P a b Q ->
  (forall regs mem rom, P' regs mem rom -> P regs mem rom) ->
  (forall regs mem rom, Q regs mem rom -> Q' regs mem rom) ->
  (forall r, C r -> C' r) ->
  (forall x, W x -> W' x) ->
  triple segs C' W' P' a b Q'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C C' W W' P P' Q Q' a b H HP HQ HC HW regs mem rom HP'.
  destruct (H _ _ _ (HP _ _ _ HP')) as (regs' & mem' & Hst & HQ0 & Hr & Hm).
  exists regs', mem'. split; [exact Hst|]. split; [apply HQ, HQ0|].
  split; [eapply regs_agree_mono; eauto | eapply mem_agree_mono; eauto].
Qed.

#[using="Type"] Lemma triple_seq_same : forall segs C W P Q R a b c,
  triple segs C W P a b Q ->
  triple segs C W Q b c R ->
  triple segs C W P a c R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W P Q R a b c H1 H2 regs mem rom HP.
  destruct (H1 _ _ _ HP) as (regs1 & mem1 & Hst1 & HQ & Hr1 & Hm1).
  destruct (H2 _ _ _ HQ) as (regs2 & mem2 & Hst2 & HR & Hr2 & Hm2).
  exists regs2, mem2. split; [eapply msteps_trans; eassumption|].
  split; [exact HR|].
  split; [eapply regs_agree_trans; eassumption | eapply mem_agree_trans; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
  forall regs mem rom regs' mem',
    regs_agree C regs regs' -> mem_agree W mem mem' ->
    R regs mem rom -> R regs' mem' rom.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_frame : forall segs C W P Q R a b,
  triple segs C W P a b Q ->
  frameable C W R ->
  triple segs C W (fun regs mem rom => P regs mem rom /\ R regs mem rom) a b
                  (fun regs mem rom => Q regs mem rom /\ R regs mem rom).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W P Q R a b H HR regs mem rom (HP & HRr).
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split; [exact Hst|].
  split; [split; [exact HQ | eapply HR; eassumption]|].
  split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frameable_and : forall C W R1 R2,
  frameable C W R1 -> frameable C W R2 ->
  frameable C W (fun regs mem rom => R1 regs mem rom /\ R2 regs mem rom).
Proof. LiaFast.lf_pins LiaFast.u0. intros C W R1 R2 H1 H2 regs mem rom regs' mem' Hr Hm (A & B); split; eauto. Qed.

#[using="Type"] Lemma frameable_reg : forall (C : regset) W (r : reg) (v : word),
  ~ C r -> frameable C W (fun regs _ _ => getr regs r = v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros C W r v Hnc regs mem rom regs' mem' Hr _ Hv.
  rewrite (Hr r Hnc). exact Hv.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma frameable_rdn : forall segs (C : regset) (W : memset) (a : word) (n : nat) bs,
  (forall i, (0 <= i < Z.of_nat n)%Z -> ~ W (Z_to_bv 64 (bv_unsigned a + i))) ->
  frameable C W (fun _ mem _ => rdn segs mem a n = Some bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W a n bs Hdisj regs mem rom regs' mem' _ Hm Hrd.
  rewrite <- Hrd. clear Hrd bs. revert a Hdisj.
  induction n as [|n IH]; intros a Hdisj; [reflexivity|].
  assert (Ha : ~ W a).
  { specialize (Hdisj 0%Z ltac:(lia)). rewrite at_self in Hdisj. exact Hdisj. }
  cbn [rdn]. rewrite (Hm a Ha). rewrite IH; [reflexivity|].
  intros i Hi. rewrite u_succ_shift. apply Hdisj. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

#[using="Type"] Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

#[using="Type"] Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop :=
  forall k : word, ret_ok k ->
    triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

(* [comment removed for export] *)
Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_call : forall segs C W P Q callsite entry ret,
  (forall regs mem rom,
     RiscvSemantics.step segs (mkst regs callsite mem rom)
       = MachineOk (mkst (regupd regs 1 ret) entry mem rom)) ->
  ret_ok ret ->
  ra_indep P ->
  proc segs C W P entry Q ->
  triple segs (fun r => C r \/ r = 1) W P callsite ret Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W P Q callsite entry ret Hjal Hret HraP Hproc regs mem rom HP.
  assert (Hpre : P (regupd regs 1 ret) mem rom
                 /\ getr (regupd regs 1 ret) 1 = ret).
  { split; [apply HraP, HP|]. apply getr_same. reg_neq_tac. }
  destruct (Hproc ret Hret (regupd regs 1 ret) mem rom Hpre)
    as (regs' & mem' & Hst & HQ & Hr & Hm).
  exists regs', mem'. split.
  - eapply mst_step; [reflexivity | apply Hjal | exact Hst].
  - split; [exact HQ|]. split; [|exact Hm].
    intros r Hr0.
    assert (HnC : ~ C r) by tauto.
    assert (Hne : r <> 1) by tauto.
    rewrite (Hr r HnC), getr_other by exact Hne. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma triple_loop : forall segs C W (I : nat -> assn) (hd out : word) (Q : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  forall n, triple segs C W (I n) hd out Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W I hd out Q Hbody Hexit n.
  induction n as [|n IH]; [exact Hexit|].
  eapply triple_seq_same; [apply Hbody | exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_loop_measure :
  forall segs C W (I : nat -> assn) (hd out : word) (Q P : assn),
  (forall i, triple segs C W (I (S i)) hd hd (I i)) ->
  triple segs C W (I O) hd out Q ->
  (forall regs mem rom, P regs mem rom -> exists n, I n regs mem rom) ->
  triple segs C W P hd out Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W I hd out Q P Hbody Hexit Hmeas regs mem rom HP.
  destruct (Hmeas _ _ _ HP) as (n & HI).
  exact (triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma triple_msteps : forall segs C W P a b Q regs mem rom,
  triple segs C W P a b Q -> P regs mem rom ->
  exists regs' mem',
    msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) /\ Q regs' mem' rom.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W P a b Q regs mem rom H HP.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  exists regs', mem'. split; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma triple_wexit : forall segs C W P a b Q bufs code regs mem rom,
  triple segs C W P a b Q ->
  P regs mem rom ->
  (forall regs' mem', Q regs' mem' rom ->
     to_wexit segs (mkst regs' b mem' rom) bufs code) ->
  to_wexit segs (mkst regs a mem rom) bufs code.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs C W P a b Q bufs code regs mem rom H HP Hcont.
  destruct (H _ _ _ HP) as (regs' & mem' & Hst & HQ & _ & _).
  eapply msteps_to_wexit; [exact Hst | apply Hcont, HQ].
Qed.
End WithFP1.

End Hoare.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP3.
Ltac expand_ctx_defs p :=
  match goal with
  | H := _ |- _ =>
      lazymatch p with
      | context [H] => let p' := eval unfold H in p in expand_ctx_defs p'
      end
  | _ => p
  end.

Section WithFP4.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP10.
Ltac norm_pc_state st :=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => wlit p
       | _ => idtac
       end.
Ltac norm_pc :=
  try lazymatch goal with
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP12.
Ltac reduce_bv_eqb_ifs :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let v := eval vm_compute in (bv_eqb a b) in
              lazymatch v with
              | true => change (if bv_eqb a b then x else y) with x
              | false => change (if bv_eqb a b then x else y) with y
              end
          end
      end
  end.

Section WithFP13.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Section WithFP14.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP14.
Ltac stepi_search F D :=
  first
    [ exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    (* [comment removed for export] *)
    | exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D) ].

Section WithFP15.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP15.
Ltac stepi F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
        exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
        exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
        exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
        exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) =>
        exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) =>
        exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRA _ _ _, _) =>
        exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
        exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
        exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_ADD _ _ _, _) =>
        exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) =>
        exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SLL _ _ _, _) =>
        exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRL _ _ _, _) =>
        exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRA _ _ _, _) =>
        exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SLL _ _ _, _) =>
        exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRL _ _ _, _) =>
        exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRA _ _ _, _) =>
        exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Auipc _ _, _) =>
        exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Lui _ _, _) =>
        exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULH _ _ _, _) =>
        exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHSU _ _ _, _) =>
        exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHU _ _ _, _) =>
        exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIV _ _ _, _) =>
        exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_REM _ _ _, _) =>
        exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIVU _ _ _, _) =>
        eapply step_divu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul M_REMU _ _ _, _) =>
        eapply step_remu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
        exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIV _ _ _, _) =>
        exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIVU _ _ _, _) =>
        exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REM _ _ _, _) =>
        exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REMU _ _ _, _) =>
        exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP16.
Ltac stepiv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        eapply step_addi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        eapply step_andi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        eapply step_ori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        eapply step_xori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        eapply step_sltiu_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        eapply step_slli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        eapply step_srli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        eapply step_srai_at with (v := vv)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        eapply step_add_at with (v := vv)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        eapply step_sub_at with (v := vv)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        eapply step_addiw_at with (v := vv)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        eapply step_mul_at with (v := vv)
    | decode_any _ = Some (Lui _ _, _) =>
        eapply step_lui_at with (v := vv)
    | decode_any _ = Some (Auipc _ _, _) =>
        eapply step_auipc_at with (v := vv)
    | _ => eapply step_addi_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP17.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP19.
Ltac stepjr F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

Section WithFP20.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof. LiaFast.lf_pins LiaFast.u0. intros x H1. apply (v_addi_m x 1); lia. Qed.

#[using="Type"] Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof. LiaFast.lf_pins LiaFast.u0. intros x H16. apply (v_addi_m x 16); lia. Qed.

#[using="Type"] Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof. LiaFast.lf_pins LiaFast.u0. intros x H32. apply (v_addi_m x 32); lia. Qed.

#[using="Type"] Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof. LiaFast.lf_pins LiaFast.u0. intros x H48. apply (v_addi_m x 48); lia. Qed.

#[using="Type"] Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof. LiaFast.lf_pins LiaFast.u0. intros x H64. apply (v_addi_m x 64); lia. Qed.

#[using="Type"] Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof. LiaFast.lf_pins LiaFast.u0. intros x H80. apply (v_addi_m x 80); lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof. LiaFast.lf_pins LiaFast.u0. intros x imm _ _. reflexivity. Qed.

(* [comment removed for export] *)
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.

Section WithFP21.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP21.
Ltac imm_norm :=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end.

Section WithFP22.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP22.
Ltac sp_norm :=
  imm_norm;
  repeat (match goal with
  | |- context [v_addi ?x ?i] =>
      lazymatch x with
      | context [v_addi _ _] => fail
      | _ => first [ rewrite (v_addi_m80 x) by (u_norm; lia)
                   | rewrite (v_addi_m64 x) by (u_norm; lia)
                   | rewrite (v_addi_m48 x) by (u_norm; lia)
                   | rewrite (v_addi_m32 x) by (u_norm; lia)
                   | rewrite (v_addi_m16 x) by (u_norm; lia)
                   | rewrite (v_addi_m1 x) by (u_norm; lia)
                   | rewrite (v_addi_nneg_t x i) by (u_norm; lia) ]
      end
  end; u_norm; cbn [Z.to_N]).

Section WithFP23.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP23.
Ltac stepi_at F D val :=
  chain_step;
  [ reflexivity
  | eapply step_addi_at with (v := val);
    [ exact F | reflexivity | exact D
    | reflexivity
    | getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm;
      first [ reflexivity | lia | f_equal; lia
            | apply bv_eq;
              lazymatch goal with |- ?g => check_closed_term g end;
              vm_compute; reflexivity ] ]
  | step_simpl ].

Section WithFP24.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP24.
Ltac bveq :=
  apply bv_eq;
  lazymatch goal with
  | |- ?g =>
      tryif check_closed_term g then
        first
          [ (vm_compute; reflexivity)
          | fail 1 "bveq: vm_compute did not close this closed goal: "
                   "its two sides compute to different values." ]
      else tryif has_evar g then
        fail 1 "bveq: the goal contains an evar — vm_compute must not "
               "see it; instantiate the machine state (eexists / "
               "chain_step) before normalizing."
      else
        (* [comment removed for export] *)
        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : FPState}.

(* [comment removed for export] *)
Goal v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8.
Proof. bveq. Abort.
Goal forall regs (v : word), getr (regupd regs 11 v) 11 = v.
Proof. intros. assert_fails bveq. getr_resolve. reflexivity. Abort.

(* [comment removed for export] *)
Goal forall v : word, exists w : word, w = v.
Proof.
  intros v. eexists.
  check_closed_term (v_addi (Z_to_bv 64 5) 3).
  assert_fails (check_closed_term (v_addi v 4)).
  lazymatch goal with |- ?g => assert_fails (check_closed_term g) end.
  set (k := Z_to_bv 64 7).
  check_closed_term (v_addi k 1).
  set (k2 := v_addi v 1).
  assert_fails (check_closed_term (v_addi k2 1)).
  let u := vm_eval (bv_unsigned (v_addi (Z_to_bv 64 5) 3)) in
  lazymatch u with 8%Z => idtac end.
  (* [comment removed for export] *)
  try (let u := vm_eval (bv_unsigned (v_addi v 4)) in
       fail 1 "vm_eval accepted an open term").
Abort.

(* [comment removed for export] *)
Goal forall v : word, v_addi v 4 = v_addi v 4.
Proof. intros v. wlit (v_addi v 4). wlits. reflexivity. Abort.
Goal forall v : word,
  (v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4).
Proof.
  intros v. wlits.
  lazymatch goal with |- (@BV _ _ _, _) = _ => idtac end.
  f_equal. bveq.
Abort.

(* [comment removed for export] *)
End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

(* [comment removed for export] *)
Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP27.
Ltac stepw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepsd F D aexp vexp vtac oktac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | stepw_addr_hyps | vtac | oktac ]
  | step_simpl ].

Ltac stepld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by stepw_addr_hyps
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Section WithFP28.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [ (* [comment removed for export] *)
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (bv_unsigned b <> 0)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b Hb Hc. apply Hb. apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_zext8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intro b. apply u_Z2bv; pose proof (u8_range b); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zext8_byte : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intro b. apply bv_eq.
  rewrite Z_to_bv_unsigned, u_zext8.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma byte_neq_lit_u : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z -> (bv_unsigned b <> z)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b z Hz Hb Hc. apply Hb. apply bv_eq.
  rewrite Hc, Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.mod_small; [reflexivity |].
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c_eq_zext_lit_false : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z ->
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b z Hz Hb. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  rewrite u_zext8, u_Z2bv by lia.
  exact (byte_neq_lit_u b z Hz Hb).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  bv_unsigned (nat_to_word n) = Z.of_nat n.
Proof. LiaFast.lf_pins LiaFast.u0. intros n Hn. unfold nat_to_word. apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat_0 : forall x : word, x + nat_to_word 0 = x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intro x. apply bv_eq. rewrite word_add_nat.
  rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_add_wrap : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2^64).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x y Hw. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z.mod_add (bv_unsigned x + bv_unsigned y - 2^64) 1 (2^64)) by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_sub_0_neg : forall y : word,
  v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (- bv_unsigned y).
Proof. LiaFast.lf_pins LiaFast.u0.
  intro y. unfold v_sub.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  f_equal.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u_neg_small : forall z : Z, (0 < z)%Z -> (z <= 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (- z)) = (2^64 - z)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros z Hz0 Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  replace (- z)%Z with ((2^64 - z) + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_neg_S : forall d : nat,
  v_addi (Z_to_bv 64 (- Z.of_nat (S d))) 1 = Z_to_bv 64 (- Z.of_nat d).
Proof. LiaFast.lf_pins LiaFast.u0.
  intro d. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bsb_bound : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
  valid_argv a -> valid_envp e ->
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) <= 2240000)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ph sp a e uid hw rnd Hva Hve.
  pose proof (build_stack_bytes_within_span ph sp a e uid hw rnd).
  pose proof (entry_stack_span_bound a e Hva Hve).
  unfold entry_stack_span_max in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_avoids_two : forall (s0 s1 : Segment) (a n : Z),
  Z.ltb a (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) = false ->
  Z.ltb a (Z.of_N (seg_base s1) + Z.of_N (seg_size s1)) = false ->
  range_avoids_ro_segs [s0; s1] a n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s0 s1 a n H0 H1. unfold range_avoids_ro_segs. cbn [forallb].
  rewrite H0, H1. rewrite !andb_false_r. cbn [negb]. rewrite !orb_true_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

#[using="Type"] Lemma range_avoids_ro_above : forall (segs : list Segment) (data_base addr n : Z),
  ro_segs_below segs data_base = true ->
  (data_base <= addr)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros segs data_base addr n Hbelow Haddr.
  unfold ro_segs_below in Hbelow. unfold range_avoids_ro_segs.
  rewrite forallb_forall in *. intros seg Hin.
  specialize (Hbelow seg Hin).
  destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
  apply Z.leb_le in Hbelow.
  apply negb_true_iff. apply andb_false_iff. right.
  apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00152513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00152513 : bv 32) (OpImm ALU_SLT 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40155513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40155513 : bv 32) (ShiftImm ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B57533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B57533 : bv 32) (Op ALU_AND 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B56533 : bv 32) (Op ALU_OR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B54533 : bv 32) (Op ALU_XOR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B51533 : bv 32) (Op ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B55533 : bv 32) (Op ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B55533 : bv 32) (Op ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B52533 : bv 32) (Op ALU_SLT 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B53533 : bv 32) (Op ALU_SLTU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5053B : bv 32) (Op32 ALU_ADD 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5153B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5153B : bv 32) (Op32 ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5553B : bv 32) (Op32 ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B5553B : bv 32) (Op32 ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015051B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015051B : bv 32) (OpImm32 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015151B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015151B : bv 32) (ShiftImm32 ALU_SLL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015551B : bv 32) (ShiftImm32 ALU_SRL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x4015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x4015551B : bv 32) (ShiftImm32 ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B51533 : bv 32) (Mul M_MULH 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B52533 : bv 32) (Mul M_MULHSU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B53533 : bv 32) (Mul M_MULHU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B54533 : bv 32) (Mul M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B56533 : bv 32) (Mul M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5053B : bv 32) (Mul32 M_MUL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5453B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5453B : bv 32) (Mul32 M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5553B : bv 32) (Mul32 M_DIVU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5653B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5653B : bv 32) (Mul32 M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5753B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5753B : bv 32) (Mul32 M_REMU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B55533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B55533 : bv 32)
                = Some (Mul M_DIVU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B57533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B57533 : bv 32)
                = Some (Mul M_REMU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00151513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00151513 : bv 32)
                = Some (ShiftImm ALU_SLL 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00157513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00157513 : bv 32)
                = Some (OpImm ALU_AND 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_andi (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A13023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A13023 : bv 32)
                = Some (Store SZ8 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A12023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 4%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A12023 : bv 32)
                = Some (Store SZ4 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A11023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 2%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A11023 : bv 32)
                = Some (Store SZ2 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A10023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 1%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A10023 : bv 32)
                = Some (Store SZ1 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0080006F : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x0080006F : bv 32)
                = Some (Jal 0 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x008000EF : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x008000EF : bv 32)
                = Some (Jal 1 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00008067 : bv 32) ->
    getr regs 1 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x00008067 : bv 32)
                = Some (Jalr 0 1 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x000500E7 : bv 32) ->
    getr regs 10 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x000500E7 : bv 32)
                = Some (Jalr 1 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

End DispatchSmoke.
End WithFP33.
