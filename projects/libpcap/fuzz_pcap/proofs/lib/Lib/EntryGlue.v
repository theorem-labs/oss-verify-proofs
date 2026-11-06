(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance entryglue_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Glue.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma regs_ok_ext_getr : forall E sr R R',
  regs_ok E sr R -> (forall r : reg, getr R' r = getr R r) -> regs_ok E sr R'.
Proof. intros E sr R R' HR Heq r. rewrite Heq. apply HR. Qed.

#[using="Type"] Lemma bv_eqb_false_of_ne : forall (r : reg), r <> 0%bv -> bv_eqb r 0%bv = false.
Proof. intros r Hr. unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hr. apply bv_eq. exact Hc. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_upd1 : forall E sr R R' (ra : reg) ea,
  regs_ok E sr R -> ra <> 0%bv ->
  getr R' ra = edenot E ea ->
  (forall r : reg, r <> ra -> getr R' r = getr R r) ->
  regs_ok E (sr_upd sr (ridx ra) ea) R'.
Proof.
  intros E sr R R' ra ea HR Ha Hva Hother.
  apply (regs_ok_ext_getr E _ (regupd R ra (edenot E ea))).
  - apply regs_ok_set; [exact HR | exact Ha | reflexivity].
  - intros r. destruct (bv_eq_dec _ r ra) as [->|Hne].
    + rewrite getr_same by exact Ha. exact Hva.
    + rewrite getr_other by exact Hne. apply Hother. exact Hne.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_upd2 : forall E sr R R' (ra rb : reg) ea eb,
  regs_ok E sr R -> ra <> 0%bv -> rb <> 0%bv -> ra <> rb ->
  getr R' ra = edenot E ea -> getr R' rb = edenot E eb ->
  (forall r : reg, r <> ra -> r <> rb -> getr R' r = getr R r) ->
  regs_ok E (sr_upd (sr_upd sr (ridx ra) ea) (ridx rb) eb) R'.
Proof.
  intros E sr R R' ra rb ea eb HR Ha Hb Hab Hva Hvb Hother.
  apply (regs_ok_ext_getr E _ (regupd (regupd R ra (edenot E ea)) rb (edenot E eb))).
  - apply regs_ok_set; [| exact Hb | reflexivity]. apply regs_ok_set; [exact HR | exact Ha | reflexivity].
  - intros r. destruct (bv_eq_dec _ r rb) as [->|Hne].
    + rewrite getr_same by exact Hb. exact Hvb.
    + rewrite getr_other by exact Hne. destruct (bv_eq_dec _ r ra) as [->|Hne2].
      * rewrite getr_same by exact Ha. exact Hva.
      * rewrite getr_other by exact Hne2. apply Hother; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kn_sub (small big : list kentry) : bool :=
  forallb (fun K => existsb (AP.kentry_eqb K) big) small.

#[using="Type"] Lemma know_ok_sub : forall E M small big,
  kn_sub small big = true -> know_ok segs E M big -> know_ok segs E M small.
Proof.
  intros E M small big Hs HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
  unfold kn_sub in Hs. pose proof (proj1 (forallb_forall _ _) Hs K Hin) as HsK.
  apply existsb_exists in HsK as (K' & Hin' & Heq). apply KNA.kentry_eqb_eq in Heq. subst K'.
  exact (proj1 (Forall_forall _ _) HK K Hin').
Qed.

#[using="Type"] Lemma know_ok_app_intro : forall E M k1 k2,
  know_ok segs E M k1 -> know_ok segs E M k2 -> know_ok segs E M (k1 ++ k2).
Proof. intros. unfold know_ok in *. apply Forall_app. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_apart_keep : forall E M M' kn ub uk un,
  know_ok segs E M kn ->
  (forall x : word, bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x ->
                    M' x = M x) ->
  know_ok segs E M' (List.filter (AP.kentry_apart_b kn ub uk un) kn).
Proof.
  intros E M M' kn ub uk un HK Hout.
  eapply KNA.know_ok_filter_apart; [exact HK | | exact Hout].
  intros K _ Hb. left. exact Hb.
Qed.

(* [comment removed for export] *)
Definition keep_b (kn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  AP.kwr_b K || AP.kentry_apart_b kn ub uk un K.

#[using="Type"] Lemma kwr_grows : forall E M M' a n,
  mem_grows M M' -> kentry_ok segs E M (KWr a n) -> kentry_ok segs E M' (KWr a n).
Proof.
  intros E M M' a n Hg [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
  intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
Qed.

#[using="Type"] Lemma know_change_keep : forall E M M' kn ub uk un,
  know_ok segs E M kn ->
  (forall x : word, bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + elenZ E un <= bv_unsigned x ->
                    M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M' (List.filter (keep_b kn ub uk un) kn).
Proof.
  intros E M M' kn ub uk un HK Hout Hg.
  eapply KNA.know_ok_filter_apart; [exact HK | | exact Hout].
  intros K Hin Hb. unfold keep_b in Hb. apply orb_prop in Hb as [Hw | Hb]; [right | left; exact Hb].
  destruct K; cbn in Hw; try discriminate.
  eapply kwr_grows; [exact Hg|]. exact (proj1 (Forall_forall _ _) HK _ Hin).
Qed.

(* [comment removed for export] *)
Definition is_pure_fact (K : kentry) : bool :=
  match K with KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true | _ => false end.

#[using="Type"] Lemma pure_fact_any_mem : forall E M M' K,
  is_pure_fact K = true -> kentry_ok segs E M K -> kentry_ok segs E M' K.
Proof. intros E M M' K Hp HK. destruct K; cbn in Hp; try discriminate; exact HK. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_below_b (spi : nat) (lows : list (expr * Z)) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ =>
      match b with
      | EVar i => if Nat.eqb i spi then Z.leb (k + Z.of_nat w) 0 && Z.leb (- 2 ^ 40) k
                  else existsb (fun p => expr_eqb (fst p) b && Z.leb 0 k && Z.leb (k + Z.of_nat w) (snd p)) lows
      | ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb (k + Z.of_nat w) (2 ^ 40)
      | _ => existsb (fun p => expr_eqb (fst p) b && Z.leb 0 k && Z.leb (k + Z.of_nat w) (snd p)) lows
      end
  end.

Definition log_below_b (spi : nat) (lows : list (expr * Z)) (log : list sentry) : bool :=
  forallb (entry_below_b spi lows) log.

Definition lows_ok (E : env) (bound : Z) (lows : list (expr * Z)) : Prop :=
  Forall (fun p => 0 <= snd p /\ bv_unsigned (edenot E (fst p)) + snd p <= bound) lows.

#[using="Type"] Lemma existsb_lows : forall E bound lows b k w,
  lows_ok E bound lows ->
  existsb (fun p => expr_eqb (fst p) b && Z.leb 0 k && Z.leb (k + Z.of_nat w) (snd p)) lows = true ->
  0 <= k /\ bv_unsigned (edenot E b) + k + Z.of_nat w <= bound.
Proof.
  intros E bound lows b k w Hl Hex.
  apply existsb_exists in Hex as (p & Hin & Hp).
  apply andb_prop in Hp as [Hp H3]. apply andb_prop in Hp as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (proj1 (Forall_forall _ _) Hl p Hin) as [A B]. subst b. lia.
Qed.

#[using="Type"] Lemma mem_denot_above : forall E M log spi lows bound (x : word),
  log_below_b spi lows log = true ->
  2 ^ 41 <= bv_unsigned (ev E spi) -> bv_unsigned (ev E spi) <= bound -> bound <= 2 ^ 64 - 2 ^ 41 ->
  lows_ok E bound lows ->
  bound <= bv_unsigned x ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi lows bound x Hb S1 S2 S3 Hl Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_below_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_below_b] in He. cbn [mem_denot].
  pose proof (u64_range x) as Hxr. pose proof (u64_range (edenot E b)) as Hbr.
  assert (G : 0 <= bv_unsigned (edenot E b) + k /\ bv_unsigned (edenot E b) + k + Z.of_nat w <= bound).
  { destruct b as [z|i| | | | | |];
      try (destruct (existsb_lows E bound lows _ k w Hl He); lia).
    - apply andb_prop in He as [He H3]. apply andb_prop in He as [H1 H2].
      apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst z.
      cbn [edenot]. rewrite u_small by lia. lia.
    - destruct (Nat.eqb i spi) eqn:Ei.
      + apply Nat.eqb_eq in Ei. subst i. apply andb_prop in He as [H1 H2].
        apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [edenot]. lia.
      + destruct (existsb_lows E bound lows _ k w Hl He). lia. }
  rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. right. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma zfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x [H1 H2]. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.

#[using="Type"] Lemma zfill_grows : forall (a n : word) m, mem_grows m (zfill a n m).
Proof. intros a n m x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kzero_zfill : forall E M (e : expr) (a : word) (n : Z),
  edenot E e = a -> 0 < n < 2 ^ 64 -> bv_unsigned a + n <= 2 ^ 64 ->
  kentry_ok segs E (zfill a (Z_to_bv 64 n) M) (KZero (SA e 0) (ELit n)).
Proof.
  intros E M e a n He Hn Hnw. pose proof (u64_range a).
  apply (kzero_intro segs E _ e a 0 (ELit n) n He); cbn [edenot]; rewrite ?u_small by lia; try lia.
  intros i Hi. apply zfill_in. rewrite !u_small by lia. lia.
Qed.

#[using="Type"] Lemma kwr_zfill : forall E M (e : expr) (a : word) (n : Z),
  edenot E e = a -> 0 < n < 2 ^ 64 -> bv_unsigned a + n <= 2 ^ 64 ->
  kentry_ok segs E (zfill a (Z_to_bv 64 n) M) (KWr (SA e 0) (ELit n)).
Proof.
  intros E M e a n He Hn Hnw. pose proof (u64_range a).
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He, !u_small by lia.
  split; [lia|]. intros d m Hd Hdm. unfold zfill.
  destruct m as [|m]; [reflexivity|]. apply store_ok_zmem; rewrite !u_small by lia; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kunk_grows : forall E M M' a n,
  mem_grows M M' -> kentry_ok segs E M (KUnk a n) -> kentry_ok segs E M' (KUnk a n).
Proof.
  intros E M M' a n Hg [Hfl Hd]. cbn [kentry_ok]. split; [exact Hfl|].
  intros i Hi. apply Hg. apply Hd. exact Hi.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kunk_of_kzero : forall E M a n,
  kentry_ok segs E M (KZero a n) -> kentry_ok segs E M (KUnk a n).
Proof.
  intros E M a n [Hfl Hz]. cbn [kentry_ok]. split; [exact Hfl|].
  intros i Hi. rewrite (Hz i Hi). discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma star_msteps : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  star_cfg segs CFG (mkCfg ms model) [] (mkCfg ms' model).
Proof. intros. apply star_cfg_msteps; assumption. Qed.

#[using="Type"] Lemma star_trans_nil : forall c1 c2 c3,
  star_cfg segs CFG c1 [] c2 -> star_cfg segs CFG c2 [] c3 -> star_cfg segs CFG c1 [] c3.
Proof. intros c1 c2 c3 H1 H2. exact (star_cfg_trans segs c1 [] c2 [] c3 H1 H2). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_ecall : forall regs (pc : word) mem rom model w,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) [] (mkCfg (epend regs pc mem rom (getr regs 17)) model).
Proof.
  intros regs pc mem rom model w Hh Hlazy HF HE.
  apply star_cfg_one. apply (sstep_cfg_instr segs CFG _ model _ model Hh); [reflexivity|].
  rewrite (mi_account_step_no_lazy segs _ model Hlazy).
  (* [comment removed for export] *)
  replace (RiscvSemantics.step segs (mkst regs pc mem rom)) with (MachineOk (epend regs pc mem rom (getr regs 17)))
    by (symmetry; eapply step_ecall_epend; eassumption).
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_mmap_grant : forall regs (pc : word) mem rom model w (len : Z) (a : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  grant_ok (getr regs 10) model a (page_round_up_Z len) = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
              (mmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)).
Proof.
  intros regs pc mem rom model w len a HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hg.
  eapply star_trans_nil; [eapply star_ecall; eassumption|].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u_small. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u_small in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  replace (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
    with (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]))).
  2:{ rewrite Hpr. unfold ms, epend. rewrite adv_mmap_grant. reflexivity. }
  rewrite <- Hpr.
  apply star_cfg_one.
  apply (sstep_cfg_syscall segs CFG ms model (getr regs 17) (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
           (mmap_model a (page_round_up (ms_gpr ms 1)) model) (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
  - exact Hh.
  - reflexivity.
  - apply mmap_succ_ok; [rewrite H17; apply u_small; lia | exact Hargs | rewrite H0, Hu1; exact Hg].
  - (* [comment removed for export] *)
    apply spurious_refusal_not_refusal. cbn [eff_ret].
    apply (grant_not_refusal segs ms (getr regs 17) model a (page_round_up_Z len) (getr regs 10));
      [rewrite H17; apply u_small; lia | apply pruZ_nonneg; lia | rewrite <- H0; exact Hg].
  - rewrite mmap_model_halted. exact Hh.
  - apply materialize_model_accesses_no_lazy. exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_set_tid : forall regs (pc : word) mem rom model w (t : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 -> m_tid model = None ->
  0 < bv_unsigned t < PID_MAX_ENVELOPE ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 t) (v_addi pc 4) mem rom) (with_tid t model)).
Proof.
  intros regs pc mem rom model w t HF HE Hh Hlazy H17 Htid Ht.
  eapply star_trans_nil; [eapply star_ecall; eassumption|].
  pose proof (node_set_tid segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) Hh Hlazy eq_refl
                ltac:(rewrite H17; apply u_small; lia) Htid) as [Hn _].
  specialize (Hn (exist _ t Ht)). cbn [proj1_sig] in Hn. rewrite adv_set_epend in Hn.
  apply star_cfg_one. apply sstep_cfg_of_unfiltered; [eapply unfiltered_sysno; [apply epend_svc | rewrite H17; reflexivity]|]. exact Hn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition readable (m : word -> option byte) (x : word) : Prop :=
  match m x with Some _ => True | None => seg_rom segs x <> None end.

#[using="Type"] Lemma readable_grows : forall m m' x, mem_grows m m' -> readable m x -> readable m' x.
Proof.
  intros m m' x Hg Hr. unfold readable in *.
  destruct (m x) as [b|] eqn:Em.
  - assert (H : m' x <> None) by (apply Hg; rewrite Em; discriminate). destruct (m' x); [exact I | congruence].
  - destruct (m' x); [exact I | exact Hr].
Qed.

#[using="Type"] Lemma readable_wbytes_in : forall m (a : word) bs (x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  readable (wbytes m a bs) x.
Proof. intros m a bs x Hnw Hx. unfold readable. rewrite wbytes_inside by assumption. exact I. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_readable : forall m n (a : word),
  bv_unsigned a + Z.of_nat n < 2 ^ 64 ->
  (forall j, (j < n)%nat -> readable m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Hnw Hr.
  - exists []. split; reflexivity.
  - pose proof (u64_range a) as Ha.
    assert (H0 : readable m a).
    { specialize (Hr 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in Hr. exact Hr. }
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    destruct (IH (a + 1)%bv ltac:(rewrite Hu1; lia)) as (bs & Hbs & Hlen).
    { intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      apply Hr. lia. }
    cbn [rdn]. unfold readable in H0.
    destruct (m a) as [b|].
    + rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
    + destruct (seg_rom segs a) as [b|]; [|congruence]. rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma readable_of_rdn : forall m n (a : word) bs,
  rdn segs m a n = Some bs -> bv_unsigned a + Z.of_nat n < 2 ^ 64 ->
  forall j, (j < n)%nat -> readable m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
Proof.
  intros m n. induction n as [|n IH]; intros a bs Hrd Hnw j Hj; [lia|].
  pose proof (u64_range a) as Ha.
  cbn [rdn] in Hrd.
  assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
  destruct j as [|j].
  - rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. unfold readable.
    destruct (m a); [exact I|]. destruct (seg_rom segs a); [discriminate | discriminate].
  - replace (bv_unsigned a + Z.of_nat (S j)) with (bv_unsigned (a + 1)%bv + Z.of_nat j) by (rewrite Hu1; lia).
    destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
    destruct (rdn segs m (a + 1)%bv n) as [r|] eqn:Er; [|discriminate].
    eapply IH; [exact Er | rewrite Hu1; lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_misses_b (spi : nat) (splo a n : Z) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ =>
      match b with
      | EVar i => Nat.eqb i spi && Z.leb splo k && Z.leb (k + Z.of_nat w) (2 ^ 40)
      | ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb (k + Z.of_nat w) (2 ^ 40)
                  && (Z.leb (k + Z.of_nat w) a || Z.leb (a + n) k)
      | _ => false
      end
  end.

Definition log_misses_b (spi : nat) (splo a n : Z) (log : list sentry) : bool :=
  forallb (entry_misses_b spi splo a n) log.

#[using="Type"] Lemma mem_denot_misses : forall E M log spi splo a n x,
  log_misses_b spi splo a n log = true ->
  2 ^ 41 <= bv_unsigned (ev E spi) -> bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64 -> - 2 ^ 40 <= splo ->
  0 <= a -> a + n <= 2 ^ 40 ->
  a <= x < a + n ->
  mem_denot E M log (Z_to_bv 64 x) = M (Z_to_bv 64 x).
Proof.
  intros E M log spi splo a n x Hb S1 S2 S3 A1 A2 Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_misses_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_misses_b] in He. cbn [mem_denot].
  assert (Hux : bv_unsigned (Z_to_bv 64 x) = x) by (apply u_small; lia).
  destruct b as [z|i| | | | | |]; try discriminate.
  - apply andb_prop in He as [He Hap]. apply andb_prop in He as [He Hw]. apply andb_prop in He as [Hz Hk].
    apply Z.eqb_eq in Hz. apply Z.leb_le in Hk. apply Z.leb_le in Hw. subst z.
    rewrite wbytes_outside.
    + apply IH. exact Hrest.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite !u_small by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite !u_small by lia.
      apply orb_prop in Hap as [Hap|Hap]; apply Z.leb_le in Hap; lia.
  - apply andb_prop in He as [He Hw]. apply andb_prop in He as [Hi Hk].
    apply Nat.eqb_eq in Hi. subst i. apply Z.leb_le in Hk. apply Z.leb_le in Hw.
    rewrite wbytes_outside.
    + apply IH. exact Hrest.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite !u_small by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite !u_small by lia. left. lia.
Qed.

(* [comment removed for export] *)
Fixpoint log_abs (log : list sentry) : list (Z * Z) :=
  match log with
  | [] => []
  | SE (SA (ELit _) k) w _ :: rest => (k, Z.of_nat w) :: log_abs rest
  | _ :: rest => log_abs rest
  end.

Definition entry_stack_or_abs_b (spi : nat) (splo : Z) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ =>
      match b with
      | EVar i => Nat.eqb i spi && Z.leb splo k && Z.leb (k + Z.of_nat w) (2 ^ 40)
      | ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb (k + Z.of_nat w) (2 ^ 40)
      | _ => false
      end
  end.

Definition log_frame_b (spi : nat) (splo : Z) (log : list sentry) : bool :=
  forallb (entry_stack_or_abs_b spi splo) log.

#[using="Type"] Lemma mem_denot_frame : forall E M log spi splo (x : word),
  log_frame_b spi splo log = true ->
  2 ^ 41 <= bv_unsigned (ev E spi) -> bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64 -> - 2 ^ 40 <= splo ->
  bv_unsigned x < bv_unsigned (ev E spi) + splo ->
  Forall (fun p => bv_unsigned x < fst p \/ fst p + snd p <= bv_unsigned x) (log_abs log) ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi splo x Hb S1 S2 S3 Hx Habs.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_frame_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_stack_or_abs_b] in He. cbn [mem_denot]. pose proof (u64_range x) as Ux.
  destruct b as [z|i| | | | | |]; try discriminate.
  - apply andb_prop in He as [He Hw]. apply andb_prop in He as [Hz Hk].
    apply Z.eqb_eq in Hz. apply Z.leb_le in Hk. apply Z.leb_le in Hw. subst z.
    cbn [log_abs] in Habs. apply Forall_cons_iff in Habs as [Hap Habs]. cbn [fst snd] in Hap.
    rewrite wbytes_outside.
    + apply IH; [exact Hrest | exact Habs].
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite !u_small by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite !u_small by lia. lia.
  - apply andb_prop in He as [He Hw]. apply andb_prop in He as [Hi Hk].
    apply Nat.eqb_eq in Hi. subst i. apply Z.leb_le in Hk. apply Z.leb_le in Hw.
    assert (Habs' : Forall (fun p : Z * Z => bv_unsigned x < fst p \/ fst p + snd p <= bv_unsigned x) (log_abs rest)).
    { cbn [log_abs] in Habs. exact Habs. }
    rewrite wbytes_outside.
    + apply IH; [exact Hrest | exact Habs'].
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite !u_small by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite !u_small by lia. left. lia.
Qed.

End Glue.
