(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2S.
#[local] Instance stdiosymdrive_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition blobs_ev (bl : list (list byte)) : nat -> list byte := fun n => nth n bl [].
Definition ENV (vals : list word) (blobs : list (list byte)) : env := Env (vals_ev vals) (blobs_ev blobs).

Section Drive.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem rz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ms_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  exists R', regs_ok E (s_regs ss') R' /\ know_ok segs E (mem_denot E M (s_log ss')) kn'
    /\ msteps segs (mkst R (Z_to_bv 64 pc) M rom)
                   (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E M (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R Hex Hc HR HK Hsc Hsc2.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  exists R'. split; [exact HR'|]. split; [|exact Hms]. eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma know_nth : forall E M kn i K,
  know_ok segs E M kn -> nth_error kn i = Some K -> kentry_ok segs E M K.
Proof.
  intros E M kn i K HK Hn. unfold know_ok in HK.
  apply (proj1 (Forall_forall _ _) HK K). eapply nth_error_In. exact Hn.
Qed.

#[using="Type"] Lemma know_ok_app : forall E M k1 k2,
  know_ok segs E M (k1 ++ k2) <-> know_ok segs E M k1 /\ know_ok segs E M k2.
Proof. intros. unfold know_ok. apply Forall_app. Qed.

#[using="Type"] Lemma know_ok_cons : forall E M K kn,
  kentry_ok segs E M K -> know_ok segs E M kn -> know_ok segs E M (K :: kn).
Proof. intros. constructor; assumption. Qed.

(* [comment removed for export] *)
Definition kread (kn : list kentry) (b : expr) (k : Z) (n : nat) : option expr :=
  match know_lookup segs kn b k n false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

#[using="Type"] Lemma kread_sound : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  exists bs, rdn segs M (adenot E (SA b k)) n = Some bs /\ length bs = n
             /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
  pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
  destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection Hr as ->.
  destruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.

#[using="Type"] Lemma word_to_le_bytes_of_lez : forall n bs,
  length bs = n -> (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros n bs Hl Hn. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kread_rdn : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  rdn segs M (adenot E (SA b k)) n = Some (word_to_le_bytes n (edenot E v)).
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
  destruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
  rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint kblob_find (kn : list kentry) (b : expr) (k : Z) : option (expr * nat) :=
  match kn with
  | [] => None
  | KBlob (SA kb kk) len bk :: rest =>
      if (expr_eqb b kb && Z.eqb k kk)%bool then Some (len, bk) else kblob_find rest b k
  | _ :: rest => kblob_find rest b k
  end.

#[using="Type"] Lemma kblob_find_sound : forall E M kn b k len bk,
  know_ok segs E M kn -> kblob_find kn b k = Some (len, bk) ->
  kentry_ok segs E M (KBlob (SA b k) len bk).
Proof.
  intros E M kn b k len bk Hkn. induction kn as [|K rest IH]; cbn [kblob_find]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [| |[kb kk] len' bk'| | | | | | |]; try (apply IH; assumption).
  destruct (expr_eqb b kb && Z.eqb k kk)%bool eqn:Heq; [|apply IH; assumption].
  apply andb_prop in Heq as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst.
  injection H as <- <-. exact HK.
Qed.

#[using="Type"] Lemma kblob_rdn : forall E M kn b k len bk,
  know_ok segs E M kn -> kblob_find kn b k = Some (len, bk) ->
  rdn segs M (adenot E (SA b k)) (length (eb E bk)) = Some (eb E bk).
Proof.
  intros E M kn b k len bk Hkn Hf.
  pose proof (kblob_find_sound E M kn b k len bk Hkn Hf) as HK. cbn [kentry_ok] in HK.
  destruct HK as (Hfl & Hlen & Hb).
  apply rdn_pointwise.
  - reflexivity.
  - rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
  - intros j Hj. rewrite (flat_u E _ _ Hfl). rewrite Hb by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_agree : forall M M' n (a : word),
  (forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = M' (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  rdn segs M a n = rdn segs M' a n.
Proof.
  intros M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn].
  pose proof (Hag 0%nat ltac:(lia)) as H0.
  rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|].
  intros j Hj. rewrite w_add_1.
  pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
  - rewrite u_small by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
    apply Hag. lia.
  - replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
      by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    specialize (Hag (S j) ltac:(lia)).
    replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
    replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.

#[using="Type"] Lemma rdn_untouched : forall M (a : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) = None) ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros M a n H0 Hnw Hnone. apply rdn_agree. intros j Hj.
  rewrite u_small by lia. rewrite Hnone by lia. reflexivity.
Qed.

#[using="Type"] Lemma kimg_rdn : forall E M kn i lo hi (a : Z) n,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros E M kn i lo hi a n HK Hn Hlo Hhi.
  pose proof (know_nth E M kn i _ HK Hn) as (H0 & H64 & Hnone).
  apply rdn_untouched; [lia | lia |]. intros j Hj. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kwr_store_ok : forall E M kn i b kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA b kk) (ELit len)) -> (0 <= len < 2 ^ 64)%Z ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z ->
  store_ok segs M (adenot E (SA b k)) m = true.
Proof.
  intros E M kn i b kk len k m HK Hn Hlen H1 H2.
  pose proof (know_nth E M kn i _ HK Hn) as (Hfl & Hst).
  unfold adenot. cbn [a_base a_off].
  unfold elenZ in *. cbn [edenot] in *. rewrite u_small in Hfl, Hst by lia.
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
  specialize (Hst (k - kk)%Z m ltac:(lia) ltac:(lia)).
  replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
  unfold v_addi. exact Hst.
Qed.

#[using="Type"] Lemma kwr_store_ok_lit : forall E M kn i kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA (ELit 0) kk) (ELit len)) -> (0 <= len < 2 ^ 64)%Z ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z -> (0 <= k < 2 ^ 64)%Z ->
  store_ok segs M (Z_to_bv 64 k) m = true.
Proof.
  intros E M kn i kk len k m HK Hn Hlen H1 H2 Hk.
  pose proof (kwr_store_ok E M kn i (ELit 0) kk len k m HK Hn Hlen H1 H2) as H.
  unfold adenot, v_addi in H. cbn [a_base a_off edenot] in H.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H. rewrite Z.add_0_l in H. exact H.
Qed.

#[using="Type"] Lemma krange_of_know : forall E M kn i e lo hi,
  know_ok segs E M kn -> nth_error kn i = Some (KRange e lo hi) ->
  (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros E M kn i e lo hi HK Hn.
  pose proof (know_nth E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma vals_ev_app_l : forall vals extra n, (n < length vals)%nat ->
  vals_ev (vals ++ extra) n = vals_ev vals n.
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.

#[using="Type"] Lemma vals_ev_app_r : forall vals extra n,
  vals_ev (vals ++ extra) (length vals + n) = vals_ev extra n.
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.

#[using="Type"] Lemma env_app_know : forall vals extra ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ extra)) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

#[using="Type"] Lemma env_app_regs : forall vals extra ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ extra)) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

#[using="Type"] Lemma env_app_edenot : forall vals extra ebs e,
  expr_vars_lt (length vals) e = true ->
  edenot (Env (vals_ev (vals ++ extra)) ebs) e = edenot (Env (vals_ev vals) ebs) e.
Proof. intros. symmetry. eapply edenot_agree; [apply vals_app_agree | assumption]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_pc4 : forall pc, (0 <= pc)%Z -> (pc + 4 < 2 ^ 64)%Z ->
  v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof. intros pc H0 H1. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_set_a0 : forall E sr R v e,
  regs_ok E sr R -> edenot E e = v -> regs_ok E (sr_upd sr (ridx 10) e) (regupd R 10 v).
Proof. intros. apply regs_ok_set; [assumption | discriminate | assumption]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_pin : forall E sr R (r : reg) e,
  regs_ok E sr R -> r <> 0%bv -> getr R r = edenot E e ->
  regs_ok E (sr_upd sr (ridx r) e) R.
Proof.
  intros E sr R r e HR Hr He.
  pose proof (regs_ok_upd E sr R r (getr R r) e HR (eq_sym He)) as H.
  assert (Hb : bv_eqb r 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hr. apply bv_eq. exact Hc. }
  rewrite Hb in H. intros r0. rewrite <- (H r0).
  destruct (bv_eq_dec _ r0 r) as [->|Hne]; [rewrite getr_same by exact Hr; reflexivity | rewrite getr_other by exact Hne; reflexivity].
Qed.

(* [comment removed for export] *)
Definition junk_vals (R' : bvmap 5 word) : list word :=
  map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).

Definition sr_after_call_j (sr : list expr) (kept : list nat) (jbase : nat) : list expr :=
  map (fun i => if existsb (Nat.eqb i) kept then nth i sr (ELit 0) else EVar (jbase + i))
      (seq 0 32).

#[using="Type"] Lemma junk_vals_length : forall R, length (junk_vals R) = 32%nat.
Proof. intros R. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

#[using="Type"] Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
  nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
  intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
  cbn [seq map]. destruct n as [|n].
  - cbn [nth]. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
  nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.

#[using="Type"] Lemma sr_vars_lt_nth : forall b sr n, sr_vars_lt b sr = true -> expr_vars_lt b (nth n sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
  cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.

#[using="Type"] Lemma regs_after_call : forall vals ebs sr R R' kept,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall i, In i kept -> (i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i))) ->
  ~ In 0%nat kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_after_call_j sr kept (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hkept H0 r.
  pose proof (ridx_range r) as Hr.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
    destruct (existsb (Nat.eqb (ridx r)) kept) eqn:Hex.
    + apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
      destruct (Hkept _ Hin) as [_ Hg]. rewrite ridx_roundtrip in Hg. rewrite Hg.
      pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
      eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
    + cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
      replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
      unfold junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_after_keeps : forall vals ebs sr R R' (kept : list reg),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r kept -> getr R' r = getr R r) ->
  ~ In 0%bv kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs)
          (sr_after_call_j sr (map ridx kept) (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hk H0.
  apply (regs_after_call vals ebs sr R R' (map ridx kept) Hlt HR).
  - intros i Hi. apply in_map_iff in Hi as (r & <- & Hr). split; [apply ridx_range|].
    rewrite ridx_roundtrip. apply Hk. exact Hr.
  - intros Hin. apply in_map_iff in Hin as (r & Hr0 & Hr). apply H0.
    replace 0%bv with r; [exact Hr|]. apply ridx_inj. rewrite Hr0. reflexivity.
Qed.

#[using="Type"] Lemma callee_kept_no0 : ~ In (0%bv : reg) callee_kept.
Proof.
  unfold callee_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

#[using="Type"] Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_junk : forall regs extra ebs,
  regs_ok (Env (vals_ev (junk_vals regs ++ extra)) ebs) sr_id regs.
Proof.
  intros regs extra ebs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hr.
    replace (nth (ridx r) sr_id (ELit 0)) with (EVar (ridx r)).
    2:{ unfold sr_id. generalize (ridx r) Hr. intros n Hn. do 32 (destruct n as [|n]; [reflexivity|]). lia. }
    cbn [edenot ev]. rewrite vals_ev_app_l by (rewrite junk_vals_length; exact Hr).
    unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

#[using="Type"] Lemma ev_junk_reg : forall regs extra ebs (r : reg),
  ev (Env (vals_ev (junk_vals regs ++ extra)) ebs) (ridx r) = getr regs r.
Proof.
  intros regs extra ebs r. cbn [ev]. pose proof (ridx_range r) as Hr.
  rewrite vals_ev_app_l by (rewrite junk_vals_length; exact Hr).
  unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

#[using="Type"] Lemma ev_junk_extra : forall regs extra ebs i,
  ev (Env (vals_ev (junk_vals regs ++ extra)) ebs) (32 + i)%nat = nth i extra (Z_to_bv 64 0).
Proof. intros. cbn [ev]. rewrite <- (junk_vals_length regs) at 1. apply vals_ev_app_r. Qed.

#[using="Type"] Lemma reg_ne0 : forall r : reg, bv_unsigned r <> 0%Z -> r <> 0%bv.
Proof. intros r H Hc. apply H. rewrite Hc. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_ext : forall E sr sr' R,
  length sr = length sr' ->
  (forall i, (i < length sr)%nat -> edenot E (nth i sr (ELit 0)) = edenot E (nth i sr' (ELit 0))) ->
  regs_ok E sr R -> regs_ok E sr' R.
Proof.
  intros E sr sr' R Hlen Heq HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hlt | Hge].
  - apply Heq. exact Hlt.
  - rewrite !nth_overflow by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition win_out_b (spi : nat) (lo hi ihi : Z) (b : expr) (k n : Z) : bool :=
  match b with
  | EVar i => Nat.eqb i spi && (Z.leb (k + n) lo || Z.leb hi k)
              && Z.leb (- 2 ^ 40) k && Z.leb (k + n) (2 ^ 40) && Z.leb 0 n
  | ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb 0 n && Z.leb (k + n) ihi
  | _ => false
  end.

(* [comment removed for export] *)
Definition win_ok (E : env) (spi : nat) (lo hi ihi : Z) : Prop :=
  (2 ^ 41 <= bv_unsigned (ev E spi))%Z /\ (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z
  /\ (lo <= hi)%Z /\ (- 2 ^ 40 <= lo)%Z /\ (hi <= 2 ^ 40)%Z
  /\ (0 <= ihi)%Z /\ (ihi <= bv_unsigned (ev E spi) + lo)%Z.

#[using="Type"] Lemma win_out_sound : forall E spi lo hi ihi b k n,
  win_out_b spi lo hi ihi b k n = true -> win_ok E spi lo hi ihi ->
  (0 <= bv_unsigned (edenot E b) + k)%Z
  /\ (bv_unsigned (edenot E b) + k < 2 ^ 64 /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z
  /\ (0 <= n)%Z
  /\ forall x : word,
       (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n)%Z ->
       ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z.
Proof.
  intros E spi lo hi ihi b k n Hb (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Z.eqb_eq in Hb. subst z.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat split; try lia.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Nat.eqb_eq in Hb. subst i.
    repeat match goal with
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : (_ || _)%bool = true |- _ => apply orb_prop in H
           end.
    cbn [edenot]. repeat split; try lia.
Qed.

Definition entry_out_b (spi : nat) (lo hi ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
  end.

Definition log_out_b (spi : nat) (lo hi ihi : Z) (log : list sentry) : bool :=
  forallb (entry_out_b spi lo hi ihi) log.

#[using="Type"] Lemma mem_denot_out : forall E M log spi lo hi ihi (x : word),
  log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
  (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi lo hi ihi x Hb Hw Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_out_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_out_b] in He.
  destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) He Hw) as (A & B & C & D).
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
    pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
    exfalso. apply (D x); lia.
Qed.

#[using="Type"] Lemma rdn_mem_denot_out : forall E M log spi lo hi ihi (a : word) n,
  log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
  (bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned (ev E spi) + hi)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
  intros E M log spi lo hi ihi a n Hb Hw H1 H2.
  destruct Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_out E M log spi lo hi ihi); [exact Hb | repeat split; assumption |].
  rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition win_in_b (spi : nat) (lo hi : Z) (b : expr) (k n : Z) : bool :=
  match b with
  | EVar i => Nat.eqb i spi && Z.leb lo k && Z.leb (k + n) hi && Z.leb 0 n
  | _ => false
  end.

Definition entry_in_b (spi : nat) (lo hi : Z) (e : sentry) : bool :=
  match e with SE (SA b k) w _ => win_in_b spi lo hi b k (Z.of_nat w) end.

Definition log_in_b (spi : nat) (lo hi : Z) (log : list sentry) : bool :=
  forallb (entry_in_b spi lo hi) log.

#[using="Type"] Lemma mem_denot_in : forall E M log spi lo hi (x : word),
  log_in_b spi lo hi log = true ->
  (2 ^ 41 <= bv_unsigned (ev E spi))%Z -> (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z ->
  (- 2 ^ 40 <= lo)%Z -> (hi <= 2 ^ 40)%Z ->
  ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi lo hi x Hb S1 S2 L1 L2 Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_in_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_in_b] in He.
  destruct b as [z|i| | | | | |]; cbn [win_in_b] in He; try discriminate.
  repeat (apply andb_prop in He; destruct He as [He ?]). apply Nat.eqb_eq in He. subst i.
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  cbn [mem_denot]. pose proof (u64_range x).
  rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition kentry_out_b (spi : nat) (lo hi ihi : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
  | KZero (SA b k) (ELit n) => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KBlob (SA b k) (ELit n) _ => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KFill (SA b k) (ELit n) _ => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KUnk (SA b k) (ELit n) => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KImg l h => Z.leb h ihi
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr _ _ => true
  | _ => false
  end.

Definition kn_cut (spi : nat) (lo hi ihi : Z) (kn : list kentry) : list kentry :=
  List.filter (kentry_out_b spi lo hi ihi) kn.

#[using="Type"] Lemma elenZ_lit_small : forall E n, (0 <= n < 2 ^ 64)%Z -> elenZ E (ELit n) = n.
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply u_small. lia. Qed.

#[using="Type"] Lemma win_out_n0 : forall spi lo hi ihi b k n, win_out_b spi lo hi ihi b k n = true -> (0 <= n)%Z.
Proof.
  intros spi lo hi ihi b k n Hb.
  destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
    repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia.
Qed.

#[using="Type"] Lemma kentry_cut_sound : forall E M M' spi lo hi ihi K,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
  mem_grows M M' ->
  kentry_ok segs E M K -> kentry_out_b spi lo hi ihi K = true -> kentry_ok segs E M' K.
Proof.
  intros E M M' spi lo hi ihi K Hw Hag Hg HK Hb.
  pose proof Hw as Hw'. destruct Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2|[b k] n fc|[b k] n];
    cbn [kentry_out_b] in Hb; cbn [kentry_ok] in HK |- *; try exact HK.
  - (* [comment removed for export] *)
    destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
    destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb Hw) as (A & B & C & D).
    rewrite <- Hr. apply rdn_agree. intros j Hj. apply Hag.
    pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
    rewrite Hu. apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hlen & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
    split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    apply Z.leb_le in Hb. destruct HK as (H0 & H64 & Hnone).
    split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
Qed.

#[using="Type"] Theorem know_cut_sound : forall E M M' spi lo hi ihi kn,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M kn -> know_ok segs E M' (kn_cut spi lo hi ihi kn).
Proof.
  intros E M M' spi lo hi ihi kn Hw Hag Hg HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_cut spi lo hi ihi (K :: rest))
    with (if kentry_out_b spi lo hi ihi K then K :: kn_cut spi lo hi ihi rest else kn_cut spi lo hi ihi rest).
  destruct (kentry_out_b spi lo hi ihi K) eqn:Hb.
  - constructor; [|apply IH; exact HK2]. eapply kentry_cut_sound; eauto.
  - apply IH. exact HK2.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_ok_filter : forall E M (p : kentry -> bool) kn,
  know_ok segs E M kn -> know_ok segs E M (List.filter p kn).
Proof.
  intros E M p kn HK. unfold know_ok in *. apply Forall_forall. intros K HinF.
  apply filter_In in HinF as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_agree_out : forall M (a : word) bs E spi lo hi,
  (bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned (ev E spi) + hi)%Z ->
  (bv_unsigned (ev E spi) + hi <= 2 ^ 64)%Z ->
  forall x : word,
    ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
    wbytes M a bs x = M x.
Proof.
  intros M a bs E spi lo hi H1 H2 H3 x Hx. pose proof (u64_range x).
  apply wbytes_outside; [lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|G]; [left; exact L | right].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|G2]; [|exact G2].
  exfalso. apply Hx. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma know_after_store : forall E M kn sa w v bs kn' scs hs,
  carry [SE sa w v] kn [] = (kn', scs, hs) -> scs = [] ->
  know_ok segs E M kn -> (w <= 8)%nat -> flat E sa (Z.of_nat w) ->
  bs = word_to_le_bytes w (edenot E v) ->
  know_ok segs E (wbytes M (adenot E sa) bs) kn'.
Proof.
  intros E M kn sa w v bs kn' scs hs Hc -> HK Hw Hfl ->.
  change (wbytes M (adenot E sa) (word_to_le_bytes w (edenot E v))) with (mem_denot E M [SE sa w v]).
  eapply carry_after; [exact Hc | | exact HK | constructor].
  cbn [log_flat]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma Z_to_bv_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

#[using="Type"] Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.

(* [comment removed for export] *)
Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
#[using="Type"] Lemma is_ecall_ECALLW : is_ecall ECALLW = true. Proof. reflexivity. Qed.

#[using="Type"] Lemma adenot_lit0 : forall E a, adenot E (SA (ELit 0) a) = Z_to_bv 64 a.
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. reflexivity. Qed.

#[using="Type"] Lemma edenot_add_lit : forall E b k, edenot E (EAlu ALU_ADD b (ELit k)) = adenot E (SA b k).
Proof.
  intros. cbn [edenot]. rewrite alu_add. unfold adenot, v_addi, v_add. cbn [a_base a_off].
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Zplus_mod_idemp_r.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_ev_reg : forall regs rest (r : reg), reg_ev regs rest (ridx r) = getr regs r.
Proof.
  intros regs rest r. unfold reg_ev. pose proof (ridx_range r) as Hr.
  replace (Nat.ltb (ridx r) 32) with true by (symmetry; apply Nat.ltb_lt; exact Hr).
  rewrite ridx_roundtrip. reflexivity.
Qed.

End Drive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

(* [comment removed for export] *)
Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

(* [comment removed for export] *)
Ltac ms_block_with HR HK fuel stops scr NX R1 HR1 HK1 MS1 :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- context [mkst R (Z_to_bv 64 ?pc) M ?rom] =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let Hsc := fresh "Hsc" in let Hsc2 := fresh "Hsc2" in
            assert (Hsc : scs_denot segs M E scs); [split_foralls|
            assert (Hsc2 : scs_denot segs M E scs2); [split_foralls|
            destruct (ms_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R
                        ltac:(vm_cast_no_check (@eq_refl _ (ss', scs, scr')))
                        ltac:(vm_cast_no_check (@eq_refl _ (kn', scs2, hs2)))
                        HR HK Hsc Hsc2) as (R1 & HR1 & HK1 & MS1);
            clear Hsc Hsc2; cbn [s_pc s_regs s_log] in HR1, HK1, MS1]]
          end
        end
      end
    end
  end.

(* [comment removed for export] *)
Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac regv_in HR r H :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR) in H; change (sr_get sr r) with e in H;
    lazymatch e with ELit _ => cbn [edenot] in H | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac krd HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krd: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac krdv HK i k n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (EVar i) k n) in
    lazymatch r with
    | Some ?v =>
        let Hf := fresh "Hflat" in
        assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
        [ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
                          ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia) Hf) as H;
            clear Hf; cbn [edenot] in H ]
    | None => fail "krdv: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
  match kn with
  | [] => None
  | K :: r => if p K then Some i else kindex p r (S i)
  end.

Definition is_krange (e : expr) (K : kentry) : bool :=
  match K with KRange e' _ _ => expr_eqb e e' | _ => false end.
Definition is_kalign (e : expr) (K : kentry) : bool :=
  match K with KAlign e' _ => expr_eqb e e' | _ => false end.
(* [comment removed for export] *)
Definition is_kwr_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KWr (SA c kk) (ELit len) => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + len)
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kimg_cov (a n : Z) (K : kentry) : bool :=
  match K with
  | KImg lo hi => Z.leb lo a && Z.leb (a + n) hi
  | _ => false
  end.

Ltac kidx kn p :=
  let r := eval vm_compute in (kindex p kn 0) in
  lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.

(* [comment removed for export] *)
Ltac krd_solve HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krd HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ev_junk_nat : forall regs extra ebs n (r : reg),
  Z.of_nat n = bv_unsigned r ->
  AX2.ev (AX2.Env (vals_ev (junk_vals regs ++ extra)) ebs) n = getr regs r.
Proof.
  intros regs extra ebs n r Hn.
  assert (Hr : n = AX2.ridx r) by (unfold AX2.ridx; rewrite <- Hn, Nat2Z.id; reflexivity).
  rewrite Hr. apply ev_junk_reg.
Qed.

(* [comment removed for export] *)
Lemma ev_junk_xnat : forall regs extra ebs n i,
  (n = 32 + i)%nat ->
  AX2.ev (AX2.Env (vals_ev (junk_vals regs ++ extra)) ebs) n = nth i extra (Z_to_bv 64 0).
Proof. intros regs extra ebs n i ->. apply ev_junk_extra. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cut2.
Import AX2 AX2S.
Variable segs : list Segment.

Definition lit_apart (lits : list (Z * Z)) (k n : Z) : bool :=
  forallb (fun lh : Z * Z => (Z.leb (k + n) (fst lh) || Z.leb (snd lh) k)%bool) lits.

Definition in_lits (lits : list (Z * Z)) (x : Z) : Prop :=
  Exists (fun lh : Z * Z => (fst lh <= x < snd lh)%Z) lits.

#[using="Type"] Lemma lit_apart_sound : forall lits k n x,
  lit_apart lits k n = true -> (k <= x < k + n)%Z -> ~ in_lits lits x.
Proof.
  intros lits k n x H Hx Hin. unfold lit_apart in H. unfold in_lits in Hin.
  induction lits as [|[lo hi] rest IH]; [inversion Hin|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. cbn [fst snd] in H1.
  apply Exists_cons in Hin as [Hh|Ht]; [|apply IH; assumption].
  cbn [fst snd] in Hh. apply orb_prop in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.

Definition kentry_out2_b (spi : nat) (lo hi ihi : Z) (lits : list (Z * Z)) (K : kentry) : bool :=
  kentry_out_b spi lo hi ihi K &&
  match K with
  | KWord (SA (ELit z) k) w _ => lit_apart lits k (Z.of_nat w)
  | KZero (SA (ELit z) k) (ELit n) => lit_apart lits k n
  | KBlob (SA (ELit z) k) (ELit n) _ => lit_apart lits k n
  | KFill (SA (ELit z) k) (ELit n) _ => lit_apart lits k n
  | KUnk (SA (ELit z) k) (ELit n) => lit_apart lits k n
  | KImg l h => lit_apart lits l (h - l)
  | _ => true
  end.

Definition kn_cut2 (spi : nat) (lo hi ihi : Z) (lits : list (Z * Z)) (kn : list kentry) : list kentry :=
  List.filter (kentry_out2_b spi lo hi ihi lits) kn.

#[using="Type"] Lemma kentry_cut2_sound : forall E M M' spi lo hi ihi lits K,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
     ~ in_lits lits (bv_unsigned x) -> M' x = M x) ->
  Forall (fun lh => (0 <= fst lh)%Z /\ (snd lh <= ihi)%Z) lits -> (ihi <= 2 ^ 40)%Z ->
  mem_grows M M' ->
  kentry_ok segs E M K -> kentry_out2_b spi lo hi ihi lits K = true -> kentry_ok segs E M' K.
Proof.
  intros E M M' spi lo hi ihi lits K Hw Hag Hlits Hihi Hg HK Hb.
  unfold kentry_out2_b in Hb. apply andb_prop in Hb as [Hb1 Hb2].
  pose proof Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  (* [comment removed for export] *)
  assert (LITS_LOW : forall x, in_lits lits x -> (x < ihi)%Z).
  { intros x Hin. unfold in_lits in Hin. apply Exists_exists in Hin as ([l h] & Hin & Hx). cbn [fst snd] in Hx.
    apply (proj1 (Forall_forall _ _) Hlits) in Hin. cbn [fst snd] in Hin. lia. }
  assert (AG1 : forall b k n, win_out_b spi lo hi ihi b k n = true ->
            match b with ELit _ => lit_apart lits k n = true | _ => True end ->
            forall x : word, (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n)%Z -> M' x = M x).
  { intros b k n Hwo Hla x Hx.
    destruct (win_out_sound E spi lo hi ihi b k n Hwo Hw) as (A & B & C & D).
    apply Hag; [apply D; exact Hx|].
    destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hwo; try discriminate.
    - repeat (apply andb_prop in Hwo; destruct Hwo as [Hwo ?]). apply Z.eqb_eq in Hwo. subst z.
      cbn [edenot] in Hx. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hx.
      eapply lit_apart_sound; [exact Hla | lia].
    - repeat (apply andb_prop in Hwo; destruct Hwo as [Hwo ?]). apply Nat.eqb_eq in Hwo. subst i.
      repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H | H : (_ || _)%bool = true |- _ => apply orb_prop in H end.
      cbn [edenot] in Hx. intros Hin. apply LITS_LOW in Hin. pose proof (u64_range (ev E spi)). lia. }
  destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2|[b k] n fc|[b k] n];
    cbn [kentry_out_b] in Hb1; cbn [kentry_ok] in HK |- *; try exact HK.
  - (* [comment removed for export] *)
    destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
    destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb1 Hw) as (A & B & C & D).
    apply (AG1 b k (Z.of_nat w) Hb1); [destruct b; try exact I; exact Hb2|].
    rewrite Hu, u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb1 as [Hn Hb1]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb1) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb1 Hw) as (A & B & C & D).
    rewrite (AG1 b k n Hb1); [apply Hz; exact Hi | destruct b; try exact I; exact Hb2 |].
    unfold estart. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb1 as [Hn Hb1]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hlen & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb1) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
    split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb1 Hw) as (A & B & C & D).
    rewrite (AG1 b k n Hb1); [apply Hz; exact Hi | destruct b; try exact I; exact Hb2 |].
    unfold estart. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    apply Z.leb_le in Hb1. destruct HK as (H0 & H64 & Hnone).
    split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite Hag; [apply Hnone; exact Hi| rewrite u_small by lia; lia |].
    rewrite u_small by lia. eapply lit_apart_sound; [exact Hb2 | lia].
  - (* [comment removed for export] *)
    destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb1 as [Hn Hb1]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb1) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb1 Hw) as (A & B & C & D).
    rewrite (AG1 b k n Hb1); [apply Hz; exact Hi | destruct b; try exact I; exact Hb2 |].
    unfold estart. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb1 as [Hn Hb1]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz). pose proof (win_out_n0 _ _ _ _ _ _ _ Hb1) as Hn0.
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb1 Hw) as (A & B & C & D).
    rewrite (AG1 b k n Hb1); [apply Hz; exact Hi | destruct b; try exact I; exact Hb2 |].
    unfold estart. cbn [a_base a_off]. rewrite u_small by lia. lia.
Qed.

#[using="Type"] Theorem know_cut2_sound : forall E M M' spi lo hi ihi lits kn,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
     ~ in_lits lits (bv_unsigned x) -> M' x = M x) ->
  Forall (fun lh => (0 <= fst lh)%Z /\ (snd lh <= ihi)%Z) lits -> (ihi <= 2 ^ 40)%Z ->
  mem_grows M M' ->
  know_ok segs E M kn -> know_ok segs E M' (kn_cut2 spi lo hi ihi lits kn).
Proof.
  intros E M M' spi lo hi ihi lits kn Hw Hag Hl Hihi Hg HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_cut2 spi lo hi ihi lits (K :: rest))
    with (if kentry_out2_b spi lo hi ihi lits K then K :: kn_cut2 spi lo hi ihi lits rest else kn_cut2 spi lo hi ihi lits rest).
  destruct (kentry_out2_b spi lo hi ihi lits K) eqn:Hb.
  - constructor; [|apply IH; exact HK2]. eapply kentry_cut2_sound; eauto.
  - apply IH. exact HK2.
Qed.
End Cut2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section InW.
Import AX2 AX2S.

Definition win_inW_b (spi : nat) (lo hi llo lhi : Z) (b : expr) (k n : Z) : bool :=
  match b with
  | EVar i => Nat.eqb i spi && Z.leb lo k && Z.leb (k + n) hi && Z.leb 0 n
  | ELit z => Z.eqb z 0 && Z.leb llo k && Z.leb (k + n) lhi && Z.leb 0 n
  | _ => false
  end.

Definition entry_inW_b (spi : nat) (lo hi llo lhi : Z) (e : sentry) : bool :=
  match e with SE (SA b k) w _ => win_inW_b spi lo hi llo lhi b k (Z.of_nat w) end.

Definition log_inW_b (spi : nat) (lo hi llo lhi : Z) (log : list sentry) : bool :=
  forallb (entry_inW_b spi lo hi llo lhi) log.

#[using="Type"] Lemma mem_denot_inW : forall E M log spi lo hi llo lhi (x : word),
  log_inW_b spi lo hi llo lhi log = true ->
  (2 ^ 41 <= bv_unsigned (ev E spi))%Z -> (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z ->
  (- 2 ^ 40 <= lo)%Z -> (hi <= 2 ^ 40)%Z -> (0 <= llo)%Z -> (lhi <= 2 ^ 40)%Z ->
  ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
  ~ (llo <= bv_unsigned x < lhi)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi lo hi llo lhi x Hb S1 S2 L1 L2 L3 L4 Hx Hy.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_inW_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_inW_b] in He. pose proof (u64_range x).
  destruct b as [z|i| | | | | |]; cbn [win_inW_b] in He; try discriminate;
    repeat (apply andb_prop in He; destruct He as [He ?]);
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  - apply Z.eqb_eq in He. subst z. cbn [mem_denot]. rewrite wbytes_outside.
    + apply IH. exact Hrest.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite u_small by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite u_small by lia. lia.
  - apply Nat.eqb_eq in He. subst i. cbn [mem_denot]. rewrite wbytes_outside.
    + apply IH. exact Hrest.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
    + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
Qed.
End InW.
