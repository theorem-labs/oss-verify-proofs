(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM PlanS CtrLib CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module MemFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.

Lemma rb_mrd : forall m a, rb segs m a = mrd segs m (wa a).
Proof. reflexivity. Qed.

Lemma wb_wview : forall m a, wb segs m a = true <-> wview segs m (wa a) <> None.
Proof. intros m a. unfold wb, wa. destruct (wview segs m (Z_to_bv 64 a)); split; congruence. Qed.

Lemma mem_inv_of_st_ok : forall E st ms mo, St.st_ok segs OPS E st ms mo -> Lib.Mem.mem_inv segs (ms_mem ms).
Proof.
  intros E st ms mo HS a b Hab. unfold ro_addr.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:F; [|reflexivity].
  rewrite (so_minv _ _ _ _ _ _ HS a b Hab seg F). reflexivity.
Qed.

Lemma based_bytes : forall priv E m k r (o : Z) (n : nat),
  St.region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false ->
  loZ r <= o -> o + Z.of_nat n <= hiZ E r ->
  exists bs, length bs = n /\ bytes_at segs m (bv_unsigned (ev E k) + o) bs.
Proof.
  intros priv E m k r o n RO K Hlo Hhi.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [RL RH]. unfold two64 in RH.
  exists (map (fun i => match rb segs m (bv_unsigned (ev E k) + o + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [reflexivity|].
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map Nat.add]. rewrite <- rb_mrd.
  destruct (ro_valid _ _ _ _ _ _ RO K (bv_unsigned (ev E k) + o + Z.of_nat i) ltac:(lia)) as (RB & _ & _).
  destruct (rb segs m (bv_unsigned (ev E k) + o + Z.of_nat i)); [reflexivity| exfalso; exact (RB eq_refl)].
Qed.

Lemma based_rw_cells : forall priv E m k r (o : Z) (n : nat),
  St.region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> Mem.rg_w r = true ->
  loZ r <= o -> o + Z.of_nat n <= hiZ E r ->
  exists junk, length junk = n /\ rw_cells segs m (bv_unsigned (ev E k) + o) [CB n junk].
Proof.
  intros priv E m k r o n RO K W Hlo Hhi.
  destruct (based_bytes priv E m k r o n RO K Hlo Hhi) as (bs & L & BA). exists bs. split; [exact L|].
  pose proof (ro_range _ _ _ _ _ _ RO K) as [RL RH]. unfold two64 in RH.
  split.
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply (proj1 (wb_wview _ _)).
    destruct (ro_valid _ _ _ _ _ _ RO K (bv_unsigned (ev E k) + o + i) ltac:(lia)) as (_ & WB & _). exact (WB W).
Qed.

Lemma based_no_segment : forall priv E m k r a,
  St.region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false ->
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r -> find_segment segs a 1 = None.
Proof. intros priv E m k r a RO K Ha. exact (proj2 (proj2 (ro_valid _ _ _ _ _ _ RO K a Ha))). Qed.

Lemma blob_region_bytes : forall priv E m k r j (o : Z) (n : nat),
  St.region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> Mem.rg_cells r = IMap.Leaf -> Mem.rg_bg r = Mem.BGBlob j 0%uint63 ->
  0 <= o -> loZ r <= o -> o + Z.of_nat n <= hiZ E r ->
  bytes_at segs m (bv_unsigned (ev E k) + o) (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 n)).
Proof.
  intros priv E m k r j o n RO K HC HB Ho Hlo Hhi.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [RL RH]. unfold two64 in RH.
  split; [lia|]. rewrite length_map, length_seq. split; [lia|].
  intros i Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map Nat.add].
  rewrite <- rb_mrd. replace (bv_unsigned (ev E k) + o + Z.of_nat i) with (bv_unsigned (ev E k) + (o + Z.of_nat i)) by lia.
  pose proof (ro_bg _ _ _ _ _ _ RO (o + Z.of_nat i) ltac:(intros _; lia) ltac:(intros X; rewrite K in X; discriminate X)) as G.
  unfold bg_byte in G. rewrite HB in G. change (to_Z 0%uint63) with 0 in G. rewrite Z.sub_0_r in G.
  replace (Z.to_nat (o + Z.of_nat i)) with (Z.to_nat o + i)%nat in G by lia. apply G.
  intros g gr _ Hf. rewrite HC in Hf. cbn in Hf. discriminate Hf.
Qed.

Lemma blob_slice_length : forall E j o n, length (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 n)) = n.
Proof. intros. rewrite length_map, length_seq. reflexivity. Qed.

Lemma rb_wrap : forall m a, rb segs m a = rb segs m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros m a. unfold rb. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma wb_wrap : forall m a, wb segs m a = wb segs m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros m a. unfold wb. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma region_ok_view_frame : forall priv E m m' k r,
  St.region_ok segs priv E m k r ->
  (forall a, 0 <= a < two64 -> rb segs m' a = rb segs m a) ->
  (forall a, 0 <= a < two64 -> wb segs m a = true -> wb segs m' a = true) ->
  St.region_ok segs priv E m' k r.
Proof.
  intros priv E m m' k r [Rbst Rrange Rvalid Rcells Rin Rbg] RB0 WB0.
  assert (RB : forall a, rb segs m' a = rb segs m a).
  { intros a. rewrite (rb_wrap m' a), (rb_wrap m a). apply RB0. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as X. rewrite bv_modulus_64 in X. exact X. }
  assert (WB : forall a, wb segs m a = true -> wb segs m' a = true).
  { intros a. rewrite (wb_wrap m' a), (wb_wrap m a). apply WB0. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as X. rewrite bv_modulus_64 in X. exact X. }
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha. destruct (Rvalid K a Ha) as (V1 & V2 & V3). rewrite RB. split; [exact V1|]. split; [| exact V3]. intros W. apply WB. exact (V2 W).
  - intros g gr Hg. destruct (Rcells g gr Hg) as [SS FA]. split; [exact SS|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) FA c Hc) as (C1 & C2 & C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi. rewrite RB. exact (C4 i Hi).
  - exact Rin.
  - intros o H1 H2 U. pose proof (Rbg o H1 H2 U) as G. destruct (bg_byte segs E k r o); [| exact I]. rewrite RB. exact G.
Qed.

Lemma st_ok_mem_ext : forall E st (R F : _) pc fc rv m m' rom mo,
  (forall x, m' x = m x) ->
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo -> St.st_ok segs OPS E st (MS R F pc fc rv m' rom) mo.
Proof.
  intros E st R F pc fc rv m m' rom mo EQ HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (RB : forall a, 0 <= a < two64 -> rb segs m' a = rb segs m a) by (intros a _; unfold rb; rewrite EQ; reflexivity).
  assert (WB : forall a, 0 <= a < two64 -> wb segs m a = true -> wb segs m' a = true).
  { intros a _. unfold wb, wview. rewrite EQ. exact (fun H => H). }
  constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
  - intros k r Hk. exact (region_ok_view_frame _ _ m m' k r (Preg k r Hk) RB WB).
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    apply (St.op_frame OPS _ _ m m' mo); [intros a _ _; symmetry; apply EQ| intros a _ H; rewrite EQ; exact H| exact OH].
  - intros a b Hab. rewrite EQ in Hab. exact (Pminv a b Hab).
Qed.

Lemma st_ok_view_ext : forall E st (R F : _) pc fc rv m m' rom mo,
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  (forall a, 0 <= a < two64 -> rb segs m' a = rb segs m a) ->
  (forall a, 0 <= a < two64 -> wb segs m a = true -> wb segs m' a = true) ->
  ops_hold OPS E (s_ops st) m' mo ->
  (forall x b, m' x = Some b -> forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true) ->
  St.st_ok segs OPS E st (MS R F pc fc rv m' rom) mo.
Proof.
  intros E st R F pc fc rv m m' rom mo HS RB WB OPSH MINV.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
  intros k r Hk. exact (region_ok_view_frame _ _ m m' k r (Preg k r Hk) RB WB).
Qed.

Lemma st_ok_based_write : forall E st (R F : _) pc fc rv m m' rom mo kd rd rd',
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  IMap.find kd (s_regs st) = Some rd -> PrimInt63.eqb kd 0%uint63 = false -> Mem.rg_w rd = true ->
  (forall a, 0 <= a < two64 ->
     ~ (bv_unsigned (ev E kd) + loZ rd <= a < bv_unsigned (ev E kd) + hiZ E rd) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall x, m x <> None -> m' x <> None) ->
  (forall x b, m' x = Some b -> forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true) ->
  St.region_ok segs (s_priv st) E m' kd rd' ->
  loZ rd <= loZ rd' -> hiZ E rd' <= hiZ E rd ->
  St.st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st))
           (MS R F pc fc rv m' rom) mo.
Proof.
  intros E st R F pc fc rv m m' rom mo kd rd rd' HS Hkd K W FR MONO MINV RO' LO HI.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *.
  pose proof (Preg kd rd Hkd) as ROd. pose proof (ro_range _ _ _ _ _ _ ROd K) as [RL RH].
  assert (FIND : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> (k = kd /\ r = rd') \/ (k <> kd /\ IMap.find k (s_regs st) = Some r)).
  { intros k r H. destruct (Uint63.eqb kd k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact Pbst. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact Pbst || exact Q). right. split; [congruence| exact H]. }

  assert (OTHER : forall k r a, IMap.find k (s_regs st) = Some r -> k <> kd -> 0 <= a < two64 ->
            (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
            (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv (s_priv st) a) ->
            m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros k r a Hk NK Ha BR AR. apply FR; [exact Ha|]. intros IN.
    destruct (Uint63.eqb k 0%uint63) eqn:K0.
    - destruct (AR eq_refl) as [[seg Hs] _]. rewrite (based_no_segment _ _ _ _ _ a ROd K IN) in Hs. discriminate Hs.
    - exact (Pdisj k r kd rd Hk Hkd NK K0 K (or_intror W) a (conj (BR eq_refl) IN)). }
  assert (REGS : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> St.region_ok segs (s_priv st) E m' k r).
  { intros k r H. destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E m m' k r Pz (Preg k r Hk)). intros a Ha BR AR. exact (OTHER k r a Hk NK Ha BR AR). }
  constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 WW a [X1 X2].
    destruct (FIND k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (FIND k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + apply (Pdisj kd rd k2 q2 Hkd G2 NE K1 K2 (or_introl W) a). split; [clear -X1 LO HI; lia| exact X2].
    + apply (Pdisj k1 q1 kd rd G1 Hkd NE K1 K2 (or_intror W) a). split; [exact X1| clear -X2 LO HI; lia].
    + exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 WW a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    pose proof (proj1 (Forall_forall _ _) Papart o Ho) as AP.
    apply (St.op_frame OPS _ _ m m' mo); [| intros a _ H; apply MONO; exact H| exact OH].
    intros a Ha FP. symmetry. apply FR; [exact Ha|]. intros IN. destruct (AP a FP) as [NB _]. apply NB. exists kd, rd. auto.
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros (k & r & H & K' & RG). destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + apply NB. exists kd, rd. split; [exact Hkd|]. split; [exact K|]. lia.
    + apply NB. exists k, r. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k & r & H & K' & RG).
    destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + exists kd, rd. split; [exact Hkd|]. split; [exact K|]. lia.
    + exists k, r. auto.
Qed.

Lemma option_eq_dec_byte : forall (x y : option byte), {x = y} + {x <> y}.
Proof.
  intros [a|] [b|]; try (right; discriminate); [| left; reflexivity].
  destruct (bv_eqb a b) eqn:Q; [left; f_equal; unfold bv_eqb in Q; apply Z.eqb_eq in Q; apply bv_eq; exact Q| right].
  intros X. injection X as ->. unfold bv_eqb in Q. rewrite Z.eqb_refl in Q. discriminate Q.
Qed.

Lemma st_ok_based_replace : forall E st (R F : _) pc fc rv m m' rom mo kd rd rd',
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  IMap.find kd (s_regs st) = Some rd -> PrimInt63.eqb kd 0%uint63 = false ->
  (forall a, 0 <= a < two64 ->
     (bv_unsigned (ev E kd) + loZ rd' <= a < bv_unsigned (ev E kd) + hiZ E rd' \/ m' (Z_to_bv 64 a) <> m (Z_to_bv 64 a)) ->
     (forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kd -> PrimInt63.eqb k2 0%uint63 = false ->
        ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
     /\ find_segment segs a 1 = None
     /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o))))) ->
  (forall x, m x <> None -> m' x <> None) ->
  (forall x b, m' x = Some b -> forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true) ->
  St.region_ok segs (s_priv st) E m' kd rd' ->
  St.st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st))
           (MS R F pc fc rv m' rom) mo.
Proof.
  intros E st R F pc fc rv m m' rom mo kd rd rd' HS Hkd K ZONE MONO MINV RO'.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *.
  assert (FIND : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> (k = kd /\ r = rd') \/ (k <> kd /\ IMap.find k (s_regs st) = Some r)).
  { intros k r H. destruct (Uint63.eqb kd k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact Pbst. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact Pbst || exact Q). right. split; [congruence| exact H]. }

  assert (SAME : forall a, 0 <= a < two64 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) \/
            ((forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kd -> PrimInt63.eqb k2 0%uint63 = false ->
                 ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
             /\ find_segment segs a 1 = None
             /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))))).
  { intros a Ha. destruct (option_eq_dec_byte (m' (Z_to_bv 64 a)) (m (Z_to_bv 64 a))) as [E1|NE]; [left; exact E1| right; apply (ZONE a Ha); right; exact NE]. }
  assert (OTHER : forall k r a, IMap.find k (s_regs st) = Some r -> k <> kd -> 0 <= a < two64 ->
            (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
            (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv (s_priv st) a) ->
            m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros k r a Hk NK Ha BR AR. destruct (SAME a Ha) as [E1|(NB & NS & _)]; [exact E1| exfalso].
    destruct (Uint63.eqb k 0%uint63) eqn:K0.
    - destruct (AR eq_refl) as [[seg Hs] _]. rewrite NS in Hs. discriminate Hs.
    - exact (NB k r Hk NK K0 (BR eq_refl)). }
  assert (REGS : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> St.region_ok segs (s_priv st) E m' k r).
  { intros k r H. destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E m m' k r Pz (Preg k r Hk)). intros a Ha BR AR. exact (OTHER k r a Hk NK Ha BR AR). }
  pose proof (ro_range _ _ _ _ _ _ RO' K) as [RL' RH'].
  constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 WW a [X1 X2].
    destruct (FIND k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (FIND k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + destruct (ZONE a ltac:(lia) (or_introl X1)) as (NB & _ & _). exact (NB k2 q2 G2 ltac:(congruence) K2 X2).
    + destruct (ZONE a ltac:(lia) (or_introl X2)) as (NB & _ & _). exact (NB k1 q1 G1 ltac:(congruence) K1 X1).
    + exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 WW a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    apply (St.op_frame OPS _ _ m m' mo); [| intros a _ H; apply MONO; exact H| exact OH].
    intros a Ha FP. destruct (SAME a Ha) as [E1|(_ & _ & NF)]; [symmetry; exact E1| exfalso; exact (NF o Ho FP)].
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros (k & r & H & K' & RG). destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + pose proof (bv_unsigned_in_range 64 (ev E kd)) as RK. rewrite bv_modulus_64 in RK.
      destruct (ZONE a ltac:(lia) (or_introl RG)) as (_ & _ & NF). exact (NF o Ho FP).
    + apply NB. exists k, r. auto.
  -
    intros a _. apply St.plain_cover. exact OPS_plain.
Qed.

Lemma rget_core_getr : forall R F pc fc rv x, rget (Core R F pc fc rv) (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x).
Proof. intros. reflexivity. Qed.
Lemma reg_of_X0 : reg_of_r5 X0 = 0%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma getr_x0 : forall R, PropExec.getr R (reg_of_r5 X0) = Z_to_bv 64 0.
Proof. intros R. rewrite reg_of_X0. unfold PropExec.getr. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma den_VPz : forall E k, den E (VP k wzero) = ev E k.
Proof. intros E k. apply bv_eq. apply (den_VP0 E k wzero eq_refl). Qed.

Lemma getr_R : forall E st ms mo, St.st_ok segs OPS E st ms mo ->
  forall x, PropExec.getr (ms_regs ms) (reg_of_r5 x) = den E (getr st x).
Proof.
  intros E st ms mo HS x. pose proof (so_regs _ _ _ _ _ _ HS x) as R. unfold rget in R. cbn [c_regs] in R.
  unfold PropExec.getr, getr. unfold is_x0 in R.
  destruct x; cbn [reg_of_r5 r5_to_Z] in R |- *; first [exact R | rewrite <- R; reflexivity].
Qed.

Lemma st_vars_below_parts : forall n st, st_vars_below n st = true ->
  rf_allb (sv_vars_below n) (s_rf st) = true /\ rf_allb (sv_vars_below n) (s_ff st) = true
  /\ resv_vars_below n (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k n && region_vars_below n r) (s_regs st) = true
  /\ forallb (fact_vars_below n) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below n) (op_args o)) (s_ops st) = true.
Proof.
  intros n st SVB. unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Ltac vb_fin :=
  cbn [sv_vars_below] in *;
  repeat rewrite andb_true_iff in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; try assumption; try reflexivity.
Ltac vb_cases :=
  repeat (match goal with
          | |- context [if ?c then _ else _] => destruct c
          | |- context [match ?x with _ => _ end] => destruct x
          end).
Lemma sv_vars_below_add_lit_fold : forall n a c, sv_vars_below n a = true -> sv_vars_below n (add_lit_fold a c) = true.
Proof. intros n a c Ha. unfold add_lit_fold. vb_cases; vb_fin. Qed.
Lemma sv_vars_below_alu : forall n op a b, op = ALU_ADD \/ op = ALU_SUB ->
  sv_vars_below n a = true -> sv_vars_below n b = true -> sv_vars_below n (sv_alu op a b) = true.
Proof.
  intros n op a b Hop Ha Hb. unfold sv_alu.
  assert (H0 : sv_vars_below n (sv_alu0 op a b) = true).
  { unfold sv_alu0.

    destruct Hop as [-> | ->]; vb_cases;
      first [ exact Ha | exact Hb | reflexivity
            | lazymatch goal with |- sv_vars_below ?m (VAlu _ ?A ?B) = true =>
                change (sv_vars_below m A && sv_vars_below m B = true); rewrite Ha, Hb; reflexivity end
            | apply sv_vars_below_add_lit_fold; assumption
            | vb_fin ]. }
  destruct Hop as [-> | ->]; cbv zeta iota beta; [exact H0| apply sv_vars_below_subsub_fold; exact H0].
Qed.

Lemma st_vars_below_setregs : forall n st kd rd rd',
  IMap.bst (s_regs st) -> st_vars_below n st = true -> IMap.find kd (s_regs st) = Some rd ->
  region_vars_below n rd' = true ->
  st_vars_below n (setregs st (IMap.add kd rd' (s_regs st))) = true.
Proof.
  intros n st kd rd rd' B SVB Hkd RV. pose proof (st_vars_below_parts n st SVB) as (P1 & P2 & P3 & P4 & P5 & P6).
  unfold st_vars_below. cbn [setregs s_rf s_ff s_resv s_regs s_facts s_ops]. rewrite P1, P2, P3, P5, P6. cbn [andb].
  rewrite andb_true_r.
  apply (proj2 (IMap.forallb_spec _ _ (IMap.bst_add _ _ _ B))) || (rewrite (proj2 (IMap.forallb_spec _ _ (IMap.bst_add _ _ _ B))); [reflexivity|]). intros k v Hk.
  pose proof (proj1 (IMap.forallb_spec _ _ B) P4) as ALL.
  destruct (Uint63.eqb kd k) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in Hk by exact B. injection Hk as <-.
    pose proof (ALL kd rd Hkd) as X. apply andb_prop in X as [X _]. rewrite X, RV. reflexivity.
  - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in Hk by (exact B || exact Q). exact (ALL k v Hk).
Qed.

Lemma clobber_sound_above : forall E st (R R' F : bvmap 5 word) pc fc rv m rom mo (Fv : Z -> word) (Gv : Z -> Z -> byte),
  St.st_ok segs OPS (env_above E (s_next st) Fv Gv) st (MS R F pc fc rv m rom) mo ->
  0 < to_Z (s_next st) -> to_Z (s_next st) + 256 <= 2 ^ 62 ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) ->
  (forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)) ->
  St.st_ok segs OPS (env_above E (s_next st) Fv Gv) (clobber st) (MS R' F pc fc rv m rom) mo.
Proof.
  intros E st R R' F pc fc rv m rom mo Fv Gv HS' POS B62 HF HK.
  set (E' := env_above E (s_next st) Fv Gv) in *.
  pose proof HS' as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (clobber_fields st) as (Fpc & Fff & Frv & FR & Ffs & Fos & Fpv & Fnx).
  pose proof (int_range (s_next st)) as NR. rewrite two63_eq in NR.
  split; rewrite ?Fpc, ?Fff, ?Frv, ?FR, ?Ffs, ?Fos, ?Fpv, ?Fnx;
    cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
  intros x. rewrite rget_core_getr. change (rf_get (s_rf (clobber st)) x) with (getr (clobber st) x). rewrite getr_clobber.
  destruct (clob_pos x) as [i|] eqn:CP.
  - rewrite <- (HF x i CP). cbn [den].
    assert (Hi : (i <= 14)%nat) by (destruct x; cbn in CP; try discriminate; injection CP as <-; lia).
    assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
    unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA.
    replace (to_Z (s_next st) + Z.of_nat i - to_Z (s_next st)) with (Z.of_nat i) by lia.
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct (r5_eqb x X0) eqn:Q0.
    + apply r5_eqb_spec in Q0. subst x. rewrite getr_x0. change (getr st X0) with (rf_get (s_rf st) X0). rewrite Px0, den_VL. reflexivity.
    + assert (N0 : x <> X0) by (intros ->; rewrite r5_eqb_refl in Q0; discriminate).
      rewrite (HK x N0 CP). pose proof (Pregs x) as RX. rewrite rget_core_getr in RX. exact RX.
Qed.

Lemma clobber_sound : forall E st (R R' F : bvmap 5 word) pc fc rv m rom mo (Fv : Z -> word) (Gv : Z -> Z -> byte),
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  st_vars_below (s_next st) st = true -> 0 < to_Z (s_next st) -> to_Z (s_next st) + 256 <= 2 ^ 62 ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) ->
  (forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)) ->
  St.st_ok segs OPS (env_above E (s_next st) Fv Gv) (clobber st) (MS R' F pc fc rv m rom) mo.
Proof.
  intros E st R R' F pc fc rv m rom mo Fv Gv HS SVB POS B62 HF HK.
  apply (clobber_sound_above E st R R' F pc fc rv m rom mo Fv Gv); try assumption.
  exact (st_ok_reval segs OPS (s_next st) E _ (env_above_ext E (s_next st) Fv Gv) st _ mo POS SVB HS).
Qed.

Lemma setpc_sound : forall E st (R F : bvmap 5 word) pc fc rv m rom mo (r : int),
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  St.st_ok segs OPS E (setpc st r) (MS R F (Z_to_bv 64 (to_Z r)) fc rv m rom) mo.
Proof.
  intros E st R F pc fc rv m rom mo r HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  split; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending setpc s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *; try assumption.
  reflexivity.
Qed.

Definition byte_at (m : word -> option byte) (a : Z) : byte := match rb segs m a with Some b => b | None => Z_to_bv 8 0 end.
Definition word4_at (m : word -> option byte) (A : Z) : word :=
  Z_to_bv 64 (bytes_le_to_Z [byte_at m A; byte_at m (A + 1); byte_at m (A + 2); byte_at m (A + 3)]).

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    pose proof (bytes_le_to_Z_nonneg bs) as NN.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. pose proof (bytes_le_to_Z_nonneg bs) as NN.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma byte_of_word4_at : forall m A t, 0 <= t < 4 ->
  byte_of (word4_at m A) t = nth (Z.to_nat t) [byte_at m A; byte_at m (A + 1); byte_at m (A + 2); byte_at m (A + 3)] (Z_to_bv 8 0).
Proof.
  intros m A t Ht. unfold word4_at, byte_of.
  set (bs := [byte_at m A; byte_at m (A + 1); byte_at m (A + 2); byte_at m (A + 3)]).
  pose proof (bytes_le_to_Z_bound bs) as B. change (2 ^ (8 * Z.of_nat (length bs))) with (2 ^ 32) in B.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia).
  pose proof (Z_to_le_bytes_nth 4 (bytes_le_to_Z bs) (Z.to_nat t) (Z_to_bv 8 0) ltac:(lia)) as NT. rewrite Z2Nat.id in NT by lia.
  rewrite <- NT. pose proof (Z_to_le_bytes_to_Z bs) as RT. change (length bs) with 4%nat in RT. rewrite RT. reflexivity.
Qed.

Lemma havoc_errno_sound : forall E st (errno : int) st' (R F : bvmap 5 word) pc fc m rom mo,
  St.st_ok segs OPS E st (MS R F pc fc None m rom) mo ->
  s_resv st = RNone ->
  ev E (s_next st) = word4_at m (to_Z errno) ->
  havoc_errno segs errno st = Some st' ->
  St.st_ok segs OPS E st' (MS R F pc fc None m rom) mo
  /\ s_pc st' = s_pc st /\ s_rf st' = s_rf st /\ s_next st' = PrimInt63.add (s_next st) 1%uint63.
Proof.
  intros E st errno st' R F pc fc m rom mo HS RV EV H.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *.
  unfold havoc_errno, fresh, store4_abs, do_store in H. cbn [fst snd addr_of s_regs s_facts s_priv s_resv s_pc s_rf s_ff s_ops s_next set_next] in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate].
  destruct (Mem.okey (wlit errno)) as [key|] eqn:HK; [|discriminate].
  destruct (can_write segs (s_facts st) (s_priv st) 0%uint63 r0 key 4%uint63) eqn:CW; [|discriminate].
  apply Some_inj in H. subst st'. rewrite RV. cbn [resv_after_store].
  split; [| repeat split; reflexivity].
  pose proof (Preg _ _ Hr0) as RO0.
  assert (W4 : wok 4%uint63) by (right; right; left; reflexivity).
  destruct (region_store_sound segs (s_priv st) E m (s_facts st) 0%uint63 r0 key 4%uint63 (VP (s_next st) wzero) Pfacts Pz RO0 W4 CW)
    as (SOK & RO' & Flo & Fhi & Fw & Fbg & FR).
  destruct (can_write_sound segs (s_priv st) E m (s_facts st) 0%uint63 r0 key 4%uint63 Pfacts Pz RO0 W4 CW) as (CR & WBk & _).
  destruct (can_read_sound segs (s_priv st) E m (s_facts st) 0%uint63 r0 key 4%uint63 Pfacts Pz RO0 W4 CR) as (RA & RAw & RBk & _).
  cbv zeta in RO', FR, RA, RAw. unfold addrZ in *. rewrite (ev0_zero E Pz), Z.add_0_l in *.
  change (to_Z 4%uint63) with 4 in *.
  assert (KEY : keyZ key = to_Z errno).
  { destruct (okey_sound (wlit errno) key HK) as [KE _]. rewrite KE, w2Zs_eq, wlit_ok. cbn [wt wlit]. lia. }
  rewrite KEY in *.
  set (A := to_Z errno) in *.
  set (m2 := write_to_mem m (Z_to_bv 64 A) (store_bytes 4%uint63 (den E (VP (s_next st) wzero)))) in *.

  assert (SAME : forall i, 0 <= i < 4 -> m2 (Z_to_bv 64 (A + i)) = Some (byte_at m (A + i)) /\ rb segs m (A + i) = Some (byte_at m (A + i))).
  { intros i Hi. split.
    - subst m2. rewrite write_to_mem_in; [| lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia].
      rewrite store_bytes_nth_error by (change (to_Z 4%uint63) with 4; lia). f_equal. rewrite den_VPz, EV, byte_of_word4_at by lia.
      destruct (Z.eq_dec i 0) as [->|]; [rewrite Z.add_0_r; reflexivity|]. destruct (Z.eq_dec i 1) as [->|]; [reflexivity|].
      destruct (Z.eq_dec i 2) as [->|]; [reflexivity|]. replace i with 3 by lia. reflexivity.
    - unfold byte_at. destruct (rb segs m (A + i)) eqn:X; [reflexivity|]. exfalso. exact (RBk i Hi X). }
  assert (RBq : forall a, 0 <= a < two64 -> rb segs m a = rb segs m2 a).
  { intros a Ha. destruct (Z_lt_le_dec a A) as [L|G]; [| destruct (Z_lt_le_dec a (A + 4)) as [L2|G2]].
    - unfold rb. subst m2. rewrite write_to_mem_frame; [reflexivity| lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia| exact Ha| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia].
    - destruct (SAME (a - A) ltac:(lia)) as [E2 E1]. replace a with (A + (a - A)) by lia. rewrite E1. unfold rb. rewrite E2. reflexivity.
    - unfold rb. subst m2. rewrite write_to_mem_frame; [reflexivity| lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia| exact Ha| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia]. }
  assert (WBq : forall a, 0 <= a < two64 -> wb segs m2 a = true -> wb segs m a = true).
  { intros a Ha W. destruct (Z_lt_le_dec a A) as [L|G]; [| destruct (Z_lt_le_dec a (A + 4)) as [L2|G2]].
    - unfold wb, wview in W |- *. subst m2. rewrite write_to_mem_frame in W; [exact W| lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia| exact Ha| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia].
    - replace a with (A + (a - A)) by lia. apply WBk. lia.
    - unfold wb, wview in W |- *. subst m2. rewrite write_to_mem_frame in W; [exact W| lia| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia| exact Ha| rewrite store_bytes_length; change (to_Z 4%uint63) with 4; lia]. }
  pose proof (region_ok_view_frame (s_priv st) E m2 m 0%uint63 _ RO' RBq WBq) as RO''.
  assert (REGS : forall k r, IMap.find k (IMap.add 0%uint63 (Mem.region_store r0 key 4%uint63 (VP (s_next st) wzero)) (s_regs st)) = Some r ->
            St.region_ok segs (s_priv st) E m k r).
  { intros k r Hk. destruct (Uint63.eqb 0%uint63 k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in Hk by exact Pbst. injection Hk as <-. exact RO''.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in Hk by (exact Pbst || exact Q). exact (Preg k r Hk). }
  split; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - apply (same_range_disjoint E (s_regs st) 0%uint63 r0 _ Pbst Hr0 Flo Fhi Fw Pdisj).
  - eapply pub_of_regions. exact REGS.
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros IB. apply NB. exact (same_range_in_based E (s_regs st) 0%uint63 r0 _ Pbst Hr0 Flo Fhi a IB).
  -
    intros a FA. apply Pcov. revert a FA. apply St.fx_acc_based. intros a IB.
    exact (same_range_in_based E (s_regs st) 0%uint63 r0 _ Pbst Hr0 Flo Fhi a IB).
Qed.

Lemma addfact_sound : forall E st ms mo f, St.st_ok segs OPS E st ms mo -> fact_holds E f -> St.st_ok segs OPS E (addfact st f) ms mo.
Proof.
  intros E st ms mo f HS Hf. pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  split; cbn [addfact s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  constructor; [exact Hf| exact Pfacts].
Qed.

Lemma st_ok_rf : forall E st (R R' F : bvmap 5 word) pc fc rv m rom mo (rf' : rf sv) (nx : int),
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' F pc fc rv) (reg_of_r5 x) = den E (rf_get rf' x)) ->
  St.st_ok segs OPS E (SS (s_pc st) rf' (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) nx) (MS R' F pc fc rv m rom) mo.
Proof.
  intros E st R R' F pc fc rv m rom mo rf' nx HS X0' REGS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *; try assumption.
Qed.

Lemma clobber_setr10_sound_above : forall E st (R R' F : bvmap 5 word) pc fc rv m rom mo (Fv : Z -> word) (Gv : Z -> Z -> byte) (v : sv),
  St.st_ok segs OPS (env_above E (s_next st) Fv Gv) st (MS R F pc fc rv m rom) mo ->
  0 < to_Z (s_next st) -> to_Z (s_next st) + 256 <= 2 ^ 62 ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)) ->
  (forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)) ->
  den (env_above E (s_next st) Fv Gv) v = PropExec.getr R' 10%bv ->
  St.st_ok segs OPS (env_above E (s_next st) Fv Gv) (setr (clobber st) X10 v) (MS R' F pc fc rv m rom) mo.
Proof.
  intros E st R R' F pc fc rv m rom mo Fv Gv v HS' POS B62 HF HK Hv.
  set (E' := env_above E (s_next st) Fv Gv) in *.
  pose proof (so_regs _ _ _ _ _ _ HS') as Pregs. pose proof (so_x0 _ _ _ _ _ _ HS') as Px0. cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv] in Pregs.
  pose proof (int_range (s_next st)) as NR. rewrite two63_eq in NR.
  pose proof (clobber_fields st) as (Fpc & Fff & Frv & FR & Ffs & Fos & Fpv & Fnx).
  rewrite (setr_eq (clobber st) X10 v eq_refl). rewrite Fpc, Fff, Frv, FR, Ffs, Fos, Fpv.
  apply (st_ok_rf E' st R R' F pc fc rv m rom mo _ _ HS').
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st)) X0) with (getr (clobber st) X0). rewrite getr_clobber. cbn [clob_pos]. exact Px0.
  - intros x. rewrite rget_core_getr.
    destruct (r5_eqb x X10) eqn:Q10.
    { apply r5_eqb_spec in Q10. subst x. rewrite rf_get_set_same. symmetry. exact Hv. }
    assert (N10 : x <> X10) by (intros ->; rewrite r5_eqb_refl in Q10; discriminate).
    rewrite rf_get_set_other by (intros Q; apply N10; symmetry; exact Q).
    change (rf_get (s_rf (clobber st)) x) with (getr (clobber st) x). rewrite getr_clobber.
    destruct (clob_pos x) as [i|] eqn:CP.
    + rewrite <- (HF x i CP). cbn [den].
      assert (Hi : (i <= 14)%nat) by (destruct x; cbn in CP; try discriminate; injection CP as <-; lia).
      assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
      unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA.
      replace (to_Z (s_next st) + Z.of_nat i - to_Z (s_next st)) with (Z.of_nat i) by lia.
      apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
    + destruct (r5_eqb x X0) eqn:Q0.
      * apply r5_eqb_spec in Q0. subst x. rewrite getr_x0. change (getr st X0) with (rf_get (s_rf st) X0). rewrite Px0, den_VL. reflexivity.
      * assert (N0 : x <> X0) by (intros ->; rewrite r5_eqb_refl in Q0; discriminate).
        rewrite (HK x N0 N10 CP). pose proof (Pregs x) as RX. rewrite rget_core_getr in RX. exact RX.
Qed.

Lemma key_range_half : forall i, - two63 / 2 <= keyZ i < two63 / 2.
Proof. intros i. pose proof (keyZ_range i). change (- two63 / 2) with (- (2 ^ 62)). rewrite half63. lia. Qed.

Lemma forget_r1_ok : forall priv E m m' r1 (ksp : int),
  ev E 0%uint63 = Z_to_bv 64 0 ->
  St.region_ok segs priv E m 1%uint63 r1 -> Mem.rg_bg r1 = Mem.BGNone -> Mem.rg_w r1 = true ->
  keyZ ksp mod 16 = 0 -> keyZ ksp < 0 ->
  let base := bv_unsigned (ev E 1%uint63) in let sp := base + keyZ ksp in
  0 <= base + loZ r1 -> base + loZ r1 <= sp -> sp <= base + hiZ E r1 < two64 ->
  (forall a, sp <= a < base + hiZ E r1 -> rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true)) ->
  (forall a, base + loZ r1 <= a < sp -> rb segs m' a <> None /\ wb segs m' a = true) ->
  St.region_ok segs priv E m' 1%uint63 (Mem.region_forget r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp)).
Proof.
  intros priv E m m' r1 ksp Hz RO HBG HW K16 KNEG. cbv zeta. intros LO0 ROOM HI AG BELOW.
  destruct (region_forget_sound segs priv E m 1%uint63 r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp) RO) as (RO' & Elo & Ehi & Ew & Ebg).
  assert (Lq : loZ (Mem.region_forget r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp)) = loZ r1) by (unfold loZ; rewrite Elo; reflexivity).
  assert (Hq : hiZ E (Mem.region_forget r1 (Mem.granule (Mem.rg_lo r1)) (Mem.granule ksp)) = hiZ E r1) by (unfold hiZ; rewrite Ehi; reflexivity).
  pose proof (keyZ_range ksp) as Rksp.
  apply (region_ok_fine_frame segs priv E m m' 1%uint63 _ Hz RO').
  - intros o R1 _ CL. specialize (R1 eq_refl). rewrite Lq, Hq in R1.
    destruct CL as [(g & gr & c & Hg & Hc & Eg & COV) | [U BG]].
    +
      unfold Mem.region_forget in Hg. rewrite HBG in Hg. cbn [Mem.is_bgnone Mem.rg_cells] in Hg.
      rewrite IMap.find_remove_range in Hg by exact (ro_bst _ _ _ _ _ _ RO).
      destruct (PrimInt63.leb (Mem.granule (Mem.rg_lo r1)) g && PrimInt63.ltb g (Mem.granule ksp))%bool eqn:RNG; [discriminate|].
      assert (LE : keyZ ksp <= o).
      { pose proof (keyZ_range (Mem.rg_lo r1)) as Rlo. pose proof (keyZ_range ksp) as Rk.
        destruct (granule_gidx (Mem.rg_lo r1) (key_range_half _)) as [Glo Ilo].
        destruct (granule_gidx ksp (key_range_half _)) as [Gk Ik].
        destruct (gidx_ok ksp) as [Gm _].
        assert (G0 : to_Z (Mem.gidx ksp) = 0).
        { rewrite Gm. destruct (keyZ_cases ksp) as [[_ EK]|[_ EK]]; rewrite EK in K16.
          - apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia.
          - replace (to_Z ksp - 2 ^ 63) with (to_Z ksp + (- 2 ^ 59) * 16) in K16 by lia. rewrite Z.mod_add in K16 by lia.
            apply Z.mod_divide in K16; [|lia]. apply Z.mod_divide; [lia|]. destruct K16 as [q Qq]. exists (2 * q). lia. }
        pose proof (Z.div_mod o 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
        unfold loZ in R1, ROOM, LO0.
        destruct (keyZ_cases g) as [[Rg Egk]|[Rg Egk]]; [lia|].
        destruct (keyZ_cases (Mem.granule (Mem.rg_lo r1))) as [[R2 E2]|[R2 E2]]; [lia|].
        destruct (keyZ_cases (Mem.granule ksp)) as [[R3 E3]|[R3 E3]]; [lia|].
        apply andb_false_iff in RNG. destruct RNG as [RNG|RNG].
        - destruct (Uint63.lebP (Mem.granule (Mem.rg_lo r1)) g) as [X|X]; [rewrite RNG in *; discriminate || lia|]. lia.
        - destruct (Uint63.ltbP g (Mem.granule ksp)) as [X|X]; [rewrite RNG in *; discriminate || lia|]. lia. }
      exact (proj1 (AG (bv_unsigned (ev E 1%uint63) + o) ltac:(unfold loZ in *; lia))).
    + exfalso. apply BG. unfold bg_byte. rewrite Ebg, HBG. reflexivity.
  - intros _ a Ha. rewrite Lq, Hq in Ha.
    destruct (Z_lt_le_dec a (bv_unsigned (ev E 1%uint63) + keyZ ksp)) as [LT|GE].
    + destruct (BELOW a ltac:(lia)) as [V1 V2]. split; [exact V1|]. intros _. exact V2.
    + destruct (ro_valid _ _ _ _ _ _ RO eq_refl a Ha) as (V1 & V2 & _).
      destruct (AG a ltac:(lia)) as [E2 W2].
      split; [rewrite E2; exact V1|]. intros Wr. apply W2. apply V2. rewrite <- Ew. exact Wr.
Qed.

Definition cfv (R' : bvmap 5 word) (e : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [PropExec.getr R' 1%bv; PropExec.getr R' 5%bv; PropExec.getr R' 6%bv; PropExec.getr R' 7%bv;
       PropExec.getr R' 11%bv; PropExec.getr R' 12%bv; PropExec.getr R' 13%bv; PropExec.getr R' 14%bv;
       PropExec.getr R' 15%bv; PropExec.getr R' 16%bv; PropExec.getr R' 17%bv;
       PropExec.getr R' 28%bv; PropExec.getr R' 29%bv; PropExec.getr R' 30%bv; PropExec.getr R' 31%bv; e] (Z_to_bv 64 0).

Lemma cfv_clob : forall R' e x i, clob_pos x = Some i -> cfv R' e (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x).
Proof. intros R' e x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.
Lemma cfv_15 : forall R' e, cfv R' e 15 = e. Proof. reflexivity. Qed.

Definition cenv (E : env) (st : sstate) (R' : bvmap 5 word) (m : word -> option byte) (errno : int) : env :=
  env_above E (s_next st) (cfv R' (word4_at m (to_Z errno))) (fun _ _ => Z_to_bv 8 0).

Lemma cenv_ext : forall E st R' m errno, env_ext (s_next st) E (cenv E st R' m errno).
Proof. intros. apply env_above_ext. Qed.
Lemma cenv_eb : forall E st R' m errno, eb (cenv E st R' m errno) = eb E.
Proof. intros. apply eb_above. Qed.

Theorem ccall_frame_above : forall E st1 (errno r : int) st2 (R R' F : bvmap 5 word) pc fc m rom mo,
  St.st_ok segs OPS (cenv E st1 R' m errno) st1 (MS R F pc fc None m rom) mo ->
  s_resv st1 = RNone -> 0 < to_Z (s_next st1) -> to_Z (s_next st1) + 256 <= 2 ^ 62 ->
  (forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)) ->
  havoc_errno segs errno (clobber st1) = Some st2 ->
  St.st_ok segs OPS (cenv E st1 R' m errno) (setpc st2 r) (MS R' F (Z_to_bv 64 (to_Z r)) fc None m rom) mo
  /\ s_next (setpc st2 r) = PrimInt63.add (s_next st1) 16%uint63 /\ s_rf (setpc st2 r) = s_rf (clobber st1).
Proof.
  intros E st1 errno r st2 R R' F pc fc m rom mo HS' RV POS B62 HK HE.
  pose proof (clobber_fields st1) as (Fpc & Fff & Frv & FR & Ffs & Fos & Fpv & Fnx).
  pose proof (int_range (s_next st1)) as NR. rewrite two63_eq in NR.
  pose proof (clobber_sound_above E st1 R R' F pc fc None m rom mo (cfv R' (word4_at m (to_Z errno))) (fun _ _ => Z_to_bv 8 0)
                HS' POS B62 (fun x i H => cfv_clob R' _ x i H) HK) as HS1.
  assert (EV : ev (cenv E st1 R' m errno) (s_next (clobber st1)) = word4_at m (to_Z errno)).
  { rewrite Fnx. unfold cenv. rewrite ev_above by (rewrite add_Z; [| change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; lia]; change (to_Z 15%uint63) with 15; lia).
    rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; lia). change (to_Z 15%uint63) with 15.
    replace (to_Z (s_next st1) + 15 - to_Z (s_next st1)) with 15 by lia. apply cfv_15. }
  destruct (havoc_errno_sound (cenv E st1 R' m errno) (clobber st1) errno st2 R' F pc fc m rom mo HS1 ltac:(rewrite Frv; exact RV) EV HE)
    as (HS2 & P2 & RF2 & NX2).
  split; [exact (setpc_sound _ _ _ _ _ _ _ _ _ _ r HS2)|].
  cbn [setpc s_next s_rf]. rewrite NX2, RF2, Fnx. split; [| reflexivity].
  apply Uint63.to_Z_inj. rewrite !add_Z; change (to_Z 15%uint63) with 15; change (to_Z 16%uint63) with 16; change (to_Z 1%uint63) with 1;
    rewrite ?wB_two63, ?two63_eq; try lia.
  rewrite add_Z; change (to_Z 15%uint63) with 15; rewrite ?wB_two63, ?two63_eq; lia.
Qed.

Theorem ccall_frame : forall E st1 (errno r : int) st2 (R R' F : bvmap 5 word) pc fc m rom mo,
  St.st_ok segs OPS E st1 (MS R F pc fc None m rom) mo ->
  s_resv st1 = RNone -> st_vars_below (s_next st1) st1 = true -> 0 < to_Z (s_next st1) -> to_Z (s_next st1) + 256 <= 2 ^ 62 ->
  (forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)) ->
  havoc_errno segs errno (clobber st1) = Some st2 ->
  St.st_ok segs OPS (cenv E st1 R' m errno) (setpc st2 r) (MS R' F (Z_to_bv 64 (to_Z r)) fc None m rom) mo
  /\ s_next (setpc st2 r) = PrimInt63.add (s_next st1) 16%uint63 /\ s_rf (setpc st2 r) = s_rf (clobber st1).
Proof.
  intros E st1 errno r st2 R R' F pc fc m rom mo HS RV SVB POS B62 HK HE.
  apply (ccall_frame_above E st1 errno r st2 R R' F pc fc m rom mo); try assumption.
  exact (st_ok_reval segs OPS (s_next st1) E _ (cenv_ext E st1 R' m errno) st1 _ mo POS SVB HS).
Qed.

End WithSegs.
End MemFX.
