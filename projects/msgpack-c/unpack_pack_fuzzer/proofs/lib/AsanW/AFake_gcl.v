(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase F_tryinit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_m2s_b.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 FsKit AFake_gc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma gc_disjoint_from_app : forall W1 W2 A k, disjoint_from W1 A k -> disjoint_from W2 A k -> disjoint_from (W1 ++ W2) A k.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; intros W2 A k H1 H2; [exact H2|]. destruct H1 as [H1 H1']. split; [exact H1| apply IH; assumption]. Qed.
Lemma gc_outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof. induction l1 as [|[lo hi] l1 IH]; cbn; intros l2 x; [tauto|]. rewrite IH. tauto. Qed.
Lemma gc_sub_fp_app_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x H. apply gc_outside_app in H. tauto. Qed.
Lemma gc_sub_fp_app_r : forall W1 W2, sub_fp W2 (W1 ++ W2).
Proof. intros W1 W2 x H. apply gc_outside_app in H. tauto. Qed.

Section CANSEC1. Context {rc : runConstT}.

Definition gfreed (bot cur : Z) (b : byte) (r : Z) : bool := negb (bv_unsigned b =? 0) && (bot <? r) && (r <? cur).

Definition gcW1 (fs c p : Z) : list (Z * Z) :=
  [(gflag fs c p, gflag fs c p + 1); (shad (gframe fs c p), shad (gframe fs c p) + 8 * 2 ^ c)].

Fixpoint gcW (fs c : Z) (fl : Z -> byte) (rs : Z -> Z) (bot cur : Z) (i : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => (if gfreed bot cur (fl i) (rs i) then gcW1 fs c i else []) ++ gcW fs c fl rs bot cur (i + 1) n'
  end.

Lemma gcW_disjoint : forall fs c fl rs bot cur A k n i,
  (forall p, i <= p < i + Z.of_nat n -> gfreed bot cur (fl p) (rs p) = true -> disjoint_from (gcW1 fs c p) A k) ->
  disjoint_from (gcW fs c fl rs bot cur i n) A k.
Proof.
  intros fs c fl rs bot cur A k n. induction n as [|n IH]; intros i H; cbn [gcW]; [exact I|].
  apply gc_disjoint_from_app.
  - destruct (gfreed bot cur (fl i) (rs i)) eqn:GF; [apply H; [lia| exact GF]| exact I].
  - apply IH. intros p Hp GF. apply H; [lia| exact GF].
Qed.

Lemma gc_pows : forall c, 0 <= c < 11 ->
  0 < 2 ^ (14 - c) <= 16384 /\ 2 ^ (15 - c) = 2 * 2 ^ (14 - c) /\ 64 <= 2 ^ (6 + c) /\ 2 ^ (14 - c) * 2 ^ (6 + c) = 1048576
  /\ 2 ^ (6 + c) = 8 * (8 * 2 ^ c) /\ 0 < 2 ^ c.
Proof.
  intros c C. split; [split; [apply Z.pow_pos_nonneg; lia| change 16384 with (2^14); apply Z.pow_le_mono_r; lia]|].
  split; [replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity|].
  split; [change 64 with (2^6); apply Z.pow_le_mono_r; lia|].
  split; [rewrite <- Z.pow_add_r by lia; replace (14 - c + (6 + c)) with 20 by lia; reflexivity|].
  split; [rewrite Z.pow_add_r by lia; change (2^6) with 64; lia| apply Z.pow_pos_nonneg; lia].
Qed.

Lemma gc_geo : forall fs c p, 0 <= c < 11 -> 0 <= p < gcN c -> 0 <= fs ->
  fs + 4096 <= gflag fs c p < fs + 36864
  /\ fs + 36864 <= gframe fs c p /\ gframe fs c p + 2 ^ (6 + c) <= fs + 11571200.
Proof.
  intros fs c p C P F0. unfold gflag, gflags, gframe, gcN in *.
  pose proof (gc_pows c C) as (P14 & P15 & P6 & PM & _ & _). split; [lia|]. split; [nia|nia].
Qed.

Lemma gc_shad_eq : forall x, shad x = 0x7fff8000 + x / 8.
Proof. intros x. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma gc_shad_step : forall fs c p q, 0 <= c < 11 -> 0 <= p < q ->
  shad (gframe fs c p) + 8 * 2 ^ c <= shad (gframe fs c q).
Proof.
  intros fs c p q C PQ. rewrite !gc_shad_eq. unfold gframe.
  pose proof (gc_pows c C) as (_ & _ & _ & _ & P8 & PC).
  replace (fs + 36864 + c * 1048576 + q * 2 ^ (6 + c)) with (fs + 36864 + c * 1048576 + p * 2 ^ (6 + c) + ((q - p) * (8 * 2 ^ c)) * 8) by (rewrite P8; ring).
  rewrite Z.div_add by lia. nia.
Qed.

Lemma gc_shad_off : forall fs c p, 0 <= c < 11 -> 0 <= p < gcN c ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP ->
  (shad (gframe fs c p) + 8 * 2 ^ c <= fs \/ fs + 11571200 <= shad (gframe fs c p))
  /\ 0x7fff8000 <= shad (gframe fs c p) /\ shad (gframe fs c p) + 8 * 2 ^ c <= 0x10007fff8000.
Proof.
  intros fs c p C P FLO FHI. pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  pose proof (gc_geo fs c p C P F0) as (_ & G2 & G3). pose proof (gc_pows c C) as (_ & _ & P6 & _ & P8 & PC).
  rewrite gc_shad_eq. pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR.
  remember (gframe fs c p) as F. remember (2 ^ c) as K. clear - FLOB FHI G2 G3 ATR P8 PC FB F0. lia.
Qed.

Section GEO.
Variables (fs c : Z).
Hypothesis C : 0 <= c < 11.
Hypothesis FLO : ablk fs (fs + 11571200).
Hypothesis FHI : fs + 11571200 <= ATOP.

Lemma gcW1_disj_in_fs : forall q A k, 0 <= q < gcN c -> fs <= A -> A + k <= fs + 11571200 -> 0 <= k ->
  (A + k <= gflag fs c q \/ gflag fs c q + 1 <= A) -> disjoint_from (gcW1 fs c q) A k.
Proof.
  intros q A k Q A0 A1 K NF. pose proof (gc_shad_off fs c q C Q FLO FHI) as (OFF & _ & _).
  cbn [gcW1 disjoint_from]. split; [exact NF|]. split; [lia| exact I].
Qed.
Lemma gcW1_disj_img : forall q A k, 0 <= q < gcN c -> A + k <= 0x62f000 -> disjoint_from (gcW1 fs c q) A k.
Proof.
  intros q A k Q A1. pose proof (gc_shad_off fs c q C Q FLO FHI) as (_ & LO & _).
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & _). unfold AIMG_HI in FLOL. pose proof (gc_geo fs c q C Q F0) as (G1 & _).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.
Lemma gcW1_disj_stack : forall q A k, 0 <= q < gcN c -> ATOP <= A -> disjoint_from (gcW1 fs c q) A k.
Proof.
  intros q A k Q A1. pose proof (gc_shad_off fs c q C Q FLO FHI) as (_ & _ & HI).
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & _). pose proof atop_range as ATR.
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.
Lemma gcW1_disj_shadow : forall q p, 0 <= q < gcN c -> 0 <= p < gcN c -> p <> q ->
  disjoint_from (gcW1 fs c q) (shad (gframe fs c p)) (8 * 2 ^ c).
Proof.
  intros q p Q P NE. pose proof (gc_shad_off fs c p C P FLO FHI) as (OFF & _ & _).
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & _).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [| exact I].
  destruct (Z.lt_ge_cases p q) as [LT|GE].
  - left. apply gc_shad_step; [exact C| lia].
  - right. apply gc_shad_step; [exact C| lia].
Qed.
End GEO.

Lemma gflag_sep : forall fs c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  gflag fs c' p + 1 <= gflag fs c q \/ gflag fs c q + 1 <= gflag fs c' p.
Proof.
  intros fs c q c' p C Q C' P NE. unfold gflag, gflags, gcN in *.
  destruct (Z.eq_dec c c') as [<-|NC]; [assert (q <> p) by congruence; lia|].
  pose proof (gc_pows c C) as (P14 & P15 & _). pose proof (gc_pows c' C') as (P14' & P15' & _).
  assert (MONO : forall a b, 0 <= a -> a < b -> b <= 14 -> 2 ^ (15 - b) <= 2 ^ (14 - a)) by (intros a b Ha Hab Hb; apply Z.pow_le_mono_r; lia).
  destruct (Z.lt_ge_cases c c').
  - pose proof (MONO c c' ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (MONO c' c ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma gframe_sep : forall fs c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  gframe fs c q + 2 ^ (6 + c) <= gframe fs c' p \/ gframe fs c' p + 2 ^ (6 + c') <= gframe fs c q.
Proof.
  intros fs c q c' p C Q C' P NE. unfold gframe, gcN in *.
  pose proof (gc_pows c C) as (P14 & _ & P6 & PM & _). pose proof (gc_pows c' C') as (P14' & _ & P6' & PM' & _).
  destruct (Z.eq_dec c c') as [<-|NC]; [assert (q <> p) by congruence; nia|]. nia.
Qed.

Lemma gshad_sep : forall fs c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  shad (gframe fs c q) + 8 * 2 ^ c <= shad (gframe fs c' p) \/ shad (gframe fs c' p) + 8 * 2 ^ c' <= shad (gframe fs c q).
Proof.
  intros fs c q c' p C Q C' P NE. rewrite !gc_shad_eq.
  pose proof (gc_pows c C) as (_ & _ & _ & _ & P8 & _). pose proof (gc_pows c' C') as (_ & _ & _ & _ & P8' & _).
  assert (DIV : forall F1 K F2, F1 + 8 * K <= F2 -> F1 / 8 + K <= F2 / 8).
  { intros F1 K F2 H. replace (F1 / 8 + K) with ((F1 + K * 8) / 8) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
  destruct (gframe_sep fs c q c' p C Q C' P NE) as [H|H].
  - left. rewrite P8 in H. pose proof (DIV _ _ _ H). lia.
  - right. rewrite P8' in H. pose proof (DIV _ _ _ H). lia.
Qed.

Section GEO2.
Variables (fs : Z).
Hypothesis FLO : ablk fs (fs + 11571200).
Hypothesis FHI : fs + 11571200 <= ATOP.
Lemma gcW1_disj_flag2 : forall c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  disjoint_from (gcW1 fs c q) (gflag fs c' p) 1.
Proof.
  intros c q c' p C Q C' P NE. pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _).
  pose proof (gc_geo fs c' p C' P F0) as (G1 & _). apply gcW1_disj_in_fs; try assumption; try lia.
  destruct (gflag_sep fs c q c' p C Q C' P NE); lia.
Qed.
Lemma gcW1_disj_shadow2 : forall c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  disjoint_from (gcW1 fs c q) (shad (gframe fs c' p)) (8 * 2 ^ c').
Proof.
  intros c q c' p C Q C' P NE. pose proof (gc_shad_off fs c' p C' P FLO FHI) as (OFF & _ & _).
  pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & _).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [| exact I].
  destruct (gshad_sep fs c q c' p C Q C' P NE); lia.
Qed.
End GEO2.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT}.

Definition gc_loop_post (ra gp tp t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (spf fs bot cur c : Z)
    (fl : Z -> byte) (rs : Z -> Z) (i : Z) (n : nat) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' a0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = gc_head 0x47f88 ra gp tp t0' t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c (gcN c) m'
    /\ munch (gcW fs c fl rs bot cur i n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ (forall p, i <= p < gcN c ->
          rw_cells asegs m' (gflag fs c p) [C1 (if gfreed bot cur (fl p) (rs p) then Z_to_bv 8 0 else fl p)]).

Lemma gc_class_loop : forall RNG (n : nat) (i : Z) ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem)
    (spf fs bot cur c : Z) (fl : Z -> byte) (rs : Z -> Z) (v0 fsz : word),
  Z.of_nat n = gcN c - i -> 0 <= i < gcN c ->
  mem_inv asegs m -> 0 <= c < 11 ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rt_shbase m -> rt_layout m ->
  rw_cells asegs m spf [C8 v0; C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 fsz] ->
  (forall p, i <= p < gcN c -> rw_cells asegs m (gflag fs c p) [C1 (fl p)]) ->
  (forall p, i <= p < gcN c -> bv_unsigned (fl p) <> 0 ->
       0 <= rs p < 2^64 /\ rw_cells asegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs p))]) ->
  (forall p, i <= p < gcN c -> gfreed bot cur (fl p) (rs p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells asegs m (shad (gframe fs c p)) (map C8 ws)) ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng_aimg RNG -> rng RNG spf 40 -> rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (gc_loop_post ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur c fl rs i n m)
    (gc_head 0x47ff8 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros RNG n. induction n as [|n IH]; intros until fsz;
    intros HN IR MI C FLO FHI FAL BOT CUR LOG SHB LAY FRM FL RS SH SPLO SPHI RIMG RSP RFS RSH; [lia|].
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  pose proof (gc_geo fs c i C IR F0) as (G1 & G2 & G3). pose proof (gc_pows c C) as (P14 & P15 & P6 & PM & P8 & PC).
  pose proof (FL i ltac:(lia)) as FLi.

  assert (CONT : forall t0' m1,
      munch (if gfreed bot cur (fl i) (rs i) then gcW1 fs c i else []) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
      rw_cells asegs m1 (gflag fs c i) [C1 (if gfreed bot cur (fl i) (rs i) then Z_to_bv 8 0 else fl i)] ->
      forall ms', gc_next0 ra gp tp t0' t1 t4 t5 t6 FR fc spf fs bot cur c i m1 ms' ->
      evtF asegs RNG (gc_loop_post ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur c fl rs i (S n) m) ms').
  { intros t0' m1 MUp WM1 MI1 FLi1 ms' NEXT.
    assert (MU1 : munch (gcW1 fs c i) m m1).
    { destruct (gfreed bot cur (fl i) (rs i)); [exact MUp|]. eapply munch_weaken; [|exact MUp]. intros x _. exact I. }
    destruct NEXT as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & [[LT ->] | [EQ ->]]).
    -
      eapply evtF_mono.
      { eapply (IH (i + 1)) with (m := m1) (fl := fl) (rs := rs); try eassumption; try lia.
        - eapply rw_cells_transport; [exact LOG| exact MU1| exact WM1|]. apply gcW1_disj_in_fs; try assumption; cbn; lia.
        - eapply rw_cells_transport; [exact SHB| exact MU1| exact WM1|]. apply gcW1_disj_img; try assumption; cbn; lia.
        - eapply rw_cells_transport; [exact LAY| exact MU1| exact WM1|]. apply gcW1_disj_img; try assumption; cbn; lia.
        - eapply rw_cells_transport; [exact FRM| exact MU1| exact WM1|]. apply gcW1_disj_stack; try assumption.
        - intros p Hp. eapply rw_cells_transport; [apply FL; lia| exact MU1| exact WM1|].
          pose proof (gc_geo fs c p C ltac:(lia) F0) as (Gp & _ & _).
          apply gcW1_disj_in_fs; try assumption; cbn; try lia. unfold gflag in *. lia.
        - intros p Hp NZp. destruct (RS p ltac:(lia) NZp) as (RSp & CELLp). split; [exact RSp|].
          eapply rw_cells_transport; [exact CELLp| exact MU1| exact WM1|].
          pose proof (gc_geo fs c p C ltac:(lia) F0) as (_ & Gp2 & Gp3).
          apply gcW1_disj_in_fs; try assumption; cbn; try lia.
        - intros p Hp FRp. destruct (SH p ltac:(lia) FRp) as (C2 & ws & LWS & CELLp). split; [exact C2|]. exists ws. split; [exact LWS|].
          eapply rw_cells_transport; [exact CELLp| exact MU1| exact WM1|].
          replace (Z.of_nat (cells_size (map C8 ws))) with (8 * 2 ^ c).
          + apply gcW1_disj_shadow; try assumption; lia.
          + assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
            { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
            rewrite CS, LWS, Z2Nat.id by lia. reflexivity. }
      cbv beta. intros ms' (t0'' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & m' & -> & MU2 & WM2 & MI2 & FLS).
      exists t0'', c0, c1, c2, c3, c4, c5, c6, c7, m'. split; [reflexivity|].
      split.
      { cbn [gcW]. eapply munch_trans.
        - eapply munch_weaken; [apply gc_sub_fp_app_l| exact MUp].
        - eapply munch_weaken; [apply gc_sub_fp_app_r| exact MU2]. }
      split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
      intros p Hp. destruct (Z.eq_dec p i) as [->|NE]; [| apply FLS; lia].
      eapply rw_cells_transport; [exact FLi1| exact MU2| exact WM2|].
      apply gcW_disjoint. intros q Hq _. apply gcW1_disj_in_fs; try assumption; cbn; try lia. unfold gflag. lia.
    -
      assert (n = 0)%nat by lia. subst n.
      apply evtF_done. exists t0', b0, b1, b2, b3, b4, b5, b6, b7, m1. rewrite EQ. split; [reflexivity|].
      split; [cbn [gcW]; rewrite app_nil_r; exact MUp|]. split; [exact WM1|]. split; [exact MI1|].
      intros p Hp. assert (p = i) by lia. subst p. exact FLi1. }
  destruct (Z.eq_dec (bv_unsigned (fl i)) 0) as [Z0|NZ].
  -
    assert (GF : gfreed bot cur (fl i) (rs i) = false) by (unfold gfreed; rewrite Z0; reflexivity).
    assert (E0 : fl i = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity).
    eapply evtF_cut.
    { eapply gc_iter_zero; try eassumption; try lia. rewrite <- E0. exact FLi. }
    cbv beta. intros ms' NEXT. eapply (CONT t0 m); try assumption.
    + rewrite GF. apply munch_refl.
    + apply wmono_refl.
    + rewrite GF. exact FLi.
  - destruct (RS i ltac:(lia) NZ) as (RSi & CELLi).
    destruct (gfreed bot cur (fl i) (rs i)) eqn:GF.
    +
      destruct (SH i ltac:(lia) GF) as (C2 & ws & LWS & SHWi).
      assert (FREE : bot < rs i < cur).
      { unfold gfreed in GF. apply andb_prop in GF. destruct GF as [GF1 GF3]. apply andb_prop in GF1. destruct GF1 as [_ GF2].
        apply Z.ltb_lt in GF2, GF3. lia. }
      eapply evtF_cut.
      { eapply gc_iter_free with (ws := ws); try eassumption; try lia. }
      cbv beta. intros ms' (t0' & m1 & NEXT & MU1 & WM1 & MI1 & FL0).
      eapply (CONT t0' m1); try assumption.
    +
      assert (KEEP : rs i <= bot \/ cur <= rs i).
      { unfold gfreed in GF. destruct (bv_unsigned (fl i) =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. cbn [negb andb] in GF.
        destruct (bot <? rs i) eqn:E1; [|apply Z.ltb_ge in E1; lia]. cbn [andb] in GF. apply Z.ltb_ge in GF. lia. }
      eapply evtF_cut.
      { eapply gc_iter_keep with (b := fl i) (rs := rs i); try eassumption; try lia. }
      cbv beta. intros ms' NEXT. eapply (CONT t0 m); try assumption.
      * apply munch_refl.
      * apply wmono_refl.
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import RtCells.TwinB AProto.TwinB ABase.TwinB F_tryinit.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB FsKit.TwinB AFake_gc.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma gc_disjoint_from_app : forall W1 W2 A k, disjoint_from W1 A k -> disjoint_from W2 A k -> disjoint_from (W1 ++ W2) A k.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; intros W2 A k H1 H2; [exact H2|]. destruct H1 as [H1 H1']. split; [exact H1| apply IH; assumption]. Qed.
Lemma gc_outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof. induction l1 as [|[lo hi] l1 IH]; cbn; intros l2 x; [tauto|]. rewrite IH. tauto. Qed.
Lemma gc_sub_fp_app_l : forall W1 W2, sub_fp W1 (W1 ++ W2).
Proof. intros W1 W2 x H. apply gc_outside_app in H. tauto. Qed.
Lemma gc_sub_fp_app_r : forall W1 W2, sub_fp W2 (W1 ++ W2).
Proof. intros W1 W2 x H. apply gc_outside_app in H. tauto. Qed.

Section CANSEC1. Context {rc : runConstT}.

Definition gfreed (bot cur : Z) (b : byte) (r : Z) : bool := negb (bv_unsigned b =? 0) && (bot <? r) && (r <? cur).

Definition gcW1 (fs c p : Z) : list (Z * Z) :=
  [(gflag fs c p, gflag fs c p + 1); (shad (gframe fs c p), shad (gframe fs c p) + 8 * 2 ^ c)].

Fixpoint gcW (fs c : Z) (fl : Z -> byte) (rs : Z -> Z) (bot cur : Z) (i : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => (if gfreed bot cur (fl i) (rs i) then gcW1 fs c i else []) ++ gcW fs c fl rs bot cur (i + 1) n'
  end.

Lemma gcW_disjoint : forall fs c fl rs bot cur A k n i,
  (forall p, i <= p < i + Z.of_nat n -> gfreed bot cur (fl p) (rs p) = true -> disjoint_from (gcW1 fs c p) A k) ->
  disjoint_from (gcW fs c fl rs bot cur i n) A k.
Proof.
  intros fs c fl rs bot cur A k n. induction n as [|n IH]; intros i H; cbn [gcW]; [exact I|].
  apply gc_disjoint_from_app.
  - destruct (gfreed bot cur (fl i) (rs i)) eqn:GF; [apply H; [lia| exact GF]| exact I].
  - apply IH. intros p Hp GF. apply H; [lia| exact GF].
Qed.

Lemma gc_pows : forall c, 0 <= c < 11 ->
  0 < 2 ^ (14 - c) <= 16384 /\ 2 ^ (15 - c) = 2 * 2 ^ (14 - c) /\ 64 <= 2 ^ (6 + c) /\ 2 ^ (14 - c) * 2 ^ (6 + c) = 1048576
  /\ 2 ^ (6 + c) = 8 * (8 * 2 ^ c) /\ 0 < 2 ^ c.
Proof.
  intros c C. split; [split; [apply Z.pow_pos_nonneg; lia| change 16384 with (2^14); apply Z.pow_le_mono_r; lia]|].
  split; [replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity|].
  split; [change 64 with (2^6); apply Z.pow_le_mono_r; lia|].
  split; [rewrite <- Z.pow_add_r by lia; replace (14 - c + (6 + c)) with 20 by lia; reflexivity|].
  split; [rewrite Z.pow_add_r by lia; change (2^6) with 64; lia| apply Z.pow_pos_nonneg; lia].
Qed.

Lemma gc_geo : forall fs c p, 0 <= c < 11 -> 0 <= p < gcN c -> 0 <= fs ->
  fs + 4096 <= gflag fs c p < fs + 36864
  /\ fs + 36864 <= gframe fs c p /\ gframe fs c p + 2 ^ (6 + c) <= fs + 11571200.
Proof.
  intros fs c p C P F0. unfold gflag, gflags, gframe, gcN in *.
  pose proof (gc_pows c C) as (P14 & P15 & P6 & PM & _ & _). split; [lia|]. split; [nia|nia].
Qed.

Lemma gc_shad_eq : forall x, shad x = 0x7fff8000 + x / 8.
Proof. intros x. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma gc_shad_step : forall fs c p q, 0 <= c < 11 -> 0 <= p < q ->
  shad (gframe fs c p) + 8 * 2 ^ c <= shad (gframe fs c q).
Proof.
  intros fs c p q C PQ. rewrite !gc_shad_eq. unfold gframe.
  pose proof (gc_pows c C) as (_ & _ & _ & _ & P8 & PC).
  replace (fs + 36864 + c * 1048576 + q * 2 ^ (6 + c)) with (fs + 36864 + c * 1048576 + p * 2 ^ (6 + c) + ((q - p) * (8 * 2 ^ c)) * 8) by (rewrite P8; ring).
  rewrite Z.div_add by lia. nia.
Qed.

Lemma gc_shad_off : forall fs c p, 0 <= c < 11 -> 0 <= p < gcN c ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP ->
  (shad (gframe fs c p) + 8 * 2 ^ c <= fs \/ fs + 11571200 <= shad (gframe fs c p))
  /\ 0x7fff8000 <= shad (gframe fs c p) /\ shad (gframe fs c p) + 8 * 2 ^ c <= 0x10007fff8000.
Proof.
  intros fs c p C P FLO FHI. pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  pose proof (gc_geo fs c p C P F0) as (_ & G2 & G3). pose proof (gc_pows c C) as (_ & _ & P6 & _ & P8 & PC).
  rewrite gc_shad_eq. pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR.
  remember (gframe fs c p) as F. remember (2 ^ c) as K. clear - FLOB FHI G2 G3 ATR P8 PC FB F0. lia.
Qed.

Section GEO.
Variables (fs c : Z).
Hypothesis C : 0 <= c < 11.
Hypothesis FLO : ablk fs (fs + 11571200).
Hypothesis FHI : fs + 11571200 <= ATOP.

Lemma gcW1_disj_in_fs : forall q A k, 0 <= q < gcN c -> fs <= A -> A + k <= fs + 11571200 -> 0 <= k ->
  (A + k <= gflag fs c q \/ gflag fs c q + 1 <= A) -> disjoint_from (gcW1 fs c q) A k.
Proof.
  intros q A k Q A0 A1 K NF. pose proof (gc_shad_off fs c q C Q FLO FHI) as (OFF & _ & _).
  cbn [gcW1 disjoint_from]. split; [exact NF|]. split; [lia| exact I].
Qed.
Lemma gcW1_disj_img : forall q A k, 0 <= q < gcN c -> A + k <= 0x631000 -> disjoint_from (gcW1 fs c q) A k.
Proof.
  intros q A k Q A1. pose proof (gc_shad_off fs c q C Q FLO FHI) as (_ & LO & _).
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & _). unfold AIMG_HI in FLOL. pose proof (gc_geo fs c q C Q F0) as (G1 & _).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.
Lemma gcW1_disj_stack : forall q A k, 0 <= q < gcN c -> ATOP <= A -> disjoint_from (gcW1 fs c q) A k.
Proof.
  intros q A k Q A1. pose proof (gc_shad_off fs c q C Q FLO FHI) as (_ & _ & HI).
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & _). pose proof atop_range as ATR.
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.
Lemma gcW1_disj_shadow : forall q p, 0 <= q < gcN c -> 0 <= p < gcN c -> p <> q ->
  disjoint_from (gcW1 fs c q) (shad (gframe fs c p)) (8 * 2 ^ c).
Proof.
  intros q p Q P NE. pose proof (gc_shad_off fs c p C P FLO FHI) as (OFF & _ & _).
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & _).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [| exact I].
  destruct (Z.lt_ge_cases p q) as [LT|GE].
  - left. apply gc_shad_step; [exact C| lia].
  - right. apply gc_shad_step; [exact C| lia].
Qed.
End GEO.

Lemma gflag_sep : forall fs c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  gflag fs c' p + 1 <= gflag fs c q \/ gflag fs c q + 1 <= gflag fs c' p.
Proof.
  intros fs c q c' p C Q C' P NE. unfold gflag, gflags, gcN in *.
  destruct (Z.eq_dec c c') as [<-|NC]; [assert (q <> p) by congruence; lia|].
  pose proof (gc_pows c C) as (P14 & P15 & _). pose proof (gc_pows c' C') as (P14' & P15' & _).
  assert (MONO : forall a b, 0 <= a -> a < b -> b <= 14 -> 2 ^ (15 - b) <= 2 ^ (14 - a)) by (intros a b Ha Hab Hb; apply Z.pow_le_mono_r; lia).
  destruct (Z.lt_ge_cases c c').
  - pose proof (MONO c c' ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (MONO c' c ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma gframe_sep : forall fs c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  gframe fs c q + 2 ^ (6 + c) <= gframe fs c' p \/ gframe fs c' p + 2 ^ (6 + c') <= gframe fs c q.
Proof.
  intros fs c q c' p C Q C' P NE. unfold gframe, gcN in *.
  pose proof (gc_pows c C) as (P14 & _ & P6 & PM & _). pose proof (gc_pows c' C') as (P14' & _ & P6' & PM' & _).
  destruct (Z.eq_dec c c') as [<-|NC]; [assert (q <> p) by congruence; nia|]. nia.
Qed.

Lemma gshad_sep : forall fs c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  shad (gframe fs c q) + 8 * 2 ^ c <= shad (gframe fs c' p) \/ shad (gframe fs c' p) + 8 * 2 ^ c' <= shad (gframe fs c q).
Proof.
  intros fs c q c' p C Q C' P NE. rewrite !gc_shad_eq.
  pose proof (gc_pows c C) as (_ & _ & _ & _ & P8 & _). pose proof (gc_pows c' C') as (_ & _ & _ & _ & P8' & _).
  assert (DIV : forall F1 K F2, F1 + 8 * K <= F2 -> F1 / 8 + K <= F2 / 8).
  { intros F1 K F2 H. replace (F1 / 8 + K) with ((F1 + K * 8) / 8) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
  destruct (gframe_sep fs c q c' p C Q C' P NE) as [H|H].
  - left. rewrite P8 in H. pose proof (DIV _ _ _ H). lia.
  - right. rewrite P8' in H. pose proof (DIV _ _ _ H). lia.
Qed.

Section GEO2.
Variables (fs : Z).
Hypothesis FLO : ablk fs (fs + 11571200).
Hypothesis FHI : fs + 11571200 <= ATOP.
Lemma gcW1_disj_flag2 : forall c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  disjoint_from (gcW1 fs c q) (gflag fs c' p) 1.
Proof.
  intros c q c' p C Q C' P NE. pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _).
  pose proof (gc_geo fs c' p C' P F0) as (G1 & _). apply gcW1_disj_in_fs; try assumption; try lia.
  destruct (gflag_sep fs c q c' p C Q C' P NE); lia.
Qed.
Lemma gcW1_disj_shadow2 : forall c q c' p, 0 <= c < 11 -> 0 <= q < gcN c -> 0 <= c' < 11 -> 0 <= p < gcN c' -> (c, q) <> (c', p) ->
  disjoint_from (gcW1 fs c q) (shad (gframe fs c' p)) (8 * 2 ^ c').
Proof.
  intros c q c' p C Q C' P NE. pose proof (gc_shad_off fs c' p C' P FLO FHI) as (OFF & _ & _).
  pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & _).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [| exact I].
  destruct (gshad_sep fs c q c' p C Q C' P NE); lia.
Qed.
End GEO2.
End CANSEC1.

Section CANSEC2. Context {rc : runConstT}.

Definition gc_loop_post (ra gp tp t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (spf fs bot cur c : Z)
    (fl : Z -> byte) (rs : Z -> Z) (i : Z) (n : nat) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' a0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = gc_head 0x48918 ra gp tp t0' t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c (gcN c) m'
    /\ munch (gcW fs c fl rs bot cur i n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ (forall p, i <= p < gcN c ->
          rw_cells bsegs m' (gflag fs c p) [C1 (if gfreed bot cur (fl p) (rs p) then Z_to_bv 8 0 else fl p)]).

Lemma gc_class_loop : forall RNG (n : nat) (i : Z) ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem)
    (spf fs bot cur c : Z) (fl : Z -> byte) (rs : Z -> Z) (v0 fsz : word),
  Z.of_nat n = gcN c - i -> 0 <= i < gcN c ->
  mem_inv bsegs m -> 0 <= c < 11 ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rt_shbase m -> rt_layout m ->
  rw_cells bsegs m spf [C8 v0; C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 fsz] ->
  (forall p, i <= p < gcN c -> rw_cells bsegs m (gflag fs c p) [C1 (fl p)]) ->
  (forall p, i <= p < gcN c -> bv_unsigned (fl p) <> 0 ->
       0 <= rs p < 2^64 /\ rw_cells bsegs m (gframe fs c p + 24) [C8 (Z_to_bv 64 (rs p))]) ->
  (forall p, i <= p < gcN c -> gfreed bot cur (fl p) (rs p) = true ->
       c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells bsegs m (shad (gframe fs c p)) (map C8 ws)) ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng_aimg RNG -> rng RNG spf 40 -> rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (gc_loop_post ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur c fl rs i n m)
    (gc_head 0x48988 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros RNG n. induction n as [|n IH]; intros until fsz;
    intros HN IR MI C FLO FHI FAL BOT CUR LOG SHB LAY FRM FL RS SH SPLO SPHI RIMG RSP RFS RSH; [lia|].
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  pose proof (gc_geo fs c i C IR F0) as (G1 & G2 & G3). pose proof (gc_pows c C) as (P14 & P15 & P6 & PM & P8 & PC).
  pose proof (FL i ltac:(lia)) as FLi.

  assert (CONT : forall t0' m1,
      munch (if gfreed bot cur (fl i) (rs i) then gcW1 fs c i else []) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
      rw_cells bsegs m1 (gflag fs c i) [C1 (if gfreed bot cur (fl i) (rs i) then Z_to_bv 8 0 else fl i)] ->
      forall ms', gc_next0 ra gp tp t0' t1 t4 t5 t6 FR fc spf fs bot cur c i m1 ms' ->
      evtF bsegs RNG (gc_loop_post ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur c fl rs i (S n) m) ms').
  { intros t0' m1 MUp WM1 MI1 FLi1 ms' NEXT.
    assert (MU1 : munch (gcW1 fs c i) m m1).
    { destruct (gfreed bot cur (fl i) (rs i)); [exact MUp|]. eapply munch_weaken; [|exact MUp]. intros x _. exact I. }
    destruct NEXT as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & [[LT ->] | [EQ ->]]).
    -
      eapply evtF_mono.
      { eapply (IH (i + 1)) with (m := m1) (fl := fl) (rs := rs); try eassumption; try lia.
        - eapply rw_cells_transport; [exact LOG| exact MU1| exact WM1|]. apply gcW1_disj_in_fs; try assumption; cbn; lia.
        - eapply rw_cells_transport; [exact SHB| exact MU1| exact WM1|]. apply gcW1_disj_img; try assumption; cbn; lia.
        - eapply rw_cells_transport; [exact LAY| exact MU1| exact WM1|]. apply gcW1_disj_img; try assumption; cbn; lia.
        - eapply rw_cells_transport; [exact FRM| exact MU1| exact WM1|]. apply gcW1_disj_stack; try assumption.
        - intros p Hp. eapply rw_cells_transport; [apply FL; lia| exact MU1| exact WM1|].
          pose proof (gc_geo fs c p C ltac:(lia) F0) as (Gp & _ & _).
          apply gcW1_disj_in_fs; try assumption; cbn; try lia. unfold gflag in *. lia.
        - intros p Hp NZp. destruct (RS p ltac:(lia) NZp) as (RSp & CELLp). split; [exact RSp|].
          eapply rw_cells_transport; [exact CELLp| exact MU1| exact WM1|].
          pose proof (gc_geo fs c p C ltac:(lia) F0) as (_ & Gp2 & Gp3).
          apply gcW1_disj_in_fs; try assumption; cbn; try lia.
        - intros p Hp FRp. destruct (SH p ltac:(lia) FRp) as (C2 & ws & LWS & CELLp). split; [exact C2|]. exists ws. split; [exact LWS|].
          eapply rw_cells_transport; [exact CELLp| exact MU1| exact WM1|].
          replace (Z.of_nat (cells_size (map C8 ws))) with (8 * 2 ^ c).
          + apply gcW1_disj_shadow; try assumption; lia.
          + assert (CS : forall l : list word, Z.of_nat (cells_size (map C8 l)) = 8 * Z.of_nat (length l)).
            { induction l as [|w l IHl]; [reflexivity|]. cbn [map cells_size csize length]. rewrite Nat2Z.inj_add, IHl. lia. }
            rewrite CS, LWS, Z2Nat.id by lia. reflexivity. }
      cbv beta. intros ms' (t0'' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & m' & -> & MU2 & WM2 & MI2 & FLS).
      exists t0'', c0, c1, c2, c3, c4, c5, c6, c7, m'. split; [reflexivity|].
      split.
      { cbn [gcW]. eapply munch_trans.
        - eapply munch_weaken; [apply gc_sub_fp_app_l| exact MUp].
        - eapply munch_weaken; [apply gc_sub_fp_app_r| exact MU2]. }
      split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
      intros p Hp. destruct (Z.eq_dec p i) as [->|NE]; [| apply FLS; lia].
      eapply rw_cells_transport; [exact FLi1| exact MU2| exact WM2|].
      apply gcW_disjoint. intros q Hq _. apply gcW1_disj_in_fs; try assumption; cbn; try lia. unfold gflag. lia.
    -
      assert (n = 0)%nat by lia. subst n.
      apply evtF_done. exists t0', b0, b1, b2, b3, b4, b5, b6, b7, m1. rewrite EQ. split; [reflexivity|].
      split; [cbn [gcW]; rewrite app_nil_r; exact MUp|]. split; [exact WM1|]. split; [exact MI1|].
      intros p Hp. assert (p = i) by lia. subst p. exact FLi1. }
  destruct (Z.eq_dec (bv_unsigned (fl i)) 0) as [Z0|NZ].
  -
    assert (GF : gfreed bot cur (fl i) (rs i) = false) by (unfold gfreed; rewrite Z0; reflexivity).
    assert (E0 : fl i = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity).
    eapply evtF_cut.
    { eapply gc_iter_zero; try eassumption; try lia. rewrite <- E0. exact FLi. }
    cbv beta. intros ms' NEXT. eapply (CONT t0 m); try assumption.
    + rewrite GF. apply munch_refl.
    + apply wmono_refl.
    + rewrite GF. exact FLi.
  - destruct (RS i ltac:(lia) NZ) as (RSi & CELLi).
    destruct (gfreed bot cur (fl i) (rs i)) eqn:GF.
    +
      destruct (SH i ltac:(lia) GF) as (C2 & ws & LWS & SHWi).
      assert (FREE : bot < rs i < cur).
      { unfold gfreed in GF. apply andb_prop in GF. destruct GF as [GF1 GF3]. apply andb_prop in GF1. destruct GF1 as [_ GF2].
        apply Z.ltb_lt in GF2, GF3. lia. }
      eapply evtF_cut.
      { eapply gc_iter_free with (ws := ws); try eassumption; try lia. }
      cbv beta. intros ms' (t0' & m1 & NEXT & MU1 & WM1 & MI1 & FL0).
      eapply (CONT t0' m1); try assumption.
    +
      assert (KEEP : rs i <= bot \/ cur <= rs i).
      { unfold gfreed in GF. destruct (bv_unsigned (fl i) =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. cbn [negb andb] in GF.
        destruct (bot <? rs i) eqn:E1; [|apply Z.ltb_ge in E1; lia]. cbn [andb] in GF. apply Z.ltb_ge in GF. lia. }
      eapply evtF_cut.
      { eapply gc_iter_keep with (b := fl i) (rs := rs i); try eassumption; try lia. }
      cbv beta. intros ms' NEXT. eapply (CONT t0 m); try assumption.
      * apply munch_refl.
      * apply wmono_refl.
Qed.
End CANSEC2.
End TwinB.
