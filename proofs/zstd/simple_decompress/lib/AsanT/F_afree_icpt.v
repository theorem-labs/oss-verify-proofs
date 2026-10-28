(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_apoison F_aalloc_s F_aalloc1 F_afree_iseg F_afree_front F_afree_tail.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.


Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_of_u64arr : forall m A ws,
  u64arr bsegs m A ws -> rw_cells bsegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [B W]. split; [split|].
  - cbn. split; [apply u64s_length| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

(* [comment removed for export] *)
Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => 0x1618a8 <= fst iv \/ (0xd09fc <= fst iv /\ snd iv <= 0x1618a0) \/ snd iv <= 0xc72f8) W -> poison_cells m'.   (* [comment removed for export] *)
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0xc72f8 <= A -> (A + n <= 0xd09fc \/ (0x1618a0 <= A /\ A + n <= 0x1618a8)) -> disjoint_from W A n).
  { intros A n HA HB. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition ek_seps (ek : enq_kind) (L : alayout) (hm lst : Z) : Prop :=
  match ek with
  | EkAppend _ _ _ _ _ _ _ _ =>
         (hm + 24 <= lst \/ lst + 8192 <= hm)
      /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  | EkNew full _ _ _ _ _ _ _ _ _ b _ =>
         (hm + 24 <= b \/ b + 8192 <= hm)
      /\ (al_nodes L + 1048576 <= b \/ b + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= b \/ b + 8192 <= al_store L)
      /\ (full = true ->
             (hm + 24 <= lst \/ lst + 8192 <= hm)
          /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L))
  end.

Definition dk_seps (g : gqd) (L : alayout) (hm : Z) : Prop :=
  g_drain g = true -> g_full g = true ->
     (hm + 24 <= g_lst g \/ g_lst g + 8 <= hm)
  /\ (al_nodes L + 1048576 <= g_lst g \/ g_lst g + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= g_lst g \/ g_lst g + 8192 <= al_store L).

(* [comment removed for export] *)
Lemma ek_pre_pure : forall ek RNG L t nb lst n hm m,
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
     (hm + 24 <= lst \/ lst + 8192 <= hm) /\ (hm + 24 <= ek_b ek lst \/ ek_b ek lst + 8192 <= hm)
  /\ (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) /\ (t + 4096 <= ek_b ek lst \/ ek_b ek lst + 8192 <= t)
  /\ (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L)
  /\ (al_nodes L + 1048576 <= ek_b ek lst \/ ek_b ek lst + 8192 <= al_nodes L) /\ (al_store L + 8388608 <= ek_b ek lst \/ ek_b ek lst + 8192 <= al_store L)
  /\ 0 <= lst /\ lst + 8192 <= ATOP /\ 0 <= ek_b ek lst /\ ek_b ek lst + 8192 <= ATOP
  /\ (lst = 0 \/ 0x10007fff8000 <= lst) /\ 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG L t nb lst n hm m EK ES T0 H0 N0 R0. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_seps ek_b] in *.
  - destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & LJ & L0 & L1 & DTL & DHL & CR' & STS' & RL). atop_facts. lia.
  - destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & BJ & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB).
    destruct ES as (S1 & S2 & S3 & S4). atop_facts.
    destruct full; [destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL); specialize (S4 eq_refl) | destruct FULL as [NB0 LST0]]; lia.
Qed.

Lemma dk_pre_pure : forall ek g RNG L t lst hm qb' m,
  dk_pre ek g RNG t lst hm qb' m -> dk_seps g L hm ->
  iclr t 4096 -> AIMG_HI <= hm -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->
  (hm + 24 <= lst \/ lst + 8192 <= hm) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) ->
  (al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
  0 <= lst -> lst + 8192 <= ATOP -> (lst = 0 \/ 0x10007fff8000 <= lst) ->
     (hm + 24 <= dk_glst g lst \/ dk_glst g lst + 8 <= hm) /\ (t + 4096 <= dk_glst g lst \/ dk_glst g lst + 8 <= t)
  /\ (al_nodes L + 1048576 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_nodes L) /\ (al_store L + 8388608 <= dk_glst g lst \/ dk_glst g lst + 8 <= al_store L)
  /\ 0 <= dk_glst g lst /\ dk_glst g lst + 8 <= ATOP /\ (dk_glst g lst = 0 \/ 0x10007fff8000 <= dk_glst g lst).
Proof.
  intros ek g RNG L t lst hm qb' m DK DS T0 H0 N0 R0 P1 P3 P5 P6 LNN LHI LZH. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  unfold dk_pre, dk_seps, dk_glst in *.
  destruct DK as (MX & GC & GNB & GQB & GFST & GLST & DK').
  destruct (g_drain g); [| lia].
  destruct DK' as (QB1 & GQ & GFULL).
  destruct (g_full g); [destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9); specialize (DS eq_refl eq_refl) | destruct GFULL as [GNB0 GLST0]];
    atop_facts; lia.
Qed.

(* [comment removed for export] *)
Lemma outside_In : forall W x jv, outside W x -> In jv W -> ~ (fst jv <= x < snd jv).
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x jv Ho Hin; [tauto|].
  destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1| exact (IH _ _ H2 Hin)].
Qed.
Lemma sub_fp_by_incl : forall W W',
  Forall (fun iv => Exists (fun jv => fst jv <= fst iv /\ snd iv <= snd jv) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x Ho. induction HF as [|[lo hi] W HE HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply Exists_exists in HE. destruct HE as (jv & Hin & H1 & H2). cbn in H1, H2.
  pose proof (outside_In W' x jv Ho Hin). lia.
Qed.
(* [comment removed for export] *)
End CANSEC1.
Ltac find_iv s :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear - s; lia]
        | apply Exists_cons_tl; find_iv s ].
Ltac solve_sub_fp s :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_iv s|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac reasm :=
  repeat (lazymatch goal with
          | |- rng _ _ _ => assumption
          | |- ex _ => eexists; eassumption
          | |- _ /\ _ => first [assumption | split; [first [assumption | lia | eexists; eassumption] | ]]
          | |- _ => first [assumption | lia | exact I]
          end).

Section CANSEC2. Context {rc : runConstT}.
Section Transport.
(* [comment removed for export] *)
Variables (L : alayout) (sp : word) (t hm lo : Z) (m m' : amem).
Hypothesis MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (0x1a1bc8, 0x5f1c10); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'.
Hypothesis WM : wmono bsegs m m'.
Hypotheses (CEIL : ATOP <= lo) (LO : lo <= bv_unsigned sp - 4096) (T0 : iclr t 4096) (T1 : t + 4096 <= ATOP)     (* [comment removed for export] *)
           (H0 : AIMG_HI <= hm) (DHT : hm + 24 <= t \/ t + 4096 <= hm) (N0 : AIMG_HI <= al_nodes L) (R0 : AIMG_HI <= al_store L)
           (DTN : t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) (DTS : t + 4096 <= al_store L \/ al_store L + 8388608 <= t).

Lemma ek_pre_front : forall ek RNG nb lst n,
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst -> ek_pre ek RNG t nb lst n hm m'.
Proof.
  intros ek RNG nb lst n EK ES. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_seps] in *.
  - destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & [junkt LJ] & L0 & L1 & DTL & DHL & CR' & STS' & RL). atop_facts.
    destruct ES as (S1 & S2 & S3).
    xport LB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S1 S2 S3; lia). xport LA MU WM ltac:(rewrite LEN; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL CNT S1 S2 S3; lia). xport LJ MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL CNT S1 S2 S3; lia).   (* [comment removed for export] *)
    xport CR' MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport STS' MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia).
    reasm.
  - destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & [junkb BJ] & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB).
    destruct ES as (S1 & S2 & S3 & S4). atop_facts.
    xport SB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport CR MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport CH MU WM ltac:(rewrite LCH; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport STS MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS; lia). xport BJ MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS B0 BL1 DTB DHB S1 S2 S3; lia).
    split.
    + destruct full; [| exact FULL]. destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1 & LA0 & LEN0 & RL). specialize (S4 eq_refl). destruct S4 as (S5 & S6 & S7).
      xport LB MU WM ltac:(clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S5 S6 S7; lia). xport LA0 MU WM ltac:(rewrite LEN0; clear -CEIL LO T0 T1 H0 DHT N0 R0 DTN DTS L0 L1 DTL DHL S5 S6 S7; lia). reasm.
    + reasm.
Qed.

Lemma dk_pre_front : forall ek g RNG lst qb',
  dk_pre ek g RNG t lst hm qb' m -> dk_seps g L hm -> dk_pre ek g RNG t lst hm qb' m'.
Proof.
  intros ek g RNG lst qb' DK DS. unfold AIMG_HI in *. band_lin.   (* [comment removed for export] *)
  unfold dk_pre, dk_seps in *.
  destruct DK as (MX & GC & GNB & GQB & GFST & GLST & DK').
  xport MX MU WM ltac:(lia). xport GC MU WM ltac:(lia).
  do 6 (split; [assumption|]).
  destruct (g_drain g); [| exact DK'].
  destruct DK' as (QB1 & GQ & GFULL). split; [exact QB1|]. split; [exact GQ|].
  destruct (g_full g); [| exact GFULL].
  destruct GFULL as (G1 & GLB & G3 & G4 & G5 & G6 & G7 & G8 & G9). specialize (DS eq_refl eq_refl). destruct DS as (D1 & D2 & D3). atop_facts.
  xport GLB MU WM ltac:(lia). reasm.
Qed.
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

Notation free_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Definition free_fast_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (free_W L sp t hm n lst ek g) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' (t + 80) (tcache_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n))
    /\ ek_post ek t lst hm n m'
    /\ dk_post g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x15f788 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xd0f00 (0xd0f00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

Lemma free_fast_spec : forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xd09fc [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x16184a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xc72e8 [C8 (Z_to_bv 64 0x15f7a0)] -> rw_cells bsegs m 0x15f7a0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0x1617c8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xcc9b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xc7300 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xcd524 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x15f788 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xd0f00 (0xd0f00 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  (* [comment removed for export] *)
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  (* [comment removed for export] *)
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF bsegs RNG (free_fast_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until trt.
  intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
         CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC EK ES DK DS DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
         UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI.
  band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_lin. band_int C0. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
  pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
  pose proof PC as PC'. destruct PC' as (GOT6 & _).
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148256256 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. atop_facts. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (ek_pre_pure ek RNG L t nb lst n hm m EK ES TI ltac:(unfold AIMG_HI; lia) NI SI)
    as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PL0 & PL1 & PB0 & PB1 & PL2 & PB2).
  pose proof (dk_pre_pure ek g RNG L t lst hm (qb + ek_delta ek n) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI PF1 PF3 PF5 PF6 PL0 PL1 PL2)
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  pose proof (qsz_int lst PL0 ltac:(clear -PL1; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).   (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
  box PF1. box PF2. box PF3. box PF4. box PF5. box PF6. box PF7. box PF8. box DF1. box DF2. box DF3. box DF4. box PL2. box DG2.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              t ctx hm n b1 actx lo top bot uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => exact AC
         | |- ADEPOT _ _ _ => exact DEP
         | |- afree_unw _ _ _ _ _ _ => exact UNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
         | |- rw_cells _ _ (_ + 16) _ => exact HUW
         | |- rw_cells _ _ (_ + 8) _ => exact CT8
         | |- rw_cells _ _ (_ + 40) _ => exact SW
         | |- rw_cells _ _ (_ + 3168) _ => exact UW
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).
  (* [comment removed for export] *)
  xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
  xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
  xport SH MUf WMf ltac:(band_disj).   (* [comment removed for export] *)
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (EK1 : ek_pre ek RNG t nb lst n hm m1).
  { eapply (ek_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact EK | exact ES]. }
  assert (DK1 : dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m1).
  { eapply (dk_pre_front L sp t hm lo m m1); [exact MUf | exact WMf | ..]; try (unfold AIMG_HI; lia).
    all: first [exact TI | unboxed DHT | unboxed DTN | unboxed DTS | exact DK | exact DS]. }
  clear EK DK PC.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply evtF_cut.
  { eapply (put_tail_spec ek g t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo sjunk).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite Hsp; exact STf
         | |- mem_inv _ _ => exact MIf
         | |- poison_cells _ => exact PC1
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK1
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK1
         | |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
         | |- _ \/ _ => ub DHT; lia
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- iclr _ _ => exact TI
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMP" G end. }
  cbv beta. intros ms2 PP. unfold put_tail_post in PP.
  destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).
  unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
  replace (ret_pc (Z_to_bv 64 348276)) with (Z_to_bv 64 348276) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FC1 MUp WMp ltac:(ub DHT; ub PF1; ub PF2; ub DF1; lia).
  xport STATS1 MUp WMp ltac:(rewrite LSJ1; ub PF3; ub PF4; ub DF2; lia).
  xport UW1 MUp WMp ltac:(ub PF3; ub PF4; ub DF2; lia).
  xport FL1 MUp WMp ltac:(ub PL2; ub DG2; lia). xport IAS1 MUp WMp ltac:(ub PL2; ub DG2; lia).
  xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub PL2; ub DG2; lia). }
  clear IAM1.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia | ub PF5; ub PF6; ub PL2; lia | ub PF7; ub PF8; lia | ub DF3; ub DF4; ub DG2; lia] |]); apply Forall_nil). }
  clear DEP1.
  (* [comment removed for export] *)
  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB1 | reflexivity]
      | exact FRS1 | exact RIMG | solve_rng ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  assert (MU : munch (free_W L sp t hm n lst ek g) m m2).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
    eapply munch_weaken; [| exact MUf].
    all: solve_sub_fp sp. }
  assert (WM : wmono bsegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
  unfold free_fast_post. exists id. do 15 eexists. exists m2, sj1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
  split; [exact HD2|]. split; [exact FC1|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact STf; try exact STp.
Qed.
End WithDepot.
End CANSEC2.
