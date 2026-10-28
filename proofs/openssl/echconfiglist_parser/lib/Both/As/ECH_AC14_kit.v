(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 SecLazy ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C10 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AStmt_C14 ECH_ALibMF ECH_ALibMid ECH_AKit ECH_AsKit
  ECH_AC1_malloc ECH_AC1_zalloc ECH_AC1_free ECH_AC1_dup ECH_AC5_small ECH_AC5_new ECH_AC5_push ECH_AC5_popfree ECH_AC10
  ECH_AC13_small ECH_AC13_ext ECH_AC13_entry ECH_AC12_addstr ECH_ARostr ECH_AC11_fail.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma sk_grow_le : forall c, 0 <= c -> 0 <= sk_grow c <= 2 * c /\ 5 * sk_grow c <= 8 * c.
Proof. intros c Hc. unfold sk_grow. Z.div_mod_to_equations. lia. Qed.

Section G.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Lemma amemflag_same : forall m m', MEMFLAG m 1 -> MEMFLAG m' 1 ->
    m' (wa A_mem_inited) = m (wa A_mem_inited) /\ (wview asegs m (wa A_mem_inited) <> None -> wview asegs m' (wa A_mem_inited) <> None).
  Proof.
    intros m m' (fb & [[_ (_ & _ & B1)] _] & V1 & _) (fb' & [[_ (_ & _ & B2)] (_ & _ & W2)] & V2 & _).
    cbn [cells_bytes cbytes app length cells_size csize Nat.add] in *.
    specialize (B1 0%nat ltac:(lia)). specialize (B2 0%nat ltac:(lia)). cbn [nth_error Z.of_nat] in B1, B2.
    replace (A_mem_inited + 0) with A_mem_inited in B1, B2 by lia.
    assert (ROM : seg_rom asegs (wa A_mem_inited) = Some (b8 0)) by (vm_compute; reflexivity).
    assert (E : fb = fb') by (rewrite (byte_eq_of_unsigned fb 1 V1), (byte_eq_of_unsigned fb' 1 V2); reflexivity). subst fb'.
    unfold mrd in B1, B2. split.
    - destruct (m (wa A_mem_inited)) as [x1|]; destruct (m' (wa A_mem_inited)) as [x2|].
      + injection B1 as ->. injection B2 as ->. reflexivity.
      + exfalso. rewrite ROM in B2. injection B2 as <-. vm_compute in V1. clear - V1. lia.
      + exfalso. rewrite ROM in B1. injection B1 as <-. vm_compute in V1. clear - V1. lia.
      + reflexivity.
    - intros _. specialize (W2 0 ltac:(lia)). replace (A_mem_inited + 0) with A_mem_inited in W2 by lia. exact W2.
  Qed.
  Lemma axpres_drop_memflag : forall L SP X1 X2 m m',
    MEMFLAG m 1 -> MEMFLAG m' 1 -> xpres H L SP (X1 ++ memflag_foot ++ X2) m m' -> xpres H L SP (X1 ++ X2) m m'.
  Proof.
    intros L SP X1 X2 m m' MF MF' XP a Ha [HC HX].
    destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply amemflag_same; assumption|].
    apply XP; [exact Ha|]. split; [exact HC|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [apply HX; apply rin_ivs_app; left; exact K|].
    apply rin_ivs_app in K. destruct K as [K|K]; [| apply HX; apply rin_ivs_app; right; exact K].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia.
  Qed.

  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Lemma chain_via_xpres_off : forall LB SP X m m' cur CH,
    as_chain H m cur CH -> xpres H LB SP X m m' -> (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) ->
    Forall (fun iv : Z * Z => snd iv <= aceil \/ offchain CH (fst iv) (snd iv - fst iv)) X -> as_chain H m' cur CH.
  Proof.
    intros LB SP X m m' cur CH C XP HS FX. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3).
    apply XP; [acb; lia|]. split; [left; lia|].
    clear - FX Ha R1 IN. induction X as [|[l h] X IH]; [intros K; exact K|]. cbn. intros [K|K].
    - pose proof (Forall_inv FX) as F1. cbn in F1. destruct F1 as [F1|F1]; [lia|]. specialize (F1 _ _ IN). lia.
    - exact (IH (Forall_inv_tail FX) K).
  Qed.
  (* [comment removed for export] *)
  Lemma aCf0 : as_Cf H 0 = 0.
  Proof.
    pose proof (ah_costs H HH) as (_ & _ & F0 & _ & _ & SF). pose proof (F0 0 ltac:(lia)) as K1. pose proof (SF 0 0 ltac:(lia) ltac:(lia)) as K2. rewrite Z.add_0_r in K2. lia.
  Qed.
  Lemma aCm_mono : forall a b, 0 <= a <= b -> as_Cm H a <= as_Cm H b.
  Proof. intros a b Hab. exact (proj1 (proj2 (ah_costs H HH)) a b Hab). Qed.
  Lemma aCf_mono : forall a b, 0 <= a <= b -> as_Cf H a <= as_Cf H b.
  Proof. intros a b Hab. exact (proj1 (proj2 (proj2 (proj2 (ah_costs H HH)))) a b Hab). Qed.
  Lemma aCm_super : forall a b, 0 <= a -> 0 <= b -> as_Cm H a + as_Cm H b <= as_Cm H (a + b).
  Proof. intros a b Ha Hb. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ah_costs H HH))))) a b Ha Hb). Qed.
  Lemma aCf_super : forall a b, 0 <= a -> 0 <= b -> as_Cf H a + as_Cf H b <= as_Cf H (a + b).
  Proof. intros a b Ha Hb. exact (proj2 (proj2 (proj2 (proj2 (proj2 (ah_costs H HH))))) a b Ha Hb). Qed.
  Lemma aCm_pos : forall a, 0 <= a -> 0 <= as_Cm H a.
  Proof. intros a Ha. exact (proj1 (ah_costs H HH) a Ha). Qed.
  Lemma aCf_pos : forall a, 0 <= a -> 0 <= as_Cf H a.
  Proof. intros a Ha. exact (proj1 (proj2 (proj2 (ah_costs H HH))) a Ha). Qed.
End G.

(* [comment removed for export] *)
Lemma errph_nonneg : forall ph, 0 <= errph_bytes ph /\ 0 <= errph_cnt ph.
Proof. intros [|c]; cbn; unfold ERRINIT_BYTES, ERRINIT_CNT; lia. Qed.
Lemma lb_bytes_perm : forall L L' : list block, Permutation L L' -> lb_bytes L = lb_bytes L'.
Proof. intros L L' P. induction P; rewrite ?lb_bytes_cons; lia. Qed.

(* [comment removed for export] *)
Definition EBof (K : skrep) (es : list extrep) : list block :=
  concat (map (fun pe => blocks_EXT (fst pe) (snd pe)) (combine (sk_elems K) es)).
Lemma blocks_EXTS_some {HCEIL : HeapCeil} : forall P K es, blocks_EXTS P (Some (K, es)) = blocks_SK P K ++ EBof K es.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section K.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.

  (* [comment removed for export] *)
  Definition avoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) X.
  Definition shavoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => sh a + nsh n <= fst iv \/ snd iv <= sh a) X.
  Lemma avoids_sub : forall X a n a' n', avoids X a n -> a <= a' -> a' + n' <= a + n -> avoids X a' n'.
  Proof. clear. intros X a n a' n' AV H1 H2. unfold avoids in *. eapply Forall_impl; [| exact AV]. cbn beta. intros [u v] K. cbn [fst snd] in *. lia. Qed.
  Lemma avoids_app : forall X Y a n, avoids X a n -> avoids Y a n -> avoids (X ++ Y) a n.
  Proof. clear. intros X Y a n AX AY. unfold avoids. apply Forall_app. split; assumption. Qed.
  Lemma shavoids_app : forall X Y a n, shavoids X a n -> shavoids Y a n -> shavoids (X ++ Y) a n.
  Proof. clear. intros X Y a n AX AY. unfold shavoids. apply Forall_app. split; assumption. Qed.
  Lemma avoids_memflag : forall a n, AIMG_TOP <= a -> avoids memflag_foot a n.
  Proof. clear. intros a n Ha. unfold avoids, memflag_foot, A_mem_inited, AIMG_TOP in *. constructor; [cbn; lia| constructor]. Qed.
  Lemma shavoids_memflag : forall a n, aapp a n -> 0 <= n -> shavoids memflag_foot a n.
  Proof. clear. intros a n AP Hn. unfold shavoids. exact (memflag_below_sh _ _ AP Hn). Qed.

  Lemma combine_app1 {X Y} : forall (l1 : list X) (l2 : list Y) a b,
    length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
  Proof.
    clear. induction l1 as [|u l1 IH]; intros [|v l2] a b L; cbn in L |- *; try discriminate; [reflexivity|].
    rewrite IH by lia. reflexivity.
  Qed.
  Lemma EBof_push : forall K es p X d c did,
    length es = length (sk_elems K) -> EBof (sk_after_push K p d c did) (es ++ [X]) = EBof K es ++ blocks_EXT p X.
  Proof.
    clear. intros K es p X d c did L. unfold EBof, sk_after_push. cbn [sk_elems]. rewrite combine_app1 by (symmetry; exact L).
    rewrite map_app, concat_app. cbn [map concat fst snd]. rewrite app_nil_r. reflexivity.
  Qed.
  Lemma SK_foot_avoids : forall P K a n,
    (forall b, In b (blocks_SK P K) -> a + n <= blk_addr b \/ blk_addr b + blk_size b <= a) -> avoids (SK_foot P K) a n.
  Proof.
    clear. intros P K a n HB. unfold avoids, SK_foot. unfold blocks_SK in HB.
    constructor; [pose proof (HB _ ltac:(left; reflexivity)) as K1; cbn [blk_addr blk_size fst snd] in K1; cbn; lia|].
    destruct (sk_cap K =? 0); [constructor|]. constructor; [| constructor].
    pose proof (HB _ ltac:(right; left; reflexivity)) as K2. cbn [blk_addr blk_size fst snd] in K2. cbn. lia.
  Qed.
  Lemma SK_foot_rin : forall P K a, rin_ivs (SK_foot P K) a -> exists b, In b (blocks_SK P K) /\ blk_addr b <= a < blk_addr b + blk_size b.
  Proof.
    clear. intros P K a Ha. unfold SK_foot in Ha. unfold blocks_SK. cbn [rin_ivs fst snd] in Ha.
    destruct Ha as [Ha|Ha]; [exists (sk_id K, P, SK_SIZE); split; [left; reflexivity| cbn; lia]|].
    destruct (sk_cap K =? 0); cbn [rin_ivs fst snd] in Ha; [destruct Ha|]. destruct Ha as [Ha|[]].
    exists (sk_did K, sk_data K, 8 * sk_cap K). split; [right; left; reflexivity| cbn; lia].
  Qed.
  Lemma ASK_foot_rin : forall P K a, rin_ivs (ASK_foot P K) a ->
    (exists b, In b (blocks_SK P K) /\ blk_addr b <= a < blk_addr b + blk_size b) \/ (sk_cap K <> 0 /\ sh (sk_data K) <= a < sh (sk_data K) + nsh (8 * sk_cap K)).
  Proof.
    clear. intros P K a Ha. unfold ASK_foot in Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [left; exact (SK_foot_rin _ _ _ Ha)| right].
    destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; cbn [rin_ivs fst snd] in Ha; [destruct Ha|]. destruct Ha as [Ha|[]]. split; [exact NE| exact Ha].
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_app : forall P K a n,
    aapp a n -> 0 <= n -> a mod 8 = 0 -> 0 <= sk_cap K ->
    (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\
                                     (a + n + 16 <= blk_addr b \/ blk_addr b + blk_size b + 16 <= a)) ->
    avoids (ASK_foot P K) a n /\ shavoids (ASK_foot P K) a n.
  Proof.
    clear. intros P K a n AP Hn A8 C0 HB. unfold ASK_foot, avoids, shavoids.
    assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H1. destruct H1 as (AP1 & M1 & D1).
    split; apply Forall_app; split.
    - apply SK_foot_avoids. intros b Hb. pose proof (HB _ Hb) as (_ & _ & D). lia.
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & D2).
      pose proof (app_vs_sh a n (sk_data K) (8 * sk_cap K) AP Hn AP2 ltac:(lia)). lia.
    - unfold SK_foot. constructor; [cbn [fst snd]; pose proof (sh_vs_app a n P SK_SIZE AP Hn AP1 ltac:(unfold SK_SIZE; lia)); lia|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & D2).
      pose proof (sh_vs_app a n (sk_data K) (8 * sk_cap K) AP Hn AP2 ltac:(lia)). lia.
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & D2).
      exact (sh_disjoint_blocks a n (sk_data K) (8 * sk_cap K) A8 M2 Hn ltac:(lia) D2).
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_stack : forall P K a n,
    aceil <= a -> 0 <= sk_cap K -> (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b)) -> avoids (ASK_foot P K) a n.
  Proof.
    clear. intros P K a n Ha C0 HB. unfold ASK_foot, avoids. apply Forall_app. split.
    - apply SK_foot_avoids. intros b Hb. pose proof (HB _ Hb) as APb.
      assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size] in H1.
      destruct b as [[q A0] n0]. cbn [blk_addr blk_size fst snd] in *. unfold blocks_SK in Hb.
      destruct Hb as [Hb|Hb]; [injection Hb as <- <- <-; pose proof (aapp_below_aceil _ _ APb); lia|].
      destruct (sk_cap K =? 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <- <-. pose proof (aapp_below_aceil _ _ APb). lia.
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2.
      acb. pose proof (sh_aapp_range _ _ H2 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. right. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_stack_sh : forall P K a n,
    aceil <= a -> 0 <= n -> a + n <= AAPP_HI -> 0 <= sk_cap K ->
    (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\ 0 <= blk_size b) -> shavoids (ASK_foot P K) a n.
  Proof.
    clear. intros P K a n Ha Hn Htop C0 HB. unfold ASK_foot, shavoids. acb. apply Forall_app. split.
    - unfold SK_foot. assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H1. destruct H1 as (AP1 & M1 & _).
      constructor; [cbn [fst snd]; exact (aapp_disjoint_sh P SK_SIZE a n AP1 ltac:(lia) Htop Hn)|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & _).
      exact (aapp_disjoint_sh (sk_data K) (8 * sk_cap K) a n AP2 ltac:(lia) Htop Hn).
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & _).
      right. pose proof (aapp_below_aceil _ _ AP2). unfold sh, nsh. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma perm_split_disjoint : forall s L L1 L2 m b1 b2,
    as_RHEAP H s L m -> Permutation L (L1 ++ L2) -> In b1 L1 -> In b2 L2 ->
    blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1.
  Proof.
    intros s L L1 L2 m b1 b2 HP PL H1 H2.
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) (ah_nodup H HH _ _ _ HP)) as ND.
    eapply (ah_disj H HH); [exact HP| | | exact (nodup_ids_app_ne _ _ _ _ ND H1 H2)].
    - eapply Permutation_in; [apply Permutation_sym; exact PL| apply in_or_app; left; exact H1].
    - eapply Permutation_in; [apply Permutation_sym; exact PL| apply in_or_app; right; exact H2].
  Qed.
  (* [comment removed for export] *)
  Lemma skpush_perm : forall K K' P p d c did (Lmid XB EB LB0 LB' NB : list block),
    K' = sk_after_push K p d c did -> skpush_lb K K' (Lmid ++ XB ++ NB ++ LB0) LB' ->
    Permutation (blocks_SK P K ++ EB) NB -> 0 <= sk_num K ->
    Permutation LB' (blocks_SK P K' ++ (Lmid ++ XB ++ EB ++ LB0))
    /\ (sk_cap K' = sk_cap K \/ (sk_cap K = 0 /\ sk_cap K' = 4) \/ (sk_cap K' = sk_grow (sk_cap K) /\ sk_num K = sk_cap K /\ 4 <= sk_cap K)).
  Proof.
    clear. intros K K' P p d c did Lmid XB EB LB0 LB' NB KEQ PLB PB NN.
    assert (IDK : sk_id K' = sk_id K) by (rewrite KEQ; reflexivity).
    assert (PR : Permutation (Lmid ++ XB ++ NB ++ LB0) (NB ++ (Lmid ++ XB ++ LB0))).
    { rewrite (app_assoc Lmid XB). etransitivity; [apply Permutation_app_swap_app|]. rewrite <- app_assoc. apply Permutation_refl. }
    destruct PLB as [(N1 & C1 & D1 & I1 & ->)|[(C0 & C4 & ->)|(C4 & NC & CG & PG)]].
    - split; [| left; exact C1].
      assert (BK : blocks_SK P K' = blocks_SK P K) by (unfold blocks_SK; rewrite IDK, C1, D1, I1; reflexivity). rewrite BK.
      etransitivity; [exact PR|]. etransitivity; [apply Permutation_app_tail; apply Permutation_sym; exact PB|].
      rewrite <- !app_assoc. apply Permutation_app_head. rewrite !(app_assoc Lmid XB). apply Permutation_app_swap_app.
    - split; [| right; left; split; [exact C0| exact C4]].
      assert (BK : blocks_SK P K = [(sk_id K, P, SK_SIZE)]) by (unfold blocks_SK; rewrite C0; reflexivity).
      assert (BK' : blocks_SK P K' = [(sk_id K, P, SK_SIZE); (sk_did K', sk_data K', 32)]) by (unfold blocks_SK; rewrite IDK, C4; reflexivity).
      rewrite BK in PB. rewrite BK'. cbn [app] in PB |- *.
      etransitivity; [apply perm_skip; exact PR|]. etransitivity; [apply perm_skip; apply Permutation_app_tail; apply Permutation_sym; exact PB|]. cbn [app].
      etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_skip.
      rewrite !(app_assoc Lmid XB). apply Permutation_app_swap_app.
    - split; [| right; right; split; [exact CG| split; [exact NC| exact C4]]].
      assert (CNZ : (sk_cap K =? 0) = false) by (apply Z.eqb_neq; lia).
      assert (GP : 1 <= sk_grow (sk_cap K)) by (unfold sk_grow; apply Z.div_le_lower_bound; lia).
      assert (CNZ' : (sk_cap K' =? 0) = false) by (apply Z.eqb_neq; lia).
      assert (BK : blocks_SK P K = [(sk_id K, P, SK_SIZE); (sk_did K, sk_data K, 8 * sk_cap K)]) by (unfold blocks_SK; rewrite CNZ; reflexivity).
      assert (BK' : blocks_SK P K' = [(sk_id K, P, SK_SIZE); (sk_did K', sk_data K', 8 * sk_cap K')]) by (unfold blocks_SK; rewrite IDK, CNZ'; reflexivity).
      rewrite BK in PB. rewrite BK'. cbn [app] in PB |- *.
      set (D := (sk_did K, sk_data K, 8 * sk_cap K)) in *. set (D' := (sk_did K', sk_data K', 8 * sk_cap K')) in *. set (S := (sk_id K, P, SK_SIZE)) in *.
      apply (@Permutation_cons_inv _ _ _ D).
      etransitivity; [exact PG|]. etransitivity; [apply perm_skip; exact PR|].
      etransitivity; [apply perm_skip; apply Permutation_app_tail; apply Permutation_sym; exact PB|]. cbn [app].
      etransitivity; [apply perm_skip; apply perm_swap|]. etransitivity; [apply perm_swap|]. apply perm_skip.
      etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_skip.
      rewrite !(app_assoc Lmid XB). apply Permutation_app_swap_app.
  Qed.
  Lemma blocks_SK_facts : forall P K, 0 <= sk_cap K ->
    lb_bytes (blocks_SK P K) <= SK_SIZE + 8 * sk_cap K /\ Z.of_nat (length (blocks_SK P K)) <= 2 /\ 1 <= Z.of_nat (length (blocks_SK P K))
    /\ (sk_cap K = 0 -> lb_bytes (blocks_SK P K) = SK_SIZE).
  Proof.
    clear. intros P K C0. unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE];
      rewrite ?lb_bytes_cons; cbn [blk_size snd length lb_bytes fold_right app]; unfold SK_SIZE; lia.
  Qed.
  Lemma SKobj_relist : forall L L' m a K, SKobj L m a K -> (forall b, In b (blocks_SK a K) -> In b L') -> SKobj L' m a K.
  Proof.
    clear. intros L L' m a K (HC & POS & HIN & NC & CAP & SRT & EL & DAT) KEEP. unfold SKobj.
    split; [exact HC|]. split; [exact POS|]. split; [apply KEEP; left; reflexivity|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & JK)]; [left; exact D0| right].
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [| split; [exact AR| exact JK]].
    apply KEEP. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma EXTobj_frameX : forall L0 SP X m m' p E,
    EXTobj L0 m p E -> xpres H L0 SP X m m' -> avoids X p EXT_SIZE -> EXTobj L0 m' p E.
  Proof.
    clear. intros L0 SP X m m' p E ((pad & PL & HC) & HIN & OF) XP A1.
    split; [| split; [exact HIN| exact OF]]. exists pad. split; [exact PL|].
    eapply (xpres_rw_cells' H); [exact XP| exact HC| |].
    - right; right; left. exists (ex_id E, p, EXT_SIZE). split; [exact HIN|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold EXT_SIZE. lia.
    - unfold ext_cells. cbn [cells_size csize Nat.add]. exact A1.
  Qed.
  Lemma EXTs_frameX : forall L0 SP X m m' ps es,
    Forall2 (fun p E => EXTobj L0 m p E) ps es -> xpres H L0 SP X m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> avoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun p E => EXTobj L0 m' p E) ps es.
  Proof.
    clear. intros L0 SP X m m' ps es F2. induction F2 as [|p E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply EXTobj_frameX; [exact HE| exact XP|]. apply (K (ex_id E, p, EXT_SIZE)). apply in_or_app. left. left. reflexivity.
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.
  Lemma oshad_xpresX : forall LB2 m m' SP X P o,
    (match o with None => True | Some (id, n) => In (id, P, n) LB2 /\ avoids X P n /\ shavoids X P n end) ->
    oshad m P o -> xpres H LB2 SP X m m' -> oshad m' P o.
  Proof.
    clear. intros LB2 m m' SP X P [[id n]|] K OSH XP; [| exact I]. cbn [oshad] in *. destruct K as (IN & AV & SAV). destruct OSH as (TOP & SH & bs & CB).
    split; [exact TOP|]. split; [eapply (addressable_xpres_blkX H); [exact IN| exact TOP| exact SH| exact XP| exact SAV]|].
    exists bs. eapply (xpres_rw_cells' H); [exact XP| exact CB| |].
    - right; right; left. exists (id, P, n). split; [exact IN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. pose proof SH as [Hn _]. lia.
    - pose proof SH as [Hn _]. eapply avoids_sub; [exact AV| lia| cbn [cells_size csize Nat.add]; lia].
  Qed.
  Lemma EXT_shad_xpresX : forall LB2 m m' SP X p E,
    In (ex_id E, p, EXT_SIZE) LB2 -> shavoids X p EXT_SIZE ->
    (match ex_val_o E with None => True | Some (id, n) => In (id, ex_val E, n) LB2 /\ avoids X (ex_val E) n /\ shavoids X (ex_val E) n end) ->
    EXT_shad m p E -> xpres H LB2 SP X m m' -> EXT_shad m' p E.
  Proof.
    clear. intros LB2 m m' SP X p E IN SAV KV (TOP & SH & OSH) XP. split; [exact TOP|]. split.
    - eapply (addressable_xpres_blkX H); [exact IN| exact TOP| exact SH| exact XP| exact SAV].
    - eapply oshad_xpresX; [exact KV| exact OSH| exact XP].
  Qed.
  Lemma EXTs_shad_xpresX : forall LB2 m m' SP X ps es,
    Forall2 (fun p E => EXT_shad m p E) ps es -> xpres H LB2 SP X m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB2 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun p E => EXT_shad m' p E) ps es.
  Proof.
    clear. intros LB2 m m' SP X ps es F2. induction F2 as [|p E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply EXT_shad_xpresX; [| | | exact HE| exact XP].
      + apply (proj1 (K (ex_id E, p, EXT_SIZE) ltac:(apply in_or_app; left; left; reflexivity))).
      + apply (proj2 (proj2 (K (ex_id E, p, EXT_SIZE) ltac:(apply in_or_app; left; left; reflexivity)))).
      + unfold blocks_EXT, blocks_of in K. destruct (ex_val_o E) as [[id n]|]; [| exact I].
        exact (K (id, ex_val E, n) ltac:(apply in_or_app; left; right; left; reflexivity)).
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.
  (* [comment removed for export] *)
  Lemma accessible_xpresX : forall s L m2 LB2 m m' SP X A n,
    as_RHEAP H s L m2 -> (forall b, In b LB2 -> In b L) -> aceil <= SP -> ashobj H LB2 SP A n -> accessible m A n -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => sh (A + n - 1) + 1 <= fst iv \/ snd iv <= sh A) X ->
    accessible m' A n.
  Proof.
    intros s L m2 LB2 m m' SP X A n HP SUB HSP OB (Q0 & Q1 & QA) XP HX.
    split; [exact Q0|]. split; [exact Q1|]. intros xa Hxa. destruct (QA xa Hxa) as (v & V1 & RD & OK).
    exists v. split; [exact V1|]. split; [| exact OK]. unfold mrd in *.
    assert (SX : ASHADOW_BASE <= sh xa < AHI_LO).
    { split; [unfold sh; Z.div_mod_to_equations; lia|].
      pose proof (sh_nsh_high xa 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. change ((1 + 7) / 8) with 1 in H0. lia. }
    destruct (XP (sh xa)) as [EQ _].
    { unfold AHI_LO in SX. rewrite ASHADOW_BASE_val in SX. lia. }
    { split; [eapply (ashobj_sh_client_sub H HH); eauto|].
      assert (M1 : sh A <= sh xa) by (apply sh_mono; lia). assert (M2 : sh xa <= sh (A + n - 1)) by (apply sh_mono; lia).
      clear - HX M1 M2. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K].
      - pose proof (Forall_inv HX) as K1. cbn in K1. lia.
      - exact (IH (Forall_inv_tail HX) K). }
    rewrite EQ. exact RD.
  Qed.


  (* [comment removed for export] *)
  Lemma RFS_via_xpresX : forall s L m2 LF0 LB2 SP X m m',
    as_RFS H LF0 m -> as_RHEAP H s L m2 -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= ATLS_PRIV_LO
                              \/ (exists b, In b L /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                              \/ (exists b, In b L /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))) X ->
    as_RFS H LF0 m'.
  Proof.
    intros s L m2 LF0 LB2 SP X m m' R HP XP HX. pose proof (RFS_fsb H HH _ _ R) as (F1 & F2 & F3 & F4). acb.
    eapply (ah_RFS_ext H HH); [exact R|].
    intros a Ha Hr. apply XP; [exact Ha|]. split.
    - unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
      + right; right; right; right; left. exact Hr.
      + right; left. unfold aimg_client. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      + right; right; right; right; right; left. exact Hr.
    - assert (LOa : ATLS_PRIV_LO <= a).
      { pose proof (sh_mono AIMG_TOP (as_FSB H) F1). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP, AIMG_TOP in *. lia. }
      pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1.
      pose proof (aapp_not_shadowland _ _ F4) as FNS.
      assert (GEN : forall iv, In iv X -> ~ (fst iv <= a < snd iv)).
      { intros iv Hiv K. pose proof (proj1 (Forall_forall _ _) HX iv Hiv) as K1. cbn beta in K1.
        destruct K1 as [K1|[(b & Hb & R1 & R2)|(b & Hb & R1 & R2)]]; [clear - K K1 LOa; lia| |].
        + pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
          pose proof (aapp_not_shadowland _ _ B7) as BNS.
          destruct Hr as [Hr|[Hr|Hr]]; [clear - K R1 R2 B6 Hr; lia| unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; clear - K R1 R2 B4 Hr; lia|].
          unfold AFS_SIZE in *. unfold ALOWSH_LO, AHI_LO, sh in *. rewrite ?ASHADOW_BASE_val in *. clear - K R1 R2 BNS Hr FNS F1 F2 B4 ACEILB. unfold AIMG_TOP in *. lia.
        + pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
          pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). rewrite S0 in S1. pose proof (aapp_not_shadowland _ _ B7) as BNS.
          destruct Hr as [Hr|[Hr|Hr]].
          * unfold AFS_SIZE, ALOWSH_LO, AHI_LO, sh, nsh in *. rewrite ?ASHADOW_BASE_val in *. clear - K R1 R2 FNS Hr S1 S2 S3 B4 B3 ACEILB F1 F2. unfold AIMG_TOP in *. lia.
          * unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. clear - K R1 R2 S1 Hr. lia.
          * unfold AFS_SIZE, sh, nsh in *. clear - K R1 R2 B6 B2 B3 F3 Hr. Z.div_mod_to_equations. lia. }
      clear - GEN. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K]; [exact (GEN iv (or_introl eq_refl) K)|].
      apply IH; [intros iv' Hiv'; apply GEN; right; exact Hiv'| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma ASK_foot_stack0 : forall P K, 0 <= sk_cap K ->
    (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b) /\ 0 <= blk_size b) -> Forall stack0_ok (ASK_foot P K).
  Proof.
    clear. intros P K C0 HB. unfold ASK_foot, SK_foot. apply Forall_app. split.
    - assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H1. destruct H1 as [AP1 _].
      constructor; [eapply stack0_ok_aapp; [exact AP1| cbn; lia| cbn; lia]|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as [AP2 _].
      eapply stack0_ok_aapp; [exact AP2| cbn; lia| cbn; lia].
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as [AP2 N2].
      pose proof (aapp_bounds _ _ AP2 N2) as (Q1 & Q2 & Q3 & Q4 & Q5). apply stack0_ok_sh; unfold AIMG_TOP in Q1; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_fs : forall P K L, 0 <= sk_cap K -> (forall b, In b (blocks_SK P K) -> In b L) ->
    Forall (fun iv : Z * Z => snd iv <= ATLS_PRIV_LO
                              \/ (exists b, In b L /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                              \/ (exists b, In b L /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))) (memflag_foot ++ ASK_foot P K).
  Proof.
    clear. intros P K L C0 SUB. apply Forall_app. split.
    { unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. constructor; [left; cbn; lia| constructor]. }
    unfold ASK_foot, SK_foot. apply Forall_app. split.
    - constructor; [right; left; exists (sk_id K, P, SK_SIZE); split; [apply SUB; unfold blocks_SK; left; reflexivity| cbn; lia]|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [apply SUB; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity| cbn; lia].
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [apply SUB; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity| cbn; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma shavoids_acc : forall X a n, shavoids X a n -> a mod 8 = 0 -> 0 <= a ->
    Forall (fun iv : Z * Z => sh (a + n - 1) + 1 <= fst iv \/ snd iv <= sh a) X.
  Proof.
    clear. intros X a n SAV A8 A0. unfold shavoids in SAV. eapply Forall_impl; [| exact SAV]. cbn beta. intros [u v] K. cbn [fst snd] in *.
    unfold sh, nsh in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_not_client : forall s Lall m2 L SP b1 a,
    as_RHEAP H s Lall m2 -> In b1 Lall -> (forall b, In b L -> In b Lall) -> (forall b, In b L -> blk_id b <> blk_id b1) -> aceil <= SP ->
    blk_addr b1 <= a < blk_addr b1 + blk_size b1 -> aclient_addr H L SP a -> False.
  Proof.
    intros s Lall m2 L SP b1 a HP IN1 SUB IDS1 HSP Ra C. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IN1) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_not_shadowland _ _ B7) as BNS.
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1. pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). rewrite S0 in S1.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
    - clear - C Ra B5 HSP. lia.
    - unfold aimg_client, AIMG_TOP in *. clear - C Ra B4. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_disj H HH _ _ _ _ _ HP (SUB _ Hb) IN1 (IDS1 _ Hb)) as DJ. clear - DJ Ra Rb. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (T1 & T2 & T3). rewrite S0 in T1. clear - Rb Ra BNS T1 T2 T3. unfold ALOWSH_LO, AHI_LO in *. lia.
    - clear - C Ra B6. lia.
    - pose proof (sh_mono _ _ F2) as M6. clear - C Ra BNS FS1 FS3 M6. unfold ALOWSH_LO, AHI_LO in *. lia.
    - clear - C Ra BNS S1 S2 B3. unfold ALOWSH_LO, AHI_LO, nsh in *. lia.
  Qed.
  Lemma blksh_not_client : forall s Lall m2 L SP b1 a,
    as_RHEAP H s Lall m2 -> In b1 Lall -> (forall b, In b L -> In b Lall) -> (forall b, In b L -> blk_id b <> blk_id b1) -> aceil <= SP ->
    sh (blk_addr b1) <= a < sh (blk_addr b1) + nsh (blk_size b1) -> aclient_addr H L SP a -> False.
  Proof.
    intros s Lall m2 L SP b1 a HP IN1 SUB IDS1 HSP Ra C. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IN1) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_not_shadowland _ _ B7) as BNS.
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1. pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). rewrite S0 in S1.
    pose proof (aapp_not_shadowland _ _ F4) as FNS.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
    - clear - C Ra S2 S3 HSP ACEILB. unfold AHI_LO in *. lia.
    - unfold aimg_client in *. clear - C Ra S1. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
      pose proof (aapp_not_shadowland _ _ D7) as BNSb. clear - Rb Ra BNSb S1 S2 S3. unfold ALOWSH_LO, AHI_LO in *. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & D2 & D3 & _ & _ & _ & D7).
      pose proof (ah_disj H HH _ _ _ _ _ HP (SUB _ Hb) IN1 (IDS1 _ Hb)) as DJ.
      pose proof (sh_disjoint_blocks (blk_addr b) (blk_size b) (blk_addr b1) (blk_size b1) ltac:(clear - D2; Z.div_mod_to_equations; lia) ltac:(clear - B2; Z.div_mod_to_equations; lia) D3 B3 DJ) as SD.
      clear - Rb Ra SD. lia.
    - clear - C Ra FNS S1 S2 S3. unfold AFS_SIZE, ALOWSH_LO, AHI_LO in *. lia.
    - assert (E6 : sh (as_FSB H + AFS_SIZE) = sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh, AFS_SIZE; clear - F3; Z.div_mod_to_equations; lia). rewrite E6 in C.
      pose proof (sh_disjoint_blocks (as_FSB H) AFS_SIZE (blk_addr b1) (blk_size b1) ltac:(clear - F3; Z.div_mod_to_equations; lia) ltac:(clear - B2; Z.div_mod_to_equations; lia) ltac:(unfold AFS_SIZE; lia) B3 ltac:(unfold AFS_SIZE in *; clear - B6; lia)) as SD2.
      clear - C Ra SD2. lia.
    - clear - C Ra S2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma addressable_acrossW : forall W m m' A n,
    addressable m A n -> munch W m m' -> wmono asegs m m' -> 0 <= A < AAPP_HI -> A + n <= AAPP_HI ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> addressable m' A n.
  Proof.
    clear. intros W m m' A n AD MU WM A0 TOP HW. pose proof AD as [Hn _].
    eapply addressable_transport; [exact AD| exact MU| exact WM|].
    pose proof (sh_in_shadowland A A0) as S1.
    assert (S2 : sh A + nsh n <= AHI_LO) by (unfold sh, nsh, AHI_LO, AAPP_HI, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    clear - HW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K. cbn in K.
    split; [unfold ALOWSH_LO, AHI_LO in *; lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  Lemma oshad_acrossW : forall W m m' P o,
    oshad m P o -> munch W m m' -> wmono asegs m m' ->
    (match o with None => True | Some (_, n) => 0 <= P < AAPP_HI /\ disjoint_from W P n end) ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> oshad m' P o.
  Proof.
    clear. intros W m m' P [[i n]|] OSH MU WM K HW; [| exact I]. cbn [oshad] in *. destruct OSH as (TOP & AD & bs & CB). destruct K as [P0 DJ].
    split; [exact TOP|]. split; [eapply addressable_acrossW; eauto|]. exists bs. eapply rw_cells_transport; [exact CB| exact MU| exact WM|].
    cbn [cells_size csize Nat.add]. pose proof AD as [Hn _]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact DJ.
  Qed.
  Lemma EXT_shad_acrossW : forall W m m' p X,
    EXT_shad m p X -> munch W m m' -> wmono asegs m m' -> 0 <= p -> disjoint_from W p EXT_SIZE ->
    (match ex_val_o X with None => True | Some (_, n) => 0 <= ex_val X < AAPP_HI /\ disjoint_from W (ex_val X) n end) ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> EXT_shad m' p X.
  Proof.
    clear. intros W m m' p X (TOP & AD & OSH) MU WM P0 DJp K HW. split; [exact TOP|].
    split; [eapply addressable_acrossW; eauto; unfold EXT_SIZE in TOP; lia|]. eapply oshad_acrossW; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_as_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    clear. intros m A cs [[WF BA] W]. unfold rw_cells, cells_at. cbn [cells_bytes cbytes cells_wf cell_wf cells_size csize].
    rewrite app_nil_r, Nat.add_0_r. split; [split; [split; [apply cells_bytes_length; exact WF| exact I]| exact BA]| exact W].
  Qed.
  Lemma nodup_ids_same : forall (L : list block) b1 b2, List.NoDup (map blk_id L) -> In b1 L -> In b2 L -> blk_id b1 = blk_id b2 -> b1 = b2.
  Proof.
    clear. induction L as [|b L IH]; intros b1 b2 ND H1 H2 E; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | exact (IH _ _ ND' H1 H2 E)].
    - exfalso. apply NI. rewrite E. apply in_map. exact H2.
    - exfalso. apply NI. rewrite <- E. apply in_map. exact H1.
  Qed.


  Lemma bytes_at_sub : forall m A zs i n,
    bytes_at asegs m A zs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length zs) ->
    bytes_at asegs m (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs))) = n.
  Proof.
    clear. intros m A zs i n BS I0 N0 LE.
    rewrite <- (firstn_skipn (Z.to_nat i) zs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
    rewrite firstn_length_le in BS by lia. rewrite Z2Nat.id in BS by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) zs)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
    split; [exact BS|]. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XR (ph : errphase) (XS : list (Z * Z)) : list (Z * Z) := XS ++ ERR_XE ++ memflag_foot ++ errph_foot ph.

  (* [comment removed for export] *)
  Lemma XR_block : forall ph s L m2 LF0 mX XS b,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> In b L ->
    (forall c0, ph = ErrReady c0 -> In (ec_es c0) L /\ blk_id (ec_es c0) <> blk_id b /\ blk_size (ec_es c0) = ERRST_SIZE) ->
    avoids (XR ph XS) (blk_addr b) (blk_size b) /\ shavoids (XR ph XS) (blk_addr b) (blk_size b).
  Proof.
    intros ph s L m2 LF0 mX XS b HP RF FXS Hb HES. acb. destruct b as [[q A] n]. cbn [blk_id blk_addr blk_size fst snd] in *.
    pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5, B6, B7.
    pose proof (aapp_bounds _ _ B7 B3) as (Q1 & Q2 & Q3 & Q4 & _). pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
    unfold XR, avoids, shavoids. split; (apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]).
    - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch H HH LF0 A n mX iv RF (fsobj_block H HH _ _ _ LF0 _ _ _ HP Hb) ltac:(lia) B3 ltac:(lia) B7 SC).
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      unfold AIMG_TOP in B4. cbn [app]. clear - B4. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. unfold AIMG_TOP in B4. clear - B4. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct ph as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as (IE & NE & SZ).
      pose proof (ah_disj H HH _ _ _ _ _ HP IE Hb NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. rewrite SZ in DJ.
      apply Forall_cons; [cbn [fst snd]; clear - DJ; lia| apply Forall_nil].
    - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch_sh H HH LF0 A n mX iv RF (fsobj_block H HH _ _ _ LF0 _ _ _ HP Hb) ltac:(lia) B3 ltac:(lia) SC).
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - S1. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. clear - S1. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct ph as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as (IE & NE & SZ).
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
      apply Forall_cons; [cbn [fst snd]; pose proof (app_vs_sh _ _ _ _ E7 E3 B7 B3); lia| apply Forall_nil].
  Qed.
  (* [comment removed for export] *)
  Lemma XR_stack : forall ph LF0 mX XS a n,
    as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> aceil <= a -> errph_below ph aceil -> avoids (XR ph XS) a n.
  Proof.
    intros ph LF0 mX XS a n RF FXS Ha EB. unfold XR, avoids. apply Forall_app. split.
    - eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RF FXS)]. cbn beta. intros iv K. lia.
    - eapply (raise_foot_frame ph a n aceil); [apply Z.le_refl| exact Ha| exact EB].
  Qed.
  Lemma XR_stack_sh : forall ph s L m2 LF0 mX XS a n,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> aceil <= a -> 0 <= n -> a + n <= AAPP_HI ->
    (forall c0, ph = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) -> shavoids (XR ph XS) a n.
  Proof.
    intros ph s L m2 LF0 mX XS a n HP RF FXS Ha Hn Htop HES. acb. unfold XR, shavoids. pose proof (RFS_fsb H HH _ _ RF) as (F1 & F2 & F3 & F4).
    assert (SA : sh aceil <= sh a) by (apply sh_mono; lia). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1.
    apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch_sh H HH LF0 a n mX iv RF (fsobj_high H HH LF0 a n mX RF Ha) ltac:(lia) Hn Htop SC).
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. unfold nsh, AFS_SIZE in FS2. clear - SA FS1 FS2. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. unfold nsh, AFS_SIZE in FS2. clear - SA FS1 FS2. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct ph as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
      apply Forall_cons; [cbn [fst snd]; exact (aapp_disjoint_sh _ _ a n E7 ltac:(lia) Htop Hn)| apply Forall_nil].
  Qed.
  (* [comment removed for export] *)
  Lemma XR_stack0 : forall ph s L m2 LF0 mX XS,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS ->
    (forall c0, ph = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) -> Forall stack0_ok (XR ph XS).
  Proof.
    intros ph s L m2 LF0 mX XS HP RF FXS HES. acb. unfold XR. pose proof (RFS_fsb H HH _ _ RF) as (F1 & F2 & F3 & F4).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. assert (LEA : AIMG_TOP <= aceil) by (unfold AIMG_TOP; lia). pose proof (sh_mono AIMG_TOP aceil LEA) as SM. rewrite S0 in SM.
    apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact FXS]. intros iv SC. unfold stack0_ok. destruct SC as [->|(k & ff & fp & FF & EE)]; cbn [fst snd].
      + pose proof (aapp_not_shadowland _ _ F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & _). rewrite S0 in FS1. unfold AFS_FLAGS, AFS_SIZE, ALOWSH_LO in *. lia.
      + pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
        pose proof (aapp_not_shadowland _ _ P9) as FNS. pose proof (sh_aapp_range _ _ P9 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3). rewrite S0 in FS1.
        pose proof (fsz_pos k ltac:(lia)).
        destruct EE as [-> |[-> | ->]]; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE, AFS_HDR, ALOWSH_LO in *; [lia| lia|].
        right. assert (LE1 : ff + fsz k <= as_FSB H + 11571200) by (clear - P6; lia). pose proof (sh_mono _ _ LE1) as SM1. pose proof (sh_mono _ _ P8) as SM2.
        assert (E8 : sh (ff + fsz k) = sh ff + fshn k) by (unfold fshn, fsz, sh; clear - M8; Z.div_mod_to_equations; nia). rewrite <- E8. clear - SM1 SM2. lia.
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - SM. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. clear - SM. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct ph as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
      apply Forall_cons; [eapply stack0_ok_aapp; [exact E7| cbn; lia| cbn; lia]| apply Forall_nil].
  Qed.
  Lemma XR_low : forall ph s L m2 LF0 mX XS,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS ->
    (forall c0, ph = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) -> Forall (fun iv : Z * Z => snd iv <= aceil) (XR ph XS).
  Proof.
    intros ph s L m2 LF0 mX XS HP RF FXS HES. acb. unfold XR.
    apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RF FXS)]. cbn beta. intros iv K. lia.
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - ACEILB. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. clear - ACEILB. apply Forall_cons; [cbn; lia| apply Forall_nil].
    - destruct ph as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & _ & _ & E5 & _). rewrite SZ in E5. apply Forall_cons; [cbn [fst snd]; exact E5| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma exts_cost_bytes : forall L m ps es,
    Forall2 (fun p X => EXTobj L m p X) ps es ->
    ecost_sum extrep (ext_cost H) es <= as_Cf H (lb_bytes (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))))
    /\ 0 <= lb_bytes (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))).
  Proof.
    intros L m ps es F2. induction F2 as [|p X ps' es' HE FF2 IH].
    - cbn. rewrite (aCf0 H HH). lia.
    - destruct IH as [IH1 IH2]. unfold ecost_sum in IH1 |- *. cbn [fold_right combine map concat fst snd]. rewrite lb_bytes_app.
      set (R := lb_bytes (concat (map (fun px : Z * extrep => blocks_EXT (fst px) (snd px)) (combine ps' es')))) in *.
      pose proof HE as (_ & _ & OF).
      assert (E1 : ext_cost H X <= as_Cf H (lb_bytes (blocks_EXT p X)) /\ 0 <= lb_bytes (blocks_EXT p X)).
      { unfold ext_cost, ocost, blocks_EXT, blocks_of. revert OF. unfold ofield. destruct (ex_val_o X) as [[i n]|]; intros OF; rewrite ?lb_bytes_cons; cbn [blk_size snd lb_bytes fold_right]; rewrite Z.add_0_r.
        - destruct OF as (_ & N0 & _). rewrite (Z.max_l n 0) by lia. pose proof (aCf_super H HH EXT_SIZE n ltac:(unfold EXT_SIZE; lia) N0). unfold EXT_SIZE in *. lia.
        - rewrite (aCf0 H HH). unfold EXT_SIZE. lia. }
      destruct E1 as [E1 P1]. pose proof (aCf_super H HH _ _ P1 IH2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SKobj_frameX : forall L0 SP X m m' a K,
    SKobj L0 m a K -> xpres H L0 SP X m m' -> avoids X a SK_SIZE -> (sk_cap K <> 0 -> avoids X (sk_data K) (8 * sk_cap K)) -> SKobj L0 m' a K.
  Proof.
    clear. intros L0 SP X m m' a K SO XP AVH AVD.
    destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    unfold SKobj. split.
    { exists pad. split; [exact PL|]. eapply (xpres_rw_cells' H); [exact XP| exact HDR| |].
      - right; right; left. exists (sk_id K, a, SK_SIZE). split; [exact HIN|]. unfold sk_hdr_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold SK_SIZE. lia.
      - unfold sk_hdr_cells. cbn [cells_size csize Nat.add]. exact AVH. }
    split; [exact POS|]. split; [exact HIN|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in NC.
    assert (AVD' : avoids X (sk_data K) (8 * sk_cap K)) by (apply AVD; lia).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split.
    - eapply (xpres_u64arr H); [exact XP| exact AR|]. split.
      + right; right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact D4|]. cbn [blk_addr blk_size fst snd]. rewrite ?length_map. lia.
      + rewrite length_map. eapply avoids_sub; [exact AVD'| lia| lia].
    - exists junk. eapply (xpres_rw_cells' H); [exact XP| exact JK| |].
      + right; right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact D4|]. cbn [blk_addr blk_size fst snd cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
      + cbn [cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply avoids_sub; [exact AVD'| lia| lia].
  Qed.
End K.
