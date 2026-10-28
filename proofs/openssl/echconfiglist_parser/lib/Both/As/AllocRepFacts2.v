(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma munch_agree : forall W m m', munch W m m' -> agree_on (outside W) m m'.
Proof.
  intros W m m' MU x Hx Hr. apply MU. unfold wa. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 x) with (x mod 2^64). rewrite Z.mod_small by lia. exact Hx.
Qed.

Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Lemma sh_sep : forall x k y l, x mod 8 = 0 -> y mod 8 = 0 -> 0 <= k -> 0 <= l ->
  x + 8 * k <= y \/ y + 8 * l <= x -> sh x + k <= sh y \/ sh y + l <= sh x.
Proof. intros x k y l Hx Hy Hk Hl D. unfold sh. Z.div_mod_to_equations. lia. Qed.

Section RecordSep.
  Variable s : ast.
  Hypothesis OK : ast_ok s.
  Let st := a_st s.
  Let W : WF st. Proof. exact (proj2 OK). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.

  (* [comment removed for export] *)
  Ltac mod8s :=
    lazymatch goal with
    | |- _ mod 8 = 0 =>
        first [ reflexivity | assumption
              | apply mod8_add; mod8s | apply mod8_sub; mod8s | apply mod8_mul_r; mod8s | apply mod8_mul_l; mod8s
              | eapply (mod8_of 16); [reflexivity| lia| assumption]
              | eapply (mod8_of 32); [reflexivity| lia| assumption]
              | eapply (mod8_of 65536); [reflexivity| lia| assumption]
              | eapply (mod8_of 4096); [reflexivity| lia| assumption]
              | eapply (mod8_of 8192); [reflexivity| lia| assumption]
              | eapply (mod8_of 262144); [reflexivity| lia| assumption]
              | lia ]
    | |- _ => first [ reflexivity | assumption
                    | solve [ repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; lia ]   (* [comment removed for export] *)
                    | lia ]
    end.

  Lemma farray_in_space : forall c, 0 <= c < kNumClasses ->
    a_sb s <= FA s c /\ FA s c + rg_mapped_free_array (get_region st c) <= a_sb s + kSpaceSize /\ FA s c mod 8 = 0
    /\ 0 <= rg_mapped_free_array (get_region st c) /\ rg_mapped_free_array (get_region st c) mod 8 = 0.
  Proof.
    intros c Hc. pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO). pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_mod _ _ RO) as FM.
    pose proof (ro_numfreed _ _ RO). pose proof (region_in_space st c Hc). pose proof PL as (S1 & _).
    unfold FA. rewrite free_array_base_eq, region_beg_eq in *. unfold a_sb, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kSpaceSize, zlen in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *. set (f := rg_mapped_free_array _) in *. clearbody f.
    repeat split; mod8s.
  Qed.

  Lemma tail_in_space : forall c, 0 <= c < kNumClasses ->
    a_sb s <= RB s c + rg_allocated_user (get_region st c) /\ RB s c + rg_mapped_user (get_region st c) <= a_sb s + kSpaceSize
    /\ (RB s c + rg_allocated_user (get_region st c)) mod 8 = 0 /\ rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c)
    /\ (rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c)) mod 8 = 0.
  Proof.
    intros c Hc. pose proof (WF_region st c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO). pose proof (ro_alloc_nonneg _ _ RO).
    pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_mod _ _ RO) as MM. pose proof (ro_alloc_mod _ _ RO) as AM. pose proof (ro_empty _ _ RO) as EM.
    pose proof (class_size_table_facts c Hc) as (_ & CS & _). pose proof (region_in_space st c Hc). pose proof PL as (S1 & _).
    unfold RB. rewrite region_beg_eq in *. unfold a_sb, kFreeArrayOffset, kUserMapSize, kSpaceSize in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *. set (al := rg_allocated_user _) in *. set (mu := rg_mapped_user _) in *.
    set (sz := class_size c) in *. clearbody al mu sz.
    assert (AM8 : al mod 8 = 0).
    { destruct (Z.eq_dec sz 0) as [E0|NZ].
      - specialize (EM E0). replace al with 0 by (first [clear - EM H1 H0; lia | lia]). reflexivity.
      - specialize (AM NZ). eapply (mod8_of sz); [| exact NZ| exact AM]. eapply (mod8_of 32); [reflexivity| lia| exact CS]. }
    assert (MM8 : mu mod 8 = 0) by (eapply (mod8_of 262144); [reflexivity| lia| exact MM]).
    repeat split; mod8s.
  Qed.

  Lemma freech_in_space : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    a_sb s <= compact_to_addr st c cp /\ compact_to_addr st c cp + class_size c <= a_sb s + kSpaceSize
    /\ compact_to_addr st c cp mod 8 = 0 /\ 0 < class_size c /\ class_size c mod 8 = 0.
  Proof.
    intros c cp Hc Hin.
    assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
    pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & CS3). pose proof (class_size_table_facts c Hc) as (_ & CS & _). pose proof PL as (S1 & _).
    rewrite compact_to_addr_eq, region_beg_eq in *. unfold a_sb in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *. set (sz := class_size c) in *. clearbody sz.
    assert (SZ8 : sz mod 8 = 0) by (eapply (mod8_of 32); [reflexivity| lia| exact CS]).
    repeat split; mod8s.
  Qed.

  Lemma batch_in_space : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
    a_sb s <= qb_addr b /\ qb_addr b + kBatchSize <= a_sb s + kSpaceSize /\ qb_addr b mod 8 = 0.
  Proof.
    intros b Hb. pose proof (batch_carved s OK b Hb) as (C' & _). pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & CS3).
    change (class_size kBatchClass) with 8192 in *. pose proof PL as (S1 & _).
    destruct C' as (_ & _ & C0 & C1 & _). rewrite region_beg_eq in C0, C1. change (class_size kBatchClass) with 8192 in C1.
    unfold a_sb, kBatchSize, kBatchClass in *. unfold st in *.
    set (sb := as_space_beg (a_st s)) in *.
    split; [lia|]. split; [lia|].
    assert (E : qb_addr b = (qb_addr b - (sb + 24 * 2^32)) + sb + 24 * 2^32) by lia.
    rewrite E. mod8s.
  Qed.

  Variable ch0 : chunk.
  Hypothesis H0 : In ch0 (chunk_list st).
  Let lo0 := ch_lo ch0.
  Let hi0 := ch_end ch0.

  (* [comment removed for export] *)
  Lemma record_ext : AIMG_TOP <= lo0 /\ hi0 <= aceil /\ lo0 <= ch_alloc_beg ch0 /\ lo0 mod 8 = 0 /\ hi0 mod 8 = 0
    /\ ch_alloc_beg ch0 + ch_rz ch0 = ch_user_beg ch0 /\ ch_user_beg ch0 + round_up (ch_used ch0) 8 <= hi0 /\ 16 <= ch_rz ch0 /\ 1 <= ch_used ch0.
  Proof.
    pose proof (ext_facts s OK ch0 H0) as (X1 & X2 & X3 & _). pose proof (chunk_align s OK ch0 H0) as (A1 & A2 & A3 & A4 & A5).
    pose proof (chunk_geom s OK ch0 H0) as (G1 & G2 & G3 & G4 & _). subst lo0 hi0. repeat split; try assumption; lia.
  Qed.
  Lemma record_band : aapp lo0 (hi0 - lo0).
  Proof. exact (ext_band s OK ch0 H0). Qed.

  (* [comment removed for export] *)
  Lemma record_primary_space : ch_primary ch0 = true -> a_sb s <= lo0 /\ hi0 <= a_sb s + kSpaceSize.
  Proof. intros P. pose proof (ext_facts s OK ch0 H0) as (_ & _ & _ & XP & _). destruct (XP P) as (_ & _ & B1 & B2). subst lo0 hi0. unfold ch_lo. rewrite P. lia. Qed.
  Lemma record_secondary_map : ch_primary ch0 = false ->
    exists h, In h (as_sec st) /\ lo0 = sc_map_beg h /\ hi0 = sc_map_beg h + sc_map_size h /\ ch_alloc_beg ch0 = sc_map_beg h + kPageSize.
  Proof. intros P. pose proof (ext_facts s OK ch0 H0) as (_ & _ & _ & _ & XS). exact (XS P). Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  (* [comment removed for export] *)
  Lemma record_vs_space : ch_primary ch0 = false -> a_sb s + kSpaceSize + kPageSize <= lo0 \/ hi0 <= a_sb s.
  Proof.
    intros P. placed. destruct (record_secondary_map P) as (h & Hh & L & E & _). pose proof (SEC h Hh) as (_ & _ & _ & _ & D & _).
    subst lo0 hi0. rewrite L, E. clear - D; try acb. unfold disj in D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma farray_vs_record : forall c, 0 <= c < kNumClasses ->
    FA s c + rg_mapped_free_array (get_region st c) <= lo0 \/ hi0 <= FA s c.
  Proof.
    intros c Hc. pose proof (WF_region st c W Hc) as RO. pose proof (ro_fa_bound _ _ RO) as FB.
    pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold FA. rewrite free_array_base_eq.
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_facts s OK ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      pose proof (carved_range st _ _ W C) as (CR1 & CR2 & CR3). subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (Z.eq_dec c (ch_class ch0)) as [->|NE].
      + right. unfold st in *. clear - EE CR2; try acb. lia.
      + destruct C as (Hc0 & _). destruct (regions_disjoint st c (ch_class ch0) ltac:(hci; lia) ltac:(hci; lia) NE) as [D|D];
          unfold st in *; clear - EE CR1 CR2 D FB; try acb; unfold kFreeArrayOffset, kFreeArraySize in *; lia.
    - destruct (record_vs_space E) as [D|D]; unfold a_sb, st in *; clear - D RS1 RS2 FB; try acb; unfold kFreeArrayOffset, kFreeArraySize, kSpaceSize, kPageSize in *; lia.
  Qed.

  Lemma tail_vs_record : forall c, 0 <= c < kNumClasses ->
    RB s c + rg_mapped_user (get_region st c) <= lo0 \/ hi0 <= RB s c + rg_allocated_user (get_region st c).
  Proof.
    intros c Hc. pose proof (WF_region st c W Hc) as RO. pose proof (ro_mapped_bound _ _ RO) as MB. pose proof (ro_alloc_nonneg _ _ RO) as AN.
    pose proof (ro_alloc_le _ _ RO) as AL.
    pose proof (region_in_space st c Hc) as [RS1 RS2]. unfold RB.
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_facts s OK ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      pose proof (carved_range st _ _ W C) as (CR1 & CR2 & CR3). subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (Z.eq_dec c (ch_class ch0)) as [->|NE].
      + right. destruct C as (_ & _ & _ & _ & CL). unfold st in *. clear - EE CL; try acb. lia.
      + destruct C as (Hc0 & _). destruct (regions_disjoint st c (ch_class ch0) ltac:(hci; lia) ltac:(hci; lia) NE) as [D|D];
          unfold st in *; clear - EE CR1 CR2 D MB AN AL; try acb; unfold kFreeArrayOffset, kUserMapSize in *; lia.
    - destruct (record_vs_space E) as [D|D]; unfold a_sb, st in *; clear - D RS1 RS2 MB AN AL; try acb; unfold kFreeArrayOffset, kUserMapSize, kSpaceSize, kPageSize in *; lia.
  Qed.

  Lemma rinfo_vs_record : a_ri s + kPageSize <= lo0 \/ hi0 <= a_ri s.
  Proof.
    unfold a_ri. destruct (ch_primary ch0) eqn:E.
    - right. exact (proj2 (record_primary_space E)).
    - destruct (record_vs_space E) as [D|D]; unfold kSpaceSize, kPageSize in *; lia.
  Qed.

  Lemma freech_vs_record : forall c cp, 0 <= c < kNumClasses ->
    In cp (rg_free_array (get_region st c)) \/ In cp (pc_chunks (get_pc st c)) ->
    compact_to_addr st c cp + class_size c <= lo0 \/ hi0 <= compact_to_addr st c cp.
  Proof.
    intros c cp Hc Hin.
    assert (C' : carved st c (compact_to_addr st c cp)) by (destruct Hin; [apply carved_free| apply carved_cache]; assumption).
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_facts s OK ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (carved_sep st _ _ _ _ W C C') as [[EC EA]|D].
      + exfalso. eapply (inuse_not_free s OK ch0 c cp); eauto.
      + clear - EE D; try acb. lia.
    - pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & _).
      destruct (record_vs_space E) as [D|D]; unfold st in *; clear - D CS1 CS2; try acb; unfold kPageSize in *; lia.
  Qed.

  Lemma batch_vs_record : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
    qb_addr b + kBatchSize <= lo0 \/ hi0 <= qb_addr b.
  Proof.
    intros b Hb. pose proof (batch_carved s OK b Hb) as (C' & _).
    destruct (ch_primary ch0) eqn:E.
    - pose proof (ext_facts s OK ch0 H0) as (_ & _ & _ & XP & _). destruct (XP E) as (C & EE & B1 & B2).
      subst lo0 hi0. unfold ch_lo. rewrite E.
      destruct (carved_sep st _ _ _ _ W C C') as [[EC EA]|D].
      + exfalso. eapply (inuse_not_batch s OK ch0 b); eauto.
      + change (class_size kBatchClass) with kBatchSize in D. clear - EE D; try acb. lia.
    - pose proof (carved_in_space s OK _ _ C') as (CS1 & CS2 & _). change (class_size kBatchClass) with kBatchSize in CS2.
      destruct (record_vs_space E) as [D|D]; unfold st in *; clear - D CS1 CS2; try acb; unfold kPageSize in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sechdr_vs_primary_record : forall h, In h (as_sec st) -> ch_primary ch0 = true ->
    sc_map_beg h + kPageSize <= lo0 \/ hi0 <= sc_map_beg h.
  Proof.
    intros h Hh P. placed. pose proof (SEC h Hh) as (_ & _ & _ & Q4 & Q & _). destruct (record_primary_space P) as [B1 B2].
    clear - Q4 Q B1 B2; try acb. unfold disj, kPageSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma record_vs_record : forall ch, In ch (chunk_list st) -> ch <> ch0 -> ch_end ch <= lo0 \/ hi0 <= ch_lo ch.
  Proof. intros ch Hch NE. destruct (records_sep s OK ch ch0 Hch H0) as [E|[D|D]]; [congruence| left; exact D| right; exact D]. Qed.

  (* [comment removed for export] *)
End RecordSep.

End HCW.

