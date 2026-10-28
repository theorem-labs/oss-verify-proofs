(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freeA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_facts RT_anndefs RT_annart.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition annsh (n v : Z) : list byte := repeat z8 (Z.to_nat (v / 8)) ++ fcrun (Z.to_nat ((n - v) / 8)).

Lemma fcrun_app : forall a b, fcrun (a + b) = fcrun a ++ fcrun b.
Proof. intros a b. unfold fcrun. rewrite repeat_app. reflexivity. Qed.

Lemma ru8_id : forall n, n mod 8 = 0 -> ru8 n = n.
Proof. intros n H. unfold ru8. lia. Qed.

Lemma annsh_len : forall n v, 0 <= v <= n -> v mod 8 = 0 -> n mod 8 = 0 -> Z.of_nat (length (annsh n v)) = n / 8.
Proof.
  intros n v Hv V8 N8. unfold annsh, fcrun. rewrite length_app, !repeat_length.
  pose proof (Z.div_mod v 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)). lia.
Qed.

Lemma ushadowA_upd : forall p n v' A, 0 <= v' <= n -> v' mod 8 = 0 -> n mod 16 = 0 ->
  ushadowA (alook p n ((p, n, v') :: arem p A)) n = annsh n v'.
Proof.
  intros p n v' A Hv V8 N16. rewrite alook_cons_same, alook_arem_same.
  assert (N8 : n mod 8 = 0) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
  destruct (ann_ok n v') eqn:OK.
  - apply ann_ok_spec in OK as (O1 & O2 & O3). unfold annsh. apply ushadowA_some; lia.
  - assert (v' = n) as ->.
    { destruct (Z.eq_dec v' n) as [E|NE]; [exact E|]. exfalso.
      assert (X : ann_ok n v' = true) by (apply ann_ok_spec; lia). rewrite OK in X. discriminate X. }
    cbn [ushadowA]. unfold ushadow, annsh. rewrite N8. cbn [Z.eqb]. rewrite Z.sub_diag. cbn. reflexivity.
Qed.

Lemma ushadowA_cur : forall p n v A, ((v = n /\ alook p n A = None) \/ (v < n /\ alook p n A = Some v)) -> 0 <= v -> n mod 16 = 0 ->
  ushadowA (alook p n A) n = annsh n v.
Proof.
  intros p n v A H Hv N16. assert (N8 : n mod 8 = 0) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
  destruct H as [(-> & E)|(Hlt & E)]; rewrite E.
  - cbn [ushadowA]. unfold ushadow, annsh. rewrite N8. cbn [Z.eqb]. rewrite Z.sub_diag. cbn. reflexivity.
  - pose proof (alook_ok p n A v E) as (O1 & O2 & O3). unfold annsh. apply ushadowA_some; lia.
Qed.

Lemma z8_run : forall k, repeat (Z_to_bv 8 0) k = repeat z8 k.
Proof. intros k. reflexivity. Qed.
Lemma fc_run : forall k, repeat (Z_to_bv 8 252) k = fcrun k.
Proof. intros k. reflexivity. Qed.

Lemma reshadow : forall (m m' : mem) (Wt : list ivl) sa n v v',
  0 <= sa -> 0 <= v <= n -> 0 <= v' <= n -> v <> v' -> v mod 8 = 0 -> v' mod 8 = 0 -> n mod 8 = 0 ->
  bytes_at asegs m sa (annsh n v) ->
  munch ((sa + Z.min v v' / 8, sa + Z.min v v' / 8 + (Z.max v v' - Z.min v v') / 8) :: Wt) m m' ->
  disjoint_from Wt sa (n / 8) ->
  bytes_at asegs m' (sa + Z.min v v' / 8) (repeat (Z_to_bv 8 (if v <? v' then 0 else 252)) (Z.to_nat ((Z.max v v' - Z.min v v') / 8))) ->
  bytes_at asegs m' sa (annsh n v').
Proof.
  intros m m' Wt sa n v v' Hsa Hv Hv' NE V8 V8' N8 OLD MU DW NEW.
  pose proof (Z.div_mod v 8 ltac:(lia)) as Dv. pose proof (Z.div_mod v' 8 ltac:(lia)) as Dv'. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
  destruct (Z_lt_le_dec v v') as [LT|GE].
  -
    rewrite (Z.min_l v v'), (Z.max_r v v') in MU, NEW by lia. rewrite (proj2 (Z.ltb_lt v v') LT), z8_run in NEW.
    unfold annsh in OLD |- *.
    replace (Z.to_nat ((n - v) / 8)) with (Z.to_nat ((v' - v) / 8) + Z.to_nat ((n - v') / 8))%nat in OLD by lia.
    rewrite fcrun_app in OLD.
    apply bytes_at_app in OLD as [B1 B23]. rewrite repeat_length in B23. apply bytes_at_app in B23 as [_ B3].
    unfold fcrun in B3 at 1. rewrite repeat_length in B3.
    replace (sa + Z.of_nat (Z.to_nat (v / 8)) + Z.of_nat (Z.to_nat ((v' - v) / 8))) with (sa + v' / 8) in B3 by lia.
    replace (Z.to_nat (v' / 8)) with (Z.to_nat (v / 8) + Z.to_nat ((v' - v) / 8))%nat by lia. rewrite repeat_app, <- app_assoc.
    apply bytes_at_app. rewrite repeat_length. split.
    + apply (bytes_at_transport asegs _ m m' _ _ B1 MU). rewrite repeat_length. cbn [disjoint_from fst snd]. split; [left; lia|].
      apply (dsj_sub Wt sa (n / 8)); [exact DW | lia | lia].
    + apply bytes_at_app. rewrite repeat_length. split.
      * replace (sa + Z.of_nat (Z.to_nat (v / 8))) with (sa + v / 8) by lia. exact NEW.
      * replace (sa + Z.of_nat (Z.to_nat (v / 8)) + Z.of_nat (Z.to_nat ((v' - v) / 8))) with (sa + v' / 8) by lia.
        apply (bytes_at_transport asegs _ m m' _ _ B3 MU). unfold fcrun. rewrite repeat_length. cbn [disjoint_from fst snd]. split; [right; lia|].
        apply (dsj_sub Wt sa (n / 8)); [exact DW | lia | lia].
  -
    assert (LT : v' < v) by lia.
    rewrite (Z.min_r v v'), (Z.max_l v v') in MU, NEW by lia. rewrite (proj2 (Z.ltb_ge v v') ltac:(lia)), fc_run in NEW.
    unfold annsh in OLD |- *.
    replace (Z.to_nat (v / 8)) with (Z.to_nat (v' / 8) + Z.to_nat ((v - v') / 8))%nat in OLD by lia.
    rewrite repeat_app, <- app_assoc in OLD.
    apply bytes_at_app in OLD as [B1 B23]. rewrite repeat_length in B23. apply bytes_at_app in B23 as [_ B3].
    rewrite repeat_length in B3.
    replace (sa + Z.of_nat (Z.to_nat (v' / 8)) + Z.of_nat (Z.to_nat ((v - v') / 8))) with (sa + v / 8) in B3 by lia.
    replace (Z.to_nat ((n - v') / 8)) with (Z.to_nat ((v - v') / 8) + Z.to_nat ((n - v) / 8))%nat by lia. rewrite fcrun_app.
    apply bytes_at_app. rewrite repeat_length. split.
    + apply (bytes_at_transport asegs _ m m' _ _ B1 MU). rewrite repeat_length. cbn [disjoint_from fst snd]. split; [left; lia|].
      apply (dsj_sub Wt sa (n / 8)); [exact DW | lia | lia].
    + apply bytes_at_app. unfold fcrun at 1. rewrite repeat_length. split.
      * replace (sa + Z.of_nat (Z.to_nat (v' / 8))) with (sa + v' / 8) by lia. exact NEW.
      * replace (sa + Z.of_nat (Z.to_nat (v' / 8)) + Z.of_nat (Z.to_nat ((v - v') / 8))) with (sa + v / 8) by lia.
        apply (bytes_at_transport asegs _ m m' _ _ B3 MU). unfold fcrun. rewrite repeat_length. cbn [disjoint_from fst snd]. split; [right; lia|].
        apply (dsj_sub Wt sa (n / 8)); [exact DW | lia | lia].
Qed.

Lemma pchunk_reshadow : forall (A A' : list (Z * Z * Z)) SB c i n (m m' : mem) W,
  pchunk A SB c i (CkAlloc n) m -> munch W m m' -> wmono asegs m m' ->
  p_abeg SB c i mod 8 = 0 ->
  disjoint_from W (p_abeg SB c i + rz_size n - 16) 16 -> (16 < rz_size n -> disjoint_from W (p_abeg SB c i) 16) ->
  disjoint_from W (shad (p_abeg SB c i)) (rz_size n / 8) ->
  disjoint_from W (shad (p_abeg SB c i + rz_size n + ru8 n)) (Z.max 0 ((ClassSize c - rz_size n - ru8 n) / 8)) ->
  bytes_at asegs m' (shad (p_abeg SB c i + rz_size n)) (ushadowA (alook (p_abeg SB c i + rz_size n) n A') n) ->
  pchunk A' SB c i (CkAlloc n) m'.
Proof.
  intros A A' SB c i n m m' W P MU WM AB8 A1 A2 A3 A4 NEW. unfold pchunk in *. cbv zeta in P. cbv zeta.
  destruct P as (Wr & Hh & Hl & (B1 & B2)). pose proof (rz_facts n) as (R1 & R2).
  split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (ahdr_transport W m m' _ _ Hh MU WM A1)|].
  split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
  unfold pshadow_allocA. split.
  - apply bytes_at_app in B1 as [B1 _]. apply bytes_at_app. split.
    + apply (bytes_at_transport asegs W m m' _ _ B1 MU). rewrite (farun_lenZ (rz_size n / 8)) by (apply Z.div_pos; lia). exact A3.
    + rewrite (farun_lenZ (rz_size n / 8)) by (apply Z.div_pos; lia).
      rewrite <- (shad_aligned_add (p_abeg SB c i) (rz_size n) AB8 ltac:(lia)). exact NEW.
  - apply (bytes_at_transport asegs W m m' _ _ B2 MU). rewrite farun_len. exact A4.
Qed.

Lemma schunk_reshadow : forall (A A' : list (Z * Z * Z)) k s (m m' : mem) W,
  schunk A k s m -> s_quar s = false -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W (s_mb s) 32 -> disjoint_from W (s_mb s + 4096) 16 -> disjoint_from W (s_mb s + 4096 + 2032) 16 ->
  disjoint_from W (shad (s_mb s)) 768 ->
  disjoint_from W (shad (s_mb s + 4096 + 2048 + ru8 (s_n s))) (Z.max 0 ((smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) / 8)) ->
  bytes_at asegs m' (shad (s_mb s + 4096 + 2048)) (ushadowA (alook (s_mb s + 4096 + 2048) (s_n s) A') (s_n s)) ->
  schunk A' k s m'.
Proof.
  intros A A' k s m m' W P Hq MU WM A1 A2 A3 A4 A5 NEW. unfold schunk in *. cbv zeta in P. cbv zeta. rewrite Hq in P |- *.
  destruct P as (Hs & Wr & Hl & Hh & St & B1 & B2 & B3).
  split; [unfold shdr in *; apply (rw_cells_transport asegs W m m' _ _ Hs MU WM); cbn [cells_size csize Nat.add length]; exact A1|].
  split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (lch_transport W m m' _ _ Hl MU WM A2)|].
  split; [exact (ahdr_transport W m m' _ _ Hh MU WM A3)|].
  split; [exact (stk_wmono m m' _ _ St WM)|].
  split; [apply (bytes_at_transport asegs W m m' _ _ B1 MU); rewrite farun_len; change (Z.max 0 ((4096 + 2048) / 8)) with 768; exact A4|].
  split; [exact NEW|].
  apply (bytes_at_transport asegs W m m' _ _ B3 MU). rewrite farun_len. exact A5.
Qed.

End GWIN.
Local Ltac kst := unfold SHB, SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, USTACK_TOP in *; lia.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

Theorem ann_ART_live : forall (Σ : rtsA) (m m' : mem) (p n lo' len usp : Z) (A' : list (Z * Z * Z)),
  ART_A Σ m -> In (p, n) (live Σ) -> 1 <= n -> n mod 16 = 0 ->
  0 <= lo' -> lo' + len <= n -> 0 <= len -> lo' mod 8 = 0 -> len mod 8 = 0 ->
  l_ACEIL (lay Σ) <= usp <= USTACK_TOP ->
  munch (W_ann (p + lo') len (l_ACEIL (lay Σ)) usp) m m' -> wmono asegs m m' ->
  (forall q k, q <> p -> alook q k A' = alook q k (ann Σ)) ->
  bytes_at asegs m' (shad p) (ushadowA (alook p n A') n) ->
  ART_A (set_ann Σ A') m' /\ (forall x, aclient (live Σ) (frames Σ) usp x -> outside (W_ann (p + lo') len (l_ACEIL (lay Σ)) usp) x).
Proof.
  intros Σ m m' p n lo' len usp A' HA HIN Hn1 N16 L0 L1 L2 L8 LN8 Husp MU WM ALK NEW.
  assert (N8 : n mod 8 = 0) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
  pose proof (ru8_id n N8) as RU.
  pose proof (geo_of_ART Σ m HA) as HG.
  pose proof (fk_aceil Σ HG) as (X1 & X2). pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  pose proof (rta_live_block Σ m HA p n HIN) as (P8 & _ & _ & _ & PCE).

  assert (PM8 : (p + lo') mod 8 = 0) by (rewrite Z.add_mod, P8, L8 by lia; reflexivity).
  pose proof (shad_aligned_add p lo' P8 L0) as SH1. pose proof (shad_aligned_add (p + lo') len PM8 L2) as SH2.
  pose proof (shad_aligned_add p n P8 ltac:(lia)) as SH3.
  assert (LD : 0 <= lo' / 8 /\ 0 <= len / 8 /\ lo' / 8 + len / 8 <= n / 8).
  { pose proof (Z.div_mod lo' 8 ltac:(lia)). pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
  destruct (geo_live Σ m HA p n HIN) as [(c & i & Hc & Hn & Ep & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & Hq & Hsn & Ep & Y1 & Y5)].
  -
    pose proof (fk_slot Σ HG c i _ Hc Hn) as (Z1 & Z2 & Z3 & Z4).
    pose proof (live_in_slot Σ m HA c i n Hc Hn) as (Q1 & Q2 & Q3 & Q4).
    pose proof (abeg_mod8 Σ m HA c i Hc) as AB8. pose proof (rz_facts n) as (R1 & R2).
    assert (HC32 : c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc; lia).
    assert (HS47 : p_abeg (l_SB (lay Σ)) c i + ClassSize c <= 2 ^ 47) by (unfold rb, kUserCap in *; clear - HC32 Z1 Z2 Z3 P1 P3 P4 X2; lia).
    assert (HE : 0 <= p_abeg (l_SB (lay Σ)) c i /\ p_abeg (l_SB (lay Σ)) c i <= p + lo' /\ p + lo' + len <= p_abeg (l_SB (lay Σ)) c i + ClassSize c
                 /\ p_abeg (l_SB (lay Σ)) c i + ClassSize c <= 2 ^ 47 /\ 0 <= len) by (unfold rb in *; lia).
    assert (ESL : forall c' i' st, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') [(c, i)] ->
                   p_abeg (l_SB (lay Σ)) c' i' + ClassSize c' <= p_abeg (l_SB (lay Σ)) c i \/ p_abeg (l_SB (lay Σ)) c i + ClassSize c <= p_abeg (l_SB (lay Σ)) c' i').
    { intros c' i' st Hc' Hn' HD.
      assert (Hne : c <> c' \/ i <> i') by (destruct (Z.eq_dec c c') as [<-|X]; [right; intros <-; apply HD; left; reflexivity | left; exact X]).
      destruct (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hn' Hne) as [X|X]; [right; exact X | left; exact X]. }
    assert (EAP : forall lo hi, (hi <= l_PRB (lay Σ) \/ l_PRB (lay Σ) + 0x2000011000 <= lo) ->
                   (forall k0 s0, nth_error (sec Σ) k0 = Some s0 -> In k0 [] -> hi <= s_mb s0 \/ s_mb s0 + smsz (s_n s0) <= lo) ->
                   hi <= p_abeg (l_SB (lay Σ)) c i \/ p_abeg (l_SB (lay Σ)) c i + ClassSize c <= lo).
    { intros lo hi Hoff _. unfold rb, kUserCap in *. clear - Hoff Z1 Z2 Z3 P3 P4 HC32 Hc. lia. }
    split; [| exact (an_client Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp [(c, i)] [] HA HE Husp EAP)].
    unshelve eapply (ann_ART Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp [(c, i)] [] HA HE
                       _ EAP _ m' A' MU WM).
    +   intros c' Hc'.
      destruct (Z.eq_dec c' c) as [->|X]; [right; exact Z2|].
      assert (0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) by (apply Z.mul_nonneg_nonneg; [pose proof (ClassSize_range c' Hc'); lia | lia]).
      assert (c' < c \/ c < c') as [Hl|Hl] by (clear - X; lia); [left | right]; unfold rb, kUserCap in *; clear - Hl H Z1 Z2 Z3 Hc Hc'; nia.
    +   intros c' i' [E|[]]. injection E as <- <-. exists n. exact Hn.
    +
      cbn [lay pr sec ann set_ann]. split.
      * intros c' i' st Hc' Hn'.
        destruct (Z.eq_dec c' c) as [->|Hcc]; [destruct (Nat.eq_dec i' i) as [->|Hii]|].
        --
           rewrite Hn in Hn'. injection Hn' as <-.
           destruct (ART_chunk Σ m HA) as [PC _].
           apply (pchunk_reshadow (ann Σ) A' _ c i n m m' _ (PC c i _ Hc Hn) MU WM AB8).
           ++ apply (an_slot' Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp HA HE c i (CkAlloc n));
                [exact Hc | exact Hn | unfold p_ubeg in *; lia | unfold p_ubeg in *; lia].
           ++ intros Hr. apply (an_slot' Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp HA HE c i (CkAlloc n));
                [exact Hc | exact Hn | lia | pose proof (ClassSize_range c Hc); lia].
           ++
              pose proof (shad_aligned_add (p_abeg (l_SB (lay Σ)) c i) (rz_size n) AB8 ltac:(lia)) as SH4.
              assert (EQ : shad (p_abeg (l_SB (lay Σ)) c i) + rz_size n / 8 = shad p) by (rewrite <- SH4; f_equal; unfold p_ubeg in *; lia).
              pose proof (fk_shad_mono p (p + lo') ltac:(lia)) as M1. pose proof (shad_hi (p + lo') ltac:(lia)) as M2.
              unfold W_ann. cbn [disjoint_from]. split; [left; clear - EQ M1; lia|]. split; [left; clear - EQ M1 M2 X1; lia | exact I].
           ++
              rewrite RU. replace (p_abeg (l_SB (lay Σ)) c i + rz_size n + n) with (p + n) by (unfold p_ubeg in *; lia).
              pose proof (fk_shad_mono (p + lo' + len) (p + n) ltac:(lia)) as M1.
              pose proof (shad_hi (p_abeg (l_SB (lay Σ)) c i + ClassSize c) HS47) as M2.
              pose proof (fk_shad_le2 (p + n) (ClassSize c - rz_size n - n) ltac:(lia) ltac:(lia)) as M3.
              replace (p + n + (ClassSize c - rz_size n - n)) with (p_abeg (l_SB (lay Σ)) c i + ClassSize c) in M3 by (unfold p_ubeg in *; lia).
              assert (0 <= (ClassSize c - rz_size n - n) / 8) by (apply Z.div_pos; lia).
              unfold W_ann. cbn [disjoint_from].
              split; [right; clear - SH2 M1; lia|]. split; [left; rewrite Z.max_r by lia; clear - M2 M3 X1 H; lia | exact I].
           ++ replace (p_abeg (l_SB (lay Σ)) c i + rz_size n) with p by (unfold p_ubeg in *; lia). exact NEW.
        -- apply (an_pchunk Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp [(c, i)] HA HE ESL m' A' c i' st MU WM Hc Hn');
             [intros [E|[]]; injection E as E2; exact (Hii (eq_sym E2)) |].
           intros n0 ->. apply ALK.
           pose proof (slot_apart Σ m HA c i c i' _ _ Hc Hc Hn Hn' (or_intror (fun E => Hii (eq_sym E)))) as SA.
           pose proof (live_in_slot Σ m HA c i' n0 Hc Hn') as (_ & W1 & W2 & W3). unfold p_ubeg in *. clear - SA W1 W2 W3 Ep Q1 Q2 Q3 Hn1. lia.
        -- apply (an_pchunk Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp [(c, i)] HA HE ESL m' A' c' i' st MU WM Hc' Hn');
             [intros [E|[]]; injection E as E1 E2; exact (Hcc (eq_sym E1)) |].
           intros n0 ->. apply ALK.
           pose proof (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hn' (or_introl (fun E => Hcc (eq_sym E)))) as SA.
           pose proof (live_in_slot Σ m HA c' i' n0 Hc' Hn') as (_ & W1 & W2 & W3). unfold p_ubeg in *. clear - SA W1 W2 W3 Ep Q1 Q2 Q3 Hn1. lia.
      * intros k s Hk.
        apply (an_schunk Σ m (p_abeg (l_SB (lay Σ)) c i) (p_abeg (l_SB (lay Σ)) c i + ClassSize c) (p + lo') len usp [] HA HE EAP m' A' k s MU WM Hk ltac:(intros [])).
        apply ALK. pose proof (fk_map Σ HG k s Hk) as (Hsn1 & _ & _ & _ & AP & _ & _ & Hroom & _).
        unfold apart, rb, kUserCap, p_ubeg in *. unfold ru8 in Hroom. pose proof (Z.div_pos (s_n s + 7) 8 ltac:(lia) ltac:(lia)).
        clear - AP Hroom H Z1 Z2 Z3 P3 P4 HC32 Hc Ep Q1 Q2 Q3 Hn1. lia.
  -
    destruct (In_nth_error _ _ Hs) as (k & Hk).
    pose proof (fk_map Σ HG k s Hk) as (Hsn1 & M0 & MCE & M5 & AP & AF & AG & Hroom & Hu & HSP).
    pose proof (map_geo Σ m HA k s Hk) as (_ & (_ & MB4096 & _) & _ & MS4096 & _).
    assert (MB8 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) MB4096); exists 512; reflexivity).
    rewrite Hsn in *.
    assert (HE : 0 <= s_mb s /\ s_mb s <= p + lo' /\ p + lo' + len <= s_mb s + smsz n /\ s_mb s + smsz n <= 2 ^ 47 /\ 0 <= len) by (unfold s_ubeg in *; lia).
    assert (ESL : forall c' i' st, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st -> ~ In (c', i') [] ->
                   p_abeg (l_SB (lay Σ)) c' i' + ClassSize c' <= s_mb s \/ s_mb s + smsz n <= p_abeg (l_SB (lay Σ)) c' i').
    { intros c' i' st Hc' Hn' _. pose proof (fk_slot Σ HG c' i' st Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
      assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia). unfold apart, rb, kUserCap in *. clear - AP H Z1 Z2 Z3 P3 P4 Hc'. lia. }
    assert (EAP : forall lo hi, (hi <= l_PRB (lay Σ) \/ l_PRB (lay Σ) + 0x2000011000 <= lo) ->
                   (forall k0 s0, nth_error (sec Σ) k0 = Some s0 -> In k0 [k] -> hi <= s_mb s0 \/ s_mb s0 + smsz (s_n s0) <= lo) -> hi <= s_mb s \/ s_mb s + smsz n <= lo).
    { intros lo hi _ Hds. pose proof (Hds k s Hk ltac:(left; reflexivity)) as X. rewrite Hsn in X. exact X. }
    split; [| exact (an_client Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp [] [k] HA HE Husp EAP)].
    unshelve eapply (ann_ART Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp [] [k] HA HE _ EAP _ m' A' MU WM).
    +   intros c' Hc'. assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia).
      assert (0 <= ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) by (apply Z.mul_nonneg_nonneg; [pose proof (ClassSize_range c' Hc'); lia | lia]).
      unfold apart, rb in *. clear - AP H H0 P3 P4 Hc'. lia.
    +   intros c' i' [].
    +
      cbn [lay pr sec ann set_ann]. split.
      * intros c' i' st Hc' Hn'.
        apply (an_pchunk Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp [] HA HE ESL m' A' c' i' st MU WM Hc' Hn' ltac:(intros [])).
        intros n0 ->. apply ALK. pose proof (fk_slot Σ HG c' i' _ Hc' Hn') as (Z1 & Z2 & Z3 & Z4).
        pose proof (live_in_slot Σ m HA c' i' n0 Hc' Hn') as (_ & W1 & W2 & W3).
        assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc'; lia).
        unfold apart, rb, kUserCap, p_ubeg, s_ubeg in *. clear - AP H Z1 Z2 Z3 W1 W2 W3 P3 P4 Hc' Ep Y1 Hn1. lia.
      * intros k' s' Hk'. destruct (Nat.eq_dec k' k) as [->|Hkk].
        --
           rewrite Hk in Hk'. injection Hk' as <-.
           destruct (ART_chunk Σ m HA) as [_ SC].
           apply (schunk_reshadow (ann Σ) A' k s m m' _ (SC k s Hk) Hq MU WM).
           ++ apply (an_secmap' Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp HA HE k s); [exact Hk | lia | rewrite Hsn; lia].
           ++ apply (an_secmap' Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp HA HE k s); [exact Hk | lia | rewrite Hsn; lia].
           ++ apply (an_secmap' Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp HA HE k s); [exact Hk | lia | rewrite Hsn; unfold ru8 in Hroom; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia].
           ++
              pose proof (shad_aligned_add (s_mb s) 6144 MB8 ltac:(lia)) as SH4. change (6144 / 8) with 768 in SH4.
              replace (s_mb s + 6144) with p in SH4 by (unfold s_ubeg in *; lia).
              pose proof (fk_shad_mono p (p + lo') ltac:(lia)) as M1. pose proof (shad_hi (p + lo') ltac:(unfold s_ubeg in *; lia)) as M2.
              unfold W_ann. cbn [disjoint_from]. split; [left; clear - SH4 M1; lia|]. split; [left; clear - SH4 M1 M2 X1; lia | exact I].
           ++
              rewrite Hsn, RU. replace (s_mb s + 4096 + 2048 + n) with (p + n) by (unfold s_ubeg in *; lia).
              pose proof (fk_shad_mono (p + lo' + len) (p + n) ltac:(lia)) as M1.
              pose proof (shad_hi (s_mb s + smsz n) ltac:(lia)) as M2.
              pose proof (fk_shad_le2 (p + n) (smsz n - 4096 - 2048 - n) ltac:(unfold s_ubeg in *; lia) ltac:(unfold s_ubeg in *; lia)) as M3.
              replace (p + n + (smsz n - 4096 - 2048 - n)) with (s_mb s + smsz n) in M3 by (unfold s_ubeg in *; lia).
              assert (0 <= (smsz n - 4096 - 2048 - n) / 8) by (apply Z.div_pos; unfold s_ubeg in *; lia).
              unfold W_ann. cbn [disjoint_from].
              split; [right; clear - SH2 M1; lia|]. split; [left; rewrite Z.max_r by lia; clear - M2 M3 X1 H; lia | exact I].
           ++ rewrite Hsn. replace (s_mb s + 4096 + 2048) with p by (unfold s_ubeg in Ep; lia). exact NEW.
        -- apply (an_schunk Σ m (s_mb s) (s_mb s + smsz n) (p + lo') len usp [k] HA HE EAP m' A' k' s' MU WM Hk' ltac:(intros [E|[]]; exact (Hkk (eq_sym E)))) .
           apply ALK. pose proof (HSP k' s' Hk' Hkk) as SA. pose proof (fk_map Σ HG k' s' Hk') as (Hsn1' & _ & _ & _ & _ & _ & _ & Hroom' & _).
           unfold apart, s_ubeg in *. unfold ru8 in Hroom, Hroom'. pose proof (Z.div_pos (s_n s' + 7) 8 ltac:(lia) ltac:(lia)).
           pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)).
           clear - SA Hroom Hroom' H H0 Ep Y1 Hn1. lia.
Qed.

End GWIN.
