(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition set_ql (Σ : rtsA) (l : list batch) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) l (qg Σ) (dep Σ) (fs0 Σ) (fs1 Σ) (fs2 Σ) (fs3 Σ) (fs4 Σ) (ia_init Σ)
    (credit Σ) (live Σ) (frames Σ).

Lemma reg_avoid_upd : forall W SB c r i st, reg_avoid W SB c r -> reg_avoid W SB c (upd_reg r i st).
Proof. intros W SB c r i st H. unfold reg_avoid, upd_reg in *. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length. exact H. Qed.

Lemma se_shad_des : forall (Σ : rtsA) j0 jB st0 stB usp, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  nth_error (r_st (pr Σ 24)) jB = Some stB -> l_ACEIL (lay Σ) + 0x10000 <= usp ->
  forall j st, nth_error (r_st (pr Σ 24)) j = Some st ->
  disjoint_from (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp) (shad (p_abeg (l_SB (lay Σ)) 24 j)) 1024.
Proof.
  intros Σ j0 jB st0 stB usp HG Hj0 HjB Hsp j st Hj.
  pose proof (se_geo Σ j0 jB st0 stB HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  pose proof (fk_slot Σ HG 24 j st ltac:(lia) Hj) as (Z1 & Z2 & Z3 & Z4). change (ClassSize 24) with 8192 in *.
  pose proof (shad_lo (p_abeg (l_SB (lay Σ)) 24 j) ltac:(clear - Z1 K1 K5; unfold rb in *; lia)) as Q1.
  pose proof (fk_shad_le2 (p_abeg (l_SB (lay Σ)) 24 j) 8192 ltac:(clear - Z1 K1 K5; unfold rb in *; lia) ltac:(lia)) as E1. change (8192 / 8) with 1024 in E1.
  pose proof (shad_hi (p_abeg (l_SB (lay Σ)) 24 j + 8192) ltac:(clear - Z1 Z2 Z3 K4 K5 K6 K16; unfold rb, kUserCap in *; lia)) as Q2.
  unfold W_E. cbn [disjoint_from].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - T4 Q1 Q2 E1; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [clear - K3 K5 K7 Q2 E1; unfold K_HIGH_SHADOW_hi, SHB, rb in *; lia|].
  split; [clear - K3 K5 K9 Q2 E1; unfold K_HIGH_SHADOW_hi, SHB, rb in *; lia|].
  split; [clear - Q2 E1 K15 Hsp; unfold SHB in *; lia | exact I].
Qed.

Lemma se_grant67 : forall (Σ : rtsA) j0 jB st0 stB usp, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
  nth_error (r_st (pr Σ 24)) jB = Some stB -> l_ACEIL (lay Σ) + 0x10000 <= usp ->
  forall j b gn a k, nth_error (startup_grants (lay Σ)) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat -> b <= a -> a + k <= b + gn ->
  disjoint_from (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp) a k.
Proof.
  intros Σ j0 jB st0 stB usp HG Hj0 HjB Hsp j b gn a k Hj Hjr H1 H2.
  pose proof (se_geo Σ j0 jB st0 stB HG Hj0 HjB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
  pose proof (g_grant Σ HG b gn (nth_error_In _ _ Hj)) as (B1 & B2 & B3 & B4 & B5).
  assert (HT1 : apart b gn (l_T (lay Σ)) 4096).
  { pose proof (g_apart Σ HG 2 j (l_T (lay Σ), 4096) (b, gn) ltac:(lia) eq_refl Hj) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  assert (HT2 : apart b gn (l_PRB (lay Σ)) 0x2000011000).
  { pose proof (g_apart Σ HG 0 j (l_PRB (lay Σ), 0x2000011000) (b, gn) ltac:(lia) eq_refl Hj) as X. cbn [fst snd] in X. unfold apart in *. lia. }
  unfold W_E. cbn [disjoint_from]. unfold apart in *.
  split; [clear - H1 H2 HT1; lia|]. split; [clear - H1 H2 HT1; lia|]. split; [clear - H1 H2 HT1; lia|].
  split; [clear - H1 H2 HT2 K5 K6 K7 K8 K11 K12; unfold rb, kUserCap in *; lia|].
  split; [clear - H1 H2 HT2 K5 K6 K9 K10 K11 K12; unfold rb, kUserCap in *; lia|].
  split; [clear - H2 B3 Hsp; lia | exact I].
Qed.

Lemma qbytes_eq : forall bs, R_quar_defs.qbytes bs = RT_state.qbytes bs.
Proof.
  induction bs as [|[b ents] bs IH]; [reflexivity|]. unfold R_quar_defs.qbytes, RT_state.qbytes, qsum, qn, bsum in *. cbn [fold_right length snd] in *.
  rewrite IH. lia.
Qed.

Lemma qwf_ql : forall Σ, rt_wf0 Σ -> qwf (l_SB (lay Σ)) (ql Σ).
Proof.
  intros Σ HW. pose proof (geo_of_wf0 Σ HW) as HG. destruct HW as (_ & HR & _ & HS & HQ & _).
  destruct HQ as (_ & _ & QB & QN & QL & QE & _ & _). pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  split.
  - rewrite map_app in QN. apply NoDup_ListNoDup in QN. exact (NoDup_app_remove_r _ _ QN).
  - apply Forall_forall. intros b Hb. assert (Hb' : In b (ql Σ ++ qg Σ)) by (apply in_or_app; left; exact Hb).
    destruct (proj1 (Forall_forall _ _) QB b Hb') as (i & Hi & Eb).
    pose proof (g_slot_geo Σ HG 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & _). change (ClassSize 24) with 8192 in *.
    split; [|split; [|split; [|split]]].
    + rewrite Eb. unfold p_abeg. apply Z.mod_divide in P3; [|lia]. destruct P3 as [q Hq]. rewrite Hq.
      replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat i * 8192) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat i) * 8192) by ring. apply Z.mod_mul. lia.
    + rewrite Eb. unfold r24, rb in *. lia.
    + rewrite Eb. unfold r24, rb, kUserCap in *. lia.
    + exact (proj1 (Forall_forall _ _) QL b Hb').
    + apply Forall_forall. intros e He. assert (Hq : In e (qents Σ)).
      { unfold qents. apply in_flat_map. exists b. split; [exact Hb' | exact He]. }
      destruct (proj1 (Forall_forall _ _) QE e Hq) as [(c & j & Hc & Hj & _)|(s & Hs & _ & Hn & _)].
      * destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hj)) as X. cbv beta iota in X. lia.
      * destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (X & _). lia.
Qed.

Section App.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (D' : depot) (pre : list batch) (j0 : nat) (ents : list (Z * Z)) (usp : Z).
Hypothesis HW0 : rt_wf Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HQL : ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some CkBatch.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D').
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 j0) usp).
#[local] Notation Wa := [(l_T (lay Σ) + 80, l_T (lay Σ) + 112); (p_abeg (l_SB (lay Σ)) 24 j0, p_abeg (l_SB (lay Σ)) 24 j0 + 8192); (usp - 2400, usp)].

Let HG : geo_ok Σ := geo_of_wf Σ HW0.

Definition app_post (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m4 : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bgasegs)
    /\ ARTc Σ2 m' /\ mem_inv bgasegs m' /\ wmono bgasegs m4 m' /\ stk bgasegs m' lo (bv_unsigned sp) /\ munch Wa m4 m'.

End App.

Lemma qents_app_snoc : forall (pre : list (Z * list (Z * Z))) (b : Z) (ents : list (Z * Z)) (e : Z * Z) (qg : list (Z * list (Z * Z))), flat_map snd ((pre ++ [(b, ents ++ [e])]) ++ qg) = flat_map snd pre ++ ents ++ e :: flat_map snd qg.
Proof. intros. rewrite !flat_map_app. cbn [flat_map snd]. rewrite app_nil_r, <- !app_assoc. reflexivity. Qed.
Lemma qents_app : forall (pre : list (Z * list (Z * Z))) (b : Z) (ents : list (Z * Z)) (qg : list (Z * list (Z * Z))), flat_map snd ((pre ++ [(b, ents)]) ++ qg) = flat_map snd pre ++ ents ++ flat_map snd qg.
Proof. intros. rewrite !flat_map_app. cbn [flat_map snd]. rewrite app_nil_r, <- !app_assoc. reflexivity. Qed.

Lemma new_ent_fresh : forall Σ m c i n, ART_A Σ m -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  ~ In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) (map fst (qents Σ)).
Proof.
  intros Σ m c i n HA Hc Hn Hin. apply in_map_iff in Hin as (e & Ee & He).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & HS & (_ & _ & _ & _ & _ & QE & _) & _).
  pose proof (live_in_slot Σ m HA c i n Hc Hn) as (_ & R16 & F & F0).
  pose proof (slot_geo Σ m HA c i _ Hc Hn) as (S1 & S2 & S3 & S4 & _). pose proof (geo_prb Σ m HA) as (P1 & P2 & _).
  destruct (proj1 (Forall_forall _ _) QE e He) as [(c' & i' & Hc' & Hi' & E')|(s & Hs & _ & Hsn & E')].
  - destruct (Z.eq_dec c c') as [<-|Hcc]; [destruct (Nat.eq_dec i i') as [<-|Hii]|].
    + rewrite Hn in Hi'. discriminate.
    + pose proof (slot_apart Σ m HA c i c i' _ _ Hc Hc Hn Hi' (or_intror Hii)) as Y.
      pose proof (slot_geo Σ m HA c i' _ Hc Hi') as (Z1 & Z2 & _).
      pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
      pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi')) as X. cbv beta iota in X. pose proof (rz_facts (snd e)) as (_ & R').
      rewrite E' in Ee. lia.
    + pose proof (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hi' (or_introl Hcc)) as Y.
      pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
      pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi')) as X. cbv beta iota in X. pose proof (rz_facts (snd e)) as (_ & R').
      rewrite E' in Ee. lia.
  - destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn' & _ & Ha & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. rewrite E' in Ee.
    unfold apart, p_abeg, rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma nodup_insert : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> NoDup (l1 ++ x :: l2).
Proof.
  intros l1 l2 x H Hx. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup.
  apply (Permutation.Permutation_NoDup (Permutation.Permutation_middle l1 l2 x)). constructor; [exact Hx | exact H].
Qed.

Lemma qbytes_app_ent : forall pre b ents e, RT_state.qbytes (pre ++ [(b, ents ++ [e])]) = RT_state.qbytes (pre ++ [(b, ents)]) + snd e.
Proof. intros. rewrite <- !qbytes_eq, !qbytes_snoc, bsum_app. unfold bsum. cbn [fold_right]. lia. Qed.

