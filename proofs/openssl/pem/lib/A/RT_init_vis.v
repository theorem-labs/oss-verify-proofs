(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore
  AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_state RT_rep RT_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Lemma shreg_noseg : forall z, shreg z -> find_segment asegs z 1 = None.
Proof.
  intros z Hs.
  unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments.
  cbn [find_segment].
  unfold Asan.Asan_segment_000, Asan.Asan_segment_001,
    Asan.Asan_segment_002, Asan.Asan_segment_003.
  cbn [seg_base seg_size]. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs.
  destruct Hs as [Hs|Hs];
    repeat match goal with |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]; cbn [andb] end; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_side (k : list kentry) (p : expr * expr) : bool :=
  fact_ok k (KRange (esub (fst p) (eaddz e_pgsp (-8388608))) 0 (2 ^ 40)).

Definition vis_p (A : atable) (ch : acs) (p : expr * expr) : bool :=
  let k := kn ch in
  let '(pb, pk) := split_lit (fst p) in
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in
  (* [comment removed for export] *)
  (fact_ok k (KAlign (fst p) 8) && flat_x k pb pk (snd p)
   && (if stk_side k p then true
       else (if ranges_apart_x k pb pk (snd p) (ELit 0) K_LOW_SHADOW_lo (ELit (K_HIGH_SHADOW_hi - K_LOW_SHADOW_lo))
             then (if kwritable_x k k sb sk sn then true
                   else existsb (fun mp => negb (is_fog mp) && xinside k pb pk (snd p) (am_base mp) 0 (am_len mp)) (a_maps ch))
             else false)))%bool.

(* [comment removed for export] *)
Definition ghost_p (ch : acs) (p : expr * expr) : bool :=
  let k := kn ch in
  let '(pb, pk) := split_lit (fst p) in
  (flat_x k pb pk (snd p) && ranges_apart_x k pb pk (snd p) (ELit 0) K_LOW_SHADOW_lo (ELit (K_HIGH_SHADOW_hi - K_LOW_SHADOW_lo)))%bool.

Definition hs_vis_ok (A : atable) (ch : acs) : bool := (forallb (vis_p A ch) (a_vis ch) && forallb (ghost_p ch) (a_ghost ch))%bool.

(* [comment removed for export] *)

Section Vis.
Variables (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable A' : list (Z * Z).
(* [comment removed for export] *)
Hypothesis SINV_pgsp : forall E0 M0, SINV E0 M0 -> APS.uE E0 e_pgsp = pgdown ISP.
Hypothesis HISP : sp_window_lo <= ISP <= sp_window_hi.

#[local] Notation M := (APS.Mr A argH E ch model FULL).

Lemma rv_know : know_ok asegs E M (kn ch).
Proof. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma rv_shadow_den : forall b n sb sk sn, shadow_of A (kn ch) b n = (sb, sk, sn) -> 0 <= estart E (SA sb sk) <= 2 ^ 64 ->
  estart E (SA sb sk) = SHB + uE E b / 8 /\ elenZ E sn = uE E n / 8.
Proof.
  intros b n sb sk sn H Hst. unfold shadow_of in H.
  destruct (split_lit (eadd (mkSrl (kn ch) b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection H as <- <- <-.
  assert (Usrl : forall e, bv_unsigned (edenot E (mkSrl (kn ch) e 3)) = uE E e / 8).
  { intros e. rewrite (mkSrl_denot asegs E M (kn ch) e 3 (Z_to_bv 64 3) rv_know) by (rewrite unsigned_lit by lia; reflexivity).
    rewrite u_srl64. rewrite unsigned_lit by lia. reflexivity. }
  split; [|unfold elenZ; apply Usrl].
  pose proof (APS.split_lit_denot E _ sb' sk' Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
  apply (f_equal bv_unsigned) in D. rewrite u_add64, Usrl, !u_lit64 in D.
  pose proof (u64_range (edenot E b)) as Rb. unfold two64 in D. rewrite Hshoff in D. rewrite (Z.mod_small SHB) in D by (unfold SHB; lia).
  assert (Hb8 : 0 <= uE E b / 8 < 2 ^ 61).
  { unfold uE. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.mod_small (uE E b / 8 + SHB)) in D by (unfold SHB; lia).
  unfold estart in *. cbn [a_base a_off] in *.
  destruct (Z.eq_dec (bv_unsigned (edenot E sb') + sk') (2 ^ 64)) as [Eq|Ne].
  - rewrite Eq, Z_mod_same_full in D. unfold SHB in D. lia.
  - rewrite Z.mod_small in D by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_wr_present : forall sb sk sn (a : word), kwritable_x (kn ch) (kn ch) sb sk sn = true ->
  estart E (SA sb sk) <= bv_unsigned a < estart E (SA sb sk) + elenZ E sn -> shreg (bv_unsigned a) -> M a <> None.
Proof.
  intros sb sk sn a Hk Ha Hs.
  destruct (APSX.kwritable_x_sound asegs E M (kn ch) (kn ch) sb sk sn rv_know rv_know Hk) as (W & W1 & W2).
  pose proof (W (Z.to_nat (elenZ E sn)) ltac:(rewrite Z2Nat.id by (unfold elenZ; pose proof (u64_range (edenot E sn)); lia); lia)) as Wj.
  pose proof (store_ok_wview asegs M _ _ (Z.to_nat (bv_unsigned a - estart E (SA sb sk))) Wj ltac:(lia)) as Wi.
  rewrite unsigned_lit in Wi by lia. rewrite Z2Nat.id in Wi by lia.
  replace (estart E (SA sb sk) + (bv_unsigned a - estart E (SA sb sk))) with (bv_unsigned a) in Wi by lia.
  unfold wa in Wi. rewrite Z_to_bv_bv_unsigned in Wi. unfold wview in Wi. rewrite (shreg_noseg _ Hs) in Wi.
  destruct (M a); [discriminate | exact Wi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rv_diff : forall a b z lo hi, 0 <= lo -> hi < 2 ^ 63 -> 0 <= z < 2 ^ 40 -> z <= uE E b -> uE E b < 2 ^ 48 ->
  kentry_ok asegs E M (KRange (esub a (eaddz b (- z))) lo hi) -> uE E b - z + lo <= uE E a <= uE E b - z + hi.
Proof.
  intros a b z lo hi Hlo Hhi Hz Hzb Hb K. cbn [kentry_ok] in K. unfold esub, eaddz in K. rewrite !mkAlu_denot in K.
  rewrite u_sub64, u_add64 in K. cbn [edenot] in K. rewrite u_lit64 in K. unfold two64 in K. unfold uE in *.
  pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E b)) as Rb.
  set (uA := bv_unsigned (edenot E a)) in *. set (uB := bv_unsigned (edenot E b)) in *.
  assert (E1 : (uB + - z mod 2 ^ 64) mod 2 ^ 64 = uB - z).
  { rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia. }
  rewrite E1 in K.
  destruct (Z_le_dec 0 (uA - (uB - z))) as [D|D].
  - rewrite Z.mod_small in K by lia. lia.
  - exfalso. assert (E2 : (uA - (uB - z)) mod 2 ^ 64 = uA - (uB - z) + 2 ^ 64).
    { rewrite <- (Z.mod_small (uA - (uB - z) + 2 ^ 64) (2 ^ 64)) by lia.
      rewrite Z.add_mod by lia. rewrite Z_mod_same_full, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
    rewrite E2 in K. lia.
Qed.

(* [comment removed for export] *)
Lemma rv_pgsp : uE E e_pgsp - 8388608 = pg_dn (bv_unsigned (vm_init_sp (m_vmmaps model)) - STACK_WIN).
Proof.
  destruct (APS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. rewrite I1.
  pose proof (SINV_pgsp E FULL (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as P. unfold APS.uE in P. unfold uE. rewrite P.
  unfold pgdown, pg_dn, STACK_WIN.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma rv_case : forall p, In p (a_vis ch) -> hs_vis_ok A ch = true ->
  let b := bv_unsigned (edenot E (fst p)) in let n := bv_unsigned (edenot E (snd p)) in
  b mod 8 = 0 /\ 0 <= b /\ b + n <= 2 ^ 64
  /\ (pg_dn (bv_unsigned (vm_init_sp (m_vmmaps model)) - STACK_WIN) <= b
      \/ ((b + n <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= b)
          /\ ((forall a : word, SHB + b / 8 <= bv_unsigned a < SHB + (b + n) / 8 -> shreg (bv_unsigned a) -> M a <> None)
              \/ exists e, In e (vm_maps (m_vmmaps model)) /\ bv_unsigned (fst e) <= b /\ b + n <= bv_unsigned (fst e) + bv_unsigned (snd e)))).
Proof.
  intros p Hp HV b n. unfold hs_vis_ok in HV. apply andb_prop in HV as [HV _].
  pose proof (proj1 (forallb_forall _ _) HV p Hp) as Hvp. unfold vis_p in Hvp.
  destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
  destruct (shadow_of A (kn ch) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  apply andb_prop in Hvp as [Hvp Hopt]. apply andb_prop in Hvp as [Hal Hflat].
  pose proof (APS.fact_ok_sound asegs E M (kn ch) _ rv_know Hal) as Hal'. cbn [kentry_ok] in Hal'. destruct Hal' as (_ & Hal').
  destruct (APS.flat_x_sound asegs E M (kn ch) pb pk (snd p) rv_know Hflat) as (F1 & F2 & F3).
  pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up. fold b in Up. fold n in F2.
  split; [exact Hal'|]. split; [lia|]. split; [lia|].
  destruct (stk_side (kn ch) p) eqn:Hstk.
  - (* [comment removed for export] *)
    left. unfold stk_side in Hstk.
    pose proof (APS.fact_ok_sound asegs E M (kn ch) _ rv_know Hstk) as K.
    assert (Hpg : 8388608 <= uE E e_pgsp < 2 ^ 48).
    { pose proof rv_pgsp as P. destruct (APS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. rewrite I1 in P.
      unfold sp_window_lo, sp_window_hi, pg_dn, STACK_WIN in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    pose proof (rv_diff (fst p) e_pgsp 8388608 0 (2 ^ 40) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) K) as D.
    rewrite <- rv_pgsp. unfold uE in D. fold b in D. unfold uE. lia.
  - (* [comment removed for export] *)
    right. destruct (ranges_apart_x (kn ch) pb pk (snd p) (ELit 0) K_LOW_SHADOW_lo (ELit (K_HIGH_SHADOW_hi - K_LOW_SHADOW_lo))) eqn:Hap; [|discriminate].
    pose proof (ranges_apart_x_sound asegs E M (kn ch) _ _ _ _ _ _ rv_know Hap) as X.
    rewrite (APS.elenZ_lit E) in X by (unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi; lia).
    unfold estart in X. cbn [a_base a_off edenot] in X. rewrite unsigned_lit in X by lia. unfold elenZ in X.
    unfold estart in Up. cbn [a_base a_off] in Up. rewrite <- Up in X. fold n in X.
    split; [unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia|].
    destruct (kwritable_x (kn ch) (kn ch) sb sk sn) eqn:Hkw.
    + left. intros a Ha Hs.
      destruct (APSX.kwritable_x_sound asegs E M (kn ch) (kn ch) sb sk sn rv_know rv_know Hkw) as (_ & W1 & W2).
      destruct (rv_shadow_den (fst p) (snd p) sb sk sn Hsh ltac:(unfold elenZ in W2; pose proof (u64_range (edenot E sn)); lia)) as (S1 & S2).
      apply (rv_wr_present sb sk sn a Hkw); [|exact Hs]. rewrite S1, S2. unfold uE. fold b n.
      assert (Hbn : (b + n) / 8 = b / 8 + n / 8).
      { pose proof Hal' as Hal8. apply Z.mod_divide in Hal8; [|lia]. destruct Hal8 as [q Hq]. fold b in Hq. rewrite Hq.
        replace (q * 8 + n) with (n + q * 8) by ring. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. lia. }
      lia.
    + right. rename Hopt into Hmap. apply existsb_exists in Hmap as (mq & Hmq & Hq). apply andb_prop in Hq as [Hqf Hin]. apply negb_true_iff in Hqf.
      destruct (xinside_sound asegs E M (kn ch) pb pk (snd p) (am_base mq) 0 (am_len mq) rv_know Hin) as (I1 & I2).
      pose proof (APS.maps_match_In E _ _ mq (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hmq Hqf) as Hinm.
      exists (APS.amap_den E mq). split; [exact Hinm|]. unfold APS.amap_den. cbn [fst snd].
      unfold estart, elenZ in I1, I2. cbn [a_base a_off] in I1, I2. rewrite <- Up in I1, I2. fold n in I2. rewrite Z.add_0_r in I1, I2.
      lia.
Qed.

(* [comment removed for export] *)
Lemma rv_ghost : hs_vis_ok A ch = true -> forall a : word, shreg (bv_unsigned a) -> APS.in_ghost E ch (bv_unsigned a) = false.
Proof.
  intros HV a Ha. unfold hs_vis_ok in HV. apply andb_prop in HV as [_ HG].
  destruct (APS.in_ghost E ch (bv_unsigned a)) eqn:X; [|reflexivity]. exfalso.
  unfold APS.in_ghost in X. apply existsb_exists in X as (p & Hp & Hb). apply andb_prop in Hb as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. unfold APS.uE in B1, B2.
  pose proof (proj1 (forallb_forall _ _) HG p Hp) as Hgp. unfold ghost_p in Hgp.
  destruct (split_lit (fst p)) as [pb pk] eqn:Hps. apply andb_prop in Hgp as [Hflat Hap].
  destruct (APS.flat_x_sound asegs E M (kn ch) pb pk (snd p) rv_know Hflat) as (F1 & F2 & F3).
  pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
  pose proof (ranges_apart_x_sound asegs E M (kn ch) _ _ _ _ _ _ rv_know Hap) as Y.
  rewrite (APS.elenZ_lit E) in Y by (unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi; lia).
  unfold estart in Y. cbn [a_base a_off edenot] in Y. rewrite unsigned_lit in Y by lia. unfold elenZ in Y.
  unfold estart in Up. cbn [a_base a_off] in Up. rewrite <- Up in Y.
  unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia.
Qed.

Theorem rim_vis : hs_vis_ok A ch = true -> hs_shlazy_ok ch = true ->
  forall a : word, shreg (bv_unsigned a) -> page_allowedb A' (page_base a) = true ->
    bv_unsigned a < shad (pg_dn (bv_unsigned (vm_init_sp (m_vmmaps model)) - STACK_WIN)) ->
    (forall e, In e (vm_maps (m_vmmaps model)) ->
       ~ (shad (bv_unsigned (fst e)) <= bv_unsigned a < shad (bv_unsigned (fst e) + bv_unsigned (snd e)))) ->
    mH FULL model A' a <> None.
Proof.
  intros HV HL a Ha Hpa HAC HX.
  assert (Hlt : bv_unsigned a < 2 ^ 47) by (unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Ha; lia).
  assert (Hm : mH FULL model A' a = FULL a).
  { unfold mH, mrestrict, HID, mkH. rewrite Hpa. cbn [negb]. rewrite andb_false_r. cbn [orb].
    replace (2 ^ 47 <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; exact Hlt). reflexivity. }
  rewrite Hm.
  (* [comment removed for export] *)
  assert (HE : exists mp, In mp (a_maps ch) /\ am_kind mp = KRWLAZY
                          /\ bv_unsigned (edenot E (am_base mp)) <= bv_unsigned a < bv_unsigned (edenot E (am_base mp)) + bv_unsigned (edenot E (am_len mp))).
  { unfold hs_shlazy_ok in HL. apply andb_prop in HL as [H2 H4].
    assert (K : forall b l, existsb (amap_rwlazy b l) (a_maps ch) = true -> 0 <= b -> 0 <= l -> b + l < 2 ^ 64 -> b <= bv_unsigned a < b + l ->
              exists mp, In mp (a_maps ch) /\ am_kind mp = KRWLAZY
                         /\ bv_unsigned (edenot E (am_base mp)) <= bv_unsigned a < bv_unsigned (edenot E (am_base mp)) + bv_unsigned (edenot E (am_len mp))).
    { intros b l Hx Hb Hl Hbl Hab. apply existsb_exists in Hx as (mp & Hmp & Hok). unfold amap_rwlazy in Hok.
      apply andb_prop in Hok as [Hok Hk]. apply andb_prop in Hok as [Hb' Hl'].
      apply expr_eqb_eq in Hb'. apply expr_eqb_eq in Hl'. apply APS.mkind_eqb_eq in Hk.
      exists mp. split; [exact Hmp|]. split; [exact Hk|]. rewrite Hb', Hl'. cbn [edenot]. rewrite !unsigned_lit by lia. lia. }
    unfold shreg in Ha. destruct Ha as [Ha|Ha].
    - apply (K _ _ H2); unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi in *; lia.
    - apply (K _ _ H4); unfold K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia. }
  destruct HE as (mp & Hmp & Hk & Hz).
  destruct (proj1 (Forall_forall _ _) (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) mp Hmp Hk a Hz) as [Hna Hlz].
  assert (Hnf : is_fog mp = false) by (unfold is_fog, is_tok_kind; rewrite Hk; reflexivity).
  assert (Hm1 : APS.in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true)
    by (eapply APS.in_ivs_maps_match; [exact (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hmp | exact Hnf | exact Hz]).
  destruct (APS.hid A argH E ch model a) eqn:Hh.
  { (* [comment removed for export] *)
    rewrite (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC a Hh Hm1 Hna Hlz (rv_ghost HV a Ha)). discriminate. }
  (* [comment removed for export] *)
  assert (HMa : M a = FULL a) by (unfold APS.Mr, mrestrict; rewrite Hh; reflexivity).
  rewrite <- HMa.
  unfold APS.hid in Hh. apply orb_false_iff in Hh as [_ Hvis]. apply negb_false_iff in Hvis. unfold APS.vis in Hvis.
  assert (Hih : APS.in_hull A (bv_unsigned a) = false).
  { unfold APS.in_hull. apply andb_false_iff. right. apply Z.ltb_ge. rewrite Hsegtop.
    unfold shreg, SEGTOP_A, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia. }
  pose proof (APS.co_top _ _ _ _ _ _ _ _ _ _ _ _ HC) as HaC. unfold CEIL, TOPMAX in HaC.
  assert (Hat : (alloc_top (m_vmmaps model) <=? bv_unsigned a) = false).
  { apply Z.leb_gt. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia. }
  rewrite Hih, Hat, Hm1, Hna, Hlz in Hvis. cbn [negb orb andb] in Hvis.
  destruct (APS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [Isp _]. pose proof HISP as [Hsp0lo _]. rewrite <- Isp in Hsp0lo. unfold sp_window_lo in Hsp0lo.
  set (sp0 := bv_unsigned (vm_init_sp (m_vmmaps model))) in *.
  assert (PG : sp0 - STACK_WIN - 4096 < pg_dn (sp0 - STACK_WIN)).
  { unfold pg_dn. pose proof (Z.mod_pos_bound (sp0 - STACK_WIN) 4096 ltac:(lia)). pose proof (Z.div_mod (sp0 - STACK_WIN) 4096 ltac:(lia)). lia. }
  unfold APS.in_allow in Hvis. apply orb_prop in Hvis as [Hv|Hs].
  - (* [comment removed for export] *)
    exfalso. unfold APS.in_vis in Hv. apply existsb_exists in Hv as (p & Hp & Hpz).
    apply andb_prop in Hpz as [P1 P2]. apply Z.leb_le in P1. apply Z.ltb_lt in P2. unfold APS.uE in P1, P2.
    destruct (rv_case p Hp HV) as (_ & _ & _ & [C|(C & _)]); try (change (bv_unsigned (vm_init_sp (m_vmmaps model))) with sp0 in C); unfold STACK_WIN in *;
      unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia.
  - (* [comment removed for export] *)
    unfold APS.in_sh in Hs. apply existsb_exists in Hs as (p & Hp & Hpz).
    apply andb_prop in Hpz as [P1 P2]. apply Z.leb_le in P1. apply Z.ltb_lt in P2.
    unfold APS.sh_lo, APS.sh_hi, APS.uE in P1, P2. rewrite Hshoff in P1, P2.
    destruct (rv_case p Hp HV) as (Al & B0 & B1 & [C|(_ & [C|(e & He & E1 & E2)])]).
    + exfalso. change (bv_unsigned (vm_init_sp (m_vmmaps model))) with sp0 in C. unfold shad in HAC. assert (pg_dn (sp0 - STACK_WIN) / 8 <= bv_unsigned (edenot E (fst p)) / 8) by (apply Z.div_le_mono; lia). lia.
    + exact (C a ltac:(lia) Ha).
    + exfalso. apply (HX e He). unfold shad. split.
      * assert (bv_unsigned (fst e) / 8 <= bv_unsigned (edenot E (fst p)) / 8) by (apply Z.div_le_mono; lia). lia.
      * assert ((bv_unsigned (edenot E (fst p)) + bv_unsigned (edenot E (snd p))) / 8 <= (bv_unsigned (fst e) + bv_unsigned (snd e)) / 8)
          by (apply Z.div_le_mono; lia). lia.
Qed.

End Vis.
