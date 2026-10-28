(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore
  AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_state RT_rep RT_init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance rvis_fx : PropExec.FPState := PropExec.fx0.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma shreg_noseg : forall z, shreg z -> find_segment bsegs z 1 = None.
Proof.
  intros z Hs.
  unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments.
  cbn [find_segment].
  unfold AsanUbsan.AsanUbsan_segment_000, AsanUbsan.AsanUbsan_segment_001,
    AsanUbsan.AsanUbsan_segment_002, AsanUbsan.AsanUbsan_segment_003.
  cbn [seg_base seg_size]. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs.
  destruct Hs as [Hs|Hs];
    repeat match goal with |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia ]; cbn [andb] end; reflexivity.
Qed.

Definition vslice (k : list kentry) (p : expr * expr) : bool :=
  (expr_eqb (eadd (fst p) (snd p)) e_band && match xhi_each k (snd p) with Some h => Z.ltb h 4096 | None => false end
   && fact_ok k (KAlign (fst p) 4096))%bool.

Definition vis_p (A : atable) (ch : acs) (p : expr * expr) : bool :=
  let k := kn ch in
  let '(pb, pk) := split_lit (fst p) in
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in
  let '(bb, bk) := split_lit e_band in

  (fact_ok k (KAlign (fst p) 8) && (if flat_x k pb pk (snd p) then true else flat_xe k pb pk (snd p))
   && (if (if (if xinside k pb pk (snd p) bb bk e_bandlen then (if flat_x k bb bk e_bandlen then true else flat_xe k bb bk e_bandlen)
               else false) then true
           else vslice k p) then true
       else (if ranges_apart_x k pb pk (snd p) (ELit 0) K_LOW_SHADOW_lo (ELit (K_HIGH_SHADOW_hi - K_LOW_SHADOW_lo))
             then (if kwritable_x k k sb sk sn then true
                   else existsb (fun mp => negb (is_fog mp) && xinside k pb pk (snd p) (am_base mp) 0 (am_len mp)) (a_maps ch))
             else false)))%bool.

Definition hs_vis_ok (A : atable) (ch : acs) : bool := forallb (vis_p A ch) (a_vis ch).

Section Vis.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).

#[local] Notation M := (APS.Mr A argH E ch model FULL).

Lemma rv_know : know_ok bsegs E M (kn ch).
Proof. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma rv_shadow_den : forall b n sb sk sn, shadow_of A (kn ch) b n = (sb, sk, sn) -> 0 <= estart E (SA sb sk) <= 2 ^ 64 ->
  estart E (SA sb sk) = SHB + uE E b / 8 /\ elenZ E sn = uE E n / 8.
Proof.
  intros b n sb sk sn H Hst. unfold shadow_of in H.
  destruct (split_lit (eadd (mkSrl (kn ch) b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection H as <- <- <-.
  assert (Usrl : forall e, bv_unsigned (edenot E (mkSrl (kn ch) e 3)) = uE E e / 8).
  { intros e. rewrite (mkSrl_denot bsegs E M (kn ch) e 3 (Z_to_bv 64 3) rv_know) by (rewrite unsigned_lit by lia; reflexivity).
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

Lemma rv_wr_present : forall sb sk sn (a : word), kwritable_x (kn ch) (kn ch) sb sk sn = true ->
  estart E (SA sb sk) <= bv_unsigned a < estart E (SA sb sk) + elenZ E sn -> shreg (bv_unsigned a) -> M a <> None.
Proof.
  intros sb sk sn a Hk Ha Hs.
  destruct (APSX.kwritable_x_sound bsegs E M (kn ch) (kn ch) sb sk sn rv_know rv_know Hk) as (W & W1 & W2).
  pose proof (W (Z.to_nat (elenZ E sn)) ltac:(rewrite Z2Nat.id by (unfold elenZ; pose proof (u64_range (edenot E sn)); lia); lia)) as Wj.
  pose proof (store_ok_wview bsegs M _ _ (Z.to_nat (bv_unsigned a - estart E (SA sb sk))) Wj ltac:(lia)) as Wi.
  rewrite unsigned_lit in Wi by lia. rewrite Z2Nat.id in Wi by lia.
  replace (estart E (SA sb sk) + (bv_unsigned a - estart E (SA sb sk))) with (bv_unsigned a) in Wi by lia.
  unfold wa in Wi. rewrite Z_to_bv_bv_unsigned in Wi. unfold wview in Wi. rewrite (shreg_noseg _ Hs) in Wi.
  destruct (M a); [discriminate | exact Wi].
Qed.

Lemma rv_case : forall p, In p (a_vis ch) -> hs_vis_ok A ch = true ->
  let b := bv_unsigned (edenot E (fst p)) in let n := bv_unsigned (edenot E (snd p)) in
  b mod 8 = 0 /\ 0 <= b /\ b + n <= 2 ^ 64
  /\ (pg_dn (bv_unsigned (vm_init_sp (m_vmmaps model)) - STACK_WIN) <= b
      \/ ((b + n <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= b)
          /\ ((forall a : word, SHB + b / 8 <= bv_unsigned a < SHB + (b + n) / 8 -> shreg (bv_unsigned a) -> M a <> None)
              \/ exists e, In e (vm_maps (m_vmmaps model)) /\ bv_unsigned (fst e) <= b /\ b + n <= bv_unsigned (fst e) + bv_unsigned (snd e)))).
Proof.
  intros p Hp HV b n. pose proof (proj1 (forallb_forall _ _) HV p Hp) as Hvp. unfold vis_p in Hvp.
  destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
  destruct (shadow_of A (kn ch) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  destruct (split_lit e_band) as [bb bk] eqn:Hbs.
  apply andb_prop in Hvp as [Hvp Hopt]. apply andb_prop in Hvp as [Hal Hflat].
  pose proof (APS.fact_ok_sound bsegs E M (kn ch) _ rv_know Hal) as Hal'. cbn [kentry_ok] in Hal'. destruct Hal' as (_ & Hal').
  destruct (APS.flat_x_or_e_sound bsegs E M (kn ch) pb pk (snd p) rv_know Hflat) as (F1 & F2 & F3).
  pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up. fold b in Up. fold n in F2.
  split; [exact Hal'|]. split; [lia|]. split; [lia|].
  pose proof (APS.band_alloc_top _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hband. unfold APS.uE, alloc_top, stack_max_size in Hband.
  pose proof (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & Hsp0lo & Hsp0hi). unfold sp_window_lo, sp_window_hi in Hsp0lo, Hsp0hi.
  set (sp0 := bv_unsigned (vm_init_sp (m_vmmaps model))) in *.
  assert (PG : pg_dn (sp0 - STACK_WIN) <= sp0 - STACK_WIN) by (unfold pg_dn; pose proof (Z.mul_div_le (sp0 - STACK_WIN) 4096 ltac:(lia)); lia).
  apply orb_prop in Hopt as [Hopt|Hopt]; [apply orb_prop in Hopt as [Hopt|Hopt]|].
  -
    left. apply andb_prop in Hopt as [Hin Hbflat].
    destruct (APS.flat_x_or_e_sound bsegs E M (kn ch) bb bk e_bandlen rv_know Hbflat) as (G1 & G2 & G3).
    pose proof (APS.u_of_split E e_band bb bk Hbs ltac:(lia)) as Ub.
    destruct (xinside_sound bsegs E M (kn ch) pb pk (snd p) bb bk e_bandlen rv_know Hin) as (I1 & I2).
    rewrite <- Ub in I1. rewrite <- Up in I1. rewrite Hband in I1. unfold STACK_WIN in *. lia.
  -
    left. unfold vslice in Hopt. apply andb_prop in Hopt as [Hopt Hal4]. apply andb_prop in Hopt as [Heq Hh].
    revert Hh. case_eq (xhi_each (kn ch) (snd p)); [intros h Hxe Hh| intros _ Hh; discriminate]. apply Z.ltb_lt in Hh.
    pose proof (APS.xhi_each_sound bsegs E M (kn ch) (snd p) h rv_know Hxe) as Nh. fold n in Nh.
    pose proof (APS.fact_ok_sound bsegs E M (kn ch) _ rv_know Hal4) as X4. cbn [kentry_ok] in X4. destruct X4 as (_ & X4). fold b in X4.
    apply expr_eqb_eq in Heq. apply (f_equal (fun e => bv_unsigned (edenot E e))) in Heq.
    unfold eadd in Heq. rewrite mkAlu_denot in Heq. cbn [edenot] in Heq. rewrite u_add64 in Heq. fold b n in Heq. rewrite Hband in Heq.
    unfold two64 in Heq. unfold estart in Up. cbn [a_base a_off] in Up.
    destruct (Z.eq_dec (b + n) (2 ^ 64)) as [EQ|NE]; [rewrite EQ, Z_mod_same_full in Heq; lia|].
    pose proof (u64_range (edenot E (snd p))) as Rn. fold n in Rn.
    rewrite Z.mod_small in Heq by (unfold estart in F1, F2; cbn [a_base a_off] in F1, F2; lia).

    unfold pg_dn, STACK_WIN. apply Z.mod_divide in X4; [|lia]. destruct X4 as [q Hq].
    assert (E2 : (sp0 - 8388608) / 4096 = q) by (symmetry; apply Z.div_unique with (r := sp0 - 8388608 - q * 4096); lia).
    rewrite E2. lia.
  -
    right. apply andb_prop in Hopt as [Hap Hopt].
    pose proof (ranges_apart_x_sound bsegs E M (kn ch) _ _ _ _ _ _ rv_know Hap) as X.
    rewrite (APS.elenZ_lit E) in X by (unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi; lia).
    unfold estart in X. cbn [a_base a_off edenot] in X. rewrite unsigned_lit in X by lia. unfold elenZ in X.
    unfold estart in Up. cbn [a_base a_off] in Up. rewrite <- Up in X. fold n in X.
    split; [unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia|].
    apply orb_prop in Hopt as [Hkw|Hmap].
    + left. intros a Ha Hs.
      destruct (APSX.kwritable_x_sound bsegs E M (kn ch) (kn ch) sb sk sn rv_know rv_know Hkw) as (_ & W1 & W2).
      destruct (rv_shadow_den (fst p) (snd p) sb sk sn Hsh ltac:(unfold elenZ in W2; pose proof (u64_range (edenot E sn)); lia)) as (S1 & S2).
      apply (rv_wr_present sb sk sn a Hkw); [|exact Hs]. rewrite S1, S2. unfold uE. fold b n.
      assert (Hbn : (b + n) / 8 = b / 8 + n / 8).
      { pose proof Hal' as Hal8. apply Z.mod_divide in Hal8; [|lia]. destruct Hal8 as [q Hq]. fold b in Hq. rewrite Hq.
        replace (q * 8 + n) with (n + q * 8) by ring. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. lia. }
      lia.
    + right. apply existsb_exists in Hmap as (mq & Hmq & Hq). apply andb_prop in Hq as [Hqf Hin]. apply negb_true_iff in Hqf.
      destruct (xinside_sound bsegs E M (kn ch) pb pk (snd p) (am_base mq) 0 (am_len mq) rv_know Hin) as (I1 & I2).
      pose proof (APS.maps_match_In E _ _ mq (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) Hmq Hqf) as Hinm.
      exists (APS.amap_den E mq). split; [exact Hinm|]. unfold APS.amap_den. cbn [fst snd].
      unfold estart, elenZ in I1, I2. cbn [a_base a_off] in I1, I2. rewrite <- Up in I1, I2. fold n in I2. rewrite Z.add_0_r in I1, I2.
      lia.
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
  assert (Hsw : APS.in_sw (bv_unsigned a) = true).
  { unfold APS.in_sw. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt];
      unfold shreg, SW_LO, KHI, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia. }
  destruct (APS.hid A argH E ch model a) eqn:Hh.
  {
    rewrite (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC a Hh Hm1 Hna Hlz (or_intror Hsw)). discriminate. }

  assert (HMa : M a = FULL a) by (unfold APS.Mr, mrestrict; rewrite Hh; reflexivity).
  rewrite <- HMa.
  unfold APS.hid in Hh. apply orb_false_iff in Hh as [_ Hvis]. apply negb_false_iff in Hvis. unfold APS.vis in Hvis.
  assert (Hih : APS.in_hull A (bv_unsigned a) = false).
  { unfold APS.in_hull. apply andb_false_iff. right. apply Z.ltb_ge. rewrite Hsegtop.
    unfold shreg, SEGTOP_A, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia. }
  pose proof (APS.alloc_top_cs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HaC. unfold CEIL, ATOPMAX in HaC.
  assert (Hat : (alloc_top (m_vmmaps model) <=? bv_unsigned a) = false).
  { apply Z.leb_gt. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia. }
  rewrite Hih, Hat, Hm1, Hna, Hlz in Hvis. cbn [negb orb andb] in Hvis.
  pose proof (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & Hsp0lo & _). unfold sp_window_lo in Hsp0lo.
  set (sp0 := bv_unsigned (vm_init_sp (m_vmmaps model))) in *.
  assert (PG : sp0 - STACK_WIN - 4096 < pg_dn (sp0 - STACK_WIN)).
  { unfold pg_dn. pose proof (Z.mod_pos_bound (sp0 - STACK_WIN) 4096 ltac:(lia)). pose proof (Z.div_mod (sp0 - STACK_WIN) 4096 ltac:(lia)). lia. }
  unfold APS.in_allow in Hvis. apply orb_prop in Hvis as [Hv|Hs].
  -
    exfalso. unfold APS.in_vis in Hv. apply existsb_exists in Hv as (p & Hp & Hpz).
    apply andb_prop in Hpz as [P1 P2]. apply Z.leb_le in P1. apply Z.ltb_lt in P2. unfold APS.uE in P1, P2.
    destruct (rv_case p Hp HV) as (_ & _ & _ & [C|(C & _)]); try (change (bv_unsigned (vm_init_sp (m_vmmaps model))) with sp0 in C); unfold STACK_WIN in *;
      unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia.
  -
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

End GWIN.
