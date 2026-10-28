(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_cdealloc R_return R_prim_lists RT_freeA RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_maltail RT_freeA2 RT_drain_defs RT_drain_pure RT_drain_kit RT_drain_art RT_drain_art3 RT_drain_geo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Definition TZ_CD (T c : Z) : list ivl := [(pc_addr T c, pc_addr T c + 80); (T + 2768, T + 3168)].

Definition W_CD (T SB c sp : Z) : list ivl :=
  [(pc_addr T c, pc_addr T c + 80); (T + 2768, T + 3168); (rinfo (RIS_of SB) c, rinfo (RIS_of SB) c + 128); (fa SB c, fa SB c + kFaCap);
   (shad (rb SB c + kUserCap), shad (rb SB c + 2 ^ 32)); (sp - 1024, sp)].

Lemma cd_TZd : forall T c, 1 <= c <= 31 ->
  disjoint_from (TZ_CD T c) T 0x50 /\ disjoint_from (TZ_CD T c) (T + 48) 16 /\ disjoint_from (TZ_CD T c) (T + 0xc60) 1
  /\ (forall c', 1 <= c' <= 31 -> c' <> c -> disjoint_from (TZ_CD T c) (pc_addr T c') 80) /\ disjoint_from (TZ_CD T c) (qcacheT T) 32.
Proof.
  intros T c Hc. unfold TZ_CD, pc_addr, qcacheT. cbn [disjoint_from].
  split; [repeat split; lia|]. split; [repeat split; lia|]. split; [repeat split; lia|].
  split; [intros c' Hc' Hne; repeat split; lia | repeat split; lia].
Qed.

Lemma cd_TZ : forall T c, 1 <= c <= 31 -> Forall (fun z => T <= fst z /\ snd z <= T + 4096) (TZ_CD T c).
Proof. intros T c Hc. unfold TZ_CD, pc_addr. repeat constructor; cbn [fst snd]; lia. Qed.

Lemma cd_full_false : forall c l, Z.of_nat (length l) < MaxCount c -> cdeal_full c l = false.
Proof. intros c l H. unfold cdeal_full. apply Z.leb_gt. lia. Qed.
Lemma cd_full_true : forall c l, Z.of_nat (length l) = MaxCount c -> cdeal_full c l = true.
Proof. intros c l H. unfold cdeal_full. apply Z.leb_le. lia. Qed.

Lemma cpw_compact : forall SB c i, Z_to_bv 64 (compact_of SB c (p_abeg SB c i)) = cpw c (Z.of_nat i).
Proof. intros SB c i. unfold compact_of, p_abeg, cpw. f_equal. f_equal. ring. Qed.

Lemma dk_wr_stk : forall (m : mem) a n, wr_at bsegs m a n -> img_hull_hi <= a -> a + n <= 2 ^ 64 -> stk bsegs m a (a + n).
Proof.
  intros m a n (Ha & Hn & H) Hi Hb. split; [lia|]. split; [lia|]. intros x Hx.
  pose proof (H (x - a) ltac:(lia)) as X. replace (a + (x - a)) with x in X by lia. split; [exact X|].
  unfold mrd. unfold wview in X. destruct (m (wa x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply X. rewrite find_segment_above; [reflexivity| rewrite wa_unsigned by lia; lia|].
  rewrite wa_unsigned by lia. apply (forallb_mono_top bsegs img_hull_hi); [lia | exact asegs_top].
Qed.

Lemma dk_stk_within : forall (m : mem) lo hi a b, stk bsegs m lo hi -> lo <= a -> b <= hi -> 0 <= a -> stk bsegs m a b.
Proof. intros m lo hi a b (H1 & H2 & H) Ha Hb Ha0. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

Lemma dk_stk_wmono : forall (m m' : mem) lo hi, stk bsegs m lo hi -> wmono bsegs m m' -> img_hull_hi <= lo -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM Hi. destruct (Z_le_gt_dec lo hi) as [Hle|Hgt].
  - replace hi with (lo + (hi - lo)) by lia. apply dk_wr_stk; [|lia|lia].
    split; [lia|]. split; [lia|]. intros x Hx. apply WM. exact (proj1 (H (lo + x) ltac:(lia))).
  - split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma dest2_prefix : forall (fl l : list Z) (ws chs : list word) (c : Z) (keep n : nat),
  firstn (length fl) ws = map (cpw c) fl -> firstn (length l) chs = map (cpw c) l -> (keep + n = length l)%nat ->
  (length fl + n <= length ws)%nat -> (forall x, In x l -> 0 <= x * ClassSize c / 16 < 2 ^ 31) ->
  firstn (length fl + n) (dest2 ws chs (Z.of_nat (length fl)) (Z.of_nat keep) n) = map (cpw c) (fl ++ skipn keep l).
Proof.
  intros fl l ws chs c keep n HF HL Hk Hws Hsm. apply nth_error_ext. intros p.
  rewrite nth_error_firstn, nth_error_map.
  destruct (Nat.ltb_spec p (length fl + n)) as [Hp|Hp].
  - destruct (Nat.ltb_spec p (length fl)) as [Hp1|Hp1].
    + rewrite dest2_nth_lo by (rewrite Nat2Z.id; exact Hp1). rewrite nth_error_app1 by exact Hp1.
      assert (E : nth_error (firstn (length fl) ws) p = nth_error (map (cpw c) fl) p) by (rewrite HF; reflexivity).
      rewrite nth_error_firstn, nth_error_map in E. rewrite (proj2 (Nat.ltb_lt p (length fl)) Hp1) in E. exact E.
    + assert (Ej : p = (Z.to_nat (Z.of_nat (length fl)) + (p - length fl))%nat) by (rewrite Nat2Z.id; lia).
      rewrite Ej. rewrite (dest2_nth_mid ws chs (Z.of_nat (length fl)) (Z.of_nat keep) n (p - length fl)) by (rewrite ?Nat2Z.id; lia).
      rewrite !Nat2Z.id. rewrite nth_error_app2 by lia. replace (length fl + (p - length fl) - length fl)%nat with (p - length fl)%nat by lia.
      rewrite nth_error_skipn.
      assert (Hkj : (keep + (p - length fl) < length l)%nat) by lia.
      destruct (nth_error l (keep + (p - length fl))) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
      assert (E : nth_error (firstn (length l) chs) (keep + (p - length fl)) = nth_error (map (cpw c) l) (keep + (p - length fl)))
        by (rewrite HL; reflexivity).
      rewrite nth_error_firstn, nth_error_map, Ex in E. rewrite (proj2 (Nat.ltb_lt _ (length l)) Hkj) in E.
      rewrite (nth_error_nth' chs (Z_to_bv 64 0) ltac:(apply nth_error_Some; rewrite E; discriminate)) in E.
      injection E as E. rewrite E. cbn [option_map]. f_equal. unfold cpw. apply sx32_zw. exact (Hsm x (nth_error_In _ _ Ex)).
  - rewrite (proj2 (nth_error_None _ _)); [reflexivity|]. rewrite length_app, length_skipn. lia.
Qed.

Lemma cache_keep : forall (l : list Z) (chs : list word) c keep, firstn (length l) chs = map (cpw c) l -> (keep <= length l)%nat ->
  firstn keep chs = map (cpw c) (firstn keep l).
Proof.
  intros l chs c keep H Hk. replace keep with (Nat.min keep (length l)) at 1 by lia. rewrite <- firstn_firstn, H. apply firstn_map.
Qed.

Definition cd_msD (Σ : rtsA) (c : Z) (i : nat) (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT (l_T (lay Σ)))) (Z_to_bv 64 INST) (Z_to_bv 64 c)
          (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom bsegs).

Definition cd_postD (Σ : rtsA) (m : mem) (c lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (Σ' : rtsA) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ ARTc Σ' m' /\ munch (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) c (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp) /\ rt_pres (live Σ) (frames Σ) (bv_unsigned sp) m m'.

Section CDK.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (st : ckst) (lo : Z)
  (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HG : geo_ok Σ.
Hypothesis HA : ARTc (set_st Σ c i CkIdle) m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hi : nth_error (r_st (pr Σ c)) i = Some st.
Hypothesis Hinit : ca_init Σ = true.
Hypothesis Hcnt : Z.of_nat (length (ca Σ c)) <= MaxCount c.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis Hlive : live_wf Σ.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation usp := (bv_unsigned sp).

#[local] Notation cd_ms := (cd_msD Σ c i ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
#[local] Notation cd_post := (cd_postD Σ m c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc).

Lemma cd_geo : T_ok (l_ACEIL L) T /\ SB_ok (l_ACEIL L) SB /\ tsep (l_ACEIL L) SB T (l_TCX L)
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ SB + 2 ^ 37 + 4096 <= l_ACEIL L /\ kHighShadowEnd < SB.
Proof using HG.
  clear - HG. pose proof (dg_ok Σ HG) as (X1 & X2 & X3). pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof X2 as (Y1 & Y2 & Y3 & Y4). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. repeat split; lia.
Qed.

Lemma cd_slot : SB + c * 2 ^ 32 <= AB < SB + c * 2 ^ 32 + 2 ^ 32 /\ (AB - SB - c * 2 ^ 32) mod 16 = 0 /\ 0 <= AB.
Proof using HG Hc Hi.
  clear - HG Hc Hi. pose proof (dk_slot_in Σ HG c i _ Hc Hi) as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (ClassSize_range c Hc) as (_ & Hm). pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold rb, kUserCap in *. split; [lia|]. split; [|lia].
  replace (AB - SB - c * 2 ^ 32) with (Z.of_nat i * ClassSize c) by (unfold p_abeg; ring).
  apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide in Hm; [|lia]. destruct Hm as (q & E). exists (2 * q). lia.
Qed.

Lemma cd_cert : Forall (dzone Σ [] [] [] (TZ_CD T c) [] [c] lo usp) (W_CD T SB c usp).
Proof using HG Hc HLO2.
  pose proof (dk_auser Σ HG c Hc) as AU.
  unfold W_CD. repeat apply Forall_cons; try apply Forall_nil.
  - right; left. exists (pc_addr T c, pc_addr T c + 80). split; [left; reflexivity | cbn [fst snd]; lia].
  - right; left. exists (T + 2768, T + 3168). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - do 4 right; left. exists c. split; [left; reflexivity | cbn [fst snd]; lia].
  - do 5 right; left. exists c. split; [left; reflexivity | cbn [fst snd]; lia].
  - do 6 right; left. exists c. split; [left; reflexivity|]. cbn [fst snd]. split; [apply fk_shad_mono; lia | lia].
  - do 9 right. cbn [fst snd]. lia.
Qed.

Lemma cd_pc : exists chs, pc_cells m (pc_addr T c) (Z.of_nat (length (ca Σ c))) (MaxCount c) (ClassSize c)
  /\ u32arr bsegs m (pc_addr T c + 16) chs /\ length chs = 16%nat /\ firstn (length (ca Σ c)) chs = map (cpw c) (ca Σ c).
Proof using HA Hc Hinit.
  assert (X : pclass_rep T c (ca_init Σ) (ca Σ c) m) by exact (proj1 (proj2 (proj2 HA)) c Hc).
  destruct X as (PC & chs & U & Hl & Hf). rewrite Hinit in PC. exists chs. split; [exact PC | split; [exact U | split; [exact Hl | exact Hf]]].
Qed.

Lemma cd_reg : reg_rep SB c (pr Σ c) m.
Proof using HA Hc.
  pose proof (proj1 (proj2 HA) c Hc) as X. rewrite set_st_pr_same' in X. exact (reg_rep_ureg_inv _ _ _ _ _ _ X).
Qed.

Lemma cd_push_cert : Forall (dzone Σ [] [] [] (TZ_CD T c) [] [] lo usp) (cdealloc_W T c sp).
Proof using HLO2.
  unfold cdealloc_W, cstat_alloc. repeat apply Forall_cons; try apply Forall_nil.
  - right; left. exists (pc_addr T c, pc_addr T c + 80). split; [left; reflexivity | cbn [fst snd]; lia].
  - right; left. exists (pc_addr T c, pc_addr T c + 80). split; [left; reflexivity | cbn [fst snd]; lia].
  - right; left. exists (T + 2768, T + 3168). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - do 9 right. cbn [fst snd]. lia.
Qed.

Theorem cd_push_evt : Z.of_nat (length (ca Σ c)) < MaxCount c -> evt bsegs (cd_post (recp Σ c i)) cd_ms.
Proof using HG HA Hc Hi Hinit ST HLO HLO2 HSP MI Hlive Hdep HQB.
  intros Hlt.
  pose proof cd_geo as (HT & HSB & TSEP & G1 & G2 & G3 & G4).
  pose proof cd_slot as (P1 & P2 & P3).
  pose proof (dg_consts L m (proj1 HA)) as (IC & MMG & TC & PS & STS & UB). destruct IC as (IC1 & IC2).
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
  destruct IC1 as (SBC & _). cbn [cells_size csize Nat.add Z.of_nat] in SBC.
  pose proof cd_pc as (chs & PC & CHS & Hchs & Hfch).
  destruct (fl_c8_of_stk m (cstat_alloc T) ltac:(apply (dk_stk_within m _ _ _ _ STS); unfold cstat_alloc; [lia | lia | pose proof HT as (X & _); lia]))
    as (stj & STJ).
  pose proof (MaxCount_range c Hc) as (MC1 & MC2). pose proof (ClassSize_range c Hc) as ((CS1 & CS2) & CS3).
  unfold cd_msD.
  eapply evt_mono; [apply (cdealloc_push_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                             F fc m (l_ACEIL L) T SB c AB (Z.of_nat (length (ca Σ c))) (MaxCount c) (ClassSize c) lo chs stj)|].
  1: exact Hc. 1: exact P1. 1: exact P2. 1: exact SBC. 1: exact PC. 1: lia. 1: lia. 1: lia. 1: exact CHS. 1: exact Hchs. 1: exact STJ.
  1: exact HT. 1: exact HSB. 1: exact ST. 1: exact HLO. 1: clear - G3 G4 HLO; unfold kHighShadowEnd in *; lia. 1: clear - HLO2; lia.
  1: exact HSP. 1: exact MI.
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & stj' & -> & MU1 & WM1 & MI1
              & PC1 & CHS1 & _ & _ & ST1).
  unfold cd_postD. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m1. split; [reflexivity|].
  assert (MU : munch (W_CD T SB c usp) m m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp, W_CD, cdealloc_W, cstat_alloc. cbn [outside]. intros x Hx. clear - Hx HLO2. repeat split; lia. }

  pose proof (ak0_reg Σ m m1 (cdealloc_W T c sp) (TZ_CD T c) lo usp HG (cd_TZ T c Hc) HLO cd_push_cert MU1 WM1 c Hc cd_reg) as RR.

  assert (HP : pclass_rep T c (ca_init Σ) (ca Σ c ++ [Z.of_nat i]) m1).
  { rewrite Hinit. split.
    - rewrite length_app. cbn [length]. replace (Z.of_nat (length (ca Σ c) + 1)) with (Z.of_nat (length (ca Σ c)) + 1) by lia. exact PC1.
    - exists (upd chs (Z.to_nat (Z.of_nat (length (ca Σ c)))) (Z_to_bv 64 (compact_of SB c AB))). rewrite Nat2Z.id. rewrite Nat2Z.id in CHS1.
      split; [exact CHS1|]. split; [rewrite upd_length; exact Hchs|].
      rewrite length_app. cbn [length]. rewrite Nat.add_1_r. rewrite firstn_upd_snoc by lia. rewrite Hfch, cpw_compact, map_app. reflexivity. }
  rewrite recp_set_rc, set_st_pr_same'. unfold cdeal_reg, cdeal_ca. rewrite (cd_full_false c (ca Σ c) Hlt).
  split; [exact (artc_rc Σ m m1 (W_CD T SB c usp) c i st (TZ_CD T c) lo usp HG Hc Hi (cd_TZ T c Hc) (cd_TZd T c Hc) HLO cd_cert HA
                  Hdep HQB MU WM1 (ureg (pr Σ c) i CkIdle) (ca Σ c ++ [Z.of_nat i]) eq_refl (reg_rep_ureg' _ _ _ _ _ _ RR) HP)|].
  split; [exact MU|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
  exact (client_rc Σ m m1 (W_CD T SB c usp) c (TZ_CD T c) lo usp HG Hc (cd_TZ T c Hc) HLO ltac:(lia) cd_cert Hlive MU).
Qed.

End CDK.

End GWIN.
