(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes PropExec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_m2s R_thread R_poison R_prim_kit R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_mmapordie R_flushshadow R_secdealloc_p3 RT_state RT_rep RT_frame RT_trans RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_sys_stmt RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_loop RT_drain_istmt RT_drain_itemp RT_facts0 RT_freeA RT_malsec_rev RT_dsec_defs RT_dsec_art2 RT_dsec_runA RT_dsec_ret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Lemma ds_FOP_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
  intros X R Hs l l' H. induction H as [|x l l' Hp IH|x y l|l l' l'' _ IH1 _ IH2]; intros HF.
  - constructor.
  - inversion HF as [|? ? Hx Hl]; subst. constructor; [|exact (IH Hl)].
    apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hx). exact (Permutation_in _ (Permutation_sym Hp) Hz).
  - inversion HF as [|? ? Hy Hl]; subst. inversion Hl as [|? ? Hx Hl']; subst.
    inversion Hy as [|? ? Hyx Hyl]; subst.
    constructor; [constructor; [exact (Hs _ _ Hyx)| exact Hx]|]. constructor; [exact Hyl| exact Hl'].
  - exact (IH2 (IH1 HF)).
Qed.

Lemma ds_FOP_app_cross : forall {X} (R : X -> X -> Prop) l1 l2, ForallOrdPairs R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|q l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  cbn [app] in H. inversion H as [|? ? Hp Hl]; subst. destruct Hx as [<-|Hx].
  - apply (proj1 (Forall_forall _ _) Hp). apply in_or_app. right. exact Hy.
  - exact (IH l2 Hl x y Hx Hy).
Qed.

Lemma ds_filter_all_true : forall {X} (f : X -> bool) (l : list X), (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros X f l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [List.filter]. rewrite (H x (or_introl eq_refl)).
  f_equal. apply IH. intros y Hy. exact (H y (or_intror Hy)).
Qed.

Lemma ds_perm_filter : forall {X} (f : X -> bool) (l l' : list X), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros X f l l' H. induction H as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2].
  - constructor.
  - cbn [List.filter]. destruct (f x); [apply perm_skip; exact IH | exact IH].
  - cbn [List.filter]. destruct (f x), (f y); try apply perm_swap; apply Permutation_refl.
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma ds_FOP_filter : forall {X} (R : X -> X -> Prop) (f : X -> bool) (l : list X), ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
  intros X R f l H. induction H as [|x l Hx Hl IH]; [constructor|]. cbn [List.filter]. destruct (f x); [|exact IH].
  constructor; [|exact IH]. apply Forall_forall. intros y Hy. apply List.filter_In in Hy as [Hy _].
  exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

Lemma ds_maps0_pos : forall L, layout_ok L -> Forall (fun e => 0 < bv_unsigned (snd e)) (l_maps0 L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HP) & _).
  exact HP.
Qed.

Lemma ds_filter_map : forall {X Y} (f : Y -> bool) (g : X -> Y) (l : list X),
  List.filter f (map g l) = map g (List.filter (fun x => f (g x)) l).
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn [map List.filter]. destruct (f (g x)); cbn [map]; rewrite IH; reflexivity. Qed.

Lemma ds_lit_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. rewrite <- (unsigned_lit x Hx), <- (unsigned_lit y Hy). rewrite E. reflexivity.
Qed.

Theorem ds_perm : forall Σ k s mo, nth_error (sec Σ) k = Some s -> geo_ok Σ -> ARTM_A Σ mo ->
  Permutation (rt_maps (recs Σ k)) (map_remove (rt_maps Σ) (Z_to_bv 64 (s_mb s))).
Proof.
  intros Σ k s mo Hk HG HA.
  pose proof (ds_maps0_pos _ (proj1 HG)) as HPOS.
  pose proof HA as (Hperm & _ & _ & _ & (_ & _ & Hsep0 & _)).
  pose proof (ds_FOP_filter iv_apart vpos _ Hsep0) as Hsep.
  pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & _ & _ & _ & _ & _ & M8 & M9).
  pose proof (dk_geo Σ HG) as (_ & G2 & _).
  pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  unfold rt_maps, map_remove. cbn [recs set_sec sec lay]. rewrite filter_app.
  assert (E0 : List.filter (fun q => negb (bv_eqb (fst q) (Z_to_bv 64 (s_mb s)))) (l_maps0 (lay Σ)) = l_maps0 (lay Σ)).
  { apply ds_filter_all_true. intros e He. apply negb_true_iff. destruct (bv_eqb (fst e) (Z_to_bv 64 (s_mb s))) eqn:Eb; [|reflexivity].
    exfalso. apply bv_eqb_eq in Eb.
    assert (HsepR : ForallOrdPairs iv_apart (map secmap (rev (sec Σ)) ++ l_maps0 (lay Σ)))
      by exact (ds_FOP_perm iv_apart (fun x y H => ltac:(unfold iv_apart in *; clear - H; lia)) _ _ Hperm Hsep).
    pose proof (ds_FOP_app_cross _ _ _ HsepR (secmap s) e ltac:(apply in_map; apply (proj1 (in_rev _ _)); exact (nth_error_In _ _ Hk)) He) as D.
    pose proof (proj1 (Forall_forall _ _) HPOS e He) as Pe.
    unfold iv_apart, secmap in D. cbn [fst snd] in D. rewrite Eb in D.
    rewrite !unsigned_lit in D by (clear - M1 M2 M8 G2; lia). cbv beta in Pe. clear - D Pe M8. lia. }
  rewrite E0. apply Permutation_app_tail.
  rewrite ds_filter_map. apply Permutation_map.
  eapply perm_trans; [apply Permutation_sym, Permutation_rev|]. eapply perm_trans; [|apply ds_perm_filter, Permutation_rev].
  eapply perm_trans; [|apply ds_perm_filter, Permutation_sym, (swap_remove_perm k (sec Σ) s Hk)].
  cbn [List.filter]. unfold secmap at 1. cbn [fst]. rewrite bv_eqb_refl. cbn [negb].
  rewrite ds_filter_all_true; [apply Permutation_refl|].
  intros t Ht. apply negb_true_iff. unfold secmap. cbn [fst].
  destruct (bv_eqb (Z_to_bv 64 (s_mb t)) (Z_to_bv 64 (s_mb s))) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb.
  destruct (swap_remove_other k (sec Σ) t Hkl Ht) as (jt & Hne & Hjt).
  pose proof (dk_map Σ HG jt t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & _).
  pose proof (M9 jt t Hjt Hne) as A.
  apply ds_lit_inj in Eb; [|lia | lia]. lia.
Qed.

Lemma ds_smsz_le : forall n, 64512 < n <= 0x20001000 -> smsz n <= 2 ^ 30.
Proof.
  intros n Hn. unfold smsz, pg_up, needed, rounded. rewrite (rz_size_big n) by lia. rewrite !Z.max_l by lia.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (8 * ((n + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (8 * ((n + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ds_mad_geo : forall Σ k s, geo_ok Σ -> nth_error (sec Σ) k = Some s ->
  pbeg (shad (s_mb s)) mod 4096 = 0 /\ pend (shad (s_mb s + smsz (s_n s))) mod 4096 = 0
  /\ pbeg (shad (s_mb s)) < pend (shad (s_mb s + smsz (s_n s)))
  /\ (K_LOW_SHADOW_lo <= pbeg (shad (s_mb s)) /\ pend (shad (s_mb s + smsz (s_n s))) <= K_LOW_SHADOW_hi
      \/ K_HIGH_SHADOW_lo <= pbeg (shad (s_mb s)) /\ pend (shad (s_mb s + smsz (s_n s))) <= K_HIGH_SHADOW_hi)
  /\ (forall p : word, pbeg (shad (s_mb s)) <= bv_unsigned p -> bv_unsigned p + 4096 <= pend (shad (s_mb s + smsz (s_n s))) ->
        page_allowedb (rtA_allow Σ) p = true).
Proof.
  intros Σ k s HG Hk.
  pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & M3 & M4 & _ & _ & _ & M8 & _).
  pose proof (dk_geo Σ HG) as (_ & G2 & _).
  pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _ & SW6 & _).
  pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & (G1 & GA & _) & _).
  pose proof (proj1 (Forall_forall _ _) SW6 s (nth_error_In _ _ Hk)) as HAW.
  pose proof (ds_smsz_le (s_n s) ltac:(lia)) as Hsz.
  pose proof (smsz_big (s_n s) ltac:(lia)) as Hbig.
  assert (MSZ4 : smsz (s_n s) mod 4096 = 0).
  { unfold smsz, pg_up. apply Z.mod_divide; [lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). lia. }
  assert (MB8 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) GA); exists 512; reflexivity).
  assert (MSZ8 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) MSZ4); exists 512; reflexivity).
  assert (ESE : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8) by (apply shad_add8'; assumption).
  set (MB := s_mb s) in *. set (MSZ := smsz (s_n s)) in *.
  assert (SH0 : 0 <= shad MB) by (unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(lia) ltac:(lia)); lia).
  assert (Q8lo : 8192 <= MSZ / 8) by (apply Z.div_le_lower_bound; lia).
  pose proof (pbeg_facts (shad MB) SH0) as (PBR & PBA).
  pose proof (pend_facts (shad (MB + MSZ)) ltac:(rewrite ESE; lia)) as (PER & PEA).
  rewrite ESE in PER.
  split; [exact PBA|]. split; [exact PEA|]. split; [rewrite ESE; lia|].
  split.
  { rewrite ESE. clear - M1 M2 M4 G2 PBR PER ESE MB8 MSZ8. unfold shad in *. pose proof (Z.div_mod MB 8 ltac:(lia)) as D1.
    pose proof (Z.div_mod (MB + MSZ) 8 ltac:(lia)) as D2. rewrite MB8 in D1. rewrite Z.add_mod, MB8, MSZ8 in D2 by lia. cbn in D2.
    unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct M4 as [X|X]; [left | right]; lia. }
  intros p' H1 H2. rewrite ESE in H2. unfold page_allowedb. apply existsb_exists. exists (pg_dn (shad MB), pg_up (shad (MB + MSZ))).
  split; [unfold rtA_allow; apply in_or_app; left; exact HAW|]. cbn [fst snd]. unfold page_size.
  pose proof (pg_dn_facts (shad MB) ltac:(unfold shad, SHB; pose proof (Z.div_pos MB 8 ltac:(lia) ltac:(lia)); lia)) as (D1 & _).
  pose proof (pg_up_facts (shad (MB + MSZ)) ltac:(unfold shad, SHB; pose proof (Z.div_pos (MB + MSZ) 8 ltac:(lia) ltac:(lia)); lia)) as (U1 & _).
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Section ISec.
Variable p : dlp.
Hypothesis MN : munmap_node.
Hypothesis AN : madvise_node.
Hypothesis HOK : dl_ok p.
#[local] Notation PMc := (dl_PMc p).

Lemma ds_mun : forall j Σk b ib ents i rest k s, rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib -> nth_error (sec Σk) k = Some s -> s_quar s = true ->
  cps bsegs (ASTA RTA Σk PMc (svc_mun p j b ents i rest Σk k s)) (ASTA RTA (recs Σk k) PMc (dl_N p j b ents i rest (recs Σk k))).
Proof using MN HOK.
  intros j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Eann).
  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof HWP as (HL & HR & _ & HSW & _ & _ & HB & _).
  pose proof HB as (B1 & B2 & B3 & B4 & B5).
  pose proof (dk_map Σk HG k s Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & (G1 & G2 & _) & _).
  eapply cps_seq.
  - intros T cf Hcf HK. pose proof Hcf as (_ & _ & (HAM & _) & _). cbn [ARTM RTA] in HAM.
    apply (MN Σk (recs Σk k) PMc (svc_mun p j b ents i rest Σk k s) (fun ms => exists ms0, svc_mun p j b ents i rest Σk k s ms0 /\ ms = nretA ms0 (mun_eff s))
             (s_mb s) (smsz (s_n s)) FDO MST eq_refl eq_refl); [| | | exact HL | clear - B1 B3; lia | exact B4 | exact M8 | | clear - M1; lia | exact G2 | exact M2 | | exact Hcf | exact HK].
    + change (In (secmap s) (map secmap (rev (sec Σk)))). apply in_map. apply (proj1 (in_rev _ _)). exact (nth_error_In _ _ Hk).
    + exact (ds_perm Σk k s (cfg_model cf) Hk HG HAM).
    + pose proof (secsum_recs Σk k s Hk) as E. unfold rt_eager. change (secsum Σk) with (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec Σk)) in E.
      change (fold_right (fun s0 acc => smsz (s_n s0) + acc) 0 (sec (recs Σk k))) with (secsum (recs Σk k)).
      change (sum_cls (fun c => r_muser (pr (recs Σk k) c) + r_mfa (pr (recs Σk k) c)) 31) with (sum_cls (fun c => r_muser (pr Σk c) + r_mfa (pr Σk c)) 31).
      change (sec_nres (recs Σk k)) with (sec_nres Σk). rewrite E. clear; lia.
    + unfold smsz, pg_up. apply Z.mod_divide; [clear; lia|]. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) + 1). clear; lia.
    + intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & _).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists (MSsvc (uod_regs (Z_to_bv 64 0x5b270) (Z_to_bv 64 (dl_usp p - 2288 - 112))
        (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' (s_mb s) (smsz (s_n s)) a2' a3' a4' a5' a6' (Z_to_bv 64 1523080) (Z_to_bv 64 b) (Z_to_bv 64 (2^37))
        (Z_to_bv 64 (Z.of_nat (length ents))) (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16))
        (Z_to_bv 64 (16 + Z.of_nat i)) (dl_s10 p) (dl_s11 p) t3' t4' t5' t6') (dl_F p) (Z_to_bv 64 sec_munmap_ecall) (Z_to_bv 64 215)
        (dl_fc p) None m' (seg_rom bsegs)). split; [exact Hms | reflexivity].
  - apply (dl_evt (recs Σk k) PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
    exact (ds_ret p j b ib ents i rest Σk k s HOK HWP HS Hk Hq Hib Eb ms0 Hms0).
Qed.

Theorem item_sec_ok : item_sec_stmt p.
Proof using MN AN HOK.
  intros j Σk b ib ents i rest k s Hi HWP HS Hib Eb Hk Hq Hent.
  pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
  pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Eann).
  assert (Esk : skipn i ents = (s_mb s + 6128, s_n s) :: skipn (S i) ents)
    by (rewrite (skipn_nth_cons ents i (0, 0) Hi), Hent; reflexivity).
  assert (HWPc : rt_wfP Σk ((b, (s_mb s + 6128, s_n s) :: skipn (S i) ents) :: rest)) by (rewrite <- Esk; exact HWP).
  pose proof (rt_wfP_recs Σk b _ _ (skipn (S i) ents) rest k s HWPc Hk Hq eq_refl eq_refl) as HWP'.
  eapply (cps_conseq bsegs); [| intros cf Hcf; exact Hcf |].
  2:{ intros cf Hcf. exists (recs Σk k). split; [exact Hcf|]. split; [exact HWP'|].
      pose proof (recs_fields Σk k) as (X1 & X2 & _ & X4 & _ & _ & _ & X8 & _ & _ & X11 & X12 & X13).
      split; [split; [rewrite X1; exact El|]; split; [rewrite X12; exact Elv|]; split; [rewrite X13; exact Efr|];
              split; [rewrite X11; exact Ecr|]; split; [rewrite X8; exact Eql | split; [rewrite X4; exact Einit | etransitivity; [|exact Eann]; reflexivity]]|].
      rewrite X2. exact Hib. }
  apply cps_pointwise. intros ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
  rewrite Hent. cbn [fst].
  change (MS (mkR (Z_to_bv 64 0x5b270) (Z_to_bv 64 (dl_usp p - 2288 - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (dl_usp p - 2288))
                  (Z_to_bv 64 INST) (Z_to_bv 64 (dl_usp p - 2288 - 104)) (Z_to_bv 64 (s_mb s + 6128)) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 1522456) (Z_to_bv 64 1523080) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                  (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                  (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
              (dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs))
    with (ds_ms p b ents i s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).

  apply (cps_seq bsegs _ (ASTA RTA Σk PMc (svc_mad p b ents i Σk k s m))).
  { apply (dl_evt Σk PMc _ _ MST). intros ms0 <-.
    exact (ds_run1 p j b ib ents i rest Σk k s m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HOK HWP HS Hk Hq DM QB Hib Eb). }
  apply (cps_seq bsegs _ (ASTA RTA Σk PMc (fun ms => exists ms0, svc_mad p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff s)))).
  2:{ apply (cps_seq bsegs _ (ASTA RTA Σk PMc (svc_mun p j b ents i rest Σk k s))).
      - apply (dl_evt Σk PMc _ _ MST). intros ms (ms0 & Hms0 & ->).
        exact (ds_run2 p j b ib ents i rest Σk k s m HOK HWP HS Hk Hq DM QB Hib Eb ms0 Hms0).
      - exact (ds_mun j Σk b ib ents i rest k s HWP HS Hib Eb Hk Hq). }

  pose proof (geo_of_wfP _ _ HWP) as HG.
  pose proof HWP as (HL & _).
  pose proof (ds_mad_geo Σk k s HG Hk) as (R1 & R2 & R3 & R5 & R6).
  apply (AN Σk PMc (svc_mad p b ents i Σk k s m) (fun ms => exists ms0, svc_mad p b ents i Σk k s m ms0 /\ ms = nretA ms0 (mad_eff s))
           (pbeg (shad (s_mb s))) (pend (shad (s_mb s + smsz (s_n s)))) FDO MST HL R1 R2 R3 R5 R6).
  intros ms Hms. pose proof Hms as (t0' & t1' & t2' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & mA & ws & lst & muw & mudw & -> & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  eexists. split; [exact Hms | reflexivity].
Qed.

End ISec.

End GWIN.
