(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require BackingAlgebra.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_depot_defs R_fs_defs R_glue_defs R_tlsgetaddr RT_state RT_rep HandoffImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance ri_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Definition kw_at (ch : acs) (e : expr) (off : Z) (w : nat) : option expr :=
  let '(b, o) := split_lit e in kw_find (kn ch) b (o + off) w.
Definition kwv (ch : acs) (e : expr) (off : Z) (w : nat) : expr :=
  match kw_at ch e off w with Some v => v | None => ELit 0 end.
Definition isSome {X} (o : option X) : bool := match o with Some _ => true | None => false end.

Lemma kw_at_in : forall ch e off w, isSome (kw_at ch e off w) = true ->
  exists b o, split_lit e = (b, o) /\ In (KWord (SA b (o + off)) w (kwv ch e off w)) (kn ch).
Proof.
  intros ch e off w H. unfold kwv, kw_at in *. destruct (split_lit e) as [b o]. exists b, o. split; [reflexivity|].
  destruct (kw_find (kn ch) b (o + off) w) as [v|] eqn:Hf; [|discriminate]. exact (kw_find_in _ _ _ _ _ Hf).
Qed.

Definition eSB (ch : acs) : expr := kwv ch (ELit 0) i_spacebeg 8.
Definition eRIS (ch : acs) : expr := kwv ch (ELit 0) i_regioninfo 8.
Definition ePRB (ch : acs) : expr := kwv ch (ELit 0) INST 8.
Definition ePAB (ch : acs) : expr := kwv ch (ELit 0) i_sec_chunks 8.
Definition eTCX (ch : acs) : expr := kwv ch (ELit 0) g_pthread_tsd_main 8.
Definition eT (ch : acs) : expr := kwv ch (eTCX ch) 0x98 8.
Definition eTop (ch : acs) : expr := kwv ch (eT ch) off_t_stack_top 8.
Definition eFSB (ch : acs) : expr := kwv ch (ELit 0) tpA 8.
Definition eDTV (ch : acs) : expr := kwv ch (ELit 0) g_tls_dtls 8.
Definition eDNB (ch : acs) : expr := kwv ch (ELit 0) d_map1 8.
Definition eSSB (ch : acs) : expr := kwv ch (ELit 0) s_data0 8.
Definition ef0 (ch : acs) : expr := kwv ch (ELit 0) s_total 8.
Definition etid (ch : acs) : expr := kwv ch (ELit 0) 0x6a7dc0 4.
Definition eH1 (ch : acs) : expr := kwv ch (eDNB ch) 16 8.

Definition sigma_init (L : layoutA) (D : depot) : rtsA :=
  mkRtsA L (fun _ => reg0) (fun _ => []) false [] 0 [] [] [] D (fs0_init 5) (fs0_init 0) (fs0_init 4) (fs0_init 1) false CREDIT_INIT [] [] [].

Section Sigma0.
Variables (A : atable) (E : env) (ch : acs) (model : Model).

Definition lay0 : layoutA :=
  mkLayoutA (bv_unsigned (vm_init_sp (m_vmmaps model))) (uE E (eTop ch)) (uE E (ePRB ch)) (uE E (eSB ch)) (uE E (ePAB ch))
    (uE E (eT ch)) (uE E (eTCX ch)) (uE E (eDTV ch)) (uE E (eFSB ch)) (uE E (eDNB ch)) (uE E (eSSB ch)) (uE E (ef0 ch))
    (uE E (etid ch)) (List.filter vpos (vm_maps (m_vmmaps model))) (APS.allowA A E ch).

Definition dep0 : depot := mkDepot [uE E (eH1 ch)] (uE E (ef0 ch)).

Definition sigma0 : rtsA := sigma_init lay0 dep0.

End Sigma0.

Lemma nbusy_repeat0 : forall n, nbusy (repeat 0 n) = 0%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat nbusy]. rewrite IH. reflexivity. Qed.

Lemma fs_cls_wf_init : forall c, 0 <= c <= 14 -> fs_cls_wf c (fs0_init c).
Proof.
  intros c Hc. unfold fs_cls_wf, fs0_init, flags_ok. cbn [fss_flags fss_hint].
  rewrite repeat_length, nbusy_repeat0. split; [split|].
  - rewrite Z2Nat.id; [reflexivity|]. unfold NF. apply Z.pow_nonneg. lia.
  - apply Forall_forall. intros z Hz. apply repeat_spec in Hz. left. exact Hz.
  - split; [lia| pose proof (fs_cap_ge c); cbn; lia].
Qed.

Lemma ClassSize_nonneg : forall c, 1 <= c -> 0 <= ClassSize c.
Proof.
  intros c Hc. unfold ClassSize. destruct (c =? 31); [lia|]. destruct (c <=? 16); [lia|].
  assert (T : 0 <= Z.shiftl 512 ((c - 16) / 2)) by (apply Z.shiftl_nonneg; lia).
  assert (0 <= c mod 2) by (apply Z.mod_pos_bound; lia). assert (0 <= Z.shiftl 512 ((c - 16) / 2) / 2) by (apply Z.div_pos; lia).
  nia.
Qed.

Lemma ClassSize_pos0 : forall c, 1 <= c <= 31 -> 0 < ClassSize c.
Proof.
  intros c Hc. unfold ClassSize. destruct (c =? 31); [lia|]. destruct (c <=? 16) eqn:H16; [lia|].
  assert (T : 512 <= Z.shiftl 512 ((c - 16) / 2)).
  { rewrite Z.shiftl_mul_pow2 by (apply Z.div_pos; lia). pose proof (Z.pow_pos_nonneg 2 ((c - 16) / 2) ltac:(lia) ltac:(apply Z.div_pos; lia)). nia. }
  assert (0 <= c mod 2) by (apply Z.mod_pos_bound; lia). assert (0 <= Z.shiftl 512 ((c - 16) / 2) / 2) by (apply Z.div_pos; lia). nia.
Qed.

Lemma reg_wf_0 : forall c, 1 <= c <= 31 -> reg_wf c reg0.
Proof.
  intros c Hc. pose proof (ClassSize_pos0 c Hc) as Hcs. unfold reg_wf, reg0, kUserCap, kUMap, kFaCap.
  cbn [r_muser r_mfa r_st r_fl length]. repeat split; try lia; constructor.
Qed.

Lemma sum_cls_0 : forall k, sum_cls (fun _ => 0 + 0) k = 0.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [sum_cls]. rewrite IH. reflexivity. Qed.

Lemma rt_wf_init : forall L D, layout_ok L -> depot_ok D (l_DNB L) (l_SSB L) (l_ACEIL L) ->
  d_n D = 1 -> d_tot D + 255 < 2 ^ 20 -> dep_inv D -> rt_wf (sigma_init L D).
Proof.
  intros L D HL HD H1 H2 H3. unfold rt_wf. split; [exact HL|]. split.
  { unfold regs_wf. cbn [pr ca ca_init sigma_init]. split; [exact reg_wf_0|]. split; [intros; reflexivity|].
    split; [|split; [intros _ c; reflexivity | split; [intros c i Hc Hi; cbn [r_st reg0] in Hi; destruct i; discriminate Hi | intros _ c; reflexivity]]].
    intros c Hc. cbn [length app]. split; [unfold MaxCount; lia|]. split; constructor. }
  split.
  { unfold live_wf. cbn [live pr sec sigma_init]. split; [cbn; unfold LIVE_MAX; lia|]. split; [constructor|].
    split; [intros p n []|]. split; [intros c i n _ Hn; destruct i; discriminate|]. intros s []. }
  split.
  { unfold sec_wf. cbn [sec sec_nres sigma_init length]. split; [unfold SEC_MAX; lia|]. split; [left; reflexivity|].
    split; [intros H; exfalso; apply H; reflexivity|]. split; [constructor|].
    split; [intros k1 k2 s1 s2 Hk; destruct k1; discriminate| split; constructor]. }
  split.
  { unfold quar_wf, qbytes, qsum. cbn [ql qg sigma_init fold_right length app map]. unfold QMAX_L, QMAX_G.
    split; [lia|]. split; [lia|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
    unfold qents. cbn [ql qg sigma_init app flat_map map]. split; [constructor|]. split; [constructor|].
    intros c i Hc Hi. cbn [pr sigma_init r_st reg0] in Hi. destruct i; discriminate Hi. }
  split.
  { unfold fs_wf. cbn [fs0 fsc0 fs4 fs1 frames sigma_init]. split; [apply fs_cls_wf_init; lia|]. split; [apply fs_cls_wf_init; lia|].
    split; [apply fs_cls_wf_init; lia|]. split; [apply fs_cls_wf_init; lia|]. split; [constructor|]. split; [constructor|]. split; [cbn; lia|].
    split; intros k Hk; destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; unfold sigma_init;
      cbn [fs_of fs0 fsc0 fs4 fs1 fss_flags fss_hint fs0_init frames List.filter length credit];
      first [rewrite nbusy_repeat0; reflexivity | unfold CREDIT_INIT, CREDIT0; lia]. }
  split.
  { unfold budget_wf. cbn [credit aw sigma_init]. unfold CREDIT0, CREDIT_INIT. split; [lia|]. split; [constructor|]. split; [cbn; lia|].
    split; [unfold rt_eager; cbn [pr sec sec_nres sigma_init r_muser r_mfa reg0 fold_right]; rewrite sum_cls_0; lia|].
    unfold secsum. cbn [sec sigma_init fold_right]. lia. }
  split; [exact HD|]. split; [cbn [dep live credit sigma_init length]; rewrite H1; unfold dep_pot, DCOST; cbn; lia|]. split; [assumption|]. split; [assumption|].
  split; [intros c i n Hc Hi; cbn [pr sigma_init r_st reg0] in Hi; destruct i; discriminate Hi | intros s Hs; destruct Hs].
Qed.

Definition grant_facts (e : expr) (n : Z) : list kentry :=
  [ KRange e 1 (2 ^ 47 - n); KAlign e 4096;
    KDisj (SA e 0) (ELit n) (SA e_band 0) (ELit BANDLEN);
    KDisj (SA e 0) (ELit n) (SA (ELit 0) K_LOW_SHADOW_lo) (ELit (K_HIGH_SHADOW_hi - K_LOW_SHADOW_lo));
    KDisj (SA e 0) (ELit n) (SA (ELit 0) 0x10000) (ELit (SEGTOP_A - 0x10000)) ].

Definition kapart (e1 : expr) (n1 : Z) (e2 : expr) (n2 : Z) : kentry := KDisj (SA e1 0) (ELit n1) (SA e2 0) (ELit n2).

Definition grant_exprs (ch : acs) : list (expr * Z) :=
  [ (ePRB ch, 0x2000011000); (ePAB ch, 0x800000); (eT ch, 4096); (eTCX ch, 0x10000); (eDTV ch, 4096); (eFSB ch, 0xb09000);
    (eDNB ch, 0x100000); (eSSB ch, 0x800000) ].
Fixpoint pairs_of {X : Type} (l : list X) : list (X * X) :=
  match l with [] => [] | x :: r => map (fun y => (x, y)) r ++ pairs_of r end.
Definition apart_facts (ch : acs) : list kentry :=
  map (fun pq => kapart (fst (fst pq)) (snd (fst pq)) (fst (snd pq)) (snd (snd pq))) (pairs_of (grant_exprs ch)).

Lemma nth_error_map_inv : forall {X Y : Type} (f : X -> Y) l i y, nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ y = f x.
Proof. intros X Y f l i y H. rewrite nth_error_map in H. destruct (nth_error l i) as [x|]; [injection H as <-; exists x; split; reflexivity | discriminate]. Qed.

Lemma pairs_of_In : forall {X : Type} (l : list X) i j x y, (i < j)%nat -> nth_error l i = Some x -> nth_error l j = Some y ->
  In (x, y) (pairs_of l).
Proof.
  intros X l. induction l as [|a r IH]; intros i j x y Hij Hi Hj; [destruct i; discriminate|].
  cbn [pairs_of]. apply in_or_app. destruct i as [|i].
  - cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj. left. apply in_map_iff. exists y. split; [reflexivity|].
    exact (nth_error_In _ _ Hj).
  - destruct j as [|j]; [lia|]. right. exact (IH i j x y ltac:(lia) Hi Hj).
Qed.

Definition lay_facts (ch : acs) : list kentry :=
  [ KAlign e_sp0 16;
    KAlign (eTop ch) 4096; KRange (esub (eTop ch) (eaddz e_sp0 (-0xa0))) 0 4095;
    KRange (esub (eSB ch) (eaddz (ePRB ch) 0)) 0 0x10000;
    KRange (ef0 ch) 2 3; KRange (etid ch) 1 (2 ^ 31 - 1) ]
  ++ grant_facts (ePRB ch) 0x2000011000 ++ grant_facts (ePAB ch) 0x800000 ++ grant_facts (eT ch) 4096
  ++ grant_facts (eTCX ch) 0x10000 ++ grant_facts (eDTV ch) 4096 ++ grant_facts (eFSB ch) 0xb09000
  ++ grant_facts (eDNB ch) 0x100000 ++ grant_facts (eSSB ch) 0x800000
  ++ [ kapart (ePRB ch) 0x2000011000 (ePAB ch) 0x800000; kapart (ePRB ch) 0x2000011000 (eT ch) 4096;
       kapart (ePRB ch) 0x2000011000 (eTCX ch) 0x10000; kapart (ePRB ch) 0x2000011000 (eFSB ch) 0xb09000;
       kapart (ePRB ch) 0x2000011000 (eDNB ch) 0x100000; kapart (ePRB ch) 0x2000011000 (eSSB ch) 0x800000;
       kapart (eT ch) 4096 (eTCX ch) 0x10000; kapart (eT ch) 4096 (eFSB ch) 0xb09000;
       kapart (eTCX ch) 0x10000 (eFSB ch) 0xb09000; kapart (ePAB ch) 0x800000 (eFSB ch) 0xb09000;
       kapart (eDNB ch) 0x100000 (eSSB ch) 0x800000 ]
  ++ apart_facts ch.

Definition lay_lookups (ch : acs) : list (option expr) :=
  [ kw_at ch (ELit 0) i_spacebeg 8; kw_at ch (ELit 0) i_regioninfo 8; kw_at ch (ELit 0) INST 8; kw_at ch (ELit 0) i_sec_chunks 8;
    kw_at ch (ELit 0) g_pthread_tsd_main 8; kw_at ch (eTCX ch) 0x98 8; kw_at ch (eT ch) off_t_stack_top 8;
    kw_at ch (ELit 0) tpA 8; kw_at ch (ELit 0) g_tls_dtls 8; kw_at ch (ELit 0) d_map1 8; kw_at ch (ELit 0) s_data0 8;
    kw_at ch (ELit 0) s_total 8; kw_at ch (ELit 0) 0x6a7dc0 4; kw_at ch (eDNB ch) 16 8 ].

Definition sb_resid (ch : acs) : kentry :=
  KRange (eadd (esub (eSB ch) (eaddz (ePRB ch) 0x10000)) (mkAlu ALU_AND (ePRB ch) (ELit 0xffff))) 0 0.

Definition maps0_exprs (ch : acs) : list (expr * Z) := grant_exprs ch ++ map (fun g => (ELit (fst g), snd g)) shadow_res.
Definition amap_is (e : expr) (n : Z) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb (am_base m) e && expr_eqb (am_len m) (ELit n))%bool.

Definition am_lit_pos (m : amap) : bool := match am_len m with ELit n => (Z.ltb 0 n && Z.ltb n (2 ^ 64))%bool | _ => false end.
Definition hs_fog1_ok (ch : acs) : bool :=
  (forallb (fun m => is_fog m || am_lit_pos m) (a_maps ch) && Nat.leb (length (List.filter is_fog (a_maps ch))) 1)%bool.
Definition hs_maps0_ok (ch : acs) : bool :=
  (forallb (fun g => existsb (amap_is (fst g) (snd g)) (a_maps ch)) (maps0_exprs ch)
   && Nat.leb (length (a_maps ch)) 64 && Z.leb (a_totsz ch) (2 ^ 45) && hs_fog1_ok ch)%bool.

Definition amap_rwlazy (b l : Z) (mp : amap) : bool :=
  (expr_eqb (am_base mp) (ELit b) && expr_eqb (am_len mp) (ELit l) && mkind_eqb (am_kind mp) KRWLAZY)%bool.
Definition hs_shlazy_ok (ch : acs) : bool :=
  (existsb (amap_rwlazy K_LOW_SHADOW_lo (K_LOW_SHADOW_hi - K_LOW_SHADOW_lo)) (a_maps ch)
   && existsb (amap_rwlazy K_HIGH_SHADOW_lo (K_HIGH_SHADOW_hi - K_HIGH_SHADOW_lo)) (a_maps ch))%bool.

Definition hs_lay_ok (ch : acs) : bool :=
  (forallb isSome (lay_lookups ch) && forallb (fact_ok (kn ch)) (lay_facts ch) && existsb (kentry_eqb (sb_resid ch)) (kn ch)
   && expr_eqb (eRIS ch) (eaddz (eSB ch) (2 ^ 37))
   && Z.leb (a_eager ch) E0_MAX && Z.leb (a_abytes ch) (2 ^ 36) && hs_maps0_ok ch && hs_shlazy_ok ch)%bool.

Lemma A_bytes_allow_main : forall L, layout_ok L -> A_bytes (allow_main L) <= 2 ^ 35.
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as ((Hlo & Hhi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & _ & _ & _ & (F1 & F2 & F3 & F4 & F5) & _ & (S1 & S2 & S3 & S4 & S5) & _).
  unfold allow_main, A_bytes, pg_up, pg_dn, shad, SHB, l_ACEIL, STACK_WIN, SEGTOP_A, sp_window_lo, sp_window_hi in *. cbn [fst snd].
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma A_wf_app' : forall l1 l2, A_wf l1 -> A_wf l2 -> A_wf (l1 ++ l2).
Proof. intros l1 l2 H1 H2. unfold A_wf in *. apply Forall_app. split; assumption. Qed.

Lemma A_wf_allow_main : forall L, layout_ok L -> A_wf (allow_main L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as ((Hlo & Hhi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & _ & _ & _ & (F1 & F2 & F3 & F4 & F5) & _ & (S1 & S2 & S3 & S4 & S5) & _).
  unfold A_wf, allow_main, pg_up, pg_dn, shad, SHB, l_ACEIL, STACK_WIN, SEGTOP_A, page_size, sp_window_lo, sp_window_hi in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat constructor; cbn [fst snd]; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Section Pure.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Hypothesis HT : hs_lay_ok ch = true.

#[local] Notation M := (APS.Mr A argH E ch model FULL).
#[local] Notation L := (lay0 A E ch model).
#[local] Notation sp0 := (bv_unsigned (vm_init_sp (m_vmmaps model))).

Lemma ri_know : know_ok asegs E M (kn ch).
Proof. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma ri_test : forallb isSome (lay_lookups ch) = true /\ forallb (fact_ok (kn ch)) (lay_facts ch) = true
  /\ eRIS ch = eaddz (eSB ch) (2 ^ 37) /\ a_eager ch <= E0_MAX /\ a_abytes ch <= 2 ^ 36 /\ In (sb_resid ch) (kn ch).
Proof.
  pose proof HT as H. unfold hs_lay_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
  split; [exact H1|]. split; [exact H2|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  apply existsb_exists in H3 as (K & HK & HKe). apply APS.kentry_eqb_eq in HKe. subst K. exact HK.
Qed.

Lemma ri_facts : Forall (kentry_ok asegs E M) (lay_facts ch).
Proof.
  apply Forall_forall. intros K HK. apply (APS.fact_ok_sound asegs E M (kn ch) K ri_know).
  exact (proj1 (forallb_forall _ _) (proj1 (proj2 ri_test)) K HK).
Qed.

Lemma ri_sp0 : sp0 = uE E e_sp0 /\ sp_window_lo <= sp0 <= sp_window_hi.
Proof. pose proof (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as X. unfold APS.uE in X. exact X. Qed.

Lemma ri_band : uE E e_band = sp0 - 0x800000.
Proof.
  pose proof (APS.band_alloc_top _ _ _ _ _ _ _ _ _ _ _ _ HC) as X. unfold APS.uE in X. unfold uE. rewrite X.
  unfold alloc_top, stack_max_size. lia.
Qed.

Lemma ri_grant : forall e n, 0 < n < 2 ^ 40 -> Forall (kentry_ok asegs E M) (grant_facts e n) -> grant_ok L (uE E e) n.
Proof.
  intros e n Hn HF. unfold grant_facts in HF.
  apply Forall_cons_iff in HF as [F1 HF]. apply Forall_cons_iff in HF as [F2 HF]. apply Forall_cons_iff in HF as [F3 HF].
  apply Forall_cons_iff in HF as [F4 HF]. apply Forall_cons_iff in HF as [F5 _].
  cbn [kentry_ok] in F1, F2, F3, F4, F5. unfold estart in F3, F4, F5. cbn [a_base a_off edenot] in F3, F4, F5.
  rewrite !APS.elenZ_lit in F3, F4, F5 by (unfold BANDLEN, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SEGTOP_A; lia).
  rewrite u_lit64 in F4, F5. unfold two64 in F4, F5. change (0 mod 2 ^ 64) with 0 in F4, F5.
  pose proof ri_band as Hb. pose proof ri_sp0 as [_ [Hlo Hhi]].
  unfold grant_ok, l_ACEIL, STACK_WIN. cbn [l_sp0 lay0]. unfold uE in *. unfold sp_window_lo, sp_window_hi, BANDLEN in *.
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  destruct F2 as [_ F2]. split; [lia|]. split; [exact F2|]. split; [lia|]. split; lia.
Qed.

Lemma ri_apart : forall e1 n1 e2 n2, 0 <= n1 < 2 ^ 64 -> 0 <= n2 < 2 ^ 64 -> kentry_ok asegs E M (kapart e1 n1 e2 n2) ->
  apart (uE E e1) n1 (uE E e2) n2.
Proof.
  intros e1 n1 e2 n2 H1 H2 K. unfold kapart in K. cbn [kentry_ok] in K. unfold estart in K. cbn [a_base a_off] in K.
  rewrite !APS.elenZ_lit in K by lia. unfold apart, uE. lia.
Qed.

Lemma ri_diff : forall a b z lo hi, 0 <= lo -> hi < 2 ^ 40 -> 0 <= z < 2 ^ 40 -> z <= uE E b -> uE E b < 2 ^ 48 ->
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

Lemma ri_test_maps0 : hs_maps0_ok ch = true.
Proof. pose proof HT as H. unfold hs_lay_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma ri_test_shlazy : hs_shlazy_ok ch = true.
Proof. pose proof HT as H. unfold hs_lay_ok in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma ri_shadow_lazy : shadow_lazy model.
Proof.
  pose proof ri_test_shlazy as H. unfold hs_shlazy_ok in H. apply andb_prop in H as [H2 H4].
  assert (K : forall b l, existsb (amap_rwlazy b l) (a_maps ch) = true -> 0 <= b -> 0 <= l -> b + l < 2 ^ 64 ->
            forall a : word, b <= bv_unsigned a < b + l ->
              page_in_ranges (page_base a) (m_vm_lazy model) = true
              /\ BackingAlgebra.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a) = false).
  { intros b l Hx Hb Hl Hbl a Ha. apply existsb_exists in Hx as (mp & Hmp & Hok). unfold amap_rwlazy in Hok.
    apply andb_prop in Hok as [Hok Hk]. apply andb_prop in Hok as [Hb' Hl'].
    apply expr_eqb_eq in Hb'. apply expr_eqb_eq in Hl'. apply APS.mkind_eqb_eq in Hk.
    destruct (proj1 (Forall_forall _ _) (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) mp Hmp Hk a) as [Hna Hlz].
    { rewrite Hb', Hl'. cbn [edenot]. rewrite !unsigned_lit by lia. lia. }
    split; [exact Hlz|]. unfold BackingAlgebra.covered, BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S.
    unfold APS.in_ivs in Hna. exact Hna. }
  intros a Ha. unfold shreg in Ha. destruct Ha as [Ha|Ha].
  - apply (K _ _ H2); unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi in *; lia.
  - apply (K _ _ H4); unfold K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia.
Qed.

Lemma maps_match_length : forall E0 ms l, APS.maps_match E0 ms l -> (length l <= length ms)%nat.
Proof.
  intros E0 ms. induction ms as [|m ms IH]; intros l H; cbn [APS.maps_match] in H.
  - subst l. cbn. lia.
  - destruct (is_fog m).
    + destruct H as [H | (iv & l' & -> & _ & H)]; [pose proof (IH l H); cbn; lia | pose proof (IH l' H); cbn; lia].
    + destruct H as (l' & -> & H). pose proof (IH l' H). cbn. lia.
Qed.

Lemma live_bytes_sum_sizes : forall l, live_bytes l = APS.sum_sizes l.
Proof. induction l as [|[a sz] l IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma sum_sizes_app : forall l1 l2, APS.sum_sizes (l1 ++ l2) = APS.sum_sizes l1 + APS.sum_sizes l2.
Proof. induction l1 as [|iv l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma sum_sizes_nonneg : forall l, 0 <= APS.sum_sizes l.
Proof. induction l as [|iv l IH]; cbn; [lia| pose proof (u64_range (snd iv)); lia]. Qed.

Lemma filter_length_le' : forall {T : Type} (f : T -> bool) (l : list T), (length (List.filter f l) <= length l)%nat.
Proof. intros T f l. induction l as [|x l IH]; cbn [List.filter length]; [lia|]. destruct (f x); cbn [length]; lia. Qed.

Lemma sum_sizes_filter_le : forall (f : word * word -> bool) l, APS.sum_sizes (List.filter f l) <= APS.sum_sizes l.
Proof.
  intros f l. induction l as [|iv l IH]; cbn [List.filter]; [lia|]. pose proof (u64_range (snd iv)).
  destruct (f iv); cbn [APS.sum_sizes]; lia.
Qed.

Lemma ri_maps0 : maps0_ok L.
Proof.
  pose proof ri_test_maps0 as H. unfold hs_maps0_ok in H. apply andb_prop in H as [H _].
  apply andb_prop in H as [H Htot]. apply andb_prop in H as [Hall Hlen].
  apply Nat.leb_le in Hlen. apply Z.leb_le in Htot.
  pose proof (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as HM.
  unfold maps0_ok. cbn [l_maps0 lay0]. split; [|split; [|split]].
  - assert (EG : startup_grants L ++ shadow_res = map (fun ge => (uE E (fst ge), snd ge)) (maps0_exprs ch)) by reflexivity.
    rewrite EG, Forall_map. apply Forall_forall. intros ge Hge.
    assert (Hpos : 0 < snd ge < 2 ^ 64).
    { unfold maps0_exprs, grant_exprs, shadow_res in Hge. cbn [app map] in Hge.
      repeat (destruct Hge as [<-|Hge]; [cbn [snd]; lia|]). destruct Hge. }
    pose proof (proj1 (forallb_forall _ _) Hall ge Hge) as Hex. apply existsb_exists in Hex as (m & Hm & Hok).
    unfold amap_is in Hok. apply andb_prop in Hok as [Hok Hl]. apply andb_prop in Hok as [Hf Hb].
    apply negb_true_iff in Hf. apply expr_eqb_eq in Hb. apply expr_eqb_eq in Hl.
    pose proof (APS.maps_match_In _ _ _ m HM Hm Hf) as Hin. unfold APS.amap_den in Hin. rewrite Hb, Hl in Hin.
    cbn [fst snd]. unfold uE. rewrite Z_to_bv_bv_unsigned. apply List.filter_In. split; [exact Hin|].
    unfold vpos. cbn [snd]. apply Z.ltb_lt. rewrite unsigned_lit by lia. lia.
  - pose proof (maps_match_length _ _ _ HM). pose proof (filter_length_le' vpos (vm_maps (m_vmmaps model))). lia.
  - pose proof (APS.co_totsz _ _ _ _ _ _ _ _ _ _ _ _ HC) as Ht. rewrite sum_sizes_app in Ht.
    pose proof (sum_sizes_nonneg (vm_reserved (m_vmmaps model))). pose proof (sum_sizes_filter_le vpos (vm_maps (m_vmmaps model))).
    rewrite live_bytes_sum_sizes. lia.
  - exact (filter_vpos_pos _).
Qed.

Lemma maps_match_len_pos : forall (ms : list amap) (l : list (word * word)), APS.maps_match E ms l ->
  (forall m, In m ms -> is_fog m = false -> 0 < uE E (am_len m)) ->
  Z.of_nat (length l) <= Z.of_nat (length (List.filter vpos l)) + Z.of_nat (length (List.filter is_fog ms)).
Proof.
  induction ms as [|m ms IH]; intros l HM Hpos; cbn [APS.maps_match] in HM.
  - subst l. cbn [length List.filter]. lia.
  - assert (Hpos' : forall m', In m' ms -> is_fog m' = false -> 0 < uE E (am_len m')) by (intros m' Hm' Hf'; apply Hpos; [right; exact Hm' | exact Hf']).
    destruct (is_fog m) eqn:Ef.
    + cbn [List.filter]. rewrite Ef. cbn [length]. destruct HM as [HM | (iv & l' & -> & _ & HM)].
      * specialize (IH l HM Hpos'). lia.
      * specialize (IH l' HM Hpos'). cbn [List.filter]. destruct (vpos iv); cbn [length]; lia.
    + cbn [List.filter]. rewrite Ef. destruct HM as (l' & -> & HM). specialize (IH l' HM Hpos').
      pose proof (Hpos m (or_introl eq_refl) Ef) as Hm. cbn [List.filter].
      assert (Ev : vpos (APS.amap_den E m) = true) by (unfold vpos, APS.amap_den; cbn [snd]; apply Z.ltb_lt; exact Hm).
      rewrite Ev. cbn [length]. lia.
Qed.

Lemma ri_zbound : maps_zbound model.
Proof.
  pose proof ri_test_maps0 as H. unfold hs_maps0_ok in H. apply andb_prop in H as [_ H]. unfold hs_fog1_ok in H.
  apply andb_prop in H as [Hall H1]. apply Nat.leb_le in H1.
  pose proof (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) as HM. unfold maps_zbound.
  pose proof (maps_match_len_pos (a_maps ch) (vm_maps (m_vmmaps model)) HM) as X.
  assert (Hpos : forall m, In m (a_maps ch) -> is_fog m = false -> 0 < uE E (am_len m)).
  { intros m Hm Hf. assert (Hx : (is_fog m || am_lit_pos m)%bool = true) by exact (proj1 (forallb_forall _ _) Hall m Hm).
    rewrite Hf in Hx. cbn [orb] in Hx.
    unfold am_lit_pos in Hx. destruct (am_len m) eqn:En; try discriminate. rename z into n.
    apply andb_prop in Hx as [X1 X2]. apply Z.ltb_lt in X1. apply Z.ltb_lt in X2. unfold uE. cbn [edenot].
    rewrite unsigned_lit by lia. exact X1. }
  specialize (X Hpos). lia.
Qed.

Lemma ri_noaccess_pos : NodesA_madv.noaccess_pos model.
Proof.
  pose proof (APS.co_naal _ _ _ _ _ _ _ _ _ _ _ _ HC) as NA. unfold NodesA_madv.noaccess_pos.
  eapply Forall_impl; [|exact NA]. intros iv (_ & _ & H). exact H.
Qed.

Lemma ri_layout_ok : layout_ok L.
Proof.
  pose proof ri_facts as HF. unfold lay_facts in HF. rewrite !Forall_app in HF.
  destruct HF as (HF0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & HA & HP).
  apply Forall_cons_iff in HF0 as [Fsp HF0]. apply Forall_cons_iff in HF0 as [Ft1 HF0]. apply Forall_cons_iff in HF0 as [Ft2 HF0].
  apply Forall_cons_iff in HF0 as [Fs2 HF0]. apply Forall_cons_iff in HF0 as [Ff0 HF0].
  apply Forall_cons_iff in HF0 as [Ftid _].
  apply ri_grant in G1; [|lia]. apply ri_grant in G2; [|lia]. apply ri_grant in G3; [|lia]. apply ri_grant in G4; [|lia].
  apply ri_grant in G5; [|lia]. apply ri_grant in G6; [|lia]. apply ri_grant in G7; [|lia]. apply ri_grant in G8; [|lia].
  rename G1 into W1.
  repeat match type of HA with Forall _ (_ :: _) => let X := fresh "X" in apply Forall_cons_iff in HA as [X HA] end.
  repeat match goal with X : kentry_ok _ _ _ (kapart _ _ _ _) |- _ => apply ri_apart in X; [| lia | lia] end.
  destruct ri_sp0 as [Hsp [Hlo Hhi]].
  pose proof ri_test as (_ & _ & _ & _ & Hab & Hres).
  cbn [kentry_ok] in Fsp, Ft1, Ff0, Ftid. destruct Fsp as [_ Fsp]. destruct Ft1 as [_ Ft1].
  unfold grant_ok in W1. destruct W1 as (W1a & W1b & W1c & W1d & W1e).
  unfold l_ACEIL, STACK_WIN in W1c. cbn [l_sp0 lay0] in W1c.
  unfold sp_window_lo, sp_window_hi in *.
  assert (Htop : sp0 - 0xa0 <= uE E (eTop ch) <= sp0 - 0xa0 + 4095).
  { pose proof (ri_diff (eTop ch) e_sp0 0xa0 0 4095 ltac:(lia) ltac:(lia) ltac:(lia)) as D. rewrite <- Hsp in D.
    specialize (D ltac:(lia) ltac:(lia) Ft2). lia. }
  assert (Hsb : uE E (ePRB ch) <= uE E (eSB ch) <= uE E (ePRB ch) + 0x10000).
  { pose proof (ri_diff (eSB ch) (ePRB ch) 0 0 0x10000 ltac:(lia) ltac:(lia) ltac:(lia)) as D.
    replace (- 0) with 0 in D by reflexivity.
    specialize (D ltac:(unfold uE; pose proof (u64_range (edenot E (ePRB ch))); lia) ltac:(lia) Fs2). lia. }
  assert (Fs1 : uE E (eSB ch) mod 2 ^ 16 = 0).
  { pose proof (proj1 (Forall_forall _ _) ri_know _ Hres) as K. unfold sb_resid in K. cbn [kentry_ok] in K.
    unfold eadd, esub, eaddz in K. rewrite !mkAlu_denot in K. rewrite u_add64, u_sub64, u_add64, u_and64 in K. cbn [edenot] in K.
    rewrite !u_lit64 in K. unfold two64 in K. replace (65535 mod 2 ^ 64) with (Z.ones 16) in K by reflexivity. rewrite Z.land_ones in K by lia.
    unfold uE in *. pose proof (u64_range (edenot E (ePRB ch))). pose proof (u64_range (edenot E (eSB ch))).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  unfold layout_ok. cbn [l_sp0 l_top l_PRB l_SB l_PAB l_T l_TCX l_DTV l_FSB l_DNB l_SSB l_f0 l_tid l_al0 lay0].
  unfold sp_window_lo, sp_window_hi.
  split; [lia|]. split; [rewrite Hsp; exact Fsp|]. split; [lia|]. split; [exact Ft1|].
  split; [unfold grant_ok; repeat split; assumption|]. split; [exact Fs1|]. split; [lia|].
  repeat (split; [assumption|]).
  split; [unfold uE in *; lia|]. split; [unfold uE in *; lia|]. split; [exact (APS.A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) O E ch)|].
  split; [pose proof (APS.co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC); lia|].
  split; [assumption|].
  split; [exact ri_maps0|].

  intros i j g1 g2 Hij H1 H2.
  assert (HG : startup_grants L = map (fun ge => (uE E (fst ge), snd ge)) (grant_exprs ch)) by reflexivity.
  rewrite HG in H1, H2. apply nth_error_map_inv in H1 as (e1 & H1 & ->). apply nth_error_map_inv in H2 as (e2 & H2 & ->).
  pose proof (pairs_of_In _ _ _ _ _ Hij H1 H2) as Hin.
  unfold apart_facts in HP. rewrite Forall_map in HP. pose proof (proj1 (Forall_forall _ _) HP _ Hin) as K. cbn beta in K.
  assert (GB : Forall (fun ge => 0 <= snd ge < 2 ^ 64) (grant_exprs ch)) by (unfold grant_exprs; repeat constructor; cbn [snd]; lia).
  pose proof (proj1 (Forall_forall _ _) GB _ (nth_error_In _ _ H1)) as B1.
  pose proof (proj1 (Forall_forall _ _) GB _ (nth_error_In _ _ H2)) as B2.
  exact (ri_apart _ _ _ _ B1 B2 K).
Qed.

Lemma ri_depot_ok : depot_ok (dep0 E ch) (l_DNB L) (l_SSB L) (l_ACEIL L).
Proof.
  pose proof ri_layout_ok as HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GD & GS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0 & _ & _ & _ & HDS).
  unfold grant_ok in GD, GS. unfold depot_ok, dep0, d_n. cbn [d_hs d_tot length].
  split; [constructor; [unfold uE; apply u64_range| constructor]|]. split; [lia|]. split; [cbn [lay0 l_f0] in Hf0; lia|].
  unfold apart in HDS. unfold SEGTOP_A in *. lia.
Qed.

Lemma ri_rt_wf : rt_wf (sigma0 A E ch model).
Proof.
  pose proof ri_layout_ok as HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0 & _).
  cbn [lay0 l_f0] in Hf0.
  apply rt_wf_init; [exact ri_layout_ok | exact ri_depot_ok | unfold dep0, d_n; cbn; reflexivity | unfold dep0; cbn [d_tot]; lia |].
  unfold dep_inv, dep0, d_n. cbn [d_hs d_tot length]. split; [constructor; [intros []| constructor]|].
  split; [lia | cbn; lia].
Qed.

Lemma seps_FOP : forall l, APS.seps l -> ForallOrdPairs iv_apart l.
Proof. intros l H. induction H as [|p l Hf Hs IH]; constructor; [exact Hf | exact IH]. Qed.

Lemma ri_artm : LIMIT = VMLIMIT -> ARTM_A (sigma0 A E ch model) model.
Proof.
  intros Hlim. unfold ARTM_A. split; [exact (Permutation_refl _)|]. split; [exact (APS.co_res _ _ _ _ _ _ _ _ _ _ _ _ HC)|].
  split; [rewrite (APS.co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC); exact Hlim|].
  split.
  { pose proof (APS.co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC) as He. pose proof ri_test as (_ & _ & _ & Hea & _).
    unfold rt_eager, sigma0, sigma_init. cbn [pr sec sec_nres r_muser r_mfa reg0 fold_right]. rewrite sum_cls_0. lia. }

  unfold artm_sys. split; [exact (APS.co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC)|].
  split; [exact (APS.co_lazyin _ _ _ _ _ _ _ _ _ _ _ _ HC)|].
  split; [exact (seps_FOP _ (APS.co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC))|].
  split; [reflexivity|].
  split; [|split; [exact ri_shadow_lazy | split; [exact ri_zbound | exact ri_noaccess_pos]]].

  intros z Hz. cbn [l_maps0 lay sigma0 sigma_init lay0]. rewrite covered_filter_vpos.
  rewrite BackingAlgebra.covered_app in Hz. apply orb_true_iff in Hz as [Hz|Hz].
  - exact (APS.co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC z Hz).
  - unfold BackingAlgebra.covered in Hz. apply existsb_exists in Hz as (iv & Hiv & Hin).
    unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S in Hin.
    apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (APS.co_lazyin _ _ _ _ _ _ _ _ _ _ _ _ HC iv Hiv ltac:(lia)) as (e & He & E1 & E2).
    unfold BackingAlgebra.covered. apply existsb_exists. exists e. split; [exact He|].
    unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S.
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma ri_allow : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rtA_allow (sigma0 A E ch model)) p = true.
Proof. intros p Hp. unfold rtA_allow, sigma0, sigma_init. cbn [aw lay l_al0 lay0 app]. apply APS.page_allowedb_app_l. exact Hp. Qed.

Lemma ri_awf : A_wf (rtA_allow (sigma0 A E ch model)).
Proof.
  unfold rtA_allow, sigma0, sigma_init. cbn [aw lay app]. apply A_wf_app'.
  - exact (APS.A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) O E ch).
  - exact (A_wf_allow_main _ ri_layout_ok).
Qed.

Lemma ri_minv : LIMIT = VMLIMIT -> MInv (rtA_allow (sigma0 A E ch model)) model.
Proof.
  intros Hlim. unfold rtA_allow, sigma0, sigma_init. cbn [aw lay app l_al0 lay0].
  apply APS.MInv_app_r; [exact (APS.co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC)|].
  rewrite APS.A_bytes_app, (APS.co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC), Hlim.
  pose proof (APS.co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC) as He. pose proof (APS.co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC) as Ha.
  pose proof ri_test as (_ & _ & _ & Hea & Hab). pose proof (A_bytes_allow_main _ ri_layout_ok) as Hm.
  unfold E0_MAX, VMLIMIT in *. lia.
Qed.

Lemma ri_sig : sigma0_ok RTA (sigma0 A E ch model) (sp0 - USP_OFF).
Proof.
  unfold sigma0_ok. cbn [rt_live rt_frames rt_credit rt_sp0 RTA]. unfold rtA_live, rtA_frames, rtA_credit, rtA_sp0, sigma0, sigma_init.
  cbn [live frames ann credit lay l_sp0 lay0]. pose proof ri_sp0 as (_ & Hlo & _). unfold sp_window_lo, USP_OFF, CREDIT_DRV, CREDIT_INIT in *.
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; lia.
Qed.

End Pure.
