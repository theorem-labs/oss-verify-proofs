(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_libiface_pem D_agree D_clx Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_writec Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W7_defs Fz_W7_segs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition W7_CALLEE_STACK : Z := 1408.
(* [comment removed for export] *)
Definition W7_CALLS_X : list (Z * Z) :=
  [(RA_FUZZ, e_fuzz_one_body);
   (SITE_w7_free1, e_free); (SITE_w7_free2, e_free); (SITE_w7_free3, e_free);
   (SITE_w7_sfree1, e_CRYPTO_free); (SITE_w7_sfree2, e_CRYPTO_free); (SITE_w7_sfree3, e_CRYPTO_free);
   (SITE_w7_sfree1, e_free); (SITE_w7_sfree2, e_free); (SITE_w7_sfree3, e_free)].
Definition W7_CALLS_ALL : list (Z * Z) := W7_CALLS_OWN ++ W7_CALLS_X.

Section W7I.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
(* [comment removed for export] *)
Variable LIB : list (Z * Z) -> mem -> Prop.
Variable REST : mem -> Prop.
Variable REST_fp : Z -> Prop.
Hypothesis REST_agree : forall m m', REST m -> agree_on REST_fp m m' -> REST m'.
Hypothesis REST_fp_where : forall a, REST_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record w7a : Type := W7A {
  a_S0 : rts RT; a_PMc : Model -> Prop;
  a_ra : word; a_sp : word; a_gp : word;
  a_s0 : word; a_s1 : word; a_s2 : word; a_s3 : word; a_s4 : word; a_s5 : word; a_s6 : word; a_s7 : word; a_s8 : word; a_s9 : word; a_s10 : word; a_s11 : word;
  a_F : bvmap 5 word; a_fc : bv 32; a_m : mem; a_lo : Z; a_CL : list (Z * Z); a_DRV : list (Z * Z);
  a_d : Z; a_bs : list byte; a_canary : word; a_E : Z; a_LBL : list (Z * Z); a_pd : Z; a_f : Z }.
Definition a_SP (en : w7a) : Z := bv_unsigned (a_sp en).
Definition a_sp1 (en : w7a) : Z := a_SP en + -160 - a_pd en.
Definition a_len (en : w7a) : Z := Z.of_nat (length (a_bs en)).
(* [comment removed for export] *)
Definition w7_savedl (en : w7a) : list cell :=
  [C8 (a_s11 en); C8 (a_s10 en); C8 (a_s9 en); C8 (a_s8 en); C8 (a_s7 en); C8 (a_s6 en); C8 (a_s5 en); C8 (a_s4 en); C8 (a_s3 en); C8 (a_s2 en); C8 (a_s1 en);
   C8 (a_s0 en); C8 (a_ra en)].
(* [comment removed for export] *)
Definition w7_mf (en : w7a) (c0 c1 c2 c3 c4 c5 c6 : cell) : list cell :=
  w7_mframe7 c0 c1 c2 c3 c4 c5 c6 (a_s11 en) (a_s10 en) (a_s9 en) (a_s8 en) (a_s7 en) (a_s6 en) (a_s5 en) (a_s4 en) (a_s3 en) (a_s2 en) (a_s1 en) (a_s0 en) (a_ra en).
(* [comment removed for export] *)
Definition w7_fhdr : list cell := [C8 (wz W7_MAGIC); C8 (wz W7_DESCR); C8 (wz e_fuzz_one_body)].

(* [comment removed for export] *)
Definition w7_ms (en : w7a) (pc : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 t3 t4 t5 t6 : word) : machine_state :=
  MS (w7_regsE ra (a_sp en) (a_gp en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 t3 t4 t5 t6 (a_d en) (a_f en) (a_pd en)) F (wz pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition w7_post (en : w7a) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (CL' : list (Z * Z)),
       ASTA RT Σ' (a_PMc en) (fun ms => exists m', ret_st (a_ra en) (a_sp en) (a_gp en) (wz TP_A) (a_s0 en) (a_s1 en) (a_s2 en) (a_s3 en) (a_s4 en) (a_s5 en)
                                                  (a_s6 en) (a_s7 en) (a_s8 en) (a_s9 en) (a_s10 en) (a_s11 en) (wz 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned (a_sp en)) (a_lo en) (a_m en) m'
         /\ cli_pres (a_DRV en) (bv_unsigned (a_sp en)) (a_m en) m' /\ LIB CL' m' /\ (exists v, rw_cells asegs m' (errno_cell (wz TP_A)) [C4 v])) c
       /\ Permutation (rt_live RT Σ') (CL' ++ a_DRV en) /\ Z.of_nat (length CL') <= CLI_MAX /\ (forall p n, In (p, n) CL' -> 0 < n)
       /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT (a_S0 en) /\ rt_credit RT (a_S0 en) - FUZZ_COST <= rt_credit RT Σ'
       /\ rt_cg RT Σ' = rt_cg RT (a_S0 en).
Definition w7_at (en : w7a) (Σ : rts RT) (ms : machine_state) : Prop := cps asegs (ASTA RT Σ (a_PMc en) (eq ms)) (w7_post en).

(* [comment removed for export] *)
Definition w7_com (en : w7a) (Σ : rts RT) (m : mem) (crem : Z) (cur : list (Z * Z)) : Prop :=
     ART RT Σ m /\ mem_inv asegs m /\ stk asegs m (a_lo en) (a_sp1 en) /\ stk asegs m (a_sp1 en) (a_SP en + -160)
  /\ (a_pd en = 0 \/ a_pd en = 16) /\ a_SP en mod 32 = a_pd en /\ a_SP en + 16 <= USTACK_TOP
  /\ rt_sp0 RT Σ - STACK_WIN <= a_lo en /\ a_lo en + RT_STACK + W7_CALLEE_STACK <= a_sp1 en /\ 0x10007fff8000 <= a_lo en
  /\ cl_env m (Z_to_bv 8 1) (a_canary en) /\ sec_off m
  /\ libenv m (a_LBL en) (a_E en) /\ incl_live (a_LBL en) (a_CL en) /\ In (a_E en, 904) (a_CL en) /\ ~ In (a_E en, 904) (a_LBL en) /\ REST m
  (* [comment removed for export] *)
  /\ Permutation (rt_live RT Σ) (cur ++ a_CL en ++ a_DRV en) /\ (forall e, In e cur -> ~ In (fst e) (map fst (a_CL en ++ a_DRV en)))
  /\ List.NoDup (map fst cur) /\ (forall e, In e (rt_live RT Σ) -> 0 < snd e)
  (* [comment removed for export] *)
  /\ rt_frames RT Σ = [(a_f en, 2%nat)] /\ rt_sp0 RT Σ = rt_sp0 RT (a_S0 en) /\ rt_cg RT Σ = rt_cg RT (a_S0 en)
  /\ Z.of_nat (length (a_CL en ++ a_DRV en)) + FUZZ_LIVE <= LIVE_MAX /\ Z.of_nat (length (a_CL en)) <= CLI_MAX
  /\ rt_credit RT (a_S0 en) - FUZZ_COST + crem <= rt_credit RT Σ /\ 0 <= crem /\ FUZZ_COST <= rt_credit RT (a_S0 en)
  /\ cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS /\ cg_sub W7_SITES_OWN W7_CALLS_ALL FZ_SITES FZ_CALLS
  /\ fp_invalid (a_s0 en) (a_sp en) /\ a_ra en = wz RA_FUZZ /\ Z.of_nat (length cur) + 32 <= FUZZ_LIVE
  (* [comment removed for export] *)
  /\ 0 < a_f en /\ (a_f en) mod 64 = 0 /\ a_f en + 256 < USTACK_TOP
  /\ rw_cells asegs m (shad (a_f en)) w7_shadow_live /\ (exists sjr, rw_cells asegs m (shad (a_f en) + 20) [CB 12 sjr]) /\ rw_cells asegs m (a_f en) w7_fhdr
  (* [comment removed for export] *)
  /\ rw_cells asegs m (a_SP en + -104) (w7_savedl en)
  /\ rt_pres_fp (a_DRV en) [] (a_SP en) LIB_W (a_m en) m
  /\ bytes_at asegs m (a_d en) (a_bs en) /\ (a_bs en = [] \/ exists p n, In (p, n) (a_DRV en) /\ p <= a_d en /\ a_d en + a_len en <= p + n) /\ a_len en < 2 ^ 26
  /\ fdfs_only (a_PMc en) /\ mat_stable (a_PMc en).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w7_lists : forall en Σ m crem cur, w7_com en Σ m crem cur ->
  (forall e, In e cur -> In e (rt_live RT Σ)) /\ (forall e, In e (a_CL en) -> In e (rt_live RT Σ)) /\ (forall e, In e (a_DRV en) -> In e (rt_live RT Σ)).
Proof.
  intros en Σ m crem cur COM.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & _).
  split; [| split]; intros e He; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app;
    [left; exact He| right; apply in_or_app; left; exact He| right; apply in_or_app; right; exact He].
Qed.

(* [comment removed for export] *)
Lemma w7_fframe_facts : forall en Σ m crem cur, w7_com en Σ m crem cur ->
  In (a_f en, 2%nat) (rt_frames RT Σ) /\ a_f en + 256 <= a_lo en /\ SEGTOP_A <= a_f en /\ (a_f en + 256 <= 0x7fff8000 \/ 0x10007fff8000 <= a_f en)
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> a_f en + 256 <= p \/ p + n <= a_f en)
  /\ 2147450880 <= shad (a_f en) /\ shad (a_f en) + 32 <= 17594333495296 /\ (shad (a_f en)) mod 8 = 0.
Proof using AF AFP.
  intros en Σ m crem cur COM.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & _).
  assert (INF : In (a_f en, 2%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (X0 & X1 & X2 & X3). change (fs_size 2) with 256 in X1, X2, X3.
  pose proof (afp_frame_mem RT GOBJ AFP Σ m _ _ ART0 INF) as (Y1 & Y2). change (fs_size 2) with 256 in Y1, Y2.
  pose proof (af_frames_align RT AF Σ m _ _ ART0 INF) as [_ FSEG].
  split; [exact INF|]. split; [clear - X1 LOW; lia|]. split; [exact FSEG|]. split; [clear - Y1 F64; Z.div_mod_to_equations; lia|]. split; [exact X3|].
  unfold shad, SHB. clear - F0 F64 FTOP. unfold USTACK_TOP in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma w7_cur_facts : forall en Σ m crem cur e, w7_com en Σ m crem cur -> In e cur -> 0 < snd e ->
  In e (rt_live RT Σ) /\ 0 < fst e /\ fst e + snd e <= a_lo en /\ (snd e <= 64512 -> 0x10007fff8000 <= fst e)
  /\ (a_f en + 256 <= fst e \/ fst e + snd e <= a_f en) /\ (fst e + snd e <= 2147450880 \/ 17594333495296 <= fst e) /\ fst e + snd e <= 2 ^ 47.
Proof using AF AFP.
  intros en Σ m crem cur e COM He POS.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & _).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & _ & _). pose proof (CLV _ He) as INe. destruct e as [p n]. cbn [fst snd] in POS |- *.
  pose proof (af_live_range RT AF Σ m p n ART0 INe) as (Q0 & Q1 & Q2). pose proof (afp_live_mem RT GOBJ AFP Σ m p n ART0 INe ltac:(clear - POS; lia)) as (Q3 & Q4).
  destruct (w7_fframe_facts en Σ m crem cur COM) as (_ & _ & _ & _ & FR & _).
  split; [exact INe|]. split; [exact Q0|]. split; [clear - Q1 LOW; lia|]. split; [intros Hn; exact (afp_live_hi RT GOBJ AFP Σ m p n ART0 INe Hn)|].
  split; [exact (FR p n INe)|]. split; [exact Q3| exact Q4].
Qed.

(* [comment removed for export] *)
Lemma w7_perm : forall en Σ m crem cur cur', w7_com en Σ m crem cur -> Permutation cur cur' -> w7_com en Σ m crem cur'.
Proof.
  intros en Σ m crem cur cur' COM HP.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & REST0).
  pose proof (Permutation_map fst HP) as HPM.
  split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [exact GAP|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|].
  split; [exact HLOS|]. split; [exact CLE|]. split; [exact SEC|]. split; [exact LE|]. split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact RST|].
  split; [exact (Permutation_trans PERM (Permutation_app_tail _ HP))|].
  split; [intros e He; exact (CFR e (Permutation_in _ (Permutation_sym HP) He))|].
  split; [exact (Permutation_NoDup HPM ND)|]. split; [exact LPOS|]. split; [exact FRS|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact CLM|].
  split; [exact CR|]. split; [exact CR0|]. split; [exact CRE|]. split; [exact CGH|]. split; [exact CGS|]. split; [exact FPI|]. split; [exact RAF|].
  split; [rewrite <- (Permutation_length HP); exact CURL| exact REST0].
Qed.

(* [comment removed for export] *)
Lemma w7_credit : forall en Σ m crem crem' cur, w7_com en Σ m crem cur -> 0 <= crem' <= crem -> w7_com en Σ m crem' cur.
Proof.
  intros en Σ m crem crem' cur COM HC.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE & REST0).
  split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [exact GAP|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|].
  split; [exact HLOS|]. split; [exact CLE|]. split; [exact SEC|]. split; [exact LE|]. split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact RST|].
  split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|]. split; [exact FRS|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact CLM|].
  split; [clear - CR HC; lia|]. split; [clear - HC; lia|]. split; [exact CRE| exact REST0].
Qed.

(* [comment removed for export] *)
Lemma w7_call_pre : forall en Σ m crem cur site G,
  w7_com en Σ m crem cur -> In (site, e_fuzz_one_body) W7_SITES_OWN -> In (site, G) W7_CALLS_ALL -> 0 <= site < 2 ^ 64 ->
     bv_unsigned (wz (a_sp1 en)) = a_sp1 en
  /\ call_ok RT Σ m (wz (a_sp1 en)) (a_lo en)
  /\ cg_ctx (rt_cg RT Σ) G (bv_unsigned (wz site) :: [RA_FUZZ])
  /\ uw_chain m (wz (a_sp1 en)) (a_sp en) [RA_FUZZ]
  /\ incl_live (a_LBL en) (rt_live RT Σ)
  /\ (length (rt_frames RT Σ) = 1)%nat /\ crem <= rt_credit RT Σ
  /\ a_lo en <= a_sp1 en /\ a_sp1 en + 160 <= a_SP en /\ a_SP en + 16 <= USTACK_TOP /\ Z.of_nat (length (rt_live RT Σ)) + 32 <= LIVE_MAX.
Proof using AF AFP.
  intros en Σ m crem cur site G COM HS HC SR.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & _).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & CLL & DLV).
  assert (HLO : a_lo en <= a_sp1 en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  assert (EU : bv_unsigned (wz (a_sp1 en)) = a_sp1 en) by (apply unsigned_lit; clear - HLO HLOS TOP PD; unfold a_sp1, USTACK_TOP in *; lia).
  split; [exact EU|].
  split. { unfold call_ok. rewrite EU. split; [exact ST|]. split; [exact LOW|]. split; [clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia|].
           split; [clear - TOP PD; unfold a_sp1, USTACK_TOP in *; lia|]. clear - PDM PD. unfold a_sp1, a_SP in *. Z.div_mod_to_equations. lia. }
  assert (HS' : In (site, e_fuzz_one_body) (cg_site (rt_cg RT Σ))) by exact (proj1 CGH _ (proj1 CGS _ HS)).
  assert (HC' : In (site, G) (cg_call (rt_cg RT Σ))) by exact (proj2 CGH _ (proj2 CGS _ HC)).
  assert (HR' : In (RA_FUZZ, e_fuzz_one_body) (cg_call (rt_cg RT Σ))).
  { apply (proj2 CGH). apply (proj2 CGS). unfold W7_CALLS_ALL, W7_CALLS_X. apply in_or_app; right. left; reflexivity. }
  split. { rewrite (unsigned_lit site) by exact SR. split; [exact HC'|]. cbn [cg_linked]. split; [| exact I]. exists e_fuzz_one_body. split; [exact HS'| exact HR']. }
  split. { cbn [uw_chain]. rewrite EU. unfold a_sp1, a_SP in *. split; [clear - PD; lia|]. split; [exact TOP|]. exists (a_s0 en). split; [| exact FPI].
           unfold w7_savedl in SAVED.
           pose proof (rw_cells_skip m _ [C8 (a_s11 en); C8 (a_s10 en); C8 (a_s9 en); C8 (a_s8 en); C8 (a_s7 en); C8 (a_s6 en); C8 (a_s5 en); C8 (a_s4 en); C8 (a_s3 en); C8 (a_s2 en); C8 (a_s1 en)]
                                          [C8 (a_s0 en); C8 (a_ra en)] SAVED) as H.
           cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H. rewrite RAF in H.
           replace (bv_unsigned (a_sp en) + -104 + 88) with (bv_unsigned (a_sp en) - 16) in H by lia. exact H. }
  split; [intros e He; exact (CLL _ (INCL _ He))|].
  split; [rewrite FRS; reflexivity|]. split; [clear - CR CRE CR0; lia|].
  split; [exact HLO|]. split; [unfold a_sp1; clear - PD; lia|]. split; [exact TOP|].
  rewrite (Permutation_length PERM), length_app, Nat2Z.inj_add. clear - LIV CURL. unfold FUZZ_LIVE in *. lia.
Qed.

(* [comment removed for export] *)
Definition w7_segok (en : w7a) (iv : Z * Z) : Prop :=
  (a_lo en <= fst iv /\ snd iv <= a_sp1 en) \/ (a_SP en + -160 <= fst iv /\ snd iv <= a_SP en + -104) \/ (a_f en + 24 <= fst iv /\ snd iv <= a_f en + 248).

Lemma w7_seg_byte : forall en Σ m crem cur iv a, w7_com en Σ m crem cur -> w7_segok en iv -> fst iv <= a < snd iv ->
     aclient (rt_live RT Σ) (rt_frames RT Σ) (a_lo en) a /\ ~ client_static a /\ ~ (2147450880 <= a < 17594333495296)
  /\ (((a < a_sp1 en \/ a_SP en + -160 <= a < a_SP en + -104) /\ a_f en + 256 <= a) \/ a_f en + 24 <= a < a_f en + 248) /\ (forall p n, In (p, n) (rt_live RT Σ) -> ~ (p <= a < p + n))
  /\ ~ (shad (a_f en) <= a < shad (a_f en) + 32).
Proof using AF AFP.
  intros en Σ m crem cur iv a COM OK Ha.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & _).
  destruct (w7_fframe_facts en Σ m crem cur COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 INF) as [SHL SHF]. change (fs_size 2) with 256 in SHL, SHF.
  assert (HLO : a_lo en <= a_sp1 en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  assert (OK' : (a_lo en <= a < a_SP en + -104 /\ (a < a_sp1 en \/ a_SP en + -160 <= a < a_SP en + -104)) \/ a_f en + 24 <= a < a_f en + 248).
  { destruct OK as [[O1 O2]|[[O1 O2]|[O1 O2]]]; [left| left| right]; unfold a_sp1 in *; clear - Ha O1 O2 HLO PD; lia. }
  clear OK Ha. destruct OK' as [[R RR]|R].
  - split; [left; clear - R TOP; unfold USTACK_TOP in *; lia|].
    split; [intros CS; pose proof (client_static_range a CS); clear - H R HLOS; unfold SEGTOP_A in *; lia|].
    split; [clear - R HLOS; lia|]. split; [left; split; [exact RR| clear - R FLO; lia]|].
    split; [intros p n Hin Hp; pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & X & _); clear - X Hp R LOW; lia|].
    clear - R HLOS SH2. lia.
  - split; [do 3 right; left; exists (a_f en), 2%nat; split; [exact INF| change (fs_size 2) with 256; clear - R; lia]|].
    split; [intros CS; pose proof (client_static_range a CS); clear - H R FSEG; lia|].
    split; [clear - R FSHR; lia|]. split; [right; exact R|].
    split; [intros p n Hin Hp; destruct (FLV p n Hin); clear - H Hp R; lia|].
    destruct (SHF _ _ INF) as [X|X].
    + change (fs_size 2) with 256 in X. clear - X R. lia.
    + replace (a_f en + 256) with (a_f en + 64 * 4) in X by lia. rewrite (shad_add64 (a_f en) 4) in X by exact F64. clear - X R. lia.
Qed.

(* [comment removed for export] *)
Lemma w7_seg : forall en Σ (m m' : mem) crem cur W,
  w7_com en Σ m crem cur -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (a_lo en) (a_sp1 en) ->
  Forall (w7_segok en) W -> w7_com en Σ m' crem cur.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros en Σ m m' crem cur W COM MU WM MI' ST' HW.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & CLL & DLV).
  assert (AGo : forall (P : Z -> Prop), (forall x iv, P x -> In iv W -> ~ (fst iv <= x < snd iv)) -> agree_on P m m').
  { intros P HP a Ha. apply MU. apply outside_intro. intros iv Hiv. exact (HP _ _ Ha Hiv). }
  assert (BF : forall iv a, In iv W -> fst iv <= a < snd iv ->
       aclient (rt_live RT Σ) (rt_frames RT Σ) (a_lo en) a /\ ~ client_static a /\ ~ (2147450880 <= a < 17594333495296)
    /\ (((a < a_sp1 en \/ a_SP en + -160 <= a < a_SP en + -104) /\ a_f en + 256 <= a) \/ a_f en + 24 <= a < a_f en + 248) /\ (forall p n, In (p, n) (rt_live RT Σ) -> ~ (p <= a < p + n))
    /\ ~ (shad (a_f en) <= a < shad (a_f en) + 32)).
  { intros iv a Hiv Ha. exact (w7_seg_byte en Σ m crem cur iv a COM (proj1 (Forall_forall _ _) HW iv Hiv) Ha). }
  assert (AGS : forall (P : Z -> Prop), (forall x, P x -> client_static x) -> agree_on P m m').
  { intros P HP. apply AGo. intros x iv Hx Hiv R. exact (proj1 (proj2 (BF iv x Hiv R)) (HP _ Hx)). }
  split. { apply (af_frame RT AF Σ m m' (a_lo en) ART0 LOW); [| exact WM]. intros a NA. apply MU. apply outside_intro. intros iv Hiv R. exact (NA (proj1 (BF iv _ Hiv R))). }
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply stk_munch; [exact GAP| exact MU| exact WM|]. intros x Hx. apply outside_intro. intros iv Hiv R.
           destruct (proj1 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) as [[X _]|X]; [clear - Hx X; lia|].
           destruct (w7_fframe_facts en Σ m crem cur COM) as (_ & FLO & _). clear - Hx X FLO LOR PD. unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *. lia. }
  split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact HLOS|].
  split; [exact (cl_env_agree m m' _ _ CLE (AGS _ (fun x Hx => cl_cell_static _ Hx)))|].
  split; [exact (sec_off_agree m m' SEC (fun a Ea => AGS (fun x => x = SEC_INIT) (fun x Hx => ltac:(rewrite Hx; exact sec_init_static)) a Ea))|].
  split. { eapply libenv_agree; [exact LE|]. apply AGo. intros x iv Hx Hiv R. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
           - exact (proj1 (proj2 (BF iv x Hiv R)) CS).
           - exact (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (CLL _ (INCL _ Hin)) Hp). }
  split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|].
  split; [exact (REST_agree m m' RST (AGS _ (fun x Hx => proj1 (REST_fp_where _ Hx))))|].
  split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|]. split; [exact FRS|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact CLM|].
  split; [exact CR|]. split; [exact CR0|]. split; [exact CRE|]. split; [exact CGH|]. split; [exact CGS|]. split; [exact FPI|]. split; [exact RAF|]. split; [exact CURL|].
  split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|].
  split. { eapply rw_cells_agree; [exact FSH| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. unfold w7_shadow_live in Hx. cbn [cells_size csize Nat.add map length] in Hx.
           apply (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R)))))). clear - Hx. lia. }
  split. { destruct FSJ as [sjr FSJ']. exists sjr. eapply rw_cells_agree; [exact FSJ'| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
           apply (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R)))))). clear - Hx. lia. }
  split. { eapply rw_cells_agree; [exact FHD| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. unfold w7_fhdr in Hx. cbn [cells_size csize Nat.add] in Hx.
           destruct (proj1 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) as [[_ X]|X]; clear - Hx X; lia. }
  split. { eapply rw_cells_agree; [exact SAVED| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. unfold w7_savedl in Hx. cbn [cells_size csize Nat.add] in Hx.
           destruct (w7_fframe_facts en Σ m crem cur COM) as (_ & FLO & _).
           destruct (proj1 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) as [[X _]|X]; clear - Hx X FLO LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia. }
  split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply MU. apply outside_intro. intros iv Hiv R.
           destruct (BF iv _ Hiv R) as (_ & NS & _ & RG & NL & _). destruct Ha as [H|[H|[H|[H|H]]]].
           - destruct (w7_fframe_facts en Σ m crem cur COM) as (_ & FLO & _). destruct RG as [[X _]|X]; clear - H X FLO LOR FTOP PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia.
           - exact (NS H).
           - destruct H as (p & n & Hin & Hp). exact (NL p n (DLV _ Hin) Hp).
           - destruct H as (f & k & [] & _).
           - destruct H as (f & k & [] & _). }
  split. { eapply bytes_at_agree; [exact PAY|]. destruct PAYIN as [EBS|(p & n & Hin & P1 & P2)]; [intros x Hx; exfalso; rewrite EBS in Hx; cbn [length Z.of_nat] in Hx; clear - Hx; lia|].
           apply AGo. intros x iv Hx Hiv R. unfold a_len in P2.
           exact (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (DLV _ Hin) ltac:(clear - Hx P1 P2; lia)). }
  split; [exact PAYIN|]. split; [exact LEN|]. split; [exact FDO| exact MST].
Qed.

(* [comment removed for export] *)
Lemma w7_callk : forall en Σ Σ' (m m' : mem) crem crem' cur cur' KEEP W cost,
  w7_com en Σ m crem cur ->
  ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (a_lo en) (a_sp1 en) ->
  rt_pres_fp KEEP (rt_frames RT Σ) (a_sp1 en) W m m' ->
  cl_env m' (Z_to_bv 8 1) (a_canary en) -> sec_off m' -> libenv m' (a_LBL en) (a_E en) ->
  rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_cg RT Σ' = rt_cg RT Σ ->
  rt_credit RT Σ - cost <= rt_credit RT Σ' -> 0 <= crem' -> crem' + cost <= crem ->
  (forall e, In e (a_CL en ++ a_DRV en) -> In e KEEP) ->
  (forall a, client_static a -> outside LIB_W a -> outside W a) ->
  (forall a, a_sp1 en <= a < USTACK_TOP -> outside W a) ->
  (forall a, a_f en <= a < a_f en + 24 -> outside W a) -> (forall a, shad (a_f en) <= a < shad (a_f en) + 32 -> outside W a) ->
  (forall p n a, In (p, n) (a_DRV en) -> p <= a < p + n -> outside W a) ->
  Permutation (rt_live RT Σ') (cur' ++ a_CL en ++ a_DRV en) -> (forall e, In e cur' -> ~ In (fst e) (map fst (a_CL en ++ a_DRV en))) ->
  List.NoDup (map fst cur') -> (forall e, In e (rt_live RT Σ') -> 0 < snd e) -> Z.of_nat (length cur') + 32 <= FUZZ_LIVE ->
  w7_com en Σ' m' crem' cur'.
Proof using AF AFP REST_agree REST_fp_where.
  intros en Σ Σ' m m' crem crem' cur cur' KEEP W cost COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS1 SP1 CG1 CR1 CR0' CRM KP HWS HWU HWH HWF HWD PERM1 CFR1 ND1 LPOS1 CURL1.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & CLL & DLV).
  assert (INF : In (a_f en, 2%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (AGS : forall (P : Z -> Prop), (forall x, P x -> client_static x /\ outside LIB_W x /\ ~ cl_cell x) -> agree_on P m m').
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PR; [apply acl_static; exact X1| exact (HWS _ X1 X2)]. }
  split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
  split. { eapply stk_agree_nw; [exact GAP|]. intros a Ha. cbv beta in Ha. apply PR; [apply acl_stack| apply HWU]; unfold a_sp1 in *; clear - Ha PD TOP; unfold USTACK_TOP in *; lia. }
  split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|].
  split; [rewrite SP1; exact LOW|]. split; [exact LOR|]. split; [exact HLOS|]. split; [exact CLE1|]. split; [exact SEC1|]. split; [exact LE1|].
  split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|].
  split; [exact (REST_agree m m' RST (AGS _ REST_fp_where))|].
  split; [exact PERM1|]. split; [exact CFR1|]. split; [exact ND1|]. split; [exact LPOS1|].
  split; [rewrite FRS1; exact FRS|]. split; [rewrite SP1; exact SP0|]. split; [rewrite CG1; exact CG|]. split; [exact LIV|]. split; [exact CLM|].
  split; [clear - CR CR1 CRM CR0'; lia|]. split; [exact CR0'|]. split; [exact CRE|].
  split; [rewrite CG1; exact CGH|]. split; [exact CGS|]. split; [exact FPI|]. split; [exact RAF|]. split; [exact CURL1|].
  split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|].
  split. { eapply rw_cells_agree_nw; [exact FSH|]. intros a Ha. cbv beta in Ha. unfold w7_shadow_live in Ha. cbn [cells_size csize Nat.add map length] in Ha.
           apply PR; [| apply HWF; clear - Ha; lia]. apply (acl_fshadow _ _ _ (a_f en) 2%nat); [exact INF|]. change (fs_size 2) with (64 * 4). rewrite (shad_add64 (a_f en) 4 F64). clear - Ha; lia. }
  split. { destruct FSJ as [sjr FSJ']. exists sjr. eapply rw_cells_agree_nw; [exact FSJ'|]. intros a Ha. cbv beta in Ha. cbn [cells_size csize Nat.add] in Ha.
           apply PR; [| apply HWF; clear - Ha; lia]. apply (acl_fshadow _ _ _ (a_f en) 2%nat); [exact INF|]. change (fs_size 2) with (64 * 4). rewrite (shad_add64 (a_f en) 4 F64). clear - Ha; lia. }
  split. { eapply rw_cells_agree_nw; [exact FHD|]. intros a Ha. cbv beta in Ha. unfold w7_fhdr in Ha. cbn [cells_size csize Nat.add] in Ha.
           apply PR; [| exact (HWH _ Ha)]. apply (acl_frame _ _ _ (a_f en) 2%nat); [exact INF| change (fs_size 2) with 256; clear - Ha; lia]. }
  split. { eapply rw_cells_agree_nw; [exact SAVED|]. intros a Ha. cbv beta in Ha. unfold w7_savedl in Ha. cbn [cells_size csize Nat.add] in Ha.
           apply PR; [apply acl_stack| apply HWU]; unfold a_sp1; clear - Ha PD TOP; lia. }
  split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. destruct Ha as [H|[H|[H|[H|H]]]].
           - apply PR; [apply acl_stack| apply HWU]; unfold a_sp1; clear - H PD; lia.
           - apply PR; [apply acl_static; exact H| exact (HWS _ H Ho)].
           - destruct H as (p & n & Hin & Hp). apply PR; [apply (acl_live _ _ _ p n); [apply KP; apply in_or_app; right; exact Hin| exact Hp]| exact (HWD p n _ Hin Hp)].
           - destruct H as (f & k & [] & _).
           - destruct H as (f & k & [] & _). }
  split. { eapply bytes_at_agree; [exact PAY|]. destruct PAYIN as [EBS|(p & n & Hin & P1 & P2)]; [intros x Hx; exfalso; rewrite EBS in Hx; cbn [length Z.of_nat] in Hx; clear - Hx; lia|].
           unfold a_len in P2. intros a Ha.
           apply PR; [apply (acl_live _ _ _ p n); [apply KP; apply in_or_app; right; exact Hin| clear - Ha P1 P2; lia]| apply (HWD p n _ Hin); clear - Ha P1 P2; lia]. }
  split; [exact PAYIN|]. split; [exact LEN|]. split; [exact FDO| exact MST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma libW_range : forall a, in_ranges LIB_W a -> 0x5a9f20 <= a < 0xbc5698.
Proof.
  intros a (lo & hi & Hin & R). unfold LIB_W in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear - R; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma perm_live_apart : forall Σ (m : mem) x rest y, ART RT Σ m -> Permutation (rt_live RT Σ) (x :: rest) -> In y rest ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros Σ m x rest y ART0 P Hy.
  pose proof (Permutation_in x (Permutation_sym P) (or_introl eq_refl)) as INx. destruct (in_split _ _ INx) as (A & B & E).
  assert (Hy' : In y (A ++ B)).
  { apply (Permutation_in y (l := rest)); [| exact Hy]. apply (@Permutation_cons_app_inv _ rest A B x). rewrite <- E. apply Permutation_sym. exact P. }
  destruct x as [p1 n1], y as [p2 n2]. exact (af_live_disj RT AF Σ m p1 n1 p2 n2 A B ART0 E Hy').
Qed.

(* [comment removed for export] *)
Lemma w7_cd_apart : forall en Σ m crem cur x y, w7_com en Σ m crem cur -> In x (cur ++ a_CL en) -> In y (a_DRV en) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros en Σ m crem cur x y COM Hx Hy.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & _).
  destruct (in_split _ _ Hx) as (l1 & l2 & E).
  apply (perm_live_apart Σ m x (l1 ++ l2 ++ a_DRV en) y ART0).
  - eapply Permutation_trans; [exact PERM|]. rewrite (app_assoc cur (a_CL en) (a_DRV en)), E, <- (app_assoc l1 (x :: l2) (a_DRV en)). cbn [app].
    apply Permutation_sym. apply Permutation_middle.
  - apply in_or_app; right. apply in_or_app; right. exact Hy.
Qed.
(* [comment removed for export] *)
Lemma w7_cc_apart : forall en Σ m crem cur x y l1 l2, w7_com en Σ m crem cur -> cur = l1 ++ x :: l2 -> In y (l1 ++ l2) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros en Σ m crem cur x y l1 l2 COM E Hy.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & _).
  apply (perm_live_apart Σ m x (l1 ++ l2 ++ a_CL en ++ a_DRV en) y ART0).
  - eapply Permutation_trans; [exact PERM|]. rewrite E, <- (app_assoc l1 (x :: l2) (a_CL en ++ a_DRV en)). cbn [app]. apply Permutation_sym. apply Permutation_middle.
  - apply in_app_iff in Hy. apply in_or_app. destruct Hy as [Hy|Hy]; [left; exact Hy| right; apply in_or_app; left; exact Hy].
Qed.
(* [comment removed for export] *)
Lemma w7_cl_apart : forall en Σ m crem cur x y, w7_com en Σ m crem cur -> In x cur -> In y (a_CL en) ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros en Σ m crem cur x y COM Hx Hy.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & _).
  destruct (in_split _ _ Hx) as (l1 & l2 & E).
  apply (perm_live_apart Σ m x (l1 ++ l2 ++ a_CL en ++ a_DRV en) y ART0).
  - eapply Permutation_trans; [exact PERM|]. rewrite E, <- (app_assoc l1 (x :: l2) (a_CL en ++ a_DRV en)). cbn [app]. apply Permutation_sym. apply Permutation_middle.
  - apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hy.
Qed.

(* [comment removed for export] *)
Definition w7_winok (en : w7a) (cur : list (Z * Z)) (W : list (Z * Z)) : Prop :=
  forall a, ~ outside W a -> in_ranges LIB_W a \/ in_live (cur ++ a_CL en) a \/ (a_f en + 24 <= a < a_f en + 248).

Lemma w7_W_facts : forall en Σ m crem cur W, w7_com en Σ m crem cur -> w7_winok en cur W ->
     (forall a, client_static a -> outside LIB_W a -> outside W a)
  /\ (forall a, a_sp1 en <= a < USTACK_TOP -> outside W a)
  /\ (forall a, a_f en <= a < a_f en + 24 -> outside W a)
  /\ (forall a, shad (a_f en) <= a < shad (a_f en) + 32 -> outside W a)
  /\ (forall p n a, In (p, n) (a_DRV en) -> p <= a < p + n -> outside W a).
Proof using AF AFP.
  intros en Σ m crem cur W COM HWC.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & _).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & CLL & DLV).
  destruct (w7_fframe_facts en Σ m crem cur COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 INF) as [SHL SHF].
  assert (HLO : a_lo en <= a_sp1 en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  assert (CCL : forall e, In e (cur ++ a_CL en) -> In e (rt_live RT Σ)) by (intros e He; apply in_app_iff in He; destruct He as [He|He]; [exact (CLV _ He)| exact (CLL _ He)]).
  assert (GO : forall a, (in_ranges LIB_W a -> False) -> (forall p n, In (p, n) (rt_live RT Σ) -> p <= a < p + n -> False) -> ~ (a_f en + 24 <= a < a_f en + 248) -> outside W a).
  { intros a H1 H2 H3. destruct (outside_dec W a) as [O|NO]; [exact O|]. exfalso. destruct (HWC _ NO) as [R|[(p & n & Hin & Hp)|R]]; [exact (H1 R)| exact (H2 p n (CCL _ Hin) Hp)| exact (H3 R)]. }
  split. { intros a CS HO. pose proof (client_static_range a CS) as RA. apply GO.
    - intros R. destruct R as (lo & hi & Hin & Hlo). exact (outside_elim LIB_W a (lo, hi) HO Hin Hlo).
    - intros p n Hin Hp. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & _ & X). clear - X Hp RA. unfold SEGTOP_A in *. lia.
    - clear - RA FSEG. lia. }
  split. { intros a Ha. apply GO.
    - intros R. pose proof (libW_range a R). clear - H Ha HLO HLOS. lia.
    - intros p n Hin Hp. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & X & _). clear - X Hp Ha HLO LOW. lia.
    - clear - Ha FLO HLO. lia. }
  split. { intros a Ha. apply GO.
    - intros R. pose proof (libW_range a R). clear - H Ha FSEG. unfold SEGTOP_A in *. lia.
    - intros p n Hin Hp. destruct (FLV p n Hin); clear - H Hp Ha; lia.
    - clear - Ha. lia. }
  split. { intros a Ha. apply GO.
    - intros R. pose proof (libW_range a R). clear - H Ha SH1. lia.
    - intros p n Hin Hp. destruct (SHL p n Hin) as [X|X]; [clear - X Hp Ha; lia|].
      replace (a_f en + fs_size 2) with (a_f en + 64 * 4) in X by reflexivity. rewrite (shad_add64 (a_f en) 4 F64) in X. clear - X Hp Ha. lia.
    - destruct (SHF _ _ INF) as [X|X].
      + change (fs_size 2) with 256 in X. clear - X Ha. lia.
      + replace (a_f en + fs_size 2) with (a_f en + 64 * 4) in X by reflexivity. rewrite (shad_add64 (a_f en) 4 F64) in X. clear - X Ha. lia. }
  intros p n a Hin Ha. destruct (outside_dec W a) as [O|NO]; [exact O|]. exfalso.
  destruct (HWC _ NO) as [R|[(q & k & Hq & Hqa)|R]].
  - pose proof (libW_range a R). pose proof (af_live_range RT AF Σ m p n ART0 (DLV _ Hin)) as (_ & _ & X). clear - X H Ha. unfold SEGTOP_A in *. lia.
  - destruct (w7_cd_apart en Σ m crem cur (q, k) (p, n) COM Hq Hin) as [X|X]; cbn [fst snd] in X; clear - X Ha Hqa; lia.
  - destruct (FLV p n (DLV _ Hin)); clear - H R Ha; lia.
Qed.

(* [comment removed for export] *)
Lemma ff2_keep : forall (m m' : mem) f A cs KEEP fr sp W,
  rw_cells asegs m A cs -> rt_pres_fp KEEP fr sp W m m' -> In (f, 2%nat) fr -> f <= A -> A + Z.of_nat (cells_size cs) <= f + 248 ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
Proof.
  intros m m' f A cs KEEP fr sp W C PR INF H1 H2 HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha.
  apply PR; [apply (acl_frame _ _ _ f 2%nat); [exact INF| change (fs_size 2) with 256; lia]| exact (HO _ Ha)].
Qed.
(* [comment removed for export] *)
Lemma rest_keep : forall (m m' : mem) E KEEP fr sp W,
  errst_at_rest E [] m -> rt_pres_fp KEEP fr sp W m m' -> In (E, 904) KEEP -> (forall x, E <= x < E + 904 -> outside W x) -> errst_at_rest E [] m'.
Proof using errst_rest_agree errst_fp_where.
  intros m m' E KEEP fr sp W R PR INE HO. apply (errst_rest_agree m m' _ _ R). intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [X | (p & n & [] & _)]. apply PR; [exact (acl_live _ _ _ E 904 _ INE X)| exact (HO _ X)].
Qed.
Lemma elive_keep : forall (m m' : mem) E top bot strs KEEP fr sp W,
  errst_live E top bot strs m -> rt_pres_fp KEEP fr sp W m m' -> In (E, 904) KEEP -> (forall e, In e strs -> In e KEEP) ->
  (forall x, E <= x < E + 904 -> outside W x) -> (forall e x, In e strs -> fst e <= x < fst e + snd e -> outside W x) -> errst_live E top bot strs m'.
Proof using errst_live_agree errst_fp_where.
  intros m m' E top bot strs KEEP fr sp W L PR INE INS HOE HOS. apply (errst_live_agree m m' _ _ _ _ L). intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [X | (p & n & Hin & Hp)].
  - apply PR; [exact (acl_live _ _ _ E 904 _ INE X)| exact (HOE _ X)].
  - apply PR; [exact (acl_live _ _ _ p n _ (INS _ Hin) Hp)| exact (HOS (p, n) _ Hin Hp)].
Qed.

(* [comment removed for export] *)
Lemma w7_out_libW : forall en Σ m crem cur x, w7_com en Σ m crem cur ->
  ((exists p n, In (p, n) cur /\ p <= x < p + n) \/ (a_f en <= x < a_f en + 248) \/ (a_sp1 en <= x < USTACK_TOP) \/ (a_E en <= x < a_E en + 904)) -> outside (lib_W (a_LBL en)) x.
Proof using AF AFP.
  intros en Σ m crem cur x COM Hx.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & _).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & CLL & DLV).
  destruct (w7_fframe_facts en Σ m crem cur COM) as (INF & FLO & FSEG & FSHR & FLV & _).
  assert (HLO : a_lo en <= a_sp1 en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  unfold lib_W. apply outside_app_intro.
  - apply outside_intro. intros [lo hi] Hiv R. cbn [fst snd] in R. pose proof (libW_range x (ex_intro _ lo (ex_intro _ hi (conj Hiv R)))) as LR.
    destruct Hx as [(p & n & Hin & Hp)|[H|[H|H]]].
    + pose proof (af_live_range RT AF Σ m p n ART0 (CLV _ Hin)) as (_ & _ & Y). clear - Y Hp LR. unfold SEGTOP_A in *. lia.
    + clear - H LR FSEG. unfold SEGTOP_A in *. lia.
    + clear - H LR HLO HLOS. lia.
    + pose proof (af_live_range RT AF Σ m (a_E en) 904 ART0 (CLL _ INE)) as (_ & _ & Y). clear - Y H LR. unfold SEGTOP_A in *. lia.
  - apply outside_intro. intros iv Hiv R. apply in_map_iff in Hiv. destruct Hiv as ([q k] & <- & Hqk). cbn [fst snd] in R.
    destruct Hx as [(p & n & Hin & Hp)|[H|[H|H]]].
    + destruct (w7_cl_apart en Σ m crem cur (p, n) (q, k) COM Hin (INCL _ Hqk)) as [Q|Q]; cbn [fst snd] in Q; clear - Q Hp R; lia.
    + destruct (FLV q k (CLL _ (INCL _ Hqk))) as [Q|Q]; clear - Q H R; lia.
    + pose proof (af_live_range RT AF Σ m q k ART0 (CLL _ (INCL _ Hqk))) as (_ & Y & _). clear - Y H R HLO LOW. lia.
    + assert (NE : (a_E en, 904) <> (q, k)) by (intros E; apply NLE; rewrite E; exact Hqk).
      destruct (live_ne_apart RT AF Σ m (a_E en) 904 q k ART0 (CLL _ INE) (CLL _ (INCL _ Hqk)) NE) as [Q|Q]; clear - Q H R; lia.
Qed.
Lemma w7_out_E : forall en Σ m crem cur x, w7_com en Σ m crem cur ->
  ((exists p n, In (p, n) cur /\ p <= x < p + n) \/ (a_f en <= x < a_f en + 248) \/ (a_sp1 en <= x < USTACK_TOP)) -> ~ (a_E en <= x < a_E en + 904).
Proof using AF AFP.
  intros en Σ m crem cur x COM Hx R.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & _).
  destruct (w7_lists en Σ m crem cur COM) as (CLV & CLL & DLV).
  destruct (w7_fframe_facts en Σ m crem cur COM) as (INF & FLO & FSEG & FSHR & FLV & _).
  assert (HLO : a_lo en <= a_sp1 en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  destruct Hx as [(p & n & Hin & Hp)|[H|H]].
  - destruct (w7_cl_apart en Σ m crem cur (p, n) (a_E en, 904) COM Hin INE) as [Q|Q]; cbn [fst snd] in Q; clear - Q Hp R; lia.
  - destruct (FLV (a_E en) 904 (CLL _ INE)) as [Q|Q]; clear - Q H R; lia.
  - pose proof (af_live_range RT AF Σ m (a_E en) 904 ART0 (CLL _ INE)) as (_ & Y & _). clear - Y H R HLO LOW. lia.
Qed.
(* [comment removed for export] *)
Lemma w7_cells_keep : forall (m m' : mem) p n A cs KEEP fr sp W,
  rw_cells asegs m A cs -> rt_pres_fp KEEP fr sp W m m' -> In (p, n) KEEP -> p <= A -> A + Z.of_nat (cells_size cs) <= p + n ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
Proof.
  intros m m' p n A cs KEEP fr sp W C PR INK H1 H2 HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbv beta in Ha.
  apply PR; [apply (acl_live _ _ _ p n); [exact INK| lia]| exact (HO _ Ha)].
Qed.
End W7I.
