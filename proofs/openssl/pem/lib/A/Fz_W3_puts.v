(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_M_malloc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux4 Fz_W3_ngets Fz_W3_hdg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Definition SITE_pu_puts : Z := 0x30c730.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pu_a_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (e tmp LB2 : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> (e = 0 \/ e = 1) -> s2 = wz tmp -> s11 = wz LB2 -> mem_inv asegs m -> rw_cells asegs m (sp1 + 104) [C8 (wz e)] ->
  evt asegs (fun ms => exists a0',
      ms = (if e =? 0 then MS (mkR (wz SITE_pu_puts) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz tmp) (wz LB2) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_PUTS) fc None m (seg_rom asegs)
            else MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0' a1 a2 a3 a4 a5 a6 a7 (wz 907) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE2) fc None m (seg_rom asegs)))
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_PUTS) fc None m (seg_rom asegs)).
Proof.
  intros until LB2. intros SP0 SPH HE -> -> MI FR104. unfold J_PUTS, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  destruct HE as [-> | ->].
  - zstep. zstep. th_if_lit. zstep. zstep. zstep. unfold SITE_pu_puts, FZ_BIO_PUTS. cbn [Z.eqb]. apply evt_done. exists (Z_to_bv 64 0). reflexivity.
  - zstep. zstep. th_if_lit. zstep. unfold J_RAISE2. cbn [Z.eqb Pos.eqb]. apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pu_b_post (sp1 : Z) (gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (got len' : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    munch [(sp1 + 104, sp1 + 112)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    ((got = 2 /\ 65 < len' /\ m' = m /\
      ms = MS (mkR ra' (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_FREE2) fc None m' (seg_rom asegs))
     \/ ((got <> 2 \/ len' <= 65) /\ rw_cells asegs m' (sp1 + 104) [C8 (wz (if got =? 2 then (if len' =? 65 then 0 else 1) else 0))] /\
      ms = MS (mkR ra' (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_GETS1) fc None m' (seg_rom asegs))).
Lemma pu_b_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (n got len' : Z) (ev : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= n <= 255 -> 0 <= got <= 2 -> 1 <= len' <= 255 -> mem_inv asegs m -> rw_cells asegs m (sp1 + 104) [C8 ev] ->
  evt asegs (pu_b_post sp1 gp s0 s2 (wz len') s4 s5 (wz got) s7 s8 s9 s10 s11 F fc got len' m)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz n) a1 a2 a3 a4 a5 a6 a7 s2 (wz len') s4 s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_pu_puts) fc None m (seg_rom asegs)).
Proof.
  intros until ev. intros SP0 SPH HN GOT LEN MI FR104. unfold SITE_pu_puts, TP_A in *.
  pose proof (munch_refl [(sp1 + 104, sp1 + 112)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 got) = got) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 len') = len') by (apply unsigned_lit; lia).
  zstep.
  replace (bv_lts (Z_to_bv 64 n) Startup_glue.z64) with false by (unfold bv_lts; change Startup_glue.z64 with (Z_to_bv 64 0); rewrite !SFModel.signed_of_Z by lia; symmetry; apply Z.ltb_ge; lia). cbv iota.
  zstep. zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *) zstep; lfix. unfold pu_b_post, J_GETS1. apply evt_done. do 17 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    right. replace (got =? 2) with false by (symmetry; apply Z.eqb_neq; lia). split; [left; lia|]. split; [eassumption| reflexivity].
  - (* [comment removed for export] *) zstep. zstep.
    replace (bv_lts (Z_to_bv 64 65) (Z_to_bv 64 len')) with (65 <? len') by (unfold bv_lts; rewrite !SFModel.signed_of_Z by lia; reflexivity).
    destruct (Z.ltb_spec 65 len') as [GT|LE].
    + unfold pu_b_post, J_FREE2. apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. left. split; [lia|]. split; [exact GT|]. split; reflexivity.
    + zstep. zstep. zstep; lfix. zstep. unfold pu_b_post, J_GETS1. apply evt_done. do 17 eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. replace (got =? 2) with true by (symmetry; apply Z.eqb_eq; lia). split; [right; exact LE|]. split; [| reflexivity].
      lazymatch goal with H : rw_cells asegs _ (sp1 + 104) [C8 (Z_to_bv 64 (Z.b2z ?X))] |- _ =>
        replace (Z.b2z X) with (if len' =? 65 then 0 else 1) in H; [exact H|] end.
      change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. destruct (Z.eqb_spec len' 65) as [->|NE]; [reflexivity|].
      rewrite <- (Z.mod_unique (len' + -65) (2 ^ 64) (-1) (len' + -65 + 2 ^ 64)) by lia. replace (0 <? len' + -65 + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gr_n_mono : forall a b, 0 <= a <= b -> gr_n a <= gr_n b.
Proof. intros a b H. unfold gr_n. Z.div_mod_to_equations. lia. Qed.
Lemma mcost_bnd : forall n, 0 <= n -> 0 <= mcost n <= 2 * n + 16384.
Proof. intros n Hn. unfold mcost. destruct (n <=? 64512); lia. Qed.

(* [comment removed for export] *)
Lemma puts_cost_fits : forall RT (en : pem_entry RT) off lenT lenO maxT maxO n crem,
  e_boff RT en <= off <= e_blen RT en -> 0 <= lenT -> 0 <= lenO -> lenT + lenO <= 2 * (off - e_boff RT en) ->
  maxT <= gr_n (lenT + 255) -> maxO <= gr_n (lenO + 255) -> 0 <= n <= 256 ->
  C_END + 8 + 2 * (e_blen RT en - off) + grow_pot RT en maxT maxO <= crem -> puts_cost lenT n maxT <= crem.
Proof.
  intros RT en off lenT lenO maxT maxO n crem HO HX HY HS MX MY HN REM.
  pose proof (mcost_bnd (gr_n (lenT + n)) ltac:(unfold gr_n; Z.div_mod_to_equations; lia)) as MC.
  assert (PC : puts_cost lenT n maxT <= 1 + mcost (gr_n (lenT + n))) by (unfold puts_cost; destruct (maxT <? lenT + n); clear - MC; lia).
  unfold grow_pot, grow_cap, e_plen, C_END in REM. unfold gr_n in *. clear - HO HX HY HS MX MY HN REM MC PC. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma puts_cost_after : forall RT (en : pem_entry RT) off lenT maxT maxT' maxO n crem,
  0 <= lenT -> 0 <= n -> (maxT' = maxT \/ (maxT < lenT + n /\ maxT' = gr_n (lenT + n))) -> lenT + n <= maxT' ->
  C_END + 8 + 2 * (e_blen RT en - off) + grow_pot RT en maxT maxO <= crem ->
  C_END + 8 + 2 * (e_blen RT en - off) + grow_pot RT en maxT' maxO + (-1) <= crem - puts_cost lenT n maxT.
Proof.
  intros RT en off lenT maxT maxT' maxO n crem HX HN HM HL REM.
  unfold puts_cost. destruct HM as [-> | [GR ->]].
  - replace (maxT <? lenT + n) with false by (symmetry; apply Z.ltb_ge; lia). clear - REM. lia.
  - replace (maxT <? lenT + n) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold grow_pot in *. unfold mcost. destruct (Z.leb_spec (gr_n (lenT + n)) 64512) as [LG|LG]; unfold gr_n in *; clear - HX HN GR HL REM LG; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma puts_size_fits : forall RT (en : pem_entry RT) off len len' lenT lenO n,
  0 <= e_boff RT en -> off <= e_blen RT en -> e_blen RT en < 2 ^ 26 -> 0 <= lenO -> 1 <= len -> len' <= len + 1 -> 0 <= n <= len' ->
  254 * (lenT + lenO) <= 255 * (off - len - e_boff RT en) -> gr_n (lenT + n) <= 2 ^ 27.
Proof. intros RT en off len len' lenT lenO n B0 OH BLT HY HL HL1 HN INVW. unfold gr_n. clear - B0 OH BLT HY HL HL1 HN INVW. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma puts_budget_after : forall RT (en : pem_entry RT) off len len' lenT lenO n,
  e_boff RT en <= off <= e_blen RT en -> 1 <= len <= 254 -> len' <= len + 1 -> (len < 254 -> off < e_blen RT en -> len' <= len) -> 0 <= n <= len' ->
  254 * (lenT + lenO) <= 255 * (off - len - e_boff RT en) ->
  254 * (lenT + n + lenO) <= 255 * (off - e_boff RT en) + (if off =? e_blen RT en then 254 else 0).
Proof.
  intros RT en off len len' lenT lenO n HO HL HL1 HL2 HN INVW.
  destruct (Z.eqb_spec off (e_blen RT en)) as [E|NE]; [clear HL2; lia|].
  destruct (Z_lt_le_dec len 254) as [LT|GE]; [pose proof (HL2 LT ltac:(lia)); lia| lia].
Qed.

Section CPuts.
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
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_BP : bio_puts_stmt RT FZ_SITES FZ_CALLS.
Hypothesis H_R2 : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_F2 : FREE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).
Local Notation hd_keepI := (hd_keepW RT AF GOBJ AFP libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).
Local Notation rest_keepI := (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).
Local Notation stk_winI := (stk_win_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS).

(* [comment removed for export] *)
Lemma first_nul : forall (bs : list byte) len', nth_error bs (Z.to_nat len') = Some (Z_to_bv 8 0) -> 0 <= len' ->
  exists n, 0 <= n <= len' /\ nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0) /\ (forall i, (i < Z.to_nat n)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)).
Proof.
  intros bs len' NUL L0. destruct (first_nul_split (Z_to_bv 8 0) bs (nth_error_In _ _ NUL)) as (a & b & E & NA).
  exists (Z.of_nat (length a)). assert (NA' : forall i, (i < length a)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)).
  { intros i Hi X. rewrite E, nth_error_app1 in X by exact Hi. exact (NA (nth_error_In _ _ X)). }
  split; [| split; [rewrite Nat2Z.id, E, nth_error_app2, Nat.sub_diag by lia; reflexivity| rewrite Nat2Z.id; exact NA']].
  split; [lia|]. destruct (Z_lt_le_dec len' (Z.of_nat (length a))) as [LT|GE]; [| exact GE]. exfalso. exact (NA' (Z.to_nat len') ltac:(lia) NUL).
Qed.

Lemma mbio_ent_len5 : forall K max, Z.of_nat (length (mbio_ent K max)) <= 5 /\ 4 <= Z.of_nat (length (mbio_ent K max)).
Proof. intros K max. unfold mbio_ent. rewrite length_app. destruct (k_d K); cbn; lia. Qed.

(* [comment removed for export] *)
Lemma puts_core : forall T (en : pem_entry) Σ (m : mem) off crem lrem j0 x1 x2 gap hj lenv j1 tav j2 bmv j3 (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) c (LB2 namev nn hBv dBv tmp len len' got prev partial : Z) (bn bs : list byte)
    (KT KO : mbk) (ov methT methO lenT maxT lenO maxO : Z),
  let rest := mbio_ent KO maxO ++ [(LB2, 256); (namev, nn)] in
  pem_com en Σ m off crem lrem (mbio_ent KT maxT ++ rest) ->
  errst_at_rest (e_E RT en) [] m -> pem_frame en m j0 (loc_H LB2 tmp) (loc_F RT en) (wz 0) hBv dBv x1 x2 gap ->
  rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m ->
  LB2 mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB2 [CB 256 bs] -> 1 <= nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] ->
  mbio_rep (rt_live RT Σ) m KT tmp methT lenT maxT 0 -> mbio_rep (rt_live RT Σ) m KO ov methO lenO maxO 0 ->
  C_END + 8 + 2 * (e_blen RT en - off) + grow_pot RT en maxT maxO <= crem ->
  (9 <= lrem /\ 19 <= lrem + Z.of_nat (length (mbio_ent KT maxT)) + Z.of_nat (length (mbio_ent KO maxO))) ->
  1 <= len' <= 255 -> nth_error bs (Z.to_nat len') = Some (Z_to_bv 8 0) ->
  1 <= len <= 254 -> len' <= len + 1 -> (len < 254 -> off < e_blen RT en -> len' <= len) -> 254 * (lenT + lenO) <= 255 * (off - len - e_boff RT en) ->
  lenT + lenO <= 2 * (off - e_boff RT en) -> maxT <= gr_n (lenT + 255) -> maxO <= gr_n (lenO + 255) -> 0 <= got <= 2 ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_PUTS m F fc (wz SITE_pu_puts) t0 t1 t2 (wz tmp) (wz LB2) a2 a3 a4 a5 a6 a7 (wz tmp) (wz len') (wz prev) s5 (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (n : Z) (pd' : option Z) (maxT' e' : Z),
     pem_com en Σ' m' off (crem - puts_cost lenT n maxT) (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) (mbio_ent (mbk_data KT pd') maxT' ++ rest) -> rt_frames RT Σ' = rt_frames RT Σ ->
     (9 <= (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) /\ 19 <= (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) + Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT')) + Z.of_nat (length (mbio_ent KO maxO))) ->
     errst_at_rest (e_E RT en) [] m' -> pem_frame en m' j0 (loc_H LB2 tmp) (loc_F RT en) (wz e') hBv dBv x1 x2 gap ->
     rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m' ->
     rw_cells asegs m' LB2 [CB 256 bs] -> rw_cells asegs m' namev [CB (Z.to_nat nn) bn] ->
     mbio_rep (rt_live RT Σ') m' (mbk_data KT pd') tmp methT (lenT + n) maxT' 0 -> mbio_rep (rt_live RT Σ') m' KO ov methO lenO maxO 0 ->
     0 <= n <= len' -> (e' = 0 \/ e' = 1) -> (got <> 2 -> e' = 0) ->
     C_END + 8 + 2 * (e_blen RT en - off) + grow_pot RT en maxT' maxO + (-1) <= crem - puts_cost lenT n maxT ->
     254 * (lenT + n + lenO) <= 255 * (off - e_boff RT en) + (if off =? e_blen RT en then 254 else 0) ->
     lenT + n + lenO <= 2 * (off - e_boff RT en) -> maxT' <= gr_n (lenT + n + 255) ->
     ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en J_GETS1 m' F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 (wz tmp) (wz len') (wz prev) s5 (wz got) (wz partial) (wz namev) (wz LB2) y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (n : Z) (pd' : option Z) (maxT' : Z),
     got = 2 -> 65 < len' ->
     pem_com en Σ' m' off (crem - puts_cost lenT n maxT) (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) (mbio_ent (mbk_data KT pd') maxT' ++ rest) -> rt_frames RT Σ' = rt_frames RT Σ ->
     9 <= (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) ->
     errst_at_rest (e_E RT en) [] m' -> pem_frame en m' j0 (loc_H LB2 tmp) (loc_F RT en) (wz 0) hBv dBv x1 x2 gap ->
     rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m' ->
     rw_cells asegs m' LB2 [CB 256 bs] -> rw_cells asegs m' namev [CB (Z.to_nat nn) bn] ->
     mbio_rep (rt_live RT Σ') m' (mbk_data KT pd') tmp methT (lenT + n) maxT' 0 -> mbio_rep (rt_live RT Σ') m' KO ov methO lenO maxO 0 ->
     C_END + 1 <= crem - puts_cost lenT n maxT ->
     ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en J_FREE2 m' F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 (wz tmp) (wz len') (wz prev) s5 (wz got) (wz partial) (wz namev) (wz LB2) y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros T en Σ m off crem lrem j0 x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 c LB2 namev nn hBv dBv tmp len len' got prev partial bn bs
         KT KO ov methT methO lenT maxT lenO maxO.
  cbv zeta. intros COM REST PFR FFC ON AL16 LBS LBC NN NBC MBT MBO REM LRM LEN' NUL LEN LEN1 LEN2 INVW LSUM MXB MYB GOT Hc KG KF.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLB : In (LB2, 256) (mbio_ent KO maxO ++ [(LB2, 256); (namev, nn)])) by (apply in_or_app; right; left; reflexivity).
  assert (HNB : In (namev, nn) (mbio_ent KO maxO ++ [(LB2, 256); (namev, nn)])) by (apply in_or_app; right; right; left; reflexivity).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBT) as (LX & _). pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBO) as (LY & _).
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite !map_app, !mbio_ent_fst in ND'. cbn [map fst app] in ND'. rewrite <- !app_assoc in ND'. cbn [app] in ND'.
  pose proof (nd_split _ _ ND') as (NDX & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDY & ND3 & DJY).
  apply List.NoDup_cons_iff in ND3. destruct ND3 as [NQL ND4]. apply List.NoDup_cons_iff in ND4. destruct ND4 as [NQN ND5]. apply List.NoDup_cons_iff in ND5. destruct ND5 as [NQE _].
  assert (NLT : ~ In (LB2, 256) (mbio_ent KT maxT)).
  { intros X. pose proof (in_map fst _ _ X) as H1. rewrite mbio_ent_fst in H1. apply (DJX _ H1). apply in_or_app; right; left; reflexivity. }
  assert (NNT : ~ In (namev, nn) (mbio_ent KT maxT)).
  { intros X. pose proof (in_map fst _ _ X) as H1. rewrite mbio_ent_fst in H1. apply (DJX _ H1). apply in_or_app; right; right; left; reflexivity. }
  assert (NET : ~ In (e_E RT en, 904) (mbio_ent KT maxT)).
  { intros X. pose proof (in_map fst _ _ X) as H1. rewrite mbio_ent_fst in H1. apply (DJX _ H1). apply in_or_app; right; right; right; left; reflexivity. }
  assert (NOT : forall e, In e (mbio_ent KO maxO) -> ~ In e (mbio_ent KT maxT)).
  { intros e He X. pose proof (in_map fst _ _ X) as H1. rewrite mbio_ent_fst in H1. apply (DJX _ H1). apply in_or_app; left. pose proof (in_map fst _ _ He) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  (* [comment removed for export] *)
  destruct (first_nul bs len' NUL ltac:(clear - LEN'; lia)) as (n & HN & NULn & NNUL).
  pose proof (puts_size_fits RT en off len len' lenT lenO n (proj1 BLT) (proj2 OFF) (proj2 BLT) ltac:(clear - LY; lia) ltac:(clear - LEN; lia) LEN1 HN INVW) as SZ.
  pose proof (puts_cost_fits RT en off lenT lenO maxT maxO n crem OFF ltac:(clear - LX; lia) ltac:(clear - LY; lia) LSUM MXB MYB ltac:(clear - HN LEN'; lia) REM) as CF.
  eapply (pem_call_bputs RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BP T en Σ m off crem lrem _ KT tmp methT lenT maxT LB2 n bs SITE_pu_puts
            F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 (wz tmp) (wz len') (wz prev) s5 (wz got) (wz partial) (wz namev) (wz LB2) t3 t4 t5 t6 c
            COM MBT SZ HLB AL16 LBS LBC ltac:(clear - HN LEN'; lia) NULn NNUL CF ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_puts, SITE_pu_puts; left; reflexivity) Hc).
  clear Hc. intros Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' pd' maxT' COM' FRS' PR WOK KP MB' HMAX HLEN Hc'.
  pose proof COM' as (ART1 & MI1 & ST1 & _).
  assert (LR9 : 9 <= (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) /\ 19 <= (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) + Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT')) + Z.of_nat (length (mbio_ent KO maxO))).
  { pose proof (mbio_ent_len5 (mbk_data KT pd') maxT') as L1. pose proof (mbio_ent_len5 KO maxO) as L2. pose proof (mbio_ent_len5 KT maxT) as L3. clear - LRM L1 L2 L3. lia. }
  set (KEEP := match k_d KT with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) in *.
  set (W := (G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W KT maxT) in *.
  pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  destruct (hd_keepI en Σ m m' off crem lrem _ KEEP _ W j0 (loc_H LB2 tmp) (wz 0) x1 x2 gap hj lenv j1 tav j2 bmv j3 hBv dBv namev nn bn COM WOK PR
              (proj1 (KP _ ltac:(apply in_or_app; right; exact INE))) (proj1 (KP _ ltac:(apply in_or_app; left; exact HNB))) NET ltac:(apply in_or_app; right; exact HNB) NNT NN REST PFR FFC ON NBC)
    as (REST' & PFR' & FFC' & ON' & NBC').
  assert (LBC' : rw_cells asegs m' LB2 [CB 256 bs]).
  { eapply (cells_keep m m' LB2 256); [exact LBC| exact PR| exact (proj1 (KP _ ltac:(apply in_or_app; left; exact HLB)))| clear; lia| cbn [cells_size csize]; clear; lia|].
    cbn [cells_size csize]. intros x Hx. apply (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL (LB2, 256) x ltac:(apply in_or_app; right; exact HLB) NLT). cbn [fst snd]. clear - Hx. lia. }
  assert (MBO' : mbio_rep (rt_live RT Σ') m' KO ov methO lenO maxO 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBO| exact PR| intros e He; exact (KP _ ltac:(apply in_or_app; left; apply in_or_app; left; exact He))|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ W COM HWL e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NOT _ He) Hx). }
  clear REST PFR FFC ON NBC LBC MBO MBT PR WOK HWS HWFR HWFF HWF HWL HWP.
  pose proof PFR' as (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE & FR224 & FRG).
  pose proof (puts_cost_after RT en off lenT maxT maxT' maxO n crem ltac:(clear - LX; lia) ltac:(clear - HN; lia) HMAX HLEN REM) as CA.
  pose proof (puts_budget_after RT en off len len' lenT lenO n OFF LEN LEN1 LEN2 HN INVW) as BA.
  assert (LSUM' : lenT + n + lenO <= 2 * (off - e_boff RT en)) by (clear - INVW LSUM HN LEN LEN1 OFF; lia).
  assert (MXB' : maxT' <= gr_n (lenT + n + 255)).
  { destruct HMAX as [-> | [_ ->]]; [eapply Z.le_trans; [exact MXB| apply gr_n_mono; clear - LX HN; lia]| apply gr_n_mono; clear - LX HN; lia]. }
  (* [comment removed for export] *)
  pose proof (pu_b_walk (wz SITE_pu_puts) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) b1 b2 b3 b4 b5 b6 b7 (wz tmp) (wz prev) s5 (wz partial) (wz (shad (e_f RT en))) (wz SHB)
                (wz namev) (wz LB2) y3 y4 y5 y6 F' fc' m' n got len' (wz 0) SP0' SPH ltac:(clear - HN LEN'; lia) GOT LEN' MI1 FR104) as Wb.
  cl_lift Wb Hc' c2 Hc2.
  destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (ra' & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m2 & MU2 & WM2 & MI2 & ARMS) & Hc2'). clear Hc2 Hc'.
  destruct ARMS as [(G2 & L65 & -> & ->) | (GL & FR104' & ->)].
  - (* [comment removed for export] *)
    refine (KF Σ' m' F' fc' ra' w0 w1 w2 g0 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c2 n pd' maxT' G2 L65 COM' FRS' (proj1 LR9) REST' PFR' FFC' ON' LBC' NBC' MB' MBO' _ Hc2').
    pose proof (grow_pot_nonneg RT en (lenT + n) lenO maxT' maxO off OFF ltac:(clear - LX HN; lia) ltac:(clear - LY; lia) LSUM' MXB' MYB) as GP. clear - CA GP OFF. unfold C_END in *. lia.
  - (* [comment removed for export] *)
    set (W2 := [(e_sp1 RT en + 104, e_sp1 RT en + 112)]) in *.
    assert (HW2 : forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W2 x) by (intros x Hx; subst W2; cbn; unfold e_sp1 in *; clear - Hx PD; lia).
    destruct (stk_winI en Σ' m' off (crem - puts_cost lenT n maxT) _ _ W2 COM' HW2) as (W2L & W2F & W2O).
    assert (KPa : forall A cs, rw_cells asegs m' A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W2 x) -> rw_cells asegs m2 A cs).
    { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU2. exact (HO _ Ha). }
    assert (PR2 : rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ') (e_sp1 RT en) W2 m' m2) by (intros a _ Ho; exact (MU2 a Ho)).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ' m' off _ _ _ COM') as [ELV' CLV'].
    assert (ST2 : stk asegs m2 (e_lo RT en) (e_sp1 RT en)).
    { eapply stk_munch; [exact ST1| exact MU2| exact WM2|]. intros x Hx. apply HW2. left. clear - Hx. lia. }
    assert (COM2 : pem_com en Σ' m2 off (crem - puts_cost lenT n maxT) (lrem + Z.of_nat (length (mbio_ent KT maxT)) - Z.of_nat (length (mbio_ent (mbk_data KT pd') maxT'))) (mbio_ent (mbk_data KT pd') maxT' ++ mbio_ent KO maxO ++ [(LB2, 256); (namev, nn)])).
    { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ' m' m2); [exact COM'| exact MU2| exact WM2| exact MI2| exact ST2|].
      subst W2. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold e_sp1 in *. clear - PD. lia. }
    assert (REST2 : errst_at_rest (e_E RT en) [] m2).
    { eapply (rest_keepI en Σ' m' m2); [exact COM'| exact REST'| exact PR2| exact (ELV' _ INE)| intros x Hx; exact (W2L _ _ x (ELV' _ INE) Hx)]. }
    assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
    { apply (KPa _ _ FFC'). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W2F. clear - Hx. lia. }
    assert (ON2 : out_null RT en m2).
    { destruct ON' as (O1 & O2 & O3 & O4).
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m' P [C8 vv] -> rw_cells asegs m2 P [C8 vv]).
      { intros P vv HPP C. apply (KPa _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W2O P x HPP). clear - Hx. lia. }
      split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|].
      split; [apply G8; [do 2 right; left; reflexivity| exact O3]|]. apply G8; [do 3 right; left; reflexivity| exact O4]. }
    assert (MBT2 : mbio_rep (rt_live RT Σ') m2 (mbk_data KT pd') tmp methT (lenT + n) maxT' 0).
    { eapply (mbio_rep_keep (rt_live RT Σ')); [exact MB'| exact PR2| intros e He; split; apply CLV'; apply in_or_app; left; exact He|].
      intros [p k] x He Hx. exact (W2L p k x (CLV' _ ltac:(apply in_or_app; left; exact He)) Hx). }
    assert (MBO2 : mbio_rep (rt_live RT Σ') m2 KO ov methO lenO maxO 0).
    { eapply (mbio_rep_keep (rt_live RT Σ')); [exact MBO'| exact PR2| intros e He; split; apply CLV'; apply in_or_app; right; apply in_or_app; left; exact He|].
      intros [p k] x He Hx. exact (W2L p k x (CLV' _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
    assert (LBC2 : rw_cells asegs m2 LB2 [CB 256 bs]).
    { apply (KPa _ _ LBC'). cbn [cells_size csize]. intros x Hx. apply (W2L LB2 256 x (CLV' _ ltac:(apply in_or_app; right; exact HLB))). clear - Hx. lia. }
    assert (NBC2 : rw_cells asegs m2 namev [CB (Z.to_nat nn) bn]).
    { apply (KPa _ _ NBC'). cbn [cells_size csize]. intros x Hx. apply (W2L namev nn x (CLV' _ ltac:(apply in_or_app; right; exact HNB))). clear - Hx NN. lia. }
    set (e' := if got =? 2 then (if len' =? 65 then 0 else 1) else 0) in *.
    assert (PFR2 : pem_frame en m2 j0 (loc_H LB2 tmp) (loc_F RT en) (wz e') hBv dBv x1 x2 gap).
    { split; [apply (KPa _ _ FR0); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
      split; [apply (KPa _ _ FRH); rewrite SZH; intros x Hx; subst W2; cbn; clear - Hx; lia|]. split; [exact SZH|].
      split; [apply (KPa _ _ FRF); rewrite SZF; intros x Hx; subst W2; cbn; clear - Hx; lia|]. split; [exact SZF|].
      split; [exact FR104'|].
      split; [apply (KPa _ _ FRE); unfold loc_E; cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
      split; [apply (KPa _ _ FR224); cbn [cells_size csize Nat.add]; intros x Hx; subst W2; cbn; clear - Hx; lia|].
      apply (KPa _ _ FRG). cbn [cells_size csize]. intros x Hx. subst W2. cbn. clear - Hx PD. lia. }
    refine (KG Σ' m2 F' fc' ra' w0 w1 w2 g0 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c2 n pd' maxT' e' COM2 FRS' LR9 REST2 PFR2 FFC2 ON2 LBC2 NBC2 MBT2 MBO2 HN _ _ CA BA LSUM' MXB' Hc2').
    + subst e'. clear. destruct (got =? 2); [destruct (len' =? 65)|]; lia.
    + subst e'. intros G. replace (got =? 2) with false by (symmetry; apply Z.eqb_neq; exact G). reflexivity.
Qed.

Theorem PUTS_proof : forall N, GETS1_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N -> PUTS_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N G1P en Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6
         LB2 namev nn hBv dBv tmp len len' got prev partial bn bs KX KY methX methY lenX maxX lenY maxY.
  intros MEAS INV LEN' NL NUL PREV PARTIAL LEN LEN1 LEN2 INVW. unfold pem_at, cps. intros T c HA Hk.
  pose proof INV as (COM & REST & REM & LRM & PFR & FFC & ON & AL16 & LBS & LBC & NAL & NNR & LBN & NBC & NIN & MBX & MBY & GOT & GLT & GE2 & ENDV & LSUM & MXB & MYB).
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBX) as (LX & _). pose proof (mbio_rep_bnd _ _ _ _ _ _ _ _ MBY) as (LY & _).
  pose proof (grow_pot_nonneg RT en lenX lenY maxX maxY off OFF ltac:(clear - LX; lia) ltac:(clear - LY; lia) LSUM MXB MYB) as GP.
  pose proof PFR as (_ & _ & _ & _ & _ & FR104 & _).
  (* [comment removed for export] *)
  assert (HE : exists e, endv = wz e /\ (e = 0 \/ e = 1)) by (destruct ENDV as [-> | ->]; [exists 0| exists 1]; split; [reflexivity| lia| reflexivity| lia]).
  destruct HE as (e & -> & HE).
  pose proof (pu_a_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz tmp) (wz len') (wz prev) s5 (wz got) (wz partial) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                t3 t4 t5 t6 F fc m e tmp LB2 SP0' SPH HE eq_refl eq_refl MI FR104) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a0' & ->) & Hc1'). clear Hc1 HA.
  destruct HE as [-> | ->]; cbn [Z.eqb] in Hc1'.
  2: { (* [comment removed for export] *)
    refine (H_R2 en Σ m off crem lrem j0 (loc_H LB2 tmp) (wz 1) x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7
              (wz len') (wz prev) s5 (wz got) (wz partial) t3 t4 t5 t6 LB2 namev nn hBv dBv 907 bn bs KX KY methX methY lenX maxX lenY maxY
              COM REST _ ltac:(clear - LRM; lia) ltac:(clear; lia) PFR FFC ON AL16 LBS LBC NAL NNR LBN NBC MBX MBY T c1 Hc1' Hk).
    clear - REM GP OFF. unfold hd_need, C_END in *. lia. }
  (* [comment removed for export] *)
  destruct (Z.eq_dec got 2) as [G2 | GN2].
  - (* [comment removed for export] *)
    pose proof (GE2 G2) as Etmp. subst tmp.
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (mbio_ent KY maxY ++ mbio_ent KX maxX ++ [(LB2, 256); (namev, nn)]) COM
                  ltac:(rewrite !app_assoc; apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl])) as COMp.
    refine (puts_core T en Σ m off crem lrem j0 x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 c1 LB2 namev nn hBv dBv dBv len len' got prev partial bn bs
              KY KX hBv methY methX lenY maxY lenX maxX COMp REST PFR
              FFC ON AL16 LBS LBC ltac:(clear - NNR; lia) NBC MBY MBX _ ltac:(clear - LRM; lia) LEN' NUL LEN LEN1 LEN2 ltac:(clear - INVW; lia) ltac:(clear - LSUM; lia) MYB MXB GOT Hc1' _ _).
    + clear - REM. unfold hd_need, grow_pot in *. lia.
    + (* [comment removed for export] *)
      intros Σ' m' F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' n pd' maxY' e' COM' FRS' LR9 REST' PFR' FFC' ON' LBC' NBC' MBY' MBX' HN HE' HE0 CA BA LSUM' MYB' Hc'.
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ' m' off _ _ _ (mbio_ent KX maxX ++ mbio_ent (mbk_data KY pd') maxY' ++ [(LB2, 256); (namev, nn)]) COM'
                    ltac:(rewrite !app_assoc; apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl])) as COMq.
      refine (G1P en Σ' m' off (crem - puts_cost lenY n maxY) _ j0 (wz e') x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 (wz len') (wz prev) s5 y3 y4 y5 y6
                LB2 namev nn hBv dBv dBv got partial bn bs KX (mbk_data KY pd') methX methY lenX maxX (lenY + n) maxY' MEAS _ PARTIAL _ T c' Hc' Hk).
      * unfold hd_inv. cbv zeta.
        split; [exact COMq|]. split; [exact REST'|]. split; [clear - CA; unfold hd_need, grow_pot in *; lia|]. split; [clear - LR9; lia|].
        split; [exact PFR'|]. split; [exact FFC'|]. split; [exact ON'|].
        split; [exact AL16|]. split; [exact LBS|]. split; [exact LBC'|].
        split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC'|]. split; [exact NIN|].
        split; [exact MBX'|]. split; [exact MBY'|].
        split; [exact GOT|]. split; [intros X; exfalso; clear - X G2; lia|]. split; [intros _; reflexivity|]. split; [destruct HE' as [-> | ->]; [left| right]; reflexivity|].
        split; [clear - LSUM'; lia|]. split; [exact MXB| exact MYB'].
      * clear - BA. lia.
    + (* [comment removed for export] *)
      intros Σ' m' F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' n pd' maxY' _ L65 COM' FRS' LR9 REST' PFR' FFC' ON' LBC' NBC' MBY' MBX' CR1 Hc'.
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ' m' off _ _ _ ((mbio_ent KX maxX ++ mbio_ent (mbk_data KY pd') maxY' ++ [(LB2, 256); (namev, nn)]) ++ []) COM'
                    ltac:(rewrite app_nil_r, !app_assoc; apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl])) as COMq.
      refine (H_F2 en Σ' m' off _ _ [] j0 (loc_H LB2 dBv) (wz 0) x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 (wz dBv) (wz len') (wz prev) s5 (wz got) (wz partial) y3 y4 y5 y6
                LB2 namev nn hBv dBv bn bs KX (mbk_data KY pd') methX methY lenX maxX (lenY + n) maxY' COMq _ CR1 PFR' FFC' ON' AL16 LBS LBC' NAL NNR LBN NBC' MBX' MBY' T c' Hc' Hk).
      split; [left; split; [reflexivity| exact REST']|]. split; [apply Forall_nil|]. split; intros ee [].
  - (* [comment removed for export] *)
    destruct (GLT ltac:(clear - GOT GN2; lia)) as (Etmp & LY0 & MY0 & _). subst tmp.
    refine (puts_core T en Σ m off crem lrem j0 x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 c1 LB2 namev nn hBv dBv hBv len len' got prev partial bn bs
              KX KY dBv methX methY lenX maxX lenY maxY COM REST PFR
              FFC ON AL16 LBS LBC ltac:(clear - NNR; lia) NBC MBX MBY _ LRM LEN' NUL LEN LEN1 LEN2 INVW LSUM MXB MYB GOT Hc1' _ _).
    + clear - REM. unfold hd_need in *. lia.
    + (* [comment removed for export] *)
      intros Σ' m' F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' n pd' maxX' e' COM' FRS' LR9 REST' PFR' FFC' ON' LBC' NBC' MBX' MBY' HN HE' HE0 CA BA LSUM' MXB' Hc'.
      refine (G1P en Σ' m' off (crem - puts_cost lenX n maxX) _ j0 (wz e') x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 (wz len') (wz prev) s5 y3 y4 y5 y6
                LB2 namev nn hBv dBv hBv got partial bn bs (mbk_data KX pd') KY methX methY (lenX + n) maxX' lenY maxY MEAS _ PARTIAL _ T c' Hc' Hk).
      * unfold hd_inv. cbv zeta.
        split; [exact COM'|]. split; [exact REST'|]. split; [clear - CA; unfold hd_need in *; lia|]. split; [exact LR9|].
        split; [exact PFR'|]. split; [exact FFC'|]. split; [exact ON'|].
        split; [exact AL16|]. split; [exact LBS|]. split; [exact LBC'|].
        split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC'|]. split; [exact NIN|].
        split; [exact MBX'|]. split; [exact MBY'|].
        split; [exact GOT|]. split; [intros _; split; [reflexivity|]; split; [exact LY0|]; split; [exact MY0|]; rewrite (HE0 GN2); reflexivity|]. split; [intros X; exfalso; exact (GN2 X)|].
        split; [destruct HE' as [-> | ->]; [left| right]; reflexivity|].
        split; [exact LSUM'|]. split; [exact MXB'| exact MYB].
      * exact BA.
    + (* [comment removed for export] *)
      intros Σ' m' F' fc' zra y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' n pd' maxX' G2 L65. exfalso. exact (GN2 G2).
Qed.
End CPuts.
