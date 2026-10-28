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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_M_malloc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Definition SITE_nm_pmal1 : Z := 0x30c598.
Definition SITE_nm_mcp : Z := 0x30c5b0.
Definition SITE_nm_pfree : Z := 0x30c5c4.
Definition SITE_nm_pmal2 : Z := 0x30c5d4.

Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

Lemma t_addiw_small : forall z c, 0 <= z + c < 2 ^ 31 -> 0 <= z < 2 ^ 64 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c) = z + c.
Proof.
  intros z c Hz Hr. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition nm1_post (sp1 : Z) (gp s0 s2 s3 s5 s6 s8 s9 s10 s11 c7 : word) (F : bvmap 5 word) (fc : bv 32) (nn HL : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR (wz SITE_nm_pmal1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz nn) c7 (wz 804) a3 a4 a5 a6 a7 s2 s3 c7 s5 s6 (wz nn) s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz FZ_PEM_MALLOC) fc None m' (seg_rom asegs)
    /\ munch [(HL, HL + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' HL [C1 (Z_to_bv 8 0)].
Lemma nm1_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (len' LB1 HL p n : Z) (b : byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 17 <= len' <= 255 -> 0 < LB1 -> HL = LB1 + len' - 6 -> 0 < HL -> HL + 1 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m HL [C1 b] -> acc asegs m p n -> p mod 8 = 0 -> n mod 8 = 0 -> 0 < p -> p <= HL -> HL < p + n ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (nm1_post sp1 gp s0 s2 (wz HL) (wz LB1) s6 s8 (wz SHB) s10 s11 c7 F fc (len' - 16) HL m)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz HL) s4 (wz LB1) s6 (wz len') s8 (wz SHB) s10 s11 t3 t4 t5 t6) F (wz J_NAME) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH LEN LB0 EHL HL0 HLH MI HC ACC PAL N8 P0 PH1 PH2 FRE. unfold J_NAME, TP_A, SHB in *.
  pose proof (munch_refl [(HL, HL + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 HL) = HL) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 LB1) = LB1) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 len') = len') by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zsh. zstep. if_false.
  zstep. change Startup_glue.z64 with (Z_to_bv 64 0). lfix.
  zstep. rewrite (swrap32_small (len' + -16)) by lia. replace (len' + -16) with (len' - 16) by lia.
  zstep. zstep. zstep. zstep. zstep.
  unfold nm1_post, SITE_nm_pmal1, FZ_PEM_MALLOC. apply evt_done. do 13 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma nm2_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (p LB1 nn : Z),
  0 < p < 2 ^ 47 -> 0 < LB1 -> LB1 + 256 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms = MS (mkR (wz SITE_nm_mcp) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) (wz p) (wz (LB1 + 11)) (wz nn) a3' a4' a5' a6' a7' s2 s3 s4 (wz LB1) s6 (wz nn) s8 s9 (wz p) s11 t3' t4' t5' t6')
              F (wz e_asan_memcpy) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_nm_pmal1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz LB1) s6 (wz nn) s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_nm_pmal1) fc None m (seg_rom asegs)).
Proof.
  intros until nn. intros HP HL0 HLH MI. unfold SITE_nm_pmal1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 LB1) = LB1) by (apply unsigned_lit; lia).
  zstep. if_false. zstep.
  zstep. zstep. zstep.
unfold SITE_nm_mcp, e_asan_memcpy. apply evt_done. do 12 eexists. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma nm3_walk : forall sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms = MS (mkR (wz SITE_nm_pfree) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) s5 s4 (wz 256) (wz 811) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (wz FZ_PEM_FREE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_nm_mcp) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_nm_mcp) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_nm_mcp, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  unfold SITE_nm_pfree, FZ_PEM_FREE. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.
Lemma nm4_walk : forall sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms = MS (mkR (wz SITE_nm_pmal2) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) (wz 256) s4 (wz 846) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (wz FZ_PEM_MALLOC) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_nm_pfree) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_nm_pfree) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_nm_pfree, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.
  unfold SITE_nm_pmal2, FZ_PEM_MALLOC. apply evt_done. do 12 eexists. split; [reflexivity| exact I].
Qed.
Lemma nm5_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (p : Z)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < p < 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_nm_pmal2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 c5 s4 s5 s6 s7 s8 s9 s10 (wz p) t3 t4 t5 t6)
                                F (wz J_NGETS) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_nm_pmal2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_nm_pmal2) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH HP MI FRE. unfold SITE_nm_pmal2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  zstep. zstep. if_false. zstep.
  unfold J_NGETS. apply evt_done. split; [reflexivity| exact I].
Qed.

Lemma rw_CB_of_bytes' : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs BA WR. split.
  - split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.
Lemma rw_CB_len : forall (m : mem) a n bs, rw_cells asegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF. Qed.

Section CName.
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
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_PM : pem_malloc_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_PF : pem_free_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis H_NGETS : NGETS_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma rest_keep : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP W,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
  In (e_E RT en, 904) KEEP -> (forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x) -> errst_at_rest (e_E RT en) [] m'.
Proof using errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem cur KEEP W COM ER PR INK HO. eapply errst_rest_agree; [exact ER|]. intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & [] & _)]. apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INK| exact R]| exact (HO _ R)].
Qed.
(* [comment removed for export] *)
Lemma com_lrem : forall (en : pem_entry) Σ (m : mem) off crem lrem lrem' cur,
  pem_com en Σ m off crem lrem cur -> 0 <= lrem' -> Z.of_nat (length (rt_live RT Σ)) + lrem' <= LIVE_MAX -> pem_com en Σ m off crem lrem' cur.
Proof.
  intros en Σ m off crem lrem lrem' cur COM H0 H1.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & REST).
  split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|].
  split; [exact HLOS|]. split; [exact CLE|]. split; [exact SEC|]. split; [exact LE|]. split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact NTL|].
  split; [exact MB|]. split; [exact OFF|]. split; [exact BLT|]. split; [exact KLV|]. split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|].
  split; [exact FRS|]. split; [exact FRN|]. split; [exact SP0|]. split; [exact CG|]. split; [exact H1|]. split; [exact H0| exact REST].
Qed.

Theorem NAME_proof : NAME_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 LB1 hBv dBv len' bs KX KY methX methY maxX maxY.
  cbv zeta. intros COM ER0 REM LRM PFR FFC ON AL16 LBS LBC LEN NL NUL MBX MBY MX0 MY0. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (HLB : In (LB1, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB1, 256) COM HLB ltac:(cbn; lia)) as (INL & L0 & LLO & LHI & LNAC). cbn [fst snd] in L0, LLO, LHI, LNAC.
  destruct (af_acc_live RT AF Σ m LB1 256 ART0 INL) as [LWR LACC].
  (* [comment removed for export] *)
  set (k := Z.to_nat (len' - 6)) in *.
  pose proof (rw_cells_split_CB asegs m LB1 [] 256 bs [] [k; 1; 255 - k]%nat LBC ltac:(cbn; clear - LEN; subst k; lia)) as LB3. cbn [mk_CB_cells app] in LB3.
  pose proof (proj1 (rw_cells_app m _ [CB k (firstn k bs)] _) LB3) as [LBa LBbc]. pose proof (proj1 (rw_cells_app m _ [CB 1%nat (firstn 1 (skipn k bs))] _) LBbc) as [LBb LBz].
  cbn [cells_size csize Nat.add] in LBbc, LBb, LBz. rewrite Nat.add_0_r in LBb, LBz, LBbc.
  set (HL := LB1 + Z.of_nat k) in *.
  assert (EHL : HL = LB1 + len' - 6) by (subst HL k; clear - LEN; lia).
  pose proof (rw_CB_len m _ _ _ LBb) as LY1.
  destruct (firstn 1 (skipn k bs)) as [|b0 [|b1 tl1]] eqn:EY; [cbn in LY1; discriminate| | cbn in LY1; discriminate].
  assert (HC : rw_cells asegs m HL [C1 b0]) by (eapply rw_cells_recast; [exact LBb| cbn; repeat split; exact I| reflexivity]).
  pose proof PFR as (FR0 & FRH & SZH & FRF & SZF & FR104 & FRE & FR224 & FRG). unfold loc_E in FRE.
  rewrite <- EHL in HA.
  (* [comment removed for export] *)
  pose proof (nm1_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz 6) (wz LIT_BEGIN) (wz LIT_TAIL) (wz (shad (e_f RT en)))
                (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) t3 t4 t5 t6 F fc m len' LB1 HL LB1 256 b0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                SP0' SPH LEN L0 EHL ltac:(clear - L0 EHL LEN; lia) ltac:(clear - LLO HLO EHL LEN; lia) MI HC LACC ltac:(clear - AL16; Z.div_mod_to_equations; lia) eq_refl L0
                ltac:(clear - EHL LEN; lia) ltac:(clear - EHL LEN; lia) FRE) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b3' & b4' & b5' & b6' & b7' & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & HC1) & Hc1'). clear Hc1.
  (* [comment removed for export] *)
  assert (PRm : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(LB1, LB1 + 256)] m m1).
  { intros a Ha [Ho _]. apply MU1. cbn. split; [clear - Ho LEN; subst HL k; lia| exact I]. }
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ [(LB1, 256)] COM ltac:(intros e [<-|[]]; left; split; [exact HLB| cbn; lia])) as WOKm.
  cbn [map rng fst snd] in WOKm. pose proof WOKm as (MWS & MWFR & MWFF & MWSH & MWL & MWP).
  assert (NXL : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY) -> ~ In e [(LB1, 256)]).
  { intros e He [<-|[]]. pose proof ND as ND'. rewrite app_assoc, map_app, <- app_assoc in ND'. pose proof (nd_split (map fst (mbio_ent KX maxX ++ mbio_ent KY maxY)) _ ND') as (_ & _ & DJ).
    apply (DJ LB1); [exact (in_map fst _ _ He)| left; reflexivity]. }
  assert (ST1 : stk asegs m1 (e_lo RT en) (e_sp1 RT en)).
  { eapply stk_munch; [exact ST| exact MU1| exact WM1|]. intros x Hx. cbn. split; [clear - Hx LLO EHL LEN; lia| exact I]. }
  assert (COM1 : pem_com en Σ m1 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])).
  { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m m1); [exact COM| exact MU1| exact WM1| exact MI1| exact ST1|].
    apply Forall_cons; [| apply Forall_nil]. right; left. exists (LB1, 256). split; [exact HLB|]. cbn [fst snd]. clear - EHL LEN; lia. }
  assert (ER1 : errst_at_rest (e_E RT en) [] m1).
  { eapply (rest_keep en Σ m m1); [exact COM| exact ER0| exact PRm| exact (ELV _ INE)|]. intros x Hx. apply (MWL (e_E RT en) 904 x (ELV _ INE)); [| exact Hx].
    intros [X|[]]. apply (CFR _ HLB). cbn [fst]. injection X. intros _ E. rewrite E. exact (in_map fst _ _ INE). }
  assert (PFR1 : pem_frame en m1 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap) by exact (pem_frame_keep RT en m m1 _ _ _ j0 lH _ endv hBv dBv x1 x2 gap PFR PRm PD TOP MWS).
  assert (FFC1 : rw_cells asegs m1 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m m1 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PRm INF MWFF).
  assert (ON1 : out_null RT en m1).
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m1 off crem lrem _ _ _ COM MWS MWFR PRm) as AGP.
    assert (G8 : forall P v, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 v] -> rw_cells asegs m1 P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]| apply G8; [do 3 right; left; reflexivity| exact O4]]. }
  assert (MBX1 : mbio_rep (rt_live RT Σ) m1 KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PRm| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM MWL e x ltac:(apply in_or_app; left; exact He) (NXL e ltac:(apply in_or_app; left; exact He)) Hx). }
  assert (MBY1 : mbio_rep (rt_live RT Σ) m1 KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PRm| intros e He; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM MWL e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) (NXL e ltac:(apply in_or_app; right; exact He)) Hx). }
  (* [comment removed for export] *)
  assert (LBa1 : rw_cells asegs m1 LB1 [CB k (firstn k bs)]).
  { eapply rw_cells_agree; [exact LBa| | exact WM1]. intros a Ha. apply MU1. cbn [cells_size csize Nat.add] in Ha. cbn. split; [clear - Ha; subst HL; lia| exact I]. }
  assert (LBz1 : rw_cells asegs m1 (HL + Z.of_nat 1) [CB (255 - k) (firstn (255 - k) (skipn 1 (skipn k bs)))]).
  { eapply rw_cells_agree; [exact LBz| | exact WM1]. intros a Ha. apply MU1. cbn [cells_size csize Nat.add] in Ha. cbn. split; [clear - Ha; lia| exact I]. }
  set (bsw := firstn k bs ++ [Z_to_bv 8 0] ++ firstn (255 - k) (skipn 1 (skipn k bs))).
  assert (LBSW : length bsw = 256%nat) by (subst bsw; rewrite !length_app, !length_firstn, !length_skipn, LBS; cbn [length]; clear - LEN; subst k; lia).
  assert (LBW1 : rw_cells asegs m1 LB1 [CB 256 bsw]).
  { eapply rw_cells_recast.
    - apply (proj2 (rw_cells_app m1 LB1 [CB k (firstn k bs)] ([C1 (Z_to_bv 8 0)] ++ [CB (255 - k) (firstn (255 - k) (skipn 1 (skipn k bs)))]))). split; [exact LBa1|].
      cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. fold HL. apply (proj2 (rw_cells_app m1 HL [C1 (Z_to_bv 8 0)] _)). split; [exact HC1|]. cbn [cells_size csize Nat.add]. exact LBz1.
    - cbn. split; [exact LBSW| exact I].
    - subst bsw. cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. reflexivity. }
  clear LBa LBz LBb LBbc LB3 LBa1 LBz1 HC HC1.
  set (nn := len' - 16) in *.
  assert (MC0 : mcost nn = 0) by (unfold mcost; replace (nn <=? 64512) with true by (symmetry; apply Z.leb_le; subst nn; clear - LEN; lia); reflexivity).
  (* [comment removed for export] *)
  eapply (pem_call_pmal RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PM T en Σ m1 off crem lrem _ nn SITE_nm_pmal1 F fc u0 u1 u2 (wz 804) b3' b4' b5' b6' b7'
            (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn) (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) u3 u4 u5 u6 c1 COM1
            ltac:(subst nn; clear - LEN; lia) ltac:(rewrite MC0; clear - CR0; lia) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_pmal, SITE_nm_pmal1; right; left; reflexivity) Hc1').
  clear Hc1' u0 u1 u2 b3' b4' b5' b6' b7' u3 u4 u5 u6.
  intros Σ1 m2 F1 fc1 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 p njunk COM2 LV1 FRS1 PR1 LNJ PC P0 P16 PTOP Hc2. rewrite MC0, Z.sub_0_r in COM2.
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ COM1) as WOK1. pose proof WOK1 as (HWS1 & HWFR1 & HWFF1 & HWF1 & HWL1 & HWP1).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ1 m2 off crem (lrem - 1) _ COM2) as [ELV2 CLV2].
  pose proof COM2 as (ART2 & MI2 & _).
  assert (FRS1' : rt_frames RT Σ1 = rt_frames RT Σ) by exact FRS1. assert (INF1 : In (e_f RT en, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1'; exact INF).
  assert (ER2 : errst_at_rest (e_E RT en) [] m2).
  { eapply (rest_keep en Σ m1 m2); [exact COM1| exact ER1| exact PR1| exact (ELV _ INE)| exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ COM1)]. }
  assert (PFR2 : pem_frame en m2 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap) by exact (pem_frame_keep RT en m1 m2 _ _ _ j0 lH _ endv hBv dBv x1 x2 gap PFR1 PR1 PD TOP HWS1).
  assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m1 m2 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC1 PR1 INF HWFF1).
  assert (ON2 : out_null RT en m2).
  { destruct ON1 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 m2 off crem lrem _ _ _ COM1 HWS1 HWFR1 PR1) as AGP.
    assert (G8 : forall P v, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m1 P [C8 v] -> rw_cells asegs m2 P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]| apply G8; [do 3 right; left; reflexivity| exact O4]]. }
  assert (MBX2 : mbio_rep (rt_live RT Σ1) m2 KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX1| exact PR1| intros e He; rewrite LV1; split; [| right]; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ _ _ COM1 HWL1 (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; left; exact He) Hx). }
  assert (MBY2 : mbio_rep (rt_live RT Σ1) m2 KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY1| exact PR1| intros e He; rewrite LV1; split; [| right]; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ _ _ COM1 HWL1 (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) Hx). }
  assert (LBW2 : rw_cells asegs m2 LB1 [CB 256 bsw]).
  { eapply rw_cells_agree_nw; [exact LBW1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 256) with 256.
    exact (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 m2 off crem lrem _ _ _ _ (LB1, 256) COM1 HWL1 (fun e0 H0 => or_intror H0) PR1 HLB (CLV _ HLB)). }
  clear COM COM1 ER0 ER1 PFR PFR1 FFC FFC1 ON ON1 MBX MBX1 MBY MBY1 LBW1 LBC PRm MU1 WM1 WOKm MWS MWFR MWFF MWSH MWL MWP ST1 HWS1 HWFR1 HWFF1 HWF1 HWL1 HWP1 WOK1.
  pose proof COM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PERM2 & CFR2 & ND2 & LPOS2 & _).
  assert (HLB2 : In (LB1, 256) ((p, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)])) by (right; exact HLB).
  assert (INL1 : In (LB1, 256) (rt_live RT Σ1)) by exact (CLV2 _ HLB2).
  assert (INP1 : In (p, nn) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (NDP : ~ In p (map fst (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)]) ++ e_E RT en :: mbio_blocks (e_K RT en))).
  { pose proof ND2 as X. change (List.NoDup (p :: (map fst (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)]) ++ e_E RT en :: mbio_blocks (e_K RT en)))) in X. inversion X; assumption. }
  assert (NPL : p <> LB1) by (intros E; apply NDP; apply in_or_app; left; rewrite E; exact (in_map fst _ _ HLB)).
  pose proof (live_ne_apart RT AF Σ1 m2 p nn LB1 256 ART2 INP1 INL1 ltac:(intros E; injection E; intros _ E1; exact (NPL E1))) as APL.
  (* [comment removed for export] *)
  pose proof (nm2_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7 (wz 6) (wz HL) (wz (e_flags RT en)) (wz LIT_TAIL) (wz (shad (e_f RT en))) (wz SHB)
                (wz (Z.land (e_flags RT en) (Z.lnot 4))) (wz (LB1 - 6)) y3 y4 y5 y6 F1 fc1 m2 p LB1 nn ltac:(clear - P0 PTOP LEN; subst nn; unfold USTACK_TOP in PTOP; lia) L0
                ltac:(clear - LLO HLO TOP PD; unfold e_sp1, USTACK_TOP in *; lia) MI2) as W.
  cl_lift W Hc2 c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (u0 & u1 & u2 & b3' & b4' & b5' & b6' & b7' & u3 & u4 & u5 & u6 & -> & _) & Hc3'). clear Hc3 Hc2.
  (* [comment removed for export] *)
  set (src := firstn (Z.to_nat nn) (skipn 11 bsw)).
  assert (LSRC : length src = Z.to_nat nn) by (subst src; rewrite length_firstn, length_skipn, LBSW; subst nn; clear - LEN; lia).
  assert (SRC : bytes_at asegs m2 (LB1 + 11) src).
  { pose proof (rw_cells_bytes_at _ _ _ _ LBW2) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 11 bsw) in B. apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B]. rewrite length_firstn, LBSW in B. cbn [Nat.min] in B.
    rewrite <- (firstn_skipn (Z.to_nat nn) (skipn 11 bsw)) in B. apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [B _]. exact B. }
  assert (A1 : p + Z.of_nat (length src) <= p + nn) by (rewrite LSRC; subst nn; clear - LEN; lia).
  assert (A2 : Z.of_nat (length src) < 2 ^ 40) by (rewrite LSRC; subst nn; clear - LEN; lia).
  assert (A3 : p + Z.of_nat (length src) <= LB1 + 11 \/ LB1 + 11 + Z.of_nat (length src) <= p) by (rewrite LSRC; destruct APL as [Q|Q]; [left| right]; subst nn; clear - Q LEN; lia).
  pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m2 off crem (lrem - 1) _ LB1 256 (LB1 + 11) (Z.of_nat (length src)) COM2 HLB2 ltac:(clear; lia) ltac:(clear; lia)
                ltac:(rewrite LSRC; subst nn; clear - LEN; lia) ltac:(clear; lia)) as CK.
  assert (ENN : wz (Z.of_nat (length src)) = wz nn) by (rewrite LSRC, Z2Nat.id by (subst nn; clear - LEN; lia); reflexivity). rewrite <- ENN in Hc3'.
  eapply (pem_icpt_memcpy RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS MCP T en Σ1 m2 off crem (lrem - 1) _ p (LB1 + 11) p nn src SITE_nm_mcp F1 fc1
            u0 u1 u2 b3' b4' b5' b6' b7' (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz (Z.of_nat (length src))) (wz p) (wz (LB1 - 6)) u3 u4 u5 u6 c3 COM2
            ltac:(left; reflexivity) ltac:(subst nn; clear - LEN; lia) ltac:(clear; lia) A1 ltac:(clear - L0 LLO HLO TOP PD; unfold e_sp1, USTACK_TOP in *; lia) A2 SRC CK A3
            ltac:(unfold SITE_nm_mcp; clear; lia) eq_refl Hc3').
  clear Hc3' u0 u1 u2 b3' b4' b5' b6' b7' u3 u4 u5 u6.
  intros m3 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c3' COM3 PR2 WOK2 PX2 MI3 BB3 Hc3. rewrite ENN in Hc3. pose proof WOK2 as (HWS2 & HWFR2 & HWFF2 & HWF2 & HWL2 & HWP2).
  pose proof COM3 as (ART3 & _).
  assert (ER3 : errst_at_rest (e_E RT en) [] m3).
  { eapply (rest_keep en Σ1 m2 m3); [exact COM2| exact ER2| exact PR2| exact (ELV2 _ INE)|]. intros x Hx. apply (HWL2 (e_E RT en) 904 x (ELV2 _ INE)); [| exact Hx].
    intros [X|[]]. apply NDP. injection X. intros _ ->. apply in_or_app; right; left; reflexivity. }
  assert (PFR3 : pem_frame en m3 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap) by exact (pem_frame_keep RT en m2 m3 _ _ _ j0 lH _ endv hBv dBv x1 x2 gap PFR2 PR2 PD TOP HWS2).
  assert (FFC3 : rw_cells asegs m3 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m2 m3 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC2 PR2 INF1 HWFF2).
  assert (ON3 : out_null RT en m3).
  { destruct ON2 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m2 m3 off crem (lrem - 1) _ _ _ COM2 HWS2 HWFR2 PR2) as AGP.
    assert (G8 : forall P v, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m2 P [C8 v] -> rw_cells asegs m3 P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]| apply G8; [do 3 right; left; reflexivity| exact O4]]. }
  assert (NXP : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)]) -> ~ In e [(p, nn)]).
  { intros e He [<-|[]]. apply NDP. apply in_or_app; left. exact (in_map fst _ _ He). }
  assert (MBX3 : mbio_rep (rt_live RT Σ1) m3 KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ1)); [exact MBX2| exact PR2| intros e He; split; apply CLV2; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m2 off crem (lrem - 1) _ _ _ COM2 HWL2 e x ltac:(right; apply in_or_app; left; exact He) (NXP e ltac:(apply in_or_app; left; exact He)) Hx). }
  assert (MBY3 : mbio_rep (rt_live RT Σ1) m3 KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ1)); [exact MBY2| exact PR2| intros e He; split; apply CLV2; right; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m2 off crem (lrem - 1) _ _ _ COM2 HWL2 e x ltac:(right; apply in_or_app; right; apply in_or_app; left; exact He) (NXP e ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
  assert (LBW3 : rw_cells asegs m3 LB1 [CB 256 bsw]).
  { eapply rw_cells_agree_nw; [exact LBW2|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 256) with 256. intros a Ha. cbv beta in Ha.
    apply PR2; [apply (acl_live _ _ _ LB1 256); [exact INL1| exact Ha]|]. cbn. split; [destruct APL as [Q|Q]; clear - Q Ha LEN; subst nn; lia| exact I]. }
  assert (NMC3 : rw_cells asegs m3 p [CB (Z.to_nat nn) src]).
  { rewrite <- LSRC. apply rw_CB_of_bytes'; [exact BB3|]. rewrite LSRC, Z2Nat.id by (subst nn; clear - LEN; lia). exact (proj1 (af_acc_live RT AF Σ1 m3 p nn ART3 INP1)). }
  clear COM2 ER2 PFR2 FFC2 ON2 MBX2 MBY2 LBW2 PR1 PR2 WOK2 HWS2 HWFR2 HWFF2 HWF2 HWL2 HWP2 PX2 BB3 MI2 ART2 PC.
  (* [comment removed for export] *)
  pose proof (nm3_walk (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz p) e1 e2 e3 e4 e5 e6 e7 (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn)
                (wz (shad (e_f RT en))) (wz SHB) (wz p) (wz (LB1 - 6)) z3 z4 z5 z6 F2 fc2 m3 MI3) as W.
  cl_lift W Hc3 c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (u0 & u1 & u2 & b4' & b5' & b6' & b7' & u3 & u4 & u5 & u6 & -> & _) & Hc4'). clear Hc4 Hc3.
  assert (HP3 : Permutation ((p, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)]) ((LB1, 256) :: (p, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY)).
  { change ((p, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB1, 256)]) with (((p, nn) :: mbio_ent KX maxX) ++ (mbio_ent KY maxY ++ [(LB1, 256)])).
    rewrite (app_assoc ((p, nn) :: mbio_ent KX maxX) (mbio_ent KY maxY) [(LB1, 256)]). apply Permutation_sym.
    change ((LB1, 256) :: (p, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY) with ((LB1, 256) :: (((p, nn) :: mbio_ent KX maxX) ++ mbio_ent KY maxY)). apply Permutation_cons_append. }
  pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ1 m3 off crem (lrem - 1) _ _ COM3 HP3) as COM3'.
  eapply (pem_call_pfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PF T en Σ1 m3 off crem (lrem - 1) _ LB1 256 256 SITE_nm_pfree F2 fc2
            u0 u1 u2 (wz 811) b4' b5' b6' b7' (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn) (wz p) (wz (LB1 - 6)) u3 u4 u5 u6 c4 COM3'
            ltac:(clear; lia) ltac:(unfold PEM_RAS_pfree, SITE_nm_pfree; do 2 right; left; reflexivity) Hc4').
  clear Hc4' u0 u1 u2 b4' b5' b6' b7' u3 u4 u5 u6.
  intros Σ2 m4 F3 fc3 v3 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c4' COM4 LV2 FRS2 PR3 RL3 Hc4.
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 off crem (lrem - 1) _ COM3') as WOK3. pose proof WOK3 as (HWS3 & HWFR3 & HWFF3 & HWF3 & HWL3 & HWP3).
  pose proof COM4 as (_ & MI4 & _).
  assert (ER4 : errst_at_rest (e_E RT en) [] m4).
  { eapply (rest_keep en Σ1 m3 m4); [exact COM3'| exact ER3| exact PR3| apply RL3; apply in_or_app; right; exact INE| exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 off crem (lrem - 1) _ COM3')]. }
  assert (PFR4 : pem_frame en m4 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap) by exact (pem_frame_keep RT en m3 m4 _ _ _ j0 lH _ endv hBv dBv x1 x2 gap PFR3 PR3 PD TOP HWS3).
  assert (FFC4 : rw_cells asegs m4 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m3 m4 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC3 PR3 INF1 HWFF3).
  assert (ON4 : out_null RT en m4).
  { destruct ON3 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 m4 off crem (lrem - 1) _ _ _ COM3' HWS3 HWFR3 PR3) as AGP.
    assert (G8 : forall P v, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m3 P [C8 v] -> rw_cells asegs m4 P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]| apply G8; [do 3 right; left; reflexivity| exact O4]]. }
  assert (MBX4 : mbio_rep (rt_live RT Σ2) m4 KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ1)); [exact MBX3| exact PR3| intros e He; split; apply RL3; apply in_or_app; left; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 off crem (lrem - 1) _ _ _ COM3' HWL3 (fun e0 H0 => or_intror H0) e x ltac:(right; right; apply in_or_app; left; exact He) Hx). }
  assert (MBY4 : mbio_rep (rt_live RT Σ2) m4 KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ1)); [exact MBY3| exact PR3| intros e He; split; apply RL3; apply in_or_app; left; right; apply in_or_app; right; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 off crem (lrem - 1) _ _ _ COM3' HWL3 (fun e0 H0 => or_intror H0) e x ltac:(right; right; apply in_or_app; right; exact He) Hx). }
  assert (NMC4 : rw_cells asegs m4 p [CB (Z.to_nat nn) src]).
  { eapply rw_cells_agree_nw; [exact NMC3|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (subst nn; clear - LEN; lia).
    exact (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 m4 off crem (lrem - 1) _ _ _ _ (p, nn) COM3' HWL3 (fun e0 H0 => or_intror H0) PR3 ltac:(right; left; reflexivity) ltac:(apply RL3; apply in_or_app; left; left; reflexivity)). }
  clear COM3 COM3' ER3 PFR3 FFC3 ON3 MBX3 MBY3 NMC3 LBW3 PR3 WOK3 HWS3 HWFR3 HWFF3 HWF3 HWL3 HWP3 MI3 ART3.
  (* [comment removed for export] *)
  pose proof (nm4_walk (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) v3 g1 g2 g3 g4 g5 g6 g7 (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn)
                (wz (shad (e_f RT en))) (wz SHB) (wz p) (wz (LB1 - 6)) w3 w4 w5 w6 F3 fc3 m4 MI4) as W.
  cl_lift W Hc4 c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (u0 & u1 & u2 & b3' & b4' & b5' & b6' & b7' & u3 & u4 & u5 & u6 & -> & _) & Hc5'). clear Hc5 Hc4.
  assert (MC256 : mcost 256 = 0) by reflexivity.
  pose proof COM4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR04 & _).
  eapply (pem_call_pmal RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PM T en Σ2 m4 off crem (lrem - 1) _ 256 SITE_nm_pmal2 F3 fc3 u0 u1 u2 (wz 846) b3' b4' b5' b6' b7'
            (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn) (wz p) (wz (LB1 - 6)) u3 u4 u5 u6 c5 COM4
            ltac:(clear; lia) ltac:(rewrite MC256; exact CR04) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_pmal, SITE_nm_pmal2; do 2 right; left; reflexivity) Hc5').
  clear Hc5' u0 u1 u2 b3' b4' b5' b6' b7' u3 u4 u5 u6.
  intros Σ3 m5 F4 fc4 k0 k1 k2 h1 h2 h3 h4 h5 h6 h7 k3 k4 k5 k6 c6 p2 njunk2 COM5 LV3 FRS3 PR4 LNJ2 PC2 P20 P216 P2TOP Hc6. rewrite MC256, Z.sub_0_r in COM5.
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m4 off crem (lrem - 1) _ COM4) as WOK4. pose proof WOK4 as (HWS4 & HWFR4 & HWFF4 & HWF4 & HWL4 & HWP4).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ2 m4 off crem (lrem - 1) _ COM4) as [ELV4 CLV4].
  pose proof COM5 as (ART5 & MI5 & _).
  assert (FRS3' : rt_frames RT Σ3 = rt_frames RT Σ) by (rewrite FRS3, FRS2; exact FRS1').
  assert (INF2 : In (e_f RT en, 1%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF1).
  assert (ER5 : errst_at_rest (e_E RT en) [] m5).
  { eapply (rest_keep en Σ2 m4 m5); [exact COM4| exact ER4| exact PR4| exact (ELV4 _ INE)| exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m4 off crem (lrem - 1) _ COM4)]. }
  assert (PFR5 : pem_frame en m5 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap) by exact (pem_frame_keep RT en m4 m5 _ _ _ j0 lH _ endv hBv dBv x1 x2 gap PFR4 PR4 PD TOP HWS4).
  assert (FFC5 : rw_cells asegs m5 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m4 m5 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC4 PR4 INF2 HWFF4).
  assert (ON5 : out_null RT en m5).
  { destruct ON4 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m4 m5 off crem (lrem - 1) _ _ _ COM4 HWS4 HWFR4 PR4) as AGP.
    assert (G8 : forall P v, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m4 P [C8 v] -> rw_cells asegs m5 P [C8 v]).
    { intros P v HP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HP). }
    split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]| apply G8; [do 3 right; left; reflexivity| exact O4]]. }
  assert (MBX5 : mbio_rep (rt_live RT Σ3) m5 KX hBv methX 0 maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ2)); [exact MBX4| exact PR4| intros e He; rewrite LV3; split; [| right]; apply CLV4; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m4 off crem (lrem - 1) _ _ _ COM4 HWL4 (fun e0 H0 => or_intror H0) e x ltac:(right; apply in_or_app; left; exact He) Hx). }
  assert (MBY5 : mbio_rep (rt_live RT Σ3) m5 KY dBv methY 0 maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ2)); [exact MBY4| exact PR4| intros e He; rewrite LV3; split; [| right]; apply CLV4; right; apply in_or_app; right; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m4 off crem (lrem - 1) _ _ _ COM4 HWL4 (fun e0 H0 => or_intror H0) e x ltac:(right; apply in_or_app; right; exact He) Hx). }
  assert (NMC5 : rw_cells asegs m5 p [CB (Z.to_nat nn) src]).
  { eapply rw_cells_agree_nw; [exact NMC4|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (subst nn; clear - LEN; lia).
    exact (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m4 m5 off crem (lrem - 1) _ _ _ _ (p, nn) COM4 HWL4 (fun e0 H0 => or_intror H0) PR4 ltac:(left; reflexivity) ltac:(apply CLV4; left; reflexivity)). }
  clear COM4 ER4 PFR4 FFC4 ON4 MBX4 MBY4 NMC4 PR4 WOK4 HWS4 HWFR4 HWFF4 HWF4 HWL4 HWP4 MI4.
  (* [comment removed for export] *)
  pose proof PFR5 as (_ & _ & _ & _ & _ & _ & FRE5 & _). unfold loc_E in FRE5.
  pose proof (nm5_walk (e_sp1 RT en) (e_gp RT en) k0 k1 k2 (e_sp RT en) h1 h2 h3 h4 h5 h6 h7 (wz 6) (wz HL) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn)
                (wz (shad (e_f RT en))) (wz SHB) (wz p) (wz (LB1 - 6)) k3 k4 k5 k6 F4 fc4 m5 p2 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                SP0' SPH ltac:(clear - P20 P2TOP; unfold USTACK_TOP in P2TOP; lia) MI5 FRE5) as W.
  cl_lift W Hc6 c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (-> & _) & Hc7'). clear Hc7 Hc6.
  (* [comment removed for export] *)
  assert (HP5 : Permutation ((p2, 256) :: (p, nn) :: mbio_ent KX maxX ++ mbio_ent KY maxY) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(p2, 256); (p, nn)])).
  { rewrite (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(p2, 256); (p, nn)]).
    apply (Permutation_trans (l' := (p2, 256) :: ((mbio_ent KX maxX ++ mbio_ent KY maxY) ++ [(p, nn)]))).
    - apply perm_skip. apply Permutation_cons_append.
    - change ((mbio_ent KX maxX ++ mbio_ent KY maxY) ++ [(p2, 256); (p, nn)]) with ((mbio_ent KX maxX ++ mbio_ent KY maxY) ++ (p2, 256) :: [(p, nn)]). apply Permutation_middle. }
  pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ3 m5 off crem (lrem - 1 - 1) _ _ COM5 HP5) as COM5'.
  assert (LEN3 : Z.of_nat (length (rt_live RT Σ3)) + (lrem - 1) <= LIVE_MAX).
  { pose proof (Permutation_length PERM2) as L1. pose proof COM5' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PERM5 & _). pose proof (Permutation_length PERM5) as L3.
    rewrite LV1 in L1. cbn [length app] in L1, L3. rewrite !length_app in L1, L3. cbn [length] in L1, L3. clear - L1 L3 LIV. lia. }
  pose proof (com_lrem en Σ3 m5 off crem (lrem - 1 - 1) (lrem - 1) _ COM5' ltac:(clear - LRM; lia) LEN3) as COM6.
  (* [comment removed for export] *)
  assert (SRCNUL : nth_error src (Z.to_nat (nn - 1)) = Some (Z_to_bv 8 0)).
  { subst src. rewrite nth_error_firstn. replace (Z.to_nat (nn - 1) <? Z.to_nat nn)%nat with true by (symmetry; apply Nat.ltb_lt; subst nn; clear - LEN; lia).
    rewrite nth_error_skipn. subst bsw. rewrite nth_error_app2 by (rewrite length_firstn, LBS; subst nn k; clear - LEN; lia).
    rewrite length_firstn, LBS. replace (11 + Z.to_nat (nn - 1) - Nat.min k 256)%nat with 0%nat by (subst nn k; clear - LEN; lia). reflexivity. }
  refine (H_NGETS en Σ3 m5 off crem (lrem - 1) j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F4 fc4 (wz SITE_nm_pmal2) k0 k1 k2 (wz p2) h1 h2 h3 h4 h5 h6 h7
            (wz 6) (wz dBv) (wz (e_flags RT en)) (wz LB1) (wz LIT_TAIL) (wz nn) k3 k4 k5 k6
            p2 p nn hBv dBv src njunk2 KX KY methX methY maxX maxY COM6 ER5 _ ltac:(clear - LRM; lia) PFR5 FFC5 ON5 P216 LNJ2 PC2 P16 ltac:(subst nn; clear - LEN; lia) LSRC NMC5 (nth_error_In _ _ SRCNUL) MBX5 MBY5 MX0 MY0 T c7 Hc7' Hk).
  clear - REM. lia.
Qed.
End CName.
