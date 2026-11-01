(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_ng_gets : Z := 0x30c5f0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ng1_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms = MS (mkR (wz SITE_ng_gets) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) c13 s11 (wz 255) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (wz FZ_BIO_GETS) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_NGETS) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
    SP_NONNEG SP_ROOM MEMOK LOCALS.
  unfold J_NGETS, FZ_BIO_GETS, SITE_ng_gets.
  zstep. zstep. zstep. zstep.
  apply evt_done. do 12 eexists. split; [reflexivity | exact I].
Qed.
(* [comment removed for export] *)
Lemma ng2_walk0 : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz 854) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE2) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_ng_gets) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MEMOK.
  unfold SITE_ng_gets, J_RAISE2.
  zstep. zstep. if_true.
  apply evt_done. split; [reflexivity | exact I].
Qed.
(* [comment removed for export] *)
Definition ng2_post (sp1 : Z) (gp s0 s3 s8 s9 s10 c4 : word) (F : bvmap 5 word) (fc : bv 32) (k LB2 : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       ms = MS (mkR ra' (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) a0' a1' a2' a3' a4' a5' a6' a7'
                  c4 s3 (wz 0) (wz k) (wz 0) (wz 0) s8 s9 s10 (wz LB2) t3' t4' t5' t6') F (wz J_HD) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ wmono asegs m m' /\ munch [(sp1 + 24, sp1 + 80); (sp1 + 104, sp1 + 112)] m m'
    /\ rw_cells asegs m' (sp1 + 24)
         [C8 (wz (Z.land (LB2 + 253) 7)); C8 (wz (Z.land LB2 7)); C8 c4; C8 (wz (shad (LB2 + 253))); C8 (wz (LB2 + 253)); C8 (wz (shad LB2)); C8 (wz LIT_ENDSTR)]
    /\ rw_cells asegs m' (sp1 + 104) [C8 (wz 0)].
Lemma ng2_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (k LB2 : Z) (endv : word)
    (hh : list byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 1 <= k <= 254 -> 0 < LB2 -> LB2 + 256 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 24) [CB 56 hh] -> rw_cells asegs m (sp1 + 104) [C8 endv] ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (ng2_post sp1 gp s0 s3 s8 (wz SHB) s10 c4 F fc k LB2 m)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (wz SHB) s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_ng_gets) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 F fc m k LB2 endv hh c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
    SP_NONNEG SP_ROOM KRANGE LB_POS LB_BELOW MEMOK SLOTS ENDSLOT LOCALS.
  pose proof (munch_refl [(sp1 + 24, sp1 + 80); (sp1 + 104, sp1 + 112)] m) as MUN.
  pose proof (wmono_refl asegs m) as WMO.
  unfold SITE_ng_gets.
  zstep. zstep. if_cases BR; zify_cond BR.
  { exfalso. rewrite (proj2 (Z.ltb_lt 0 k)), (proj2 (Z.ltb_lt k _)) in BR by lia. discriminate BR. }
  zstep. zstep. zstep. zstep.
  fix_lit_store.
  zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. fix_lit_store.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite !Z.shiftr_div_pow2 in SLOTS by lia. change (2 ^ 3) with 8 in SLOTS.
  apply evt_done. unfold ng2_post. do 16 eexists. exists m1.
  split; [reflexivity|]. split; [exact MEMOK|]. split; [exact WMO|]. split; [exact MUN|].
  split; [exact SLOTS | exact ENDSLOT].
Qed.

(* [comment removed for export] *)
Lemma mbio_ent_len0 : forall live (m : mem) K BI meth len off, mbio_rep live m K BI meth len 0 off -> length (mbio_ent K 0) = 4%nat.
Proof.
  intros live m K BI meth len off (BM & fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MT)).
  unfold mbio_ent. destruct (k_d K) as [d|]; [destruct MT as (junk & _ & POS & _); exfalso; clear - POS; lia| rewrite app_nil_r; reflexivity].
Qed.

Section CNgets.
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
Hypothesis C_BG : bio_gets_stmt RT.
Hypothesis H_R2 : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_HD : forall N, HD_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma rest_keep_n : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur KEEP W,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp KEEP (rt_frames RT Σ) (e_sp1 RT en) W m m' ->
  In (e_E RT en, 904) KEEP -> (forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x) -> errst_at_rest (e_E RT en) [] m'.
Proof using errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem cur KEEP W COM ER PR INK HO. eapply errst_rest_agree; [exact ER|]. intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & [] & _)]. apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INK| exact R]| exact (HO _ R)].
Qed.

(* [comment removed for export] *)
Lemma stk_win_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur (W : list (Z * Z)),
  pem_com en Σ m off crem lrem cur -> (forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W x) ->
     (forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> outside W x)
  /\ (forall x, e_f RT en <= x < e_f RT en + 128 -> outside W x)
  /\ (forall P x, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> P <= x < P + 8 -> outside W x).
Proof using AF AFP.
  intros en Σ m off crem lrem cur W COM HW.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  split. { intros p n x Hin Hx. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & R & _). apply HW. left. clear - R Hx LOW LOR. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia. }
  split. { intros x Hx. pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & R & _). change (fs_size 1) with 128 in R. apply HW. left.
           clear - R Hx LOW LOR. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia. }
  intros P x HP Hx. assert (HL : pp_loc (e_frames RT en) (e_m RT en) USTACK_TOP P) by exact (proj2 (proj1 (Forall_forall _ _) OUTS P HP)).
  destruct HL as [[H1 H2]|(f & k & Hin & H1 & H2 & _)].
  - exfalso. clear - H1 H2. unfold USTACK_TOP in *. lia.
  - assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin). pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & R & _).
    apply HW. left. clear - R H1 H2 Hx LOW LOR. unfold e_sp1, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
Qed.

Theorem NGETS_proof : NGETS_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof using AF AFP libenv_agree libenv_fp_where errst_rest_agree errst_fp_where C_BG H_R2 H_HD.
  unfold NGETS_stmt.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6
    LB2 namev nn hBv dBv bn junk KX KY methX methY maxX maxY
    COMMON ERR_REST CREDIT LIVEROOM FRAME FFCELLS OUTNULL LB2_ALIGN JUNK_LEN JUNK_CELLS NAME_ALIGN NAME_RANGE NAME_LEN NAME_CELLS NAME_NUL
    MBX MBY MAXX0 MAXY0.
  subst maxX maxY.
  pose proof COMMON as (ART0 & MEMOK & STACKOK & PADV & PLMOD & PLTOP & SP0LO & LOWROOM & LOGLOB & CANARY & SECOFF & LIBE & LBLSUB & EIN & ENOTLBL & CUROUT
     & MBIOK & OFFR & BLENR & KLV & PERM & CURFRESH & NODUPC & LPOS & FRAMES & FRN & SP0EQ & CGEQ & LIVEROOM2 & LRPOS & CREDR & CREMPOS & CREDOK
     & CGHAS & CGSUB & CGCTX & UWC & FPOS & FMOD & FTOP & FSEG & FSHI & FSH & SAVED & PRES & FLAGR & NDOUT & OUTS & FDOUT & MSTA).
  pose proof MSTA as MST.
  intros T c0 ENTRY KONT.
  pose proof FRAME as (FR0 & FRH & FRHS & FRF & FRFS & FREND & FRE & FRX & FRGAP).
  pose proof (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COMMON) as (EUSP & CALLOK & LBLIVE & FRLT & CRLE & LOSP & SPPL).
  assert (SPLO : 0 <= e_sp1 RT en) by (clear - LOWROOM LOGLOB; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SPHI : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - SPPL PLTOP; unfold USTACK_TOP in *; lia).
  unfold loc_E in FRE.
  pose proof (ng1_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
       (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) t3 t4 t5 t6 F fc m _ _ _ _ _ _ _ _ _ _ _ _ _ _
       SPLO SPHI MEMOK FRE) as WALK1.
  assert (WALK1' : forall ms, eq (pem_ms en J_NGETS m F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) t3 t4 t5 t6) ms ->
            evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
              ms' = MS (mkR (wz SITE_ng_gets) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0' t1' t2' (e_sp RT en) (wz (e_sp1 RT en))
                          (wz (e_BI RT en)) (wz LB2) (wz 255) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) t3' t4' t5' t6')
                       F (wz FZ_BIO_GETS) fc None m (seg_rom asegs) /\ True) ms)
    by (intros ms <-; exact WALK1).
  apply (cps_realizes asegs _ _ T c0 (asta_evt' RT AF Σ (e_PMc RT en) _ _ MST WALK1') ENTRY).
  clear WALK1 WALK1' ENTRY. intros c1 STEP1.
  destruct (ASTA_unpack RT Σ _ _ _ STEP1) as (ms1 & (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & MS1 & _) & AT1).
  clear STEP1. subst ms1.
  assert (POT : 0 <= grow_pot RT en 0 0).
  { apply (grow_pot_nonneg RT en 0 0 0 0 off OFFR); try lia; vm_compute gr_n; lia. }
  assert (CR1 : 1 <= crem) by (clear - CREDIT POT OFFR; unfold gn_need, C_END in CREDIT; lia).
  assert (LBCUR : In (LB2, 256) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(LB2, 256); (namev, nn)]))
    by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (SITER : 0 <= SITE_ng_gets < 2 ^ 64) by (unfold SITE_ng_gets; lia).
  assert (SITEV : SITE_ng_gets mod 2 = 0) by reflexivity.
  change (MS (mkR (wz SITE_ng_gets) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) u0 u1 u2 (e_sp RT en) (wz (e_sp1 RT en))
             (wz (e_BI RT en)) (wz LB2) (wz 255) b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) v3 v4 v5 v6)
             F (wz FZ_BIO_GETS) fc None m (seg_rom asegs))
    with (pem_ms en FZ_BIO_GETS m F fc (wz SITE_ng_gets) u0 u1 u2 (wz (e_BI RT en)) (wz LB2) (wz 255) b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) v3 v4 v5 v6) in AT1.
  apply (pem_call_bgets RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BG
           T en Σ m off crem lrem _ LB2 junk SITE_ng_gets F fc u0 u1 u2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) v3 v4 v5 v6 c1
           COMMON LBCUR LB2_ALIGN JUNK_LEN JUNK_CELLS CR1 SITER SITEV AT1).
  intros Σ2 m2 F2 fc2 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 k off2 bs2
    COM2 LIVE2 FRAMES2 PRES2 BSLEN BSCELLS KCASE AT2.
  pose proof (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COMMON) as (ELIVE & CURLIVE).
  assert (EINL : In (e_E RT en, 904) (rt_live RT Σ)) by exact (ELIVE _ EIN).
  assert (ENOTK : ~ In (e_E RT en, 904) (mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros HIN. pose proof (in_map fst _ _ HIN) as HM. rewrite mbio_ent_fst in HM. cbn [fst] in HM.
    exact (CUROUT (e_E RT en, 904) (or_introl eq_refl) (in_or_app _ _ _ (or_introl HM))). }
  assert (WOK : w_ok RT en Σ ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))
                  ((LB2, LB2 + 256) :: mbio_W (e_K RT en) (e_bmax RT en))).
  { change ((LB2, LB2 + 256) :: mbio_W (e_K RT en) (e_bmax RT en))
      with (map rng ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
    apply (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COMMON).
    intros e [<- | HIN]; [left; split; [exact LBCUR | cbn; lia] | right; exact HIN]. }
  destruct WOK as (WSTK & WFRM & WFF & WFSH & WLIVE & WACL).
  assert (EOUT : forall x, e_E RT en <= x < e_E RT en + 904 -> outside ((LB2, LB2 + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) x).
  { intros x Hx. refine (WLIVE _ _ x EINL _ Hx). intros [HEQ | HIN]; [inversion HEQ | exact (ENOTK HIN)]. }
  pose proof (mbio_ent_fst KX 0) as FKX.
  pose proof (mbio_ent_fst KY 0) as FKY.
  pose proof (mbio_ent_fst (e_K RT en) (e_bmax RT en)) as FKE.
  pose proof NODUPC as NDALL. rewrite !map_app, FKX, FKY in NDALL. cbn [map fst] in NDALL.
  destruct (nd_split _ _ NDALL) as (NDC & _ & SEPC).
  assert (ADDR : forall p n, In (p, n) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(namev, nn)]) ->
                   In p ((mbio_blocks KX ++ mbio_blocks KY) ++ [namev])).
  { intros p n HIN. rewrite <- app_assoc. apply in_app_or in HIN. destruct HIN as [H | H].
    - apply in_or_app; left. rewrite <- FKX. exact (in_map fst _ _ H).
    - apply in_app_or in H. destruct H as [H | H].
      + apply in_or_app; right; apply in_or_app; left. rewrite <- FKY. exact (in_map fst _ _ H).
      + destruct H as [HEQ | []]. injection HEQ as -> _. apply in_or_app; right; apply in_or_app; right; left; reflexivity. }
  assert (LBNOT : ~ In LB2 ((mbio_blocks KX ++ mbio_blocks KY) ++ [namev])).
  { intros HBAD.
    assert (NDP : List.NoDup (LB2 :: ((mbio_blocks KX ++ mbio_blocks KY) ++ [namev]))).
    { apply (Permutation_NoDup (l := mbio_blocks KX ++ mbio_blocks KY ++ [LB2; namev])); [| exact NDC].
      rewrite app_assoc. apply Permutation_sym, Permutation_middle. }
    exact (proj1 (proj1 (NoDup_cons_iff LB2 _) NDP) HBAD). }
  assert (NOTXL : forall p n, In (p, n) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(namev, nn)]) ->
                    ~ In (p, n) ((LB2, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros p n HIN HBAD. pose proof (ADDR p n HIN) as HP. destruct HBAD as [HEQ | HK].
    - injection HEQ as -> _. exact (LBNOT HP).
    - pose proof (in_map fst _ _ HK) as HKM. rewrite FKE in HKM. cbn [fst] in HKM.
      refine (SEPC p _ (or_intror HKM)). rewrite <- app_assoc in HP.
      apply in_app_or in HP. destruct HP as [H | H]; [apply in_or_app; left; exact H|].
      apply in_app_or in H. destruct H as [H | H]; [apply in_or_app; right; apply in_or_app; left; exact H|].
      apply in_or_app; right; apply in_or_app; right; right; exact H. }
  assert (CURIN : forall p n, In (p, n) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(namev, nn)]) ->
                    In (p, n) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(LB2, 256); (namev, nn)])).
  { intros p n HIN. apply in_app_or in HIN. destruct HIN as [H | H]; [apply in_or_app; left; exact H|].
    apply in_app_or in H. destruct H as [H | H]; [apply in_or_app; right; apply in_or_app; left; exact H|].
    apply in_or_app; right; apply in_or_app; right; right; exact H. }
  assert (CUROUTW : forall p n x, In (p, n) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(namev, nn)]) -> p <= x < p + n ->
                      outside ((LB2, LB2 + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) x).
  { intros p n x HIN Hx. exact (WLIVE p n x (CURLIVE _ (CURIN p n HIN)) (NOTXL p n HIN) Hx). }
  assert (ERR2 : errst_at_rest (e_E RT en) [] m2).
  { refine (rest_keep_n en Σ m m2 off crem lrem _ (rt_live RT Σ2) _ COMMON ERR_REST PRES2 _ EOUT).
    rewrite LIVE2. exact EINL. }
  assert (FRAME2 : pem_frame en m2 j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap)
    by exact (pem_frame_keep RT en m m2 _ _ _ _ _ _ _ _ _ _ _ _ FRAME PRES2 PADV PLTOP WSTK).
  assert (FFCELLS2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
  { refine (ff_keep m m2 (e_f RT en) (rt_live RT Σ2) (rt_frames RT Σ) (e_sp1 RT en) _ _ _ _ _ _ _ _ FFCELLS PRES2 _ WFF).
    rewrite FRAMES. left. reflexivity. }
  assert (NAMECELLS2 : rw_cells asegs m2 namev [CB (Z.to_nat nn) bn]).
  { refine (cells_keep m m2 namev nn namev _ (rt_live RT Σ2) (rt_frames RT Σ) (e_sp1 RT en) _ NAME_CELLS PRES2 _ _ _ _).
    - rewrite LIVE2. apply CURLIVE, CURIN. apply in_or_app; right; apply in_or_app; right; left; reflexivity.
    - lia.
    - cbn [cells_size csize]. lia.
    - intros x Hx. refine (CUROUTW namev nn x _ _).
      + apply in_or_app; right; apply in_or_app; right; left; reflexivity.
      + cbn [cells_size csize] in Hx. lia. }
  assert (PAGREE : forall P, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> agree_on (fun x => P <= x < P + 8) m m2)
    by exact (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m2 off crem lrem _ (rt_live RT Σ2) _ COMMON WSTK WFRM PRES2).
  assert (OUTNULL2 : out_null RT en m2).
  { pose proof OUTNULL as (ON1 & ON2 & ON3 & ON4). unfold out_null.
    assert (KEEPC : forall P (v : word), In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 v] -> rw_cells asegs m2 P [C8 v]).
    { intros P v HP (HC & HW). split.
      - exact (cells_at_agree asegs m m2 P [C8 v] HC (PAGREE P HP)).
      - exact (wr_at_agree_nw asegs m m2 P 8 HW (PAGREE P HP)). }
    split; [| split; [| split]].
    - exact (KEEPC _ _ (or_introl eq_refl) ON1).
    - exact (KEEPC _ _ (or_intror (or_introl eq_refl)) ON2).
    - exact (KEEPC _ _ (or_intror (or_intror (or_introl eq_refl))) ON3).
    - exact (KEEPC _ _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) ON4). }
  assert (MBKEEP : forall (K : mbk) (BI meth : Z), mbio_rep (rt_live RT Σ) m K BI meth 0 0 0 ->
                     (forall e, In e (mbio_ent K 0) -> In e (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(namev, nn)])) ->
                     mbio_rep (rt_live RT Σ2) m2 K BI meth 0 0 0).
  { intros K BI meth MB HSUB.
    refine (mbio_rep_keep (rt_live RT Σ) (rt_live RT Σ2) m m2 K BI meth 0 0 0 (rt_live RT Σ2) (rt_frames RT Σ) (e_sp1 RT en) _ MB PRES2 _ _).
    - intros e HE. destruct e as (p, n). pose proof (CURLIVE _ (CURIN p n (HSUB _ HE))) as HL.
      rewrite LIVE2. split; exact HL.
    - intros e x HE Hx. destruct e as (p, n). exact (CUROUTW p n x (HSUB _ HE) Hx). }
  assert (MBX2 : mbio_rep (rt_live RT Σ2) m2 KX hBv methX 0 0 0).
  { refine (MBKEEP KX hBv methX MBX _). intros e HE. apply in_or_app; left; exact HE. }
  assert (MBY2 : mbio_rep (rt_live RT Σ2) m2 KY dBv methY 0 0 0).
  { refine (MBKEEP KY dBv methY MBY _). intros e HE. apply in_or_app; right; apply in_or_app; left; exact HE. }
  assert (GCAP : 65536 <= grow_cap RT en).
  { unfold grow_cap. assert (PLEN : 0 <= 2 * e_plen RT en + 8) by (unfold e_plen; lia).
    assert (G1 : 0 <= gr_n (2 * e_plen RT en + 8)) by (unfold gr_n; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
    assert (G2 : 0 <= gr_n (2 * e_plen RT en + 8) / 4) by (apply Z.div_pos; lia).
    lia. }
  assert (POT1 : 655360 <= grow_pot RT en 0 0) by (unfold grow_pot; lia).
  destruct KCASE as [(KZERO & OFFSAME & OFFEND) | (KRANGE & KNUL & KNL & OFFADV)].
  - subst k. subst off2.
    assert (WALK0' : forall ms, eq (pem_ms en SITE_ng_gets m2 F2 fc2 (wz SITE_ng_gets) y0 y1 y2 (wz 0) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) y3 y4 y5 y6) ms ->
              evt asegs (fun ms' => ms' = pem_ms en J_RAISE2 m2 F2 fc2 (wz SITE_ng_gets) y0 y1 y2 (wz 0) d1 d2 d3 d4 d5 d6 d7 (wz 854) s3 s4 s5 s6 s7 (wz namev) (wz LB2) y3 y4 y5 y6 /\ True) ms)
      by (intros ms <-; exact (ng2_walk0 (wz SITE_ng_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7
            (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) y3 y4 y5 y6 F2 fc2 m2 (proj1 (proj2 COM2)))).
    apply (cps_realizes asegs _ _ T c2 (asta_evt' RT AF Σ2 (e_PMc RT en) _ _ MST WALK0') AT2).
    clear AT2 WALK0'. intros c3 STEP3.
    destruct (ASTA_unpack RT Σ2 _ _ _ STEP3) as (ms3 & (MS3 & _) & AT3). clear STEP3. subst ms3.
    refine (H_R2 en Σ2 m2 off (crem - 1) lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_ng_gets) y0 y1 y2 (wz 0) d1 d2 d3 d4 d5 d6 d7
              s3 s4 s5 s6 s7 y3 y4 y5 y6 LB2 namev nn hBv dBv 854 bn bs2 KX KY methX methY 0 0 0 0
              COM2 ERR2 _ _ _ FRAME2 FFCELLS2 OUTNULL2 LB2_ALIGN BSLEN BSCELLS NAME_ALIGN NAME_RANGE NAME_LEN NAMECELLS2 MBX2 MBY2 T c3 AT3 KONT).
    + unfold C_END. unfold gn_need, C_END in CREDIT. lia.
    + lia.
    + lia.
  - pose proof FRAME2 as (FR0' & FRH' & FRHS' & FRF' & FRFS' & FREND' & FRE' & FRX' & FRGAP').
    assert (HSZ : cells_size lH = 56%nat) by lia.
    assert (SLOTS2 : rw_cells asegs m2 (e_sp1 RT en + 24) [CB 56 (cells_bytes lH)]).
    { pose proof (rw_cells_blur m2 (e_sp1 RT en + 24) lH []) as HB.
      rewrite app_nil_r, HSZ in HB. exact (HB FRH'). }
    pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB2, 256) COMMON LBCUR ltac:(cbn; lia))
      as (_ & LBPOS & LBLO & _ & _).
    cbn [fst snd] in LBPOS, LBLO.
    assert (LBSP : LB2 + 256 <= e_sp1 RT en) by (clear - LBLO LOWROOM; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
    assert (KLE : 1 <= k <= 254) by (clear - KRANGE; pose proof (Z.le_min_r (e_blen RT en - off) 254); lia).
    unfold loc_E in FRE'.
    pose proof (ng2_walk (wz SITE_ng_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7
         s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz namev) y3 y4 y5 y6 F2 fc2 m2 k LB2 endv (cells_bytes lH)
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ SPLO SPHI KLE LBPOS LBSP (proj1 (proj2 COM2)) SLOTS2 FREND' FRE') as WALK2.
    assert (WALK2' : forall ms, eq (pem_ms en SITE_ng_gets m2 F2 fc2 (wz SITE_ng_gets) y0 y1 y2 (wz k) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 (wz namev) (wz LB2) y3 y4 y5 y6) ms ->
              evt asegs (ng2_post (e_sp1 RT en) (e_gp RT en) (e_sp RT en) s3 (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz hBv) F2 fc2 k LB2 m2) ms)
      by (intros ms <-; exact WALK2).
    apply (cps_realizes asegs _ _ T c2 (asta_evt' RT AF Σ2 (e_PMc RT en) _ _ MST WALK2') AT2).
    clear AT2 WALK2 WALK2'. intros c3 STEP3.
    destruct (ASTA_unpack RT Σ2 _ _ _ STEP3) as (ms3 & (r3 & z0 & z1 & z2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m3 & MS3 & MEM3 & WMO3 & MUN3 & HSLOT3 & HEND3) & AT3).
    clear STEP3. subst ms3.
    pose proof (stk_win_facts en Σ2 m2 off2 (crem - 1) lrem _
         [(e_sp1 RT en + 24, e_sp1 RT en + 80); (e_sp1 RT en + 104, e_sp1 RT en + 112)] COM2
         ltac:(clear - SPPL; cbn; intros x [Hx | Hx]; repeat split; lia)) as (SWLIVE & SWFF & SWP).
    assert (KEEP3 : forall A cs, rw_cells asegs m2 A cs ->
              (forall x, A <= x < A + Z.of_nat (cells_size cs) ->
                 outside [(e_sp1 RT en + 24, e_sp1 RT en + 80); (e_sp1 RT en + 104, e_sp1 RT en + 112)] x) ->
              rw_cells asegs m3 A cs).
    { intros A cs (HC & HW) HO. split.
      - exact (cells_at_agree asegs m2 m3 A cs HC (fun a Ha => MUN3 a (HO _ Ha))).
      - exact (wr_at_agree_nw asegs m2 m3 A _ HW (fun a Ha => MUN3 a (HO _ Ha))). }
    assert (LIVE3 : forall A cs p n, rw_cells asegs m2 A cs -> In (p, n) (rt_live RT Σ2) ->
              p <= A -> A + Z.of_nat (cells_size cs) <= p + n -> rw_cells asegs m3 A cs).
    { intros A cs p n HR HL HA HB. refine (KEEP3 A cs HR _). intros x Hx. exact (SWLIVE p n x HL ltac:(lia)). }
    assert (STK3 : stk asegs m3 (e_lo RT en) (e_sp1 RT en)).
    { refine (stk_munch _ m2 m3 _ _ (proj1 (proj2 (proj2 COM2))) MUN3 WMO3 _).
      clear. cbn. intros x Hx. repeat split; lia. }
    assert (COM3 : pem_com en Σ2 m3 off2 (crem - 1) lrem (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(LB2, 256); (namev, nn)])).
    { refine (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ2 m2 m3 off2 (crem - 1) lrem _ _ COM2 MUN3 WMO3 MEM3 STK3 _).
      apply Forall_cons; [left; cbn [fst snd]; clear - SPPL; lia|].
      apply Forall_cons; [left; cbn [fst snd]; clear - SPPL; lia| apply Forall_nil]. }
    assert (ERR3 : errst_at_rest (e_E RT en) [] m3).
    { refine (rest_keep_n en Σ2 m2 m3 off2 (crem - 1) lrem _ (rt_live RT Σ2) _ COM2 ERR2 _ _ _).
      - exact (pres_fp_of_munch _ _ _ _ _ _ _ MUN3 (fun x _ H => H)).
      - rewrite LIVE2. exact EINL.
      - intros x Hx. refine (SWLIVE (e_E RT en) 904 x _ Hx). rewrite LIVE2. exact EINL. }
    assert (FRAME3 : pem_frame en m3 j0 (loc_H LB2 hBv) (loc_F RT en) (wz 0) hBv dBv x1 x2 gap).
    { unfold pem_frame, loc_H. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      - refine (KEEP3 _ _ FR0' _). cbn [cells_size csize]. intros x Hx. cbn. clear - Hx; repeat split; lia.
      - exact HSLOT3.
      - cbn [cells_size csize]. reflexivity.
      - refine (KEEP3 _ _ FRF' _). rewrite FRFS'. intros x Hx. cbn. clear - Hx; repeat split; lia.
      - exact FRFS'.
      - exact HEND3.
      - refine (KEEP3 _ _ FRE' _). cbn [cells_size csize]. intros x Hx. cbn. clear - Hx; repeat split; lia.
      - refine (KEEP3 _ _ FRX' _). cbn [cells_size csize]. intros x Hx. cbn. clear - Hx; repeat split; lia.
      - refine (KEEP3 _ _ FRGAP' _). cbn [cells_size csize]. intros x Hx. cbn.
        assert (PDR : Z.of_nat (Z.to_nat (e_pd RT en)) <= 16) by (clear - PADV; lia). clear - Hx PDR; repeat split; lia. }
    assert (FFCELLS3 : rw_cells asegs m3 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
    { refine (KEEP3 _ _ FFCELLS2 _). intros x Hx. refine (SWFF x _).
      unfold ff_cells in Hx. cbn [cells_size csize] in Hx. lia. }
    assert (OUTNULL3 : out_null RT en m3).
    { pose proof OUTNULL2 as (ON1 & ON2 & ON3 & ON4). unfold out_null.
      assert (PK : forall P (v : word), In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m2 P [C8 v] -> rw_cells asegs m3 P [C8 v]).
      { intros P v HP HR. refine (KEEP3 _ _ HR _). cbn [cells_size csize]. intros x Hx. exact (SWP P x HP ltac:(lia)). }
      split; [| split; [| split]].
      - exact (PK _ _ (or_introl eq_refl) ON1).
      - exact (PK _ _ (or_intror (or_introl eq_refl)) ON2).
      - exact (PK _ _ (or_intror (or_intror (or_introl eq_refl))) ON3).
      - exact (PK _ _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) ON4). }
    assert (BSCELLS3 : rw_cells asegs m3 LB2 [CB 256 bs2]).
    { refine (LIVE3 _ _ LB2 256 BSCELLS _ ltac:(lia) _); [| cbn [cells_size csize]; lia].
      rewrite LIVE2. exact (CURLIVE _ LBCUR). }
    assert (NAMECELLS3 : rw_cells asegs m3 namev [CB (Z.to_nat nn) bn]).
    { refine (LIVE3 _ _ namev nn NAMECELLS2 _ ltac:(lia) _); [| cbn [cells_size csize]; lia].
      rewrite LIVE2. refine (CURLIVE _ _). apply in_or_app; right; apply in_or_app; right; right; left; reflexivity. }
    assert (MB3 : forall (K : mbk) (BI meth : Z), mbio_rep (rt_live RT Σ2) m2 K BI meth 0 0 0 ->
                    (forall e, In e (mbio_ent K 0) -> In e (rt_live RT Σ2)) -> mbio_rep (rt_live RT Σ2) m3 K BI meth 0 0 0).
    { intros K BI meth MB HSUB. refine (mbio_rep_agree _ m2 m3 K BI meth 0 0 0 MB _).
      intros a (e & HE & HR). destruct e as (p, n). exact (MUN3 a (SWLIVE p n _ (HSUB _ HE) HR)). }
    assert (MBX3 : mbio_rep (rt_live RT Σ2) m3 KX hBv methX 0 0 0).
    { refine (MB3 KX hBv methX MBX2 _). intros e HE. rewrite LIVE2. refine (CURLIVE _ _).
      apply in_or_app; left; exact HE. }
    assert (MBY3 : mbio_rep (rt_live RT Σ2) m3 KY dBv methY 0 0 0).
    { refine (MB3 KY dBv methY MBY2 _). intros e HE. rewrite LIVE2. refine (CURLIVE _ _).
      apply in_or_app; right; apply in_or_app; left; exact HE. }
    pose proof (mbio_ent_len0 _ _ _ _ _ _ _ MBX3) as LENX.
    pose proof (mbio_ent_len0 _ _ _ _ _ _ _ MBY3) as LENY.
    change (MS (mkR r3 (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) g0 g1 g2 g3 g4 g5 g6 g7
               (wz hBv) s3 (wz 0) (wz k) (wz 0) (wz 0) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) w3 w4 w5 w6)
               F2 (wz J_HD) fc2 None m3 (seg_rom asegs))
      with (pem_ms en J_HD m3 F2 fc2 r3 z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 (wz hBv) s3 (wz 0) (wz k) (wz 0) (wz 0) (wz namev) (wz LB2) w3 w4 w5 w6) in AT3.
    refine (H_HD (e_blen RT en - off2) en Σ2 m3 off2 (crem - 1) lrem j0 (wz 0) (wz 0) x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2
              r3 z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 s3 w3 w4 w5 w6 LB2 namev nn hBv dBv hBv k 0 0 bn bs2 KX KY methX methY 0 0 0 0
              ltac:(lia) _ _ KNUL ltac:(lia) _ _ T c3 AT3 KONT).
    + refine (conj COM3 (conj ERR3 (conj _ (conj (conj _ _) (conj FRAME3 (conj FFCELLS3 (conj OUTNULL3
        (conj LB2_ALIGN (conj BSLEN (conj BSCELLS3 (conj NAME_ALIGN (conj NAME_RANGE (conj NAME_LEN (conj NAMECELLS3
        (conj NAME_NUL (conj MBX3 (conj MBY3 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))))))))).
      * clear - CREDIT POT1 OFFADV KLE OFFR. unfold hd_need, gn_need, C_END in *. lia.
      * clear - LIVEROOM. lia.
      * rewrite LENX, LENY. clear - LIVEROOM. lia.
      * lia.
      * intros _. repeat split; reflexivity.
      * intros HG2. exfalso. clear - HG2. lia.
      * left. reflexivity.
      * clear - OFFR OFFADV KLE. lia.
      * vm_compute gr_n. lia.
      * vm_compute gr_n. lia.
    + clear - KLE; lia.
    + intros HLEN HOFF. refine (KNL _). clear - HLEN HOFF OFFADV; lia.
    + clear - OFFR OFFADV KLE; lia.
Qed.
End CNgets.
