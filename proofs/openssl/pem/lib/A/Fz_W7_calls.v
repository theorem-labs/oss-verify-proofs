(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_libiface_pem D_agree D_clx PLayout I_lkit I_ut Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_aux4 Fz_G_kit Fz_W7_defs Fz_W7_segs Fz_W7_inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Lemma not_outside_app : forall (W1 W2 : list (Z * Z)) x, ~ outside (W1 ++ W2) x -> ~ outside W1 x \/ ~ outside W2 x.
Proof.
  intros W1 W2 x H. destruct (outside_dec W1 x) as [O1|O1]; [| left; exact O1]. destruct (outside_dec W2 x) as [O2|O2]; [| right; exact O2].
  exfalso. exact (H (outside_app_intro W1 W2 x O1 O2)).
Qed.
Lemma not_outside_ranges : forall (W : list (Z * Z)) x, ~ outside W x -> in_ranges W x.
Proof.
  intros W x. induction W as [|[lo hi] W IH]; intros H; [exfalso; apply H; exact I|].
  destruct (wg_not_outside_cons lo hi W x H) as [R|R]; [exists lo, hi; split; [left; reflexivity| exact R]|].
  destruct (IH R) as (lo' & hi' & Hin & R'). exists lo', hi'. split; [right; exact Hin| exact R'].
Qed.
Lemma not_outside_blocks : forall (l : list (Z * Z)) x, ~ outside (map (fun e => (fst e, fst e + snd e)) l) x -> in_live l x.
Proof.
  intros l x H. destruct (not_outside_ranges _ _ H) as (lo & hi & Hin & R). apply in_map_iff in Hin. destruct Hin as ([p n] & E & Hpn).
  injection E as <- <-. exists p, n. split; [exact Hpn| exact R].
Qed.

(* [comment removed for export] *)
Definition sfn_post (ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma sfn_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m -> mem_inv asegs m ->
  evt asegs (sfn_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_secure_free) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT MI. unfold e_CRYPTO_secure_free in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 48, SP)]) by sh_fp_lia.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 5 zstep. zstep.
  zstep. if_true.
  do 5 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sfn_post. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma nd_app : forall (l1 l2 : list Z), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> List.NoDup (l1 ++ l2).
Proof.
  intros l1 l2 N1 N2 DJ. induction l1 as [|x l1 IH]; cbn; [exact N2|].
  inversion N1 as [|y l NI N1']; subst. constructor.
  - intros X. apply in_app_iff in X. destruct X as [X|X]; [exact (NI X)| exact (DJ x (or_introl eq_refl) X)].
  - apply IH; [exact N1'| intros z Hz1 Hz2; exact (DJ z (or_intror Hz1) Hz2)].
Qed.

(* [comment removed for export] *)
Lemma w7_shadow_byte4 : forall (m : mem) s, rw_cells asegs m s w7_shadow_live ->
  bytes_at asegs m (s + 4) [z8] /\ bytes_at asegs m (s + 8) [z8] /\ bytes_at asegs m (s + 12) [z8] /\ bytes_at asegs m (s + 16) [z8].
Proof.
  intros m s H. unfold w7_shadow_live in H. cbn [map] in H. pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes app] in B. unfold z8.
  pose proof (proj2 (proj1 (bytes_at_app _ m s [Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15)] _) B)) as B4. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in B4.
  pose proof (proj2 (proj1 (bytes_at_app _ m (s + 4) [Z_to_bv 8 0; Z_to_bv 8 (-14); Z_to_bv 8 (-14); Z_to_bv 8 (-14)] _) B4)) as B8. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in B8.
  replace (s + 4 + 4) with (s + 8) in B8 by lia.
  pose proof (proj2 (proj1 (bytes_at_app _ m (s + 8) [Z_to_bv 8 0; Z_to_bv 8 (-14); Z_to_bv 8 (-14); Z_to_bv 8 (-14)] _) B8)) as B12. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in B12.
  replace (s + 8 + 4) with (s + 12) in B12 by lia.
  pose proof (proj2 (proj1 (bytes_at_app _ m (s + 12) [Z_to_bv 8 0; Z_to_bv 8 (-14); Z_to_bv 8 (-14); Z_to_bv 8 (-14)] _) B12)) as B16. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in B16.
  replace (s + 12 + 4) with (s + 16) in B16 by lia.
  split; [exact (proj1 (proj1 (bytes_at_app _ m (s + 4) [Z_to_bv 8 0] _) B4))|].
  split; [exact (proj1 (proj1 (bytes_at_app _ m (s + 8) [Z_to_bv 8 0] _) B8))|].
  split; [exact (proj1 (proj1 (bytes_at_app _ m (s + 12) [Z_to_bv 8 0] _) B12))| exact (proj1 (proj1 (bytes_at_app _ m (s + 16) [Z_to_bv 8 0] _) B16))].
Qed.

Section W7C.
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
Variable LIB : list (Z * Z) -> mem -> Prop.
Variable REST : mem -> Prop.
Variable REST_fp : Z -> Prop.
Hypothesis REST_agree : forall m m', REST m -> agree_on REST_fp m m' -> REST m'.
Hypothesis REST_fp_where : forall a, REST_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.

Local Notation w7a := (w7a RT).
Local Notation w7_com := (w7_com RT libenv FZ_SITES FZ_CALLS REST).
Local Notation w7_winok := (w7_winok RT).
Local Notation P5 x := (x RT libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P6 x := (x RT AF libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P7 x := (x RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation PK x := (x RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where) (only parsing).

(* [comment removed for export] *)
Definition w7_cs (en : w7a) (pc : Z) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : machine_state :=
  MS (mkR ra (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma winok_libW : forall (en : w7a) Σ m crem cur, w7_com en Σ m crem cur -> w7_winok en cur (lib_W (a_LBL RT en)).
Proof.
  intros en Σ m crem cur COM a Ha.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & _).
  unfold lib_W in Ha. destruct (not_outside_app _ _ _ Ha) as [X|X]; [left; exact (not_outside_ranges _ _ X)| right; left].
  destruct (not_outside_blocks _ _ X) as (p & n & Hin & Hp). exists p, n. split; [apply in_or_app; right; exact (INCL _ Hin)| exact Hp].
Qed.

(* [comment removed for export] *)
Lemma sec_keep : forall (m m' : mem) KEEP fr sp W, sec_off m -> rt_pres_fp KEEP fr sp W m m' -> (forall a, client_static a -> outside LIB_W a -> outside W a) -> sec_off m'.
Proof.
  intros m m' KEEP fr sp W SEC PR HWS. eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
  assert (CS : client_static SEC_INIT) by exact sec_init_static.
  assert (HO : outside LIB_W SEC_INIT) by (unfold LIB_W, SEC_INIT; cbn; repeat split; try exact I; clear; lia).
  apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; exact CS| exact (HWS _ CS HO)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w7c_bnew : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS ->
  forall T (en : w7a) Σ (m : mem) crem (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem [] -> 1 <= crem ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en FZ_BIO_NEW m F fc (wz SITE_w7_bnew) t0 t1 t2 (wz M_MEM) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (K : mbk) (BI BB BM RP : Z),
     K = MBK BI BB BM RP None -> w7_com en Σ' m' (crem - 1) (mbio_ent K 0) ->
     rt_live RT Σ' = (RP, 32) :: (BM, 32) :: (BB, 16) :: (BI, 128) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) (lib_W (a_LBL RT en)) m m' ->
     mbio_rep (rt_live RT Σ') m' K BI M_MEM 0 0 0 ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en SITE_w7_bnew m' F' fc' (wz SITE_w7_bnew) y0 y1 y2 (wz BI) b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_BN T en Σ m crem F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM CRM HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ SITE_w7_bnew A_BIO_new COM ltac:(unfold W7_SITES_OWN; cbn [map]; do 2 right; left; reflexivity)
              ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 2 right; left; reflexivity)
              ltac:(unfold SITE_w7_bnew; clear; lia)) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  destruct (P7 w7_W_facts en Σ m crem _ (lib_W (a_LBL RT en)) COM (winok_libW en Σ m crem _ COM)) as (HWS & HWU & HWH & HWF & HWD).
  apply (C_BN Σ (a_PMc RT en) (wz SITE_w7_bnew) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz M_MEM) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) [RA_FUZZ] (a_canary RT en) (a_LBL RT en) (a_E RT en) M_MEM
           FDO MST eq_refl eq_refl (or_introl eq_refl) LE INCL1 ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold W7_CALLEE_STACK, BNEW_STACK in *; lia) CLE CTX1 UWC1 CGH
           ltac:(rewrite FRL; unfold FRAMES_MAX; clear; lia) ltac:(clear - LVB; lia) ltac:(clear - CRED CRM; lia) T c HA).
  intros c' (Σ' & AP & FRS' & SP' & CR' & CG'). unfold apost in AP.
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (WM1 & LE1 & (K & BI & BB & BM & RP & -> & HK & LV' & MBN))) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PR. rewrite (ret_pc_even SITE_w7_bnew) in Hc' by (unfold SITE_w7_bnew; clear; lia).
  pose proof (sec_keep m m' _ _ _ _ SEC PR HWS) as SEC1.
  (* [comment removed for export] *)
  assert (F1 : forall e, In e ([] ++ (BM, 32) :: (BB, 16) :: (BI, 128) :: rt_live RT Σ) -> fst e <> RP).
  { apply (live_fresh RT AF Σ' m' [] RP 32 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; destruct He as [<-|[<-|[<-|He]]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
  assert (F2 : forall e, In e ([(RP, 32)] ++ (BB, 16) :: (BI, 128) :: rt_live RT Σ) -> fst e <> BM).
  { apply (live_fresh RT AF Σ' m' [(RP, 32)] BM 32 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; apply in_app_iff in He; destruct He as [[<-|[]]|[<-|[<-|He]]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
  assert (F3 : forall e, In e ([(RP, 32); (BM, 32)] ++ (BI, 128) :: rt_live RT Σ) -> fst e <> BB).
  { apply (live_fresh RT AF Σ' m' [(RP, 32); (BM, 32)] BB 16 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; apply in_app_iff in He; destruct He as [[<-|[<-|[]]]|[<-|He]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
  assert (F4 : forall e, In e ([(RP, 32); (BM, 32); (BB, 16)] ++ rt_live RT Σ) -> fst e <> BI).
  { apply (live_fresh RT AF Σ' m' [(RP, 32); (BM, 32); (BB, 16)] BI 128 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; apply in_app_iff in He; destruct He as [[<-|[<-|[<-|[]]]]|He]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
  cbn [app] in F1, F2, F3, F4.
  assert (FL : forall q e, In q [BI; BB; BM; RP] -> In e (rt_live RT Σ) -> fst e <> q).
  { intros q e Hq He. destruct Hq as [<-|[<-|[<-|[<-|[]]]]]; [apply F4| apply F3| apply F2| apply F1]; do 3 right; exact He. }
  assert (ND4 : List.NoDup [BI; BB; BM; RP]).
  { apply (nd_insert1 []); [apply (nd_insert1 []); [apply (nd_insert1 []); [apply (nd_insert1 []); [constructor| intros []]|]|]|]; cbn; intros X.
    - destruct X as [X|[]]. exact (F1 (BM, 32) ltac:(left; reflexivity) (eq_sym X)).
    - destruct X as [X|[X|[]]]; [exact (F2 (BB, 16) ltac:(right; left; reflexivity) (eq_sym X))| exact (F1 (BB, 16) ltac:(right; left; reflexivity) (eq_sym X))].
    - destruct X as [X|[X|[X|[]]]]; [exact (F3 (BI, 128) ltac:(right; right; left; reflexivity) (eq_sym X))| exact (F2 (BI, 128) ltac:(right; right; left; reflexivity) (eq_sym X))| exact (F1 (BI, 128) ltac:(right; right; left; reflexivity) (eq_sym X))]. }
  subst K.
  eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' (MBK BI BB BM RP None) BI BB BM RP); [reflexivity| | exact LV'| exact FRS'| exact PR| exact MBN| exact Hc'].
  eapply (PK w7_callk en Σ Σ' m m' crem (crem - 1) [] _ _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS' SP' CG' CR');
    [clear - CRM; lia| clear; lia| intros e He; apply in_app_iff in He; destruct He as [He|He]; [exact (CLL _ He)| exact (DLV _ He)]| exact HWS| exact HWU| exact HWH| exact HWF| exact HWD| | | exact ND4| | cbn; clear; unfold FUZZ_LIVE; lia].
  - rewrite LV'. cbn [mbio_ent k_bi k_bb k_bm k_rp k_d app].
    apply (Permutation_trans (l' := [(RP, 32); (BM, 32); (BB, 16); (BI, 128)] ++ ([] ++ a_CL RT en ++ a_DRV RT en))); [exact (Permutation_app_head [(RP, 32); (BM, 32); (BB, 16); (BI, 128)] PERM)|].
    change ((BI, 128) :: (BB, 16) :: (BM, 32) :: (RP, 32) :: a_CL RT en ++ a_DRV RT en) with ([(BI, 128); (BB, 16); (BM, 32); (RP, 32)] ++ ([] ++ a_CL RT en ++ a_DRV RT en)).
    apply Permutation_app_tail. apply (Permutation_rev [(RP, 32); (BM, 32); (BB, 16); (BI, 128)]).
  - intros e He. cbn [mbio_ent k_bi k_bb k_bm k_rp k_d app] in He.
    assert (LV0 : forall e', In e' (a_CL RT en ++ a_DRV RT en) -> In e' (rt_live RT Σ)) by (intros e' He'; apply in_app_iff in He'; destruct He' as [He'|He']; [exact (CLL _ He')| exact (DLV _ He')]).
    destruct He as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; intros X; apply in_map_iff in X; destruct X as (e' & E' & He');
      first [exact (FL BI e' ltac:(left; reflexivity) (LV0 _ He') E')| exact (FL BB e' ltac:(right; left; reflexivity) (LV0 _ He') E')
            | exact (FL BM e' ltac:(right; right; left; reflexivity) (LV0 _ He') E')| exact (FL RP e' ltac:(right; right; right; left; reflexivity) (LV0 _ He') E')].
  - intros e He. rewrite LV' in He. destruct He as [<-|[<-|[<-|[<-|He]]]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w7c_write : bio_writeg_stmt RT FZ_SITES FZ_CALLS ->
  forall T (en : w7a) Σ (m : mem) crem rest K BI len max off IN n (src : list byte) site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem (mbio_ent K max ++ rest) -> mbio_rep (rt_live RT Σ) m K BI M_MEM len max off -> gr_n (len - off + n) <= 2 ^ 27 -> 0 < n < 2 ^ 31 ->
  bytes_at asegs m IN src -> length src = Z.to_nat n -> src_blk (rt_live RT Σ) IN n (mbio_blocks K) ->
  puts_cost (len - off) n max <= crem -> Z.of_nat (length rest) <= 8 ->
  In (site, e_fuzz_one_body) W7_SITES_OWN -> In (site, A_BIO_write) W7_CALLS_ALL -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en FZ_BIO_WRITE m F fc (wz site) t0 t1 t2 (wz BI) (wz IN) (wz n) a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (pd' : option Z) (max' : Z),
     w7_com en Σ' m' (crem - puts_cost (len - off) n max) (mbio_ent (mbk_data K pd') max' ++ rest) ->
     rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) (rt_frames RT Σ) (a_sp1 RT en)
                ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) m m' ->
     (forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) /\ In e (rt_live RT Σ')) ->
     mbio_rep (rt_live RT Σ') m' (mbk_data K pd') BI M_MEM (len - off + n) max' 0 -> (max' = max \/ (max < len - off + n /\ max' = gr_n (len - off + n))) -> len - off + n <= max' ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en site m' F' fc' (wz site) y0 y1 y2 (wz n) b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_BW T en Σ m crem rest K BI len max off IN n src site F fc t0 t1 t2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c
         COM MBK GRN HN SRC LSRC SB CRM R8 HS HC SR SEV HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct MBK as [BM0 MBX].
  assert (XLC : forall e, In e (mbio_ent K max) -> In e (mbio_ent K max ++ rest) /\ 0 < snd e).
  { intros e He. split; [apply in_or_app; left; exact He| exact (mbio_ent_pos _ _ _ _ _ _ _ _ _ _ MBX e He)]. }
  assert (WOK : w7_winok en (mbio_ent K max ++ rest) ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max)).
  { intros a Ha. destruct (wg_not_outside_cons _ _ _ _ Ha) as [R|X].
    - left. exists 0xb9f200, 0xb9f848. split; [unfold LIB_W; do 2 right; left; reflexivity| unfold G_ALLOW_CUST in R; clear - R; lia].
    - right; left. unfold mbio_W in X. destruct (not_outside_blocks _ _ X) as (p & n' & Hin & Hp). exists p, n'. split; [apply in_or_app; left; apply in_or_app; left; exact Hin| exact Hp]. }
  destruct (P7 w7_W_facts en Σ m crem _ _ COM WOK) as (HWS & HWU & HWH & HWF & HWD).
  destruct (P7 w7_call_pre en Σ m crem _ site A_BIO_write COM HS HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  assert (PC1 : 1 <= puts_cost (len - off) n max).
  { unfold puts_cost, mcost. destruct (max <? len - off + n); [| clear; lia]. destruct (gr_n (len - off + n) <=? 64512) eqn:E; [clear; lia| apply Z.leb_gt in E; clear - E; lia]. }
  apply (C_BW Σ (a_PMc RT en) (wz site) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz BI) (wz IN) (wz n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) [RA_FUZZ] (a_canary RT en)
           K BI M_MEM len max off IN n src FDO MST eq_refl eq_refl eq_refl eq_refl (ex_intro _ BM0 MBX) GRN HN SRC LSRC SB
           ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold W7_CALLEE_STACK, BWRITE_STACK in *; lia) CLE SEC CTX1 UWC1 CGH ltac:(rewrite FRL; unfold FRAMES_MAX; clear; lia)
           ltac:(clear - LVB; lia) ltac:(clear - CRED CRM; lia) T c HA).
  intros c' (Σ' & AP & FRS' & SP' & CR' & CG'). unfold apost in AP.
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (SEC1 & (pd' & max' & -> & HMAX & HLEN & MB1 & PL))) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PR. rewrite (ret_pc_even site SR SEV) in Hc'.
  set (KEEP := match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) in *.
  (* [comment removed for export] *)
  assert (DJK : forall q, In q (mbio_blocks K) -> ~ In q (map fst rest) /\ ~ In q (map fst (a_CL RT en ++ a_DRV RT en))).
  { intros q Hq. rewrite map_app, mbio_ent_fst in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ).
    split; [intros X; exact (DJ q Hq X)|].
    rewrite <- (mbio_ent_fst K max) in Hq. apply in_map_iff in Hq. destruct Hq as (e & <- & He). exact (CFR e ltac:(apply in_or_app; left; exact He)). }
  assert (KSUB : forall e, In e KEEP -> In e (rt_live RT Σ)) by (intros e He; subst KEEP; destruct (k_d K); [exact (live_remove_sub _ _ _ He)| exact He]).
  assert (KIN : forall e, In e (rt_live RT Σ) -> (forall d, k_d K = Some d -> fst e <> d) -> In e KEEP).
  { intros e He Hd. subst KEEP. destruct (k_d K) as [d|]; [| exact He]. apply live_remove_keep; [exact He| exact (Hd d eq_refl)]. }
  assert (RCD : forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ)).
  { intros e He. apply (Permutation_in _ (Permutation_sym PERM)). rewrite <- app_assoc. apply in_or_app; right. exact He. }
  assert (KPR : forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e KEEP).
  { intros e He. apply KIN; [exact (RCD _ He)|].
    intros d EKD X. assert (HD : In d (mbio_blocks K)) by (unfold mbio_blocks; rewrite EKD; apply in_or_app; right; left; reflexivity).
    apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (DJK _ HD) ltac:(rewrite <- X; exact (in_map fst _ _ He)))| exact (proj2 (DJK _ HD) ltac:(rewrite <- X; exact (in_map fst _ _ He)))]. }
  assert (LE1 : libenv m' (a_LBL RT en) (a_E RT en)).
  { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; apply KPR; apply in_or_app; right; apply in_or_app; left; exact (INCL _ He)|].
    intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(LW & CS & NC)|(p' & n' & Hin & Hp)].
    - cbn [outside]. split; [intros R; apply NC; exists G_ALLOW_CUST, (G_ALLOW_CUST + 1); split; [unfold CL_CELLS; do 4 right; left; reflexivity| exact R]|].
      unfold mbio_W. apply outside_intro. intros iv Hiv R. apply in_map_iff in Hiv. destruct Hiv as ([p n'] & <- & Hpn). cbn [fst snd] in R.
      pose proof (af_live_range RT AF Σ m p n' ART0 (CLV _ (proj1 (XLC _ Hpn)))) as (_ & _ & Y). pose proof (client_static_range x CS). clear - Y R H. unfold SEGTOP_A in *. lia.
    - cbn [outside]. split; [intros R; pose proof (af_live_range RT AF Σ m p' n' ART0 (CLL _ (INCL _ Hin))) as (_ & _ & Y); clear - Y R Hp; unfold G_ALLOW_CUST, SEGTOP_A in *; lia|].
      unfold mbio_W. apply outside_intro. intros iv Hiv R. apply in_map_iff in Hiv. destruct Hiv as ([p n''] & <- & Hpn). cbn [fst snd] in R.
      destruct (P6 w7_cl_apart en Σ m crem _ (p, n'') (p', n') COM (proj1 (XLC _ Hpn)) (INCL _ Hin)) as [Q|Q]; cbn [fst snd] in Q; clear - Q R Hp; lia. }
  (* [comment removed for export] *)
  assert (FIN : forall cur', cur' = mbio_ent (mbk_data K pd') max' ++ rest ->
    Permutation (rt_live RT Σ') (cur' ++ a_CL RT en ++ a_DRV RT en) -> (forall e, In e cur' -> ~ In (fst e) (map fst (a_CL RT en ++ a_DRV RT en))) ->
    List.NoDup (map fst cur') -> (forall e, In e (rt_live RT Σ') -> 0 < snd e) -> (forall e, In e KEEP -> In e (rt_live RT Σ')) -> realizes asegs c' T).
  { intros cur' -> PERM1 CFR1 ND1 LPOS1 KL.
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' pd' max'); [| exact FRS'| exact PR| intros e He; split; [exact (KPR e He)| exact (KL _ (KPR e He))]| exact MB1| exact HMAX| exact HLEN| exact Hc'].
    eapply (PK w7_callk en Σ Σ' m m' crem (crem - puts_cost (len - off) n max) _ _ KEEP _ (puts_cost (len - off) n max) COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS' SP' CG' CR');
      [clear - CRM; lia| clear; lia| intros e He; apply KPR; apply in_or_app; right; exact He| exact HWS| exact HWU| exact HWH| exact HWF| exact HWD| exact PERM1| exact CFR1| exact ND1| exact LPOS1|].
    unfold mbio_ent. rewrite !length_app. cbn [mbk_data k_bi k_bb k_bm k_rp k_d]. destruct pd'; cbn [length Nat.add]; clear - R8; unfold FUZZ_LIVE; lia. }
  pose proof MBX as (fl0 & rrw0 & numw0 & padw0 & nr0 & nw0 & _ & _ & _ & _ & NDK & _).
  assert (B4 : forall e, In e [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] -> In e (mbio_ent K max)) by (intros e He; unfold mbio_ent; apply in_or_app; left; exact He).
  destruct PL as [(EPD & EMAX & LV')|[(q & EPD & EKD & LV')|(q & d & EPD & EKD & LV')]].
  - (* [comment removed for export] *)
    subst pd' max'. apply (FIN (mbio_ent K max ++ rest)); [destruct K; reflexivity| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| intros e He; rewrite LV'; exact (KSUB e He)].
  - (* [comment removed for export] *)
    subst pd'. unfold KEEP in *. rewrite EKD in *. clear KEEP.
    pose proof (mbio_rep_dpos _ _ _ _ _ _ _ _ q MB1 ltac:(destruct K; reflexivity)) as MQ.
    assert (FQ : forall e, In e ([] ++ rt_live RT Σ) -> fst e <> q).
    { apply (live_fresh RT AF Σ' m' [] q max' (rt_live RT Σ) ART1); [rewrite LV'; reflexivity| clear - MQ; lia| intros e He; exact (LPOS e He)]. }
    cbn [app] in FQ.
    assert (PERM0 : Permutation (rt_live RT Σ) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (rest ++ a_CL RT en ++ a_DRV RT en))).
    { unfold mbio_ent in PERM. rewrite EKD, app_nil_r, <- app_assoc in PERM. exact PERM. }
    apply (FIN (([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ [(q, max')]) ++ rest)); [cbn [mbio_ent mbk_data k_bi k_bb k_bm k_rp k_d]; reflexivity| | | | |].
    + rewrite LV', <- !app_assoc. cbn [app].
      change (Permutation ((q, max') :: rt_live RT Σ) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (q, max') :: (rest ++ a_CL RT en ++ a_DRV RT en))).
      apply Permutation_cons_app. exact PERM0.
    + intros e He. rewrite <- app_assoc in He. apply in_app_iff in He. destruct He as [He|He]; [exact (CFR e ltac:(apply in_or_app; left; exact (B4 e He)))|].
      destruct He as [<-|He]; [| exact (CFR e ltac:(apply in_or_app; right; exact He))].
      cbn [fst]. intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQ e' (RCD _ ltac:(apply in_or_app; right; exact He')) E').
    + rewrite !map_app, <- !app_assoc. cbn [map fst app]. apply (nd_insert1 [k_bi K; k_bb K; k_bm K; k_rp K]).
      * unfold mbio_ent in ND. rewrite EKD, app_nil_r, map_app in ND. exact ND.
      * intros X. assert (X' : In q (map fst (mbio_ent K max ++ rest))) by (unfold mbio_ent; rewrite EKD, app_nil_r, map_app; exact X).
        apply in_map_iff in X'. destruct X' as (e' & E' & He'). exact (FQ e' (CLV _ He') E').
    + intros e He. rewrite LV' in He. destruct He as [<-|He]; [cbn; clear - MQ; lia| exact (LPOS e He)].
    + intros e He. rewrite LV'. right. exact He.
  - (* [comment removed for export] *)
    subst pd'. unfold KEEP in *. rewrite EKD in *. clear KEEP.
    pose proof (mbio_rep_dpos _ _ _ _ _ _ _ _ q MB1 ltac:(destruct K; reflexivity)) as MQ.
    assert (FQ : forall e, In e ([] ++ live_remove d (rt_live RT Σ)) -> fst e <> q).
    { apply (live_fresh RT AF Σ' m' [] q max' (live_remove d (rt_live RT Σ)) ART1); [rewrite LV'; reflexivity| clear - MQ; lia| intros e He; exact (LPOS e (live_remove_sub _ _ _ He))]. }
    cbn [app] in FQ.
    assert (HD : In d (mbio_blocks K)) by (unfold mbio_blocks; rewrite EKD; apply in_or_app; right; left; reflexivity).
    assert (ND4 : forall e, In e [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] -> fst e <> d).
    { intros e He E. unfold mbio_blocks in NDK. rewrite EKD in NDK. pose proof (nd_split _ _ NDK) as (_ & _ & DJ). apply (DJ (fst e)); [| left; exact (eq_sym E)].
      destruct He as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; [left| right; left| right; right; left| right; right; right; left]; reflexivity. }
    assert (PERM0 : Permutation (live_remove d (rt_live RT Σ)) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (rest ++ a_CL RT en ++ a_DRV RT en))).
    { apply (live_remove_split d max).
      - unfold mbio_ent in PERM. rewrite EKD, <- !app_assoc in PERM. cbn [app] in PERM.
        eapply Permutation_trans; [exact PERM|]. apply Permutation_sym.
        change (Permutation ((d, max) :: [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (rest ++ a_CL RT en ++ a_DRV RT en)) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (d, max) :: (rest ++ a_CL RT en ++ a_DRV RT en))).
        apply Permutation_middle.
      - intros e He. apply in_app_iff in He. destruct He as [He|He]; [exact (ND4 e He)|]. intros E.
        apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (DJK _ HD) ltac:(rewrite <- E; exact (in_map fst _ _ He)))| exact (proj2 (DJK _ HD) ltac:(rewrite <- E; exact (in_map fst _ _ He)))]. }
    apply (FIN (([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ [(q, max')]) ++ rest)); [cbn [mbio_ent mbk_data k_bi k_bb k_bm k_rp k_d]; reflexivity| | | | |].
    + rewrite LV', <- !app_assoc. cbn [app].
      change (Permutation ((q, max') :: live_remove d (rt_live RT Σ)) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (q, max') :: (rest ++ a_CL RT en ++ a_DRV RT en))).
      apply Permutation_cons_app. exact PERM0.
    + intros e He. rewrite <- app_assoc in He. apply in_app_iff in He. destruct He as [He|He]; [exact (CFR e ltac:(apply in_or_app; left; exact (B4 e He)))|].
      destruct He as [<-|He]; [| exact (CFR e ltac:(apply in_or_app; right; exact He))].
      cbn [fst]. intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQ e' (KPR e' ltac:(apply in_or_app; right; exact He')) E').
    + rewrite !map_app, <- !app_assoc. cbn [map fst app]. apply (nd_insert1 [k_bi K; k_bb K; k_bm K; k_rp K]).
      * unfold mbio_ent in ND. rewrite EKD, !map_app, <- !app_assoc in ND. cbn [map fst app] in ND. exact (nd_drop [k_bi K; k_bb K; k_bm K; k_rp K] _ d ND).
      * intros X. assert (X' : In q (map fst (mbio_ent K max ++ rest)) /\ q <> d).
        { apply in_app_iff in X. split.
          - unfold mbio_ent. rewrite EKD, !map_app, <- !app_assoc. cbn [map fst]. apply in_or_app. destruct X as [X|X]; [left; exact X| right; right; exact X].
          - intros ->. unfold mbio_ent in ND. rewrite EKD, !map_app, <- !app_assoc in ND. cbn [map fst] in ND.
            pose proof (nd_split [k_bi K; k_bb K; k_bm K; k_rp K] _ ND) as (_ & NDR & DJ). destruct X as [X|X]; [exact (DJ d X ltac:(left; reflexivity))|].
            cbn [app] in NDR. inversion NDR; subst. exact (H1 X). }
        destruct X' as [X' NQD]. apply in_map_iff in X'. destruct X' as (e' & E' & He'). apply (FQ e'); [| exact E'].
        apply live_remove_keep; [exact (CLV _ He')| rewrite E'; exact NQD].
    + intros e He. rewrite LV' in He. destruct He as [<-|He]; [cbn; clear - MQ; lia| exact (LPOS e (live_remove_sub _ _ _ He))].
    + intros e He. rewrite LV'. right. exact He.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma w7_icpt0 : forall (en : w7a) Σ (m m' : mem) crem cur,
  w7_com en Σ m crem cur -> ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' (a_lo RT en) (a_sp1 RT en) ->
  rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) 0 0 m m' ->
  w7_com en Σ m' crem cur /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m'.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros en Σ m m' crem cur COM ART1 MI1 ST1 PX.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & _).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m') by (intros a Ha _; apply PX; [exact Ha| clear; lia]).
  split; [| exact PR].
  assert (CLE1 : cl_env m' (Z_to_bv 8 1) (a_canary RT en)) by (eapply cl_env_pres_ex; [exact CLE| exact PX| intros x _; clear; lia]).
  assert (LE1 : libenv m' (a_LBL RT en) (a_E RT en)).
  { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (CLL _ (INCL _ He))| intros x _; exact I]. }
  pose proof (sec_keep m m' _ _ _ _ SEC PR ltac:(intros a _ _; exact I)) as SEC1.
  eapply (PK w7_callk en Σ Σ m m' crem crem cur cur (rt_live RT Σ) [] 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 eq_refl eq_refl eq_refl);
    [clear; lia| exact CR0| clear; lia| intros e He; apply in_app_iff in He; destruct He as [He|He]; [exact (CLL _ He)| exact (DLV _ He)]
    | intros a _ _; exact I| intros a _; exact I| intros a _; exact I| intros a _; exact I| intros p n a _ _; exact I| exact PERM| exact CFR| exact ND| exact LPOS| exact CURL].
Qed.

(* [comment removed for export] *)
Lemma w7c_write0 : bio_write0_stmt RT ->
  forall T (en : w7a) Σ (m : mem) crem cur n site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem cur -> - 2 ^ 31 <= n <= 0 ->
  In (site, e_fuzz_one_body) W7_SITES_OWN -> In (site, A_BIO_write) W7_CALLS_ALL -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en FZ_BIO_WRITE m F fc (wz site) t0 t1 t2 a0 a1 (wz n) a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ m' crem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m' ->
     ASTA RT Σ (a_PMc RT en) (eq (w7_cs en site m' F' fc' (wz site) y0 y1 y2 (wz 0) b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_B0 T en Σ m crem cur n site F fc t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM HN HS HC SR SEV HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ site A_BIO_write COM HS HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  apply (C_B0 Σ (a_PMc RT en) (wz site) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 a0 a1 (wz n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) (a_canary RT en) n FDO MST eq_refl eq_refl HN
           ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold W7_CALLEE_STACK, RT_STACK in *; lia) CLE T c HA).
  intros c' AP. unfold apost in AP.
  destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & WM1)) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PR. rewrite (ret_pc_even site SR SEV) in Hc'.
  eapply (Hk m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact PR| exact Hc'].
  assert (LE1 : libenv m' (a_LBL RT en) (a_E RT en)).
  { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (CLL _ (INCL _ He))| intros x _; exact I]. }
  pose proof (sec_keep m m' _ _ _ _ SEC PR ltac:(intros a _ _; exact I)) as SEC1.
  eapply (PK w7_callk en Σ Σ m m' crem crem cur cur (rt_live RT Σ) [] 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 eq_refl eq_refl eq_refl);
    [clear; lia| exact CR0| clear; lia| intros e He; apply in_app_iff in He; destruct He as [He|He]; [exact (CLL _ He)| exact (DLV _ He)]
    | intros a _ _; exact I| intros a _; exact I| intros a _; exact I| intros a _; exact I| intros p n' a _ _; exact I| exact PERM| exact CFR| exact ND| exact LPOS| exact CURL].
Qed.

(* [comment removed for export] *)
Lemma w7c_slen : strlen_icontract RT ->
  forall T (en : w7a) Σ (m : mem) crem cur s (str slack : list byte) site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem cur -> bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2 ^ 40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> 0 < s <= 2 ^ 47 ->
  s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= a_lo RT en -> checked_src RT Σ m (wz (a_sp1 RT en)) (a_lo RT en) s (Z.of_nat (length str) + 1) ->
  0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en e_strlen m F fc (wz site) t0 t1 t2 (wz s) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ m' crem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m' -> mem_inv asegs m' ->
     ASTA RT Σ (a_PMc RT en) (eq (w7_cs en site m' F' fc' (wz site) y0 y1 y2 (wz (Z.of_nat (length str))) b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros SLC T en Σ m crem cur s str slack site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM BB NZ LS SLK HS LO CK SR SE HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  assert (HLO : a_lo RT en <= a_sp1 RT en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  assert (EU : bv_unsigned (wz (a_sp1 RT en)) = a_sp1 RT en) by (apply unsigned_lit; clear - HLO HLOS TOP PD; unfold a_sp1, USTACK_TOP in *; lia).
  assert (COK : call_ok RT Σ m (wz (a_sp1 RT en)) (a_lo RT en)).
  { unfold call_ok. rewrite EU. split; [exact ST|]. split; [exact LOW|]. split; [clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia|].
    split; [clear - TOP PD; unfold a_sp1, USTACK_TOP in *; lia|]. clear - PDM PD. unfold a_sp1, a_SP in *. Z.div_mod_to_equations. lia. }
  apply (SLC Σ (a_PMc RT en) (wz site) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz s) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s str slack (a_lo RT en)
           FDO MST eq_refl BB NZ LS SLK HS (or_introl LO) CK ART0 MI COK T c HA).
  intros c' AP. unfold icpt_post in AP.
  destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PX & _) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PX. rewrite (ret_pc_even site SR SE) in Hc'.
  destruct (w7_icpt0 en Σ m m' crem cur COM ART1 MI1 ST1 PX) as [COM1 PR].
  exact (Hk m' F' fc' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM1 PR MI1 Hc').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma w7_after_free : forall (en : w7a) Σ Σ' (m m' : mem) crem rest p n,
  w7_com en Σ m crem ((p, n) :: rest) ->
  ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (a_lo RT en) (a_sp1 RT en) ->
  rt_pres (rt_live RT Σ') (rt_frames RT Σ) (a_sp1 RT en) m m' -> cl_env m' (Z_to_bv 8 1) (a_canary RT en) ->
  rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ <= rt_credit RT Σ' -> rt_cg RT Σ' = rt_cg RT Σ ->
     (w7_com en Σ' m' crem rest /\ (forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')))
  /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (a_sp1 RT en) [] m m'.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros en Σ Σ' m m' crem rest p n COM ART1 MI1 ST1 PRS CLE1 LV' FRS' SP' CR' CG'.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & _).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  pose proof (pres_fp_of_pres _ _ _ [] m m' PRS) as PR.
  assert (FP : forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> fst e <> p).
  { intros e He E. apply in_app_iff in He. destruct He as [He|He].
    - cbn [map fst] in ND. pose proof (proj1 (List.NoDup_cons_iff _ _) ND) as [NI _]. apply NI. rewrite <- E. exact (in_map fst _ _ He).
    - apply (CFR (p, n) ltac:(left; reflexivity)). cbn [fst]. rewrite <- E. exact (in_map fst _ _ He). }
  assert (KP : forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')).
  { intros e He. rewrite LV'. apply live_remove_keep; [| exact (FP e He)]. apply (Permutation_in _ (Permutation_sym PERM)). right. exact He. }
  assert (PERM1 : Permutation (rt_live RT Σ') (rest ++ a_CL RT en ++ a_DRV RT en)).
  { rewrite LV'. apply (live_remove_split p n); [exact PERM| exact FP]. }
  split; [| exact PR]. split; [| exact KP].
  assert (LE1 : libenv m' (a_LBL RT en) (a_E RT en)).
  { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; apply KP; apply in_or_app; right; apply in_or_app; left; exact (INCL _ He)| intros x _; exact I]. }
  pose proof (sec_keep m m' _ _ _ _ SEC PR ltac:(intros a _ _; exact I)) as SEC1.
  eapply (PK w7_callk en Σ Σ' m m' crem crem _ rest (rt_live RT Σ') [] 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS' SP' CG');
    [clear - CR'; lia| exact CR0| clear; lia| intros e He; apply KP; apply in_or_app; right; exact He
    | intros a _ _; exact I| intros a _; exact I| intros a _; exact I| intros a _; exact I| intros p' n' a _ _; exact I| exact PERM1| intros e He; exact (CFR e ltac:(right; exact He))
    | cbn [map fst] in ND; exact (proj2 (proj1 (List.NoDup_cons_iff _ _) ND))| intros e He; rewrite LV' in He; exact (LPOS e (live_remove_sub _ _ _ He))| cbn [length] in CURL; clear - CURL; lia].
Qed.

Lemma w7c_free : crypto_free_env_stmt RT ->
  forall T (en : w7a) Σ (m : mem) crem rest p n site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem ((p, n) :: rest) ->
  In (site, e_fuzz_one_body) W7_SITES_OWN -> In (site, A_CRYPTO_free) W7_CALLS_ALL -> In (site, e_free) W7_CALLS_ALL -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en e_CRYPTO_free m F fc (wz site) t0 t1 t2 (wz p) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ' m' crem rest -> rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (a_sp1 RT en) [] m m' -> (forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')) ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_FR T en Σ m crem rest p n site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM HS HC HCF SR SEV HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ site A_CRYPTO_free COM HS HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  assert (HCF' : In (bv_unsigned (wz site), e_free) (cg_call (rt_cg RT Σ))) by (rewrite (unsigned_lit site) by exact SR; exact (proj2 CGH _ (proj2 CGS _ HCF))).
  apply (C_FR Σ (a_PMc RT en) (wz site) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz p) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n (a_lo RT en) [RA_FUZZ] (Z_to_bv 8 1) (a_canary RT en)
           FDO MST eq_refl eq_refl (CLV _ ltac:(left; reflexivity)) ART0 MI COK CTX1 UWC1 HCF' CLE T c HA).
  intros c' (Σ' & v & AP & LV' & FRS' & SP' & CR' & CG').
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & ST1) & PRS & CLE1) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PRS. rewrite (ret_pc_even site SR SEV) in Hc'.
  destruct (w7_after_free en Σ Σ' m m' crem rest p n COM ART1 MI1 ST1 PRS CLE1 LV' FRS' SP' ltac:(clear - CR'; lia) CG') as ([COM1 KP] & PR).
  exact (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' COM1 LV' FRS' PR KP Hc').
Qed.

Lemma w7c_sfree : crypto_secure_free_env_stmt RT ->
  forall T (en : w7a) Σ (m : mem) crem rest p n site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem ((p, n) :: rest) -> 1 <= n ->
  In (site, e_fuzz_one_body) W7_SITES_OWN -> In (site, A_CRYPTO_secure_free) W7_CALLS_ALL -> In (site, e_CRYPTO_free) W7_CALLS_ALL -> In (site, e_free) W7_CALLS_ALL ->
  0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en e_CRYPTO_secure_free m F fc (wz site) t0 t1 t2 (wz p) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ' m' crem rest -> rt_live RT Σ' = live_remove p (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (a_sp1 RT en) [] m m' -> (forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')) ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_SF T en Σ m crem rest p n site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM HN HS HC HCF1 HCF2 SR SEV HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ site A_CRYPTO_secure_free COM HS HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  assert (HCF1' : In (bv_unsigned (wz site), e_CRYPTO_free) (cg_call (rt_cg RT Σ))) by (rewrite (unsigned_lit site) by exact SR; exact (proj2 CGH _ (proj2 CGS _ HCF1))).
  assert (HCF2' : In (bv_unsigned (wz site), e_free) (cg_call (rt_cg RT Σ))) by (rewrite (unsigned_lit site) by exact SR; exact (proj2 CGH _ (proj2 CGS _ HCF2))).
  apply (C_SF Σ (a_PMc RT en) (wz site) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz p) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n (a_lo RT en) [RA_FUZZ] (Z_to_bv 8 1) (a_canary RT en)
           FDO MST eq_refl eq_refl (CLV _ ltac:(left; reflexivity)) HN ART0 MI COK CTX1 UWC1 HCF1' HCF2' CLE SEC T c HA).
  intros c' (Σ' & v & AP & LV' & FRS' & SP' & CR' & CG').
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & ST1) & PRS & CLE1 & SEC1) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PRS. rewrite (ret_pc_even site SR SEV) in Hc'.
  destruct (w7_after_free en Σ Σ' m m' crem rest p n COM ART1 MI1 ST1 PRS CLE1 LV' FRS' SP' ltac:(clear - CR'; lia) CG') as ([COM1 KP] & PR).
  exact (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' COM1 LV' FRS' PR KP Hc').
Qed.

(* [comment removed for export] *)
Lemma w7c_freen : crypto_free_null_env_stmt RT ->
  forall T (en : w7a) Σ (m : mem) crem cur site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem cur ->
  In (site, e_fuzz_one_body) W7_SITES_OWN -> In (site, A_CRYPTO_free) W7_CALLS_ALL -> In (site, e_free) W7_CALLS_ALL -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en e_CRYPTO_free m F fc (wz site) t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ m' crem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m' ->
     ASTA RT Σ (a_PMc RT en) (eq (w7_cs en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_FN T en Σ m crem cur site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM HS HC HCF SR SEV HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ site A_CRYPTO_free COM HS HC SR) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  assert (HCF' : In (bv_unsigned (wz site), e_free) (cg_call (rt_cg RT Σ))) by (rewrite (unsigned_lit site) by exact SR; exact (proj2 CGH _ (proj2 CGS _ HCF))).
  apply (C_FN Σ (a_PMc RT en) (wz site) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz 0) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) [RA_FUZZ] (Z_to_bv 8 1) (a_canary RT en)
           FDO MST eq_refl eq_refl ART0 MI COK CTX1 UWC1 HCF' CLE T c HA).
  intros c' (v & AP).
  destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PRS & CLE1) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PRS. rewrite (ret_pc_even site SR SEV) in Hc'.
  pose proof (pres_fp_of_pres _ _ _ [] m m' PRS) as PR.
  eapply (Hk m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact PR| exact Hc'].
  assert (LE1 : libenv m' (a_LBL RT en) (a_E RT en)).
  { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (CLL _ (INCL _ He))| intros x _; exact I]. }
  pose proof (sec_keep m m' _ _ _ _ SEC PR ltac:(intros a _ _; exact I)) as SEC1.
  eapply (PK w7_callk en Σ Σ m m' crem crem cur cur (rt_live RT Σ) [] 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 eq_refl eq_refl eq_refl);
    [clear; lia| exact CR0| clear; lia| intros e He; apply in_app_iff in He; destruct He as [He|He]; [exact (CLL _ He)| exact (DLV _ He)]
    | intros a _ _; exact I| intros a _; exact I| intros a _; exact I| intros a _; exact I| intros p n' a _ _; exact I| exact PERM| exact CFR| exact ND| exact LPOS| exact CURL].
Qed.

(* [comment removed for export] *)
Lemma w7c_sfreen : forall T (en : w7a) Σ (m : mem) crem cur site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem cur -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en e_CRYPTO_secure_free m F fc (wz site) t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall (m' : mem) c',
     w7_com en Σ m' crem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m' ->
     ASTA RT Σ (a_PMc RT en) (eq (w7_cs en site m' F fc (wz site) t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros T en Σ m crem cur site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM SR SEV HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  assert (HLO : a_lo RT en <= a_sp1 RT en - 48) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  assert (EU : bv_unsigned (wz (a_sp1 RT en)) = a_sp1 RT en) by (apply unsigned_lit; clear - HLO HLOS TOP PD; unfold a_sp1, USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (sfn_walk (wz site) (wz (a_sp1 RT en)) (a_gp RT en) t0 t1 t2 (a_sp RT en) s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en)
                ltac:(rewrite EU; exact HLO) HLOS ltac:(rewrite EU; clear - TOP PD; unfold a_sp1, USTACK_TOP in *; lia) ltac:(rewrite EU; exact ST) UT MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1 HA.
  rewrite EU in MU1, ST1. rewrite (ret_pc_even site SR SEV) in Hc1'.
  assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m1).
  { intros a Ha _. apply MU1. cbn [outside]. split; [| exact I]. intros R.
    destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H R. lia.
    - pose proof (client_static_range _ H). clear - H0 R HLO HLOS. unfold SEGTOP_A in *. lia.
    - destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & X & _). clear - X Hp R HLO LOW. unfold RT_STACK in *. lia.
    - destruct H as (f & k & Hin & Hf). rewrite FRS in Hin. destruct Hin as [E|[]]. injection E as <- <-. change (fs_size 2) with 256 in Hf.
      destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (_ & FLO & _). clear - Hf R FLO HLO. lia.
    - destruct H as (f & k & Hin & Hf). rewrite FRS in Hin. destruct Hin as [E|[]]. injection E as <- <-.
      destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (_ & _ & _ & _ & _ & SH1 & SH2 & _).
      replace (a_f RT en + fs_size 2) with (a_f RT en + 64 * 4) in Hf by reflexivity. rewrite (shad_add64 (a_f RT en) 4 F64) in Hf. clear - Hf R SH2 HLO HLOS. lia. }
  eapply (Hk m1 c1); [| exact PR| exact Hc1'].
  eapply (w7_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where en Σ m m1 crem cur _ COM MU1 WM1 MI1 ST1).
  constructor; [| constructor]. left. cbn [fst snd]. split; [clear - HLO; lia| clear; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w7c_bfree : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS ->
  forall T (en : w7a) Σ (m : mem) crem rest K BI BM blw len max off (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem (mbio_ent K max ++ rest) -> mbio_repx (rt_live RT Σ) m K BI BM blw M_MEM len max off -> 1 <= crem ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en FZ_BIO_FREE m F fc (wz SITE_w7_bfree) t0 t1 t2 (wz BI) a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ' m' (crem - 1) rest ->
     rt_live RT Σ' = live_remove_all (mbio_blocks K) (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (a_sp1 RT en) (lib_W (a_LBL RT en)) m m' ->
     (forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')) ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en SITE_w7_bfree m' F' fc' (wz SITE_w7_bfree) y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_BF T en Σ m crem rest K BI BM blw len max off F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM MBX CRM HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ SITE_w7_bfree A_BIO_free COM ltac:(unfold W7_SITES_OWN; cbn [map]; do 16 right; left; reflexivity)
              ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 16 right; left; reflexivity)
              ltac:(unfold SITE_w7_bfree; clear; lia)) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  destruct (P7 w7_W_facts en Σ m crem _ (lib_W (a_LBL RT en)) COM (winok_libW en Σ m crem _ COM)) as (HWS & HWU & HWH & HWF & HWD).
  (* [comment removed for export] *)
  assert (KIDS : forall q, In q (mbio_blocks K) -> ~ In q (map fst rest) /\ ~ In q (map fst (a_CL RT en ++ a_DRV RT en))).
  { intros q Hq. rewrite map_app, mbio_ent_fst in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ).
    split; [intros X; exact (DJ q Hq X)|].
    rewrite <- (mbio_ent_fst K max) in Hq. apply in_map_iff in Hq. destruct Hq as (e & <- & He). exact (CFR e ltac:(apply in_or_app; left; exact He)). }
  assert (NTLK : forall e, In e (a_LBL RT en) -> ~ In (fst e) (mbio_blocks K)).
  { intros e He X. apply (proj2 (KIDS _ X)). rewrite map_app. apply in_or_app; left. exact (in_map fst _ _ (INCL _ He)). }
  apply (C_BF Σ (a_PMc RT en) (wz SITE_w7_bfree) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 (wz BI) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) [RA_FUZZ] (a_canary RT en) (a_LBL RT en) K (a_E RT en) BI BM M_MEM len max off blw
           FDO MST eq_refl eq_refl LE INCL1 NTLK MBX ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold W7_CALLEE_STACK, BFREE_STACK in *; lia) CLE SEC CTX1 UWC1 CGH
           ltac:(rewrite FRL; unfold FRAMES_MAX; clear; lia) ltac:(clear - CRED CRM; lia) T c HA).
  intros c' (Σ' & AP & LV' & FRS' & SP' & CR' & CG'). unfold apost in AP.
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & LE1 & SEC1)) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PR. rewrite (ret_pc_even SITE_w7_bfree) in Hc' by (unfold SITE_w7_bfree; clear; lia).
  assert (KP : forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')).
  { intros e He. rewrite LV'. apply live_remove_all_keep; [apply (Permutation_in _ (Permutation_sym PERM)); rewrite <- app_assoc; apply in_or_app; right; exact He|].
    intros X. apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (KIDS _ X) (in_map fst _ _ He))| exact (proj2 (KIDS _ X) (in_map fst _ _ He))]. }
  assert (PERM1 : Permutation (rt_live RT Σ') (rest ++ a_CL RT en ++ a_DRV RT en)).
  { rewrite LV'. apply (live_remove_all_split _ _ (mbio_ent K max)); [rewrite app_assoc; exact PERM| intros e He; rewrite <- (mbio_ent_fst K max); apply in_map; exact He|].
    intros e He X. apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (KIDS _ X) (in_map fst _ _ He))| exact (proj2 (KIDS _ X) (in_map fst _ _ He))]. }
  rewrite <- LV' in PR.
  eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| exact PR| exact KP| exact Hc'].
  eapply (PK w7_callk en Σ Σ' m m' crem (crem - 1) _ rest _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS' SP' CG' CR');
    [clear - CRM; lia| clear; lia| intros e He; apply KP; apply in_or_app; right; exact He| exact HWS| exact HWU| exact HWH| exact HWF| exact HWD| exact PERM1
    | intros e He; exact (CFR e ltac:(apply in_or_app; right; exact He))
    | rewrite map_app in ND; exact (proj1 (proj2 (nd_split _ _ ND)))
    | intros e He; apply LPOS; rewrite LV' in He; exact (proj1 (live_remove_all_sub _ _ _ He))
    | rewrite length_app in CURL; clear - CURL; lia].
Qed.

(* [comment removed for export] *)
Lemma w7c_eclear : err_clear_steady_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS ->
  forall T (en : w7a) Σ (m : mem) crem strs rest top bot (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem (strs ++ rest) -> errst_live (a_E RT en) top bot strs m -> 1 <= crem ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en FZ_ERR_CLEAR m F fc (wz SITE_w7_eclear) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     w7_com en Σ' m' (crem - 1) rest -> errst_at_rest (a_E RT en) [] m' ->
     rt_live RT Σ' = live_remove_all (map fst strs) (rt_live RT Σ) -> rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (a_sp1 RT en) ((a_E RT en, a_E RT en + 904) :: lib_W (a_LBL RT en)) m m' ->
     (forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')) ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en SITE_w7_eclear m' F' fc' (wz SITE_w7_eclear) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_EC T en Σ m crem strs rest top bot F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM EL CRM HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_call_pre en Σ m crem _ SITE_w7_eclear A_ERR_clear_error COM ltac:(unfold W7_SITES_OWN; cbn [map]; do 17 right; left; reflexivity)
              ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 17 right; left; reflexivity)
              ltac:(unfold SITE_w7_eclear; clear; lia)) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  assert (WOK : w7_winok en (strs ++ rest) ((a_E RT en, a_E RT en + 904) :: lib_W (a_LBL RT en))).
  { intros a Ha. destruct (wg_not_outside_cons _ _ _ _ Ha) as [R|X]; [right; left; exists (a_E RT en), 904; split; [apply in_or_app; right; exact INE| exact R]|].
    exact (winok_libW en Σ m crem _ COM a X). }
  destruct (P7 w7_W_facts en Σ m crem _ _ COM WOK) as (HWS & HWU & HWH & HWF & HWD).
  (* [comment removed for export] *)
  pose proof ND as NDt. rewrite map_app in NDt. pose proof (nd_split _ _ NDt) as (NDS & NDR & DJ).
  assert (SLV : incl_live strs (rt_live RT Σ)) by (intros e He; exact (CLV _ ltac:(apply in_or_app; left; exact He))).
  assert (SNL : forall e, In e strs -> ~ In e (a_LBL RT en) /\ e <> (a_E RT en, 904)).
  { intros e He. pose proof (CFR e ltac:(apply in_or_app; left; exact He)) as X. rewrite map_app in X. split.
    - intros Y. apply X. apply in_or_app; left. exact (in_map fst _ _ (INCL _ Y)).
    - intros ->. apply X. apply in_or_app; left. exact (in_map fst _ _ INE). }
  apply (C_EC Σ (a_PMc RT en) (wz SITE_w7_eclear) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) [RA_FUZZ] (a_canary RT en) (a_LBL RT en) (a_E RT en) top bot strs
           FDO MST eq_refl LE INCL1 (CLL _ INE) SLV SNL NDS EL ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold W7_CALLEE_STACK, ERRC_STACK in *; lia) CLE CTX1 UWC1 CGH
           ltac:(rewrite FRL; unfold FRAMES_MAX; clear; lia) ltac:(clear - CRED CRM; lia) T c HA).
  intros c' (Σ' & AP & LV' & FRS' & SP' & CR' & CG'). unfold apost in AP.
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (LE1 & REST1)) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PR. rewrite (ret_pc_even SITE_w7_eclear) in Hc' by (unfold SITE_w7_eclear; clear; lia).
  assert (KP : forall e, In e (rest ++ a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')).
  { intros e He. rewrite LV'. apply live_remove_all_keep; [apply (Permutation_in _ (Permutation_sym PERM)); rewrite <- app_assoc; apply in_or_app; right; exact He|].
    intros X. apply in_app_iff in He. destruct He as [He|He]; [exact (DJ _ X (in_map fst _ _ He))|].
    apply in_map_iff in X. destruct X as (e' & E' & He'). apply (CFR e' ltac:(apply in_or_app; left; exact He')). rewrite E'. exact (in_map fst _ _ He). }
  assert (PERM1 : Permutation (rt_live RT Σ') (rest ++ a_CL RT en ++ a_DRV RT en)).
  { rewrite LV'. apply (live_remove_all_split _ _ strs); [rewrite app_assoc; exact PERM| intros e He; apply in_map; exact He|].
    intros e He X. apply in_app_iff in He. destruct He as [He|He]; [exact (DJ _ X (in_map fst _ _ He))|].
    apply in_map_iff in X. destruct X as (e' & E' & He'). apply (CFR e' ltac:(apply in_or_app; left; exact He')). rewrite E'. exact (in_map fst _ _ He). }
  rewrite <- LV' in PR. pose proof (sec_keep m m' _ _ _ _ SEC PR HWS) as SEC1.
  eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact REST1| exact LV'| exact FRS'| exact PR| exact KP| exact Hc'].
  eapply (PK w7_callk en Σ Σ' m m' crem (crem - 1) _ rest _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS' SP' CG' CR');
    [clear - CRM; lia| clear; lia| intros e He; apply KP; apply in_or_app; right; exact He| exact HWS| exact HWU| exact HWH| exact HWF| exact HWD| exact PERM1
    | intros e He; exact (CFR e ltac:(apply in_or_app; right; exact He))
    | exact NDR
    | intros e He; apply LPOS; rewrite LV' in He; exact (proj1 (live_remove_all_sub _ _ _ He))
    | rewrite length_app in CURL; clear - CURL; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w7c_pem : pem_read_bio_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS ->
  forall T (en : w7a) Σ (m : mem) crem K BI blen bmax flags (on oh od ol : word) (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) c,
  w7_com en Σ m crem (mbio_ent K bmax) -> mbio_rep (rt_live RT Σ) m K BI M_MEM blen bmax 0 -> blen < 2 ^ 26 -> errst_at_rest (a_E RT en) [] m ->
  rw_cells asegs m (a_f RT en + 32) [C8 on] -> rw_cells asegs m (a_f RT en + 64) [C8 oh] -> rw_cells asegs m (a_f RT en + 96) [C8 od] -> rw_cells asegs m (a_f RT en + 128) [C8 ol] ->
  pem_credit (blen - 0) <= crem -> 0 <= flags < 256 ->
  ASTA RT Σ (a_PMc RT en) (eq (w7_cs en FZ_PEM_READ_BIO m F fc (wz SITE_w7_pem) t0 t1 t2 (wz BI) (wz (a_f RT en + 32)) (wz (a_f RT en + 64)) (wz (a_f RT en + 96)) (wz (a_f RT en + 128)) (wz flags) a6 a7
                                 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) c ->
  (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (ret boff' top bot : Z) (strs news : list (Z * Z)),
     w7_com en Σ' m' (crem - pem_credit (blen - 0)) (mbio_ent K bmax ++ strs ++ news) -> rt_frames RT Σ' = rt_frames RT Σ ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en)
                ([(a_f RT en + 32, a_f RT en + 32 + 8); (a_f RT en + 64, a_f RT en + 64 + 8); (a_f RT en + 96, a_f RT en + 96 + 8); (a_f RT en + 128, a_f RT en + 128 + 8); (a_E RT en, a_E RT en + 904)]
                 ++ mbio_W K bmax ++ lib_W (a_LBL RT en)) m m' ->
     (forall e, In e (a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')) ->
     0 <= boff' <= blen -> mbio_rep (rt_live RT Σ') m' K BI M_MEM blen bmax boff' ->
     errst_live (a_E RT en) top bot strs m' -> (length strs <= 2)%nat -> Forall (fun e => 0 < snd e <= 64) strs -> List.NoDup (map fst (strs ++ news)) ->
     pem_out ret m' (a_f RT en + 32) (a_f RT en + 64) (a_f RT en + 96) (a_f RT en + 128) news -> 254 * news_sz news <= 255 * (boff' - 0) + 254 * 512 ->
     ASTA RT Σ' (a_PMc RT en) (eq (w7_cs en SITE_w7_pem m' F' fc' (wz SITE_w7_pem) y0 y1 y2 (wz ret) b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP libenv_agree libenv_fp_where REST_agree REST_fp_where.
  intros C_PEM T en Σ m crem K BI blen bmax flags on oh od ol F fc t0 t1 t2 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c COM MBK BLT REST0 CN CH CD CL CRM FL HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  destruct (P7 w7_call_pre en Σ m crem _ SITE_w7_pem A_PEM_read_bio_ex COM ltac:(unfold W7_SITES_OWN; cbn [map]; do 4 right; left; reflexivity)
              ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 4 right; left; reflexivity)
              ltac:(unfold SITE_w7_pem; clear; lia)) as (EU & COK & CTX1 & UWC1 & INCL1 & FRL & CRED & HLO & H160 & TOP' & LVB).
  set (W := [(a_f RT en + 32, a_f RT en + 32 + 8); (a_f RT en + 64, a_f RT en + 64 + 8); (a_f RT en + 96, a_f RT en + 96 + 8); (a_f RT en + 128, a_f RT en + 128 + 8); (a_E RT en, a_E RT en + 904)]
            ++ mbio_W K bmax ++ lib_W (a_LBL RT en)).
  assert (WOK : w7_winok en (mbio_ent K bmax) W).
  { intros a Ha. subst W. destruct (not_outside_app _ _ _ Ha) as [X|X].
    - destruct (wg_not_outside_cons _ _ _ _ X) as [R|X1]; [right; right; clear - R; lia|].
      destruct (wg_not_outside_cons _ _ _ _ X1) as [R|X2]; [right; right; clear - R; lia|].
      destruct (wg_not_outside_cons _ _ _ _ X2) as [R|X3]; [right; right; clear - R; lia|].
      destruct (wg_not_outside_cons _ _ _ _ X3) as [R|X4]; [right; right; clear - R; lia|].
      destruct (wg_not_outside_cons _ _ _ _ X4) as [R|X5]; [right; left; exists (a_E RT en), 904; split; [apply in_or_app; right; exact INE| exact R]|].
      exfalso. apply X5. exact I.
    - destruct (not_outside_app _ _ _ X) as [Y|Y].
      + right; left. unfold mbio_W in Y. destruct (not_outside_blocks _ _ Y) as (p & n & Hin & Hp). exists p, n. split; [apply in_or_app; left; exact Hin| exact Hp].
      + exact (winok_libW en Σ m crem _ COM a Y). }
  destruct (P7 w7_W_facts en Σ m crem _ _ COM WOK) as (HWS & HWU & HWH & HWF & HWD).
  assert (NTLK : forall e, In e ((a_E RT en, 904) :: a_LBL RT en) -> ~ In (fst e) (mbio_blocks K)).
  { intros e He X. rewrite <- (mbio_ent_fst K bmax) in X. apply in_map_iff in X. destruct X as (e' & E' & He').
    apply (CFR e' He'). rewrite E', map_app. apply in_or_app; left. apply (in_map fst). destruct He as [<-|He]; [exact INE| exact (INCL _ He)]. }
  (* [comment removed for export] *)
  assert (ND4 : List.NoDup [a_f RT en + 32; a_f RT en + 64; a_f RT en + 96; a_f RT en + 128]).
  { repeat constructor; cbn [In]; clear; lia. }
  destruct (w7_shadow_byte4 m _ FSH) as (SB4 & SB8 & SB12 & SB16).
  assert (SHX : forall k, shad (a_f RT en + 8 * k) = shad (a_f RT en) + k) by (intros k; unfold shad; replace (a_f RT en + 8 * k) with (a_f RT en + k * 8) by lia; rewrite Z.div_add by lia; lia).
  assert (OUTS : Forall (fun P => P mod 8 = 0 /\ pp_loc (rt_frames RT Σ) m USTACK_TOP P) [a_f RT en + 32; a_f RT en + 64; a_f RT en + 96; a_f RT en + 128]).
  { assert (G : forall j (B : bytes_at asegs m (shad (a_f RT en) + j) [z8]), 4 <= j <= 16 -> (a_f RT en + 8 * j) mod 8 = 0 /\ pp_loc (rt_frames RT Σ) m USTACK_TOP (a_f RT en + 8 * j)).
    { intros j B Hj. split; [clear - F64; Z.div_mod_to_equations; lia|]. right. exists (a_f RT en), 2%nat. split; [exact INF|]. split; [clear - Hj; lia|].
      split; [change (fs_size 2) with 256; clear - Hj; lia|]. rewrite SHX. exact B. }
    replace (a_f RT en + 32) with (a_f RT en + 8 * 4) by lia. replace (a_f RT en + 64) with (a_f RT en + 8 * 8) by lia.
    replace (a_f RT en + 96) with (a_f RT en + 8 * 12) by lia. replace (a_f RT en + 128) with (a_f RT en + 8 * 16) by lia.
    constructor; [exact (G 4 SB4 ltac:(clear; lia))|]. constructor; [exact (G 8 SB8 ltac:(clear; lia))|].
    constructor; [exact (G 12 SB12 ltac:(clear; lia))|]. constructor; [exact (G 16 SB16 ltac:(clear; lia))| constructor]. }
  replace (a_f RT en + 8 * 4) with (a_f RT en + 32) in OUTS by lia. replace (a_f RT en + 8 * 8) with (a_f RT en + 64) in OUTS by lia.
  replace (a_f RT en + 8 * 12) with (a_f RT en + 96) in OUTS by lia. replace (a_f RT en + 8 * 16) with (a_f RT en + 128) in OUTS by lia.
  apply (C_PEM Σ (a_PMc RT en) (wz SITE_w7_pem) (wz (a_sp1 RT en)) (a_gp RT en) (wz TP_A) t0 t1 t2 (a_sp RT en) s1
           (wz BI) (wz (a_f RT en + 32)) (wz (a_f RT en + 64)) (wz (a_f RT en + 96)) (wz (a_f RT en + 128)) (wz flags) a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (a_lo RT en) [RA_FUZZ] (a_canary RT en) (a_LBL RT en) K
           (a_E RT en) BI M_MEM blen bmax 0 (a_f RT en + 32) (a_f RT en + 64) (a_f RT en + 96) (a_f RT en + 128) flags on oh od ol
           FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl FL LE INCL1 (CLL _ INE) NLE NTLK REST0 MBK BLT ND4 OUTS CN CH CD CL
           ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold W7_CALLEE_STACK, PEMR_STACK, PEM_CALLEE_STACK in *; lia) CLE SEC CTX1 UWC1 CGH
           ltac:(rewrite FRL; unfold FRAMES_MAX; clear; lia) ltac:(clear - LVB; lia) ltac:(clear - CRED CRM; lia) LPOS T c HA).
  intros c' (Σ' & AP & FRS' & SP' & CR' & CG'). unfold apost in AP.
  destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (SEC1 & (ret & boff' & top & bot & strs & news & -> & BOFF & MB1 & LE1 & EL1 & LS2 & S64 & NDSN & NSZ & POUT & PERM' & FRSH))) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PR. rewrite (ret_pc_even SITE_w7_pem) in Hc' by (unfold SITE_w7_pem; clear; lia). fold W in PR.
  assert (LV0 : forall e, In e (a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ)) by (intros e He; apply in_app_iff in He; destruct He as [He|He]; [exact (CLL _ He)| exact (DLV _ He)]).
  assert (KP : forall e, In e (a_CL RT en ++ a_DRV RT en) -> In e (rt_live RT Σ')).
  { intros e He. apply (Permutation_in _ (Permutation_sym PERM')). apply in_or_app; right. apply in_or_app; right. exact (LV0 _ He). }
  assert (PERM1 : Permutation (rt_live RT Σ') ((mbio_ent K bmax ++ strs ++ news) ++ a_CL RT en ++ a_DRV RT en)).
  { eapply Permutation_trans; [exact PERM'|]. rewrite <- (app_assoc (mbio_ent K bmax) (strs ++ news) (a_CL RT en ++ a_DRV RT en)).
    apply (Permutation_trans (l' := (strs ++ news) ++ (mbio_ent K bmax ++ a_CL RT en ++ a_DRV RT en))).
    - rewrite (app_assoc strs news (rt_live RT Σ)). apply Permutation_app_head. exact PERM.
    - apply Permutation_app_swap_app. }
  assert (NPOS : forall e, In e news -> 0 < snd e).
  { intros e He. destruct POUT as [(_ & -> & _)|(_ & NM & HD & DT & nn & nh & dlen & bn & bh & bd & -> & NN & NH & DL & _)]; [destruct He|].
    destruct He as [<-|[<-|[<-|[]]]]; cbn; clear - NN NH DL; lia. }
  eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' ret boff' top bot strs news); [| exact FRS'| exact PR| exact KP| exact BOFF| exact MB1| exact EL1| exact LS2| exact S64| exact NDSN| exact POUT| exact NSZ| exact Hc'].
  eapply (PK w7_callk en Σ Σ' m m' crem (crem - pem_credit (blen - 0)) _ _ (rt_live RT Σ) W (pem_credit (blen - 0)) COM ART1 MI1 ST1 PR CLE1 SEC1 LE1 FRS' SP' CG' CR');
    [clear - CRM; lia| clear; lia| exact LV0| exact HWS| exact HWU| exact HWH| exact HWF| exact HWD| exact PERM1| | | |].
  - intros e He. apply in_app_iff in He. destruct He as [He|He]; [exact (CFR e He)|].
    intros X. apply (FRSH e He). apply in_map_iff in X. destruct X as (e' & E' & He'). rewrite <- E'. exact (in_map fst _ _ (LV0 _ He')).
  - rewrite map_app. apply nd_app; [exact ND| exact NDSN|].
    intros x Hx Hy. apply in_map_iff in Hy. destruct Hy as (e & <- & He). apply (FRSH e He). apply in_map_iff in Hx. destruct Hx as (e' & E' & He'). rewrite <- E'.
    exact (in_map fst _ _ (CLV _ He')).
  - intros e He. apply (Permutation_in _ PERM') in He. apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (proj1 (Forall_forall _ _) S64 e He))|].
    apply in_app_iff in He. destruct He as [He|He]; [exact (NPOS e He)| exact (LPOS e He)].
  - rewrite !length_app. unfold mbio_ent. cbn [length app].
    assert (LN : (length news <= 3)%nat) by (destruct POUT as [(_ & -> & _)|(_ & NM & HD & DT & nn & nh & dlen & bn & bh & bd & -> & _)]; cbn; clear; lia).
    destruct (k_d K); cbn [length]; clear - LS2 LN; unfold FUZZ_LIVE; lia.
Qed.

(* [comment removed for export] *)
Lemma w7_chk_cur : forall (en : w7a) Σ (m : mem) crem cur p sz s k,
  w7_com en Σ m crem cur -> In (p, sz) cur -> 0 < sz -> p <= s -> s + k <= p + sz -> 0 <= k ->
  checked_src RT Σ m (wz (a_sp1 RT en)) (a_lo RT en) s k.
Proof using AF AFP.
  intros en Σ m crem cur p sz s k COM HP POS H1 H2 K0.
  pose proof COM as (ART0 & _).
  pose proof (P7 w7_cur_facts en Σ m crem cur (p, sz) COM HP POS) as (INP & _ & PLO & _). cbn [fst snd] in PLO.
  split; [| left; clear - PLO H2; lia]. intros _. split.
  - destruct (af_acc_live RT AF Σ m p sz ART0 INP) as [_ ACC]. eapply acc_sub; [exact ACC| exact H1| exact H2].
  - left. exists p, sz. split; [exact INP| clear - H1 H2; lia].
Qed.
End W7C.
