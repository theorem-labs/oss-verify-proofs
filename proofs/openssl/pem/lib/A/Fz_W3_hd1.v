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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_endl Fz_W3_ngets Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_hd_j1 : Z := 0x30c684.    (* [comment removed for export] *)
Definition SITE_hd_j2 : Z := 0x30c6a0.    (* [comment removed for export] *)
Definition SITE_hd_mchr : Z := 0x30c69c.  (* [comment removed for export] *)
Definition SITE_hd_snc : Z := 0x30c6b4.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hd_a_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (len LB2 tmp : Z) (b253 : byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 1 <= len <= 254 -> 0 < LB2 -> LB2 + 256 <= sp1 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 24) (loc_H LB2 tmp) ->
  ro_cells asegs m (shad (LB2 + 253)) [C1 (Z_to_bv 8 0)] ->
  ov_read_bytes asegs m (Z_to_bv 64 (LB2 + 253)) 1%nat = Some [b253] ->
  evt asegs (fun ms => exists (a0' : word) (pv : Z),
      ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz len) s6 (wz pv) s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_hd_j1) fc None m (seg_rom asegs)
      /\ 0 <= pv <= 1)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz len) s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz J_HD) fc None m (seg_rom asegs)).
Proof.
  intros until b253. intros SP0 SPH LEN HL0 HLH MI FRH ROsh RD. unfold J_HD, TP_A, loc_H in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 LB2) = LB2) by (apply unsigned_lit; lia).
  zstep. zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *) zstep.
    unfold SITE_hd_j1. apply evt_done. eexists _, 0. split; [reflexivity| lia].
  - (* [comment removed for export] *)
    zstep. zstep. cbv beta. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). zstep. if_false.
    zstep. zstep. zstep. zstep. zstep.
    unfold SITE_hd_j1. apply evt_done. eexists _, (Z.b2z (0 <? Z.land (bv_unsigned b253 + -10) 18446744073709551615)). split; [reflexivity|].
    clear; destruct (0 <? _); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma hd_b0_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (got : Z),
  got <> 0 -> 0 <= got <= 2 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd_j2) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd_j1) fc None m (seg_rom asegs)).
Proof.
  intros until got. intros G0 GR MI. unfold SITE_hd_j1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUg : bv_unsigned (Z_to_bv 64 got) = got) by (apply unsigned_lit; lia).
  zstep. if_true. unfold SITE_hd_j2. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma hd_b1_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s8 s9 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (len LB2 : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_hd_mchr) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz LB2) (wz 58) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 (wz len) (wz 0) s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6)
                               F (wz e_icpt_memchr) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz len) (wz 0) s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_hd_j1) fc None m (seg_rom asegs)).
Proof.
  intros until LB2. intros MI. unfold SITE_hd_j1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_false. zstep. zstep. zstep. zstep.
  unfold SITE_hd_mchr, e_icpt_memchr. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma hd_b2_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (r : Z),
  0 <= r < 2 ^ 64 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz (if r =? 0 then 0 else 1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (wz SITE_hd_j2) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd_mchr) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros RR MI. unfold SITE_hd_mchr, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  zstep. replace (Z.b2z (0 <? r)) with (if r =? 0 then 0 else 1) by (destruct (Z.eqb_spec r 0) as [->|NE]; [reflexivity| destruct (0 <? r) eqn:E; [reflexivity| apply Z.ltb_ge in E; lia]]).
  unfold SITE_hd_j2. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma hd_c_walk : forall ra0 sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (LB2 tmp : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m -> rw_cells asegs m (sp1 + 24) (loc_H LB2 tmp) ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_hd_snc) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz LB2) (wz LIT_ENDSTR) (wz 9) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6)
                               F (wz e_icpt_strncmp) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz LB2) t3 t4 t5 t6) F (wz SITE_hd_j2) fc None m (seg_rom asegs)).
Proof.
  intros until tmp. intros SP0 SPH MI FRH. unfold SITE_hd_j2, TP_A, loc_H in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  unfold SITE_hd_snc, e_icpt_strncmp. apply evt_done. split; [reflexivity| exact I].
Qed.

Lemma land_full8 : forall f, 0 <= f < 256 -> Z.land 18446744073709551615 f = f.
Proof. intros f Hf. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_m5_8 : forall f, 0 <= f < 256 -> Z.land 18446744073709551611 f = Z.land f (Z.lnot 4).
Proof.
  intros f Hf. assert (E : Z.land f 255 = f) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- E. rewrite (Z.land_comm (Z.land f 255) (Z.lnot 4)), (Z.land_comm f 255), !Z.land_assoc. reflexivity.
Qed.

Definition hd_mask (flags r g : Z) : Z := if ((r =? 0) || (g =? 1))%bool then Z.land flags (Z.lnot 4) else flags.
(* [comment removed for export] *)
Lemma hd_d_walk : forall ra0 sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (r g flags : Z)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> -1 <= r <= 1 -> 0 <= g <= 2 -> 0 <= flags < 256 -> mem_inv asegs m -> c7 = wz flags ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => exists (a0' a1' : word),
      ms = MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0' a1' (wz (hd_mask flags r g)) a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz g) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_HD2) fc None m (seg_rom asegs))
    (MS (mkR ra0 (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz g) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_hd_snc) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH RR GR FL MI -> FRE. unfold SITE_hd_snc, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 flags) = flags) by (apply unsigned_lit; lia).
  assert (Hr : r = 0 \/ r = 1 \/ r = -1) by lia. assert (Hg : g = 0 \/ g = 1 \/ g = 2) by lia. clear RR GR.
  destruct Hr as [-> |[-> | ->]]; destruct Hg as [-> |[-> | ->]].
  all: do 8 zstep.
  all: match goal with |- context [Z_to_bv 64 (Z.land ?E ?f)] => is_var f; let v := eval vm_compute in E in replace (Z.land E f) with (Z.land v f) by reflexivity end.
  all: rewrite ?land_full8, ?land_m5_8 by lia.
  all: unfold J_HD2; cbv beta iota delta [hd_mask Z.eqb Pos.eqb orb]; apply evt_done; eexists _, _; reflexivity.
Qed.

(* [comment removed for export] *)
Definition pem_end_str : list byte := Eval vm_compute in (match image_bytes asegs LIT_ENDSTR 9 with Some bs => bs | None => [] end).
Lemma pem_end_len : length pem_end_str = 9%nat. Proof. reflexivity. Qed.
Lemma pem_end_ro : ro_bytes asegs LIT_ENDSTR (pem_end_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_end_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_ENDSTR (pem_end_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_ENDSTR; lia| rewrite length_app, pem_end_len; unfold LIT_ENDSTR; cbn; lia| exact pem_end_ro]. Qed.

(* [comment removed for export] *)
Lemma memchr_chk_range : forall c n buf, 0 <= n -> 0 <= memchr_chk c n buf <= n.
Proof.
  intros c n buf Hn. unfold memchr_chk. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:F; [| lia].
  apply find_byte_Some in F. destruct F as (Hi & _). rewrite length_firstn in Hi. lia.
Qed.
Lemma memchr_res_range : forall A c n buf, 0 < A -> 0 <= n -> memchr_res A c n buf = 0 \/ A <= memchr_res A c n buf < A + n.
Proof.
  intros A c n buf HA Hn. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:F; [| left; reflexivity].
  right. apply find_byte_Some in F. destruct F as (Hi & _). rewrite length_firstn in Hi. lia.
Qed.

Section CHd1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MCHR : memchr_icontract RT.
Hypothesis SNC : strncmp_icontract RT.
Hypothesis GO_end : GOBJ LIT_ENDSTR LIT_ENDSTR_SZ.
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

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).
Local Notation icpt_keepI := (icpt_keep RT AF GOBJ AFP libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS).

Theorem HD1_proof : forall N, HD2_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N -> HD_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N HD2P en Σ m off crem lrem j0 pv0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6
         LB2 namev nn hBv dBv tmp len got prev bn bs KX KY methX methY lenX maxX lenY maxY.
  intros MEAS INV LEN NULk PREV LFH INVW. unfold pem_at, cps. intros T c HA Hk.
  pose proof INV as (COM & REST & REM & LRM & PFR & FFC & ON & AL16 & LBS & LBC & NAL & NNR & LBN & NBC & NIN & MBX & MBY & GOT & GLT & GE2 & ENDV & LSUM & MXB & MYB).
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLB : In (LB2, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB2, 256) COM HLB ltac:(cbn; lia)) as (INL & L0 & LLO & LHI & LNAC). cbn [fst snd] in L0, LLO, LHI, LNAC.
  destruct (af_acc_live RT AF Σ m LB2 256 ART0 INL) as [LWR LACC].
  pose proof PFR as (_ & FRH & _).
  (* [comment removed for export] *)
  assert (ROsh : ro_cells asegs m (shad (LB2 + 253)) [C1 (Z_to_bv 8 0)]).
  { unfold shad, SHB. apply (acc_shadow0 m LB2 256 (LB2 + 253) LACC); clear - AL16 L0; [Z.div_mod_to_equations; lia| lia| lia|].
    replace (LB2 + 253 - LB2) with 253 by lia. cbn. lia. }
  destruct (nth_error bs 253%nat) as [b253|] eqn:Hb; [| exfalso; apply nth_error_None in Hb; rewrite LBS in Hb; clear - Hb; lia].
  pose proof (u8arr_read asegs m LB2 bs 253 b253 (Z_to_bv 64 (LB2 + 253)) (u8arr_of_rw_cells _ _ _ _ _ LBC) Hb ltac:(clear; lia) ltac:(symmetry; apply wa_of_Z_to_bv; clear - L0 LLO HLO SPH; lia)) as RD.
  (* [comment removed for export] *)
  pose proof (hd_a_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz got) pv0 (wz (shad (e_f RT en))) (wz SHB) (wz namev)
                t3 t4 t5 t6 F fc m len LB2 tmp b253 SP0' SPH LEN L0 ltac:(clear - LLO HLO; lia) MI FRH ROsh RD) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a0' & pv & -> & PV) & Hc1'). clear Hc1 HA RD ROsh.
  clear FRH ST ART0 LWR LACC.
  (* [comment removed for export] *)
  assert (TAILK : forall (m1 : mem) (F1 : bvmap 5 word) (fc1 : bv 32) (zra z0 z1 z2 e0 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 : word) (got1 : Z) c2,
    pem_com en Σ m1 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)]) -> mem_inv asegs m1 ->
    errst_at_rest (e_E RT en) [] m1 -> pem_frame en m1 j0 (loc_H LB2 tmp) (loc_F RT en) endv hBv dBv x1 x2 gap ->
    rw_cells asegs m1 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m1 -> rw_cells asegs m1 LB2 [CB 256 bs] ->
    rw_cells asegs m1 namev [CB (Z.to_nat nn) bn] ->
    mbio_rep (rt_live RT Σ) m1 KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m1 KY dBv methY lenY maxY 0 ->
    0 <= got1 <= 2 -> (got1 = 2 <-> got = 2) ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en SITE_hd_j2 m1 F1 fc1 zra z0 z1 z2 e0 e1 e2 e3 e4 e5 e6 e7 (wz tmp) s3 (wz prev) (wz len) (wz got1) (wz pv) (wz namev) (wz LB2) z3 z4 z5 z6)) c2 ->
    realizes asegs c2 T).
  { intros m1 F1 fc1 zra z0 z1 z2 e0 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 got1 c2 COM1 MI1 REST1 PFR1 FFC1 ON1 LBC1 NBC1 MBX1 MBY1 GOT1 G12 Hc2.
    pose proof COM1 as (ART1 & _). pose proof PFR1 as (_ & FRH1 & _).
    pose proof (hd_c_walk zra (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) e0 e1 e2 e3 e4 e5 e6 e7 (wz tmp) s3 (wz prev) (wz len) (wz got1) (wz pv) (wz (shad (e_f RT en))) (wz SHB) (wz namev)
                  z3 z4 z5 z6 F1 fc1 m1 LB2 tmp SP0' SPH MI1 FRH1) as W.
    cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & _) & Hc3'). clear Hc3 Hc2.
    pose proof (strncmp_sz_range 9 bs (pem_end_str ++ [Z_to_bv 8 0]) ltac:(clear; lia)) as SZ.
    assert (B1 : bytes_at asegs m1 LB2 bs) by (pose proof (rw_cells_bytes_at _ _ _ _ LBC1) as B; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
    assert (OK : strncmp_ok 9 bs (pem_end_str ++ [Z_to_bv 8 0])) by (unfold strncmp_ok; rewrite LBS, length_app, pem_end_len; cbn [length]; clear - SZ; lia).
    pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ LB2 256 LB2 (strncmp_sz 9 bs (pem_end_str ++ [Z_to_bv 8 0])) COM1 HLB
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SZ; lia) ltac:(clear - SZ; lia)) as CK1.
    assert (CK2 : checked_src RT Σ m1 (wz (e_sp1 RT en)) (e_lo RT en) LIT_ENDSTR (strncmp_sz 9 bs (pem_end_str ++ [Z_to_bv 8 0]))).
    { split; [| left; unfold LIT_ENDSTR; clear - HLOS SZ; lia]. intros _. split.
      - exact (afp_acc_global RT GOBJ AFP Σ m1 LIT_ENDSTR LIT_ENDSTR_SZ LIT_ENDSTR (strncmp_sz 9 bs (pem_end_str ++ [Z_to_bv 8 0])) ART1 GO_end ltac:(clear; lia) ltac:(unfold LIT_ENDSTR_SZ; clear - SZ; lia)).
      - right; right; right. unfold LIT_ENDSTR, SEGTOP_A. clear - SZ. lia. }
    eapply (pem_icpt_strncmp RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SNC T en Σ m1 off crem lrem _ LB2 LIT_ENDSTR 9 bs (pem_end_str ++ [Z_to_bv 8 0])
              SITE_hd_snc F1 fc1 z0 z1 z2 e3 e4 e5 e6 e7 (wz tmp) s3 (wz prev) (wz len) (wz got1) (wz pv) (wz namev) (wz LB2) z3 z4 z5 z6 c3
              COM1 ltac:(clear; lia) B1 (pem_end_bytes m1 MI1) OK CK1 CK2 ltac:(unfold SITE_hd_snc; clear; lia) eq_refl Hc3').
    clear Hc3'. intros m2 F2 fc2 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c4 COM2 PR2 MI2 Hc4.
    destruct (icpt_keepI en Σ m1 m2 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY
                COM1 PR2 REST1 PFR1 FFC1 ON1 LBC1 ltac:(clear - NNR; lia) NBC1 MBX1 MBY1) as (REST2 & PFR2 & FFC2 & ON2 & LBC2 & NBC2 & MBX2 & MBY2).
    clear COM1 MI1 REST1 PFR1 FFC1 ON1 LBC1 NBC1 MBX1 MBY1 PR2 B1 OK CK1 CK2 ART1 FRH1.
    pose proof (strncmp_res_range 9 bs (pem_end_str ++ [Z_to_bv 8 0])) as RR.
    set (r := strncmp_res 9 bs (pem_end_str ++ [Z_to_bv 8 0])) in *.
    pose proof PFR2 as (_ & _ & _ & _ & _ & _ & FRE2 & _). unfold loc_E in FRE2.
    pose proof (hd_d_walk (wz SITE_hd_snc) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 (wz tmp) s3 (wz prev) (wz len) (wz pv) (wz (shad (e_f RT en))) (wz SHB)
                  (wz namev) (wz LB2) w3 w4 w5 w6 F2 fc2 m2 r got1 (e_flags RT en) _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP0' SPH ltac:(clear - RR; lia) GOT1 FLR MI2 eq_refl FRE2) as W.
    cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (a0'' & a1'' & ->) & Hc5'). clear Hc5 Hc4.
    refine (HD2P en Σ m2 off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_hd_snc) w0 w1 w2 a0'' a1'' g3 g4 g5 g6 g7 s3 w3 w4 w5 w6
              LB2 namev nn hBv dBv tmp len got1 prev pv (hd_mask (e_flags RT en) r got1) bn bs KX KY methX methY lenX maxX lenY maxY MEAS _ LEN NULk PREV PV _ LFH INVW T c5 Hc5' Hk).
    - unfold hd_inv. cbv zeta.
      split; [exact COM2|]. split; [exact REST2|]. split; [exact REM|]. split; [exact LRM|].
      split; [exact PFR2|]. split; [exact FFC2|]. split; [exact ON2|].
      split; [exact AL16|]. split; [exact LBS|]. split; [exact LBC2|].
      split; [exact NAL|]. split; [exact NNR|]. split; [exact LBN|]. split; [exact NBC2|]. split; [exact NIN|].
      split; [exact MBX2|]. split; [exact MBY2|].
      split; [exact GOT1|]. split; [intros G1; apply GLT; clear - G1 G12 GOT; lia|]. split; [intros G1; apply GE2; clear - G1 G12; lia|]. split; [exact ENDV|].
      split; [exact LSUM|]. split; [exact MXB| exact MYB].
    - unfold hd_mask. destruct (_ || _)%bool; [right| left]; reflexivity. }
  (* [comment removed for export] *)
  destruct (Z.eq_dec got 0) as [G0|GNZ].
  - subst got.
    pose proof (hd_b1_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0' a1 a2 a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz pv) (wz (shad (e_f RT en))) (wz SHB) (wz namev)
                  t3 t4 t5 t6 F fc m len LB2 MI) as W.
    cl_lift W Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc1'.
    assert (BB : bytes_at asegs m LB2 bs) by (pose proof (rw_cells_bytes_at _ _ _ _ LBC) as B; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
    assert (MOK : memchr_ok LB2 58 len bs) by (unfold memchr_ok; destruct (find_byte _ _); [left|]; rewrite LBS; clear - LEN; lia).
    pose proof (memchr_chk_range 58 len bs ltac:(clear - LEN; lia)) as CHK.
    pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ LB2 256 LB2 (memchr_chk 58 len bs) COM HLB
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - CHK LEN; lia) ltac:(clear - CHK; lia)) as CK.
    eapply (pem_icpt_memchr RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS MCHR T en Σ m off crem lrem _ LB2 58 len bs SITE_hd_mchr F fc
              t0 t1 t2 a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz len) (wz 0) (wz pv) (wz namev) (wz LB2) t3 t4 t5 t6 c2
              COM ltac:(clear - L0 LLO HLO SPH; lia) ltac:(clear; lia) ltac:(clear - LEN; lia) BB MOK ltac:(rewrite LBS; clear - LLO; lia) CK
              ltac:(unfold SITE_hd_mchr; clear; lia) eq_refl Hc2').
    clear Hc2'. intros m1 F1 fc1 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c3 COM1 PR1 MI1 Hc3.
    destruct (icpt_keepI en Σ m m1 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY
                COM PR1 REST PFR FFC ON LBC ltac:(clear - NNR; lia) NBC MBX MBY) as (REST1 & PFR1 & FFC1 & ON1 & LBC1 & NBC1 & MBX1 & MBY1).
    pose proof (memchr_res_range LB2 58 len bs L0 ltac:(clear - LEN; lia)) as MR.
    pose proof (hd_b2_walk (wz SITE_hd_mchr) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7 (wz tmp) s3 (wz prev) (wz len) (wz 0) (wz pv) (wz (shad (e_f RT en))) (wz SHB)
                  (wz namev) (wz LB2) y3 y4 y5 y6 F1 fc1 m1 (memchr_res LB2 58 len bs) ltac:(clear - MR L0 LLO HLO SPH LEN; lia) MI1) as W.
    cl_lift W Hc3 c4 Hc4. destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (-> & _) & Hc4'). clear Hc4 Hc3.
    refine (TAILK m1 F1 fc1 (wz SITE_hd_mchr) y0 y1 y2 (wz (memchr_res LB2 58 len bs)) d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 (if memchr_res LB2 58 len bs =? 0 then 0 else 1) c4
              COM1 MI1 REST1 PFR1 FFC1 ON1 LBC1 NBC1 MBX1 MBY1 _ _ Hc4'); clear; destruct (_ =? 0); lia.
  - pose proof (hd_b0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0' a1 a2 a3 a4 a5 a6 a7 (wz tmp) s3 (wz prev) (wz len) (wz pv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2)
                  t3 t4 t5 t6 F fc m got GNZ GOT MI) as W.
    cl_lift W Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (-> & _) & Hc2'). clear Hc2 Hc1'.
    exact (TAILK m F fc xra t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 got c2 COM MI REST PFR FFC ON LBC NBC MBX MBY GOT (conj (fun x => x) (fun x => x)) Hc2').
Qed.
End CHd1.
