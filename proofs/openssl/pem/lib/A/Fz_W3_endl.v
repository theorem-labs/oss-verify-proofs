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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_icpt0 Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_lits Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_el_slen : Z := 0x30c7f8.   (* [comment removed for export] *)
Definition SITE_el_snc1 : Z := 0x30c810.   (* [comment removed for export] *)
Definition SITE_el_snc2 : Z := 0x30c830.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pem_tail_str : list byte := Eval vm_compute in (match image_bytes asegs LIT_TAIL 6 with Some bs => bs | None => [] end).
Lemma pem_tail_len : length pem_tail_str = 6%nat. Proof. reflexivity. Qed.
Lemma pem_tail_ro : ro_bytes asegs LIT_TAIL (pem_tail_str ++ [Z_to_bv 8 0]).
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_tail_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_TAIL (pem_tail_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_TAIL; lia| rewrite length_app, pem_tail_len; unfold LIT_TAIL; cbn; lia| exact pem_tail_ro]. Qed.

(* [comment removed for export] *)
Definition el_c_post (sp1 : Z) (ra' : Z) (pc' : Z) (gp s0 s1 a0' a1' a2' a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (wz ra') (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc') fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma el_c0_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (LB2 namev : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= LB2 -> LB2 + 256 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => el_c_post sp1 SITE_el_slen e_strlen gp s0 s1 (wz namev) a1 a2 a3 s2 (wz (LB2 + 9)) s4 s5 s6 s7 s8 s9 (wz namev) (wz LB2) F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (wz namev) (wz LB2) t3 t4 t5 t6) F (wz J_ENDLINE) fc None m (seg_rom asegs)).
Proof.
  intros until namev. intros SP0 SPH LB0 LBH MI. unfold J_ENDLINE, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUL : bv_unsigned (Z_to_bv 64 LB2) = LB2) by (apply unsigned_lit; lia).
  zstep. zstep. zstep.
  unfold el_c_post, SITE_el_slen, e_strlen. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma el_c1_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (P1 namev LB2 L : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => el_c_post sp1 SITE_el_snc1 e_strncmp gp s0 s1 (wz P1) (wz namev) (wz L) a3 s2 (wz P1) (wz L) s5 s6 s7 s8 s9 (wz namev) (wz LB2) F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz L) a1 a2 a3 a4 a5 a6 a7 s2 (wz P1) s4 s5 s6 s7 s8 s9 (wz namev) (wz LB2) t3 t4 t5 t6) F (wz SITE_el_slen) fc None m (seg_rom asegs)).
Proof.
  intros until L. intros SP0 SPH MI. unfold SITE_el_slen, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  unfold el_c_post, SITE_el_snc1, e_strncmp. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma el_c2r_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (r : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> r <> 0 -> -1 <= r <= 1 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 897) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE2) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_el_snc1) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros SP0 SPH R0 RR MI. unfold SITE_el_snc1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit_wrap in K; first [clear - K R0 RR; assert (r = 1 \/ r = -1) as [-> | ->] by lia; cbv in K; lia | idtac]].
  all: try (unfold J_RAISE2; apply evt_done; split; [reflexivity| exact I]).
Qed.

(* [comment removed for export] *)
Lemma el_c2_walk : forall ra sp1 gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (P1 L : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= P1 -> 0 <= L -> P1 + L < 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => el_c_post sp1 SITE_el_snc2 e_strncmp gp s0 s1 (wz (P1 + L)) (wz LIT_TAIL) (wz 6) a3 (wz 897) (wz P1) (wz L) s5 s6 s7 s8 s9 s10 s11 F fc m ms /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 (wz P1) (wz L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_el_snc1) fc None m (seg_rom asegs)).
Proof.
  intros until L. intros SP0 SPH P0 L0 PLH MI. unfold SITE_el_snc1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUP : bv_unsigned (Z_to_bv 64 P1) = P1) by (apply unsigned_lit; lia). assert (EUL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep.
  unfold el_c_post, SITE_el_snc2, e_strncmp, LIT_TAIL. apply evt_done. split; [| exact I]. do 11 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma el_c3r_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (r : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> r <> 0 -> -1 <= r <= 1 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE2) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_el_snc2) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros SP0 SPH R0 RR MI. unfold SITE_el_snc2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit_wrap in K; first [clear - K R0 RR; assert (r = 1 \/ r = -1) as [-> | ->] by lia; cbv in K; lia | idtac]].
  all: try (unfold J_RAISE2; apply evt_done; split; [reflexivity| exact I]).
Qed.

(* [comment removed for export] *)
Lemma el_c3a_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (got : Z)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> got <> 0 -> 0 <= got <= 2 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 c3 c5 s4 s5 c6 c4 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_LFREE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz got) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_el_snc2) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH G0 GR MI FRE. unfold SITE_el_snc2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. th_if_lit.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by (clear - GR; lia); clear - K G0; lia|].
  zstep. zstep. zstep. zstep. zstep.
  unfold J_LFREE. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma el_c3b_walk : forall ra sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 h0 h1 h2 h3 h4 h5 h6 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  rw_cells asegs m (sp1 + 24) [C8 h0; C8 h1; C8 h2; C8 h3; C8 h4; C8 h5; C8 h6] ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 c3 h2 s4 s5 c6 c5 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_LFREE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_el_snc2) fc None m (seg_rom asegs)).
Proof.
  intros until h6. intros SP0 SPH MI FRE FRH. unfold SITE_el_snc2, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. th_if_lit. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  unfold J_LFREE. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma lf_c4_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  evt asegs (fun ms => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms = MS (mkR (wz J_TAIL) (wz sp1) gp (wz TP_A) t0' t1' t2' s0 (wz sp1) s11 c7 (wz 256) (wz 930) a4' a5' a6' a7' s2 s3 c7 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz FZ_PEM_FREE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_LFREE) fc None m (seg_rom asegs)).
Proof.
  intros until c13. intros SP0 SPH MI FRE. unfold J_LFREE, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. zstep. zstep.
  unfold J_TAIL, FZ_PEM_FREE. apply evt_done. do 11 eexists. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Section CEndl.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SLC : strlen_icontract RT.
Hypothesis SNC : strncmp_icontract RT.
Hypothesis SNC0 : strncmp0_icontract RT.
(* [comment removed for export] *)
Hypothesis GO_tail : GOBJ LIT_TAIL LIT_TAIL_SZ.
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
Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_PF : pem_free_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis TAILP : TAIL_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis RAISE2P : RAISE2_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma rest_keep : forall (en : pem_entry) Σ Σ' (m m' : mem) off crem lrem cur,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
  In (e_E RT en, 904) (rt_live RT Σ') -> errst_at_rest (e_E RT en) [] m'.
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ Σ' m m' off crem lrem cur COM REST PR INE'. apply (errst_rest_agree m m' _ _ REST). intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
  apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INE' | exact R] | exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM _ R)].
Qed.

(* [comment removed for export] *)
Lemma mcost_mono : forall a b, 0 <= a <= b -> mcost a <= mcost b.
Proof. intros a b H. unfold mcost. destruct (a <=? 64512) eqn:E1; destruct (b <=? 64512) eqn:E2; apply Z.leb_le in E1 || apply Z.leb_gt in E1; apply Z.leb_le in E2 || apply Z.leb_gt in E2; lia. Qed.

(* [comment removed for export] *)
Theorem LFREE_proof : LFREE_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6
         LB2 namev nn hBv dBv hB' dB' bn bs KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM REST REM LRM PFR FFC ON LBA LBS LBC NMA NN BNL NMC NUL MBX MBY LSUM SW. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
  (* [comment removed for export] *)
  pose proof (lf_c4_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 (wz (e_f RT en)) (wz dB') s4 s5 (wz (e_f RT en)) (wz hB') (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) t3 t4 t5 t6 F fc m
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP0' SPH MI FRE) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & -> & _) & Hc1'). clear Hc1.
  (* [comment removed for export] *)
  assert (HP : Permutation (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)]) ((LB2, 256) :: mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)])).
  { apply Permutation_sym. rewrite (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(namev, nn)]), (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(LB2, 256); (namev, nn)]).
    apply Permutation_middle. }
  pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM HP) as COM1.
  eapply (pem_call_pfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PF T en Σ m off crem lrem _ LB2 256 256 J_TAIL
            F fc u0 u1 u2 (wz 930) b4 b5 b6 b7 (wz (e_f RT en)) (wz dB') (wz (e_flags RT en)) s5 (wz (e_f RT en)) (wz hB') (wz namev) (wz LB2) u3 u4 u5 u6 c1 COM1 ltac:(clear; lia)
            ltac:(unfold PEM_RAS_pfree, J_TAIL; cbn; tauto) Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM' LV' FRS' PR RL Hc'.
  assert (SL' : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn)]) -> In e (rt_live RT Σ')) by (intros e He; apply RL; apply in_or_app; left; exact He).
  assert (INE' : In (e_E RT en, 904) (rt_live RT Σ')) by (apply RL; apply in_or_app; right; exact INE).
  pose proof (rest_keep en Σ Σ' m m' off crem lrem _ COM1 REST PR INE') as REST'.
  pose proof (pem_frame_keep RT en m m' _ _ _ j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap PFR PR PD TOP HWS) as PFR'.
  pose proof (ff_keep m m' (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC PR INF HWFF) as FFC'.
  assert (ON' : out_null RT en m').
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ COM1 HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m' P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (NMC' : rw_cells asegs m' namev [CB (Z.to_nat nn) bn]).
  { eapply rw_cells_agree_nw; [exact NMC|]. intros a Ha.
    apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ _ _ (namev, nn) COM1 HWL (fun e H => or_intror H) PR
             ltac:(right; apply in_or_app; right; apply in_or_app; right; left; reflexivity) ltac:(apply SL'; apply in_or_app; right; apply in_or_app; right; left; reflexivity)).
    cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha NN. lia. }
  assert (MBX' : mbio_rep (rt_live RT Σ') m' KX hBv methX lenX maxX 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; split; apply SL'; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM1 HWL (fun e0 H0 => or_intror H0) e x ltac:(right; apply in_or_app; left; exact He) Hx). }
  assert (MBY' : mbio_rep (rt_live RT Σ') m' KY dBv methY lenY maxY 0).
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; apply SL'; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM1 HWL (fun e0 H0 => or_intror H0) e x ltac:(right; apply in_or_app; right; apply in_or_app; left; exact He) Hx). }
  (* [comment removed for export] *)
  destruct SW as [(-> & ->) | (-> & -> & -> & ->)].
  - refine (TAILP en Σ' m' off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' hBv dBv (wz J_TAIL) y0 y1 y2 v b1 b2 b3 d4 d5 d6 d7 s5 (wz LB2) y3 y4 y5 y6
              namev nn hBv dBv bn KX KY methX methY lenX maxX lenY maxY COM' REST' ltac:(clear - REM; lia) LRM PFR' FFC' ON' NMA NN BNL NMC' NUL MBX' MBY' LSUM T c' Hc' Hk).
  - assert (HP2 : Permutation (mbio_ent KX maxX ++ mbio_ent KY 0 ++ [(namev, nn)]) (mbio_ent KY 0 ++ mbio_ent KX maxX ++ [(namev, nn)])).
    { rewrite (app_assoc (mbio_ent KX maxX)), (app_assoc (mbio_ent KY 0)). apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl]. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ' m' off crem lrem _ _ COM' HP2) as COM2.
    refine (TAILP en Σ' m' off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F' fc' hBv dBv (wz J_TAIL) y0 y1 y2 v b1 b2 b3 d4 d5 d6 d7 s5 (wz LB2) y3 y4 y5 y6
              namev nn dBv hBv bn KY KX methY methX 0 0 lenX maxX COM2 REST' _ LRM PFR' FFC' ON' NMA NN BNL NMC' NUL MBY' MBX' ltac:(clear - LSUM; lia) T c' Hc' Hk).
    pose proof (mcost_mono lenX (lenX + 1)) as M1. destruct MBX as (BMx & flx & rrwx & numwx & padwx & nrx & nwx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & X1 & X2 & X3 & _)).
    specialize (M1 ltac:(clear - X1; lia)). replace (mcost (0 + 1)) with 0 by reflexivity. replace (mcost 0) with 0 in REM by reflexivity. clear - REM M1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pres_nil_any : forall K fr sp W (m m' : mem), rt_pres_fp K fr sp [] m m' -> rt_pres_fp K fr sp W m m'.
Proof. intros K fr sp W m m' H a Ha _. exact (H a Ha I). Qed.

(* [comment removed for export] *)
Lemma strncmp_res_range : forall n b1 b2, strncmp_res n b1 b2 = 0 \/ strncmp_res n b1 b2 = 1 \/ strncmp_res n b1 b2 = -1.
Proof.
  intros n b1 b2. unfold strncmp_res. destruct (strncmp_idx n b1 b2 =? n); [left; reflexivity|].
  destruct (nth_error b1 _); [| left; reflexivity]. destruct (nth_error b2 _); [| left; reflexivity].
  destruct (bv_unsigned _ <? bv_unsigned _); [right; right; reflexivity|]. destruct (bv_unsigned _ <? bv_unsigned _); [right; left; reflexivity| left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma pem_icpt_strncmp0 :
  forall T (en : pem_entry) Σ (m : mem) off crem lrem cur p1 p2 site (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
  pem_com en Σ m off crem lrem cur -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
  ASTA RT Σ (e_PMc RT en) (eq (pem_ms en e_strncmp m F fc (wz site) t0 t1 t2 (wz p1) (wz p2) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
  (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1' b2' b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
     pem_com en Σ m' off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' -> mem_inv asegs m' ->
     ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz 0) b1' b2' b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof using AF AFP SNC0 libenv_agree libenv_fp_where.
  intros T en Σ m off crem lrem cur p1 p2 site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM SR SE HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
  apply (SNC0 Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz p1) (wz p2) (wz 0) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m p1 p2 (e_lo RT en) FDO MST eq_refl eq_refl eq_refl ART0 MI COK T c HA).
  intros c' AP. unfold icpt_post in AP.
  destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PX & _) & Hc'). clear AP.
  destruct RS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
  rewrite EU in ST1, PX. rewrite (ret_pc_even site SR SE) in Hc'.
  destruct (com_icpt0 RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m m' off crem lrem cur COM ART1 MI1 ST1 PX) as [COM1 PR].
  exact (Hk m' F' fc' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM1 PR MI1 Hc').
Qed.
(* [comment removed for export] *)
Lemma strncmp_sz_range : forall n b1 b2, 0 <= n -> 0 <= strncmp_sz n b1 b2 <= n.
Proof. intros n b1 b2 H. unfold strncmp_sz, strncmp_idx. lia. Qed.

(* [comment removed for export] *)
Lemma mcost_le : forall n, 0 <= n -> 0 <= mcost n <= 2 * n + 16384.
Proof. intros n H. unfold mcost. destruct (n <=? 64512); lia. Qed.

(* [comment removed for export] *)
Lemma icpt_keep : forall (en : pem_entry) Σ (m m' : mem) off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3
    (LB2 namev nn hBv dBv : Z) (bn bs : list byte) (KX KY : mbk) (methX methY lenX maxX lenY maxY : Z),
  let cur := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)] in
  pem_com en Σ m off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' ->
  errst_at_rest (e_E RT en) [] m -> pem_frame en m j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap -> rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
  out_null RT en m -> rw_cells asegs m LB2 [CB 256 bs] -> 1 <= nn -> rw_cells asegs m namev [CB (Z.to_nat nn) bn] ->
  mbio_rep (rt_live RT Σ) m KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m KY dBv methY lenY maxY 0 ->
     errst_at_rest (e_E RT en) [] m' /\ pem_frame en m' j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap /\ rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)
  /\ out_null RT en m' /\ rw_cells asegs m' LB2 [CB 256 bs] /\ rw_cells asegs m' namev [CB (Z.to_nat nn) bn]
  /\ mbio_rep (rt_live RT Σ) m' KX hBv methX lenX maxX 0 /\ mbio_rep (rt_live RT Σ) m' KY dBv methY lenY maxY 0.
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ m m' off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM PR REST PFR FFC ON LBC NN NMC MBX MBY.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (HLB : In (LB2, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HNM : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  assert (WL0 : w_live RT Σ [] []) by (intros p n x _ _ _; exact I).
  split. { exact (rest_keep en Σ Σ m m' off crem lrem _ COM REST (pres_nil_any _ _ _ (lib_W (e_LBL RT en)) m m' PR) (ELV _ INE)). }
  split. { exact (pem_frame_keep RT en m m' _ _ [] j0 lH (loc_F RT en) endv hBv dBv x1 x2 gap PFR PR PD TOP (fun x _ => I)). }
  split. { exact (ff_keep m m' (e_f RT en) _ _ _ [] hj lenv j1 tav j2 bmv j3 FFC PR INF (fun x _ => I)). }
  split.
  { destruct ON as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ [] COM (fun x _ => I) (fun f k x _ _ => I) PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m' P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  split.
  { eapply rw_cells_agree_nw; [exact LBC|]. intros a Ha.
    apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ [] [] (LB2, 256) COM WL0 ltac:(intros e0 []) PR HLB (CLV _ HLB)).
    cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha. lia. }
  split.
  { eapply rw_cells_agree_nw; [exact NMC|]. intros a Ha.
    apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m m' off crem lrem _ _ [] [] (namev, nn) COM WL0 ltac:(intros e0 []) PR HNM (CLV _ HNM)).
    cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha NN. lia. }
  split.
  { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBX| exact PR| intros e He; split; apply CLV; apply in_or_app; left; exact He| intros e x _ _; exact I]. }
  eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBY| exact PR| intros e He; split; apply CLV; apply in_or_app; right; apply in_or_app; left; exact He| intros e x _ _; exact I].
Qed.

(* [comment removed for export] *)
Theorem ENDLINE_proof : forall N, ENDLINE_at RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS N.
Proof.
  intros N en Σ m off crem lrem j0 endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 t3 t4 t5 t6
         LB2 namev nn hBv dBv tmp len' got prev bn bs KX KY methX methY lenX maxX lenY maxY HINV LEN NUL PREV LXY.
  destruct HINV as (COM & REST & REM & LRM & PFR & FFC & ON & LBA & LBS & LBC & NMA & NN & BNL & NMC & HIN & MBX & MBY & GOT & GLT & GEQ & ENDV & LSUM & MXB & MYB).
  unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  assert (HLB : In (LB2, 256) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HNM : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (LB2, 256) COM HLB ltac:(cbn; clear; lia)) as (INL & L0 & LLO & _). cbn [fst snd] in L0, LLO.
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (namev, nn) COM HNM ltac:(cbn; clear - NN; lia)) as (INN & N0 & NLO & _). cbn [fst snd] in N0, NLO.
  (* [comment removed for export] *)
  pose proof MBX as (BMx & flx & rrwx & numwx & padwx & nrx & nwx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & X1 & X2 & X3 & _)).
  pose proof MBY as (BMy & fly & rrwy & numwy & padwy & nry & nwy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmy & _ & _ & _ & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)).
  pose proof (mcost_le (lenX + 1) ltac:(clear - X1; lia)) as M1. pose proof (mcost_le lenY ltac:(clear - Y1; lia)) as M2.
  assert (CRL : C_END + 8 + mcost (lenX + 1) + mcost lenY <= crem).
  { unfold hd_need, grow_pot, grow_cap, e_plen in REM. unfold gr_n in REM, MXB, MYB. clear - REM M1 M2 X1 Y1 OFF LSUM MXB MYB. Z.div_mod_to_equations. lia. }
  assert (CR7 : C_END + 7 <= crem) by (clear - CRL M1 M2; lia).
  clear BMx flx rrwx numwx padwx nrx nwx rmx BMy fly rrwy numwy padwy nry nwy rmy X2 X3 Y2 Y3.
  (* [comment removed for export] *)
  destruct (first_nul_split (Z_to_bv 8 0) bn HIN) as (str & bn2 & Ebn & NSTR). subst bn. clear HIN.
  assert (LSTR : Z.of_nat (length str) + 1 + Z.of_nat (length bn2) = nn) by (rewrite length_app in BNL; cbn [length] in BNL; clear - BNL NN; lia).
  assert (HIN : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_elt).
  (* [comment removed for export] *)
  destruct (af_live_slack RT AF Σ m namev nn ART0 INN) as (slack & SLB & SLM & SLT).
  assert (NMB : bytes_at asegs m namev (str ++ Z_to_bv 8 0 :: bn2 ++ slack)).
  { pose proof (rw_cells_bytes_at _ _ _ _ NMC) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite app_comm_cons, app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B|]. rewrite BNL, Z2Nat.id by (clear - NN; lia). exact SLB. }
  assert (SLK : (- (namev + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (bn2 ++ slack))).
  { rewrite length_app, Nat2Z.inj_add. clear - LSTR SLM NN. Z.div_mod_to_equations. lia. }
  assert (LO1 : namev + Z.of_nat (length str) + 1 + Z.of_nat (length (bn2 ++ slack)) <= e_lo RT en) by (rewrite length_app, Nat2Z.inj_add; clear - LSTR SLT LOW; lia).
  pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ namev nn namev (Z.of_nat (length str) + 1) COM HNM
                ltac:(clear - NN; lia) ltac:(clear; lia) ltac:(clear - LSTR; lia) ltac:(clear; lia)) as CK0.
  (* [comment removed for export] *)
  pose proof (el_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz got) s7
                (wz (shad (e_f RT en))) (wz SHB) t3 t4 t5 t6 F fc m LB2 namev SP0' SPH ltac:(clear - L0; lia) ltac:(clear - LLO HLO SPH; lia) MI) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc1'). clear Hc1 HA.
  eapply (pem_icpt_strlen RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SLC T en Σ m off crem lrem _ namev str (bn2 ++ slack) SITE_el_slen F fc
            u0 u1 u2 a1 a2 a3 b4 b5 b6 b7 s2 (wz (LB2 + 9)) s4 s5 (wz got) s7 (wz namev) (wz LB2) u3 u4 u5 u6 c1 COM NMB NSTR
            ltac:(clear - LSTR NN; lia) SLK ltac:(clear - N0 NLO HLO SPH NN; lia) LO1 CK0 ltac:(unfold SITE_el_slen; clear; lia) eq_refl Hc1').
  clear Hc1' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m1 F1 fc1 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 COM1 PR1 MI1 Hc2.
  destruct (icpt_keep en Σ m m1 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv _ bs KX KY methX methY lenX maxX lenY maxY
              COM PR1 REST PFR FFC ON LBC ltac:(clear - NN; lia) NMC MBX MBY) as (REST1 & PFR1 & FFC1 & ON1 & LBC1 & NMC1 & MBX1 & MBY1).
  clear COM REST PFR FFC ON LBC NMC MBX MBY PR1 NMB SLB SLK LO1 CK0 MI.
  (* [comment removed for export] *)
  assert (MATCH : forall (m2 : mem) (F2 : bvmap 5 word) (fc2 : bv 32) (z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 s4w : word) c4,
    pem_com en Σ m2 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(LB2, 256); (namev, nn)]) -> mem_inv asegs m2 ->
    errst_at_rest (e_E RT en) [] m2 -> pem_frame en m2 j0 (loc_H LB2 tmp) (loc_F RT en) endv hBv dBv x1 x2 gap ->
    rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> out_null RT en m2 -> rw_cells asegs m2 LB2 [CB 256 bs] ->
    rw_cells asegs m2 namev [CB (Z.to_nat nn) (str ++ Z_to_bv 8 0 :: bn2)] ->
    mbio_rep (rt_live RT Σ) m2 KX hBv methX lenX maxX 0 -> mbio_rep (rt_live RT Σ) m2 KY dBv methY lenY maxY 0 ->
    s4w = wz (Z.of_nat (length str)) ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en SITE_el_snc1 m2 F2 fc2 (wz SITE_el_snc1) z0 z1 z2 (wz 0) e1 e2 e3 e4 e5 e6 e7 s2 (wz (LB2 + 9)) s4w s5 (wz got) s7 (wz namev) (wz LB2) z3 z4 z5 z6)) c4 ->
    realizes asegs c4 T).
  { intros m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 s4w c4 COM2 MI2 REST2 PFR2 FFC2 ON2 LBC2 NMC2 MBX2 MBY2 -> Hc4.
    (* [comment removed for export] *)
    pose proof (el_c2_walk (wz SITE_el_snc1) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) (wz (e_sp1 RT en)) e1 e2 e3 e4 e5 e6 e7 s2 s5 (wz got) s7 (wz (shad (e_f RT en))) (wz SHB)
                  (wz namev) (wz LB2) z3 z4 z5 z6 F2 fc2 m2 (LB2 + 9) (Z.of_nat (length str)) SP0' SPH ltac:(clear - L0; lia) ltac:(clear; lia) ltac:(clear - LLO HLO SPH LSTR NN; lia) MI2) as W.
    cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc5'). clear Hc5 Hc4.
    pose proof COM2 as (ART2 & _).
    pose proof (strncmp_sz_range 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0]) ltac:(clear; lia)) as SZ2.
    assert (B1 : bytes_at asegs m2 (LB2 + 9 + (Z.of_nat (length str))) (skipn (9 + length str) bs)).
    { pose proof (rw_cells_bytes_at _ _ _ _ LBC2) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      rewrite <- (firstn_skipn (9 + length str) bs) in B. apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B].
      rewrite firstn_length_le in B by (rewrite LBS; clear - LSTR NN; lia). replace (LB2 + Z.of_nat (9 + length str)) with (LB2 + 9 + (Z.of_nat (length str))) in B by (clear; lia). exact B. }
    assert (OK2 : strncmp_ok 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0])).
    { unfold strncmp_ok. rewrite length_skipn, LBS, length_app, pem_tail_len. cbn [length]. clear - SZ2 LSTR NN. lia. }
    pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m2 off crem lrem _ LB2 256 (LB2 + 9 + (Z.of_nat (length str))) (strncmp_sz 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0])) COM2 HLB
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SZ2 LSTR NN; lia) ltac:(clear - SZ2; lia)) as CK1.
    assert (CK2 : checked_src RT Σ m2 (wz (e_sp1 RT en)) (e_lo RT en) LIT_TAIL (strncmp_sz 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0]))).
    { split; [| left; unfold LIT_TAIL; clear - HLOS SZ2; lia]. intros _. split.
      - exact (afp_acc_global RT GOBJ AFP Σ m2 LIT_TAIL LIT_TAIL_SZ LIT_TAIL (strncmp_sz 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0])) ART2 GO_tail ltac:(clear; lia) ltac:(unfold LIT_TAIL_SZ; clear - SZ2; lia)).
      - right; right; right. unfold LIT_TAIL, SEGTOP_A. clear - SZ2. lia. }
    eapply (pem_icpt_strncmp RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SNC T en Σ m2 off crem lrem _ (LB2 + 9 + (Z.of_nat (length str))) LIT_TAIL 6
              (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0]) SITE_el_snc2 F2 fc2 u0 u1 u2 e3 b4 b5 b6 b7 (wz 897) (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 (wz got) s7 (wz namev) (wz LB2) u3 u4 u5 u6 c5
              COM2 ltac:(clear; lia) B1 (pem_tail_bytes m2 MI2) OK2 CK1 CK2 ltac:(unfold SITE_el_snc2; clear; lia) eq_refl Hc5').
    clear Hc5' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m3 F3 fc3 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c6 COM3 PR3 MI3 Hc6.
    destruct (icpt_keep en Σ m2 m3 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv _ bs KX KY methX methY lenX maxX lenY maxY
                COM2 PR3 REST2 PFR2 FFC2 ON2 LBC2 ltac:(clear - NN; lia) NMC2 MBX2 MBY2) as (REST3 & PFR3 & FFC3 & ON3 & LBC3 & NMC3 & MBX3 & MBY3).
    clear COM2 MI2 REST2 PFR2 FFC2 ON2 LBC2 NMC2 MBX2 MBY2 PR3 B1 OK2 CK1 CK2 ART2.
    destruct (strncmp_res_range 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0])) as [R0 | RNZ].
    - (* [comment removed for export] *)
      rewrite R0 in Hc6. pose proof PFR3 as (_ & FRH3 & _ & _ & _ & _ & FRE3 & _). unfold loc_E in FRE3. unfold loc_H in FRH3.
      destruct (Z.eq_dec got 0) as [G0 | GNZ].
      + (* [comment removed for export] *)
        subst got. destruct (GLT ltac:(clear; lia)) as (Etmp & LY0 & MY0 & _). subst tmp.
        pose proof (el_c3b_walk (wz SITE_el_snc2) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 (wz 897) (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 s7
                      (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) w3 w4 w5 w6 F3 fc3 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP0' SPH MI3 FRE3 FRH3) as W.
        cl_lift W Hc6 c7 Hc7. destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & (-> & _) & Hc7'). clear Hc7 Hc6.
        exact (LFREE_proof en Σ m3 off crem lrem j0 (loc_H LB2 hBv) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 (wz SITE_el_snc2) w0 w1 w2 (wz 0) g1 g2 g3 g4 g5 g6 g7
                 (wz (Z.of_nat (length str))) s5 w3 w4 w5 w6 LB2 namev nn hBv dBv dBv hBv (str ++ Z_to_bv 8 0 :: bn2) bs KX KY methX methY lenX maxX lenY maxY
                 COM3 REST3 CRL ltac:(clear - LRM; lia) PFR3 FFC3 ON3 LBA LBS LBC3 NMA NN BNL NMC3 HIN MBX3 MBY3 LXY (or_intror (conj eq_refl (conj eq_refl (conj LY0 MY0)))) T c7 Hc7' Hk).
      + (* [comment removed for export] *)
        pose proof (el_c3a_walk (wz SITE_el_snc2) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 (wz 897) (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 s7
                      (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) w3 w4 w5 w6 F3 fc3 m3 got _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP0' SPH GNZ GOT MI3 FRE3) as W.
        cl_lift W Hc6 c7 Hc7. destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & (-> & _) & Hc7'). clear Hc7 Hc6.
        exact (LFREE_proof en Σ m3 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 (wz SITE_el_snc2) w0 w1 w2 (wz 0) g1 g2 g3 g4 g5 g6 g7
                 (wz (Z.of_nat (length str))) s5 w3 w4 w5 w6 LB2 namev nn hBv dBv hBv dBv (str ++ Z_to_bv 8 0 :: bn2) bs KX KY methX methY lenX maxX lenY maxY
                 COM3 REST3 CRL ltac:(clear - LRM; lia) PFR3 FFC3 ON3 LBA LBS LBC3 NMA NN BNL NMC3 HIN MBX3 MBY3 LXY (or_introl (conj eq_refl eq_refl)) T c7 Hc7' Hk).
    - (* [comment removed for export] *)
      assert (RZ : (strncmp_res 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0])) <> 0) by (clear - RNZ; lia). assert (RR : -1 <= (strncmp_res 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0])) <= 1) by (clear - RNZ; lia).
      pose proof (el_c3r_walk (wz SITE_el_snc2) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 (wz 897) (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 (wz got) s7
                    (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) w3 w4 w5 w6 F3 fc3 m3 _ SP0' SPH RZ RR MI3) as W.
      cl_lift W Hc6 c7 Hc7. destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & (-> & _) & Hc7'). clear Hc7 Hc6.
      exact (RAISE2P en Σ m3 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 (wz SITE_el_snc2) w0 w1 w2 (wz (strncmp_res 6 (skipn (9 + length str) bs) (pem_tail_str ++ [Z_to_bv 8 0]))) g1 g2 g3 g4 g5 g6 g7
              (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 (wz got) s7 w3 w4 w5 w6 LB2 namev nn hBv dBv 897 (str ++ Z_to_bv 8 0 :: bn2) bs KX KY methX methY lenX maxX lenY maxY
               COM3 REST3 CR7 ltac:(clear - LRM; lia) ltac:(clear; lia) PFR3 FFC3 ON3 LBA LBS LBC3 NMA NN BNL NMC3 MBX3 MBY3 T c7 Hc7' Hk). }
  (* [comment removed for export] *)
  pose proof (el_c1_walk (wz SITE_el_slen) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) d1 d2 d3 d4 d5 d6 d7 s2 s4 s5 (wz got) s7
                (wz (shad (e_f RT en))) (wz SHB) y3 y4 y5 y6 F1 fc1 m1 (LB2 + 9) namev LB2 (Z.of_nat (length str)) SP0' SPH MI1) as W.
  cl_lift W Hc2 c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & ((u0 & u1 & u2 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->) & _) & Hc3'). clear Hc3 Hc2.
  destruct (Z.eq_dec (Z.of_nat (length str)) 0) as [LZ | LNZ].
  - (* [comment removed for export] *)
    rewrite LZ in Hc3'.
    eapply (pem_icpt_strncmp0 T en Σ m1 off crem lrem _ (LB2 + 9) namev SITE_el_snc1 F1 fc1 u0 u1 u2 d3 b4 b5 b6 b7 s2 (wz (LB2 + 9)) (wz 0) s5 (wz got) s7 (wz namev) (wz LB2) u3 u4 u5 u6 c3
              COM1 ltac:(unfold SITE_el_snc1; clear; lia) eq_refl Hc3').
    clear Hc3' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c4 COM2 PR2 MI2 Hc4.
    destruct (icpt_keep en Σ m1 m2 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv _ bs KX KY methX methY lenX maxX lenY maxY
                COM1 PR2 REST1 PFR1 FFC1 ON1 LBC1 ltac:(clear - NN; lia) NMC1 MBX1 MBY1) as (REST2 & PFR2 & FFC2 & ON2 & LBC2 & NMC2 & MBX2 & MBY2).
    exact (MATCH m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 (wz 0) c4 COM2 MI2 REST2 PFR2 FFC2 ON2 LBC2 NMC2 MBX2 MBY2 ltac:(rewrite LZ; reflexivity) Hc4).
  - (* [comment removed for export] *)
    pose proof (strncmp_sz_range (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2) ltac:(clear; lia)) as SZ1.
    assert (B1 : bytes_at asegs m1 (LB2 + 9) (skipn 9 bs)).
    { pose proof (rw_cells_bytes_at _ _ _ _ LBC1) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      rewrite <- (firstn_skipn 9 bs) in B. apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B]. rewrite firstn_length_le in B by (rewrite LBS; clear; lia). exact B. }
    assert (B2 : bytes_at asegs m1 namev (str ++ Z_to_bv 8 0 :: bn2)).
    { pose proof (rw_cells_bytes_at _ _ _ _ NMC1) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (OK1 : strncmp_ok (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2)).
    { unfold strncmp_ok. rewrite length_skipn, LBS, length_app. cbn [length]. clear - SZ1 LSTR NN. lia. }
    pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ LB2 256 (LB2 + 9) (strncmp_sz (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2)) COM1 HLB
                  ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - SZ1 LSTR NN; lia) ltac:(clear - SZ1; lia)) as CK1.
    pose proof (com_chk_cur RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 off crem lrem _ namev nn namev (strncmp_sz (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2)) COM1 HNM
                  ltac:(clear - NN; lia) ltac:(clear; lia) ltac:(clear - SZ1 LSTR; lia) ltac:(clear - SZ1; lia)) as CK2.
    eapply (pem_icpt_strncmp RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS SNC T en Σ m1 off crem lrem _ (LB2 + 9) namev (Z.of_nat (length str))
              (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2) SITE_el_snc1 F1 fc1 u0 u1 u2 d3 b4 b5 b6 b7 s2 (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 (wz got) s7 (wz namev) (wz LB2) u3 u4 u5 u6 c3
              COM1 ltac:(clear - LNZ LSTR NN; lia) B1 B2 OK1 CK1 CK2 ltac:(unfold SITE_el_snc1; clear; lia) eq_refl Hc3').
    clear Hc3' u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6. intros m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c4 COM2 PR2 MI2 Hc4.
    destruct (icpt_keep en Σ m1 m2 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 LB2 namev nn hBv dBv _ bs KX KY methX methY lenX maxX lenY maxY
                COM1 PR2 REST1 PFR1 FFC1 ON1 LBC1 ltac:(clear - NN; lia) NMC1 MBX1 MBY1) as (REST2 & PFR2 & FFC2 & ON2 & LBC2 & NMC2 & MBX2 & MBY2).
    clear B1 B2 OK1 CK1 CK2 PR2.
    destruct (strncmp_res_range (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2)) as [R0 | RNZ].
    + rewrite R0 in Hc4. exact (MATCH m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 (wz (Z.of_nat (length str))) c4 COM2 MI2 REST2 PFR2 FFC2 ON2 LBC2 NMC2 MBX2 MBY2 eq_refl Hc4).
    + (* [comment removed for export] *)
      assert (RZ : (strncmp_res (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2)) <> 0) by (clear - RNZ; lia). assert (RR : -1 <= (strncmp_res (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2)) <= 1) by (clear - RNZ; lia).
      pose proof (el_c2r_walk (wz SITE_el_snc1) (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) e1 e2 e3 e4 e5 e6 e7 s2 (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 (wz got) s7
                    (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz LB2) z3 z4 z5 z6 F2 fc2 m2 _ SP0' SPH RZ RR MI2) as W.
      cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (-> & _) & Hc5'). clear Hc5 Hc4.
      exact (RAISE2P en Σ m2 off crem lrem j0 (loc_H LB2 tmp) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F2 fc2 (wz SITE_el_snc1) z0 z1 z2 (wz (strncmp_res (Z.of_nat (length str)) (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2))) e1 e2 e3 e4 e5 e6 e7
               (wz (LB2 + 9)) (wz (Z.of_nat (length str))) s5 (wz got) s7 z3 z4 z5 z6 LB2 namev nn hBv dBv 897 (str ++ Z_to_bv 8 0 :: bn2) bs KX KY methX methY lenX maxX lenY maxY
               COM2 REST2 CR7 ltac:(clear - LRM; lia) ltac:(clear; lia) PFR2 FFC2 ON2 LBA LBS LBC2 NMA NN BNL NMC2 MBX2 MBY2 T c5 Hc5' Hk).
Qed.
End CEndl.
