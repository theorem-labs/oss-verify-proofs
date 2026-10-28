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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W4_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W4_defs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_dc_ctrl : Z := 0x30ca14.    (* [comment removed for export] *)
Definition SITE_dc_pmal1 : Z := 0x30ca28.   (* [comment removed for export] *)
Definition SITE_dc_pmal2 : Z := 0x30ca54.   (* [comment removed for export] *)
Definition SITE_dc_hread : Z := 0x30ca98.   (* [comment removed for export] *)
Definition J_DC5 : Z := 0x30ca9c.           (* [comment removed for export] *)
Definition SITE_dc_dread : Z := 0x30caec.   (* [comment removed for export] *)

Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
Lemma sx32_small' : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.
Lemma t_addiw_small' : forall z c, 0 <= z + c < 2 ^ 31 -> 0 <= z < 2 ^ 64 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c) = z + c.
Proof.
  intros z c Hz Hr. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition dcE (PD PH PN f hBv dBv flags PLN BI : Z) : list cell :=
  [C8 (wz PD); C8 (wz PH); C8 (wz PN); C8 (wz f); C8 (wz hBv); C8 (wz dBv); C8 (wz f); C8 (wz flags);
   C8 (wz (shad PN)); C8 (wz (shad PLN)); C8 (wz PLN); C8 (wz (shad PD)); C8 (wz (shad PH)); C8 (wz BI)].

(* [comment removed for export] *)
Lemma dc0_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (hBv : Z),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_dc_ctrl) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz hBv) (wz 3) (wz 0) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz hBv) s8 s9 s10 s11 t3 t4 t5 t6) F (wz FZ_BIO_CTRL) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz hBv) s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_DEC) fc None m (seg_rom asegs)).
Proof.
  intros until hBv. intros MI. unfold J_DEC, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. unfold SITE_dc_ctrl, FZ_BIO_CTRL. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma dc1_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (lenX PD PH PN f hBv dBv flags PLN BI : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= lenX < 2 ^ 31 - 1 -> mem_inv asegs m -> rw_cells asegs m (sp1 + 112) (dcE PD PH PN f hBv dBv flags PLN BI) ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_dc_pmal1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz (lenX + 1)) (wz flags) (wz 1003) a3 a4 a5 a6 a7 s2 s3 (wz lenX) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz FZ_PEM_MALLOC) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_dc_ctrl) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz lenX) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_dc_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until BI. intros SP0 SPH LX MI FRE. unfold SITE_dc_ctrl, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep.
  zstep. match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by (rewrite ?unsigned_lit by lia; lia) end. rewrite ?unsigned_lit by lia.
  zstep. zstep. zstep.
  unfold SITE_dc_pmal1, FZ_PEM_MALLOC. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma dc2_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (HD dlen PD PH PN f hBv dBv flags PLN BI : Z) (q0 q2 : word) (pv : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> 0 <= dlen < 2 ^ 31 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f hBv dBv flags PLN BI) -> rw_cells asegs m (sp1 + 80) [C8 q0; C8 (wz (f + 32)); C8 q2] -> rw_cells asegs m (f + 32) [C4 (wz dlen)] ->
  ro_cells asegs m (shad PH) [C1 z8] -> rw_cells asegs m PH [C8 pv] -> 0 < PH -> PH + 8 <= sp1 -> (PH + 8 <= f \/ f + 128 <= PH) ->
  2147450880 <= shad PH < 17594333495296 -> (PH + 8 <= 2147450880 \/ 17594333495296 <= PH) ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_dc_pmal2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz dlen) (wz flags) (wz 1004) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz FZ_PEM_MALLOC) fc None m' (seg_rom asegs)
       /\ munch [(PH, PH + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PH [C8 (wz HD)])
    (MS (mkR (wz SITE_dc_pmal1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz HD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_dc_pmal1) fc None m (seg_rom asegs)).
Proof.
  intros until pv. intros SP0 SPH F0 FH DL MI FRE FRF FC32 SHP PHC P0 PHS PHF SRH PSH. unfold SITE_dc_pmal1, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PH, PH + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (shad PH)) = shad PH) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. rewrite (sx32_small' dlen) by lia.
  zstep. zstep. lfix.
  zstep. zstep. zstep. zstep.
  unfold SITE_dc_pmal2, FZ_PEM_MALLOC. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact PHC].
Qed.

(* [comment removed for export] *)
Lemma dc3z_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (HD PD PH PN f hBv dBv flags PLN BI : Z) (pv : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f hBv dBv flags PLN BI) ->
  ro_cells asegs m (shad PD) [C1 z8] -> rw_cells asegs m PD [C8 pv] -> 0 < PD -> PD + 8 <= sp1 -> 2147450880 <= shad PD < 17594333495296 -> (PD + 8 <= 2147450880 \/ 17594333495296 <= PD) ->
  ro_cells asegs m (shad PH) [C1 z8] -> rw_cells asegs m PH [C8 (wz HD)] -> 0 < PH -> PH + 8 <= sp1 -> 2147450880 <= shad PH < 17594333495296 -> (PH + 8 <= PD \/ PD + 8 <= PH) ->
  0 < HD < 2 ^ 47 ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_dc_pmal2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) (wz HD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz J_OUTFREE) fc None m' (seg_rom asegs)
       /\ munch [(PD, PD + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PD [C8 (wz 0)] /\ rw_cells asegs m' PH [C8 (wz HD)])
    (MS (mkR (wz SITE_dc_pmal2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_dc_pmal2) fc None m (seg_rom asegs)).
Proof.
  intros until pv. intros SP0 SPH MI FRE SHD PDC D0 PDS SRD PSD SHP PHC P0 PHS SRH DJ HDR. unfold SITE_dc_pmal2, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PD, PD + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (shad PD)) = shad PD) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (shad PH)) = shad PH) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  assert (EUH : bv_unsigned (Z_to_bv 64 HD) = HD) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. change Startup_glue.z64 with (Z_to_bv 64 0). lfix.
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. if_false. zstep. th_if_lit.
  unfold J_OUTFREE. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PDC| exact PHC].
Qed.

(* [comment removed for export] *)
Lemma dc3_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (HD DT lenX PD PH PN f eh ed hBv dBv flags PLN BI : Z) (pv : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f eh ed flags PLN BI) ->
  ro_cells asegs m (shad PD) [C1 z8] -> rw_cells asegs m PD [C8 pv] -> 0 < PD -> PD + 8 <= sp1 -> 2147450880 <= shad PD < 17594333495296 -> (PD + 8 <= 2147450880 \/ 17594333495296 <= PD) ->
  ro_cells asegs m (shad PH) [C1 z8] -> rw_cells asegs m PH [C8 (wz HD)] -> 0 < PH -> PH + 8 <= sp1 -> 2147450880 <= shad PH < 17594333495296 -> (PH + 8 <= PD \/ PD + 8 <= PH) ->
  0 < HD < 2 ^ 47 -> 0 < DT < 2 ^ 47 -> 0 <= lenX < 2 ^ 31 - 1 ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz (if lenX =? 0 then SITE_dc_pmal2 else SITE_dc_hread)) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (if lenX =? 0 then wz DT else wz hBv) (wz HD) (if lenX =? 0 then a2 else wz lenX) a3 a4 a5 a6 a7
                    s2 s3 (wz lenX) s5 s6 (wz hBv) s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if lenX =? 0 then J_DC5 else FZ_BIO_READ)) fc None m' (seg_rom asegs)
       /\ munch [(PD, PD + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PD [C8 (wz DT)] /\ rw_cells asegs m' PH [C8 (wz HD)])
    (MS (mkR (wz SITE_dc_pmal2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz DT) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz lenX) s5 s6 (wz hBv) s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_dc_pmal2) fc None m (seg_rom asegs)).
Proof.
  intros until pv. intros SP0 SPH MI FRE SHD PDC D0 PDS SRD PSD SHP PHC P0 PHS SRH DJ HDR DTR LX. unfold SITE_dc_pmal2, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PD, PD + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (shad PD)) = shad PD) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (shad PH)) = shad PH) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  assert (EUH : bv_unsigned (Z_to_bv 64 HD) = HD) by (apply unsigned_lit; lia).
  assert (EUD : bv_unsigned (Z_to_bv 64 DT) = DT) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lenX) = lenX) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. lfix.
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. if_false. zstep. if_false.
  zstep. replace (lenX + 0) with lenX by lia. rewrite (ubs_sw32 lenX) by lia.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - replace (lenX =? 0) with true by (symmetry; apply Z.eqb_eq; clear - K; lia). cbv iota. unfold J_DC5.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PDC| exact PHC].
  - replace (lenX =? 0) with false by (symmetry; apply Z.eqb_neq; clear - K; lia). cbv iota. zstep. zstep. zstep. unfold FZ_BIO_READ, SITE_dc_hread.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact PDC| exact PHC].
Qed.

(* [comment removed for export] *)
Lemma dc4_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (lenX : Z),
  0 <= lenX < 2 ^ 31 - 1 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_dc_hread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz lenX) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz lenX) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_DC5) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_dc_hread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz lenX) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz lenX) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_dc_hread) fc None m (seg_rom asegs)).
Proof.
  intros until lenX. intros LX MI. unfold SITE_dc_hread, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUl : bv_unsigned (Z_to_bv 64 lenX) = lenX) by (apply unsigned_lit; lia).
  zstep. if_false. unfold J_DC5. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma dc5_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (HD HL DT lenX dlen PD PH PN f eh ed hBv dBv flags PLN BI : Z) (q0 q2 : word) (bl : byte),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> 0 <= dlen < 2 ^ 31 -> 0 <= lenX < 2 ^ 31 - 1 -> HD + lenX = HL -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f eh ed flags PLN BI) -> rw_cells asegs m (sp1 + 80) [C8 q0; C8 (wz (f + 32)); C8 q2] -> rw_cells asegs m (f + 32) [C4 (wz dlen)] ->
  ro_cells asegs m (shad PH) [C1 z8] -> rw_cells asegs m PH [C8 (wz HD)] -> 0 < PH -> PH + 8 <= sp1 -> 2147450880 <= shad PH < 17594333495296 ->
  ro_cells asegs m (shad PD) [C1 z8] -> rw_cells asegs m PD [C8 (wz DT)] -> 0 < PD -> PD + 8 <= sp1 -> 2147450880 <= shad PD < 17594333495296 ->
  rw_cells asegs m HL [C1 bl] -> acc asegs m HD (lenX + 1) -> 0 < HD -> HL + 1 <= sp1 ->
  (HL + 1 <= 2147450880 \/ 17594333495296 <= HD) -> (HL + 1 <= f \/ f + 128 <= HD) -> (HL + 1 <= PD \/ PD + 8 <= HD) -> (HL + 1 <= PH \/ PH + 8 <= HD) ->
  0 < DT < 2 ^ 47 ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_dc_dread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz dBv) (wz DT) (wz dlen) a3 a4 a5 a6 a7 (wz (f + 32)) (wz dBv) (wz lenX) s5 s6 (wz hBv) s8 (wz SHB) s10 s11 t3 t4 t5 t6)
               F (wz FZ_BIO_READ) fc None m' (seg_rom asegs)
       /\ munch [(HL, HL + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' HL [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) s8 (wz SHB) s10 s11 t3 t4 t5 t6) F (wz J_DC5) fc None m (seg_rom asegs)).
Proof.
  intros until bl. intros SP0 SPH F0 FH DL LX EHL MI FRE FRF FC32 SHP PHC P0 PHS SRH SHD PDC D0 PDS SRD HB1 ACCH H0 HS HSH HF HPD HPH DTR.
  unfold J_DC5, TP_A, SHB in *. unfold dcE in FRE.
  pose proof (munch_refl [(HL, HL + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHFP : sh_fp [(HL, HL + 1)]) by sh_fp_lia.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (shad PD)) = shad PD) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (shad PH)) = shad PH) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  assert (EUH : bv_unsigned (Z_to_bv 64 HD) = HD) by (apply unsigned_lit; lia).
  assert (EUX : bv_unsigned (Z_to_bv 64 HL) = HL) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lenX) = lenX) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. lfix. rewrite EHL.
  chk_pass ACCH HL 1 0x30cac4 11 12.
  zstep. change Startup_glue.z64 with (Z_to_bv 64 0). lfix.
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. zstep. rewrite (sx32_small' dlen) by lia. zstep. zstep.
  change Startup_glue.z64 with (Z_to_bv 64 0).
  unfold SITE_dc_dread, FZ_BIO_READ. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact HB1].
Qed.

Definition J_DC6B : Z := 0x30cb08.          (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dc6a_walk : forall sp1 gp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (dlen PD PH PN f hBv dBv flags PLN BI : Z) (plv : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < f -> f + 128 <= sp1 -> 0 <= dlen < 2 ^ 31 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f hBv dBv flags PLN BI) -> rw_cells asegs m (f + 32) [C4 (wz dlen)] ->
  ro_cells asegs m (shad PLN) [C1 z8] -> rw_cells asegs m PLN [C8 plv] -> 0 < PLN -> PLN + 8 <= sp1 -> 2147450880 <= shad PLN < 17594333495296 ->
  (PLN + 8 <= f \/ f + 128 <= PLN) ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_dc_dread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz dlen) (wz PLN) a2 a3 a4 a5 a6 a7 (wz (f + 32)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz J_DC6B) fc None m' (seg_rom asegs)
       /\ munch [(PLN, PLN + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PLN [C8 (wz dlen)])
    (MS (mkR (wz SITE_dc_dread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz dlen) a1 a2 a3 a4 a5 a6 a7 (wz (f + 32)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_dc_dread) fc None m (seg_rom asegs)).
Proof.
  intros until plv. intros SP0 SPH F0 FH DL MI FRE FC32 SHL PLC L0 PLS SRL FL. unfold SITE_dc_dread, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PLN, PLN + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (shad PLN)) = shad PLN) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 PLN) = PLN) by (apply unsigned_lit; lia).
  assert (EUg : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 dlen) = dlen) by (apply unsigned_lit; lia).
  zstep. rewrite (sx32_small' dlen) by lia. zstep. if_false.
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. lfix.
  unfold J_DC6B. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact PLC].
Qed.

(* [comment removed for export] *)
Lemma dc6b_walk : forall sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (namev PD PH PN f hBv dBv flags PLN BI : Z) (pnv : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= namev < 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f hBv dBv flags PLN BI) ->
  ro_cells asegs m (shad PN) [C1 z8] -> rw_cells asegs m PN [C8 pnv] -> 0 < PN -> PN + 8 <= sp1 -> 2147450880 <= shad PN < 17594333495296 ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_dc_dread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz PN) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz 1) s6 s7 s8 s9 (wz 0) s11 t3 t4 t5 t6)
               F (wz J_RELOAD) fc None m' (seg_rom asegs)
       /\ munch [(PN, PN + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PN [C8 (wz namev)])
    (MS (mkR (wz SITE_dc_dread) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (wz namev) s11 t3 t4 t5 t6) F (wz J_DC6B) fc None m (seg_rom asegs)).
Proof.
  intros until pnv. intros SP0 SPH NMR MI FRE SHN PNC N0 PNS SRN. unfold J_DC6B, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PN, PN + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (shad PN)) = shad PN) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 PN) = PN) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. lfix.
  zstep. zstep. zstep.
  unfold J_RELOAD. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact PNC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SITE_of_pf1 : Z := 0x30cbd8.    (* [comment removed for export] *)
Definition SITE_of_pf2 : Z := 0x30cc10.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma of0_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (HD PD PH PN f eh ed flags PLN BI : Z),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f eh ed flags PLN BI) ->
  ro_cells asegs m (shad PH) [C1 z8] -> rw_cells asegs m PH [C8 (wz HD)] -> 0 < PH -> PH + 8 <= sp1 -> 2147450880 <= shad PH < 17594333495296 -> 0 <= HD < 2 ^ 64 ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_of_pf1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz HD) (wz flags) (wz 0) (wz 1019) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz FZ_PEM_FREE) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_OUTFREE) fc None m (seg_rom asegs)).
Proof.
  intros until BI. intros SP0 SPH MI FRE SHP PHC P0 PHS SRH HDR. unfold J_OUTFREE, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (shad PH)) = shad PH) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep.
  unfold SITE_of_pf1, FZ_PEM_FREE. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Lemma of1_walk : forall sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (PD PH PN f eh ed flags PLN BI pdv : Z) (phv : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f eh ed flags PLN BI) ->
  ro_cells asegs m (shad PH) [C1 z8] -> rw_cells asegs m PH [C8 phv] -> 0 < PH -> PH + 8 <= sp1 -> 2147450880 <= shad PH < 17594333495296 -> (PH + 8 <= 2147450880 \/ 17594333495296 <= PH) ->
  ro_cells asegs m (shad PD) [C1 z8] -> rw_cells asegs m PD [C8 (wz pdv)] -> 0 < PD -> PD + 8 <= sp1 -> 2147450880 <= shad PD < 17594333495296 -> (PH + 8 <= PD \/ PD + 8 <= PH) ->
  0 <= pdv < 2 ^ 64 ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_of_pf2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz pdv) (wz flags) (wz 0) (wz 1021) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz FZ_PEM_FREE) fc None m' (seg_rom asegs)
       /\ munch [(PH, PH + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PH [C8 (wz 0)])
    (MS (mkR (wz SITE_of_pf1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_of_pf1) fc None m (seg_rom asegs)).
Proof.
  intros until phv. intros SP0 SPH MI FRE SHP PHC P0 PHS SRH PSH SHD PDC D0 PDS SRD DJ PDV. unfold SITE_of_pf1, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PH, PH + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (shad PD)) = shad PD) by (apply unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (shad PH)) = shad PH) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. change Startup_glue.z64 with (Z_to_bv 64 0). lfix.
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep.
  unfold SITE_of_pf2, FZ_PEM_FREE. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact PHC].
Qed.

(* [comment removed for export] *)
Lemma of2_walk : forall sp1 gp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte)
    (PD PH PN f eh ed flags PLN BI : Z) (pdw : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) (dcE PD PH PN f eh ed flags PLN BI) ->
  ro_cells asegs m (shad PD) [C1 z8] -> rw_cells asegs m PD [C8 pdw] -> 0 < PD -> PD + 8 <= sp1 -> 2147450880 <= shad PD < 17594333495296 -> (PD + 8 <= 2147450880 \/ 17594333495296 <= PD) ->
  evt asegs (fun ms => exists m' : word -> option byte,
       ms = MS (mkR (wz SITE_of_pf2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz PD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz J_RELOAD) fc None m' (seg_rom asegs)
       /\ munch [(PD, PD + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PD [C8 (wz 0)])
    (MS (mkR (wz SITE_of_pf2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_of_pf2) fc None m (seg_rom asegs)).
Proof.
  intros until pdw. intros SP0 SPH MI FRE SHD PDC D0 PDS SRD PSD. unfold SITE_of_pf2, TP_A in *. unfold dcE in FRE.
  pose proof (munch_refl [(PD, PD + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (shad PD)) = shad PD) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep. if_false.
  zstep. zstep. zstep. change Startup_glue.z64 with (Z_to_bv 64 0). lfix.
  unfold J_RELOAD. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact PDC].
Qed.
