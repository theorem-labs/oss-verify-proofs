(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env Pm_iface Pm_iface2 RT_fk RT_fk_iface D_iface D_defs Bi_fktw RT23_iface Po_rows Po_iface Po_kit Po_mod_defs Po_udd_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_oc_defs () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K53Lib5Image:ro_bytes_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53Lib5Image>ro_cells_imageC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00c69OSSVerify5KrLib2K53B23:Po_oc_defsFpixOrientCorrect2_caseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3rtsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib2K53B238RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem7reg_getC69OSSVerify5KrLib2K53B238Po_iface4fs32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53B238Po_iface5res0dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface5optrFC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface4uctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface7po_rowsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface4LSTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface4lenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface4lresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface6LIB_POC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3ARTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53B238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53B238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235RT_fk7ret_stFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface7lpost_fC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53B23:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface6keepsLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface3p_dC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53B238Po_iface5pix1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface3p_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface3p_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface3c_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface8c_nallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface7c_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface:pix_chunksC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2K53B238Po_iface=pix_copy_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib2K53B23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53B23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface5r_fa0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface5F_1_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface5r_fa1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_ifaceBe_pixOrientCorrectC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface7OC_COSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Po_iface7OC_SECBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c69OSSVerify5KrLib2K53B23:Po_oc_defsEpixOrientCorrect2_cpsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition oc_hd   : Z := e_pixOrientCorrect + 0x128.   (* [comment removed for export] *)
Definition oc_d1   : Z := e_pixOrientCorrect + 0x13c.   (* [comment removed for export] *)
Definition oc_st   : Z := e_pixOrientCorrect + 0x184.   (* [comment removed for export] *)
Definition oc_sev  : Z := e_pixOrientCorrect + 0x1e8.   (* [comment removed for export] *)
Definition oc_jt   : Z := e_pixOrientCorrect + 0x228.   (* [comment removed for export] *)
Definition oc_o0   : Z := e_pixOrientCorrect + 0x22c.   (* [comment removed for export] *)
Definition oc_o4   : Z := e_pixOrientCorrect + 0x2c0.   (* [comment removed for export] *)
Definition oc_o2   : Z := e_pixOrientCorrect + 0x308.   (* [comment removed for export] *)
Definition oc_o3   : Z := e_pixOrientCorrect + 0x350.   (* [comment removed for export] *)
Definition oc_o1   : Z := e_pixOrientCorrect + 0x3a0.   (* [comment removed for export] *)
Definition oc_bad  : Z := e_pixOrientCorrect + 0x3e0.   (* [comment removed for export] *)
Definition oc_rot  : Z := e_pixOrientCorrect + 0x394.   (* [comment removed for export] *)
Definition oc_cp0  : Z := e_pixOrientCorrect + 0x3d8.   (* [comment removed for export] *)
Definition oc_cpy  : Z := e_pixOrientCorrect + 0x3fc.   (* [comment removed for export] *)
Definition oc_err  : Z := e_pixOrientCorrect + 0x278.   (* [comment removed for export] *)
Definition oc_ep   : Z := e_pixOrientCorrect + 0x408.   (* [comment removed for export] *)
Definition oc_fl   : Z := e_pixOrientCorrect + 0x444.   (* [comment removed for export] *)
Definition oc_fs   : Z := e_pixOrientCorrect + 0x448.   (* [comment removed for export] *)
Definition oc_fz   : Z := e_pixOrientCorrect + 0x44c.   (* [comment removed for export] *)
Definition oc_rr   : Z := e_pixOrientCorrect + 0x470.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition oc_ra_fk   : Z := e_pixOrientCorrect + 0x090.
Definition oc_ra_udd (i : Z) : Z := e_pixOrientCorrect + (if i =? 1 then 0x158 else 0x17c).
Definition oc_ra_r90  : Z := e_pixOrientCorrect + 0x164.
Definition oc_ra_des  : Z := e_pixOrientCorrect + 0x184.
Definition oc_ra_mod  : Z := e_pixOrientCorrect + 0x1e8.
Definition oc_ra_msg (o : Z) : Z := e_pixOrientCorrect + match o with 0 => 0x248 | 4 => 0x2dc | 2 => 0x324 | 3 => 0x36c | _ => 0x3bc end.
Definition oc_ra_err  : Z := e_pixOrientCorrect + 0x2b4.
Definition oc_ra_orth : Z := e_pixOrientCorrect + 0x39c.
Definition oc_ra_cpy  : Z := e_pixOrientCorrect + 0x408.
(* [comment removed for export] *)
Definition A_OC_PROC : Z := 0x45f80.
Definition A_OC_FMT (o : Z) : Z := match o with 0 => 0x45fc0 | 4 => 0x46140 | 2 => 0x46080 | 3 => 0x460e0 | _ => 0x46020 end.
Definition A_OC_ERRMSG : Z := 0x45f40.
(* [comment removed for export] *)
Definition A_OC_JT : Z := 0x45f14.
Definition OC_JT_BYTES : list Z := [108; 200; 19; 0; 224; 201; 19; 0; 72; 201; 19; 0; 144; 201; 19; 0; 0; 201; 19; 0].
Lemma oc_jt_cells : forall (m : mem), mem_inv asegs m -> ro_cells asegs m A_OC_JT [CB 20 (map (Z_to_bv 8) OC_JT_BYTES)].
Proof.
  intros m MI.
  lazymatch goal with |- ro_cells _ _ ?A [CB _ ?bs] => change (ro_cells asegs m A [CB (length bs) bs]) end; (apply (Image.ro_cells_image asegs); [exact MI | vm_compute; reflexivity | unfold A_OC_JT; lia | cbn; unfold A_OC_JT; lia]).
Qed.

Definition OC_STOPS : list Z :=
  [e_stack_malloc 0%nat; e_pixUpDownDetect; e_pixRotate90; e_pixDestroy; e_makeOrientDecision; e_lept_stderr; e_returnErrorPtr; e_pixRotateOrth;
   e_pixCopy; oc_hd; oc_st; oc_sev; oc_jt; oc_rot; oc_cp0; oc_cpy; oc_ep; oc_fl].

Section OcDefs.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixOrientCorrect2_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs pup pleft prot : Z) (vs : pixv) (cvs : cmapv) (x1 x2 x3 : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> reg_get F r_fa0 = fs32 F_1_0 -> reg_get F r_fa1 = fs32 F_1_0 ->
  a1 = Z_to_bv 64 pup -> a2 = Z_to_bv 64 pleft -> a3 = Z_to_bv 64 prot -> a4 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 -> res0d vs ->
  optrF RT Σ m pup 4 -> optrF RT Σ m pleft 4 -> optrF RT Σ m prot 4 -> List.NoDup [pup; pleft; prot] ->
  rw_cells asegs m pup [C4 x1] -> rw_cells asegs m pleft [C4 x2] -> rw_cells asegs m prot [C4 x3] ->
  uctx m sp s0 ras -> po_rows e_pixOrientCorrect ra ras ->
  lenv RT Σ m sp lo (LSTK 19) -> lres RT Σ 15 88 OC_COST -> sec_bytes (rt_live RT Σ) + OC_SECB <= SEC_BYTES -> LIB_PO m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixOrientCorrect m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv) (ub lb : word) (rot : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(pup, pup + 4); (pleft, pleft + 4); (prot, prot + 4); (pixs + 20, pixs + 24); (p_data vs, p_data vs + rsize vs)] m m'
          /\ pix_obj (rt_live RT Σ') m' pixs vs cvs
          /\ (p_d vs <> 1 -> pixd = 0 /\ rw_cells asegs m' pup [C4 x1] /\ rw_cells asegs m' pleft [C4 x2] /\ rw_cells asegs m' prot [C4 x3])
          /\ (p_d vs = 1 -> pixd <> 0 /\ pix1c (rt_live RT Σ') m' pixd vd cvd
                           /\ ((p_w vd = p_w vs /\ p_h vd = p_h vs) \/ (p_w vd = p_h vs /\ p_h vd = p_w vs))
                           /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
                           /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)
                           /\ rw_cells asegs m' pup [C4 ub] /\ rw_cells asegs m' pleft [C4 lb] /\ rw_cells asegs m' prot [C4 (Z_to_bv 64 rot)]
                           /\ In rot [0; 90; 180; 270])) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_copy_live pixd vd cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - OC_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixOrientCorrect2_case (AL : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs pup pleft prot : Z) (vs : pixv) (cvs : cmapv) (x1 x2 x3 : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> reg_get F r_fa0 = fs32 F_1_0 -> reg_get F r_fa1 = fs32 F_1_0 ->
  a1 = Z_to_bv 64 pup -> a2 = Z_to_bv 64 pleft -> a3 = Z_to_bv 64 prot -> a4 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 -> res0d vs ->
  optrF RT Σ m pup 4 -> optrF RT Σ m pleft 4 -> optrF RT Σ m prot 4 -> List.NoDup [pup; pleft; prot] ->
  rw_cells asegs m pup [C4 x1] -> rw_cells asegs m pleft [C4 x2] -> rw_cells asegs m prot [C4 x3] ->
  uctx m sp s0 ras -> po_rows e_pixOrientCorrect ra ras ->
  lenv RT Σ m sp lo (LSTK 19) -> lres RT Σ 15 88 OC_COST -> sec_bytes (rt_live RT Σ) + OC_SECB <= SEC_BYTES -> LIB_PO m ->
  bv_unsigned sp mod 32 = AL ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixOrientCorrect m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv) (ub lb : word) (rot : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(pup, pup + 4); (pleft, pleft + 4); (prot, prot + 4); (pixs + 20, pixs + 24); (p_data vs, p_data vs + rsize vs)] m m'
          /\ pix_obj (rt_live RT Σ') m' pixs vs cvs
          /\ (p_d vs <> 1 -> pixd = 0 /\ rw_cells asegs m' pup [C4 x1] /\ rw_cells asegs m' pleft [C4 x2] /\ rw_cells asegs m' prot [C4 x3])
          /\ (p_d vs = 1 -> pixd <> 0 /\ pix1c (rt_live RT Σ') m' pixd vd cvd
                           /\ ((p_w vd = p_w vs /\ p_h vd = p_h vs) \/ (p_w vd = p_h vs /\ p_h vd = p_w vs))
                           /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
                           /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)
                           /\ rw_cells asegs m' pup [C4 ub] /\ rw_cells asegs m' pleft [C4 lb] /\ rw_cells asegs m' prot [C4 (Z_to_bv 64 rot)]
                           /\ In rot [0; 90; 180; 270])) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_copy_live pixd vd cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - OC_COST <= rt_credit RT Σ').

Lemma pixOrientCorrect2_of_cases : pixOrientCorrect2_case 0 -> pixOrientCorrect2_case 16 -> pixOrientCorrect2_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_oc_defs ()) ["OcDefs"] "p'0h01Hh12ALh22H5h32H0h42H1h52H2h62H3h72H4h82H6h92H7h:2H8h;4__x1h<4__x2h=4__x3h>4__x4h?4__x5h@2C0hA3C16hB3ENVhC1FhD3H10hE3H11hF3H12hG4H12bhH3H13hI3H14hJ3H15hK3H16hL3H17hM3H18hN3H19hO3H20hP3H21hQ3H23hR3H24hS3H25hT2H9hU3PMchV3SPAhW2_HhX3_H0hY3_H1hZ3_H2h[3_H3h\3_H4h]3_H5h^3_H6h_3_H7h`7__arithha4__ffhb8__varmaphc5__withd2a0he2a1hf2a2hg2a3hh2a4hi2a5hj2a6hk2a7hl1chm3cvdhn3cvsho2fchp2gphq2lbhr2lohs1mht2m'hu2mshv4pixdhw4pixshx5plefthy4prothz3puph{1qh|2q0h}1rh~2r0i002rai013rasi023roti032s0i042s1i053s10i063s11i072s2i082s3i092s4i0:2s5i0;2s6i0<2s7i0=2s8i0>2s9i0?2spi0@2t0i0A2t1i0B2t2i0C2t3i0D2t4i0E2t5i0F2t6i0G2tpi0H2ubi0I2vdi0J2vsi0K2x1i0L2x2i0M2x3i0N2Σi0O3Σ'p%0p&0p;1p;2p;3p;5p;4p;6p;7p;Sp;Dp;8g00R?k109Tg0000j14Tg003Tj1<Tg00SLk10UTg000Uj1aTg0013j1iTg002oj1>Tg00TDk20`Tg001Vk10]Tg006Bj1`Tg00U0k10TTg00Unk10DTg00Vjj2LTg005hj33k20BTg00WPk206Tg00X:k10cTg00Y3j2JTg00Yok505Tg00Zmk102Tg00[jj1QTg00\Ck10aTg00]=j5hTg0042j1ZTg00^9j2wTg00^Uj1GTg00_Mk40XTg00`Hk30WTg00aDk10STg00b?k60RTg00c:k50NTg00d5k10CTg00e3k10ATg00enj1oTg00fij1XTg00gdj3MTg00h\j20Tg00iFj21Tg00jAS00j2_Tg00<6j28Tg00j[j2~Tg00k<j2STg00kYj2\Tg00l6j29Tg00=2j27Tg00lVj2}Tg00@:j2?Tg00m=j2|Tg00mdj2zTg00nJj2yTg00A:j2xTg004Rj2fTg00o0k10_Tg00oNk20^Tg00GFj1HTg00ooj3gTg010Xj2vTg011Ak20\Tg011mj2YTg00FBj3@Tg012Yj2uTg006bk10[Tg0137j4eTg007@k10ZTg007^k10YTg008Ij2dTg013Uk10VTg0147j2WTg014Zj3rTg00A[j3mTg008lj4cTg015=k70QTg015ak70PTg009Wk20MTg00:9k20LTg00:ek30KTg00;Dk40ETg016EmS0GTg017Bk40Hk50lTg018;mD0ITg0194k70JTg01:2j2pTg01:Rk10@Tg01;Nk70?Tg01<Kk10OTg01=ER0j26Tg01=`k50>Tg01>Zj1qTg01?Tj1nTg01@Nj1lTg01AKj1sTg01BEk10=Tg01CDk10<Tg01DBk30;Tg01EAk30nTg01E^k30mTg01F5j2ETg01FOk20kTg01Flk40jTg01Gnk208Tg01Hlk207Tg01Ijj2jTg01JGk30gTg01K<k40fTg0028k20eTg01L5k40:Tg01Ljj3kTg00Fbk70dTg01MSk60bTg01N7k80hTg01N[k40iTg00KNR1f0R2g00MIR333p=:f1R4=@12p=Og01O;R5?@42p=Ig00LQR6f2R7P4P2H0fp=C1774/82p=b20e62p=FP6P7P4P2H0:p=Pf5R8f4R9'7g01P3R:'8f3R;/97=3131842'6'6p==g01Q2R<,j8/8917;7/84/62'6p=A1642,67p=21074/92p=;A3142p=5P6P;P7P4H0:/62p=^A3173A3142'_p=B1j4</82p>0419;7=3131842'6p=]1789/8;1774/8:/62'6p>031742/8:p>011942=313p>001874/62p=U1842,67p={1v12p=NAk142p=VAk1429k17p=[P1P4g01R0P2Ccp=KP4g00I0R:g00IOR<P<g00IoR=P2g00JOK0dp=DP4P:P<P<P=P2J0bp=tP;P:P<P<P=P7P4P2L0hp=RA3142,_7p>0FP1P1P4P2H0ip=T&093g00KlR>#4R?#4R@#4RA#4RB#<RC$09p,2RTRD$0UREg01RWp-0[%4BRF#4#aRG#iRH%>?RI#a00`H%aF#i%aA#i$0]\HRAg01SMRJg01TJRK%`1f]RL$0Tf^RM$0Df[RNg01UH,LG53HfVS01f<S02,LG53HfAROg01V?+06g01W9$0cRP53HfBS03g01X3+06=3HPfXRPf>S04,LG53HRQ1LG393HPfhRR,JDfERSfCS05f?S06Q04I05f@S07$02#:#Q&0aOPDfkRTfHRUPS%<@RVDhPDflRWfIRXPSPVDhPDfmRYfJS08PSPVDhfGS09fFS0:%Z1S0;'O'O,OU,w1fLS0<fDS0=#G%Z5R5'IRZ7CXfMS0>?CXZfNS0??CXZfOS0@foRZfiR[Q0=H0Xg01XmS0AfqR\<0WSPDftS0BfQS0CP\fPS0D%>@#>#<$0SR]J0RPDfuR^%>>R_#>#>#<%>I#4S0E#4#4#<g01Z4S0FI0NfvR`,JD$0Cg01[0g01[l3bfTRa$0AP0fURb#o%XbfxRc=MDb%Fb10G^Rd9Pba11DcRePaPaP]PdPdPCPdPCPdPeE=EA3232%<FRF9;G`Re#:S0G15eCS0H'_P;fWRe#o%XPf{Rf=MDP%FP10GcRg9PPe11DfRhPePeP]PgPgPCPgPCPgPhE=EA3232P0fYRh#Xf|Rg=MDh%FhPhPPfyS0I,0GRi11DgRjPPPPP]PiPiPCPiPCPiPjE=EAC^32fzRj=;GFRi?BiCP2%XNp+01@Rif\Rk5MD%FkPkPN10GgRl11DiRmPNPNP]PlPlPCPlPCPlPmE=EAC^32P0p+01ARm=MDL%FLf}S0J,0GRl9PLk11DmRnPkPkP]PlPlPCPlPCPlPnE=EA32f~=;GFRn?BnCP2p+01CRnf_Rl5MDf`Ro#F10GmRp9Polp+01D,1DRqPlPlP]PpPpPCPpPCPpPqE=EA32P0faRq#FPqPop+01BRp,0GRrp+01ERs,1DRtPoPoP]PrPrPCPrPCPrPtE=EAC^A;GnFRt?BtCP2fcRt#FfdRrPt10GsRup+01HRv,1DRwPtPtP]PuPuPCPuPCPuPwE=EAC^P0feS0Kp+01F,0GRw7Prp+01IRu,1DRxPrPrP]PwPwPCPwPCPwPxE=EAp+01G=;GFRx?BxCP2fgRxffRw10Gv3Pp+01L,1DRvPxPxP]10GuRuPuPCPuPCPuPvE=EAP0p+01MRv,1DRu004RPRP]p+01J,0GRyPyPCPyPCPyPuC]J03p+01K=;GFRu?BuCP2p+01ORu,1DfjRy+04PTP]10GvRvPvPCPvPCPvp+01PRv,1DC]J03P0p+01N,0GRz9bW]PzPCPzPCPzp+01QRz,1DE=A;GuFRu?BuCP2fnRu10Gv7b]10GzRzPCPzPCPzp+01TRz,1DE=P0p+01R,0GR]001CP]PCP]p+01UR],1DC]p+01S=;GFRv?BvCP210Gz001C10G]R]PCP]p+01XR],1DC]P0p+01V,0GR0000Cp+01YRz,1D,80p+01W=;GFR0?B0CP210G]000C10Gzp+01\Rz,1D'8p+01Z,0G/~F%:FR]#Qp+01[,0GR01S0F,\F190F'7'5[1}0F1?3FR010GzRz/9FRv1?vF5U3[1|zF1?F3p+01],0GRz/9FRv,?F?{v3[1zzFp+01^,0GRz/SF#:\]1yzFp+01_,0GRz/9F/5z\]1SzFP1p+01`=;GFP1p+01a,0G/~C%:CRz#Qp+01b,0GRv1SvC,\C19vC'7'5[1}vC1?3CRvp+01c,0GR{/9CR|1?|C5U3[1|{C1?C3p+01d,0GR{/9CR|,?C?{|3[1z{Cp+01e,0GR{/SC#:\z1y{Cp+01f,0GR{/9C/5{\z1S{CP1p+01g=;GCP1P8g00QYR{1x3C'fPveO11?2C9U32f=S0L1x3F,f{P0eO1f8R01?0F5U3g00NgR{&0_>-0^1Rvg00P:S0M#HS0N#HR|#HR}#HS0O#H#HR~#N5g1S0P%N}R}%N|R|9g1vS0QQ0M,v1S0M'V3[%H~#NS0RQ0O#NR~9g1vS0O1V}|3[Q0N#NR|Q0M'Vg01\j+0\Rv'Y'YQ0PQ0Q,V}7[~Q0RQ0O1V}|3[/Yv'Y%Z{5@{3@%`{P1P11u19P7&0[1R{CeP4P11u18P;P{CeCe&0Z1&0Y1R{P{1d1CRv1d13R|'K,D{,t{&0V<R}1W1_S0O1W1I9r1v1W1?S0R5m1'K,D{CRP}P{P{P:P<P<P=P1P|g00OS1W1>R?Cc,D{P1P?g01]V1d1FR~Cc,D{K0QP}P{P{1K~|,D{,t{P}Q0O1W1@9r1~=m1?'K,D{CRP}P{Q0R/K|,D{P}P{P:P<P<P=1K?|,D{1K?v,D{K0PCRCRCRCR20M{=P2P7g00MgR{g00NGR='f20L27=3{=dB0K134H0EbabbbcX;1X<1X=1X>1X?1g01^=R=\z1\C8/77,5;[1?4F9U34P=\]f6R],\F/7;,58[%:9R=B0F=9C[[[[^;1^<1^=1^>1^?1P2P9f;R=p+01k,0GP;f:R7f9RzP4Q07Q03O9b`b3b2b~b|b:b9b8b2b7b}b{b6b5b4b3b0W_WVP4P2O2n2001000000121000000W0W^P4P2O2n2001000000121000000W0W]P4P2O2n2001000000121000000W0W\P4P2O2n2001000000121000000W0W[P4P2O2n2001000000121000000W0WZP4P2O2n2001000000121000000W0WYP4P2O2n2001000000121000000W0WXP4P2O2n2001000000121000000W0WWP4P2O2n200100000012100000019dFRd?BdCQ00Q0GQ0HPDPjQ0Ig01^ZRdPcfwR?P`P^Q0BfsRvfrR|P\fpR<PZPuPYPWPTPyP[PRPxPwQ0KPrPtfbR:PqPoPlPMPLPkPNfZR}PhPPQ0APeNS0G+0BH0Hg01_aPDP]PpPnPpPmPiPfPjP\P<PZPuPYPWPTPyP[PRf7Ri,LGPtP2P4ND0IPDPsP0PqP2PpPoK0JPD1JDsPsPp1p11Rp17MV,TM17LV,TL17kV,Tk%4I#4#<,7l%4_#4#4#<,7l'T&02NR_&0@N,7_'T%Zp5@p5@p5@p5@p3@PqP2K0?1JD0P2PlPNP}I05&0ON%<>'5R>#Q%:0R_%G}/I59C4l%Gh/I59C4M%GP/I59C4L'632[%Q_1JDzP4P0PiP]I0>%qiR_%qkRI'5%niRV%nkRs'5'615_s15VI'6'_%lk#:%l0#:[%li#:#Q%si%sk'5&0=i&0=k'5&0<i&0<k'532[B0;0i]B0;okN60n1,w1%G8/I59C4l%G9/I59C4M1LG;#G/I59C4LQ0E#>#4R4#<%44#<%>B#>#>#4#<Q0;'O'O'O9@13:0m1;'632323232\>'63232XtA,EAXudPiI0l%`pRp1JD]P{Pp20k831JDnR3P8P9P;P3H0jn010000002000033g00Jo,p1#`208D]208Dn3311D]11Dn'5207DnQ0F'j207D]'83232Z021,E1XqH,EHZ0HH,EHXmK,EKZ0IJ,EJXv1,E1Z0OE,EEWl60g6P2A;G?FRF#:Q0JPfPjQ0IPcP?P`P^Q0BPvP|P\P<PZPuPYPWPTPyP[PRPxPwQ0KPrPtP:PqPoPlPMPLPkPNP}PhPPPeQ01PbPafSRGfRR6Q0CQ0DQ0@Q0?Q0>Q0<fKREQ08PXPUQ09Q0:PSQ0=Q05Q03POQ07Q06Q04Q0LQ02P=P7PzP0PiP]P8P9P;P2OzW1P2O115FCPgPfPjQ0IPcP?P`P^Q0BPvP|P\P<PZPuPYPWPTPyP[PRPxPwQ0KPrPtP:PqPoPlPMPLPkPNP}PhPPPeQ01PbPaPGP6Q0CQ0DQ0@Q0?Q0>Q0<PEQ08PXPUQ09Q0:PSQ0=Q05Q03POQ07Q06Q04Q0LQ02P=P7PzP0PiP]P8P9P;P2OzW1P2O1n200100001021000010000b1WSWRWQWBWPWOWNWMWLWKWJWIWHWGWFWEWDXTQX:QW9W8W2W7W6W5W4Y01Z0MHZ0LHZ0KHWnY0JXy1Xx1Xz1Xw1Xr1WsWoWCZ0FHZ0EHZ0DHZ0CHZ06HZ05HZ0>HZ0=HZ0<HZ0;HZ0:HZ09HZ08HZ07HXkHXjHXiHXhHXgHXfHXeHXdHZ04HZ03HZ0BHZ0AHZ0@HZ0GHXpHZ0?HY00WUY0Ng01`VeWAW@o"). Qed.

(* [comment removed for export] *)
Lemma pixOrientCorrect2_weaken : forall (P : Prop), P -> P.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_oc_defs ()) ["OcDefs"] "h01Hh11Pp-0f0R0P0W0W1o"). Qed.
End OcDefs.
