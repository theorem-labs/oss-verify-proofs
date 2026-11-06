(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnDivWords BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_topA AsStruct2 AW_num_bits_word BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_part_recursive AW_kara_closedA AW_mul_core.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctx_getA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import BgLeaves BgLive DivModel.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_mul.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_expandAF W_lshiftAF W_copyAF W_ctxAF W_ctx_endAF W_ctx_getAF W_div_tailAF W_div_padAF W_divAF W_bndivAF W_mulAF W_mulA2F ExpKitAF MulOneKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require MulOneCoreA.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import UbStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2268436 => 2
  | 2268448 => 1
  | 2268452 => 2
  | 2268496 => 2
  | 2268500 => 1
  | 2268504 => 2
  | 2268548 => 1
  | 2268552 => 2
  | 2268596 => 1
  | 2268600 => 2
  | 2268632 => 2
  | 2268636 => 1
  | 2268640 => 2
  | 2268800 => 2
  | 2268804 => 1
  | 2268808 => 2
  | 2268824 => 1
  | 2268828 => 2
  | 2268856 => 1
  | 2268860 => 1
  | 2268864 => 2
  | 2268904 => 2
  | 2268908 => 1
  | 2268912 => 1
  | 2268916 => 2
  | 2269036 => 2
  | 2269040 => 1
  | 2269044 => 2
  | 2269148 => 1
  | 2269152 => 2
  | 2269192 => 2
  | 2269196 => 1
  | 2269200 => 1
  | 2269204 => 2
  | 2269328 => 1
  | 2269332 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).

Notation disp_normal := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.disp_normal.
Notation disp_comba8 := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.disp_comba8.
Notation disp_part := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.disp_part.
Notation disp_rec := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.disp_rec.
Notation disp_kara := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.disp_kara.
Notation mul_res := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.mul_res.
Notation mul_res_okm := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.mul_res_ok.
Notation kara_kj_facts := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.kara_kj_facts.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ml_start := (E_bn_mul_fixed_top_229bac : uk_call BN_MUL_FIXED_TOP 0x229d94 BN_CTX_START).
Local Notation E_ml_get1 := (E_bn_mul_fixed_top_229bc0 : uk_call BN_MUL_FIXED_TOP 0x229da8 BN_CTX_GET).
Local Notation E_ml_wexpc := (E_bn_mul_fixed_top_229bec : uk_call BN_MUL_FIXED_TOP 0x229dd4 BN_WEXPAND).
Local Notation E_ml_get2 := (E_bn_mul_fixed_top_229cc0 : uk_call BN_MUL_FIXED_TOP 0x229ea8 BN_CTX_GET).
Local Notation E_ml_wexpr1 := (E_bn_mul_fixed_top_229ce8 : uk_call BN_MUL_FIXED_TOP 0x229ed0 BN_WEXPAND).
Local Notation E_ml_wexpr2 := (E_bn_mul_fixed_top_229cf8 : uk_call BN_MUL_FIXED_TOP 0x229ee0 BN_WEXPAND).
Local Notation E_ml_wexpn := (E_bn_mul_fixed_top_229d80 : uk_call BN_MUL_FIXED_TOP 0x229f68 BN_WEXPAND).
Local Notation E_ml_wexpp1 := (E_bn_mul_fixed_top_229e08 : uk_call BN_MUL_FIXED_TOP 0x229ff0 BN_WEXPAND).
Local Notation E_ml_wexpp2 := (E_bn_mul_fixed_top_229e18 : uk_call BN_MUL_FIXED_TOP 0x22a000 BN_WEXPAND).
Local Notation E_mul_ft := (E_BN_mul_229ac8 : uk_call BN_MUL 0x229cb0 BN_MUL_FIXED_TOP).

Lemma ro_cells_app_lA : forall (m : mem) A cs1 cs2, ro_cells bgbsegs m A (cs1 ++ cs2) -> ro_cells bgbsegs m A cs1.
Proof. intros m A cs1 cs2. unfold ro_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app. tauto. Qed.

Lemma core_premsA1 : forall Σ OW LB m ls PL EA rr x y R X Y Dr al bl lo SPv,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPv USTACK_TOP -> frames_lb PL LB -> stk bgbsegs m lo (SPv + -112) -> mem_inv bgbsegs m ->
  ref_at ls OW PL rr R -> ref_at ls OW PL x X -> ref_at ls OW PL y Y -> rr <> y -> hpl PL rr -> x = ROne -> y <> ROne -> nbuf PL y ->
  rw_cells bgbsegs m R (bn_cells Dr (getbn rr ls)) -> BnRepDefs.bn_arr m OW Dr (getbn rr ls) ->
  (al <= bn_top (getbn x ls))%nat -> (bl <= bn_top (getbn y ls))%nat -> (0 < al)%nat -> (0 < bl)%nat -> (al + bl <= bn_dmax (getbn rr ls))%nat ->
  ACEIL <= lo -> lo <= SPv - 112 - MUL_CST -> SPv + 16 <= USTACK_TOP ->
  exists Dy,
    mulc_preA (Z_to_bv 64 SPv) lo R X Y Dr DATA_ONE Dy MUL_CST (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls)))
    /\ MulOneCoreA.mulc_memA (Z_to_bv 64 SPv) m lo R X Y Dr DATA_ONE Dy (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls))).
Proof.
  intros Σ OW LB m ls PL EA rr x y R X Y Dr al bl lo SPv HEAP LS FROK NOFR ST MI HR HX HY NEY HPr EOx NROy NBy SR ARR HAL HBL AL0 BL0 HD CEIL LO SPT.
  subst x.
  change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEY.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  rewrite MUL_CST_val in LO.
  assert (ESP : bv_unsigned (Z_to_bv 64 SPv) = SPv) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_wf_ok rr ls WFS HVR NROr) as (OKR1 & OKR2 & OKR3 & OKR4).
  pose proof (st_wf_ok y ls WFS HVY NROy) as (LMY & TDY & DMY & _).
  unfold BG_DMAX in DMY, OKR3.
  destruct (one_viewA Σ OW LB m ls PL EA X HEAP LS MI HX) as (EX & EONE & ROX & HLX1 & ACX & ACDX & ALXs & ALDX & X0' & PDX & XC' & DXC). subst X.
  destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HPr) ltac:(first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))])) as (UR & _ & DR0 & DRC & _ & DSEPR).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NROr) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  assert (RIM : R + 24 <= 65536 \/ 12554240 <= R) by (clear - SAI Ra1 Ra2; lia).
  destruct (operand_view_ne Σ OW LB m ls PL EA SPv rr R Dr y Y bl HEAP LS FROK NOFR HR NROr SR ARR HY NROy HBL ltac:(congruence) NBy)
    as (Dy & HYd & HLY & UY & ARRY & Y0' & YC' & DY0 & DYC & SYR & SYA & _ & ALY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HY NROy) as (ACY & ALYs & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
  destruct (arr_shA _ _ _ _ _ _ HEAP ltac:(first [exact ARRY | exact (bn_arr_nofr PL y _ _ _ _ PWF NOFR NROy ARRY ltac:(solve_nbuf))])) as (ACDY & ALDY & _).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARR ltac:(lia)) as (PDR & IDR).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARRY ltac:(lia)) as (PDY & _).
  assert (EAL : al = 1%nat) by (rewrite EONE in HAL; cbn in HAL; clear - HAL AL0; lia). subst al.
  rewrite EONE. cbn [bn_buf bn_const_one firstn].
  assert (LLB : length (firstn bl (bn_buf (getbn y ls))) = bl) by (apply firstn_length_le; exact (Nat.le_trans _ _ _ HBL TDY)).
  exists Dy. split.
  - unfold mulc_preA. rewrite LLB, ESP. cbn [length].
    split; [constructor; [unfold limb, BW; clear; lia| constructor]|]. split; [apply limbs_firstn; exact LMY|]. split; [exact (bg_okm _ (st_wf_ok rr ls WFS HVR NROr))|].
    split; [clear - HBL TDY DMY; unfold bn_dmax in *; lia|].
    split; [rewrite MUL_CST_val; unfold BnHeapA.ACEIL, CONST_ONE, DATA_ONE in *; clear - SA0 SAC Ra1 Ra2 Y0' YC' DR0 DRC DY0 DYC CEIL LO SPT TDY HBL C1; unfold bn_dmax in *; lia|].
    split; [exact (DSEPR rr R HR)|]. split; [unfold DATA_ONE; clear - RIM; lia|]. split; [clear - SYA TDY HBL; unfold bn_dmax in *; lia|].
    split; [unfold DATA_ONE; clear - IDR; lia|]. split; [clear - ALY TDY HBL; unfold bn_dmax in *; lia|].
    split; [unfold CONST_ONE; clear - RIM SYR; lia|].
    split; [exact (conj ALR (conj ALXs (conj ALYs (conj ALDR (conj ALDX ALDY)))))|].
    unfold SHHI. split; [exact OFR|]. split; [exact OFDR|]. split; [unfold BnHeapA.ACEIL in *; clear - C2 CEIL; lia|].
    split; [exact IDR|]. split; [exact PDR|]. split; [exact PDX|]. split; [exact PDY| exact RIM].
  - unfold MulOneCoreA.mulc_memA. rewrite LLB, ESP. cbn [length].
    split; [exact SR|]. split; [exact UR|].
    split; [exact (ro_cells_app_lA m CONST_ONE [C8 (wz DATA_ONE)] _ ROX)|]. split; [exact HYd|]. split; [exact HLX1|]. split; [exact HLY|].
    split; [exact ST|]. split; [exact MI|]. split; [exact (AH_shb _ _ _ _ HEAP)|].
    split; [exact ACR|]. split; [eapply acc_sub; [exact ACX | lia | lia]|]. split; [eapply acc_sub; [exact ACY | lia | lia]|].
    split; [exact ACDR|]. split; [exact ACDX|].
    eapply acc_sub; [exact ACDY | lia | clear - TDY HBL; unfold bn_dmax in *; lia].
Qed.

Lemma one_opndA : forall Σ OW LB m (ls : bstate bptr) PL EA x X,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> mem_inv bgbsegs m -> ref_at ls OW PL x X -> x = ROne ->
  getbn x ls = bn_const_one
  /\ ro_cells bgbsegs m X (bn_cells DATA_ONE (getbn x ls))
  /\ acc bgbsegs m X 24 /\ X mod 8 = 0 /\ (X + 24 <= SHLO \/ SHHI <= X)
  /\ 0 < X /\ X + 24 <= ACEIL /\ X = CONST_ONE.
Proof.
  intros Σ OW LB m ls PL EA x X HEAP LS MI HX ->.
  destruct (one_viewA Σ OW LB m ls PL EA X HEAP LS MI HX) as (EX & EONE & ROX & _ & ACX & _ & ALX & _ & X0 & _ & XC & _). subst X.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1.
  split; [exact EONE|]. split; [rewrite EONE; exact ROX|]. split; [exact ACX|]. split; [exact ALX|].
  split; [left; unfold SHLO, CONST_ONE; clear; lia|]. split; [exact X0|]. split; [clear - XC C1; lia | reflexivity].
Qed.

Lemma mul_endA1 : forall (ac : Z) (qc : bptr)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL : Z)
    (rr x y : bnref) (R X Y : Z) (na nb : bool) (v : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state),
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  pl_ctx PL = Some (ac, qc) -> hpl PL rr -> x = ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras TOTAL rr x y R X Y ac na nb v Σ' ms' ->
  implA (BN_CTX_end ops (setbn rr (bn_with_neg (getbn rr (snd v)) (xorb na nb)) (snd v))) Σ'
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA TOTAL (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1)) ms'.
Proof.
  intros until ms'. intros LO EC HPr EOx NROy NBx NBy (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x22 & x23 & x24 & x25 & x27 & t3 & t4 & t5 & t6 & FE & fcE
                             & mE & OWE & w0 & used & -> & ENV & USED & LS & HR & HX & HY & ENA & ENB).
  change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr.
  destruct v as [[] lsE]. cbn [fst snd] in *.
  unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (one_opndA Σ' OWE LB mE lsE PL EA x X HEAP LS MI HX EOx) as (_ & SX & ACX & ALX & OFX & X0 & XC & _).
  destruct (open_ro Σ' OWE LB mE lsE PL EA (bv_unsigned sp) y Y HEAP LS FROK NOFR HY NROy) as (Dy & SY & _ & _ & Y0 & YC & _).
  unfold bn_cells, MallocRep.wz in SX, SY. rewrite ENA in SX. rewrite ENB in SY.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HY NROy) as (ACY & ALY & OFY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
  destruct (lib_state_open [] lsE mE OWE PL EA rr R LS ND HR ltac:(intros []) NROr) as ((Dr & SR & ARR) & OKR & LSH).
  apply (fun ARRnb__ => bn_arr_nofr PL rr _ _ _ _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS))) NOFR NROr ARRnb__ (hpl_nbuf PL rr HPr)) in ARR.
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct (bn_arr_facts_w lsE OWE PL EA (bv_unsigned sp) USTACK_TOP Σ' LB mE rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HPr) ltac:(first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))])) as (U & LENW & D0 & DC & DI & DSEP).
  specialize (DSEP rr R HR).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NROr) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  set (b := getbn rr lsE) in *.
  unfold bn_cells, MallocRep.wz in SR.
  assert (NA : 0 <= Z.b2z na <= 1) by (destruct na; cbn; lia).
  assert (NB : 0 <= Z.b2z nb <= 1) by (destruct nb; cbn; lia).
  assert (AX : 0 < X /\ X + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - X0 XC CEIL LO SPR SPT; lia).
  assert (AY : 0 < Y /\ Y + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Y0 YC CEIL LO SPR SPT; lia).
  assert (ARR24 : 0 < R /\ R + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA0 SAC Ra1 Ra2 CEIL LO SPR SPT; lia).
  pose proof (munch_refl [(R, R + 24)]%Z mE) as MU. pose proof (wmono_refl bgbsegs mE) as WM.
  assert (OFF : offshW [(R, R + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFR; lia).
  apply hide_intro in OFX. apply hide_intro in OFY. apply hide_intro in OFR. apply hide_intro in SAI. apply hide_intro in DI.
  apply implA_from_evt.

  ub. zstep.
  do 2 zstep. shl_with ACY ALY. chk0.
  zstep. do 2 zstep. shl_with ACX ALX.
  step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
  chk0.
  zstep. do 2 zstep. shl_with ACR ALR.
  step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
  chk0.
  zstep.
  setreg 10%Z (Z_to_bv 64 (Z.b2z (xorb na nb))) ltac:(clear; destruct na, nb; reflexivity).
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

  assert (HWL : Forall (w_lib lsE OWE PL lo (bv_unsigned sp)) [(R, R + 24)]).
  { constructor; [w_lib_ref HR NROr | constructor]. }
  assert (WOK : Forall (w_ok OWE LB lsE PL EA (bv_unsigned sp) [rr]) [(R, R + 24)]).
  { constructor; [eapply (w_struct OWE LB lsE PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity| exact HR| exact NROr| cbn; clear; lia| cbn; clear; lia] | constructor]. }
  set (lsN := setbn rr (bn_with_neg b (xorb na nb)) lsE).
  assert (LSN : lib_state lsN m1 OWE PL EA).
  { unfold lib_state, lsN. eapply (lib_state_close [] lsE m1 OWE PL EA rr R); [| exact ND| exact HR| exact NROr| | |].
    - eapply (lib_state_frame _ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP | exact LSH | exact MU | exact WM | exact FROK | exact WOK].
    - exists Dr. split; [unfold bn_cells, bn_with_neg, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; exact SR|].
      eapply bn_arr_of_u64arr; [first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))] | exact U].
    - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, bn_with_neg, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. auto.
    - apply ids_ok_setbn_same; [exact IDS | exact HVR | reflexivity]. }
  match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1, FRx : rw_cells _ m1 (bv_unsigned sp + -112) _ |- _ =>
    assert (ENVN : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ' lsN m1 OWE);
    [ apply cenv_setbnA; [| exact HVR | reflexivity];
      eapply (cenv_silentA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m);
        [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact STx | exact MIx | unfold mul_frame; cbn [app]; exact FRx | cbn; lia]
    | ] end.
  clear SR U MU WM LSH ENV LS.
  ub; zstep. if_cases KE; zify_cond KE; [|exfalso; apply KE; reflexivity]. clear KE.
  ub; zstep. ub; step.
  ub; zstep. ub; step.

  apply evt_done. fold b. fold lsN.
  eapply implA_post_evt.
  { eapply BN_CTX_end_walkA with (lo := lo) (OW := OWE) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| reflexivity | exact EC | reflexivity].
    eapply cenv_preA; [exact ENVN | exact LSN | unfold BN_CTX_END_STACK; clear - LO; lia | clear - USED; lia]. }
  cbv beta. intros [uE lsF] ΣF msF PO.
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -112) TOTAL Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVN))].
  cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & FF & fcF & mF & OWF & PLzF & -> & CPF & (EPLzF & _)).
  subst PLzF. specialize (CPF eq_refl).
  assert (EF : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + 0) ΣF lsF mF OWF
               /\ lib_state lsF mF OWF PL EA) by (eapply cenv_postA; [exact ENVN | exact CPF]).
  destruct EF as (ENVF & LSF).
  cbn [fst snd] in *.
  fix_ret.
  pose proof (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m _ _ _ _ _ _ ENVF LSF ltac:(clear - USED; lia))
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  env_openA ENVF. unfold mul_frame in FRe. cbn [app] in FRe.
  ub; zstep. do 13 (ub; step).
  release_frame FRe STe (bv_unsigned sp). ub; step. ub; step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists mF, OWF, PL. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. split; reflexivity.
Qed.

Lemma mul_finish1A1 : forall (ac : Z)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z) (w0 : word)
    (Σ2 : rts RT) (ls2 : bstate bptr) (m2 : mem) (OW2 : list block) (rr x y : bnref) (R X Y Dr n8 CST : Z)
    (w : list Z) (topn : nat) (x22 x23 x24 x25 x27 : word) (ms' : machine_state),
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ2 ls2 m2 OW2 ->
  used <= TOTAL -> lib_state ls2 m2 OW2 PL EA ->
  0 <= CST -> lo <= bv_unsigned sp - 112 - CST ->
  ref_at ls2 OW2 PL rr R -> ref_at ls2 OW2 PL x X -> ref_at ls2 OW2 PL y Y -> rr <> x -> rr <> y -> hpl PL rr -> x = ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  rw_cells bgbsegs m2 R (bn_cells Dr (getbn rr ls2)) -> BnRepDefs.bn_arr m2 OW2 Dr (getbn rr ls2) ->
  limbs w -> (0 < length w <= bn_dmax (getbn rr ls2))%nat -> (topn <= bn_dmax (getbn rr ls2))%nat -> n8 = 8 * Z.of_nat (length w) ->
  mulc_postA sp gp (wz TP_A) m2 lo R Dr (getbn rr ls2) F fc sp (Z_to_bv 64 ac) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R)
             x22 x23 x24 x25 x27 [(Dr, Dr + n8); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)] topn w (fun _ => True) ms' ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras TOTAL rr x y R X Y ac
            (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)) (tt, setbn rr (mul_res (getbn rr ls2) w topn) ls2) Σ2 ms'.
Proof.
  intros until ms'. intros ENV USED LS HCST LO HR HX HY NEX NEY HPr EOx NROy NBx NBy SR ARR LW [HW0 HWD] HTD ->
    (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MU & WM & MI3 & SR3 & HR3 & ST3 & _).
  change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEX. apply hide_intro in NEY.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_open [] ls2 m2 OW2 PL EA rr R LS ND HR ltac:(intros []) NROr) as (_ & OKR & LSH).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct (bn_arr_facts_w ls2 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ2 LB m2 rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HPr) ltac:(first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))])) as (U & LENW & D0 & DC & DI & DSEP).
  pose proof (DSEP rr R HR) as DSR.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NROr) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
  set (br := getbn rr ls2) in *.
  unfold BnRepDefs.bn_arr, bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
  2:{ exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HWD. rewrite Eb in HWD. cbn [length] in HWD. lia. }
  destruct ARR as [HinR _].
  pose proof (AH_range _ _ _ _ _ _ _ HEAP HinR) as (_ & _ & _ & _ & DRI).
  assert (HWL : Forall (w_lib ls2 OW2 PL lo (bv_unsigned sp)) [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
  { constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | lia]|].
    constructor; [w_lib_ref HR NROr|].
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  assert (WOK : Forall (w_ok OW2 LB ls2 PL EA (bv_unsigned sp) [rr]) [(Dr, Dr + 8 * Z.of_nat (length w)); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)]).
  { constructor; [eapply (w_limbs OW2 LB ls2 PL EA (bv_unsigned sp) false [rr] _ rr pr Dr); [left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; lia | cbn [fst snd]; fold br; lia]|].
    constructor; [eapply (w_struct OW2 LB ls2 PL EA (bv_unsigned sp) false [rr] _ rr R); [left; reflexivity| exact HR| exact NROr| cbn; clear; lia| cbn; clear; lia]|].
    constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (apply splice_length; unfold bn_dmax in *; lia).
  set (lsN := setbn rr (mul_res br w topn) ls2).
  assert (LSN : lib_state lsN m3 OW2 PL EA).
  { unfold lib_state, lsN. eapply (lib_state_close [] ls2 m3 OW2 PL EA rr R); [| exact ND| exact HR| exact NROr| | |].
    - eapply (lib_state_frame _ LB (bv_unsigned sp) USTACK_TOP); [exact HEAP | exact LSH | exact MU | exact WM | exact FROK | exact WOK].
    - exists Dr. split; [unfold bn_cells, mul_res, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR3|].
      unfold BnRepDefs.bn_arr, bn_arr, mul_res. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LSP.
      split; [exact HinR|].
      eapply arr_splice0; [exact U | exact MU | exact WM | exact HR3 | unfold bn_dmax in *; lia | |].
      + cbn [disjoint_from]. lia.
      + cbn [disjoint_from]. unfold bn_dmax in *. lia.
    - apply mul_res_okm; [exact OKR | exact LW | lia | exact HTD].
    - apply ids_ok_setbn_same; [exact IDS | exact HVR |]. unfold bn_blocks, mul_res, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
  unfold mul_joinA. do 23 eexists. exists m3, OW2, w0, used. split; [reflexivity|]. cbn [fst snd]. fold lsN.
  split.
  { apply cenv_setbnA; [| exact HVR | fold br; unfold mul_res, bn_blocks; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Edr; reflexivity].
    eapply (cenv_silentA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m);
      [exact ENV | exact LS | exact MU | exact WM | exact HWL | exact ST3 | exact MI3 | | exact FSZ].
    unfold mul_frame. cbn [app]. eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn. unfold BnHeapA.ACEIL in *. lia. }
  split; [exact USED|]. split; [exact LSN|].
  split; [apply ref_at_setbn; exact HR|]. split; [apply ref_at_setbn; exact HX|]. split; [apply ref_at_setbn; exact HY|].
  unfold lsN. rewrite !getbn_setbn_other by assumption. split; reflexivity.
Qed.

Lemma mul_path_normalA1 : forall (ac : Z)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (used : Z) (w0 : word)
    (Σ1 : rts RT) (ls1 : bstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z) (al bl : nat)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x27 t3 t4 t5 t6 : word),
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 m1 OW1 ->
  used + MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls1 m1 OW1 PL EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls1 OW1 PL rr R -> ref_at ls1 OW1 PL x X -> ref_at ls1 OW1 PL y Y -> rr <> x -> rr <> y -> hpl PL rr -> x = ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  al = bn_top (getbn x ls1) -> bl = bn_top (getbn y ls1) -> (0 < al)%nat -> (0 < bl)%nat ->
  implA (disp_normal rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) (al + bl) ls1) Σ1
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST rr x y R X Y ac (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) (Z_to_bv 64 (Z.of_nat bl)) x25
             (Z_to_bv 64 SHB) x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x229f5c) fc None m1 (seg_rom bgbsegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HX HY NEX NEY HPr EOx NROy NBx NBy EAL EBL HAL HBL.
  change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEX. apply hide_intro in NEY.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (WFS1 & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_wf_ok rr ls1 WFS1 HVR NROr) as (_ & TDR1 & _).
  pose proof (OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.opnd_ok x ls1 WFS1 HVX) as (LMX & TDX & DMX). pose proof (st_wf_ok y ls1 WFS1 HVY NROy) as (LMY & TDY & DMY & _).
  unfold BG_DMAX in DMY.
  set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
  unfold MallocRep.wz. apply implA_from_evt. do 2 (ub; zstep). ub; step.

  apply evt_done. unfold disp_normal. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr (al + bl) ls1 HVR TDR1)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB) (PL := PL) (EA := EA) (r := rr) (a := R) (words := (al + bl)%nat);
      [| | | reflexivity | exact HR | exact (hpl_wref PL rr HPr) | reflexivity | unfold MallocRep.wz; f_equal; lia | clear - EAL EBL TDX DMX TDY DMY; unfold bn_dmax in *; lia].
    - eapply cenv_preA; [exact ENV | exact LS | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | exact USED].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpn CTX). }
  cbv beta. intros [u2 ls2] Σ2 ms2 [PO LEAF].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP].
  cbn [fst snd] in PO, LEAF.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PLz2 & -> & CP & (EPLz2 & -> & HDM & _ & _)).
  subst PLz2. specialize (CP eq_refl).
  assert (E2 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (used + MC) Σ2 ls2 m2 OW2
               /\ lib_state ls2 m2 OW2 PL EA) by (eapply cenv_postA; [exact ENV | exact CP]).
  destruct E2 as (ENV2 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS.
  fix_ret.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS HR) as HR2. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HX) as HX2. pose proof (ref_at_stable _ _ _ _ _ _ _ RS HY) as HY2.
  destruct LEAF as (LOTH & _).
  assert (EGX : getbn x ls2 = getbn x ls1) by (apply LOTH; exact NEX).
  assert (EGY : getbn y ls2 = getbn y ls1) by (apply LOTH; exact NEY).
  clear CP ENV LS.

  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.

  pose proof ENV2 as (_ & HEAP2 & ST2 & MI2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  destruct (lib_state_open [] ls2 m2 OW2 PL EA rr R LS2 ND2 HR2 ltac:(intros []) NROr) as ((Dr & SR & ARR) & OKR & _).
  apply (fun ARRnb__ => bn_arr_nofr PL rr _ _ _ _ (proj1 (proj2 (lib_state_h_parts _ _ _ _ _ _ LS2))) NOFR NROr ARRnb__ (hpl_nbuf PL rr HPr)) in ARR.
  destruct (core_premsA1 Σ2 OW2 LB m2 ls2 PL EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP2 LS2 FROK NOFR ST2 MI2 HR2 HX2 HY2 NEY HPr EOx NROy NBy SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) HAL HBL HDM CEIL ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia)) as (Dy & PREA & MEMA).
  rewrite EGX, EGY in PREA, MEMA. fold la lb in PREA. fold la lb in MEMA.
  pose proof (mul_normal_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY)) as (LW & _ & NW).
  rewrite LLA, LLB in NW.
  replace ((al =? 0)%nat || (bl =? 0)%nat) with false in NW by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; lia).
  set (br := getbn rr ls2) in *.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof PREA as (_ & _ & _ & _ & (R0 & R24 & _) & _).
  ub; zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ R0 R24 LO SPR. lia. }
  clear KZ.
  replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
  eapply evt_mono.
  { eapply (MulOneCoreA.mulc_normalA sp gp (Z_to_bv 64 TP_A) m2 lo R X Y Dr DATA_ONE Dy MUL_CST br la lb PREA MEMA F2 fc2).
    - rewrite LLA, LLB. exact HDM.
    - rewrite MUL_CST_val. lia. }
  intros ms' PO.
  eapply (mul_finish1A1 ac ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST (used + MC) w0 Σ2 ls2 m2 OW2 rr x y R X Y Dr
            (8 * (Z.of_nat (length la) + Z.of_nat (length lb))) MUL_CST (mul_normal la lb) (length la + length lb)%nat) in PO;
    [ | exact ENV2 | exact USED | exact LS2 | rewrite MUL_CST_val; lia | rewrite MUL_CST_val; clear - LO; lia | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY | exact HPr | exact EOx | exact NROy | exact NBx | exact NBy
      | exact SR | | exact LW | | | ].
  - rewrite EGX, EGY in PO. fold br. rewrite LLA, LLB in PO. exact PO.
  - subst br. unfold BnRepDefs.bn_arr, bn_arr in *. exact ARR.
  - rewrite NW. fold br. clear - HDM HAL. lia.
  - rewrite LLA, LLB. fold br. exact HDM.
  - rewrite NW, LLA, LLB. lia.
Qed.

Lemma bn_mul_fixed_top_walkA_one : forall (ac : Z) (qc : bptr)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr x y : bnref) (R X Y : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_MUL_FIXED_STACKA BN_MUL_TOP_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr R -> ref_at ls OW PL x X -> ref_at ls OW PL y Y ->
  hpl PL rr -> x = ROne -> y <> ROne -> nbuf PL x -> nbuf PL y -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz R -> a1 = wz X -> a2 = wz Y -> a3 = wz ac ->
  implA (bn_mul_fixed_top (tree_ops bptr) rr x y ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_MUL_TOP_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Y. intros PRE UW CTX -> HR HX HY HPr EOx NROy NBx NBy EC -> -> -> ->.
  change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr.
  assert (NEX0 : rr <> x) by (rewrite EOx; exact NROr).
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  assert (LOF : lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA) by exact LO'.
  unfold BN_MUL_FIXED_TOP, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof MC_nonneg as MCP.
  destruct (one_opndA Σ OW LB m ls PL EA x X HEAP LS MI HX EOx) as (EONE & SX & ACX & ALX & OFX & X0 & XC & _).
  pose proof (OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_mul.opnd_ok x ls (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS HX)) as (_ & TDX & DMX).
  destruct (open_ro Σ OW LB m ls PL EA (bv_unsigned sp) y Y HEAP LS FROK NOFR HY NROy) as (Dy0 & SY & OKY & _ & Y0 & YC & _).
  pose proof OKY as (_ & TDY & DMY & _). unfold BG_DMAX in DMY.
  unfold bn_cells, MallocRep.wz in SX, SY.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HY NROy) as (ACY & ALY & OFY).
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).

  unfold bn_mul_fixed_top. rewrite bn_live_run.
  destruct (live_refs (st_ctx ls) [rr; x; y]) eqn:LIVE; [| apply implA_unr].
  apply live_refs_true_iff in LIVE.
  assert (LTR0 : (rr < NFIX + gx_used (st_ctx ls))%nat) by exact (Forall_inv LIVE).
  assert (LTX0 : (x < NFIX + gx_used (st_ctx ls))%nat) by exact (Forall_inv (Forall_inv_tail LIVE)).
  assert (LTY0 : (y < NFIX + gx_used (st_ctx ls))%nat) by exact (Forall_inv (Forall_inv_tail (Forall_inv_tail LIVE))).
  clear LIVE.
  unfold bbind at 1 2. unfold bget at 1 2. cbn [bind ret tree_ops tbind fst snd].
  set (al := bn_top (getbn x ls)) in *. set (bl := bn_top (getbn y ls)) in *.
  assert (AL1 : al = 1%nat) by (subst al; rewrite EONE; reflexivity).
  assert (AL23 : Z.of_nat al < 8388608) by (clear - TDX DMX; unfold bn_dmax in *; lia).
  assert (BL23 : Z.of_nat bl < 8388608) by (clear - TDY DMY; unfold bn_dmax in *; lia).
  assert (AX : 0 < X /\ X + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - X0 XC CEIL LO SPR SPT; lia).
  assert (AY : 0 < Y /\ Y + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Y0 YC CEIL LO SPR SPT; lia).
  apply hide_intro in OFX. apply hide_intro in OFY.
  apply implA_from_evt.
  carve_frame 112%nat ST. do 15 step.

  ub. do 2 zstep. ub. do 2 zstep. do 3 step.
  zstep. do 2 zstep. shl_with ACX ALX.
  chk0.
  ub. zstep. do 2 zstep. shl_with ACY ALY.
  step. rewrite (sx32_small (Z.of_nat al)) by (clear - AL23; lia).
  chk0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 112, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  apply rw_cells_CB8_hd in FR.
  lazymatch type of FR with rw_cells _ _ _ ?fr =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m pre 0 Σ ls m1 OW)
  end.
  { unfold cenvA. split.
    { unfold cenv_ok. split; [exact CEIL|]. split; [clear - LO; lia|]. split; [clear; lia|]. split; [unfold USTACK_TOP; clear - SPT; lia|]. split; [exact SP16|].
      split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FROK|]. split; [exact FAL| exact NOFR]. }
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ => split; [exact STx|]; split; [exact MIx|] end.
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(clear - LO; lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    lazymatch pre with C8 ?w :: _ =>
      change pre with (mul_frame w s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) in ENV; set (w0 := w) in * end end.
  pose proof ENV as (OK & HEAP1 & _).
  ub; zstep. if_cases KA0; zify_cond KA0.
  {
    replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; left; apply Nat.eqb_eq; clear - KA0; lia).
    apply evt_done. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    eapply mul_zero_pathA; [exact ENV | clear; unfold BN_MUL_TOP_COST, MC; lia | exact LS1 | exact LOF | exact HR | exact HPr]. }
  step. rewrite (sx32_small (Z.of_nat bl)) by (clear - BL23; lia).
  zstep. if_cases KB0; zify_cond KB0.
  {
    replace ((al =? 0)%nat || (bl =? 0)%nat) with true by (symmetry; apply orb_true_iff; right; apply Nat.eqb_eq; clear - KB0; lia).
    apply evt_done. unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    eapply mul_zero_pathA; [exact ENV | clear; unfold BN_MUL_TOP_COST, MC; lia | exact LS1 | exact LOF | exact HR | exact HPr]. }
  replace ((al =? 0)%nat || (bl =? 0)%nat) with false by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; [clear - KA0 | clear - KB0]; lia).

  zstep. rewrite (bn_swrap32_small (Z.of_nat al + Z.of_nat bl)) by (clear - AL23 BL23; lia).
  ub. zstep. step.

  clear SX SY MU WM HWL WOK FR SHB1 SHB2.
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_start_leaves ls)|].
    eapply (BN_CTX_start_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| | | reflexivity | exact EC | reflexivity].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear; unfold BN_MUL_TOP_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_start CTX). }
  cbv beta. intros [u1 ls1] Σ1 ms1 [PO LEAF1].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -112) BN_MUL_TOP_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F1 & fc1 & m2 & OW1 & PLz1 & -> & CP1 & (EPLz1 & _)).
  subst PLz1. specialize (CP1 eq_refl).
  assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m
                 (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) (0 + MC) Σ1 ls1 m2 OW1
               /\ lib_state ls1 m2 OW1 PL EA) by (eapply cenv_postA; [exact ENV | exact CP1]).
  destruct E1 as (ENV1 & LS1').
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
  fix_ret. unfold MallocRep.wz.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS1 HR) as HR1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS1 HX) as HX1. pose proof (ref_at_stable _ _ _ _ _ _ _ RS1 HY) as HY1.
  unfold start_leaf in LEAF1. cbn [fst snd] in LEAF1. destruct LEAF1 as (EGs & _ & EU1 & _).
  assert (EG1 : forall r0, getbn r0 ls1 = getbn r0 ls) by (intros r0; unfold getbn; rewrite EGs; reflexivity).
  assert (LTR : (rr < NFIX + gx_used (st_ctx ls1))%nat) by (rewrite EU1; exact LTR0).
  assert (LTX : (x < NFIX + gx_used (st_ctx ls1))%nat) by (rewrite EU1; exact LTX0).
  assert (LTY : (y < NFIX + gx_used (st_ctx ls1))%nat) by (rewrite EU1; exact LTY0).
  clear CP1 ENV LS1.

  cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind with (Q1 := mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST rr x y R X Y ac
                                     (bn_neg (getbn x ls)) (bn_neg (getbn y ls))).
  2:{ cbv beta. intros [uE lsE] ΣE msE J. cbn [fst snd].
      unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
      eapply (mul_endA1 ac qc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST rr x y R X Y
                (bn_neg (getbn x ls)) (bn_neg (getbn y ls)) (uE, lsE) ΣE msE LOF EC HPr EOx NROy NBx NBy J). }

  pose proof ENV1 as (_ & HEAP2 & _).
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS1') as PARTS1; pose proof PARTS1 as (WFS1 & PWF1 & IDS1 & _).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 NOFR HR1 NROr) as (qr & Ar & nr & Hinr & Rr1 & Rr2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinr) as (RA0 & _ & _ & RAC & _).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS1 NOFR HY1 NROy) as (qy & Ay & ny & Hiny & Ry1 & Ry2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hiny) as (YA0 & _ & _ & YAC & _).
  apply implA_from_evt.
  ub; zstep. if_cases KRX; zify_cond KRX.
  { exfalso.
    pose proof (struct_disj Σ1 OW1 LB m2 HEAP2 ls1 PL EA (bv_unsigned sp) USTACK_TOP PARTS1 FROK rr x R X NEX0 HR1 HX1) as SD.
    rewrite ?unsigned_lit in KRX by (unfold BnHeapA.ACEIL in *; lia). clear - KRX SD. lia. }
  assert (NEX : rr <> x) by exact NEX0.
  ub; zstep.
  ub; zstep. if_cases KRY; zify_cond KRY.
  2:{ assert (E : rr = y).
      { destruct (Nat.eq_dec rr y) as [E|NE]; [exact E|exfalso].
        pose proof (struct_disj Σ1 OW1 LB m2 HEAP2 ls1 PL EA (bv_unsigned sp) USTACK_TOP PARTS1 FROK rr y R Y NE HR1 HY1) as SD.
        rewrite ?unsigned_lit in KRY by (unfold BnHeapA.ACEIL in *; lia). clear - KRY SD. lia. }
      subst y. replace (rr =? rr)%nat with true by (symmetry; apply Nat.eqb_refl).
      apply evt_done. rewrite orb_true_r. cbn [bunr unreachable tree_ops]. apply implA_unr. }
  assert (NEY : rr <> y) by (intros E; subst y; apply KRY; rewrite (ref_at_fun _ _ _ _ _ _ ND2 HR1 HY1); reflexivity).
  rewrite (proj2 (Nat.eqb_neq rr x) NEX), (proj2 (Nat.eqb_neq rr y) NEY). cbn [orb].
  clear KRX KRY.
  assert (EAL1 : al = bn_top (getbn x ls1)) by (rewrite EG1; reflexivity).
  assert (EBL1 : bl = bn_top (getbn y ls1)) by (rewrite EG1; reflexivity).
  rewrite <- (EG1 x), <- (EG1 y).

  zstep. rewrite (bn_swrap32_small (Z.of_nat al - Z.of_nat bl)) by (clear - AL23 BL23; lia).
  ub. zstep.
  eassert (CONT : ((al =? bl)%nat && (al =? 8)%nat = false) -> _).
  2:{ zstep. if_cases K8A; zify_cond K8A.
      { apply CONT. apply andb_false_iff. right. apply Nat.eqb_neq. clear - K8A. lia. }
      exfalso. clear - K8A AL1. lia. }
  intros ENC. rewrite ENC.
  zstep.
  assert (HAL : (0 < al)%nat) by (clear - KA0; lia). assert (HBL : (0 < bl)%nat) by (clear - KB0; lia).
  zstep. rewrite lts_small by (clear - AL23; lia). if_cases K16A; zify_cond K16A.
  { replace (16 <=? al)%nat with false by (symmetry; apply Nat.leb_gt; clear - K16A; lia). cbn [andb].
    apply evt_done. eapply mul_path_normalA1; try eassumption; clear; unfold BN_MUL_TOP_COST, MC; lia. }
  exfalso. clear - K16A AL1. lia.
Qed.

Lemma bn_mul_fixed_top_walkA1 : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_MUL_FIXED_STACKA BN_MUL_TOP_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> ry <> ROne -> nbuf PL rx -> nbuf PL ry -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
  implA (bn_mul_fixed_top (tree_ops bptr) rr rx ry ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_MUL_TOP_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MUL_FIXED_TOP) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qc. intros PRE UW CTX ETP HR HX HY HPr NROy NBx NBy EC E0 E1 E2 E3.
  destruct (Nat.eq_dec rx ROne) as [EOx | NROx].
  - exact (bn_mul_fixed_top_walkA_one ac qc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ ls OW LB PL EA
             lo ras rr rx ry ar ax ay PRE UW CTX ETP HR HX HY HPr EOx NROy NBx NBy EC E0 E1 E2 E3).
  - exact (bn_mul_fixed_top_walkA ac qc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ ls OW LB PL EA
             lo ras rr rx ry ar ax ay PRE UW CTX ETP HR HX HY HPr NROx NROy NBx NBy EC E0 E1 E2 E3).
Qed.

End WithRT.
