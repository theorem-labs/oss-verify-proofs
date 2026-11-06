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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_topA AsStruct2 AW_num_bits_word BnKaraMemA BnCallsKA AW_mul_recursive AW_mul_part_recursive AW_kara_closedA AW_mul_core.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctx_getA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import BgLeaves BgLive DivModel.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_mul.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_callsAF W_expandAF W_lshiftAF W_copyAF W_ctxAF W_ctx_endAF W_ctx_getAF W_div_tailAF W_div_padAF W_divAF W_bndivAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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

Definition BN_MUL_FIXED_TOP : Z := 0x22a928.
Definition BN_MUL : Z := 0x22a8e0.

Definition MUL_CST : Z := part_stackA CS8A 23.
Definition BN_MUL_FIXED_STACKA : Z := 112 + MUL_CST.
Definition BN_MUL_TOP_STACK : Z := 32 + BN_MUL_FIXED_STACKA.

Definition BN_MUL_TOP_COST : Z := 4 * MC.

Lemma MUL_CST_val : MUL_CST = 73216.
Proof. reflexivity. Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_ml_start := (E_bn_mul_fixed_top_22a7d8 : uk_call BN_MUL_FIXED_TOP 0x22a9c0 BN_CTX_START).
Local Notation E_ml_get1 := (E_bn_mul_fixed_top_22a7ec : uk_call BN_MUL_FIXED_TOP 0x22a9d4 BN_CTX_GET).
Local Notation E_ml_wexpc := (E_bn_mul_fixed_top_22a80c : uk_call BN_MUL_FIXED_TOP 0x22a9f4 BN_WEXPAND).
Local Notation E_ml_get2 := (E_bn_mul_fixed_top_22a8bc : uk_call BN_MUL_FIXED_TOP 0x22aaa4 BN_CTX_GET).
Local Notation E_ml_wexpr1 := (E_bn_mul_fixed_top_22a8f0 : uk_call BN_MUL_FIXED_TOP 0x22aad8 BN_WEXPAND).
Local Notation E_ml_wexpr2 := (E_bn_mul_fixed_top_22a900 : uk_call BN_MUL_FIXED_TOP 0x22aae8 BN_WEXPAND).
Local Notation E_ml_wexpn := (E_bn_mul_fixed_top_22a978 : uk_call BN_MUL_FIXED_TOP 0x22ab60 BN_WEXPAND).
Local Notation E_ml_wexpp1 := (E_bn_mul_fixed_top_22a9f4 : uk_call BN_MUL_FIXED_TOP 0x22abdc BN_WEXPAND).
Local Notation E_ml_wexpp2 := (E_bn_mul_fixed_top_22aa04 : uk_call BN_MUL_FIXED_TOP 0x22abec BN_WEXPAND).
Local Notation E_mul_ft := (E_BN_mul_22a718 : uk_call BN_MUL 0x22a900 BN_MUL_FIXED_TOP).

Definition mul_frame (w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 : word) : list cell :=
  [C8 w0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].

Definition mul_joinA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL : Z)
    (rr x y : bnref) (R X Y ac : Z) (na nb : bool)
    (v : unit * bstate bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x25 x26 x27 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' w0 used,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 R) (Z_to_bv 64 Y) (Z_to_bv 64 X) (Z_to_bv 64 R) x22 x23 (Z_to_bv 64 SHB) x25 x26 x27 t3 t4 t5 t6)
             F' (Z_to_bv 64 MULC_TAIL) fc' None m' (seg_rom bgasegs)
    /\ cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ' (snd v) m' OW'
    /\ used <= TOTAL
    /\ lib_state (snd v) m' OW' PL EA
    /\ ref_at (snd v) OW' PL rr R /\ ref_at (snd v) OW' PL x X /\ ref_at (snd v) OW' PL y Y
    /\ bn_neg (getbn x (snd v)) = na /\ bn_neg (getbn y (snd v)) = nb.

Lemma mul_endA : forall (ac : Z) (qc : bptr)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL : Z)
    (rr x y : bnref) (R X Y : Z) (na nb : bool) (v : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state),
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  pl_ctx PL = Some (ac, qc) -> hpl PL rr -> x <> ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras TOTAL rr x y R X Y ac na nb v Σ' ms' ->
  implA (BN_CTX_end ops (setbn rr (bn_with_neg (getbn rr (snd v)) (xorb na nb)) (snd v))) Σ'
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA TOTAL (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1)) ms'.
Proof.
  intros until ms'. intros LO EC HPr NROx NROy NBx NBy (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x22 & x23 & x25 & x26 & x27 & t3 & t4 & t5 & t6 & FE & fcE
                             & mE & OWE & w0 & used & -> & ENV & USED & LS & HR & HX & HY & ENA & ENB).
  change (not_one x) in NROx. change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr.
  destruct v as [[] lsE]. cbn [fst snd] in *.
  unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW). unfold mul_frame in FR. cbn [app] in FR.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (open_ro Σ' OWE LB mE lsE PL EA (bv_unsigned sp) x X HEAP LS FROK NOFR HX NROx) as (Dx & SX & _ & _ & X0 & XC & _).
  destruct (open_ro Σ' OWE LB mE lsE PL EA (bv_unsigned sp) y Y HEAP LS FROK NOFR HY NROy) as (Dy & SY & _ & _ & Y0 & YC & _).
  unfold bn_cells, MallocRep.wz in SX, SY. rewrite ENA in SX. rewrite ENB in SY.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALX & OFX).
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
  pose proof (munch_refl [(R, R + 24)]%Z mE) as MU. pose proof (wmono_refl bgasegs mE) as WM.
  assert (OFF : offshW [(R, R + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFR; lia).
  apply hide_intro in OFX. apply hide_intro in OFY. apply hide_intro in OFR. apply hide_intro in SAI. apply hide_intro in DI.
  apply implA_from_evt.
  zstep.
  do 2 zstep. shl_with ACX ALX. chk0.
  do 3 zstep. shl_with ACY ALY.
  step. rewrite (sx32_small (Z.b2z na)) by (clear - NA; lia).
  chk0.
  do 3 zstep. shl_with ACR ALR.
  step. rewrite (sx32_small (Z.b2z nb)) by (clear - NB; lia).
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
  zstep. if_cases KE; zify_cond KE; [|exfalso; apply KE; reflexivity]. clear KE.
  zstep. step.
  zstep. step.

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
  zstep. do 13 step.
  release_frame FRe STe (bv_unsigned sp). step. step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists mF, OWF, PL. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. split; reflexivity.
Qed.

Lemma mul_finish1A : forall (ac : Z)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (TOTAL used : Z) (w0 : word)
    (Σ2 : rts RT) (ls2 : bstate bptr) (m2 : mem) (OW2 : list block) (rr x y : bnref) (R X Y Dr n8 CST : Z)
    (w : list Z) (topn : nat) (x22 x23 x25 x26 x27 : word) (ms' : machine_state),
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) TOTAL Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ2 ls2 m2 OW2 ->
  used <= TOTAL -> lib_state ls2 m2 OW2 PL EA ->
  0 <= CST -> lo <= bv_unsigned sp - 112 - CST ->
  ref_at ls2 OW2 PL rr R -> ref_at ls2 OW2 PL x X -> ref_at ls2 OW2 PL y Y -> rr <> x -> rr <> y -> hpl PL rr -> x <> ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  rw_cells bgasegs m2 R (bn_cells Dr (getbn rr ls2)) -> BnRepDefs.bn_arr m2 OW2 Dr (getbn rr ls2) ->
  limbs w -> (0 < length w <= bn_dmax (getbn rr ls2))%nat -> (topn <= bn_dmax (getbn rr ls2))%nat -> n8 = 8 * Z.of_nat (length w) ->
  mulc_postA sp gp (wz TP_A) m2 lo R Dr (getbn rr ls2) F fc sp (Z_to_bv 64 ac) (Z_to_bv 64 R) (Z_to_bv 64 Y) (Z_to_bv 64 X) (Z_to_bv 64 R)
             x22 x23 x25 x26 x27 [(Dr, Dr + n8); (R, R + 24); (bv_unsigned sp - 112 - CST, bv_unsigned sp + -112)] topn w (fun _ => True) ms' ->
  mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras TOTAL rr x y R X Y ac
            (bn_neg (getbn x ls2)) (bn_neg (getbn y ls2)) (tt, setbn rr (mul_res (getbn rr ls2) w topn) ls2) Σ2 ms'.
Proof.
  intros until ms'. intros ENV USED LS HCST LO HR HX HY NEX NEY HPr NROx NROy NBx NBy SR ARR LW [HW0 HWD] HTD ->
    (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & -> & MU & WM & MI3 & SR3 & HR3 & ST3 & _).
  change (not_one x) in NROx. change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEX. apply hide_intro in NEY.
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

Lemma arr_pos : forall Σ OW LB m D (b : bignum bptr), AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> (0 < bn_dmax b)%nat ->
  0 < D /\ (D + 8 * Z.of_nat (bn_dmax b) <= 65536 \/ 12345344 <= D).
Proof.
  intros Σ OW LB m D b HEAP ARR HD. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d b) as [p|] eqn:E.
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & _ & AI). lia.
  - destruct ARR as [_ Eb]. exfalso. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. lia.
Qed.

Lemma core_premsA : forall Σ OW LB m ls PL EA rr x y R X Y Dr al bl lo SPv,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> frames_ok LB PL SPv USTACK_TOP -> frames_lb PL LB -> stk bgasegs m lo (SPv + -112) -> mem_inv bgasegs m ->
  ref_at ls OW PL rr R -> ref_at ls OW PL x X -> ref_at ls OW PL y Y -> rr <> x -> rr <> y -> hpl PL rr -> x <> ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  rw_cells bgasegs m R (bn_cells Dr (getbn rr ls)) -> BnRepDefs.bn_arr m OW Dr (getbn rr ls) ->
  (al <= bn_top (getbn x ls))%nat -> (bl <= bn_top (getbn y ls))%nat -> (0 < al)%nat -> (0 < bl)%nat -> (al + bl <= bn_dmax (getbn rr ls))%nat ->
  ACEIL <= lo -> lo <= SPv - 112 - MUL_CST -> SPv + 16 <= USTACK_TOP ->
  exists Dx Dy,
    mulc_preA (Z_to_bv 64 SPv) lo R X Y Dr Dx Dy MUL_CST (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls)))
    /\ mulc_memA (Z_to_bv 64 SPv) m lo R X Y Dr Dx Dy (getbn rr ls) (firstn al (bn_buf (getbn x ls))) (firstn bl (bn_buf (getbn y ls))).
Proof.
  intros Σ OW LB m ls PL EA rr x y R X Y Dr al bl lo SPv HEAP LS FROK NOFR ST MI HR HX HY NEX NEY HPr NROx NROy NBx NBy SR ARR HAL HBL AL0 BL0 HD CEIL LO SPT.
  change (not_one x) in NROx. change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEX. apply hide_intro in NEY.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  rewrite MUL_CST_val in LO.
  assert (ESP : bv_unsigned (Z_to_bv 64 SPv) = SPv) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_wf_ok rr ls WFS HVR NROr) as (OKR1 & OKR2 & OKR3 & OKR4).
  pose proof (st_wf_ok x ls WFS HVX NROx) as (LMX & TDX & DMX & _). pose proof (st_wf_ok y ls WFS HVY NROy) as (LMY & TDY & DMY & _).
  unfold BG_DMAX in DMX, DMY, OKR3.
  destruct (bn_arr_facts_w ls OW PL EA SPv USTACK_TOP Σ LB m rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HPr) ltac:(first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))])) as (UR & _ & DR0 & DRC & _ & DSEPR).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NROr) as (qs & As & ns & Hins & Ra1 & Ra2).
  pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & _).
  destruct (operand_view_ne Σ OW LB m ls PL EA SPv rr R Dr x X al HEAP LS FROK NOFR HR NROr SR ARR HX NROx HAL ltac:(congruence) NBx)
    as (Dx & HXd & HLX & UX & ARRX & X0' & XC' & DX0 & DXC & SXR & SXA & _ & ALX).
  destruct (operand_view_ne Σ OW LB m ls PL EA SPv rr R Dr y Y bl HEAP LS FROK NOFR HR NROr SR ARR HY NROy HBL ltac:(congruence) NBy)
    as (Dy & HYd & HLY & UY & ARRY & Y0' & YC' & DY0 & DYC & SYR & SYA & _ & ALY).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALXs & _).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HY NROy) as (ACY & ALYs & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
  destruct (arr_shA _ _ _ _ _ _ HEAP ltac:(first [exact ARRX | exact (bn_arr_nofr PL x _ _ _ _ PWF NOFR NROx ARRX ltac:(solve_nbuf))])) as (ACDX & ALDX & _).
  destruct (arr_shA _ _ _ _ _ _ HEAP ltac:(first [exact ARRY | exact (bn_arr_nofr PL y _ _ _ _ PWF NOFR NROy ARRY ltac:(solve_nbuf))])) as (ACDY & ALDY & _).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARR ltac:(lia)) as (PDR & IDR).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARRX ltac:(lia)) as (PDX & _).
  destruct (arr_pos _ _ _ _ _ _ HEAP ARRY ltac:(lia)) as (PDY & _).
  assert (LLA : length (firstn al (bn_buf (getbn x ls))) = al) by (apply firstn_length_le; exact (Nat.le_trans _ _ _ HAL TDX)).
  assert (LLB : length (firstn bl (bn_buf (getbn y ls))) = bl) by (apply firstn_length_le; exact (Nat.le_trans _ _ _ HBL TDY)).
  exists Dx, Dy. split.
  - unfold mulc_preA. rewrite LLA, LLB, ESP.
    split; [apply limbs_firstn; exact LMX|]. split; [apply limbs_firstn; exact LMY|]. split; [exact (bg_okm _ (st_wf_ok rr ls WFS HVR NROr))|].
    split; [clear - HAL HBL TDX DMX TDY DMY; unfold bn_dmax in *; lia|].
    split; [rewrite MUL_CST_val; unfold BnHeapA.ACEIL in *; clear - SA0 SAC Ra1 Ra2 X0' XC' Y0' YC' DR0 DRC DX0 DXC DY0 DYC CEIL LO SPT TDX TDY HAL HBL; unfold bn_dmax in *; lia|].
    split; [exact (DSEPR rr R HR)|]. split; [clear - SXA TDX HAL; unfold bn_dmax in *; lia|]. split; [clear - SYA TDY HBL; unfold bn_dmax in *; lia|].
    split; [clear - ALX TDX HAL; unfold bn_dmax in *; lia|]. split; [clear - ALY TDY HBL; unfold bn_dmax in *; lia|].
    split; [clear - SXR SYR; lia|].
    split; [exact (conj ALR (conj ALXs (conj ALYs (conj ALDR (conj ALDX ALDY)))))|].
    unfold SHHI. split; [exact OFR|]. split; [exact OFDR|]. split; [unfold BnHeapA.ACEIL in *; clear - C2 CEIL; lia|].
    split; [exact IDR|]. split; [exact PDR|]. split; [exact PDX|]. split; [exact PDY|]. exact SAC0 || (pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (_ & _ & _ & _ & SAI); clear - SAI Ra1 Ra2; lia).
  - unfold mulc_memA. rewrite LLA, LLB, ESP.
    split; [exact SR|]. split; [exact UR|]. split; [exact HXd|]. split; [exact HYd|]. split; [exact HLX|]. split; [exact HLY|].
    split; [exact ST|]. split; [exact MI|]. split; [exact (AH_shb _ _ _ _ HEAP)|].
    split; [exact ACR|]. split; [eapply acc_sub; [exact ACX | lia | lia]|]. split; [eapply acc_sub; [exact ACY | lia | lia]|].
    split; [exact ACDR|]. split; [eapply acc_sub; [exact ACDX | lia | clear - TDX HAL; unfold bn_dmax in *; lia]|].
    eapply acc_sub; [exact ACDY | lia | clear - TDY HBL; unfold bn_dmax in *; lia].
Qed.

Lemma mul_path_normalA : forall (ac : Z)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (used : Z) (w0 : word)
    (Σ1 : rts RT) (ls1 : bstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z) (al bl : nat)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word),
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 m1 OW1 ->
  used + MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls1 m1 OW1 PL EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls1 OW1 PL rr R -> ref_at ls1 OW1 PL x X -> ref_at ls1 OW1 PL y Y -> rr <> x -> rr <> y -> hpl PL rr -> x <> ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  al = bn_top (getbn x ls1) -> bl = bn_top (getbn y ls1) -> (0 < al)%nat -> (0 < bl)%nat ->
  implA (disp_normal rr (firstn al (bn_buf (getbn x ls1))) (firstn bl (bn_buf (getbn y ls1))) (al + bl) ls1) Σ1
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST rr x y R X Y ac (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 Y) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 (Z.of_nat bl)) (Z_to_bv 64 SHB) x25 x26
             (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x22ab54) fc None m1 (seg_rom bgasegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HX HY NEX NEY HPr NROx NROy NBx NBy EAL EBL HAL HBL.
  change (not_one x) in NROx. change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEX. apply hide_intro in NEY.
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (WFS1 & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_wf_ok rr ls1 WFS1 HVR NROr) as (_ & TDR1 & _).
  pose proof (st_wf_ok x ls1 WFS1 HVX NROx) as (LMX & TDX & DMX & _). pose proof (st_wf_ok y ls1 WFS1 HVY NROy) as (LMY & TDY & DMY & _).
  unfold BG_DMAX in DMX, DMY.
  set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
  unfold MallocRep.wz. apply implA_from_evt. do 2 zstep. step.

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
  destruct (core_premsA Σ2 OW2 LB m2 ls2 PL EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP2 LS2 FROK NOFR ST2 MI2 HR2 HX2 HY2 NEX NEY HPr NROx NROy NBx NBy SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) HAL HBL HDM CEIL ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia)) as (Dx & Dy & PREA & MEMA).
  rewrite EGX, EGY in PREA, MEMA. fold la lb in PREA. fold la lb in MEMA.
  pose proof (mul_normal_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY)) as (LW & _ & NW).
  rewrite LLA, LLB in NW.
  replace ((al =? 0)%nat || (bl =? 0)%nat) with false in NW by (symmetry; apply orb_false_iff; split; apply Nat.eqb_neq; lia).
  set (br := getbn rr ls2) in *.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof PREA as (_ & _ & _ & _ & (R0 & R24 & _) & _).
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ R0 R24 LO SPR. lia. }
  clear KZ.
  replace (Z_to_bv 64 (Z.of_nat al)) with (Z_to_bv 64 (Z.of_nat (length la))) by (rewrite LLA; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length lb))) by (rewrite LLB; reflexivity).
  replace (Z_to_bv 64 (Z.of_nat al + Z.of_nat bl)) with (Z_to_bv 64 (Z.of_nat (length la) + Z.of_nat (length lb))) by (rewrite LLA, LLB; reflexivity).
  eapply evt_mono.
  { eapply (mulc_normalA sp gp (Z_to_bv 64 TP_A) m2 lo R X Y Dr Dx Dy MUL_CST br la lb PREA MEMA F2 fc2).
    - rewrite LLA, LLB. exact HDM.
    - rewrite MUL_CST_val. lia. }
  intros ms' PO.
  eapply (mul_finish1A ac ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST (used + MC) w0 Σ2 ls2 m2 OW2 rr x y R X Y Dr
            (8 * (Z.of_nat (length la) + Z.of_nat (length lb))) MUL_CST (mul_normal la lb) (length la + length lb)%nat) in PO;
    [ | exact ENV2 | exact USED | exact LS2 | rewrite MUL_CST_val; lia | rewrite MUL_CST_val; clear - LO; lia | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY | exact HPr | exact NROx | exact NROy | exact NBx | exact NBy
      | exact SR | | exact LW | | | ].
  - rewrite EGX, EGY in PO. fold br. rewrite LLA, LLB in PO. exact PO.
  - subst br. unfold BnRepDefs.bn_arr, bn_arr in *. exact ARR.
  - rewrite NW. fold br. clear - HDM HAL. lia.
  - rewrite LLA, LLB. fold br. exact HDM.
  - rewrite NW, LLA, LLB. lia.
Qed.

Lemma mul_path_comba8A : forall (ac : Z)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z) (used : Z) (w0 : word)
    (Σ1 : rts RT) (ls1 : bstate bptr) (m1 : mem) (OW1 : list block) (rr x y : bnref) (R X Y : Z)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 x27 t3 t4 t5 t6 : word),
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -112) s0 ra (Some ras) BN_MUL_TOP_COST Σ ls OW m (mul_frame w0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1) used Σ1 ls1 m1 OW1 ->
  used + MC <= BN_MUL_TOP_COST -> uk_ctx BN_MUL_FIXED_TOP (bv_unsigned ra :: ras) ->
  lib_state ls1 m1 OW1 PL EA ->
  lo <= bv_unsigned sp - BN_MUL_FIXED_STACKA ->
  ref_at ls1 OW1 PL rr R -> ref_at ls1 OW1 PL x X -> ref_at ls1 OW1 PL y Y -> rr <> x -> rr <> y -> hpl PL rr -> x <> ROne -> y <> ROne -> nbuf PL x -> nbuf PL y ->
  bn_top (getbn x ls1) = 8%nat -> bn_top (getbn y ls1) = 8%nat ->
  implA (disp_comba8 rr (firstn 8 (bn_buf (getbn x ls1))) (firstn 8 (bn_buf (getbn y ls1))) ls1) Σ1
    (mul_joinA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST rr x y R X Y ac (bn_neg (getbn x ls1)) (bn_neg (getbn y ls1)))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 R) (Z_to_bv 64 Y) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 8) (Z_to_bv 64 8) (Z_to_bv 64 SHB) x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x22a9e8) fc None m1 (seg_rom bgasegs)).
Proof.
  intros until t6. intros ENV USED CTX LS LO HR HX HY NEX NEY HPr NROx NROy NBx NBy EAL0 EBL0.
  change (not_one x) in NROx. change (not_one y) in NROy. pose proof (proj1 HPr : not_one rr) as NROr. apply hide_intro in NEX. apply hide_intro in NEY.
  set (al := 8%nat). set (bl := 8%nat).
  assert (EAL : al = bn_top (getbn x ls1)) by (symmetry; exact EAL0). assert (EBL : bl = bn_top (getbn y ls1)) by (symmetry; exact EBL0).
  pose proof LO as LO'. unfold BN_MUL_FIXED_STACKA in LO. rewrite MUL_CST_val in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ENV as (OK & HEAP & _). pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (WFS1 & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HY) as HVY.
  pose proof (st_wf_ok rr ls1 WFS1 HVR NROr) as (_ & TDR1 & _).
  pose proof (st_wf_ok x ls1 WFS1 HVX NROx) as (LMX & TDX & DMX & _). pose proof (st_wf_ok y ls1 WFS1 HVY NROy) as (LMY & TDY & DMY & _).
  unfold BG_DMAX in DMX, DMY.
  set (la := firstn al (bn_buf (getbn x ls1))). set (lb := firstn bl (bn_buf (getbn y ls1))).
  assert (LLA : length la = al) by (subst la; apply firstn_length_le; rewrite EAL; exact TDX).
  assert (LLB : length lb = bl) by (subst lb; apply firstn_length_le; rewrite EBL; exact TDY).
  unfold MallocRep.wz. apply implA_from_evt. do 2 zstep. step.

  apply evt_done. unfold disp_comba8. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_wexpand_leaves rr 16 ls1 HVR TDR1)|].
    eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB) (PL := PL) (EA := EA) (r := rr) (a := R) (words := 16%nat);
      [| | | reflexivity | exact HR | exact (hpl_wref PL rr HPr) | reflexivity | reflexivity | lia].
    - eapply cenv_preA; [exact ENV | exact LS | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | exact USED].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_ml_wexpc CTX). }
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
  destruct (core_premsA Σ2 OW2 LB m2 ls2 PL EA rr x y R X Y Dr al bl lo (bv_unsigned sp) HEAP2 LS2 FROK NOFR ST2 MI2 HR2 HX2 HY2 NEX NEY HPr NROx NROy NBx NBy SR ARR
              ltac:(rewrite EGX; lia) ltac:(rewrite EGY; lia) ltac:(lia) ltac:(lia) ltac:(subst al bl; lia) CEIL ltac:(unfold BN_MUL_FIXED_STACKA in LO'; clear - LO'; lia) ltac:(unfold USTACK_TOP; clear - SPT; lia))
    as (Dx & Dy & PREA & MEMA).
  rewrite EGX, EGY in PREA, MEMA. fold la lb in PREA. fold la lb in MEMA.
  pose proof (mul_comba8_spec la lb ltac:(subst la; apply limbs_firstn; exact LMX) ltac:(subst lb; apply limbs_firstn; exact LMY) LLA LLB) as (LW & NW & _).
  set (br := getbn rr ls2) in *.
  rewrite Z_to_bv_bv_unsigned in PREA, MEMA.
  pose proof PREA as (_ & _ & _ & _ & (R0 & R24 & _) & _).
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ R0 R24 LO SPR. lia. }
  clear KZ.
  pose proof (mulc_comba8A sp gp (Z_to_bv 64 TP_A) m2 lo R X Y Dr Dx Dy MUL_CST br la lb PREA MEMA CS8A F2 fc2) as CORE.
  rewrite LLA, LLB in CORE. change (Z.of_nat al) with 8 in CORE. change (Z.of_nat bl) with 8 in CORE.
  eapply evt_mono.
  { eapply CORE; [exact comba8_okA | rewrite MUL_CST_val; unfold CS8A; lia | reflexivity | reflexivity | exact HDM]. }
  clear CORE. intros ms' PO.
  eapply (mul_finish1A ac ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m Σ ls OW LB PL EA lo ras BN_MUL_TOP_COST (used + MC) w0 Σ2 ls2 m2 OW2 rr x y R X Y Dr
            (8 * 16) MUL_CST (mul_comba8 la lb) 16%nat) in PO;
    [ | exact ENV2 | exact USED | exact LS2 | rewrite MUL_CST_val; lia | rewrite MUL_CST_val; clear - LO; lia | exact HR2 | exact HX2 | exact HY2 | exact NEX | exact NEY | exact HPr | exact NROx | exact NROy | exact NBx | exact NBy
      | exact SR | | exact LW | | | ].
  - rewrite EGX, EGY in PO. fold br. exact PO.
  - subst br. unfold BnRepDefs.bn_arr, bn_arr in *. exact ARR.
  - rewrite NW. fold br. clear - HDM. lia.
  - fold br. exact HDM.
  - rewrite NW. reflexivity.
Qed.

End WithRT.
