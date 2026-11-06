(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: role_ffl is proofs/libreac/fuzz_knock/lib/A/APgLib.v link_FFL at origin/ossv/recipes
   6ebe35ba632 (in the form proofs/libreac/fuzz_decode/lib/A/DecodeARtStackMalloc.v dec_ffl states it, without the
   unfold of YImgTop's notations), at reac-pw/fuzz_role's image A and its start-up record TfibB; the rest of the file
   is written new. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses from the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): lib/A/RPgLib.v's statement of the walk of
   LLVMFuzzerTestOneInput (0x7ff88), proved.

     role_lib_x_all : role_lib_x_all_stmt

   It is lib/A/RPgTopI.v role_lib_x_A at the relocated frame's start-up record AD2l.TfibB, its sink AE2k.tfib_K,
   XL0 and ACfn's harness constants (A_LLVMF 0x7ff88, RA_LLVMF 0x7fe84, A_EMPTY 0x5d5a60, EV_LIB 2000, LIVE_LIB 2^33,
   LLVMF_STK 32768), with every premise discharged:
   - the walk's pieces by their lanes' theorems (RPgE01.e01_ok, RPgW3a .. RPgW8, RPgPostTop / PostCorr / PostReq /
     PostMal, RPgScanHead / Setup / Outer / Inner, RPgM02Key / M02Tail, RPgX01.rx_S_X01), the two middle contracts by
     RPgMainL.role_build_holds / role_check_holds inside role_lib_x_A;
   - the runtime contracts the pieces call, at TfibB: __asan_memcpy 0x510d4 and __asan_memset 0x51570 (AE2q / AE2r),
     the strlen wrapper 0x41ac8 (Rt/Strlen.v), the strcmp wrapper 0x41ad0 at every float state (Rt/Strcmp.v), the
     class-3 frame (Rt/StackMalloc3.v), __asan_set_shadow_f5 0x5409c (Rt/SetShadow.v), the parse 0x82ef0
     (RPgParse.rl_parse_A); malloc and free are role_lib_x_all_stmt's own premises;
   - the symbol record's facts: TfibSyms TfibB (AD2l.TfibB_syms), the static law (RPgStatA.rh_static_A), the
     allocator's model laws from the trace universe (YG05.model_laws_ok), the API environment, the frame flag law,
     the sink's laws (AD1u.tfib_AIL), the record's cells and code entries, and the call traces of the four
     allocator sites (each in lib/A/ACej.v's Tfib_universe), by computation;
   - the harness constants' numeric premises, by computation.
   One premise is open, a Section hypothesis of this file: the piece of ent_build's cases 6 .. 8,
   RPgSeg.rs_piece_W6c_stmt at TfibB, at every run ceiling and float state. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG05 SetShadowDef AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import AF0l AF0m AD2l ACej.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require AB1v AE2k ACfn AD1u AE2q AE2r ACeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A.Rt Require Strcmp Strlen StackMalloc3 SetShadow StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgHarn RPgLib.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgTopI RPgStatA RPgParse.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgE01D RPgE01 RPgW3a RPgW3b RPgW3bPre RPgProp
RPgW5IntP RPgW5OpenP RPgW5CloseP RPgW6a RPgW6b RPgEnt0 RPgW7b RPgW8 RPgPostTop RPgPostCorr RPgPostReq RPgPostMal
RPgScanHead RPgScanSetup RPgScanOuter RPgScanInner RPgM02Key RPgM02Tail RPgX01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac zlt := apply Z.ltb_lt; vm_compute; reflexivity.

(* ===================================== the harness constants ===================================== *)
Lemma role_c_hofl : 0x9b528 <= @YI16.sk_ofl_head AE2k.tfib_sink_head.
Proof. zle. Qed.
Lemma role_c_entry : ACfn.A_LLVMF = RH_ENTRY.
Proof. reflexivity. Qed.
Lemma role_c_ev : RH_EV <= ACfn.EV_LIB.
Proof. zle. Qed.
Lemma role_c_stk : RH_RSZ + 32 + ASTACK <= ACfn.LLVMF_STK.
Proof. zle. Qed.
(* S_E01's: the frame's request and its callee's stack, one event, the first block *)
Lemma role_c_e01_stk : 432 + ASTACK <= ACfn.LLVMF_STK.
Proof. zle. Qed.
Lemma role_c_e01_ev : 1 <= ACfn.EV_LIB.
Proof. zle. Qed.
Lemma role_c_e01_live : Layout.PP_SIZE <= ACfn.LIVE_LIB.
Proof. zle. Qed.
Lemma role_c_empty : 0 < ACfn.A_EMPTY < kLowMemEnd.
Proof. split; zlt. Qed.
(* the malloc(pod) step's *)
Lemma role_c_c23_stk : ASTACK + RH_RSZ + 16 <= ACfn.LLVMF_STK.
Proof. zle. Qed.
Lemma role_c_c23_ev : 2 <= ACfn.EV_LIB.
Proof. zle. Qed.
Lemma role_c_c23_live : Layout.PP_SIZE + 5440 <= ACfn.LIVE_LIB.
Proof. zle. Qed.
(* S_X01's *)
Lemma role_c_x01_stk : ASTACK + 0x1b0 <= ACfn.LLVMF_STK.
Proof. zle. Qed.
Lemma role_c_x01_ev : 4 <= ACfn.EV_LIB.
Proof. zle. Qed.

(* ===================================== the call traces of the four allocator sites ===================================== *)
(* malloc(pp), return 0x80194 (RPgE01D.e01_trace_stmt) *)
Lemma role_e01_trace : RPgE01D.e01_trace_stmt TfibB ACfn.RA_LLVMF.
Proof.
unfold RPgE01D.e01_trace_stmt. intros regsT ch Hra Hch. unfold call_trace0, unwind_of_chain. rewrite Hra.
destruct Hch as [-> | (fp & v & ->)]; apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* malloc(pod), return 0x820c4 (RPgPostMal.rl_A_S_C23's trace premise) *)
Lemma role_c23_trace : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
  raZ (h_regs rsegs hx) = ACfn.RA_LLVMF -> raZ regsT = RH_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TfibB)) regsT (RPgPostMal.rl_c23_ch hx)) (as_universe TfibB).
Proof.
intros regsT hx Hh Hr. unfold RPgPostMal.rl_c23_ch.
destruct (spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)); unfold call_trace0, unwind_of_chain; rewrite Hr.
- rewrite Hh. apply In_of_existsb; vm_compute; reflexivity.
- apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* free(pod) and free(pp), returns 0x82480 and 0x82488 (RPgX01.rx_S_X01's trace premise) *)
Lemma role_x01_trace : forall c : list Z,
  In c [[RPgX01.RX_RA1]; [RPgX01.RX_RA1; ACfn.RA_LLVMF]; [RPgX01.RX_RA2]; [RPgX01.RX_RA2; ACfn.RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code TfibB) ::
    flat_map (fun r => if r =? pc_free_ra0 (as_code TfibB) then [] else [r]) c)) (as_universe TfibB).
Proof.
intros c Hc. cbn [In] in Hc.
destruct Hc as [<- | [<- | [<- | [<- | []]]]]; apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* ===================================== the record's facts ===================================== *)
(* errno's word [0x5d62ec, 0x5d62f0) lies in one loaded segment *)
Lemma role_errno_img_chk : existsb (fun s => (Z.of_N (seg_base s) <=? 0x5d62ec) &&
  (0x5d62f0 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_api_env : api_env rsegs TfibB.
Proof.
split; [cbn [as_errno TfibB]; unfold TFIB_ERRNO, kLowMemEnd; lia|].
split.
- intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha.
  pose proof role_errno_img_chk as C. apply existsb_exists in C as (s & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hs | lia].
- split; apply In_of_existsb; vm_compute; reflexivity.
Qed.

Lemma role_ml : model_laws (as_universe TfibB).
Proof. exact (YG05.model_laws_ok _ (ts_universe _ TfibB_syms)). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma role_laws : AR_laws rsegs TfibB.
Proof. exact (AR_laws_ok rsegs TfibB). Qed.

(* the side stack's flag law [knock APgLib.v:258-271 link_FFL] *)
Lemma role_ffl : frame_flag_lawP rsegs TfibB.
Proof.
intros ly S W mem md cid pos HAR Hin.
pose proof role_laws as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (ACeg.tfib_img_cover ly S md L) as [C1 C2].
unfold ACeg.TFIB_IMG_LO, ACeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ===================================== the runtime's contracts at TfibB ===================================== *)
Lemma role_memcpy : aintrin_realizes rsegs TfibB OCpy 0x510d4.
Proof.
pose proof (AE2q.asan_memcpy_realizes TfibB role_laws TfibB_syms) as H.
unfold aintrin_realizes. exact H.
Qed.

Lemma role_memset : aintrin_realizes rsegs TfibB OSet 0x51570.
Proof.
unfold aintrin_realizes. intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE2r.asan_memset_realizes TfibB role_laws TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst
  Hra Hhull Ham).
Qed.

Lemma role_strlen : StrlenDef.astrlen_realizes rsegs TfibB StrlenDef.STRLEN_ENTRY.
Proof. exact (Strlen.strlen_icpt_contract TfibB role_laws TfibB_syms). Qed.

Lemma role_sm3 : astack_malloc_realizes rsegs TfibB 3.
Proof. exact (StackMalloc3.stack_malloc3_contract TfibB role_laws TfibB_syms). Qed.

Lemma role_ssf5 : SetShadowDef.aset_shadow_realizes rsegs TfibB RPgX01.RX_SSF5 0xf5.
Proof. exact (SetShadow.disco_set_shadow_f5 TfibB role_laws TfibB_syms). Qed.

Lemma role_strcmp : AStrcmpDef.astrcmp_realizes rsegs TfibB 0x41ad0.
Proof. exact (Strcmp.strcmp_icpt_contract TfibB role_laws TfibB_syms). Qed.

End a.

Lemma role_strcmp_all {rc : YM05.RunCeil} : forall fy : YK11.FPState, @AStrcmpDef.astrcmp_realizes fy rc rsegs TfibB 0x41ad0.
Proof. intros fy. exact (role_strcmp (fx := fy) (rc := rc)). Qed.

(* ===================================== the statement ===================================== *)
Section t.
(* ent_build's cases 6 .. 8 (0x81184 .. J 0x8165c): the one piece whose proof is not yet on the tree *)
Hypothesis PW6c : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  rs_piece_W6c_stmt (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) rsegs TfibB ameter_triv.

Theorem role_lib_x_all : role_lib_x_all_stmt.
Proof.
intros rc LS LEAF AFREE AMALLOC fx. unfold role_lib_contract_x.
pose proof (AR_laws_ok rsegs TfibB) as LAWS.
pose proof ameter_triv_laws as MTL.
pose proof (role_memcpy (fx := fx) (rc := rc)) as MCPY.
pose proof (role_memset (fx := fx) (rc := rc)) as MSET.
pose proof (role_strlen (fx := fx) (rc := rc)) as STRL.
pose proof (role_strcmp_all (rc := rc)) as STRC.
pose proof (RPgParse.rl_parse_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS
  eq_refl eq_refl (role_strcmp (fx := fx) (rc := rc))) as PARSE.
exact (@RPgTopI.role_lib_x_A fx rc AE2k.tfib_sink_head LS role_c_hofl TfibB
  (RPgStatA.rh_static_A (rc := rc) TfibB TfibB_syms)
  AE2k.tfib_K XL0 ACfn.A_LLVMF ACfn.RA_LLVMF ACfn.A_EMPTY ACfn.EV_LIB ACfn.LIVE_LIB ACfn.LLVMF_STK
  role_c_entry role_c_ev role_c_stk (AD1u.tfib_AIL TfibB TfibB_syms) LEAF
  (* S_E01 *)
  (RPgE01.e01_ok (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB 0x9a120 0x9b528
    ACfn.RA_LLVMF ACfn.A_EMPTY ACfn.EV_LIB ACfn.LIVE_LIB ACfn.LLVMF_STK
    role_c_e01_stk (role_sm3 (fx := fx) (rc := rc)) role_ml role_api_env eq_refl eq_refl eq_refl eq_refl eq_refl
    role_c_empty (AMALLOC fx) eq_refl role_e01_trace role_c_e01_ev role_c_e01_live)
  (* the malloc(pod) step *)
  (RPgPostMal.rl_A_S_C23 (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB 0x9a120 0x9b528
    ACfn.RA_LLVMF ACfn.A_EMPTY ACfn.EV_LIB ACfn.LIVE_LIB ACfn.LLVMF_STK
    (AMALLOC fx) role_api_env role_ml eq_refl role_c_c23_stk role_c_c23_ev role_c_c23_live role_c23_trace)
  (* S_X01, at every float state *)
  (fun fx' => RPgX01.rx_S_X01 (fx := fx') (rc := rc) (SK := AE2k.tfib_sink_head) TfibB 0x9a120 0x9b528
    ACfn.RA_LLVMF ACfn.A_EMPTY ACfn.EV_LIB ACfn.LIVE_LIB ACfn.LLVMF_STK
    role_ml role_api_env (AFREE fx') (role_ffl (rc := rc)) (role_ssf5 (fx := fx') (rc := rc)) eq_refl
    role_x01_trace role_c_x01_stk role_c_x01_ev)
  (* the build's pieces *)
  (RPgW3a.rs_piece_W3a (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS MSET)
  (RPgW3b.rs_piece_W3b_hdr (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgW3b.rs_piece_W3b_b7 (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgW3bPre.rs_piece_W3b_pre (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgProp.pa_piece_sel (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgProp.pa_piece_int7 (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS MSET)
  (RPgProp.pa_piece_key (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgProp.pa_piece_latch (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgW5IntP.w5_piece_int (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS MSET)
  (RPgW5OpenP.w5_piece_open (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgW5CloseP.w5_piece_close (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgW6a.w6_disp (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS MSET)
  (RPgW6a.w6_cases (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgW6b.rs_piece_W6b (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS MCPY STRL)
  (PW6c rc fx)
  (RPgEnt0.r7_piece_W7a (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv STRL MCPY)
  (RPgW7b.w7_piece (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv STRL MCPY)
  (RPgW8.rs_piece_W8 (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MCPY MSET)
  (RPgPostTop.w10_post (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgPostCorr.w10_corr (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgPostReq.w10_req (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (* the checks' pieces *)
  (RPgScanHead.rk_head_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MCPY PARSE)
  (RPgScanSetup.rk_setup_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgScanOuter.rk_outer_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgScanInner.rk_inner_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv)
  (RPgM02Key.rl_m02_key_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS STRC
    eq_refl eq_refl)
  (RPgM02Tail.rl_m02_checks_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS)
  (RPgM02Tail.rl_m02_tail_A (fx := fx) (rc := rc) (SK := AE2k.tfib_sink_head) TfibB ameter_triv MTL LAWS STRC
    eq_refl eq_refl)).
Qed.
End t.

Print Assumptions role_lib_x_all.
