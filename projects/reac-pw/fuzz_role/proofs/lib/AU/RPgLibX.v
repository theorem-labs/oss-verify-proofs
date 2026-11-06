(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: role_ffl is proofs/libreac/fuzz_knock/lib/A/APgLib.v link_FFL at origin/ossv/recipes
   6ebe35ba632 (in the form proofs/libreac/fuzz_decode/lib/A/DecodeARtStackMalloc.v dec_ffl states it, without the
   unfold of YImgTop's notations), at reac-pw/fuzz_role's image A and its start-up record TfibB; the rest of the file
   is written new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgLibX.v at c9f9a5a10e3 for image B: image B's
   core (lib/AU YB1v / YD2l / YE2k / YCfn / YD1u / YE2q / YE2r / YF0m / YF0x / YCej), its runtime entries (memcpy
   0x5116c, memset 0x51608, the strlen wrapper 0x41b60, the strcmp wrapper 0x41b68, the class-4 frame, set_shadow_f5
   0x54134; lib/AU/Rt), the read-only range 0x9a3c0 .. 0x9b7c8, the chaining of lib/AU/RPgTopI.v, and every walk
   piece of image B by its theorem, as proofs/reac-pw/fuzz_rate/lib/AU/RtPgTopAB.v / RtPgLinkB.v at 7ed26d298ff
   discharge theirs; image A's open W6c premise is a theorem here. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses from the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): lib/AU/RPgLib.v's statement of the walk of
   LLVMFuzzerTestOneInput (0x80020), proved.

     role_lib_x_all : role_lib_x_all_stmt

   It is lib/AU/RPgTopI.v role_lib_x_B at the relocated frame's start-up record YD2l.TfibB, its sink YE2k.tfib_K,
   XL0 and YCfn's harness constants (A_LLVMF 0x80020, RA_LLVMF 0x7ff1c, A_EMPTY 0x5d5ce0, EV_LIB 2000, LIVE_LIB 2^33,
   LLVMF_STK 32768), with every premise discharged:
   - the harness constants' numeric premises and the sink's overflow head (0x9b7c8 <= 0x5f6d08), by computation;
   - the sink's laws: YD1u.tfib_AIL at TfibB; the static law: RPgStatA.rh_static_B at TfibB;
   - the walk's pieces by their theorems (RPgE01.e01_ok, RPgW3a .. RPgW8, RPgPostTop / PostCorr / PostReq /
     PostMal, RPgScanHead / Setup / Outer / Inner, RPgM02Key / M02Tail, RPgX01.rx_S_X01_B), the two middle contracts
     by RPgMainL.role_build_holds / role_check_holds inside role_lib_x_B;
   - the runtime contracts the pieces call, at TfibB: __asan_memcpy 0x5116c and __asan_memset 0x51608 (YE2q / YE2r),
     the strlen wrapper 0x41b60 (Rt/Strlen.v), the strcmp wrapper 0x41b68 at every float state (Rt/Strcmp.v), the
     class-4 frame (Rt/StackMalloc4.v), __asan_set_shadow_f5 0x54134 at every float state (Rt/SetShadow.v), the
     parse 0x83130 (RPgParse.rl_parse_B), pod_write_ent (PweRun.pod_write_ent_B inside the pieces' _B forms);
   - the symbol record's facts: the allocator's model laws (YG05.model_laws_ok), the API environment, the frame flag
     law, the GOT / runtime cells and code entries (RPgE01B.e01b_TfibB_cells and by computation) and the call traces
     of the four allocator sites (each in YCej.Tfib_universe), by computation on TfibB;
   - malloc and free: role_lib_x_all_stmt's own premises.
   No Section hypothesis is left. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require YB1v YD2l YE2k YCfn YD1u YE2q YE2r YF0m YF0x YCej.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.Rt Require Strcmp Strlen StackMalloc4 SetShadow StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgHarn RPgLib.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgTopI RPgParseBase RPgParse.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgW6a RPgW7bBase RPgW7bCall RPgEnt0 RPgW7b.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgScanHead RPgScanSetup RPgScanOuter RPgScanInner.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgM02Key RPgM02Tail RPgX01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgStatA RPgE01D RPgE01B RPgE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgW3a RPgW3aB7 RPgW3b RPgW3bPre.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgProp RPgPropSelB RPgPropSel RPgPropKeyB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgW5IntP RPgW5OpenP RPgW5CloseP RPgW6c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgW8 RPgPostTop RPgPostCorr RPgPostReq RPgPostMal.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgW6b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Local Notation TB := YD2l.TfibB.
Local Notation TBS := YD2l.TfibB_syms.
(* the relocated frame's sink head, for the statements below that read it *)
#[local] Existing Instance YE2k.tfib_sink_head.

Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac zlt := apply Z.ltb_lt; vm_compute; reflexivity.

(* ===================================== the harness constants ===================================== *)
Lemma role_c_hofl : 0x9b7c8 <= @YI16.sk_ofl_head YE2k.tfib_sink_head.
Proof. zle. Qed.
Lemma role_c_entry : YCfn.A_LLVMF = RH_ENTRY.
Proof. reflexivity. Qed.
Lemma role_c_ev : RH_EV <= YCfn.EV_LIB.
Proof. zle. Qed.
Lemma role_c_stk : RH_RSZ + 32 + ASTACK <= YCfn.LLVMF_STK.
Proof. zle. Qed.
Lemma role_c_empty : 0 < YCfn.A_EMPTY < kLowMemEnd.
Proof. split; zlt. Qed.

(* ===================================== the record's facts ===================================== *)
(* errno's word lies in one loaded segment *)
Lemma role_errno_img_chk : existsb (fun s => (Z.of_N (seg_base s) <=? YF0m.TFIB_ERRNO) &&
  (YF0m.TFIB_ERRNO + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_api_env : api_env rsegs TB.
Proof.
split; [rewrite (YF0m.ts_errno TB TBS); unfold YF0m.TFIB_ERRNO, kLowMemEnd; lia|].
split.
- intros a Ha. rewrite (YF0m.ts_errno TB TBS) in Ha.
  pose proof role_errno_img_chk as C. apply existsb_exists in C as (s & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hs | lia].
- split; apply YCej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma role_ml : model_laws (as_universe TB).
Proof. exact (YG05.model_laws_ok (as_universe TB) (YF0m.ts_universe TB TBS)). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let LAWS : AR_laws rsegs TB := AR_laws_ok rsegs TB.

(* the side stack's flag law [knock APgLib.v:258-271 link_FFL] *)
Lemma role_ffl : frame_flag_lawP rsegs TB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YF0x.img_cover_of_ledger ly S md L) as [C1 C2].
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ===================================== the runtime's contracts at TfibB ===================================== *)
Lemma role_memcpy : aintrin_realizes rsegs TB OCpy 0x5116c.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (YE2q.asan_memcpy_realizes TB LAWS TBS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull
  Hsrc).
Qed.

Lemma role_memset : aintrin_realizes rsegs TB OSet 0x51608.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (YE2r.asan_memset_realizes TB LAWS TBS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma role_strlen : StrlenDef.astrlen_realizes rsegs TB StrlenDef.STRLEN_ENTRY.
Proof. exact (Strlen.strlen_icpt_contract TB LAWS TBS). Qed.

Lemma role_sm4 : astack_malloc_realizes rsegs TB 4.
Proof. exact (StackMalloc4.stack_malloc4_contract TB LAWS TBS). Qed.

Lemma role_ssf5 : SetShadowDef.aset_shadow_realizes rsegs TB SetShadow.SSF5_ENTRY 0xf5.
Proof. exact (SetShadow.disco_set_shadow_f5 TB LAWS TBS). Qed.

Lemma role_strcmp : AStrcmpDef.astrcmp_realizes rsegs TB 0x41b68.
Proof. exact (Strcmp.strcmp_icpt_contract TB LAWS TBS). Qed.

Lemma role_AIL : asink_img_laws rsegs TB YE2k.tfib_K.
Proof. apply YD1u.tfib_AIL; first [exact TBS | exact LAWS]. Qed.

(* The strlen wrapper's law in the form case 0's pieces state it (lib/AU/RPgW7bCall.v's copy, whose read-only premise
   w7b_aro_unowned is lib/AU/Rt/WrapRo.v's aro_unowned word for word, at Img0.rsegs), from Rt/Strlen.v's (at
   YB1v.tfibsegs: the same loaded segments). *)
Lemma role_strlen_w7b : RPgW7bCall.w7b_astrlen_realizes rsegs TB RPgW7bBase.W7B_STRLEN.
Proof.
pose proof role_strlen as H.
unfold RPgW7bCall.w7b_astrlen_realizes, RPgW7bCall.w7b_aro_unowned, RPgW7bBase.W7B_STRLEN.
unfold StrlenDef.astrlen_realizes, WrapRo.aro_unowned, StrlenDef.STRLEN_ENTRY in H. exact H.
Qed.
End a.

Lemma role_strcmp_all {rc : YM05.RunCeil} : forall fy : YK11.FPState, @AStrcmpDef.astrcmp_realizes fy rc rsegs TB 0x41b68.
Proof. intros fy. exact (role_strcmp (fx := fy) (rc := rc)). Qed.

(* the runtime's shadow-offset cell and its GOT entry (the parse and the M02 pieces load K through them) *)
Lemma role_hgot : as_got_shadow TB = 0x9aad0.
Proof. vm_compute. reflexivity. Qed.
Lemma role_hsc : as_shadow_cell TB = 0xa3678.
Proof. vm_compute. reflexivity. Qed.
(* the free trampoline's entry *)
Lemma role_hfree : pc_wrap_free (as_code TB) = RPgX01.RX_FREE.
Proof. vm_compute. reflexivity. Qed.

(* free(pod) and free(pp), returns 0x82578 and 0x82580: their call traces are in YCej.Tfib_universe *)
Lemma role_x01_trace : forall c,
  In c [[RPgX01.RX_RA1]; [RPgX01.RX_RA1; YCfn.RA_LLVMF]; [RPgX01.RX_RA2]; [RPgX01.RX_RA2; YCfn.RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code TB) ::
    flat_map (fun r => if r =? pc_free_ra0 (as_code TB) then [] else [r]) c)) (as_universe TB).
Proof.
intros c Hc. cbn [In] in Hc.
repeat (destruct Hc as [<-|Hc]; [apply YCej.memZL_In; vm_compute; reflexivity|]). contradiction.
Qed.
(* S_X01's stack and event budgets *)
Lemma role_c_x01_stk : ASTACK + RH_RSZ + 16 <= YCfn.LLVMF_STK.
Proof. zle. Qed.
Lemma role_c_x01_ev : 4 <= YCfn.EV_LIB.
Proof. zle. Qed.

(* malloc(pp), return 0x802c4 (RPgE01D.e01b_trace_stmt): its call traces are in YCej.Tfib_universe *)
Lemma role_e01_trace : RPgE01D.e01b_trace_stmt TB YCfn.RA_LLVMF.
Proof.
unfold RPgE01D.e01b_trace_stmt. intros regsT ch Hra Hch. unfold call_trace0, unwind_of_chain. rewrite Hra.
destruct Hch as [-> | (fp & v & ->)]; apply YCej.memZL_In; vm_compute; reflexivity.
Qed.
(* S_E01's frame bound, event and live budgets *)
Lemma role_c_e01_stk : 0x210 + ASTACK <= YCfn.LLVMF_STK.
Proof. zle. Qed.
Lemma role_c_e01_ev : 1 <= YCfn.EV_LIB.
Proof. zle. Qed.
Lemma role_c_e01_live : Layout.PP_SIZE <= YCfn.LIVE_LIB.
Proof. zle. Qed.

(* malloc(pod), return 0x82168 (RPgPostMal.rl_B_S_C23's trace premise): its call traces are in YCej.Tfib_universe *)
Lemma role_c23_trace : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
  raZ (h_regs rsegs hx) = YCfn.RA_LLVMF -> raZ regsT = RH_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (RPgPostMal.rl_c23_ch hx)) (as_universe TB).
Proof.
intros regsT hx Hh Hr. unfold RPgPostMal.rl_c23_ch.
destruct (spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)); unfold call_trace0, unwind_of_chain; rewrite Hr.
- rewrite Hh. apply YCej.memZL_In; vm_compute; reflexivity.
- apply YCej.memZL_In; vm_compute; reflexivity.
Qed.
(* the malloc(pod) step's event and live budgets (its stack bound is S_X01's) *)
Lemma role_c_c23_ev : 2 <= YCfn.EV_LIB.
Proof. zle. Qed.
Lemma role_c_c23_live : Layout.PP_SIZE + 5440 <= YCfn.LIVE_LIB.
Proof. zle. Qed.

(* ===================================== the statement ===================================== *)
Theorem role_lib_x_all : role_lib_x_all_stmt.
Proof.
intros rc LS LEAF AFREE AMALLOC fx.
unfold role_lib_contract_x, RO_LO, RO_HI, XL0.
(* the runtime and symbol facts the pieces take, at this run ceiling and float state *)
pose proof ameter_triv_laws as MTL.
pose proof (AR_laws_ok rsegs TB) as LAWS.
pose proof (role_memset : aintrin_realizes rsegs TB OSet 0x51608) as MSET.
pose proof (role_memcpy : aintrin_realizes rsegs TB OCpy 0x5116c) as MCPY.
pose proof (role_strlen : StrlenDef.astrlen_realizes rsegs TB StrlenDef.STRLEN_ENTRY) as STRL.
pose proof (role_strlen_w7b : RPgW7bCall.w7b_astrlen_realizes rsegs TB RPgW7bBase.W7B_STRLEN) as STRL7.
pose proof (role_strcmp : AStrcmpDef.astrcmp_realizes rsegs TB 0x41b68) as STRC0.
pose proof (role_strcmp_all (rc := rc)) as STRC.
pose proof (fun fy : YK11.FPState => role_ssf5 (fx := fy) (rc := rc)) as SSF5.
pose proof (role_ffl : frame_flag_lawP rsegs TB) as FFL.
pose proof role_ml as ML. pose proof role_api_env as HAPI.
pose proof role_hgot as HGOT. pose proof role_hsc as HSC. pose proof role_hfree as HFREE.
pose proof role_x01_trace as HTRACE. pose proof role_c_x01_stk as HSTKX. pose proof role_c_x01_ev as HEVX.
(* S_E01's: the class-4 frame law, the record's cells and code entries, malloc, the empty input, the trace, budgets *)
pose proof (role_sm4 : astack_malloc_realizes rsegs TB 4) as ASM4.
destruct RPgE01B.e01b_TfibB_cells as (HGOT2 & HSC2 & HGU & HUC & HBsm & HBmalloc).
pose proof (AMALLOC fx) as AMAL.
pose proof role_c_empty as HAE. pose proof role_e01_trace as HTRACE_E01.
pose proof role_c_e01_stk as HSTKE. pose proof role_c_e01_ev as HEVE. pose proof role_c_e01_live as HLIVE.
(* the malloc(pod) step's: its trace and budgets *)
pose proof role_c23_trace as HTRACE_C23. pose proof role_c_c23_ev as HEV_C23. pose proof role_c_c23_live as HLIVE_C23.
(* the parse 0x83130 (RPgParse.rl_parse_B), the callee of the checks' head *)
assert (PARSE : rl_parse_specX rsegs TB ameter_triv RPgParseBase.A_PARSE RPgParseBase.A_KEY RPgParseBase.role_B_dcs)
  by (apply RPgParse.rl_parse_B; assumption).
eapply (@RPgTopI.role_lib_x_B fx rc YE2k.tfib_sink_head LS role_c_hofl TB).
all: first
  [ exact LEAF | exact role_c_entry | exact role_c_ev | exact role_c_stk | exact role_AIL
  (* the static law (RPgStatA) *)
  | exact (RPgStatA.rh_static_B TB TBS)
  (* the pieces, by their theorems *)
  | (eapply RPgE01.e01_ok; assumption)
  | (apply RPgW3a.rs_piece_W3a; assumption)
  | (apply RPgW3aB7.rs_piece_W3b_b7; assumption)
  | (apply RPgW3b.rs_piece_W3b_hdr; assumption)
  | (apply RPgW3bPre.rs_piece_W3b_pre; assumption)
  | (apply RPgPropSelB.pa_piece_sel; assumption)
  | (apply RPgProp.pa_piece_int7_B; assumption)
  | (apply RPgPropKeyB.pa_piece_key; assumption)
  | (apply RPgPropSel.pa_piece_latch; assumption)
  | (apply RPgW5IntP.w5_piece_int_B; assumption)
  | (apply RPgW5OpenP.w5_piece_open; assumption)
  | (apply RPgW5CloseP.w5_piece_close; assumption)
  | (apply RPgW6a.w6b_disp; assumption)
  | (apply RPgW6a.w6b_cases; assumption)
  | (apply RPgW6b.rs_piece_W6b; assumption)
  | (apply RPgW6c.w6cb_piece; assumption)
  | (apply RPgW8.rs_piece_W8; assumption)
  | (apply RPgPostTop.w10_post; assumption)
  | (apply RPgPostCorr.w10_corr; assumption)
  | (apply RPgPostReq.w10_req; assumption)
  | (eapply RPgPostMal.rl_B_S_C23; assumption)
  | (apply RPgEnt0.r7b_W7a; assumption)
  | (apply RPgW7b.w7b_piece; assumption)
  | (apply RPgScanHead.rk_head_B; assumption)
  | (apply RPgScanSetup.rk_setup_B; assumption)
  | (apply RPgScanOuter.rk_outer_B; assumption)
  | (apply RPgScanInner.rk_inner_B; assumption)
  | (apply RPgM02Key.rl_m02_key_B; assumption)
  | (apply RPgM02Tail.rl_m02_checks_B; assumption)
  | (apply RPgM02Tail.rl_m02_tail_B; assumption)
  | (eapply RPgX01.rx_S_X01_B; assumption) ].
Qed.
