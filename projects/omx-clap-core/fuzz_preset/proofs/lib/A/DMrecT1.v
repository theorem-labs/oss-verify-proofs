(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecT1.v (commit 67deba317dfb, blob ec4a74871847) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhf AFhd AFhl AFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrecS DMrecL DMrecS2 DMrecS3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ErrnoApartpreset.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, AFh9.YFRAME, AFha.YFRAME, AFhc.YFRAME, AFhb.YFRAME, DMwalkIFA.DRSTACK_X in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma errno_w : forall B i, TfibSyms B -> 0 <= i < 4 -> bv_unsigned (w64 (as_errno B + i)) = as_errno B + i.
Proof. intros B i TB Hi. rewrite (ts_errno B TB). unfold w64. apply unsigned_lit_small. unfold TFIB_ERRNO. lia. Qed.
Lemma errno_stk : forall B ly lo hi i, TfibSyms B -> layout_ok ly -> img_cover ly -> ly_stk_lo ly <= lo -> 0 <= i < 4 ->
~ (lo <= bv_unsigned (w64 (as_errno B + i)) < hi).
Proof.
intros B ly lo hi i TB LY IMG L Hi Hw. rewrite (errno_w B i TB Hi) in Hw.
apply (errno_apart_stack errno_in_img_preset B ly lo hi (as_errno B + i) TB LY IMG L Hw). lia.
Qed.
Lemma ek_trans : forall B m1 m2 m3, errno_kept B m1 m2 -> errno_kept B m2 m3 -> errno_kept B m1 m3.
Proof. intros B m1 m2 m3 H1 H2 i Hi. rewrite (H2 i Hi). exact (H1 i Hi). Qed.
Lemma mn_safe_stk : forall ly (x : word), layout_ok ly -> ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly ->
MemnormT.mn_safe tfibsegs x.
Proof.
intros ly x LY Hx. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : DMwalkIFA.rmaxd_ok RMAXD.
Hypothesis RV : DMwalkIFA.di_rview_x_t B ARXr DRq RMAXD.
Hypothesis FR : di_frame_t ARXr AOX.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIFA.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (AFhd.sp0 regs0).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@AFhd.zlen _).
Local Notation SB := (ly_space ly).
Local Notation hdra := (AFhd.hdra B ly).
Local Notation accr := (DMrecL.accr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation ostr := (DMrecL.ostr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTr := (DMrecL.OSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Ltac open_PRE := pose proof PRE as (HAR0 & Hinst & HDQ & LY & IMG & HSTK & HBL & LENP & INIT & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & CELLS).
Local Notation entry_facts := (DMrecS2.entry_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (DMrecS2.sp_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation HLY := (DMrecS3.HLY B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation slot_facts := (DMrecS.slot_facts_r B ARXr DRq RMAXD HRM RV ly HLY).
Local Notation lastaddr := (AFhg.lastaddr ly).
Local Notation DRSTACK_X := DMwalkIFA.DRSTACK_X.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, AFhd.sp1, AFhd.sp0, DMrecL.SYr in *; numconst.

Lemma batch_cells_in_slots_r : forall l ce, DMrecL.blen_ok l -> In ce (batch_cells l) ->
exists b, In b l /\ forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> bslot ly (b_self b) (aeval B ly (c_at ce) + j).
Proof.
intros l ce Hl Hce. apply In_batch_cells in Hce as (i & b & Hi & Hce). exists b. split; [exact (nth_error_In _ _ Hi)|].
apply (batch_own_cells_in_slot B ly b (next_exp l i) ce); [|exact Hce]. exact (proj1 (Forall_forall _ _) Hl b (nth_error_In _ _ Hi)).
Qed.
Lemma batch_cells_xfer_r : forall l (rd rd' : reader), DMrecL.blen_ok l ->
(forall b a, In b l -> bslot ly (b_self b) a -> rd' a = rd a) ->
Forall (cell_holds B ly rd) (batch_cells l) -> Forall (cell_holds B ly rd') (batch_cells l).
Proof.
intros l rd rd' Hl AG OLD. apply Forall_forall. intros ce Hce.
apply (cell_holds_agree B ly rd rd' ce (proj1 (Forall_forall _ _) OLD ce Hce)). intros j Hj.
destruct (batch_cells_in_slots_r l ce Hl Hce) as (b & Hb & Hs). exact (AG b _ Hb (Hs j Hj)).
Qed.

Lemma ARXr_after_stack_write : forall X (W : world tfibsegs) mem mem' md mat (WINP : Z -> Prop),
ARXr (as_inst B) ly X W mem md -> (forall a, AOX ly X a -> AOX ly X0 a) ->
(forall a, WINP a -> ly_stk_lo ly <= a < ly_stk_hi ly) -> (forall a, WINP a \/ ~ WINP a) ->
(forall x : word, ~ WINP (bv_unsigned x) -> mem' x = mem x) ->
(forall a, WINP a -> apresent (w_H W) mem' a) ->
ARXr (as_inst B) ly X W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros X W mem mem' md mat WINP HA SH HST DEC MQ PRS. open_PRE. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (FR (as_inst B) ly X W mem md mem' _ HA).
- intros a Ha O. apply aview_same. apply MQ. rewrite unsigned_lit_small by exact Ha. intros Hw.
  exact (DMrecS2.stack_not_owned_r B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE X a SH (HST a Hw) O).
- intros a Hv HN. cbn [im_segs AImg_A] in Hv, HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (mem' x) as [b'|] eqn:E'; [cbn in HN; discriminate|].
destruct (mem x) as [b0|] eqn:E0; [|exact (Hv HN)].
destruct (DEC a') as [C|C].
+ destruct (PRS a' C) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
+ rewrite (MQ x C) in E'. congruence.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. apply MQ. unfold w64. rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
intros Hw. pose proof (HST a Hw). clear - Ha H T7. unfold in_band_rw, zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.

Lemma ek_stk : forall lo hi (m m' : word -> option byte), ly_stk_lo ly <= lo ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> errno_kept B m m'.
Proof.
intros lo hi m m' L MQ i Hi. open_PRE.
apply MQ. exact (errno_stk B ly lo hi i TB LY IMG L Hi).
Qed.
Lemma mk_stk : forall lo hi (m m' : word -> option byte), ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> MemnormT.memnorm_keep tfibsegs m m'.
Proof.
intros lo hi m m' L H MQ. open_PRE.
apply (MemnormLocG.memnorm_keep_window tfibsegs (fun a => lo <= a < hi) m m'); [|exact MQ].
intros x Hx. cbv beta in Hx. apply (mn_safe_stk ly x LY). lia.
Qed.
End e.
End c.
