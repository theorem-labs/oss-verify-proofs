(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillSeamcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 8c00fdba16cf) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane W, ReallocPrimary.CfW; a Theorem Labs lane cf layer).  rule 24: no function proved (kind: interface,
   the SEAM between the two halves of the cf refill walk).

   The cf layer's refill walk target YGcfInstRefill.refill_spec_core_cf (d80162ffa5c9) is proved by re-basing c5's memnorm refill
   walk (MnRefillB3 / MnRefillR, cgif's AR + YFl1.refill_pre) on ARXq_cf / ARmcf / cls_ok_cf and the cf tree
   refill_tree_cf.  Two hands, one seam, fixed here:
   - HALF 1 (lane W, CfW): [refill_B3_inner_cf] (the B3 walk from the joined symbolic state R3_J, c5 MnRefillB3.refill_B3
     re-based; the class-full report arm is ONE named Section hypothesis of half 1's file, proved by another hand) and
     [refill_B3_entry_cf] (the inited cache with too few free chunks, from the refill entry: c5 MnRefillR.refill_B3R).
   - HALF 2 (a Theorem Labs lane): [refill_B2_entry_cf] (the inited cache with enough free chunks: c5 MnRefillR.refill_B2R) and
     [refill_uninit_entry_cf] (the uninited cache: c5 MnRefillR.refill_uninitR, whose B3 case calls
     [refill_B3_inner_cf] at the post-init state, as c5 MnRefillR.v:285 calls MnRefillB3.refill_B3).
   [refill_spec_core_cf_of_cases] assembles the layer's walk target refill_spec_core_cf (d80162ffa5c9) from the three
   entry cases; the Allocate-site corollary refill_walk_cf is TkSecLink's.
   Every statement here is over cgif's image (YFk5 / YFk8's names, TfibSyms), the cf model and the layer's
   [refill_leaf_core_cf]; both halves relocate to each cf unit (reply lane W; preset A11) by the agreloc route.
   EVENT-FREE: st_nev appears only in the tick `set_nev (st_nev S0 + 1) S0`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFk5cf YFk8cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstRefill.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.
(* refill_B3_inner_cf is at cgif's image: AImg_cgif / AGImg_cgif (AGif2cgif.v:24, AGif0cgif.v:116) by instance resolution. *)

(* ================================================================================================================ *)
(* HALF 1's inner B3 walk: c5 MnRefillB3.refill_B3's statement (MnRefillB3.v:83-274, :2069) with cgif's model parts
   replaced: ARm -> ARmcf (+ Hp), AR -> ARcf, the event regime refill_reg / the EV_A slack / qloosem dropped, qloose
   (Wf_cf's mroom_cf source, YG08cf), xs_mapped_cf and the class room of refill_state_gen_cf added (batch_room_cf for
   kBatchClass, whose populate_cf is cgif's; ERRB_ROOM for every other class); the tree is refill_tree_cf and the leaf is the
   layer's refill_leaf_core_cf at the call state S (unticked: WfP_cf 1 0 0, one user map of credit).  Field round 3:
   the call-state facts of the layer's refill contracts (YGcfInstRefill.refill_walk_cf / refill_spec_core_cf /
   refill_spec_cf), arodata_ok_cf and cf_hull_ok (memnorm left in part 3c), at the entry, supplied by the caller. *)
Definition refill_B3_case_cf (Q : Z -> Z -> Prop) : Prop :=
forall (Hp : list Z) (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z)
  (mat0 : list word) (msJ : machine_state) (B : asyms) (S : astate),
let sp0 := bv_unsigned (getr regs0 2) in
let T := ly_T ly in
img_cover ly -> layout_ok ly -> 1 <= c <= 31 -> maxc = max_cached c -> n = maxc / 2 -> csz = class_size c ->
(0 <= nf /\ 4 * nf <= mf) -> (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) ->
(0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) ->
0 <= j64 < 2 ^ 32 -> 0 <= jna < 2 ^ 64 -> 0 <= jnf < 2 ^ 64 -> 0 <= jsm < 2 ^ 64 -> 0 <= jm1 < 2 ^ 64 -> 0 <= jm2 < 2 ^ 64 -> 0 <= jex < 2 ^ 8 ->
(ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) -> ly_stk_lo ly + REP_W c <= sp0 ->
YK0s.ret_ok (getr regs0 1) -> 4096 <= bv_unsigned (getr regs0 1) -> getr regs0 4 = w64 TFIB_TP ->
getr regs0 10 = w64 (T + t_cache) -> getr regs0 11 = w64 (@YFk5cf.Pr ly c) -> getr regs0 12 = w64 A_ALLOCATOR ->
getr regs0 13 = w64 c ->
nf < n -> mu - au < kUserMapSize + kMaxSize -> au mod csz = 0 -> need = n - nf -> tot = au + need * csz ->
adr = @YFk5cf.RBv ly c + mu -> sha = YFk5cf.SHBv + adr / 8 -> mu2 = mu + kUserMapSize -> nce = (mu - au) / csz ->
ncg = (mu2 - au) / csz -> nfe = nf + nce -> nfg = nf + ncg -> fadr = @YFk5cf.FAv ly c + mf -> shf = YFk5cf.SHBv + fadr / 8 ->
mf2 = mf + kFreeArrayMapSize -> aue = au + nce * csz -> aug = au + ncg * csz ->
@YFk5cf.at_R3 _ ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg
  fadr shf mf2 aue aug W md0 (@YFk5cf.WINR0 ly regs0 c) (fun _ => True) YFk8cf.R3_J W
  (mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0)) ->
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) ->
(forall a, sp0 - REP_W c <= a < sp0 -> apresent (w_H W) mem0 a) ->
(forall a, @YFk5cf.DSTv ly c <= a < @YFk5cf.DSTv ly c + 64 -> apresent (w_H W) mem0 a) ->
(forall a, @YFk5cf.FAv ly c <= a < @YFk5cf.FAv ly c + mf -> apresent (w_H W) mem0 a) ->
TfibSyms B -> ly_tsd ly = TFIB_TSD ->
ARmcf B ly S Hp (aview tfibsegs (w_H W) mem0) ->
getr regs0 3 = w64 (as_gp B) -> st_cache_inited S = true -> pc_chunks (cache S c) = [] ->
nf = fa_len (rg_free (reg S c)) -> mf = rg_mapped_fa (reg S c) -> au = rg_alloc_user (reg S c) ->
mu = rg_mapped_user (reg S c) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 64) 4 j64 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 72) 8 jna ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 80) 8 jnf ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2792) 8 jsm ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2 ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFk5cf.RGv ly c + 68) 1 jex ->
exh_cell_cf B ly S (aview tfibsegs (w_H W) mem0) -> errb_cells_cf B ly S (aview tfibsegs (w_H W) mem0) ->
qloose S -> ARcf tfibsegs B ly S Hp W mem0 md0 -> xs_mapped_cf ly S md0 ->
(c = kBatchClass -> batch_room_cf S) -> (c <> kBatchClass -> ERRB_ROOM S /\ WfP_cf (as_universe B) 1 1 0 S) ->
WfP_cf (as_universe B) 1 0 0 S ->
arodata_ok_cf tfibsegs B mem0 -> cf_hull_ok S ->
Q mu tot ->
amreal tfibsegs (refill_tree_cf c S) W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0))
  (refill_leaf_core_cf B Hp ly S c W regs0 mem0 md0).
(* exh_cell_cf / errb_cells_cf (YGcfInstBase.v:67-80 at 24612d340b0): the class's exhausted byte RI+68 is
   (if exh_mem_cf S c then 1 else 0), so jex is that value, and the error-message buffer's object cells are the model's
   errb.  Both come from ARX_cf at the call state (ARX_cf :85-88; projections ARX_cf_exh :119, ARX_cf_errb :123), which
   refill_state_gen_cf (YGcfInstRefill.v :115) carries for every caller (Allocate's and Enqueue's miss arms). *)
(* The whole inner walk: every case. *)
Definition refill_B3_inner_cf : Prop := refill_B3_case_cf (fun _ _ => True).
(* THE CLASS-FULL REPORT ARM (proved by a Theorem Labs lane's report walk; MnRefillB3cf takes it as a Section hypothesis): the
   user region needs a new map (mu < tot) and none fits (kFreeArrayOffset < mu + kUserMapSize): c5 MnRefillB3.v:2056's XF
   case, vacuous in cgif's tree (E_mmu_fail, mcheck 222820), the cf tree's errb_report_cf / set_exh_cf arm. *)
Definition refill_B3_classfull_cf : Prop :=
  refill_B3_case_cf (fun mu tot => mu < tot /\ kFreeArrayOffset < mu + kUserMapSize).

(* ================================================================================================================ *)
(* The three entry cases of the layer's refill_spec_core_cf (YGcfInstRefill.v:171 at d80162ffa5c9): the CALL-SITE-GENERIC
   refill, unticked at the call state, any caller's registers / stack (refill_state_gen_cf :115, refill_call_gen_cf :123),
   the machine leaf refill_leaf_core_cf (acall_post_cf / errno view / raw frame over the class window REP_W c, refill
   route 2, d94d29d53c8: RSTACK at kBatchClass, REP_STACK otherwise). *)
Section b.
Context {IM : AImg} {AG : AGImg}.
Variable B : asyms.
Variable IOK : Z -> Prop.

Definition refill_case_cf (P : astate -> Z -> Prop) : Prop :=
forall Hp inst ly S W regs mem md c,
refill_state_gen_cf B IOK Hp inst ly S W mem md c ->
arodata_ok_cf im_segs B mem -> cf_hull_ok S ->
refill_call_gen_cf B inst ly W regs mem c ->
P S c ->
amreal im_segs (refill_tree_cf c S) W (cfg_at im_segs ag_refill regs mem md) (refill_leaf_core_cf B Hp ly S c W regs mem md).

(* HALF 1 (c5 MnRefillR.refill_B3R): the inited cache with fewer than max_cached / 2 free chunks *)
Definition refill_B3_entry_cf : Prop :=
refill_case_cf (fun S c => st_cache_inited S = true /\ fa_len (rg_free (reg S c)) < max_cached c / 2).
(* HALF 2 (c5 MnRefillR.refill_B2R): the inited cache with at least max_cached / 2 free chunks *)
Definition refill_B2_entry_cf : Prop :=
refill_case_cf (fun S c => st_cache_inited S = true /\ max_cached c / 2 <= fa_len (rg_free (reg S c))).
(* HALF 2 (c5 MnRefillR.refill_uninitR, both free-count cases; its B3 case uses refill_B3_inner_cf) *)
Definition refill_uninit_entry_cf : Prop :=
refill_case_cf (fun S _ => st_cache_inited S = false).

(* The assembly (lane W): the three cases give the layer's walk target. *)
Lemma refill_spec_core_cf_of_cases :
  refill_B3_entry_cf -> refill_B2_entry_cf -> refill_uninit_entry_cf -> refill_spec_core_cf B IOK.
Proof.
intros H3 H2 HU Hp inst ly S W regs mem md c HS HRO HH HC.
destruct (st_cache_inited S) eqn:EI.
- destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [L|L].
  + exact (H3 Hp inst ly S W regs mem md c HS HRO HH HC (conj EI L)).
  + exact (H2 Hp inst ly S W regs mem md c HS HRO HH HC (conj EI L)).
- exact (HU Hp inst ly S W regs mem md c HS HRO HH HC EI).
Qed.
End b.
End a.
