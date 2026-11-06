(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the composition technique (an SRr prefix joined to an amreal run with
   YG0d.v:101 amreal_SRr_pre, and the amreal's leaves continued by a second SRr run) is ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/AF0w.v and A/AFij.v, where cgif composes its malloc wrapper's walk the same
   way; the walk of lib/A/DecodeCallocWrap.v is re-run here with a stronger post (see WHY walk_C2X below). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_decode/lib/A/DecodeCallocTop.v (donor image sha256 5973b76807d8), with its module paths changed, names decodesegs0 -> tfibsegs and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/DecodeCallocTop.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The top of libreac/fuzz_decode's ASan calloc chain in image A (fuzz_decode.asan): the wrapper's EPILOGUE, and
   the composition that closes the kit's phase-1 claim [DecodeCalloc.decode_acalloc_of_allocate_A].

   WHAT THE EPILOGUE DOES (image A, read with capstone from the ORIGINAL unstripped binary
   fuzz_decode.asan; the walk runs
   the same words out of lib/A/DecodeCallocTbl.v's tbl_calloc_A, whose words are read from the image module):

     0x524a8  addi sp, sp, 0x70     sp = entry sp - 0x7f0        (entry sp = the wrapper's own entry sp)
     0x524ac  ld ra, 0x7e8(sp)      ra = [entry sp - 8]          the prologue's 0x52368 `sd ra, 0x7e8(sp)`
     0x524b0  ld s0, 0x7e0(sp)      s0 = [entry sp - 16]         0x5236c
     0x524b4  ld s1, 0x7d8(sp)      s1 = [entry sp - 24]         0x52370
     0x524b8  ld s2, 0x7d0(sp)      s2 = [entry sp - 32]         0x52374
     0x524bc  ld s3, 0x7c8(sp)      s3 = [entry sp - 40]         0x52378
     0x524c0  ld s4, 0x7c0(sp)      s4 = [entry sp - 48]         0x5237c
     0x524c4  ld s5, 0x7b8(sp)      s5 = [entry sp - 56]         0x52380
     0x524c8  ld s6, 0x7b0(sp)      s6 = [entry sp - 64]         0x52384
     0x524cc  addi sp, sp, 0x7f0    sp = entry sp
     0x524d0  ret                   to the caller's return address, the ra the prologue saved

   So the epilogue reads eight stack cells and writes no memory: the eight cells are the ones the prologue wrote,
   and [at_C2X] below carries them (that is the only reason this file re-runs the wrapper's walk).

   WHY [walk_C2X].  lib/A/DecodeCallocWrap.v's [at_C2] states the registers and the trace object at the call of
   __asan::asan_calloc, but not the eight saved cells and not x23 .. x27 (s7 .. s11, which the wrapper never
   touches).  The epilogue's eight loads and the leaf's [aregs_preserved] need exactly those, so [walk_C2X] is
   [walk_C2]'s script with a stronger close: the same seed, the same runtime-entry contracts, the same
   instructions, plus eight [st_ok_chunk_val] reads of the frame's chunks and five register reads.  If
   [at_C2] is strengthened in DecodeCallocWrap.v, [walk_C2X] can be deleted and [walk_C2] used in its place.

   THE COMPOSITION ([decode_acalloc_of_allocate_A_holds]).  From the trampoline 0x51f68:
     1. [walk_C2X] (SRr) to the entry of asan_calloc 0x31bd4, joined to the allocator run with
        YG0d.v:101 amreal_SRr_pre;
     2. [DecodeCallocEntry.entry_walk] (amreal over YG00.malloc at n = nm * sz) from there to the wrapper's
        0x524a8, its premises [entry_pre] built from [at_C2X] and the claim's own premises - including
        Allocate's `ly_bot ly < sp` at ITS entry, which is the claim's [cdepth] premise
        `ly_bot ly + DEC_CALLOC_DEPTH < spZ regs` at the wrapper's entry (DEC_CALLOC_DEPTH = 2192 = the
        wrapper's 2144-byte frame plus asan_calloc's 48);
     3. the epilogue (SRr) on every leaf, by DecodeCallocEntry.v:372 amreal_post_SRr;
     4. the leaf: YGCalloc.v's [calloc_leaf_with] at the cgif instance = YG0d.v:244 malloc_leaf (the allocator
        post, the layout and world order, the callee-saved registers, same_io, the memory frame, the stack
        window, a0 = the block, qtight) and YGCalloc.v's [calloc_zeroed] (every byte of [a0, a0 + n) reads 0).

   The callee-saved registers of the leaf: x2 is the entry sp again (sp - 2144 + 0x70 + 0x7f0); x3, x4 and
   x23 .. x27 are untouched the whole way ([at_C2X] and the Allocate leaf's own aregs_preserved); x8, x9,
   x18 .. x22 come back from the eight cells, whose bytes are unchanged because the Allocate leaf's memory frame
   covers every address that is neither owned by the allocator, nor inside asan_calloc's scratch window
   [sp - 6288, sp - 2144), nor errno, nor the new block, and the saved cells [entry sp - 64, entry sp) are none
   of those (the block lies below alloc_ceiling <= ly_stk_lo, errno below kLowMemEnd).

   Section hypotheses, each named in the report:
   - [IMG], [CELLS]: at any state of this unit's call precondition, the layout's image extent covers this image
     (DecodeCallocRt.v dec_img_cover) and the sixteen start-up cells hold (DecodeCallocWrap.v dec_cells_A).
     DecodeCallocWrap.v takes both as facts about one state; the claim quantifies over states, so they are
     stated here as that implication.  Both are start-up facts about .bss / .data that this unit's start-up
     certificate will discharge.
   - [HTP]: the unit's thread pointer is the one measured in image A.
   - [HINST]: the unit's allocator instance is __asan::instance at DEC_A_instance = 0x9d758 (DecodeCallocEntry.v
     HINST: it places the third IMG_CONST cell at 0x9d778).
   - [RT_TRY], [RT_MCS], [RT_GETPC], [RT_UNW], [FILL]: the five runtime-entry contracts of
     lib/A/DecodeCallocRt.v (TryAsanInitFromRtl, GetMallocContextSize, StackTrace::GetCurrentPc,
     BufferedStackTrace::UnwindImpl, the zero fill through __interception::real_memset).
   - [LAWS]: the allocator relation's law record (YG0d.v:496 AR_laws), which the unit's AsanAPI carries.
   - [IMG_CONST]: the three image cells the walk reads as cells of the allocator relation's constant list (the
     third in the symbol record's form `c8 (AInst o_space) (ASp 0)`).
   - [ERRNO_LOW]: errno lies below kLowMemEnd.
   Allocate's own contract is NOT a hypothesis here: it is the antecedent of the claim itself
   (YGCalloc.v acalloc_of_allocateP). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import
YB1v DecodeCallocTbl DecodeCalloc DecodeCallocSkel DecodeCallocSeed DecodeCallocRt
DecodeCallocWrap DecodeCallocEntry.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YN2j YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import CallocImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import YGCallocModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YGAlloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The `ret` the epilogue ends at (0x524d0, word 0x00008067). *)
Definition DEC_A_wrap_ret_insn : Z := 0x5722c.

(* ================================================================================================================
   PART 1.  The wrapper's walk again, with the eight saved cells and x23 .. x27 in its post. *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (S : astate).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
Hypothesis IMG : dec_img_cover ly.
Hypothesis HTP : as_tp B = DEC_A_TP.
Hypothesis RT_TRY : decode_try_init_spec_A.
Hypothesis RT_MCS : decode_mcs_spec_A.
Hypothesis RT_GETPC : decode_getpc_spec_A.
Hypothesis RT_UNW : decode_unwind_spec_A.
Hypothesis CELLS : dec_cells_A ly W mem0.

Local Abbreviation sp0 := (spZ regs0).
Local Abbreviation DEC_tr := (call_trace ly DEC_A_calloc_ra0 regs0 ch).

(* [DecodeCallocWrap.at_C2] with the five registers the wrapper never touches and the eight cells its prologue
   wrote: what the epilogue reloads, and what the leaf's [aregs_preserved] needs. *)
Definition at_C2X (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
c' = cfg_at tfibsegs DEC_A_asan_calloc regs mem (with_vm_backing (m_vm_lazy md0) mat md0) /\
YK11.getr regs 1 = w64 DEC_A_calloc_ret /\
YK11.getr regs 2 = w64 (sp0 - ICPT_FRAME) /\
YK11.getr regs 3 = YK11.getr regs0 3 /\
YK11.getr regs 4 = YK11.getr regs0 4 /\
YK11.getr regs 8 = YK11.getr regs0 2 /\
YK11.getr regs 10 = YK11.getr regs0 10 /\
YK11.getr regs 11 = YK11.getr regs0 11 /\
YK11.getr regs 12 = w64 (sp0 - ICPT_TRACE) /\
YK11.getr regs 23 = YK11.getr regs0 23 /\
YK11.getr regs 24 = YK11.getr regs0 24 /\
YK11.getr regs 25 = YK11.getr regs0 25 /\
YK11.getr regs 26 = YK11.getr regs0 26 /\
YK11.getr regs 27 = YK11.getr regs0 27 /\
(forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - ICPT_TRACE + 8) 8 (Z.of_nat (length DEC_tr)) /\
(forall i, (i < length DEC_tr)%nat ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - ICPT_BUF + 8 * Z.of_nat i) 8 (nth i DEC_tr 0)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 8) 8 (bv_unsigned (YK11.getr regs0 1)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 16) 8 (bv_unsigned (YK11.getr regs0 8)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 24) 8 (bv_unsigned (YK11.getr regs0 9)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 32) 8 (bv_unsigned (YK11.getr regs0 18)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 40) 8 (bv_unsigned (YK11.getr regs0 19)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 48) 8 (bv_unsigned (YK11.getr regs0 20)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 56) 8 (bv_unsigned (YK11.getr regs0 21)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - 64) 8 (bv_unsigned (YK11.getr regs0 22)).

Lemma walk_C2X : SRr tfibsegs W (cfg_at tfibsegs DEC_A_wrap_calloc regs0 mem0 md0) at_C2X.
Proof.
pose proof decode_wx as Hwx.
pose proof (sp0_facts B W ly S regs0 mem0 md0 ch PRE) as (Flo & Fbot & Fhi & Fal & Fhmb & Fhme & LY).
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hgp0 & Htp0 & (Hra4096 & Hchain) & _).
pose proof (lo_top ly LY) as (Ttop1 & Ttop2 & _).
assert (HIT : IMG_TOP = 0x602000) by (apply IMG_TOP_val).
assert (SPlo : 17594333511680 <= sp0) by (cbv [ASTACK kHighMemBeg] in Flo, Fhmb |- *; lia).
assert (SPhi : sp0 <= 140737488355328) by (cbv [kHighMemEnd] in Fhi, Fhme |- *; lia).
assert (E2 : bv_unsigned (ew (E0 regs0) 2) = sp0)
by (rewrite (E0_reg regs0 2 2%bv eq_refl); reflexivity).
eapply SRr_bind; [exact (walk_C1 B W ly S regs0 mem0 md0 ch PRE)|].
intros W1 c1 _ (-> & ms & mat & -> & HS & MEQ & PRES).
(* The two image cells the walk reads through, as regions of the symbolic state. *)
pose proof (cells_at B W ly S regs0 mem0 md0 ch PRE CELLS (ms_mem ms) MEQ) as CUR.
unfold dec_cells_A in CUR. cbv zeta in CUR.
destruct CUR as (XIN & XMCS & XTKI & XTK & XTSDP & XTSD & XC152 & XT40 & XT8 & XT16 & XTU & XTUP
& XGPS & XPS & XGCF & XCF).
apply (st_ok_add_region tfibsegs _ _ _ (lit1 DEC_A_cf_fast 1)) in HS;
[ | vm_compute; reflexivity
| unfold region_ok, lit1;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
cbv zeta; split; [vm_compute; discriminate|]; split; [vm_compute; discriminate|];
split; [intros o Ho; lia|]; apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val tfibsegs _ _ 0 DEC_A_cf_fast 1%N (SLit 1) 1);
[reflexivity | cbn; lia | cbn; lia | exact XCF]
| cbn [ss_mem SS_C1 REG_C1]; apply Forall_cons; [|apply Forall_nil];
unfold extent_disjoint, lit1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E2;
left; cbv [DEC_A_cf_fast DEC_A_common_flags CF_FAST_UNWIND_ON_MALLOC ASTACK]; lia ].
apply (st_ok_add_region tfibsegs _ _ _ (lit8 DEC_A_got_common_flags DEC_A_common_flags)) in HS;
[ | vm_compute; reflexivity
| unfold region_ok, lit8;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
cbv zeta; split; [vm_compute; discriminate|]; split; [vm_compute; discriminate|];
split; [intros o Ho; lia|]; apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val tfibsegs _ _ 0 DEC_A_got_common_flags 8%N (SLit DEC_A_common_flags) DEC_A_common_flags);
[reflexivity | cbn; cbv [DEC_A_common_flags]; lia | cbn; lia | exact XGCF]
| cbn [ss_mem SS_C1 REG_C1]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
unfold extent_disjoint, lit8, lit1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
[ left; cbv [DEC_A_got_common_flags DEC_A_cf_fast DEC_A_common_flags CF_FAST_UNWIND_ON_MALLOC]; lia
| rewrite E2; left; cbv [DEC_A_got_common_flags DEC_A_common_flags ASTACK]; lia ] ].
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with SS_C1X in HS by (vm_compute; reflexivity) end.
(* ---- 0x5239c `jal 0x590ac`: TryAsanInitFromRtl. ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_TryAsanInitFromRtl.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
assert (MEQ0 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> ms_mem ms0 x = mem0 x).
{ intros x Hx. rewrite (HF x); [apply MEQ, Hx|]. intros Hin. apply Hx.
pose proof (wrange_window_lo regs0 (E0 regs0) (ss_mem SS_C1X) (bv_unsigned x) (- ASTACK) E2
ltac:(vm_compute; reflexivity) Hin) as HW. lia. }
assert (PRES0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Ha. eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2; cbv [ASTACK] in Ha |- *; lia
| rewrite HIT; cbv [ASTACK] in Ha |- *; lia]. }
clear HF HFr.
pose proof (cells_at B W ly S regs0 mem0 md0 ch PRE CELLS (ms_mem ms0) MEQ0) as CUR0.
unfold dec_cells_A in CUR0. cbv zeta in CUR0.
destruct CUR0 as (YIN & YMCS & YTKI & YTK & YTSDP & YTSD & YC152 & YT40 & YT8 & YT16 & YTU & YTUP
& YGPS & YPS & YGCF & YCF).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape.
cbn [ss_pc] in Hshape. rewrite Hshape.
eapply SRr_bind.
{ eapply RT_TRY.
- rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
- rewrite R2, unsigned_lit_small by lia.
replace (sp0 + -2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Fal.
- rewrite R2, unsigned_lit_small by lia. rewrite HIT. cbv [TAI_STK]. lia.
- intros a Ha. rewrite R2, unsigned_lit_small in Ha by lia. apply PRES0. cbv [TAI_STK ASTACK] in *. lia.
- exact YIN. }
intros W2 c2 _ (-> & regs1 & mem1 & mat1 & -> & HP & Ha0 & Hfr & Hpr). srr_norm_model.
(* The state after the call: the callee wrote only [sp - 16, sp), so the frame above it is kept. *)
assert (HFR : forall x : word, ~ (sp0 - 2160 <= bv_unsigned x < sp0 - 2144) -> mem1 x = ms_mem ms0 x).
{ intros x Hx. apply Hfr. rewrite R2, unsigned_lit_small by lia. cbv [TAI_STK]. lia. }
assert (MEQ1 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = mem0 x).
{ intros x Hx. rewrite HFR by (cbv [ASTACK] in Hx; lia). apply MEQ0, Hx. }
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a)
by (intros a Ha; apply Hpr, PRES0, Ha).
rewrite R1.
dcall3 HS 32%nat regs1 (mrestrict (w_H W) mem1) HP (-2144) HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
(eapply (kept_of_frame W regs0 _ _ _ (fun a => sp0 - 2160 <= a < sp0 - 2144)); [exact HFR | exact Hpr | |]);
intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha |- *;
rewrite ?E2 in Ha; rewrite ?HIT; split; lia. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
(* a0 = 1: the runtime is initialised, so the branch at 0x523a0 is not taken. *)
apply (st_ok_pin_reg _ _ _ 10%bv (SLit 1)) in HS;
[ | intros Hc; discriminate | cbn [sv_denot ms_regs restrict mkst]; rewrite Ha0; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
(* ---- 0x523a0 .. 0x523c4: the branch (not taken), the stack object's three stores, and the first
   `jal 0x59e34` (GetMallocContextSize). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_GetMallocContextSize.
rreg HS (1%bv : bv 5) R1b.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ2 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ1, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- apply (apresent_same' (w_H W) mem1 _ a); [|apply PRES1; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (cells_at B W ly S regs0 mem0 md0 ch PRE CELLS _ MEQ2) as CUR1.
unfold dec_cells_A in CUR1. cbv zeta in CUR1.
destruct CUR1 as (ZIN & ZMCS & ZTKI & ZTK & ZTSDP & ZTSD & ZC152 & ZT40 & ZT8 & ZT16 & ZTU & ZTUP
& ZGPS & ZPS & ZGCF & ZCF).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape2.
cbn [ss_pc] in Hshape2. rewrite Hshape2.
eapply SRr_bind.
{ eapply (RT_MCS _ _ _ _ DEC_A_MCS).
- rewrite R1b. apply ret_ok_even. vm_compute. reflexivity.
- exact ZMCS.
- cbv [DEC_A_MCS]; lia. }
intros W3 c3 _ (-> & regs2 & mem2 & mat2 & -> & HP2 & Ha2 & Hfr2). srr_norm_model.
rewrite R1b.
jafter_call HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply kept_all_same. intros x. unfold mrestrict. rewrite Hfr2. reflexivity. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit DEC_A_MCS)) in HS;
[ | intros Hc; discriminate | cbn [sv_denot ms_regs restrict mkst]; rewrite Ha2; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (MEQ3 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem2 x = mem0 x)
by (intros x Hx; rewrite Hfr2; apply MEQ2, Hx).
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a)
by (intros a Ha; eapply (apresent_same' (w_H W) _ mem2 a);
[rewrite Hfr2; reflexivity | apply PRES2, Ha]).
(* ---- 0x523c8 .. 0x52434: the depth test (2 < 30, so the unwind arm), and `jal 0x72a08`
   (StackTrace::GetCurrentPc). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_GetCurrentPc.
rreg HS (1%bv : bv 5) R1c.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ4 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ3, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES4 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- apply (apresent_same' (w_H W) mem2 _ a); [|apply PRES3; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape3.
cbn [ss_pc] in Hshape3. rewrite Hshape3.
eapply SRr_bind.
{ eapply RT_GETPC. rewrite R1c. apply ret_ok_even. vm_compute. reflexivity. }
intros W4 c4 _ (-> & regs3 & mem3 & mat3 & -> & HP3 & Ha3 & Hfr3). srr_norm_model.
rewrite R1c.
jafter_call HS 64%nat regs3 (mrestrict (w_H W) mem3) HP3 HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply kept_all_same. intros x. unfold mrestrict. rewrite Hfr3. reflexivity. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
(* a0 = 0x52438, the pc the trace records. *)
apply (st_ok_pin_reg _ _ _ 10%bv (SLit DEC_A_calloc_ra0)) in HS;
[ | intros Hc; discriminate
| cbn [sv_denot ms_regs restrict mkst]; rewrite Ha3, R1c; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (MEQ5 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem3 x = mem0 x)
by (intros x Hx; rewrite Hfr3; apply MEQ4, Hx).
assert (PRES5 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem3 a)
by (intros a Ha; eapply (apresent_same' (w_H W) _ mem3 a);
[rewrite Hfr3; reflexivity | apply PRES4, Ha]).
(* ---- 0x52438 .. 0x52448: the flags pointer, the fast-unwind byte, and the second
   `jal 0x59e34` (GetMallocContextSize). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_GetMallocContextSize.
rreg HS (1%bv : bv 5) R1d.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ6 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ5, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES6 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- apply (apresent_same' (w_H W) mem3 _ a); [|apply PRES5; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (cells_at B W ly S regs0 mem0 md0 ch PRE CELLS _ MEQ6) as CUR3.
unfold dec_cells_A in CUR3. cbv zeta in CUR3.
destruct CUR3 as (VIN & VMCS & VTKI & VTK & VTSDP & VTSD & VC152 & VT40 & VT8 & VT16 & VTU & VTUP
& VGPS & VPS & VGCF & VCF).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape4.
cbn [ss_pc] in Hshape4. rewrite Hshape4.
eapply SRr_bind.
{ eapply (RT_MCS _ _ _ _ DEC_A_MCS).
- rewrite R1d. apply ret_ok_even. vm_compute. reflexivity.
- exact VMCS.
- cbv [DEC_A_MCS]; lia. }
intros W5 c5 _ (-> & regs4 & mem4 & mat4 & -> & HP4 & Ha4 & Hfr4). srr_norm_model.
rewrite R1d.
jafter_call HS 80%nat regs4 (mrestrict (w_H W) mem4) HP4 HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply kept_all_same. intros x. unfold mrestrict. rewrite Hfr4. reflexivity. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit DEC_A_MCS)) in HS;
[ | intros Hc; discriminate | cbn [sv_denot ms_regs restrict mkst]; rewrite Ha4; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (MEQ7 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem4 x = mem0 x)
by (intros x Hx; rewrite Hfr4; apply MEQ6, Hx).
assert (PRES7 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem4 a)
by (intros a Ha; eapply (apresent_same' (w_H W) _ mem4 a);
[rewrite Hfr4; reflexivity | apply PRES6, Ha]).
(* ---- 0x5244c .. 0x52490: the arguments of the unwinder (this, pc0, the entry sp as the frame pointer, 0,
   the fast-unwind byte, 30), and `jal 0x59e44` (BufferedStackTrace::UnwindImpl). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_UnwindImpl.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ8 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ7, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES8 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- eapply (apresent_same' (w_H W) mem4 _ a); [|apply PRES7; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (cells_at B W ly S regs0 mem0 md0 ch PRE CELLS _ MEQ8) as CUR4.
unfold dec_cells_A in CUR4. cbv zeta in CUR4.
destruct CUR4 as (UIN & UMCS & UTKI & UTK & UTSDP & UTSD & UC152 & UT40 & UT8 & UT16 & UTU & UTUP
& UGPS & UPS & UGCF & UCF).
(* The object's two cells, and the caller's saved ra and frame pointer, read off the state's chunks. *)
assert (E1 : ew (E0 regs0) 1 = YK11.getr regs0 1) by (apply (E0_reg regs0 1 1%bv); reflexivity).
assert (E8 : ew (E0 regs0) 8 = YK11.getr regs0 8) by (apply (E0_reg regs0 8 8%bv); reflexivity).
pose proof (C2_obj_ok B W ly S regs0 mem0 md0 ch PRE) as (OA1 & OA2 & OA3 & OA4 & OA5 & OA6).
assert (S8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16 sp0);
[exists 2; reflexivity | apply Z.mod_divide; [lia | exact Fal]]. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 2%nat (-2136) 8%N (SOff 2 (-2120))
(sp0 - ICPT_BUF) (sp0 - ICPT_TRACE) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; cbv [ICPT_TRACE]; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E2; f_equal; cbv [ICPT_BUF]; lia
| cbn; cbv [ICPT_BUF]; lia | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (OBJZ : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX)) (sp0 - ICPT_TRACE + 8) 8 0);
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 1%nat (-2128) 8%N (SLit 0) 0
(sp0 - ICPT_TRACE + 8) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; cbv [ICPT_TRACE]; lia
| reflexivity | cbn; lia | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (RA0 : rdword (aview tfibsegs (w_H W) (ms_mem msX)) (sp0 - 8) = Some (raZ regs0));
[ apply val_mem_rdword; [apply u64_range|];
eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 10%nat (-8) 8%N (SOff 1 0) (raZ regs0) (sp0 - 8) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E1; unfold raZ; rewrite Z.add_0_r; reflexivity
| unfold raZ; apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (NFP0 : rdword (aview tfibsegs (w_H W) (ms_mem msX)) (sp0 - 16) = Some (s0Z regs0));
[ apply val_mem_rdword; [apply u64_range|];
eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 9%nat (-16) 8%N (SOff 8 0) (s0Z regs0) (sp0 - 16) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E8; unfold s0Z; rewrite Z.add_0_r; reflexivity
| unfold s0Z; apply u64_range | cbn; lia ]
| ] end.
rreg HS (1%bv : bv 5) R1e. rreg HS (2%bv : bv 5) R2e. rewrite E2 in R2e.
rreg HS (4%bv : bv 5) R4e. rreg HS (10%bv : bv 5) R10e. rewrite E2 in R10e.
rreg HS (11%bv : bv 5) R11e. rreg HS (12%bv : bv 5) R12e.
rreg HS (13%bv : bv 5) R13e. rreg HS (14%bv : bv 5) R14e. rreg HS (15%bv : bv 5) R15e.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape5.
cbn [ss_pc] in Hshape5. rewrite Hshape5.
eapply SRr_bind.
{ apply (RT_UNW W ly _ _ _ (sp0 - ICPT_TRACE) DEC_A_calloc_ra0 sp0 (raZ regs0) (s0Z regs0) ch).
- exact LY.
- exact IMG.
- rewrite R10e; f_equal; cbv [ICPT_TRACE]; lia.
- rewrite R11e; reflexivity.
- rewrite R12e, <- E2; symmetry; apply Z_to_bv_bv_unsigned.
- exact R13e.
- exact R14e.
- exact R15e.
- rewrite R4e, (E0_reg regs0 4 4%bv eq_refl), Htp0, HTP; reflexivity.
- rewrite R1e; apply ret_ok_even; vm_compute; reflexivity.
- cbv [DEC_A_calloc_ra0]; lia.
- exact UIN.
- exact UTKI.
- exact UTK.
- exact UTSDP.
- exact UTSD.
- exact UC152.
- exact UT40.
- exact UT8.
- exact UT16.
- exact UTU.
- exact UTUP.
- exact UGPS.
- exact UPS.
- rewrite R2e, unsigned_lit_small by lia;
replace (sp0 + -2144) with (sp0 + (-134) * 16) by lia; rewrite Z_mod_plus_full; exact Fal.
- rewrite R2e, unsigned_lit_small by lia; cbv [UNW_STK ASTACK] in *; lia.
- intros a Ha; rewrite R2e, unsigned_lit_small in Ha by lia; apply PRES8;
cbv [UNW_STK ASTACK] in *; lia.
- exact OA1.
- cbv [ICPT_TRACE ASTACK] in *; lia.
- right; rewrite R2e, unsigned_lit_small by lia; cbv [ICPT_TRACE]; lia.
- intros a Ha; apply PRES8; cbv [ICPT_TRACE BST_SIZE ASTACK] in *; lia.
- cbv [ICPT_TRACE BST_SIZE]; lia.
- rewrite R2e, unsigned_lit_small by lia; lia.
- exact Fbot.
- exact Fhi.
- exact S8.
- exact RA0.
- exact NFP0.
- exact Hra4096.
- unfold frame0_ok in Hchain.
destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hchain].
destruct (bad_next sp0 (ly_top ly) (s0Z regs0)) eqn:Hb; [exact Hchain|].
destruct Hchain as [H16 Hch']. split; [exact H16|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _].
apply Bool.orb_false_iff in Hb as [Hb1 Hb2]. apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
apply Z.ltb_lt in Hf0.
eapply fpchain_ext2; [exact Hch' | lia |].
intros aX vX HaX1 HaX2 HvX. eapply rdword_keep; [|exact HvX].
intros i Hi. apply aview_same'. apply MEQ8.
rewrite unsigned_lit_small by (cbv [kHighMemEnd] in Fhme |- *; lia). cbv [ASTACK]. lia. }
intros W6 c6 _ (-> & regs5 & mem5 & mat5 & -> & HP5 & Hfr5 & Hpr5 & HT1 & HT2 & HT3). srr_norm_model.
(* The unwinder wrote the three fields of the object and its own stack window, and nothing else. *)
assert (HFR5 : forall x : word, ~ (sp0 - 2288 <= bv_unsigned x < sp0 - 64) -> mem5 x = ms_mem ms4 x).
{ intros x Hx. apply Hfr5; cbv [UNW_STK ICPT_TRACE BST_SIZE]; rewrite ?R2e;
rewrite ?unsigned_lit_small by lia; lia. }
assert (OBJ0F : val_mem tfibsegs (mrestrict (w_H W) mem5) (sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF)).
{ eapply val_mem_frameH; [|exact OBJ0]. intros k Hk. apply Hfr5;
cbv [UNW_STK ICPT_TRACE BST_SIZE]; rewrite ?R2e; rewrite ?unsigned_lit_small by lia; lia. }
assert (OBJZF : val_mem tfibsegs (mrestrict (w_H W) mem5) (sp0 - ICPT_TRACE + 8 + 4) 4 0).
{ eapply val_mem_frameH; [|apply val_mem_zero_hi; exact OBJZ]. intros k Hk. apply Hfr5;
cbv [UNW_STK ICPT_TRACE BST_SIZE]; rewrite ?R2e; rewrite ?unsigned_lit_small by lia; lia. }
assert (LENF : val_mem tfibsegs (mrestrict (w_H W) mem5)
(sp0 - ICPT_TRACE + 8) 8 (Z.of_nat (length DEC_tr))).
{ replace (Z.of_nat (length DEC_tr)) with (Z.of_nat (length DEC_tr) + 2 ^ 32 * 0) by lia.
apply val_mem_4_4; [pose proof (C2_tr_len ly regs0 ch); lia | lia | exact HT1 | exact OBJZF]. }
assert (MEQ9 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem5 x = mem0 x).
{ intros x Hx. rewrite HFR5 by (cbv [ASTACK] in Hx; lia). apply MEQ8, Hx. }
assert (PRES9 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem5 a)
by (intros a Ha; apply Hpr5, PRES8, Ha).
rewrite R1e.
dcall3 HS 96%nat regs5 (mrestrict (w_H W) mem5) HP5 (-64) HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
(eapply (kept_of_frame W regs0 _ _ _ (fun a => sp0 - 2288 <= a < sp0 - 64)); [exact HFR5 | exact Hpr5 | |]);
intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha |- *;
rewrite ?ew_havoc_old in Ha by lia; rewrite ?E2 in Ha; rewrite ?HIT; split; lia. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
(* ---- 0x52494 .. 0x524a4: the three arguments of asan_calloc, and `jal 0x31bd4`. ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_asan_calloc.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (FRF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> mB x = mem5 x) end.
{ intros x Hx. apply HF. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo regs0 Ex rsx (bv_unsigned x) (-64)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQF : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite FRF by (cbv [ASTACK] in Hx; lia). apply MEQ9, Hx. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRESF : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hlo'|Hhi'].
- eapply (apresent_same' (w_H W) mem5 _ a); [|apply PRES9; lia].
apply FRF. rewrite unsigned_lit_small by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
(* The object's cells at the reached state: the last run stores nothing. *)
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (TR1 : val_mem tfibsegs (mrestrict (w_H W) mB) (sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF));
[ eapply val_mem_frameH; [|exact OBJ0F]; intros k Hk; apply FRF;
rewrite unsigned_lit_small by (cbv [ICPT_TRACE]; lia); cbv [ICPT_TRACE]; lia | ] end.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (TR2 : val_mem tfibsegs (mrestrict (w_H W) mB)
(sp0 - ICPT_TRACE + 8) 8 (Z.of_nat (length DEC_tr)));
[ eapply val_mem_frameH; [|exact LENF]; intros k Hk; apply FRF;
rewrite unsigned_lit_small by (cbv [ICPT_TRACE]; lia); cbv [ICPT_TRACE]; lia | ] end.
pose proof (C2_tr_len ly regs0 ch) as TRLEN.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (TR3 : forall i, (i < length DEC_tr)%nat ->
val_mem tfibsegs (mrestrict (w_H W) mB) (sp0 - ICPT_BUF + 8 * Z.of_nat i) 8 (nth i DEC_tr 0));
[ intros i Hi; eapply val_mem_frameH;
[ intros k Hk; apply FRF;
rewrite unsigned_lit_small by (cbv [ICPT_BUF]; lia); cbv [ICPT_BUF]; lia
| eapply val_mem_addr; [exact (HT2 i Hi) | cbv [ICPT_TRACE ICPT_BUF]; lia] ] | ] end.
clear HF HFr.
(* The eight cells the prologue wrote, read off the frame region the callee kept (the chunks of
   DecodeCallocSkel.REG_C1, trimmed to [entry sp - 64, entry sp)). *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV64 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 64) 8 (bv_unsigned (YK11.getr regs0 22)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 0%nat (-64) 8%N (SOff 22 0)
(bv_unsigned (YK11.getr regs0 22)) (sp0 - 64) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite (E0_reg regs0 22 22%bv eq_refl);
rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV56 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 56) 8 (bv_unsigned (YK11.getr regs0 21)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 1%nat (-56) 8%N (SOff 21 0)
(bv_unsigned (YK11.getr regs0 21)) (sp0 - 56) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite (E0_reg regs0 21 21%bv eq_refl);
rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV48 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 48) 8 (bv_unsigned (YK11.getr regs0 20)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 2%nat (-48) 8%N (SOff 20 0)
(bv_unsigned (YK11.getr regs0 20)) (sp0 - 48) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite (E0_reg regs0 20 20%bv eq_refl);
rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV40 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 40) 8 (bv_unsigned (YK11.getr regs0 19)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 3%nat (-40) 8%N (SOff 19 0)
(bv_unsigned (YK11.getr regs0 19)) (sp0 - 40) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite (E0_reg regs0 19 19%bv eq_refl);
rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV32 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 32) 8 (bv_unsigned (YK11.getr regs0 18)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 4%nat (-32) 8%N (SOff 18 0)
(bv_unsigned (YK11.getr regs0 18)) (sp0 - 32) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite (E0_reg regs0 18 18%bv eq_refl);
rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV24 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 24) 8 (bv_unsigned (YK11.getr regs0 9)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 5%nat (-24) 8%N (SOff 9 0)
(bv_unsigned (YK11.getr regs0 9)) (sp0 - 24) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite (E0_reg regs0 9 9%bv eq_refl);
rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV16 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 16) 8 (bv_unsigned (YK11.getr regs0 8)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 6%nat (-16) 8%N (SOff 8 0)
(bv_unsigned (YK11.getr regs0 8)) (sp0 - 16) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E8; rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SV8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - 8) 8 (bv_unsigned (YK11.getr regs0 1)));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 7%nat (-8) 8%N (SOff 1 0)
(bv_unsigned (YK11.getr regs0 1)) (sp0 - 8) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E1; rewrite Z.add_0_r; reflexivity
| apply u64_range | cbn; lia ]
| ] end.
(* The registers at the call, and the close. *)
rreg HS (1%bv : bv 5) R1f. rreg HS (2%bv : bv 5) R2f. rewrite E2 in R2f.
rreg HS (3%bv : bv 5) R3f. rreg HS (4%bv : bv 5) R4f. rreg HS (8%bv : bv 5) R8f.
rreg HS (10%bv : bv 5) R10f. rreg HS (11%bv : bv 5) R11f.
rreg HS (12%bv : bv 5) R12f. rewrite E2 in R12f.
rreg HS (23%bv : bv 5) R23f. rreg HS (24%bv : bv 5) R24f. rreg HS (25%bv : bv 5) R25f.
rreg HS (26%bv : bv 5) R26f. rreg HS (27%bv : bv 5) R27f.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as HshapeF.
cbn [ss_pc] in HshapeF.
apply SRr_ret. rewrite HshapeF. unfold at_C2X. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at; reflexivity|].
split; [rewrite R1f; reflexivity|].
split; [rewrite R2f; f_equal; cbv [ICPT_FRAME]; lia|].
split; [rewrite R3f; apply (E0_reg regs0 3 3%bv); reflexivity|].
split; [rewrite R4f; apply (E0_reg regs0 4 4%bv); reflexivity|].
split; [rewrite R8f; apply (E0_reg regs0 2 2%bv); reflexivity|].
split; [rewrite R10f; apply (E0_reg regs0 10 10%bv); reflexivity|].
split; [rewrite R11f; apply (E0_reg regs0 11 11%bv); reflexivity|].
split; [rewrite R12f; f_equal; cbv [ICPT_TRACE]; lia|].
split; [rewrite R23f; apply (E0_reg regs0 23 23%bv); reflexivity|].
split; [rewrite R24f; apply (E0_reg regs0 24 24%bv); reflexivity|].
split; [rewrite R25f; apply (E0_reg regs0 25 25%bv); reflexivity|].
split; [rewrite R26f; apply (E0_reg regs0 26 26%bv); reflexivity|].
split; [rewrite R27f; apply (E0_reg regs0 27 27%bv); reflexivity|].
split; [exact MEQF|]. split; [exact PRESF|].
split; [exact TR1|]. split; [exact TR2|]. split; [exact TR3|].
split; [exact SV8|]. split; [exact SV16|]. split; [exact SV24|]. split; [exact SV32|].
split; [exact SV40|]. split; [exact SV48|]. split; [exact SV56|]. exact SV64.
Qed.
End w.

(* ================================================================================================================
   PART 2.  The epilogue's seed, and the composition. *)

(* The epilogue's frame, as a read-only region over the entry sp of asan_calloc's caller: sp at 0x524a8 is
   entry sp - 2144, so the eight saved cells stand at sp + 2080 .. sp + 2136.  Atom 32 is the caller's ra and
   atoms 33 .. 39 are its s0 .. s6, the values the prologue stored. *)
Definition R_EPI : YP09.region := YP09.mkRegion (Some 2%nat) 2080 2144 0 0
[YP09.mkChunk 2080 (CVal 8 (SOff 39 0)); YP09.mkChunk 2088 (CVal 8 (SOff 38 0));
YP09.mkChunk 2096 (CVal 8 (SOff 37 0)); YP09.mkChunk 2104 (CVal 8 (SOff 36 0));
YP09.mkChunk 2112 (CVal 8 (SOff 35 0)); YP09.mkChunk 2120 (CVal 8 (SOff 34 0));
YP09.mkChunk 2128 (CVal 8 (SOff 33 0)); YP09.mkChunk 2136 (CVal 8 (SOff 32 0))].
Definition FG_P : facts := mkFacts [(2%nat, mkAF kHighMemBeg (kHighMemEnd - ICPT_FRAME) 4)] [] [].
Definition SS_P : sstate := mkSS DEC_A_wrap_after_call sr_atoms [R_EPI] None FG_P.
Definition E_P (regs0 regsL : bvmap 5 word) : env :=
Ereg regsL [YK11.getr regs0 1; YK11.getr regs0 8; YK11.getr regs0 9; YK11.getr regs0 18;
YK11.getr regs0 19; YK11.getr regs0 20; YK11.getr regs0 21; YK11.getr regs0 22].

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section q.
Variables (regs0 regsL : bvmap 5 word).
Lemma EP_lo (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew (E_P regs0 regsL) k = YK11.getr regsL r.
Proof. intros Hk. exact (ew_Ereg_nat regsL _ k r Hk). Qed.
Lemma EP_32 : ew (E_P regs0 regsL) 32 = YK11.getr regs0 1. Proof. reflexivity. Qed.
Lemma EP_33 : ew (E_P regs0 regsL) 33 = YK11.getr regs0 8. Proof. reflexivity. Qed.
Lemma EP_34 : ew (E_P regs0 regsL) 34 = YK11.getr regs0 9. Proof. reflexivity. Qed.
Lemma EP_35 : ew (E_P regs0 regsL) 35 = YK11.getr regs0 18. Proof. reflexivity. Qed.
Lemma EP_36 : ew (E_P regs0 regsL) 36 = YK11.getr regs0 19. Proof. reflexivity. Qed.
Lemma EP_37 : ew (E_P regs0 regsL) 37 = YK11.getr regs0 20. Proof. reflexivity. Qed.
Lemma EP_38 : ew (E_P regs0 regsL) 38 = YK11.getr regs0 21. Proof. reflexivity. Qed.
Lemma EP_39 : ew (E_P regs0 regsL) 39 = YK11.getr regs0 22. Proof. reflexivity. Qed.

Lemma R_EPI_ok : forall (m : word -> option byte),
let b := bv_unsigned (YK11.getr regsL 2) in
b + 2144 <= 2 ^ 64 ->
val_mem tfibsegs m (b + 2136) 8 (bv_unsigned (YK11.getr regs0 1)) ->
val_mem tfibsegs m (b + 2128) 8 (bv_unsigned (YK11.getr regs0 8)) ->
val_mem tfibsegs m (b + 2120) 8 (bv_unsigned (YK11.getr regs0 9)) ->
val_mem tfibsegs m (b + 2112) 8 (bv_unsigned (YK11.getr regs0 18)) ->
val_mem tfibsegs m (b + 2104) 8 (bv_unsigned (YK11.getr regs0 19)) ->
val_mem tfibsegs m (b + 2096) 8 (bv_unsigned (YK11.getr regs0 20)) ->
val_mem tfibsegs m (b + 2088) 8 (bv_unsigned (YK11.getr regs0 21)) ->
val_mem tfibsegs m (b + 2080) 8 (bv_unsigned (YK11.getr regs0 22)) ->
YP09.region_ok tfibsegs (E_P regs0 regsL) m R_EPI.
Proof.
intros m b Hb V36 V28 V20 V12 V04 V96 V88 V80.
assert (E2 : bv_unsigned (ew (E_P regs0 regsL) 2) = b) by (rewrite (EP_lo 2 2%bv eq_refl); reflexivity).
pose proof (u64_range (YK11.getr regsL 2)) as Hr.
unfold YP09.region_ok, R_EPI.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [fold b in Hr; lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (CK : forall off (k : nat) (w : word), ew (E_P regs0 regsL) k = w ->
val_mem tfibsegs m (b + off) 8 (bv_unsigned w) ->
YP09.chunk_ok tfibsegs (E_P regs0 regsL) m b (YP09.mkChunk off (CVal 8 (SOff k 0)))).
{ intros off k w Hk Hv.
apply (chunk_ok_val tfibsegs _ _ b off 8 (SOff k 0) (bv_unsigned w)).
- rewrite denot_off0, Hk. symmetry. apply Z_to_bv_bv_unsigned.
- apply u64_range.
- lia.
- exact Hv. }
constructor; [exact (CK 2080 39%nat _ EP_39 V80)|].
constructor; [exact (CK 2088 38%nat _ EP_38 V88)|].
constructor; [exact (CK 2096 37%nat _ EP_37 V96)|].
constructor; [exact (CK 2104 36%nat _ EP_36 V04)|].
constructor; [exact (CK 2112 35%nat _ EP_35 V12)|].
constructor; [exact (CK 2120 34%nat _ EP_34 V20)|].
constructor; [exact (CK 2128 33%nat _ EP_33 V28)|].
constructor; [exact (CK 2136 32%nat _ EP_32 V36)|].
constructor.
Qed.
End q.
End p.

(* ----------------------------------------------------------------------------------------------------------
   The claim. *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* The layout's image extent covers this unit's image, at any state of the unit's call precondition. *)
Hypothesis IMG : forall ly S W regs mem md ch,
acall_pre tfibsegs B ly S W regs mem md ch -> dec_img_cover ly.
(* The unit's thread pointer is the one measured in image A. *)
Hypothesis HTP : as_tp B = DEC_A_TP.
(* The unit's allocator instance is __asan::instance, measured in image A. *)
Hypothesis HINST : as_inst B = DEC_A_instance.
(* The five runtime-entry contracts of lib/A/DecodeCallocRt.v. *)
Hypothesis RT_TRY : decode_try_init_spec_A.
Hypothesis RT_MCS : decode_mcs_spec_A.
Hypothesis RT_GETPC : decode_getpc_spec_A.
Hypothesis RT_UNW : decode_unwind_spec_A.
Hypothesis FILL : decode_zero_fill_spec_A B.
(* The sixteen start-up cells, at any state of the unit's call precondition. *)
Hypothesis CELLS : forall ly S W regs mem md ch,
acall_pre tfibsegs B ly S W regs mem md ch -> dec_cells_A ly W mem.
(* The allocator relation's law record. *)
Hypothesis LAWS : AR_laws tfibsegs B.
(* The image's constant cells the walk reads, as cells of the allocator relation's constant list. *)
Hypothesis IMG_CONST : forall ly,
In (z8 (ANum DEC_A_got_real_memset) DEC_A_real_memset) (as_const B ly) /\
In (z8 (ANum DEC_A_real_memset) DEC_A_memset) (as_const B ly) /\
In (c8 (AInst o_space) (ASp 0)) (as_const B ly).
(* errno lies in low memory. *)
Hypothesis ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd.

Local Ltac cs_tac :=
unfold acallee_saved;
match goal with |- context [bv_unsigned ?x] =>
let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Theorem decode_acalloc_of_allocate_A_holds : decode_acalloc_of_allocate_A B.
Proof.
unfold decode_acalloc_of_allocate_A, RtLCallocR.aseg_acalloc_of_allocate.
intros HPRIM ALLOC. unfold RtLCallocR.aseg_acalloc_realizes.
intros ly S W regs0 mem0 md0 nm sz ch PRE HDEPTH H10 H11 Hnm0 Hsz0 Hns Hcmax Hlive Htr.
apply (tr_admit_call (as_universe B) S ly DEC_A_calloc_ra0 regs0 ch) in Htr.
cbv beta.
pose proof decode_wx as Hwx.
pose proof PRE as (HAR & Hreg & Hret0 & Hal0 & Hslo0 & Hbot0 & Hshi0 & Hpres0 & Hgp0 & Htp0 & Hchain & Hqm).
pose proof (sp0_facts B W ly S regs0 mem0 md0 ch PRE) as (Flo & Fbot & Fhi & Fal & Fhmb & Fhme & LY).
pose proof (C2_obj_ok B W ly S regs0 mem0 md0 ch PRE) as (OA1 & OA2 & OA3 & OA4 & OA5 & OA6).
pose proof (C2_tr_len ly regs0 ch) as TRLEN.
pose proof (lo_stk_ceil ly LY) as CEIL. unfold ASAN_CEIL in CEIL.
pose proof (proj1 (@ASAN_CEIL_range rc)) as ACR. unfold ASAN_CEIL in ACR.
pose proof ERRNO_LOW as (EL1 & EL2). unfold kLowMemEnd in EL2.
assert (HIT : IMG_TOP = 0x602000) by (apply IMG_TOP_val).
assert (SPlo : kHighMemBeg + ASTACK <= spZ regs0) by lia.
assert (SPhi : spZ regs0 <= kHighMemEnd) by lia.
(* ---- 1. the wrapper's walk to the entry of asan_calloc. ---- *)
apply (amreal_SRr_pre tfibsegs _ W _ _ (at_C2X W ly regs0 mem0 md0 ch)).
{ exact (walk_C2X B W ly S regs0 mem0 md0 ch PRE (IMG ly S W regs0 mem0 md0 ch PRE) HTP
RT_TRY RT_MCS RT_GETPC RT_UNW (CELLS ly S W regs0 mem0 md0 ch PRE)). }
intros W1 c1 _ (-> & regs & mem & mat & -> & G1 & G2 & G3 & G4 & G8 & G10 & G11 & G12
& G23 & G24 & G25 & G26 & G27 & MEQ & PRESM & T1 & T2 & T3 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V64).
assert (SPW : spZ regs = spZ regs0 - ICPT_FRAME).
{ unfold spZ. rewrite G2. unfold w64. apply unsigned_lit_small.
assert (HB : kHighMemBeg + ASTACK <= spZ regs0 <= kHighMemEnd) by (split; [exact SPlo | exact SPhi]).
cbv [ICPT_FRAME ASTACK kHighMemBeg kHighMemEnd] in HB |- *. unfold spZ in HB. lia. }
(* ---- 2. the premises of asan_calloc's walk. ---- *)
assert (HARm : AR tfibsegs B ly S W mem (with_vm_backing (m_vm_lazy md0) mat md0)).
{ apply (AR_frame_wvb B LAWS ly S W mem0 mem md0 mat (spZ regs0 - ASTACK) (spZ regs0) HAR).
- cbv [ASTACK kHighMemBeg] in *; lia.
- cbv [kHighMemEnd] in *; lia.
- exact MEQ.
- intros a Ha. split; [lia|]. split; [apply Hpres0; lia | apply PRESM; lia]. }
assert (HEP : entry_pre B ly S W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) nm sz
(spZ regs0 - ICPT_TRACE) (spZ regs0 - ICPT_BUF) (call_trace ly DEC_A_calloc_ra0 regs0 ch)).
{ unfold entry_pre.
split; [exact HARm|]. split; [exact Hreg|]. split; [exact Hqm|].
split; [rewrite G1; exact ret_ok_wrapper|].
split; [rewrite SPW; replace (spZ regs0 - ICPT_FRAME) with (spZ regs0 + (-134) * 16)
by (cbv [ICPT_FRAME]; lia); rewrite Z_mod_plus_full; exact Fal|].
split; [rewrite SPW; cbv [ENTRY_STK ENTRY_FRAME YGAlloc.AFSTACK_G ICPT_FRAME ASTACK] in *; lia|].
split; [rewrite SPW; cbv [ENTRY_FRAME ICPT_FRAME DEC_CALLOC_DEPTH] in *; lia|].
split; [rewrite SPW; cbv [ICPT_FRAME]; lia|].
split; [intros a Ha; rewrite SPW in Ha; apply PRESM;
cbv [ENTRY_STK ENTRY_FRAME YGAlloc.AFSTACK_G ICPT_FRAME ASTACK] in *; lia|].
split; [rewrite G3; exact Hgp0|]. split; [rewrite G4; exact Htp0|].
split; [rewrite G10; exact H10|]. split; [rewrite G11; exact H11|]. split; [exact G12|].
split; [rewrite SPW; cbv [ICPT_FRAME ICPT_TRACE]; lia|].
split; [exact OA4|]. split; [exact OA1|].
split; [rewrite SPW; cbv [ICPT_FRAME ICPT_BUF]; lia|].
split; [exact OA6|]. split; [exact OA2|].
split; [exact TRLEN|]. split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
split; [exact Htr|]. split; [exact Hnm0|]. split; [exact Hsz0|]. split; [exact Hns|].
split; [cbv [PRIM_MAX DEC_CALLOC_MAX] in *; lia | exact Hlive]. }
(* ---- 3. asan_calloc's walk over Allocate, and the epilogue on each of its leaves. ---- *)
pose proof (entry_walk B ALLOC FILL LAWS IMG_CONST HINST ERRNO_LOW ly S W regs mem
(with_vm_backing (m_vm_lazy md0) mat md0) nm sz (spZ regs0 - ICPT_TRACE) (spZ regs0 - ICPT_BUF)
(call_trace ly DEC_A_calloc_ra0 regs0 ch) HEP) as HAM.
apply (amreal_post_SRr tfibsegs _ W _ _ _ HAM).
intros r W2 c2 HLEAF.
destruct HLEAF as (ly' & regsL & memL & mdL & Hc2 & HARL & Hly & Hwle & HPR & Hio & Hfr & HpresL
& Ha0 & Hqt & Hpath & Hnn & Hzero).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (RAW : raZ regs = DEC_A_wrap_after_call).
{ unfold raZ. rewrite G1. unfold w64. apply unsigned_lit_small.
cbv [DEC_A_calloc_ret DEC_A_wrap_after_call]; lia. }
rewrite RAW in Hc2. subst c2.
(* The registers the Allocate leaf kept. *)
assert (PRL : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> YK11.getr regsL rr = YK11.getr regs rr).
{ intros rr Hrr. rewrite <- (getr_lit regsL _ rr eq_refl), <- (getr_lit regs _ rr eq_refl).
exact (HPR _ Hrr). }
assert (L2 : YK11.getr regsL 2 = w64 (spZ regs0 - ICPT_FRAME)) by (rewrite PRL by cs_tac; exact G2).
assert (L3 : YK11.getr regsL 3 = YK11.getr regs0 3) by (rewrite PRL by cs_tac; exact G3).
assert (L4 : YK11.getr regsL 4 = YK11.getr regs0 4) by (rewrite PRL by cs_tac; exact G4).
assert (L23 : YK11.getr regsL 23 = YK11.getr regs0 23) by (rewrite PRL by cs_tac; exact G23).
assert (L24 : YK11.getr regsL 24 = YK11.getr regs0 24) by (rewrite PRL by cs_tac; exact G24).
assert (L25 : YK11.getr regsL 25 = YK11.getr regs0 25) by (rewrite PRL by cs_tac; exact G25).
assert (L26 : YK11.getr regsL 26 = YK11.getr regs0 26) by (rewrite PRL by cs_tac; exact G26).
assert (L27 : YK11.getr regsL 27 = YK11.getr regs0 27) by (rewrite PRL by cs_tac; exact G27).
assert (LB : bv_unsigned (YK11.getr regsL 2) = spZ regs0 - ICPT_FRAME).
{ rewrite L2. unfold w64. apply unsigned_lit_small.
cbv [ICPT_FRAME ASTACK kHighMemBeg kHighMemEnd] in *; lia. }
(* The model's block, and the addresses it occupies: below alloc_ceiling, hence below the stack. *)
destruct (calloc_model_of_AR tfibsegs B ly S W mem0 md0 HAR) as [HU HWf].
destruct (calloc_block_table (as_universe B) S nm sz (call_trace ly DEC_A_calloc_ra0 regs0 ch) r
HU HWf Hreg Hnm0 Hsz0 Hns Hlive Htr Hpath) as (Hbl & _ & _).
destruct (calloc_addr_side tfibsegs B ly ly' S (snd r) W mem0 md0 W2 memL mdL (fst r) (nm * sz)
LAWS HAR Hly HARL Hbl) as (Eab & A4096).
assert (HIn : In (sptr_addr B ly' (fst r), nm * sz) (ablocks B ly' (snd r)))
by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly' (snd r) W2 memL mdL _ (nm * sz) HARL HIn)
as (_ & _ & Bceil & _ & _ & _ & _).
(* Outside asan_calloc's own scratch window the stack bytes it was called with are unchanged. *)
assert (NOWN : forall a, spZ regs0 - ASTACK <= a < spZ regs0 ->
~ aowned B ly S a /\ ~ aowned B ly' (snd r) a).
{ intros a Ha. split.
- apply (al_stack _ _ LAWS ly S W mem0 md0 a HAR). lia.
- apply (al_stack _ _ LAWS ly' (snd r) W2 memL mdL a HARL). rewrite Eslo, Eshi. lia. }
assert (NBLK : forall a, spZ regs0 - ASTACK <= a < spZ regs0 ->
~ (fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size (nm * sz))).
{ intros a Ha [_ Hb]. cbv [ASTACK] in *. lia. }
assert (NSCR : forall a, spZ regs0 - ASTACK <= a < spZ regs0 ->
~ (spZ regs0 - 6288 <= a < spZ regs0 - 2144) -> ~ ascratch B ENTRY_STK regs a).
{ intros a Ha Hout [Hs|He].
- rewrite SPW in Hs. cbv [ENTRY_STK ENTRY_FRAME YGAlloc.AFSTACK_G ICPT_FRAME] in Hs. lia.
- cbv [ASTACK kHighMemBeg] in *. lia. }
assert (AVW : forall a, spZ regs0 - ASTACK <= a < spZ regs0 ->
~ (spZ regs0 - 6288 <= a < spZ regs0 - 2144) ->
aview tfibsegs (w_H W2) memL a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hout. apply Hfr.
- cbv [ASTACK kHighMemBeg kHighMemEnd] in *; lia.
- apply (NOWN a Ha).
- apply (NOWN a Ha).
- apply (NSCR a Ha Hout).
- apply (NBLK a Ha). }
assert (CELLP : forall d v, 8 <= d <= 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs0 - d) 8 v ->
val_mem tfibsegs (mrestrict (w_H W2) memL) (spZ regs0 - d) 8 v).
{ intros d v Hd Hv. apply (val_mem_of_aview (w_H W) (w_H W2) mem memL); [|exact Hv].
intros k Hk. apply AVW; cbv [ASTACK] in *; lia. }
assert (PRESL : forall a, spZ regs0 - ASTACK <= a < spZ regs0 -> apresent (w_H W2) memL a).
{ intros a Ha. destruct (Z_le_gt_dec (spZ regs0 - 6288) a) as [C1|C1];
[destruct (Z_lt_ge_dec a (spZ regs0 - 2144)) as [C2|C2]|].
- apply HpresL. rewrite SPW. cbv [ENTRY_STK ENTRY_FRAME YGAlloc.AFSTACK_G ICPT_FRAME]. lia.
- apply apresent_of_aview_high; [rewrite HIT; cbv [ASTACK kHighMemBeg kHighMemEnd] in *; lia|].
rewrite (AVW a Ha ltac:(lia)). apply aview_of_apresent. apply PRESM. exact Ha.
- apply apresent_of_aview_high; [rewrite HIT; cbv [ASTACK kHighMemBeg kHighMemEnd] in *; lia|].
rewrite (AVW a Ha ltac:(lia)). apply aview_of_apresent. apply PRESM. exact Ha. }
(* ---- 4. the epilogue's seed and run. ---- *)
assert (HSP : st_ok tfibsegs (E_P regs0 regsL) SS_P
(restrict (w_H W2) (YK11.mkst regsL (w64 DEC_A_wrap_after_call) memL (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_P, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. apply R_EPI_ok; rewrite ?LB.
+ cbv [ICPT_FRAME kHighMemEnd] in *; lia.
+ eapply val_mem_addr; [exact (CELLP 8 _ ltac:(lia) V8) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 16 _ ltac:(lia) V16) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 24 _ ltac:(lia) V24) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 32 _ ltac:(lia) V32) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 40 _ ltac:(lia) V40) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 48 _ ltac:(lia) V48) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 56 _ ltac:(lia) V56) | cbv [ICPT_FRAME]; lia].
+ eapply val_mem_addr; [exact (CELLP 64 _ ltac:(lia) V64) | cbv [ICPT_FRAME]; lia].
- cbn. split; exact I.
- split; [|split; exact I]. unfold FG_P. cbn [f_atoms atoms_ok]. split; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regsL _ 2 2%bv eq_refl), LB.
split; [cbv [ICPT_FRAME ASTACK kHighMemBeg] in *; lia|]. split.
+ change (2 ^ 4) with 16.
replace (spZ regs0 - ICPT_FRAME) with (spZ regs0 + (-134) * 16) by (cbv [ICPT_FRAME]; lia).
rewrite Z_mod_plus_full. exact Fal.
+ cbv [ICPT_FRAME kHighMemEnd] in *; lia. }
unfold cfg_at.
srr_run_to_sh tbl_calloc_A_ok HSP DEC_A_wrap_ret_insn.
repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H end.
repeat match goal with H : frame_of _ ?rs ?m ?m' |- _ =>
apply frame_of_read_only in H; [|vm_compute; reflexivity] end.
match type of HSP with st_ok _ _ _ (restrict _ ?m) =>
assert (MMF : ms_mem m = memL) by congruence; rename m into msF end.
rreg HSP (1%bv : bv 5) F1. rreg HSP (2%bv : bv 5) F2. rreg HSP (3%bv : bv 5) F3.
rreg HSP (4%bv : bv 5) F4. rreg HSP (8%bv : bv 5) F8. rreg HSP (9%bv : bv 5) F9.
rreg HSP (10%bv : bv 5) F10. rreg HSP (18%bv : bv 5) F18. rreg HSP (19%bv : bv 5) F19.
rreg HSP (20%bv : bv 5) F20. rreg HSP (21%bv : bv 5) F21. rreg HSP (22%bv : bv 5) F22.
rreg HSP (23%bv : bv 5) F23. rreg HSP (24%bv : bv 5) F24. rreg HSP (25%bv : bv 5) F25.
rreg HSP (26%bv : bv 5) F26. rreg HSP (27%bv : bv 5) F27.
(* The registers at the `ret`: sp is the caller's entry sp again, ra and s0 .. s6 are the saved values,
   s7 .. s11, gp and tp were never touched, and a0 is the block. *)
assert (K1 : YK11.getr (ms_regs msF) 1 = YK11.getr regs0 1)
by (rewrite F1; apply (EP_32 regs0 regsL)).
assert (K2 : YK11.getr (ms_regs msF) 2 = YK11.getr regs0 2).
{ rewrite F2, (EP_lo regs0 regsL 2 2%bv eq_refl), LB.
replace (spZ regs0 - ICPT_FRAME + 2144) with (spZ regs0) by (cbv [ICPT_FRAME]; lia).
unfold spZ. apply Z_to_bv_bv_unsigned. }
assert (K3 : YK11.getr (ms_regs msF) 3 = YK11.getr regs0 3)
by (rewrite F3, (EP_lo regs0 regsL 3 3%bv eq_refl); exact L3).
assert (K4 : YK11.getr (ms_regs msF) 4 = YK11.getr regs0 4)
by (rewrite F4, (EP_lo regs0 regsL 4 4%bv eq_refl); exact L4).
assert (K8 : YK11.getr (ms_regs msF) 8 = YK11.getr regs0 8)
by (rewrite F8; apply (EP_33 regs0 regsL)).
assert (K9 : YK11.getr (ms_regs msF) 9 = YK11.getr regs0 9)
by (rewrite F9; apply (EP_34 regs0 regsL)).
assert (K18 : YK11.getr (ms_regs msF) 18 = YK11.getr regs0 18)
by (rewrite F18; apply (EP_35 regs0 regsL)).
assert (K19 : YK11.getr (ms_regs msF) 19 = YK11.getr regs0 19)
by (rewrite F19; apply (EP_36 regs0 regsL)).
assert (K20 : YK11.getr (ms_regs msF) 20 = YK11.getr regs0 20)
by (rewrite F20; apply (EP_37 regs0 regsL)).
assert (K21 : YK11.getr (ms_regs msF) 21 = YK11.getr regs0 21)
by (rewrite F21; apply (EP_38 regs0 regsL)).
assert (K22 : YK11.getr (ms_regs msF) 22 = YK11.getr regs0 22)
by (rewrite F22; apply (EP_39 regs0 regsL)).
assert (K23 : YK11.getr (ms_regs msF) 23 = YK11.getr regs0 23)
by (rewrite F23, (EP_lo regs0 regsL 23 23%bv eq_refl); exact L23).
assert (K24 : YK11.getr (ms_regs msF) 24 = YK11.getr regs0 24)
by (rewrite F24, (EP_lo regs0 regsL 24 24%bv eq_refl); exact L24).
assert (K25 : YK11.getr (ms_regs msF) 25 = YK11.getr regs0 25)
by (rewrite F25, (EP_lo regs0 regsL 25 25%bv eq_refl); exact L25).
assert (K26 : YK11.getr (ms_regs msF) 26 = YK11.getr regs0 26)
by (rewrite F26, (EP_lo regs0 regsL 26 26%bv eq_refl); exact L26).
assert (K27 : YK11.getr (ms_regs msF) 27 = YK11.getr regs0 27)
by (rewrite F27, (EP_lo regs0 regsL 27 27%bv eq_refl); exact L27).
assert (K10 : YK11.getr (ms_regs msF) 10 = w64 (sptr_addr B ly' (fst r)))
by (rewrite F10, (EP_lo regs0 regsL 10 10%bv eq_refl); exact Ha0).
assert (RETEQ : v_jalr (YK11.getr (ms_regs msF) 1) 0 = w64 (raZ regs0)).
{ rewrite K1. unfold w64, raZ. rewrite Z_to_bv_bv_unsigned. exact Hret0. }
apply (SRr_ret_at tfibsegs tbl_calloc_A tbl_calloc_A_ok Hwx W2 _ _ msF _ _ HSP
ltac:(reflexivity)); [vm_compute; reflexivity|].
intros mat'.
(* ---- 5. the leaf. ---- *)
assert (SIO : same_io md0 mdL).
{ eapply same_io_trans; [apply same_io_wvb | exact Hio]. }
assert (SIOW : forall md', same_io md0 md' -> forall l X, same_io md0 (with_vm_backing l X md')).
{ intros md' H l X. exact (same_io_trans _ _ _ H (same_io_wvb md' l X)). }
assert (Hprod : 0 <= nm * sz) by (apply Z.mul_nonneg_nonneg; assumption).
assert (Hreq : nm * sz <= req_size (nm * sz))
by (unfold req_size; destruct (Z.eqb_spec (nm * sz) 0); lia).
split.
{ (* the allocation leaf: YG0d.v:244 malloc_leaf *)
exists ly'. eexists. eexists. eexists.
split; [unfold cfg_at; rewrite RETEQ; reflexivity|].
split.
{ (* YG0d.v:235 acall_post *)
split.
{ (* the allocator relation at the post *)
rewrite MMF. repeat (apply (AR_wvb B LAWS)). exact HARL. }
split; [exact Hly|]. split; [exact Hwle|].
split.
{ (* the callee-saved registers *)
intros k Hk.
assert (Hc : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/
k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by (unfold acallee_saved in Hk; lia).
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 2 2%bv eq_refl), (getr_lit regs0 2 2%bv eq_refl); exact K2|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 3 3%bv eq_refl), (getr_lit regs0 3 3%bv eq_refl); exact K3|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 4 4%bv eq_refl), (getr_lit regs0 4 4%bv eq_refl); exact K4|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 8 8%bv eq_refl), (getr_lit regs0 8 8%bv eq_refl); exact K8|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 9 9%bv eq_refl), (getr_lit regs0 9 9%bv eq_refl); exact K9|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 18 18%bv eq_refl), (getr_lit regs0 18 18%bv eq_refl); exact K18|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 19 19%bv eq_refl), (getr_lit regs0 19 19%bv eq_refl); exact K19|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 20 20%bv eq_refl), (getr_lit regs0 20 20%bv eq_refl); exact K20|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 21 21%bv eq_refl), (getr_lit regs0 21 21%bv eq_refl); exact K21|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 22 22%bv eq_refl), (getr_lit regs0 22 22%bv eq_refl); exact K22|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 23 23%bv eq_refl), (getr_lit regs0 23 23%bv eq_refl); exact K23|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 24 24%bv eq_refl), (getr_lit regs0 24 24%bv eq_refl); exact K24|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 25 25%bv eq_refl), (getr_lit regs0 25 25%bv eq_refl); exact K25|].
destruct Hc as [->|Hc];
[rewrite (getr_lit (ms_regs msF) 26 26%bv eq_refl), (getr_lit regs0 26 26%bv eq_refl); exact K26|].
subst k.
rewrite (getr_lit (ms_regs msF) 27 27%bv eq_refl), (getr_lit regs0 27 27%bv eq_refl); exact K27. }
split.
{ (* same_io *) repeat (apply SIOW). exact SIO. }
split.
{ (* the memory frame *)
intros a Ha H1 H2 H3 H4. rewrite MMF.
assert (HW : ~ (spZ regs0 - ASTACK <= a < spZ regs0)) by (intros Hc; apply H3; left; exact Hc).
rewrite (Hfr a Ha H1 H2).
- apply aview_eq_of_mem. apply MEQ. rewrite unsigned_lit_small by lia. exact HW.
- intros [Hs|He];
[apply H3; left; rewrite SPW in Hs;
cbv [ENTRY_STK ENTRY_FRAME YGAlloc.AFSTACK_G ICPT_FRAME ASTACK] in *; lia
| apply H3; right; exact He].
- exact H4. }
(* the stack window is present *)
rewrite MMF. exact PRESL. }
split; [rewrite K10; reflexivity | exact Hqt]. }
(* the user bytes read zero: YGCalloc.v calloc_zeroed *)
intros i Hi _. cbn [cfg_ms ms_regs ms_mem mkst].
rewrite MMF, K10. unfold w64. rewrite unsigned_lit_small by lia.
exact (Hzero i Hi).
Qed.
End t.
