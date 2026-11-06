(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S4 of the ASan+UBSan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput (fuzz_scene.asan-ubsan, sha256
   e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f), proved against the cut statement of
   lib/AU/P_LLVMFuzzerTestOneInput_seg.v (a Theorem Labs lane, unchanged by this file).  Rule 24: no function is proved here;
   this lane proves ONE segment lemma of the walk, with the runtime contracts and the glue's laws as Section
   hypotheses and with S3 (one loop turn) as the hypothesis the statement names. *)

(*   S4 = all of the whole_transfer block outside one turn:
     0x82e50 .. 0x82ea8  the guard `flags & 2` and `n' = 8904`, the malloc at 0x82e6c, its null test, and the
                         loop entry (got = 0, k = 0, declared = 0, blk.i + 7 and ~again spilled, blk.i + 9,
                         the poison byte and 8904 into their registers), ending at the loop head 0x82eac;
     the loop itself      closed by induction over the S3 hypothesis (343 turns, cut T k -> cut T (k+1) or cut TX);
     0x82f70 .. 0x82fa0  the got / declared checks, the bcmp at 0x82f90 and the free at 0x82f9c;
     and the no-T arm, which `beqz a0` 0x82e58 / `bne s8,a0` 0x82e64 take straight to C5 at 0x82fa4.
   Gate 6h: the sink head is this file's own Section variable SK, passed by name at every statement constant that
   takes one, so no global instance (the plain YI5b.src0_sink_head, cgif's AE2k.tfib_sink_head) can be chosen. *)
(* Cut base of record: a Theorem Labs lane's lib/AU/P_LLVMFuzzerTestOneInput_seg.v at
   18ba727d44b (a Theorem Labs lane, 2026-10-29 03:15Z).  This file Requires the cut file and the walk context, not
   lib/AU/P_LLVMFuzzerTestOneInput.v, so the capture of the short name YI16.sink_head that 18ba727d44b
   fixes there cannot reach it; its own sink head is the Section variable SK below. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC1h YC45 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h: scene's sink head is this Section's own variable; the glue instantiates it with scene_sink_head.
   It is made the local instance only so that the framework lemmas that take one implicitly get THIS one and
   never a global (YI5b.src0_sink_head of the released plain proof, or cgif's AE2k.tfib_sink_head). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation IM := scene_geom_asan_ubsan.

Section h.
Variable B : asyms.
Variable WK : swalk.

(* ---- the walk's constants, as the statement file (lib/AU/P_LLVMFuzzerTestOneInput.v) fixes them ---- *)
Definition S4_SPDROP : Z := 240.
Definition S4_malloc2_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + 0x5cc.
Definition S4_free1_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + 0x6fc.
Definition S4_bcmp_ra : Z := BASE + AF_LLVMFuzzerTestOneInput + 0x6f0.

(* ---- the glue's laws and bindings (the statement file's Section h, restricted to what S4 uses) ---- *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane's wrappers and a Theorem Labs lane's bcmp. *)
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
(* A Theorem Labs lane's allocation traces, at the two sites S4 calls (the statement file's HTRACE, whose six sites
   include them). *)
Hypothesis HTRACE : rt_trace_in_stmt SEGS (sw_ra WK) (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
(BASE + AF_LLVMFuzzerTestOneInput + 0x3ac) S4_malloc2_ra (BASE + AF_LLVMFuzzerTestOneInput + 0x708)
S4_free1_ra (BASE + AF_LLVMFuzzerTestOneInput + 0x8bc) (BASE + AF_LLVMFuzzerTestOneInput + 0x8c4)
(as_universe B).
(* the three budgets of the statement file (HSTK with LLVMF_SPDROP = 240, HEV with LLVMF_EV = 6,
   HLIVE with LLVMF_NMAX = 65535), as facts about this walk's constants. *)
Hypothesis HWSTK : S4_SPDROP + ASTACK <= sw_stk WK.
Hypothesis HWEV : 6 <= sw_ev WK.
Hypothesis HWLIVE : 2 * 65535 <= sw_live WK.
(* The walk's read-only window is PI_scene's, as `scene_llvmf_stmt` of lib/AU/P_LLVMFuzzerTestOneInput.v
   instantiates RLO / RHI with pa_relro_lo / pa_relro_hi; the `ro_below_ofl` instance above is over the same
   two numbers, and the journal transport of `arodata_okS` (lib/AU/Prog/SceneBase.v arodata_ok_journalP)
   needs them to agree. *)
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding, discharged by the composition *)
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* A Theorem Labs lane's ruling 04:04Z: segment-Section binding, discharged by the composition *)

(* ================================================================================================
   THE LOOP, CLOSED.  Purely the induction: 343 turns of the S3 hypothesis, from the head of turn k
   down to the exit.  The donor's counter induction (cgif A/ACfj.v:157-165 rt_G_allX) over the measure
   `sg_nturns IM - k`; the base case is refuted because the head carries 0 <= k < sg_nturns IM.
   ================================================================================================ *)
Lemma s4_loop_closed : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop),
(forall k, 0 <= k < sg_nturns IM ->
(k + 1 < sg_nturns IM -> sc_from_T (SK := SK) SEGS B ameter_triv WK IM cx POST (k + 1)) ->
sc_from_TX (SK := SK) SEGS B ameter_triv WK IM cx POST ->
sc_from_T (SK := SK) SEGS B ameter_triv WK IM cx POST k) ->
sc_from_TX (SK := SK) SEGS B ameter_triv WK IM cx POST ->
forall k, 0 <= k < sg_nturns IM -> sc_from_T (SK := SK) SEGS B ameter_triv WK IM cx POST k.
Proof.
intros cx POST HS3 HTX.
assert (HN : forall n : nat, forall k, 0 <= k < sg_nturns IM -> sg_nturns IM - k <= Z.of_nat n ->
  sc_from_T (SK := SK) SEGS B ameter_triv WK IM cx POST k).
{ induction n as [|m IH]; intros k Hk Hn; [exfalso; cbn [Z.of_nat] in Hn; lia|].
  apply (HS3 k Hk); [intros Hlt; apply (IH (k + 1)); [lia | rewrite Nat2Z.inj_succ in Hn; lia] | exact HTX]. }
intros k Hk. apply (HN (Z.to_nat (sg_nturns IM - k)) k Hk). rewrite Z2Nat.id by lia. lia.
Qed.

(* ================================================================================================
   THE CALLER CHAIN at a call inside LLVMFuzzerTestOneInput.  The entry contract's `afn_pre` gives the
   chain [] at the entry state; the prologue's saved ra and s0 (the cut's `sc_saves`, slots sp0 - 8 and
   sp0 - 16) push the entry's own record, which is exactly the context's `rt_ch cx` -- the list the
   trace hypothesis HTRACE speaks about.  (cgif's A/ACf5.v rt_chain.)
   ================================================================================================ *)
Lemma s4_chain : forall (cx : rtcx SEGS) ly3 S3 (W3 : world SEGS) mem3 md3 ev (regsT : bvmap 5 word),
afn_pre SEGS B (sw_stk WK) (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [] ->
c_sp1 cx = 32 * ((spZ (c_regs cx) - 224) / 32) ->
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(sg_cid IM, c_fpos cx)] ly3 S3 W3 mem3 md3 ev ->
sc_saves SEGS cx W3 mem3 ->
spZ regsT = c_sp1 cx -> s0Z regsT = spZ (c_regs cx) -> 4096 <= raZ regsT ->
chain_pre ly3 (aview SEGS (w_H W3) mem3) regsT (rt_ch cx).
Proof.
intros cx ly3 S3 W3 mem3 md3 ev regsT HPRE HSP1 HJ HSAV Hsp Hs0 Hra4.
pose proof HPRE as (HAR & Hra & Hra0 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & HK1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
assert (HSTK0 : 240 + ASTACK <= sw_stk WK) by exact HWSTK.
assert (HASTK : ASTACK = 16384) by reflexivity.
assert (HS0 : rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
{ replace (spZ (c_regs cx) - 8) with (spZ (c_regs cx) - 8 - 8 * 0) by lia. exact (HSAV 0 ltac:(lia)). }
assert (HS1 : rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 8 - 8 * 1) by lia. exact (HSAV 1 ltac:(lia)). }
unfold rt_ch.
destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hf0 | Hf0].
- eapply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)));
  [| lia | exact Hs0 | exact Hra4].
  eapply (achain_ly_top (c_ly cx) ly3); [exact Etop |].
  eapply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem3)
    (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (c_sp1 cx) Hch ltac:(lia)).
  + intros a Ha. apply HK1; lia.
  + exact HS0.
  + exact HS1.
  + exact Hra0.
  + lia.
  + revert Hal16. clear. intros. Z.div_mod_to_equations. lia.
  + lia.
  + lia.
- eapply (achain_chain_pre ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)));
  [| lia | exact Hs0 | exact Hra4].
  left. split; [right; left; lia | reflexivity].
Qed.

(* ---- reading a cut's `vat` clauses: the table's rows are literal, so the register number / spill offset
   reduces, and `vat` becomes a `getr` or a `rdword` equation ---- *)
Local Ltac s4v H :=
cbn [vat scene_geom_asan_ubsan
sg_cid sg_frame sg_off_blki sg_off_mac sg_off_blk sg_off_expect sg_blk_n sg_mac_n sg_scene_n sg_nturns
sgT_got sgT_k sgT_shF sgT_sp1 sgT_sp0 sgT_blki sgT_srcA sgT_srcB sgT_f8 sgT_n1 sgT_extra sgT_nagain
sgT_again sgT_body sgT_decl sgT_nprime sgT_Fsp sgT_mac sgT_shexp sgT_expect sgT_Fb sgT_nn sgT_body2 sgTX_got2
sg5_F sg5_shF sg5_sp1 sg5_sp0 sg5_nprime sg5_expect sg5_shexp sg5_Fsp sg5_mac sg5_body sg5_nn
sg3_F sg3_Fb sg3_shF sg3_sp1 sg3_sp0 sg3_blki sg3_expect sg3_nprime sg3_flags sg3_step sg3_shexp sg3_Fsp
sg3_mac sg3_body sg3_nn
] in H;
cbv [RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 RV_a1 RV_a6 RV_t2] in H.

(* the two heap blocks of the T arm are below the allocation ceiling, hence never inside the callee stack
   windows below the realigned sp *)
Lemma s4_block_off_stack : forall (cx : rtcx SEGS) p n a,
alloc_ceiling <= ly_stk_lo (c_ly cx) -> ly_stk_lo (c_ly cx) + sw_stk WK <= spZ (c_regs cx) ->
c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240 ->
4096 <= p -> p + n <= alloc_ceiling -> p <= a < p + n ->
~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx).
Proof.
intros cx p n a Hceil Hslo HO Hp Hpn Ha.
assert (HE : ESTACK = 4096) by reflexivity. pose proof HWSTK as HS. unfold S4_SPDROP in HS.
assert (HA : ASTACK = 16384) by reflexivity. lia.
Qed.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let ENVB : api_env SEGS B := pal_env B TL.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* a run whose regions are all read-only changes no byte *)
Lemma s4_kept_ro : forall (W : world SEGS) E (rs : smem) (m m' : word -> option byte),
(forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) ->
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W E rs m m' Hro HF a. apply (aview_eq_of SEGS).
apply (HF (Z_to_bv 64 a)). intros (r & Hin & Hr). pose proof (Hro r Hin) as Hq. lia.
Qed.
(* the one region of the tail: the spill slots this segment reads, read-only (it stores nothing) *)
Definition s4_stkR (again : Z) : smem :=
[YP09.mkRegion (Some 9%nat) 8 96 0 0
[YP09.mkChunk 8 (CVal 8 (SLit 8904)); YP09.mkChunk 64 (CVal 8 (SLit 8904));
YP09.mkChunk 88 (CVal 8 (SLit again))]].
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI_scene).

(* ---- the local tactics of the walk, as a Theorem Labs lane's segment proofs use them ---- *)
(* pin a register of the symbolic state to the literal the cut gives it *)
Local Ltac pin HS r e Hr :=
let H := fresh "HSp" in
pose proof (ast_ok_pi_set_reg_fp _ _ _ r e HS eq_refl
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Hr; reflexivity)) as H;
clear HS; rename H into HS; cbn [add_atom ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
(* the write permission of a run whose only region is read-only (this segment stores nothing) *)
Local Ltac s4_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc lyx own) end;
repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |]].
(* read a register off the symbolic state without normalising its atom away *)
Local Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) => pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) => pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr
end;
lazymatch type of Hr with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
change (sr_get (ss_regs ssx) r) with e in Hr end;
cbn [ms_regs restrict mkst] in Hr.

(* ---- three facts the C5 cut needs after the free ---- *)
(* a byte array is kept when each of its bytes is (SceneFrame.v val_mem_moved, byte by byte) *)
Lemma s4_garr8_moved : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a + j) = aview SEGS (w_H W) m (a + j)) ->
garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W') m') a l.
Proof.
intros W W' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (a + Z.of_nat j) 1%nat); [|exact Hv].
intros k Hk1. rewrite <- !Z.add_assoc. apply Hk. lia.
Qed.
(* the 2048 shadow bytes of a fake frame below the ASan ceiling lie between the low shadow's start and
   the high memory's start, so no heap block in zone2 meets them *)
Lemma s4_shadow_lo : forall F, 4096 <= F -> F + 16384 <= 0x7fffff800000 ->
2147450880 <= shadow_addr F /\ shadow_addr F + 2048 <= 17594333462528.
Proof. intros F H1 H2. unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.
(* a shadow cell of an object at offset off of an 8-aligned 16384-byte frame is one of the frame's 2048 *)
Lemma s4_open_idx : forall F off len i, F mod 8 = 0 -> (F + off) mod 8 = 0 -> 0 <= off -> 0 <= len ->
off + len <= 16384 -> 0 <= i < (len + 7) / 8 ->
shadow_addr F <= shadow_of_addr SHADOW_OFF (F + off) + i < shadow_addr F + 2048.
Proof. intros F off len i H1 H2 H3 H4 H5 H6. unfold shadow_addr, shadow_of_addr. Z.div_mod_to_equations. lia. Qed.

(* ================================================================================================
   THE TAIL, 0x82f70 .. 0x82fa0: the two exit checks (got and declared, both 8904 at the loop exit),
   the bcmp of `again` against `body` -- equal, because the loop wrote b into again -- and the free of
   `again`, landing at C5 with ev = 3.
   ================================================================================================ *)
Lemma s4_tail : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop),
sc_base SEGS B ameter_triv WK cx ->
sc_from_C5 (SK := SK) SEGS B ameter_triv WK IM cx POST ->
sc_from_TX (SK := SK) SEGS B ameter_triv WK IM cx POST.
Proof.
intros cx POST HBASE HC5 ly3 S3 W3 regs3 mem3 md3 bs body again b HTX.
pose proof HBASE as (HBASE0 & HSP1).
pose proof HBASE0 as (HPRE & HraW & Hp10 & Hp11 & Hpn0 & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK0 & Hfd0 & Hfs0 & HMO0).
pose proof HPRE as (HAR0 & Hra & Hra0 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HWSTK as HSTKb. unfold S4_SPDROP in HSTKb.
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
destruct HTX as (HT & HgotX & Hgot2).
pose proof HT as (Hk & Hwhole & HJj & Hab & Hbbnd & HokB & HokA & Hsepab & Hlenb & Hgb & Hjaex &
Hfrm & Hsav & Hshbg & Hshblki & HopB & HopM & Himg & Hinput & Hmacb & Rsp0 & Rsp1 & RFsp & RshF & Rblki &
RsrcA & RsrcB & Rmac & Rshexp & Rbody & Ragain & Rnprime & Rgot & Rkk & Rdecl & Rn1 & Rext & Rnag & Rexp &
RFb & Rnn & Rbody2 & Rf8).
pose proof HJj as (HJ & Hfrs3 & Hmle).
destruct Hjaex as (ja & Hjalen & Hgagain).
pose proof Himg as (Hsp3 & Hgp3 & Htp3 & HROD3).
pose proof HokA as (HA4096 & HAzone & HAceil & HA16 & HAwr & HAftok).
pose proof HokB as (HB4096 & HBzone & HBceil & HB16 & HBwr & HBftok).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & Hnev3 & Hk3 & HK1 & HK2 & HK3 & HK4 & _ & HPRES3 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the table's numbers *)
change (sg_scene_n IM) with 8904 in *. change (sg_nturns IM) with 343 in *. change (sg_cid IM) with 8 in *.
assert (HRS : req_size 8904 = 8904) by reflexivity.
rewrite HRS in HAceil, HBceil.
(* b fills again in full at the exit *)
assert (Hlenb' : length b = 8904%nat) by (apply Nat2Z.inj; rewrite Hlenb; reflexivity).
assert (Hja0 : ja = []).
{ apply length_zero_iff_nil. apply Nat2Z.inj. rewrite Hjalen, scT_off_343. reflexivity. }
assert (Hfa : firstn (Z.to_nat (scT_off 343)) b = b).
{ rewrite scT_off_343. replace (Z.to_nat 8904) with 8904%nat by reflexivity. apply firstn_all2. lia. }
rewrite Hfa, Hja0, app_nil_r in Hgagain.
(* the two blocks are in the journal's block list *)
assert (HinA : In (again, 8904) (ablocks B ly3 S3)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HinB : In (body, 8904) (ablocks B ly3 S3))
by (rewrite Hab; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
(* the bytes of the two blocks, as aview equations *)
assert (HVA : forall i, 0 <= i < 8904 -> aview SEGS (w_H W3) mem3 (again + i) = Some (nth (Z.to_nat i) (u8s b) 0)).
{ intros i Hi. destruct (garr8_nthZ SEGS _ _ _ i Hgagain ltac:(lia)
    ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
  exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
assert (HVB : forall i, 0 <= i < 8904 -> aview SEGS (w_H W3) mem3 (body + i) = Some (nth (Z.to_nat i) (u8s b) 0)).
{ intros i Hi. destruct (garr8_nthZ SEGS _ _ _ i Hgb ltac:(lia)
    ltac:(unfold u8s; rewrite length_map; lia)) as (Hv & Hr).
  exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
(* the registers and spill slots of the cut, as plain equations *)
s4v Rsp1. s4v Rsp0. s4v RshF. s4v Rbody. s4v Ragain. s4v Rnprime. s4v Rdecl. s4v Rbody2. s4v Hgot2. s4v Rnn.
s4v RFsp. s4v Rmac. s4v Rshexp. s4v Rexp. s4v RFb. s4v Rblki. s4v RsrcA. s4v RsrcB. s4v Rf8. s4v Rgot. s4v Rkk.
cbn [Z.eqb] in Rdecl.
(* ---- the symbolic state at the loop exit: the three spill slots this segment reads, as literal chunks of
   a read-only region over the frame's spill window; every other value stays in its entry atom ---- *)
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx).
{ rewrite (EE 9%nat (9%bv : bv 5) eq_refl), Rsp1. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi SEGS VAL E
(mkSS (AF_LLVMFuzzerTestOneInput + SEG_TX_off) sr_atoms (s4_stkR again) None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_TX_off))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [| constructor].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    + apply (chunk_ok_val SEGS E _ _ 8 8%N (SLit 8904) 8904);
      [cbn [sv_denot]; first [reflexivity | rewrite zcanon_id by (unfold M64; lia); reflexivity]
      | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS). exact Rnprime.
    + apply (chunk_ok_val SEGS E _ _ 64 8%N (SLit 8904) 8904);
      [cbn [sv_denot]; first [reflexivity | rewrite zcanon_id by (unfold M64; lia); reflexivity]
      | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS). exact Rdecl.
    + apply (chunk_ok_val SEGS E _ _ 88 8%N (SLit again) again);
      [cbn [sv_denot]; first [reflexivity | rewrite zcanon_id by (unfold M64; lia); reflexivity]
      | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS). exact Ragain.
  - cbv [s4_stkR]. cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
clear HE.
(* got is 8904 at the exit, so the two checks fall through *)
assert (R24 : getr regs3 (24%bv : bv 5) = w64 8904) by (rewrite Hgot2; reflexivity).
pin HS (24%bv : bv 5) (SLit 8904) R24.
unfold cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
replace pcw with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_TX_off)))
by (cbn [sg_pc_tx scene_geom_asan_ubsan]; unfold w64; f_equal; lia) end.
paj_run_shc RUNP RUNC HS HJ; [s4_awr |].
(* the run changed no byte: its one region is read-only *)
assert (KM : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ apply (s4_kept_ro W3 E (s4_stkR again) mem3 (ms_mem ms));
  [intros r Hin; cbv [s4_stkR] in Hin; cbn [In] in Hin;
   repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi]; lia |]); destruct Hin
  | exact HFr]. }
(* 0x82f90: bcmp(again, body, 8904) *)
pmkst HS.
prreg_raw HS (10%bv : bv 5) Ra0. prreg_raw HS (11%bv : bv 5) Ra1. prreg_raw HS (12%bv : bv 5) Ra2.
prreg_raw HS (1%bv : bv 5) Rra. prreg_raw HS (2%bv : bv 5) Qsp.
prreg_raw HS (3%bv : bv 5) Qgp. prreg_raw HS (4%bv : bv 5) Qtp.
prreg_raw HS (8%bv : bv 5) Qs0. prreg_raw HS (9%bv : bv 5) Qs1.
assert (HSP1b : spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224) by (destruct HO; lia).
assert (HOmod : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ destruct HO as [HOx | HOx]; rewrite HOx;
  [replace (spZ (c_regs cx) - 224 - spZ (c_regs cx)) with (-224) by lia
  |replace (spZ (c_regs cx) - 240 - spZ (c_regs cx)) with (-240) by lia]; reflexivity. }
assert (Hsp' : spZ (ms_regs ms) = c_sp1 cx).
{ unfold spZ. rewrite Qsp. cbn [sv_denot]. rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl).
  unfold spZ in Hsp3. rewrite Hsp3. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W3 rg mm
    (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly3 S3 mdx 2 again body 8904 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 1776))) end.
  - exact HJ.
  - rewrite Ra0; cbn [sv_denot]; unfold w64;
    first [reflexivity | (f_equal; rewrite zcanon_id by (unfold M64; lia); reflexivity)].
  - rewrite Ra1. cbn [sv_denot]. rewrite Z.add_0_r, (EE 11%nat (11%bv : bv 5) eq_refl).
    rewrite Z_to_bv_bv_unsigned. exact Rbody2.
  - rewrite Ra2. cbn [sv_denot]. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Hsp'. lia.
  - exact HOmod.
  - lia.
  - lia.
  - rewrite Qgp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl).
    exact Hgp3.
  - rewrite Qtp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl).
    exact Htp3.
  - rewrite Rra. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 1776). reflexivity.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + rewrite KM. replace a with (again + (a - again)) by lia. rewrite (HVA (a - again) ltac:(lia)). discriminate.
    + rewrite Hsp'. lia.
  - intros a Ha. split.
    + rewrite KM. replace a with (body + (a - body)) by lia. rewrite (HVB (a - body) ltac:(lia)). discriminate.
    + rewrite Hsp'. lia.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ again 8904 again 8904 (proj1 HJ) HinA
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - exact (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ body 8904 body 8904 (proj1 HJ) HinB
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ again 8904 again 8904 (proj1 HJ) HinA
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ again 8904 again 8904 (proj1 HJ) HinA
      ltac:(lia) ltac:(rewrite HRS; lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ body 8904 body 8904 (proj1 HJ) HinB
      ltac:(lia) ltac:(rewrite HRS; lia)).
  - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ body 8904 body 8904 (proj1 HJ) HinB
      ltac:(lia) ltac:(rewrite HRS; lia) ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & KMc & KPres).
(* again holds b in full, so the compare is equal and `bnez a0` 0x82f94 falls through *)
assert (Hv0 : v = w64 0).
{ apply (proj2 Hcmp). intros i Hi. rewrite KM, KM, (HVA i Hi), (HVB i Hi). reflexivity. }
assert (KMc' : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha Hn. apply KMc; [exact Ha|].
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia. exact Hn. }
assert (Hrd2 : forall a vv, 0 <= a -> a + 8 <= 2 ^ 64 ->
(forall kk, 0 <= kk < 8 -> ~ (c_sp1 cx - 2 * ESTACK <= a + kk < c_sp1 cx)) ->
rdword (aview SEGS (w_H W3) mem3) a = Some vv -> rdword (aview SEGS (w_H W3) mem2) a = Some vv).
{ intros a vv H0 H8 Hns Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem2) a); [exact Hr|].
  intros kk Hkk. rewrite (KMc' (a + kk) ltac:(lia) (Hns kk Hkk)). apply KM. }
(* ---- the state after the compare: a0 = 0, so `bnez a0` 0x82f94 falls through, then `ld a0,0x58(s1)`
   and the free of `again` at 0x82f9c ---- *)
assert (HPr : forall (n : Z) (r : bv 5), acallee_saved n -> bv_unsigned r = n -> getr regs2 r = getr (ms_regs ms) r).
{ intros n r Hn Hr. pose proof (HP2 n Hn) as HQ.
  replace (Z_to_bv 5 n) with r in HQ by (apply bv_eq; rewrite Z_to_bv_unsigned, Hr;
    unfold bv_wrap; rewrite Z.mod_small; [reflexivity | rewrite <- Hr; apply bv_unsigned_in_range]).
  exact HQ. }
assert (Q9b : getr regs2 (9%bv : bv 5) = w64 (c_sp1 cx)).
{ rewrite (HPr 9 (9%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qs1. cbn [sv_denot].
  rewrite Z.add_0_r, (EE 9%nat (9%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rsp1. }
assert (Q8b : getr regs2 (8%bv : bv 5) = w64 (spZ (c_regs cx))).
{ rewrite (HPr 8 (8%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qs0. cbn [sv_denot].
  rewrite Z.add_0_r, (EE 8%nat (8%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rsp0. }
assert (Q3b : getr regs2 (3%bv : bv 5) = w64 (as_gp B)).
{ rewrite (HPr 3 (3%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qgp. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl). exact Hgp3. }
assert (Q4b : getr regs2 (4%bv : bv 5) = w64 (as_tp B)).
{ rewrite (HPr 4 (4%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qtp. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl). exact Htp3. }
assert (Q2b : getr regs2 (2%bv : bv 5) = w64 (c_sp1 cx)).
{ rewrite (HPr 2 (2%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qsp. cbn [sv_denot].
  rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned.
  unfold spZ in Hsp3. unfold w64. rewrite <- Hsp3. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity | apply bv_unsigned_in_range]. }
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9b : bv_unsigned (ew E2 9) = c_sp1 cx).
{ rewrite (EE2 9%nat (9%bv : bv 5) eq_refl), Q9b. unfold w64. apply unsigned_lit_small. lia. }
assert (HS2 : st_ok_pi SEGS VAL E2
(mkSS 1776 sr_atoms [YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SLit again))]]
None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 1776)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [| constructor].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    apply (chunk_ok_val SEGS E2 _ _ 88 8%N (SLit again) again);
    [cbn [sv_denot]; first [reflexivity | rewrite zcanon_id by (unfold M64; lia); reflexivity]
    | cbn; lia | cbn; lia |].
    apply (val_mem_of_rdword SEGS). apply Hrd2; [lia | lia | intros kk Hkk; lia | exact Ragain].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
clear HE2.
assert (Ra0z : getr regs2 (10%bv : bv 5) = w64 0) by (rewrite Hv, Hv0; reflexivity).
pin HS2 (10%bv : bv 5) (SLit 0) Ra0z.
paj_run_shc RUNP RUNC HS2 HJ2; [s4_awr |].
(* the second run changed no byte either: its one region is read-only *)
assert (KM2 : forall a, aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem2 a).
{ apply (s4_kept_ro W3 E2 [YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SLit again))]]
    mem2 (ms_mem ms0));
  [intros r Hin; cbn [In] in Hin;
   repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi]; lia |]); destruct Hin | exact HFr0]. }
assert (Hrd3 : forall a vv, 0 <= a -> a + 8 <= 2 ^ 64 ->
(forall kk, 0 <= kk < 8 -> ~ (c_sp1 cx - 2 * ESTACK <= a + kk < c_sp1 cx)) ->
rdword (aview SEGS (w_H W3) mem3) a = Some vv -> rdword (aview SEGS (w_H W3) (ms_mem ms0)) a = Some vv).
{ intros a vv H0 H8 Hns Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem2) (aview SEGS (w_H W3) (ms_mem ms0)) a);
  [ apply Hrd2; assumption | intros kk Hkk; apply KM2 ]. }
assert (HSAV2 : sc_saves SEGS cx W3 (ms_mem ms0)).
{ intros j Hj. apply Hrd3; [lia | lia | intros kk Hkk; lia | exact (Hsav j Hj)]. }
(* 0x82f9c: free(again) *)
pose proof (afree04_rule_triv SEGS B Hsegs ENVB LAWS ML AFREE) as FREE4.
pmkst HS2.
prreg_raw HS2 (10%bv : bv 5) Fa0. prreg_raw HS2 (1%bv : bv 5) Fra. prreg_raw HS2 (2%bv : bv 5) Fsp.
prreg_raw HS2 (3%bv : bv 5) Fgp. prreg_raw HS2 (4%bv : bv 5) Ftp. prreg_raw HS2 (8%bv : bv 5) Fs0.
assert (Fspz : spZ (ms_regs ms0) = c_sp1 cx).
{ unfold spZ. rewrite Fsp. cbn [sv_denot]. rewrite Z.add_0_r, (EE2 2%nat (2%bv : bv 5) eq_refl), Q2b.
  rewrite Z_to_bv_bv_unsigned. unfold w64. apply unsigned_lit_small. lia. }
assert (Fs0z : s0Z (ms_regs ms0) = spZ (c_regs cx)).
{ unfold s0Z. rewrite Fs0. cbn [sv_denot]. rewrite Z.add_0_r, (EE2 8%nat (8%bv : bv 5) eq_refl), Q8b.
  rewrite Z_to_bv_bv_unsigned. unfold w64. apply unsigned_lit_small. lia. }
assert (Fraz : raZ (ms_regs ms0) = BASE + 1788).
{ unfold raZ. rewrite Fra. cbn [sv_denot]. rewrite (img_env_codeptr E2 HEI2 1788).
  pose proof pa_B_ok as HBok. apply unsigned_lit_small. lia. }
rewrite (pal_free B TL).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply (FREE4 W3 rg mm (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(8, c_fpos cx)] ly3 S3 mdx 2 again 8904 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 1788)) (rt_ch cx)) end.
  - exact HJ2.
  - exact HinA.
  - rewrite Fa0; cbn [sv_denot]; unfold w64;
    first [reflexivity | (f_equal; rewrite zcanon_id by (unfold M64; lia); reflexivity)].
  - rewrite Fspz. lia.
  - exact HOmod.
  - lia.
  - lia.
  - rewrite Fgp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 3%nat (3%bv : bv 5) eq_refl).
    exact Q3b.
  - rewrite Ftp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 4%nat (4%bv : bv 5) eq_refl).
    exact Q4b.
  - rewrite Fra. cbn [sv_denot]. rewrite (img_env_codeptr E2 HEI2 1788). reflexivity.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia.
  - exact (s4_chain cx ly3 S3 W3 (ms_mem ms0) _ 2 (ms_regs ms0) HPRE HSP1 HJ2 HSAV2 Fspz Fs0z
      ltac:(rewrite Fraz; pose proof (pa_base_lo (PL := PL_scene)) as HBLO; lia)).
  - apply (HTRACE (pc_free_ra0 (as_code B)) (BASE + 1788) (ms_regs ms0) cx HraW Fraz).
    right. split; [reflexivity|]. left. unfold S4_free1_ra, AF_LLVMFuzzerTestOneInput. lia.
  - exact HAftok.
  - exact I. }
(* ---- after the free: `ld s8,8(s1)` 0x82fa0, then the cut C5 at 0x82fa4 ---- *)
cbv beta. intros W4 c4 Hwle4
  (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Hl1 & Hl2) & Hfrs4 & KPT & _).
pose proof KPT as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
assert (Hown3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HAR4 : AR SEGS B ly4 S4 W4 mem4 md4) by exact (proj1 HJ4).
(* the block list after the free is a permutation of the entry's plus body *)
assert (HPERM : Permutation (ablocks B ly4 S4) (ablocks B (c_ly cx) (c_S cx) ++ [(body, 8904)])).
{ apply (Permutation_cons_inv (a := (again, 8904))).
  apply (Permutation_trans (l' := l1 ++ (again, 8904) :: l2));
  [ rewrite Hl2; apply Permutation_middle
  | rewrite <- Hl1, Hab; apply Permutation_sym; apply Permutation_cons_append ]. }
(* and its byte total is the entry's plus one block of 8904 *)
assert (HBB4 : blocks_bytes S4 <= blocks_bytes (c_S cx) + req_size 8904).
{ rewrite (blocks_bytes_bsum B ly4 S4), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  rewrite (bsum_perm _ _ HPERM), bsum_app. cbn [bsum fold_right snd]. rewrite HRS. lia. }
(* ---- the three memory transports from the cut's state to the state after the free ---- *)
(* (1) every address above the allocation ceiling and outside the callee window: acall_kept clause 1 *)
assert (KSTK : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp1 cx - ASTACK <= a < c_sp1 cx) ->
aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite (KT1 a Ha ltac:(replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
    with (c_sp1 cx) by lia; exact Hn)).
  rewrite KM2. rewrite (KMc' a ltac:(lia) ltac:(lia)). apply KM. }
(* (2) body's bytes: acall_kept clause 2, since body is disjoint from the freed block *)
assert (KBLK : forall i, 0 <= i < 8904 -> aview SEGS (w_H W4) mem4 (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
{ intros i Hi. rewrite (KT2 body 8904 i HinB ltac:(rewrite HRS; lia) ltac:(rewrite HRS; lia)).
  rewrite KM2. rewrite (KMc' (body + i) ltac:(lia) ltac:(lia)). apply KM. }
(* (3) the fake frame and its shadow: acall_kept clause 4, since neither meets the freed block -- the frame
   by the AR separation of blocks and frames (YCbq.v sep_block_frame), the shadow because the freed block
   lies in zone2 and the frame's shadow between the low shadow and the high memory (YCbq.v:765-771) *)
assert (HFB : fs_frame_bytes 8 = 16384) by reflexivity.
assert (EF3 : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS IM cx).
{ unfold sc_F, rt_F, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (HF32 & _ & _ & _).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (HF4096 & HFceil & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 again 8904 8 (c_fpos cx) HAR3 HinA Hown3) as HdA.
unfold zdisjoint in HdA. cbn [fst snd] in HdA.
rewrite EF3 in HF32, HF4096, HFceil, HdA. rewrite HFB in HFceil, HdA. rewrite HRS in HdA.
assert (HSL : 2147450880 <= shadow_addr (sc_F SEGS IM cx) /\ shadow_addr (sc_F SEGS IM cx) + 2048 <= 17594333462528).
{ apply s4_shadow_lo; [exact HF4096 | lia]. }
pose proof (zone2_band _ _ HAzone) as HAz2. rewrite HRS in HAz2.
assert (HF8 : sc_F SEGS IM cx mod 8 = 0).
{ revert HF32. generalize (sc_F SEGS IM cx). clear. intros F HF. Z.div_mod_to_equations. lia. }
assert (KFRM : forall a, (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
  shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha.
  assert (Hna : ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx)) by lia.
  rewrite (KT4 8 (c_fpos cx) a Hown3).
  - rewrite KM2. rewrite (KMc' a ltac:(lia) Hna). apply KM.
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, HFB. change (16384 / 8) with 2048. exact Ha.
  - intros Hc. cbv beta in Hc. rewrite ?HRS in Hc. lia. }
(* the spill slots and the saved words lie above the callee window: KSTK *)
assert (SPILL4 : forall aa vv, c_sp1 cx <= aa -> aa + 8 <= spZ (c_regs cx) ->
  rdword (aview SEGS (w_H W3) mem3) aa = Some vv -> rdword (aview SEGS (w_H W4) mem4) aa = Some vv).
{ intros aa vv Hsa Hsb Hsr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W4) mem4) aa); [exact Hsr|].
  intros kk Hkk. apply KSTK; lia. }
assert (EF4 : frame_addr ly4 8 (c_fpos cx) = sc_F SEGS IM cx).
{ pose proof HJ4 as (_ & Hly4 & _). unfold sc_F, rt_F, frame_addr.
  pose proof Hly4 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hown4 : In (8, c_fpos cx) (frames S4)) by (rewrite Hfrs4; exact Hown3).
(* ---- the callee-saved registers C5 names, from the loop exit through the bcmp and the free ---- *)
prreg_raw HS (19%bv : bv 5) Qs3. prreg_raw HS (20%bv : bv 5) Qs4.
prreg_raw HS2 (9%bv : bv 5) Fs1. prreg_raw HS2 (19%bv : bv 5) Fs3. prreg_raw HS2 (20%bv : bv 5) Fs4.
assert (Q19b : getr regs2 (19%bv : bv 5) = w64 (shadow_addr (sc_F SEGS IM cx))).
{ rewrite (HPr 19 (19%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qs3. cbn [sv_denot].
  rewrite Z.add_0_r, (EE 19%nat (19%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact RshF. }
assert (Q20b : getr regs2 (20%bv : bv 5) = w64 body).
{ rewrite (HPr 20 (20%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Qs4. cbn [sv_denot].
  rewrite Z.add_0_r, (EE 20%nat (20%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rbody. }
assert (HP4r : forall (n : Z) (r : bv 5), acallee_saved n -> bv_unsigned r = n -> getr regs4 r = getr (ms_regs ms0) r).
{ intros n r Hn Hr. pose proof (HP4 n Hn) as HQ.
  replace (Z_to_bv 5 n) with r in HQ by (apply bv_eq; rewrite Z_to_bv_unsigned, Hr;
    unfold bv_wrap; rewrite Z.mod_small; [reflexivity | rewrite <- Hr; apply bv_unsigned_in_range]).
  exact HQ. }
assert (Q2c : getr regs4 (2%bv : bv 5) = w64 (c_sp1 cx)).
{ rewrite (HP4r 2 (2%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Fsp. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 2%nat (2%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q2b. }
assert (Q3c : getr regs4 (3%bv : bv 5) = w64 (as_gp B)).
{ rewrite (HP4r 3 (3%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Fgp. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 3%nat (3%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q3b. }
assert (Q4c : getr regs4 (4%bv : bv 5) = w64 (as_tp B)).
{ rewrite (HP4r 4 (4%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Ftp. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 4%nat (4%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q4b. }
assert (Q8c : getr regs4 (8%bv : bv 5) = w64 (spZ (c_regs cx))).
{ rewrite (HP4r 8 (8%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Fs0. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 8%nat (8%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q8b. }
assert (Q9c : getr regs4 (9%bv : bv 5) = w64 (c_sp1 cx)).
{ rewrite (HP4r 9 (9%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Fs1. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 9%nat (9%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q9b. }
assert (Q19c : getr regs4 (19%bv : bv 5) = w64 (shadow_addr (sc_F SEGS IM cx))).
{ rewrite (HP4r 19 (19%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Fs3. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 19%nat (19%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q19b. }
assert (Q20c : getr regs4 (20%bv : bv 5) = w64 body).
{ rewrite (HP4r 20 (20%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Fs4. cbn [sv_denot].
  rewrite Z.add_0_r, (EE2 20%nat (20%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q20b. }
(* ---- 0x82fa0: `ld s8,8(s1)` reloads n' = 8904; the state holds the one slot it reads, read-only ---- *)
remember (Eimg (Ereg regs4 [])) as E4 eqn:HE4.
assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs4 r)
by (intros n r Hn; subst E4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9c : bv_unsigned (ew E4 9) = c_sp1 cx).
{ rewrite (EE4 9%nat (9%bv : bv 5) eq_refl), Q9c. unfold w64. apply unsigned_lit_small. lia. }
assert (HS3 : st_ok_pi SEGS VAL E4
(mkSS 1788 sr_atoms [YP09.mkRegion (Some 9%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SLit 8904))]]
None (mkFacts [] [] []))
(restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 1788)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E4. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [| constructor].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9c. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    apply (chunk_ok_val SEGS E4 _ _ 8 8%N (SLit 8904) 8904);
    [cbn [sv_denot]; first [reflexivity | rewrite zcanon_id by (unfold M64; lia); reflexivity]
    | cbn; lia | cbn; lia |].
    apply (val_mem_of_rdword SEGS). apply SPILL4; [lia | lia | exact Rnprime].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
clear HE4.
paj_run_to_shc RUNTOP HS3 HJ4 1792; [s4_awr |].
(* the run changed no byte: its one region is read-only *)
assert (KM5 : forall a, aview SEGS (w_H W4) (ms_mem ms1) a = aview SEGS (w_H W4) mem4 a).
{ apply (s4_kept_ro W4 E4 [YP09.mkRegion (Some 9%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SLit 8904))]]
    mem4 (ms_mem ms1));
  [intros r Hin; cbn [In] in Hin;
   repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi]; lia |]); destruct Hin | exact HFr1]. }
assert (SPILLF : forall aa vv, c_sp1 cx <= aa -> aa + 8 <= spZ (c_regs cx) ->
  rdword (aview SEGS (w_H W3) mem3) aa = Some vv -> rdword (aview SEGS (w_H W4) (ms_mem ms1)) aa = Some vv).
{ intros aa vv Hsa Hsb Hsr.
  rewrite (rdword_ext (aview SEGS (w_H W4) mem4) (aview SEGS (w_H W4) (ms_mem ms1)) aa);
  [exact (SPILL4 aa vv Hsa Hsb Hsr) | intros kk Hkk; apply KM5]. }
assert (KFRMF : forall a, (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
  shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
  aview SEGS (w_H W4) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite KM5. exact (KFRM a Ha). }
assert (SHR : forall lo hi vv, 0 <= lo -> hi <= 2048 ->
  sc_shr SEGS IM cx W3 mem3 lo hi vv -> sc_shr SEGS IM cx W4 (ms_mem ms1) lo hi vv).
{ intros lo hi vv Hlo Hhi Hsh o Ho. rewrite KFRMF; [exact (Hsh o Ho) | right; lia]. }
assert (OPEN : forall off len, 0 <= off -> 0 <= len -> off + len <= 16384 ->
  sc_open SEGS IM cx W3 mem3 off len -> sc_open SEGS IM cx W4 (ms_mem ms1) off len).
{ intros off len Ho Hl Hol (Hp & Hn & Hc). split; [exact Hp|]. split; [exact Hn|].
  intros i Hi. rewrite KFRMF; [exact (Hc i Hi)|]. right.
  exact (s4_open_idx (sc_F SEGS IM cx) off len i HF8 Hp Ho Hl Hol Hi). }
(* the read-only bytes: the entry's, through the journal (SceneBase.v arodata_ok_journalP) *)
assert (HROF : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W4) (ms_mem ms1))).
{ pose proof HROD0 as HR0. rewrite HWRLO, HWRHI in HR0 |- *.
  exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HR0). }
(* the frame's bytes and shadow are present at the final state: AR's frame law there *)
pose proof (al_frames _ _ LAWS ly4 S4 W4 (ms_mem ms1) _ 8 (c_fpos cx) (proj1 HJ4) Hown4) as (_ & _ & HFb4 & HFsh4).
(* the registers after the ld *)
pmkst HS3.
prreg_raw HS3 (24%bv : bv 5) G24. prreg_raw HS3 (2%bv : bv 5) G2. prreg_raw HS3 (3%bv : bv 5) G3.
prreg_raw HS3 (4%bv : bv 5) G4. prreg_raw HS3 (8%bv : bv 5) G8. prreg_raw HS3 (9%bv : bv 5) G9.
prreg_raw HS3 (19%bv : bv 5) G19. prreg_raw HS3 (20%bv : bv 5) G20.
assert (V24 : getr (ms_regs ms1) (24%bv : bv 5) = w64 8904).
{ rewrite G24; cbn [sv_denot]; unfold w64;
  first [reflexivity | (f_equal; rewrite zcanon_id by (unfold M64; lia); reflexivity)]. }
assert (VspZ : spZ (ms_regs ms1) = c_sp1 cx).
{ unfold spZ. rewrite G2. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 2%nat (2%bv : bv 5) eq_refl), Q2c.
  rewrite Z_to_bv_bv_unsigned. unfold w64. apply unsigned_lit_small. lia. }
assert (V3 : getr (ms_regs ms1) (3%bv : bv 5) = w64 (as_gp B)).
{ rewrite G3. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 3%nat (3%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q3c. }
assert (V4 : getr (ms_regs ms1) (4%bv : bv 5) = w64 (as_tp B)).
{ rewrite G4. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 4%nat (4%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q4c. }
assert (V8 : getr (ms_regs ms1) (8%bv : bv 5) = w64 (spZ (c_regs cx))).
{ rewrite G8. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 8%nat (8%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q8c. }
assert (V9 : getr (ms_regs ms1) (9%bv : bv 5) = w64 (c_sp1 cx)).
{ rewrite G9. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 9%nat (9%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q9c. }
assert (V19 : getr (ms_regs ms1) (19%bv : bv 5) = w64 (shadow_addr (sc_F SEGS IM cx))).
{ rewrite G19. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 19%nat (19%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q19c. }
assert (V20 : getr (ms_regs ms1) (20%bv : bv 5) = w64 body).
{ rewrite G20. cbn [sv_denot]. rewrite Z.add_0_r, (EE4 20%nat (20%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Q20c. }
(* ---- the cut C5 at 0x82fa4, ev = 3 ---- *)
assert (HNP : sc_nprime IM bs = 8904) by exact (proj2 Hwhole).
assert (HNN : sc_nn IM bs = 8904) by (unfold sc_nn; rewrite HNP; reflexivity).
replace (Z_to_bv 64 (BASE + 1792)) with (w64 (sg_pc_c5 IM))
  by (cbn [sg_pc_c5 scene_geom_asan_ubsan]; unfold w64, SEG_C5_off, AF_LLVMFuzzerTestOneInput; f_equal; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) ?MD) _ =>
  change (SRr SEGS W4 (cfg_at SEGS (sg_pc_c5 IM) R M MD) POST);
  apply (HC5 ly4 S4 W4 R M MD bs body b 3) end.
unfold cut_C5.
split; [lia|].
split; [split; [exact HJ4 | split; [rewrite Hfrs4; exact Hfrs3 | exact I]]|].
split; [rewrite HNN; exact HPERM|].
split; [rewrite HNN; exact HBB4|].
split; [rewrite HNN; exact HokB|].
split; [rewrite HNN; exact Hlenb|].
split.
{ apply (s4_garr8_moved W3 W4 mem3 (ms_mem ms1) body (u8s b)); [| exact Hgb].
  intros j Hj. unfold u8s in Hj. rewrite length_map, Hlenb in Hj. rewrite KM5. apply KBLK. lia. }
split.
{ pose proof Hfrm as (Hflag & _ & _).
  split; [| split].
  - rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W4) (ms_mem ms1)) _); [exact Hflag|].
    intros kk Hkk. apply KFRMF. left. change (fs_frame_bytes (sg_cid IM)) with 16384. lia.
  - intros a Ha. rewrite <- EF4 in Ha. exact (proj1 (HFb4 a Ha)).
  - intros a Ha. change (fs_frame_bytes (sg_cid IM) / 8) with 2048 in Ha. rewrite <- EF4 in Ha.
    assert (Hi : 0 <= a - shadow_addr (frame_addr ly4 8 (c_fpos cx)) < fs_frame_bytes 8 / 8)
      by (change (fs_frame_bytes 8 / 8) with 2048; lia).
    pose proof (proj1 (HFsh4 _ Hi)) as Hq.
    replace (shadow_addr (frame_addr ly4 8 (c_fpos cx)) + (a - shadow_addr (frame_addr ly4 8 (c_fpos cx))))
      with a in Hq by lia.
    exact Hq. }
split; [intros j Hj; apply SPILLF; [lia | lia | exact (Hsav j Hj)]|].
split.
{ unfold sc_shbg in Hshbg |- *. rewrite Forall_forall in Hshbg |- *. intros t Ht.
  pose proof (Hshbg t Ht) as Ht'.
  cbn [sg_sh_bg scene_geom_asan_ubsan In] in Ht.
  apply SHR; [| | exact Ht'];
  repeat (destruct Ht as [<- | Ht]; [cbn [fst snd]; lia |]); destruct Ht. }
split; [apply SHR; [cbn; lia | cbn; lia | exact Hshblki]|].
split; [apply OPEN; [cbn; lia | cbn; lia | cbn; lia | exact HopB]|].
split; [apply OPEN; [cbn; lia | cbn; lia | cbn; lia | exact HopM]|].
split; [split; [exact VspZ | split; [exact V3 | split; [exact V4 | exact HROF]]]|].
split; [exact Hinput|].
split; [rewrite HNN; lia|].
split.
{ apply (s4_garr8_moved W3 W4 mem3 (ms_mem ms1) _ (sc_macb bs)); [| exact Hmacb].
  intros j Hj. unfold sc_macb in Hj. cbn [length] in Hj. apply KFRMF. left.
  change (sg_off_mac IM) with 112. lia. }
split; [change (sg5_sp0 IM) with (VReg RV_s0); cbn [vat]; exact V8|].
split; [change (sg5_sp1 IM) with (VReg RV_s1); cbn [vat]; exact V9|].
split; [change (sg5_F IM) with (VSpill 0x18); cbn [vat]; apply SPILLF; [lia | lia | exact RFsp]|].
split; [change (sg5_Fsp IM) with (VSpill 0x28); cbn [vat]; apply SPILLF; [lia | lia | exact RFb]|].
split; [change (sg5_shF IM) with (VReg RV_s3); cbn [vat]; exact V19|].
split; [change (sg5_expect IM) with (VSpill 0x30); cbn [vat]; apply SPILLF; [lia | lia | exact Rexp]|].
split; [change (sg5_mac IM) with (VSpill 0x38); cbn [vat]; apply SPILLF; [lia | lia | exact Rmac]|].
split; [change (sg5_shexp IM) with (VSpill 0x10); cbn [vat]; apply SPILLF; [lia | lia | exact Rshexp]|].
split; [change (sg5_body IM) with (VReg RV_s4); cbn [vat]; exact V20|].
split; [change (sg5_nn IM) with (VSpill 0x20); cbn [vat]; apply SPILLF; [lia | lia | exact Rnn]|].
rewrite HNP. change (sg5_nprime IM) with (VReg RV_s8). cbn [vat]. exact V24.
Qed.

(* ================================================================================================
   THE NO-T ARM'S CUT C5.  Both no-T arms (`beqz a0` 0x82e58, `bne s8,a0` 0x82e64) reach 0x82fa4 with
   the cut C3's layout, state and world, a memory that differs from C3's at most in the two spill windows
   the T arm writes ([sp1+8, sp1+16) and [sp1+64, sp1+96)), the journal still at ev = 1, and the registers
   C5 names untouched.  So cut_C5 is cut_C3 read back, and the `sc_from_C5` hypothesis closes the arm.
   ================================================================================================ *)
Lemma s4_C5_of_C3 : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop)
  ly3 S3 (W3 : world SEGS) regs3 mem3 md3 bs body bb,
sc_base SEGS B ameter_triv WK cx ->
sc_from_C5 (SK := SK) SEGS B ameter_triv WK IM cx POST ->
cut_C3 (SK := SK) SEGS B ameter_triv WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ->
forall (regs' : bvmap 5 word) mem' md',
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly3 S3 W3 mem' md' 1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
getr regs' 2 = w64 (c_sp1 cx) -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
getr regs' 8 = w64 (spZ (c_regs cx)) -> getr regs' 9 = w64 (c_sp1 cx) ->
getr regs' 19 = w64 (shadow_addr (sc_F SEGS IM cx)) -> getr regs' 20 = w64 body ->
getr regs' 24 = w64 (sc_nprime IM bs) ->
SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 1792)) mem' (seg_rom SEGS)) md') POST.
Proof.
intros cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb HBASE HC5 HC3 regs' mem' md' HJx KH
  X2 X3 X4 X8 X9 X19 X20 X24.
pose proof HBASE as (HBASE0 & HSP1).
pose proof HBASE0 as (HPRE & HraW & Hp10 & Hp11 & Hpn0 & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK0 & Hfd0 & Hfs0 & HMO0).
pose proof HPRE as (HAR0 & Hra & Hra0 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HWSTK as HSTKb. unfold S4_SPDROP in HSTKb.
assert (HAS : ASTACK = 16384) by reflexivity.
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
assert (HSP1b : spZ (c_regs cx) - 240 <= c_sp1 cx <= spZ (c_regs cx) - 224) by (destruct HO; lia).
destruct HC3 as (HJj & Hab & Hbbnd & HokB & Hlenbb & Hgb & Hfrm & Hsav & Hshbg & Hshblki & HopB & HopM &
  Himg & Hinput & Hnnb & Hmacb & Rsp0 & Rsp1 & RF & RFb & RFsp & RshF & Rblki & Rexp & Rmac & Rshexp &
  Rbody & Rnn & Rnprime & Rflags & Rstep).
pose proof HJj as (HJ & Hfrs3 & Hmle).
pose proof HJ as (HAR3 & Hly & _).
pose proof HokB as (HB4096 & HBzone & HBceil & HB16 & HBwr & HBftok).
assert (Hrq : sc_nn IM bs <= req_size (sc_nn IM bs))
  by (unfold req_size; destruct (Z.eqb_spec (sc_nn IM bs) 0); lia).
s4v RF. s4v RFsp. s4v RFb. s4v Rexp. s4v Rmac. s4v Rshexp. s4v Rnn.
change (sg_cid IM) with 8 in *.
assert (Hown3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HFB : fs_frame_bytes 8 = 16384) by reflexivity.
assert (EF3 : frame_addr ly3 8 (c_fpos cx) = sc_F SEGS IM cx).
{ unfold sc_F, rt_F, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (HF32 & _ & _ & _).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (HF4096 & HFceil & _).
rewrite EF3 in HF32, HF4096, HFceil. rewrite HFB in HFceil.
assert (HSL : 2147450880 <= shadow_addr (sc_F SEGS IM cx) /\ shadow_addr (sc_F SEGS IM cx) + 2048 <= 17594333462528).
{ apply s4_shadow_lo; [exact HF4096 | lia]. }
assert (HF8 : sc_F SEGS IM cx mod 8 = 0).
{ revert HF32. generalize (sc_F SEGS IM cx). clear. intros F HF. Z.div_mod_to_equations. lia. }
(* every address C5 reads, outside the two spill windows: the cut's byte *)
assert (KLO : forall a, 0 <= a < c_sp1 cx -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply KH; lia. }
assert (SPILL : forall aa vv, c_sp1 cx + 16 <= aa -> aa + 8 <= c_sp1 cx + 64 \/ c_sp1 cx + 96 <= aa ->
  aa + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) mem3) aa = Some vv -> rdword (aview SEGS (w_H W3) mem') aa = Some vv).
{ intros aa vv Hsa Hsb Hs64 Hsr.
  rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem') aa); [exact Hsr|].
  intros kk Hkk. apply KH; lia. }
assert (KFRM : forall a, (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
  shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
  aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply KLO. lia. }
assert (SHR : forall lo hi vv, 0 <= lo -> hi <= 2048 ->
  sc_shr SEGS IM cx W3 mem3 lo hi vv -> sc_shr SEGS IM cx W3 mem' lo hi vv).
{ intros lo hi vv Hlo Hhi Hsh o Ho. rewrite KFRM; [exact (Hsh o Ho) | right; lia]. }
assert (OPEN : forall off len, 0 <= off -> 0 <= len -> off + len <= 16384 ->
  sc_open SEGS IM cx W3 mem3 off len -> sc_open SEGS IM cx W3 mem' off len).
{ intros off len Ho Hl Hol (Hp & Hn & Hc). split; [exact Hp|]. split; [exact Hn|].
  intros i Hi. rewrite KFRM; [exact (Hc i Hi)|]. right.
  exact (s4_open_idx (sc_F SEGS IM cx) off len i HF8 Hp Ho Hl Hol Hi). }
assert (HROF : arodata_okS SEGS B (sw_rlo WK) (sw_rhi WK) (aview SEGS (w_H W3) mem')).
{ pose proof HROD0 as HR0. rewrite HWRLO, HWRHI in HR0 |- *.
  exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HR0). }
pose proof (al_frames _ _ LAWS ly3 S3 W3 mem' md' 8 (c_fpos cx) (proj1 HJx) Hown3) as (_ & _ & HFb' & HFsh').
assert (VspZ : spZ regs' = c_sp1 cx) by (unfold spZ; rewrite X2; unfold w64; apply unsigned_lit_small; lia).
(* ---- the cut C5 at 0x82fa4, ev = 1 ---- *)
replace (Z_to_bv 64 (BASE + 1792)) with (w64 (sg_pc_c5 IM))
  by (cbn [sg_pc_c5 scene_geom_asan_ubsan]; unfold w64, SEG_C5_off, AF_LLVMFuzzerTestOneInput; f_equal; lia).
change (SRr SEGS W3 (cfg_at SEGS (sg_pc_c5 IM) regs' mem' md') POST).
apply (HC5 ly3 S3 W3 regs' mem' md' bs body bb 1).
unfold cut_C5.
split; [lia|].
split; [split; [exact HJx | split; [exact Hfrs3 | exact I]]|].
split; [rewrite Hab; apply Permutation_refl|].
split; [exact Hbbnd|].
split; [exact HokB|].
split; [exact Hlenbb|].
split.
{ apply (s4_garr8_moved W3 W3 mem3 mem' body (u8s bb)); [| exact Hgb].
  intros j Hj. unfold u8s in Hj. rewrite length_map, Hlenbb in Hj. apply KLO. lia. }
split.
{ pose proof Hfrm as (Hflag & _ & _).
  split; [| split].
  - rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem') _); [exact Hflag|].
    intros kk Hkk. apply KFRM. left. change (fs_frame_bytes (sg_cid IM)) with 16384. lia.
  - intros a Ha. rewrite <- EF3 in Ha. exact (proj1 (HFb' a Ha)).
  - intros a Ha. change (fs_frame_bytes (sg_cid IM) / 8) with 2048 in Ha. rewrite <- EF3 in Ha.
    assert (Hi : 0 <= a - shadow_addr (frame_addr ly3 8 (c_fpos cx)) < fs_frame_bytes 8 / 8)
      by (change (fs_frame_bytes 8 / 8) with 2048; lia).
    pose proof (proj1 (HFsh' _ Hi)) as Hq.
    replace (shadow_addr (frame_addr ly3 8 (c_fpos cx)) + (a - shadow_addr (frame_addr ly3 8 (c_fpos cx))))
      with a in Hq by lia.
    exact Hq. }
split; [intros j Hj; apply SPILL; [lia | right; lia | lia | exact (Hsav j Hj)]|].
split.
{ unfold sc_shbg in Hshbg |- *. rewrite Forall_forall in Hshbg |- *. intros t Ht.
  pose proof (Hshbg t Ht) as Ht'.
  cbn [sg_sh_bg scene_geom_asan_ubsan In] in Ht.
  apply SHR; [| | exact Ht'];
  repeat (destruct Ht as [<- | Ht]; [cbn [fst snd]; lia |]); destruct Ht. }
split; [apply SHR; [cbn; lia | cbn; lia | exact Hshblki]|].
split; [apply OPEN; [cbn; lia | cbn; lia | cbn; lia | exact HopB]|].
split; [apply OPEN; [cbn; lia | cbn; lia | cbn; lia | exact HopM]|].
split; [split; [exact VspZ | split; [exact X3 | split; [exact X4 | exact HROF]]]|].
split; [exact Hinput|].
split; [exact Hnnb|].
split.
{ apply (s4_garr8_moved W3 W3 mem3 mem' _ (sc_macb bs)); [| exact Hmacb].
  intros j Hj. unfold sc_macb in Hj. cbn [length] in Hj. apply KFRM. left.
  change (sg_off_mac IM) with 112. lia. }
split; [change (sg5_sp0 IM) with (VReg RV_s0); cbn [vat]; exact X8|].
split; [change (sg5_sp1 IM) with (VReg RV_s1); cbn [vat]; exact X9|].
split; [change (sg5_F IM) with (VSpill 0x18); cbn [vat]; apply SPILL; [lia | left; lia | lia | exact RF]|].
split; [change (sg5_Fsp IM) with (VSpill 0x28); cbn [vat]; apply SPILL; [lia | left; lia | lia | exact RFsp]|].
split; [change (sg5_shF IM) with (VReg RV_s3); cbn [vat]; exact X19|].
split; [change (sg5_expect IM) with (VSpill 0x30); cbn [vat]; apply SPILL; [lia | left; lia | lia | exact Rexp]|].
split; [change (sg5_mac IM) with (VSpill 0x38); cbn [vat]; apply SPILL; [lia | left; lia | lia | exact Rmac]|].
split; [change (sg5_shexp IM) with (VSpill 0x10); cbn [vat]; apply SPILL; [lia | left; lia | lia | exact Rshexp]|].
split; [change (sg5_body IM) with (VReg RV_s4); cbn [vat]; exact X20|].
split; [change (sg5_nn IM) with (VSpill 0x20); cbn [vat]; apply SPILL; [lia | left; lia | lia | exact Rnn]|].
change (sg5_nprime IM) with (VReg RV_s8). cbn [vat]. exact X24.
Qed.

(* ================================================================================================
   THE HEAD, 0x82e50 .. 0x82ea8: the guard `flags & 2` and `n' = 8904`, the malloc at 0x82e6c, its
   null test and the loop entry at k = 0; and the two no-T arms, which jump straight to C5.
   ================================================================================================ *)
(* the two windows of the spill frame this segment writes: [sp1+8, sp1+16) (n' at 0x82e68) and
   [sp1+64, sp1+96) (declared 0x40, blk.i+7 0x48, ~again 0x50, again 0x58).  The slots the cut of C5
   and the cut of T read back -- 0x10, 0x18, 0x20, 0x28, 0x30, 0x38 -- lie between them and are kept
   by every run's `frame_of`. *)
Definition s4h_R8 : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 8 16 [].
Definition s4h_Rhi : YP09.region :=
YP09.mkRegion (Some 9%nat) 64 96 64 96 [YP09.mkChunk 88 (CVal 8 (SOff 32 0))].
Definition s4h_Rhi2 : YP09.region := YP09.mkRegion (Some 9%nat) 64 96 64 96 [].
(* a run keeps every byte outside its regions' write windows *)
Lemma s4h_keep : forall (W : world SEGS) E (rs : smem) (m m' : word -> option byte),
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W E rs m m' HF a Ha Hn. apply (aview_eq_of SEGS). apply (HF (Z_to_bv 64 a)).
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* the write permission of this segment's runs: one stack region at a negative offset from sp0 *)
Local Ltac s4h_awr U9x d :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp fp b0 bc lyx own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat d);
  [reflexivity | cbn [ew ewset Nat.eqb]; rewrite U9x; lia
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].
(* one more run, on the same two windows: carry a `kept outside the windows` fact across it *)
Local Ltac s4h_step Ex KEEPprev HFrx U9x :=
let a := fresh "a" in let Ha := fresh "Ha" in let N1 := fresh "N1" in let N2 := fresh "N2" in
intros a Ha N1 N2;
rewrite (s4h_keep _ Ex [s4h_R8; s4h_Rhi] _ _ HFrx a Ha
ltac:(let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbv [s4h_R8 s4h_Rhi] in Hin; cbn [In] in Hin;
destruct Hin as [<- | [<- | []]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U9x in Hr; [apply N1 | apply N2]; lia));
apply KEEPprev; assumption.
(* a callee-saved register of the run's final state, against the value the cut gives it *)
Local Ltac s4h_regv HSx EEx n r Hf :=
let Hr := fresh "Hr" in prreg_raw HSx r Hr; rewrite Hr; cbn [sv_denot];
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEx n r eq_refl); exact Hf.
Local Ltac s4h_regsp HSx EEx Hsp :=
let Hr := fresh "Hr" in prreg_raw HSx (2%bv : bv 5) Hr; rewrite Hr; cbn [sv_denot];
rewrite Z.add_0_r, (EEx 2%nat (2%bv : bv 5) eq_refl);
unfold spZ in Hsp; unfold w64; rewrite <- Hsp; apply bv_eq; rewrite Z_to_bv_unsigned;
unfold bv_wrap; rewrite Z.mod_small; [reflexivity | apply bv_unsigned_in_range].
(* the same, generic in the regions the run started from (a run that stored leaves its chunk behind) *)
Local Ltac s4h_step2 Ex KEEPprev HFrx U9x :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; intros;
rewrite (s4h_keep _ Ex _ _ _ HFrx a Ha
ltac:(let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U9x in Hr; lia |]);
destruct Hin));
apply KEEPprev; assumption.
(* `not a0` 0x82e94 (xori a0,a0,-1), as a value (cgif A/AE2y.v:419, :430, copied) *)
Lemma s4h_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|].
  apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (Eq : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite Eq.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma s4h_U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite s4h_lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). apply zcanon_id. unfold M64. lia.
Qed.
(* the shadow byte of a frame object, as an offset from the frame's shadow base *)
Lemma s4h_shoff : forall F off i, F mod 8 = 0 -> off mod 8 = 0 -> 0 <= off -> 0 <= i ->
shadow_of_addr SHADOW_OFF (F + off) + i = shadow_addr F + (off / 8 + i).
Proof.
intros F off i HF Hoff Ho Hi. unfold shadow_of_addr, shadow_addr.
assert (Hd : off = 8 * (off / 8)) by (apply (Z.div_exact off 8 ltac:(lia)); exact Hoff).
rewrite Hd at 1. rewrite (Z.mul_comm 8 (off / 8)), Z.div_add by lia. lia.
Qed.

(* ---- transporting the cut's memory clauses across a run or a call ---- *)
Lemma s4h_mbyte_of_aview : forall (W W' : world SEGS) (m m' : word -> option byte) a,
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a ->
mbyte SEGS (mrestrict (w_H W') m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
intros W W' m m' a H. unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W') m') a) as [b1|] eqn:E1;
destruct (mbyte SEGS (mrestrict (w_H W) m) a) as [b2|] eqn:E2; cbn in H; try discriminate; [| reflexivity].
f_equal. apply bv_eq. injection H as H. exact H.
Qed.
Lemma s4h_garr8_kept : forall (W W' : world SEGS) (m m' : word -> option byte) base l,
garr8 SEGS (mrestrict (w_H W) m) base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
garr8 SEGS (mrestrict (w_H W') m') base l.
Proof.
intros W W' m m' base l Hg HK. apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|].
intros a Ha. apply s4h_mbyte_of_aview. apply HK. exact Ha.
Qed.
Lemma s4h_u8s : forall l : list Z, bytes_ok l -> u8s (map (fun z : Z => Z_to_bv 8 z) l) = l.
Proof.
intros l H. unfold u8s. rewrite map_map. induction H as [|x l Hx Hl IH]; cbn [map]; [reflexivity|].
rewrite IH. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. lia.
Qed.
(* a fresh block's bytes, as a byte list: every byte of it is present *)
Lemma s4h_garr8_block : forall (W : world SEGS) (m : word -> option byte) base n,
(forall a, base <= a < base + n -> apresent (w_H W) m a) -> 0 <= n ->
exists l : list byte, Z.of_nat (length l) = n /\ garr8 SEGS (mrestrict (w_H W) m) base (u8s l).
Proof.
intros W m base n Hp Hn.
destruct (garr8_of_present SEGS (mrestrict (w_H W) m) base (Z.to_nat n)) as (l & Hl & Hg).
{ intros a Ha. destruct (Hp a ltac:(lia)) as (Hh & (b & Hb)). exists b. unfold mrestrict. rewrite Hh. exact Hb. }
exists (map (fun z : Z => Z_to_bv 8 z) l). split.
- rewrite length_map, Hl. lia.
- rewrite (s4h_u8s l (garr8_bytes_ok SEGS _ _ _ Hg)). exact Hg.
Qed.
(* the frame-shadow clauses of a cut *)
Lemma s4h_shr_kept : forall (cx' : rtcx SEGS) IMx (W W' : world SEGS) (m m' : word -> option byte) lo hi v,
(forall o, lo <= o < hi -> aview SEGS (w_H W') m' (shadow_addr (sc_F SEGS IMx cx') + o)
= aview SEGS (w_H W) m (shadow_addr (sc_F SEGS IMx cx') + o)) ->
sc_shr SEGS IMx cx' W m lo hi v -> sc_shr SEGS IMx cx' W' m' lo hi v.
Proof. intros cx' IMx W W' m m' lo hi v HK H o Ho. rewrite (HK o Ho). exact (H o Ho). Qed.
Lemma s4h_shbg_kept : forall (cx' : rtcx SEGS) IMx (W W' : world SEGS) (m m' : word -> option byte),
(forall o, 0 <= o < 2048 -> aview SEGS (w_H W') m' (shadow_addr (sc_F SEGS IMx cx') + o)
= aview SEGS (w_H W) m (shadow_addr (sc_F SEGS IMx cx') + o)) ->
Forall (fun t => 0 <= fst (fst t) /\ snd (fst t) <= 2048) (sg_sh_bg IMx) ->
sc_shbg SEGS IMx cx' W m -> sc_shbg SEGS IMx cx' W' m'.
Proof.
intros cx' IMx W W' m m' HK HB H. unfold sc_shbg in *. rewrite Forall_forall in *.
intros t Ht. pose proof (H t Ht) as Ht1. pose proof (HB t Ht) as (Hb1 & Hb2).
intros o Ho. rewrite (HK o ltac:(lia)). exact (Ht1 o Ho).
Qed.
(* a frame object whose shadow the walk has opened *)
Lemma s4h_open_kept : forall (cx' : rtcx SEGS) IMx (W W' : world SEGS) (m m' : word -> option byte) off len,
(forall o, 0 <= o < 2048 -> aview SEGS (w_H W') m' (shadow_addr (sc_F SEGS IMx cx') + o)
= aview SEGS (w_H W) m (shadow_addr (sc_F SEGS IMx cx') + o)) ->
sc_F SEGS IMx cx' mod 8 = 0 -> off mod 8 = 0 -> 0 <= off ->
(forall i, 0 <= i < (len + 7) / 8 -> 0 <= off / 8 + i < 2048) ->
sc_open SEGS IMx cx' W m off len -> sc_open SEGS IMx cx' W' m' off len.
Proof.
intros cx' IMx W W' m m' off len HK HF8 Hoff Ho Hb (Hp & Hn & Hc).
split; [exact Hp|]. split; [exact Hn|]. intros i Hi.
rewrite (s4h_shoff (sc_F SEGS IMx cx') off i HF8 Hoff Ho ltac:(lia)).
rewrite (HK (off / 8 + i) (Hb i Hi)).
rewrite <- (s4h_shoff (sc_F SEGS IMx cx') off i HF8 Hoff Ho ltac:(lia)).
exact (Hc i Hi).
Qed.
(* the cut's `vat` clause as a GOAL: reduce only the location, never the value *)
Local Ltac s4vg1 :=
lazymatch goal with |- vat _ _ _ _ _ ?l _ =>
let l' := eval cbn [scene_geom_asan_ubsan
sgT_got sgT_k sgT_shF sgT_sp1 sgT_sp0 sgT_blki sgT_srcA sgT_srcB sgT_f8 sgT_n1
sgT_again sgT_body sgT_decl sgT_nprime sgT_Fsp sgT_mac sgT_shexp sgT_expect sgT_Fb sgT_nn
RV_s0 RV_s1 RV_s2 RV_s3 RV_s4 RV_s5 RV_s6 RV_s7 RV_s8 RV_s9 RV_s10 RV_s11 RV_a1] in l in
change l with l'; cbn [vat] end.
Local Ltac s4h_inchunk := cbn [In]; repeat first [ (left; reflexivity) | right ].
(* a register goal `getr (ms_regs ms) r = _`, read off the final symbolic state with the goal's own `r` *)
Local Ltac s4h_greg HSx :=
lazymatch goal with |- getr _ ?r = _ =>
let Hr := fresh "Hr" in
lazymatch type of HSx with st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H Ex ssx ms r HSx) as Hr end;
lazymatch type of Hr with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in Hr end;
cbn [ms_regs restrict mkst] in Hr; rewrite Hr; cbn [sv_denot] end.




Lemma s4_head : forall (cx : rtcx SEGS) (POST : world SEGS -> config -> Prop),
sc_base SEGS B ameter_triv WK cx ->
sc_from_T (SK := SK) SEGS B ameter_triv WK IM cx POST 0 ->
sc_from_C5 (SK := SK) SEGS B ameter_triv WK IM cx POST ->
sc_from_C3 (SK := SK) SEGS B ameter_triv WK IM cx POST.
Proof.
intros cx POST HBASE HT0 HC5 ly3 S3 W3 regs3 mem3 md3 bs body bb HC3.
pose proof HBASE as (HBASE0 & HSP1).
pose proof HBASE0 as (HPRE & HraW & Hp10 & Hp11 & Hpn0 & Hfr0 & Hev0 & Hlive0 & HROD0 & HSINK0 & Hfd0 & Hfs0 & HMO0).
pose proof HPRE as (HAR0 & Hra & Hra0 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HWSTK as HSTKb. unfold S4_SPDROP in HSTKb.
assert (HO : c_sp1 cx = spZ (c_regs cx) - 224 \/ c_sp1 cx = spZ (c_regs cx) - 240).
{ revert HSP1 Hal16. clear. intros HSP1 Hal16. rewrite HSP1. Z.div_mod_to_equations. lia. }
pose proof HC3 as HC3c.
destruct HC3 as (HJj & Hab & Hbbnd & HokB & Hlenbb & Hgb & Hfrm & Hsav & Hshbg & Hshblki & HopB & HopM &
Himg & Hinput & Hnnb & Hmacb & Rsp0 & Rsp1 & RF & RFb & RFsp & RshF & Rblki & Rexp & Rmac & Rshexp &
Rbody & Rnn & Rnprime & Rflags & Rstep).
pose proof HJj as (HJ & Hfrs3 & Hmle).
pose proof Himg as (Hsp3 & Hgp3 & Htp3 & HROD3).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & Hnev3 & Hk3 & HK1 & HK2 & HK3 & HK4 & _ & HPRES3 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
change (sg_scene_n IM) with 8904 in *. change (sg_nturns IM) with 343 in *. change (sg_cid IM) with 8 in *.
s4v Rsp0. s4v Rsp1. s4v RF. s4v RFb. s4v RFsp. s4v RshF. s4v Rblki. s4v Rexp. s4v Rmac. s4v Rshexp.
s4v Rbody. s4v Rnn. s4v Rnprime. s4v Rflags. s4v Rstep.
destruct (Hinput 0 ltac:(lia)) as (Hb0 & _ & _).
(* ---- the symbolic state at 0x82e50 ---- *)
remember (Eimg (Ereg regs3 [Z_to_bv 64 (sc_flags bs)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx).
{ rewrite (EE 9%nat (9%bv : bv 5) eq_refl), Rsp1. unfold w64. apply unsigned_lit_small. lia. }
assert (U32 : bv_unsigned (ew E 32) = sc_flags bs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs3 _ 0).
  cbn [nth]. apply unsigned_lit_small. unfold sc_flags in *. lia. }
assert (HS : st_ok_pi SEGS VAL E
(mkSS (AF_LLVMFuzzerTestOneInput + SEG_C3_off) sr_atoms [s4h_R8; s4h_Rhi] None (mkFacts [] [] []))
(restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C3_off))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor]].
    + unfold region_ok, s4h_R8.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [| constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPRES3. lia.
    + unfold region_ok, s4h_Rhi.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply HPRES3. lia.
      * repeat constructor.
        apply (chunk_ok_val SEGS E _ _ 88 8%N (SOff 32 0) (sc_flags bs));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; unfold sc_flags in *; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS). exact Rflags.
  - cbv [s4h_R8 s4h_Rhi]. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. repeat split; try exact I. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
clear HE.
unfold cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
replace pcw with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + SEG_C3_off)))
by (cbn [sg_pc_c3 scene_geom_asan_ubsan]; unfold w64; f_equal; lia) end.
paj_run_shc RUNP RUNC HS HJ; [s4h_awr U9 (c_sp1 cx - spZ (c_regs cx)) |].
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha N1 N2. apply (s4h_keep W3 E [s4h_R8; s4h_Rhi] mem3 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbv [s4h_R8 s4h_Rhi] in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U9 in Hr; [apply N1 | apply N2]; lia. }
(* ---- the join at C5: both no-T arms reach 0x82fa4 with the same memory and the same registers, so the
   whole of cut_C5 is proved once, here ---- *)
assert (EXIT : forall regs' mem' md',
ajournal SEGS B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(8, c_fpos cx)] ly3 S3 W3 mem' md' 1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
getr regs' 2 = w64 (c_sp1 cx) -> getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
getr regs' 8 = w64 (spZ (c_regs cx)) -> getr regs' 9 = w64 (c_sp1 cx) ->
getr regs' 19 = w64 (shadow_addr (sc_F SEGS IM cx)) -> getr regs' 20 = w64 body ->
getr regs' 24 = w64 (sc_nprime IM bs) ->
SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 1792)) mem' (seg_rom SEGS)) md') POST).
{ intros regs' mem' md' HJx HKx X2' X3' X4' X8' X9' X19' X20' X24'.
  exact (s4_C5_of_C3 cx POST ly3 S3 W3 regs3 mem3 md3 bs body bb HBASE HC5 HC3c regs' mem' md' HJx HKx
    X2' X3' X4' X8' X9' X19' X20' X24'). }
psrr_branch_pi RUNP BR HS.
- (* the `beqz a0` 0x82e58 arm: flags & 2 = 0, straight to C5 *)
  paj_run_to_shc RUNTOP HS HJ 1792; [s4h_awr U9 (c_sp1 cx - spZ (c_regs cx)) |].
  pmkst HS.
  prreg_raw HS (2%bv : bv 5) X2. prreg_raw HS (3%bv : bv 5) X3. prreg_raw HS (4%bv : bv 5) X4.
  prreg_raw HS (8%bv : bv 5) X8. prreg_raw HS (9%bv : bv 5) X9. prreg_raw HS (19%bv : bv 5) X19.
  prreg_raw HS (20%bv : bv 5) X20. prreg_raw HS (24%bv : bv 5) X24.
  apply (EXIT (ms_regs ms0) (ms_mem ms0) _ HJ);
  [ intros a Ha N1 N2;
    rewrite (s4h_keep W3 E [s4h_R8; s4h_Rhi] (ms_mem ms) (ms_mem ms0) HFr0 a Ha
      ltac:(intros (r & Hin & Hr); cbv [s4h_R8 s4h_Rhi] in Hin; cbn [In] in Hin;
            destruct Hin as [<- | [<- | []]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U9 in Hr;
            [apply N1 | apply N2]; lia));
    apply KEEP1; assumption
  | rewrite X2; cbn [sv_denot]; rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl);
    unfold spZ in Hsp3; unfold w64; rewrite <- Hsp3; apply bv_eq; rewrite Z_to_bv_unsigned;
    unfold bv_wrap; rewrite Z.mod_small; [reflexivity | apply bv_unsigned_in_range]
  | rewrite X3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp3
  | rewrite X4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp3
  | rewrite X8; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 8%nat (8%bv : bv 5) eq_refl); exact Rsp0
  | rewrite X9; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 9%nat (9%bv : bv 5) eq_refl); exact Rsp1
  | rewrite X19; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 19%nat (19%bv : bv 5) eq_refl); exact RshF
  | rewrite X20; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 20%nat (20%bv : bv 5) eq_refl); exact Rbody
  | rewrite X24; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 24%nat (24%bv : bv 5) eq_refl); exact Rnprime ].
- (* flags & 2 <> 0: on to the `bne s8,a0` 0x82e64 *)
  paj_run_shc RUNP RUNC HS HJ; [s4h_awr U9 (c_sp1 cx - spZ (c_regs cx)) |].
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a) by (s4h_step E KEEP1 HFr0 U9).
  psrr_branch_pi RUNP BR HS.
  + (* n' <> 8904: the second no-T arm, also straight to C5 *)
    paj_run_to_shc RUNTOP HS HJ 1792; [s4h_awr U9 (c_sp1 cx - spZ (c_regs cx)) |].
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a) by (s4h_step E KEEP2 HFr1 U9).
    pmkst HS.
    apply (EXIT (ms_regs ms1) (ms_mem ms1) _ HJ);
    [ exact KEEP3
    | s4h_regsp HS EE Hsp3 | s4h_regv HS EE 3%nat (3%bv : bv 5) Hgp3 | s4h_regv HS EE 4%nat (4%bv : bv 5) Htp3
    | s4h_regv HS EE 8%nat (8%bv : bv 5) Rsp0 | s4h_regv HS EE 9%nat (9%bv : bv 5) Rsp1
    | s4h_regv HS EE 19%nat (19%bv : bv 5) RshF | s4h_regv HS EE 20%nat (20%bv : bv 5) Rbody
    | s4h_regv HS EE 24%nat (24%bv : bv 5) Rnprime ].
  + (* n' = 8904: the T arm.  `sd s8,8(s1)` 0x82e68 and the malloc at 0x82e6c *)
    paj_run_shc RUNP RUNC HS HJ; [s4h_awr U9 (c_sp1 cx - spZ (c_regs cx)) |].
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a) by (s4h_step E KEEP2 HFr1 U9).
    (* the two guards, as the facts `sc_whole` asks for *)
    assert (U24 : bv_unsigned (ew E 24) = 8904).
    { revert Hc0. rewrite branch_ne_U, U_SOff, U_SLit, Z.add_0_r. intros Hq.
      apply negb_false_iff, Z.eqb_eq in Hq.
      pose proof (bv_unsigned_in_range 64 (ew E 24)) as Hrg.
      change (bv_modulus 64) with (2 ^ 64) in Hrg.
      rewrite (zcanon_id (bv_unsigned (ew E 24))) in Hq by (unfold M64; lia).
      change (zcanon 8904) with 8904 in Hq. exact Hq. }
    assert (HNP : sc_nprime IM bs = 8904).
    { assert (Hb1 : 0 <= bs 1 < 256) by (destruct (Hinput 1 ltac:(lia)) as (H & _); exact H).
      assert (Hb2 : 0 <= bs 2 < 256) by (destruct (Hinput 2 ltac:(lia)) as (H & _); exact H).
      assert (Hrange : 0 <= sc_nprime IM bs <= 65535).
      { unfold sc_nprime, sc_u16. destruct (Z.land (bs 0) 1 =? 0); [lia |].
        change (sg_scene_n scene_geom_asan_ubsan) with 8904. lia. }
      revert U24. rewrite (EE 24%nat (24%bv : bv 5) eq_refl), Rnprime. unfold w64.
      rewrite unsigned_lit_small by lia. exact (fun H => H). }
    assert (HNN : sc_nn IM bs = 8904) by (unfold sc_nn; rewrite HNP; reflexivity).
    assert (HW2 : Z.land (bs 0) 2 <> 0).
    { intros HZ. revert Hc. rewrite branch_eq_U, U_SAlu, U_SOff, !U_SLit, U32, Z.add_0_r.
      cbn [zalu_raw]. rewrite (zcanon_id (sc_flags bs)) by (unfold M64, sc_flags in *; lia).
      change (zcanon 2) with 2. unfold sc_flags. rewrite HZ. cbn. discriminate. }
    (* the malloc of `again` at 0x82e6c *)
    pose proof (amalloc04_rule_triv SEGS B Hsegs ENVB LAWS ML AMALLOC) as MALLOC4.
    assert (HRS : req_size (sc_nn IM bs) = sc_nn IM bs)
    by (unfold req_size; destruct (Z.eqb_spec (sc_nn IM bs) 0); lia).
    pmkst HS.
    prreg_raw HS (10%bv : bv 5) Ma0. prreg_raw HS (1%bv : bv 5) Mra. prreg_raw HS (2%bv : bv 5) Msp.
    prreg_raw HS (3%bv : bv 5) Mgp. prreg_raw HS (4%bv : bv 5) Mtp. prreg_raw HS (8%bv : bv 5) Ms0.
    assert (Mspz : spZ (ms_regs ms1) = c_sp1 cx).
    { unfold spZ. rewrite Msp. cbn [sv_denot].
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 2%nat (2%bv : bv 5) eq_refl).
      unfold spZ in Hsp3. exact Hsp3. }
    assert (Ms0z : s0Z (ms_regs ms1) = spZ (c_regs cx)).
    { unfold s0Z. rewrite Ms0. cbn [sv_denot].
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 8%nat (8%bv : bv 5) eq_refl), Rsp0.
      unfold w64. apply unsigned_lit_small. lia. }
    assert (Mraz : raZ (ms_regs ms1) = BASE + 1484).
    { unfold raZ. rewrite Mra. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 1484).
      pose proof pa_B_ok as HBok. apply unsigned_lit_small. lia. }
    assert (M8 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx + 8) = Some 8904).
    { pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
      apply (rdword_of_val_mem SEGS); [| lia].
      eapply (field_of_region E _ 9%nat (c_sp1 cx) _ _ _ _ _ 8 8%N (SOff 24 0) 8904);
      [ exact HR0 | exact U9 | cbn [In]; left; reflexivity
      | cbn [sv_denot]; rewrite U24, Z.add_0_r; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
    assert (MSAV : sc_saves SEGS cx W3 (ms_mem ms1)).
    { intros j Hj.
      rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem ms1)));
      [exact (Hsav j Hj) | intros k Hk; apply KEEP3; lia]. }
    rewrite (pal_malloc B TL).
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (MALLOC4 W3 rg mm (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
        [(8, c_fpos cx)] ly3 S3 mdx 1 8904 (c_sp1 cx - spZ (c_regs cx))
        (Z_to_bv 64 (BASE + 1484)) (rt_ch cx)) end.
      - exact HJ.
      - rewrite Ma0. cbn [sv_denot]. reflexivity.
      - unfold MALLOC_MAX. lia.
      - rewrite HRS, HNN in Hbbnd. unfold LIVE_MAX in *. lia.
      - rewrite Mspz. lia.
      - destruct HO as [HOx | HOx]; rewrite HOx;
        [replace (spZ (c_regs cx) - 224 - spZ (c_regs cx)) with (-224) by lia
        |replace (spZ (c_regs cx) - 240 - spZ (c_regs cx)) with (-240) by lia]; reflexivity.
      - lia.
      - lia.
      - rewrite Mgp. cbn [sv_denot].
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl). exact Hgp3.
      - rewrite Mtp. cbn [sv_denot].
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl). exact Htp3.
      - rewrite Mra. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 1484). reflexivity.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - lia.
      - exact (s4_chain cx ly3 S3 W3 (ms_mem ms1) _ 1 (ms_regs ms1) HPRE HSP1 HJ MSAV Mspz Ms0z
          ltac:(rewrite Mraz; pose proof (pa_base_lo (PL := PL_scene)) as HBLO; lia)).
      - apply (HTRACE (pc_malloc_ra0 (as_code B)) (BASE + 1484) (ms_regs ms1) cx HraW Mraz).
        left. split; [reflexivity|]. right; left. unfold S4_malloc2_ra, AF_LLVMFuzzerTestOneInput. lia.
      - exact I. }
    cbv beta. intros W2 c2 Hwle2
      (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & H4096 & Habl2 & HKEPT & _).
    (* ---- after the malloc: the null test 0x82e74 and the loop entry 0x82e78 .. 0x82ea8 ---- *)
    assert (HRS8 : req_size 8904 = 8904) by reflexivity.
    assert (HinR : In (res, 8904) (ablocks B ly2 S2))
    by (rewrite Habl2; apply in_or_app; right; left; reflexivity).
    pose proof (proj1 HJ2) as HAR2.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res 8904 HAR2 HinR)
      as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrn).
    rewrite HRS8 in Hrceil, Hrapp, Hrpres.
    pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & Hnev2 & _ & HL1 & HL2 & HL3 & HL4 & _ & HPRES2 & _).
    pose proof HKEPT as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
    assert (HPr2 : forall (n : Z) (r : bv 5), acallee_saved n -> bv_unsigned r = n ->
    getr regs2 r = getr (ms_regs ms1) r).
    { intros n r Hn Hr. pose proof (HP2 n Hn) as HQ.
      replace (Z_to_bv 5 n) with r in HQ by (apply bv_eq; rewrite Z_to_bv_unsigned, Hr;
        unfold bv_wrap; rewrite Z.mod_small; [reflexivity | rewrite <- Hr; apply bv_unsigned_in_range]).
      exact HQ. }
    prreg_raw HS (9%bv : bv 5) Ms1r. prreg_raw HS (19%bv : bv 5) Ms3.
    prreg_raw HS (20%bv : bv 5) Ms4. prreg_raw HS (25%bv : bv 5) Ms9.
    assert (Q9 : getr regs2 (9%bv : bv 5) = w64 (c_sp1 cx)).
    { rewrite (HPr2 9 (9%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Ms1r. cbn [sv_denot].
      rewrite Z.add_0_r, (EE 9%nat (9%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rsp1. }
    assert (Q8 : getr regs2 (8%bv : bv 5) = w64 (spZ (c_regs cx))).
    { rewrite (HPr2 8 (8%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Ms0. cbn [sv_denot].
      rewrite Z.add_0_r, (EE 8%nat (8%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rsp0. }
    assert (Q19 : getr regs2 (19%bv : bv 5) = w64 (shadow_addr (sc_F SEGS IM cx))).
    { rewrite (HPr2 19 (19%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Ms3. cbn [sv_denot].
      rewrite Z.add_0_r, (EE 19%nat (19%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact RshF. }
    assert (Q20 : getr regs2 (20%bv : bv 5) = w64 body).
    { rewrite (HPr2 20 (20%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Ms4. cbn [sv_denot].
      rewrite Z.add_0_r, (EE 20%nat (20%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rbody. }
    assert (Q25 : getr regs2 (25%bv : bv 5) = w64 (sc_F SEGS IM cx + sg_off_blki IM)).
    { rewrite (HPr2 25 (25%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Ms9. cbn [sv_denot].
      rewrite Z.add_0_r, (EE 25%nat (25%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned. exact Rblki. }
    assert (Q3 : getr regs2 (3%bv : bv 5) = w64 (as_gp B)).
    { rewrite (HPr2 3 (3%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Mgp. cbn [sv_denot].
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl). exact Hgp3. }
    assert (Q4 : getr regs2 (4%bv : bv 5) = w64 (as_tp B)).
    { rewrite (HPr2 4 (4%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Mtp. cbn [sv_denot].
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl). exact Htp3. }
    assert (Q2 : getr regs2 (2%bv : bv 5) = w64 (c_sp1 cx)).
    { rewrite (HPr2 2 (2%bv : bv 5) ltac:(cbv [acallee_saved]; lia) eq_refl), Msp. cbn [sv_denot].
      rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl), Z_to_bv_bv_unsigned.
      unfold spZ in Hsp3. unfold w64. rewrite <- Hsp3. apply bv_eq. rewrite Z_to_bv_unsigned.
      unfold bv_wrap. rewrite Z.mod_small; [reflexivity | apply bv_unsigned_in_range]. }
    (* the symbolic state at 0x82e70 *)
    remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
    assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
    assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
    assert (U29 : bv_unsigned (ew E2 9) = c_sp1 cx).
    { rewrite (EE2 9%nat (9%bv : bv 5) eq_refl), Q9. unfold w64. apply unsigned_lit_small. lia. }
    assert (U210 : bv_unsigned (ew E2 10) = res).
    { rewrite (EE2 10%nat (10%bv : bv 5) eq_refl), Ha0. unfold w64. apply unsigned_lit_small.
      pose proof alloc_ceiling_lt as HAC. lia. }
    assert (HS2 : st_ok_pi SEGS VAL E2
    (mkSS (AF_LLVMFuzzerTestOneInput + 0x5cc) sr_atoms [s4h_Rhi2] None (mkFacts [] [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 1484)) mem2 (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - subst E2. apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - constructor; [| constructor]. unfold region_ok, s4h_Rhi2.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U29. split; [lia|]. split; [lia|]. split; [| constructor].
        intros o Ho. apply (apresent_writable SEGS). apply HPRES2. lia.
      - cbn [pairwise_disjoint all_disjoint]. tauto.
      - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
    clear HE2.
    paj_run_shc RUNP RUNC HS2 HJ2; [s4h_awr U29 (c_sp1 cx - spZ (c_regs cx)) |].
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
    aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha N2. apply (s4h_keep W2 E2 [s4h_Rhi2] mem2 (ms_mem ms2) HFr2 a Ha).
      intros (r & Hin & Hr). cbv [s4h_Rhi2] in Hin. cbn [In] in Hin.
      destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite U29 in Hr; apply N2; lia. }
    psrr_branch_pi RUNP BR HS2.
    * (* `beqz a0` 0x82e74: refuted by 4096 <= res *)
      exfalso.
      lazymatch goal with Hq : branch_taken BC_EQ _ _ = true |- _ => revert Hq end.
      rewrite branch_eq_U, U_SOff, U_SLit, Z.add_0_r, U210.
      rewrite (zcanon_id res) by (unfold M64; pose proof alloc_ceiling_lt as HAC; lia).
      change (zcanon 0) with 0. intros Hq. apply Z.eqb_eq in Hq. lia.
    * (* 0x82e78 .. 0x82ea8: the loop entry *)
      paj_run_to_shc RUNTOP HS2 HJ2 1544; [s4h_awr U29 (c_sp1 cx - spZ (c_regs cx)) |].
      assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
      aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a) by (s4h_step2 E2 KEEP4 HFr3 U29).
      (* ---- the frame and the two heap blocks, transported to the loop head ---- *)
      assert (Hown3 : In (8, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
      assert (Hown2 : In (8, c_fpos cx) (frames S2)) by (rewrite Hfrs2; exact Hown3).
      assert (EFR : forall cid pos, frame_addr ly3 cid pos = frame_addr (c_ly cx) cid pos).
      { destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly3 HAR0 Hly)
          as (_ & HFa & _). exact HFa. }
      assert (EFR2 : forall cid pos, frame_addr ly2 cid pos = frame_addr (c_ly cx) cid pos).
      { destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly2 HAR0 Hly2)
          as (_ & HFa & _). exact HFa. }
      assert (EFIM : sc_F SEGS IM cx = frame_addr (c_ly cx) 8 (c_fpos cx)) by reflexivity.
      assert (HFB : 4096 <= sc_F SEGS IM cx /\ sc_F SEGS IM cx + 16384 <= alloc_ceiling).
      { destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (H1 & H2 & _).
        change (fs_frame_bytes 8) with 16384 in H2. rewrite EFIM, <- (EFR 8 (c_fpos cx)).
        split; [exact H1 | exact H2]. }
      assert (HF32 : sc_F SEGS IM cx mod 32 = 0).
      { destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 8 (c_fpos cx) HAR3 Hown3) as (H1 & _).
        rewrite EFIM, <- (EFR 8 (c_fpos cx)). exact H1. }
      assert (HSH : forall o, 0 <= o < 2048 ->
      2147446784 < shadow_addr (sc_F SEGS IM cx) + o < 17594333495296 /\
      shadow_addr (sc_F SEGS IM cx) + o < alloc_ceiling).
      { intros o Ho. unfold shadow_addr, SHADOW_OFF. destruct HFB as (HFa1 & HFa2).
        split; [split|]; Z.div_mod_to_equations; lia. }
      assert (Hz2 : zone2 res (req_size 8904)).
      { apply zone2_of_app; [rewrite HRS8; exact Hrapp |].
        pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 res 8904 HAR2 HinR) as Hoff. exact Hoff. }
      rewrite HRS8 in Hz2. destruct Hz2 as (Hz2a & Hz2b).
      assert (HinB : In (body, sc_nn IM bs) (ablocks B ly3 S3))
      by (rewrite Hab; apply in_or_app; right; left; reflexivity).
      pose proof HokB as (HB4096 & HBzone & HBceil & HB16 & HBwr & HBftok).
      rewrite HRS, HNN in HBceil.
      assert (Hdis : body + 8904 <= res \/ res + 8904 <= body).
      { pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (body, 8904) (res, 8904)
          (ablocks B (c_ly cx) (c_S cx)) [] [] HAR2
          ltac:(rewrite Habl2, Hab, HNN, <- app_assoc; reflexivity)) as Hd.
        unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite HRS8 in Hd.
        destruct Hd as [Hd | Hd]; [left | right]; lia. }
      assert (HnB : forall i, 0 <= i < 8904 -> ~ (res <= body + i < res + 8904))
      by (intros i Hi; destruct Hdis as [Hd | Hd]; lia).
      (* the frame bytes and the frame shadow *)
      assert (Hfrdis : forall a, sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 ->
      ~ (res <= a < res + req_size 8904)).
      { intros a Ha Hin.
        pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res 8904 8 (c_fpos cx) HAR2 HinR Hown2) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (EFR2 8 (c_fpos cx)) in Hd.
        change (fs_frame_bytes 8) with 16384 in Hd. rewrite HRS8 in Hd, Hin. rewrite EFIM in Ha.
        destruct Hd as [Hd | Hd]; lia. }
      assert (KF : forall a,
      (sc_F SEGS IM cx <= a < sc_F SEGS IM cx + 16384 \/
       shadow_addr (sc_F SEGS IM cx) <= a < shadow_addr (sc_F SEGS IM cx) + 2048) ->
      aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W3) mem3 a).
      { assert (Hsh1 : 2147446784 < shadow_addr (sc_F SEGS IM cx))
        by (destruct (HSH 0 ltac:(lia)) as ((Hs1 & _) & _); lia).
        assert (Hsh2 : shadow_addr (sc_F SEGS IM cx) + 2047 < 17594333495296)
        by (destruct (HSH 2047 ltac:(lia)) as ((_ & Hs2) & _); lia).
        assert (Hsh3 : shadow_addr (sc_F SEGS IM cx) + 2047 < alloc_ceiling)
        by (destruct (HSH 2047 ltac:(lia)) as (_ & Hs3); lia).
        pose proof HFB as (HB1 & HB2).
        intros a Ha.
        assert (Hin4 : in_zr a (frame_rng ly3 (8, c_fpos cx)) \/
        in_zr a (shadow_addr (frame_addr ly3 8 (c_fpos cx)), fs_frame_bytes 8 / 8)).
        { destruct Ha as [Hx | Hx];
          [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite (EFR 8 (c_fpos cx)), <- EFIM;
             change (fs_frame_bytes 8) with 16384; lia
          |right; unfold in_zr; cbn [fst snd]; rewrite (EFR 8 (c_fpos cx)), <- EFIM;
             change (fs_frame_bytes 8 / 8) with 2048; lia]. }
        assert (HnE : ~ (res <= a < res + req_size 8904)).
        { destruct Ha as [Hx | Hx]; [exact (Hfrdis a Hx) |].
          rewrite HRS8. destruct Hz2b as [Hq | Hq]; lia. }
        assert (Hlo : 0 <= a) by (destruct Ha as [Hx | Hx]; lia).
        assert (Hhi : a < alloc_ceiling) by (destruct Ha as [Hx | Hx]; lia).
        rewrite (KEEP5 a ltac:(lia) ltac:(lia)).
        rewrite (KT4 8 (c_fpos cx) a Hown3 Hin4 HnE).
        apply KEEP3; lia. }
      (* every byte at or above the allocation ceiling outside the callee window and the two spill windows *)
      assert (KS : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp1 cx - ASTACK <= a < c_sp1 cx) ->
      ~ (c_sp1 cx + 8 <= a < c_sp1 cx + 16) -> ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
      aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W3) mem3 a).
      { intros a Ha N0 N1 N2.
        rewrite (KEEP5 a ltac:(lia) N2).
        rewrite (KT1 a Ha ltac:(replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia;
                                exact N0)).
        apply KEEP3; [lia | exact N1 | exact N2]. }
      (* body's bytes: the call keeps every block of the cut's state outside the new one *)
      assert (KB : forall i, 0 <= i < 8904 ->
      aview SEGS (w_H W2) (ms_mem ms3) (body + i) = aview SEGS (w_H W3) mem3 (body + i)).
      { intros i Hi.
        rewrite (KEEP5 (body + i) ltac:(lia) ltac:(lia)).
        rewrite (KT2 body (sc_nn IM bs) i HinB ltac:(rewrite HRS, HNN; lia)
          ltac:(rewrite HRS8; apply HnB; lia)).
        apply KEEP3; lia. }
      (* [sp1+8] was written before the call: kept by the call and by the last run *)
      assert (KS8 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp1 cx - ASTACK <= a < c_sp1 cx) ->
      ~ (c_sp1 cx + 64 <= a < c_sp1 cx + 96) ->
      aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms1) a).
      { intros a Ha N0 N2. rewrite (KEEP5 a ltac:(lia) N2). apply (KT1 a Ha).
        replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia. exact N0. }
      assert (HBB : blocks_bytes S2 = blocks_bytes S3 + 8904).
      { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly3 S3), Habl2, bsum_app.
        cbn [bsum fold_right snd]. lia. }
      pose proof (proj1 HJ2) as HARf.
      destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms3) _ 8 (c_fpos cx) HARf Hown2) as (_ & _ & HPF & HPS).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms3) _ res 8904 HARf HinR) as (_ & _ & _ & _ & HPR & _).
      rewrite HRS8 in HPR.
      assert (U28 : bv_unsigned (ew E2 8) = spZ (c_regs cx)).
      { rewrite (EE2 8%nat (8%bv : bv 5) eq_refl), Q8. unfold w64. apply unsigned_lit_small. lia. }
      assert (U220 : bv_unsigned (ew E2 20) = body).
      { rewrite (EE2 20%nat (20%bv : bv 5) eq_refl), Q20. unfold w64. apply unsigned_lit_small. lia. }
      assert (U225 : bv_unsigned (ew E2 25) = sc_F SEGS IM cx + sg_off_blki IM).
      { rewrite (EE2 25%nat (25%bv : bv 5) eq_refl), Q25. unfold w64. apply unsigned_lit_small.
        destruct HFB as (HFa1 & HFa2). change (sg_off_blki IM) with 32. lia. }
      pose proof (st_ok_pi_region_nth E2 _ _ 0%nat _ HS2 eq_refl) as HRfin. cbn [ms_mem restrict] in HRfin.
      pmkst HS2.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
      replace pcw with (w64 (sg_pc_t IM)) by (cbn [sg_pc_t scene_geom_asan_ubsan]; unfold w64; f_equal;
        unfold AF_LLVMFuzzerTestOneInput, SEG_T_off; lia) end.
      apply (HT0 ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) _ bs body res bb).
      unfold cut_T.
      (* k, the whole arm, the journal, the two blocks *)
      split; [cbn [sg_nturns scene_geom_asan_ubsan]; lia |].
      split; [split; [exact HW2 | exact HNP] |].
      split; [split; [exact HJ2 | split; [rewrite Hfrs2; exact Hfrs3 | exact I]] |].
      split; [rewrite Habl2, Hab, HNN; reflexivity |].
      split; [rewrite HBB; change (req_size (sg_scene_n IM)) with 8904; rewrite HRS, HNN in Hbbnd; lia |].
      split; [rewrite HNN in HokB; exact HokB |].
      split.
      { change (sg_scene_n IM) with 8904. unfold sc_blk_ok. rewrite HRS8.
        split; [exact Hr4096 |]. split; [split; [exact Hz2a | exact Hz2b] |].
        split; [exact Hrceil |]. split; [exact Hr16 |]. split.
        - intros blc lyq ownq i Hin Hi.
          exact (awr_new_block_any SEGS B LAWS (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
            (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 W3 (ms_mem ms1) _ 1 ly2 S2 W2 mem2 md2 res 8904
            blc i lyq ownq HJ HAR2 Habl2 ltac:(lia) Hin ltac:(rewrite HRS8; exact Hi)).
        - exact (aftok_new_block SEGS B LAWS (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
            (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly3 S3 W3 (ms_mem ms1) _ 1 ly2 S2 W2 mem2 md2 res 8904
            HJ HAR2 Habl2 ltac:(lia)). }
      split; [change (sg_scene_n IM) with 8904; destruct Hdis as [Hd | Hd]; [right | left]; lia |].
      split; [rewrite Hlenbb, HNN; reflexivity |].
      (* body's bytes *)
      split.
      { apply (s4h_garr8_kept W3 W2 mem3 (ms_mem ms3) body (u8s bb) Hgb).
        intros a Ha. unfold u8s in Ha. rewrite length_map, Hlenbb, HNN in Ha.
        replace a with (body + (a - body)) by lia. apply KB. lia. }
      (* `again`: nothing of b yet, and 8904 bytes of something *)
      split.
      { destruct (s4h_garr8_block W2 (ms_mem ms3) res 8904
          ltac:(intros a Ha; exact (proj1 (HPR a Ha))) ltac:(lia)) as (ja & Hjal & Hja).
        exists ja. rewrite scT_off_0. split; [rewrite Hjal; reflexivity |].
        cbn [Z.to_nat firstn app]. exact Hja. }
      (* the frame *)
      split.
      { pose proof Hfrm as (Hflag & _ & _). unfold sc_frame.
        change (fs_frame_bytes (sg_cid IM)) with 16384 in *. split; [| split].
        - rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
          [exact Hflag | intros k Hk; apply KF; left; destruct HFB as (HFa1 & HFa2); lia].
        - intros a Ha. change (fs_frame_bytes 8) with 16384 in HPF.
          apply (proj1 (HPF a ltac:(rewrite (EFR2 8 (c_fpos cx)), <- EFIM; lia))).
        - intros a Ha. change (fs_frame_bytes 8 / 8) with 2048 in HPS.
          rewrite (EFR2 8 (c_fpos cx)), <- EFIM in HPS.
          assert (HFB8 : fs_frame_bytes (sg_cid IM) / 8 = 2048) by reflexivity.
          assert (H16 : 16384 / 8 = 2048) by reflexivity.
          rewrite ?HFB8, ?H16 in Ha.
          assert (Hi : 0 <= a - shadow_addr (sc_F SEGS IM cx) < 2048) by lia.
          pose proof (proj1 (HPS _ Hi)) as Hp.
          replace (shadow_addr (sc_F SEGS IM cx) + (a - shadow_addr (sc_F SEGS IM cx))) with a in Hp by lia.
          exact Hp. }
      split.
      { intros j Hj.
        rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact (Hsav j Hj) | intros k Hk; apply KS; lia]. }
      split.
      { apply (s4h_shbg_kept cx IM W3 W2 mem3 (ms_mem ms3)); [| | exact Hshbg].
        - intros o Ho. apply KF. right. lia.
        - cbn [sg_sh_bg scene_geom_asan_ubsan]. repeat constructor; cbn [fst snd]; lia. }
      split.
      { apply (s4h_shr_kept cx IM W3 W2 mem3 (ms_mem ms3)); [| exact Hshblki].
        intros o Ho. apply KF. right. cbn [sg_sh_blki_lo sg_sh_blki_hi scene_geom_asan_ubsan] in Ho. lia. }
      split.
      { apply (s4h_open_kept cx IM W3 W2 mem3 (ms_mem ms3)); [ | | | | | exact HopB].
        - intros o Ho. apply KF. right. lia.
        - rewrite <- (Z.mod_mod_divide (sc_F SEGS IM cx) 32 8) by (exists 4; reflexivity). rewrite HF32. reflexivity.
        - reflexivity.
        - cbn. lia.
        - intros i Hi. change ((sg_blk_n IM + 7) / 8) with 5 in Hi. change (sg_off_blk IM / 8) with 18. lia. }
      split.
      { apply (s4h_open_kept cx IM W3 W2 mem3 (ms_mem ms3)); [ | | | | | exact HopM].
        - intros o Ho. apply KF. right. lia.
        - rewrite <- (Z.mod_mod_divide (sc_F SEGS IM cx) 32 8) by (exists 4; reflexivity). rewrite HF32. reflexivity.
        - reflexivity.
        - cbn. lia.
        - intros i Hi. change ((sg_mac_n IM + 7) / 8) with 1 in Hi. change (sg_off_mac IM / 8) with 14. lia. }
      (* the machine and the read-only bytes *)
      split.
      { split; [| split; [| split]].
        - unfold spZ. prreg_raw HS2 (2%bv : bv 5) Z2. rewrite Z2. cbn [sv_denot].
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 2%nat (2%bv : bv 5) eq_refl), Q2.
          unfold w64. apply unsigned_lit_small. lia.
        - prreg_raw HS2 (3%bv : bv 5) Z3. rewrite Z3. cbn [sv_denot].
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 3%nat (3%bv : bv 5) eq_refl). exact Q3.
        - prreg_raw HS2 (4%bv : bv 5) Z4. rewrite Z4. cbn [sv_denot].
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 4%nat (4%bv : bv 5) eq_refl). exact Q4.
        - rewrite HWRLO, HWRHI.
          apply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B (sw_stk WK) (spZ (c_regs cx)) []
            (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(8, c_fpos cx)] ly2 S2 W2 (ms_mem ms3) _ 2 HJ2).
          rewrite HWRLO, HWRHI in HROD0. exact HROD0. }
      split; [exact Hinput |].
      split.
      { apply (s4h_garr8_kept W3 W2 mem3 (ms_mem ms3) _ _ Hmacb).
        intros a Ha. cbn [sc_macb length Z.of_nat Pos.of_succ_nat] in Ha. apply KF. left.
        change (sg_off_mac IM) with 112 in Ha. destruct HFB as (HFa1 & HFa2). lia. }
      (* the registers and spill slots of the loop head *)
      split.
      { s4vg1. s4h_greg HS2.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 8%nat (8%bv : bv 5) eq_refl). exact Q8. }
      split.
      { s4vg1. s4h_greg HS2.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 9%nat (9%bv : bv 5) eq_refl). exact Q9. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact RF | intros k Hk; apply KS; lia]. }
      split.
      { s4vg1. s4h_greg HS2.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 19%nat (19%bv : bv 5) eq_refl). exact Q19. }
      split.
      { s4vg1. s4h_greg HS2.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 25%nat (25%bv : bv 5) eq_refl). exact Q25. }
      split.
      { s4vg1. apply (rdword_of_val_mem SEGS);
        [| destruct HFB as (HFa1 & HFa2); change (sg_off_blki IM) with 32; lia].
        eapply (field_of_region E2 _ 9%nat (c_sp1 cx) _ _ _ _ _ 72 8%N (SOff 25 7)
          (sc_F SEGS IM cx + sg_off_blki IM + 7));
        [ exact HRfin | exact U29 | s4h_inchunk | cbn [sv_denot]; rewrite U225; reflexivity
        | change (8 * Z.of_N 8) with 64; destruct HFB as (HFa1 & HFa2); change (sg_off_blki IM) with 32; lia
        | cbn; lia ]. }
      split.
      { s4vg1. s4h_greg HS2. rewrite U225. reflexivity. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact Rmac | intros k Hk; apply KS; lia]. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact Rshexp | intros k Hk; apply KS; lia]. }
      split.
      { s4vg1. s4h_greg HS2.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 20%nat (20%bv : bv 5) eq_refl). exact Q20. }
      split.
      { s4vg1. apply (rdword_of_val_mem SEGS); [| lia].
        eapply (field_of_region E2 _ 9%nat (c_sp1 cx) _ _ _ _ _ 88 8%N (SOff 10 0) res);
        [ exact HRfin | exact U29 | s4h_inchunk | cbn [sv_denot]; rewrite U210, Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms1)) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact M8 | intros k Hk; apply KS8; lia]. }
      split.
      { s4vg1. s4h_greg HS2. rewrite scT_off_0. reflexivity. }
      split.
      { s4vg1. s4h_greg HS2. reflexivity. }
      split.
      { s4vg1. cbn [Z.eqb]. apply (rdword_of_val_mem SEGS); [| lia].
        eapply (field_of_region E2 _ 9%nat (c_sp1 cx) _ _ _ _ _ 64 8%N (SLit 0) 0);
        [ exact HRfin | exact U29 | s4h_inchunk | cbn [sv_denot]; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
      split.
      { s4vg1. s4h_greg HS2. reflexivity. }
      split; [change (sgT_extra IM) with (@nil (vloc * Z)); apply Forall_nil |].
      split.
      { change (sgT_nagain IM) with (Some (VSpill 0x50)). cbn [vat].
        apply (rdword_of_val_mem SEGS); [| lia].
        eapply (field_of_region E2 _ 9%nat (c_sp1 cx) _ _ _ _ _ 80 8%N (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))
          (2 ^ 64 - 1 - res));
        [ exact HRfin | exact U29 | s4h_inchunk
        | rewrite denot_lit_U, s4h_U_not, U_SOff, U210, Z.add_0_r, (zcanon_id res) by (unfold M64; lia);
          reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact Rexp | intros k Hk; apply KS; lia]. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact RFb | intros k Hk; apply KS; lia]. }
      split.
      { s4vg1. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) (ms_mem ms3)));
        [exact Rnn | intros k Hk; apply KS; lia]. }
      split.
      { change (sgT_body2 IM) with (Some (VReg RV_a1)). cbn [vat]. cbv [RV_a1]. s4h_greg HS2.
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE2 20%nat (20%bv : bv 5) eq_refl). exact Q20. }
      s4vg1. s4h_greg HS2. reflexivity.
Qed.

(* ================================================================================================
   SEGMENT S4, assembled: the head (C3 to the loop head at k = 0, or the two no-T arms to C5), the loop
   closed over the S3 hypothesis (s4_loop_closed), and the tail (the loop exit to C5).
   ================================================================================================ *)
Theorem scene_seg_S4_au : seg_S4_stmt (SK := SK) SEGS B ameter_triv WK IM.
Proof.
unfold seg_S4_stmt. intros cx POST HBASE HS3 HC5.
apply (s4_head cx POST HBASE); [| exact HC5].
exact (s4_loop_closed cx POST HS3 (s4_tail cx POST HBASE HC5) 0 ltac:(change (sg_nturns IM) with 343; lia)).
Qed.

End h.
End d.
