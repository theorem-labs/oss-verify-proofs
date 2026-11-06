(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostMal.v at 01f4363fe7d2, for reac-pw/fuzz_headamp
   image A: module paths; rl_c23_chain -> hq_c23_chain; RPgHarn's rh_cut_C2 / rh_at_C3 / rh_S_C23_stmt -> lib/A/HPgSegC23.v's
   hq_cut_C2 / hq_at_C3 / hq_S_C23_stmt over lib/A/HPgSegM.v's harness record hq_hcx; the `jal` 0x820c0 -> 0x82e60, the
   malloc trampoline 0x52428 -> 0x53060, C3 0x820c4 -> 0x82e64, the real frame 0x1a0 -> 0x1e0 below S; the allocator's
   rule at every float state (the step is stated at the float state fx2 C2 is reached at); the trace premise in
   lib/A/HPgE01D.v's e01_trace_stmt form; new: C3's whole cut (hq_cut_C3: the block list, the new block fresh, the
   carried cells, C3's value list, the frame's shadow, the record's bytes, the pod block's shadow and alignment) from
   the rule's post. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): THE malloc(pod) STEP of the
   walk of LLVMFuzzerTestOneInput, C2 = 0x82e60 -> C3 = 0x82e64, i.e. lib/A/HPgSegC23.v hq_S_C23_stmt at the concrete
   segments lib/A/Img0.v rsegs. Proves no function (kind: segment lemma).

   THE CODE. At C2 a0 = len + (len == 0) (hd_cut hi_L2: (LReg 10, XLenNZ)), and 8 <= len <= 5440 (hq_cut_C2's record
   facts), so a0 = len. 0x82e60 is `jal 0x53060`: ra := 0x82e64, pc := 0x53060, which is the runtime's malloc entry of
   image A (pc_wrap_malloc, the 4-byte jump to the wrapper). C3 = 0x82e64 is the return address.

   THE ROUTE.
   1. The engine runs the one `jal` from an entry state with every register an atom (the one-word table c23_tbl at
      0x82e60); it stops at 0x53060 with ra the literal 0x82e64 and every other register its own atom, and no byte
      written.
   2. The kernel's journal malloc rule YCbq.aj_malloc_at04 at the harness journal hq_j (STK = LLVMF_STK, sp0 = S,
      FP = [], own = [(4, pos)], k = 1), with o = R - S (R = e_R e the 32-aligned real-frame base, so o is 16-aligned,
      -0x1f0 <= o <= -0x1e0), the event and live-byte budgets from hq_base, and the caller chain from the harness entry:
      the entry's achain (afn_pre, ch = []) pushed with the frame record the prologue stored at S - 8 (ra) and S - 16
      (s0), which hq_kept carries (hq_c23_chain), s0 = S at C2 (hd_cut hi_L2: (LReg 8, XS)).
   3. The rule's post gives hq_at_C3's call part: the journal at two events, a0 = pod >= 4096, the callee-saved
      registers of C2 kept (the `jal` changes only ra), frames kept, the block appended, acall_kept at [R - ASTACK, R).
   4. C3's cut (hq_cut_C3 at the env with pod): the block list is a permutation of the entry's with pp and pod
      appended; pod is fresh (were it an entry block, AR's block separation at C3 would put it apart from itself) and
      16-aligned, its shadow addressable and visible (AR's block law, HPgMem.hm_blk_ra) and amem_range pod (len + 8)
      (the block lies in the application range); C3's values are C2's but a0 (callee-saved registers kept, the
      real-frame cells above R kept by acall_kept's stack clause); the frame's 1024 bytes and 128 shadow bytes and the
      thirteen saves, the float saves and the flag word are kept (acall_kept's frame and stack clauses; a block lies in
      the application range, apart from the frame's shadow); the pp block's bytes are kept (acall_kept's block clause:
      pp and pod are two members of C3's block list, so they are apart).

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     amalloc_realizes rsegs B at every float state   the runtime's malloc against the model
     errno_low   api_env rsegs B                                 errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)                      the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x53060            the code record: malloc's entry is the jal's target
     HSTK_C23    ASTACK + HQ_RSZ + 16 <= LLVMF_STK               the call's stack budget: ASTACK - o <= LLVMF_STK
     HEV_C23     2 <= EV_LIB                                     room for this event: st_nev < EV_MAX
     HLIVE_C23   Layout.PP_SIZE + 5440 <= LIVE_LIB               room for pod after pp: blocks_bytes + len <= LIVE_MAX
     HTRACE_C23  the malloc traces at ra = 0x82e64 are in the universe (the two chain shapes; HPgE01D e01_trace_stmt's
                 form).
   AXIOMS (Print Assumptions below): the primitive int / string / array axioms and Stdlib's
   functional_extensionality_dep, which the kernel's engine runner YCbq.SRr_run_tok_AJ uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG0s YG0q YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg HPgSegM HPgSegC23.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the one instruction word the engine runs: the `jal` at C2 ---- *)
Definition c23_tbl : ctable := build_table rsegs HQ_C2 1 TEmpty.
Lemma c23_tbl_ok : table_ok rsegs c23_tbl.
Proof. apply build_table_ok0. unfold HQ_C2. lia. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- memories equal at every word give the same view, presence, words and kept clauses ---- *)
Lemma c23_aview_mem : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview rsegs H m' a = aview rsegs H m a.
Proof. intros H m m' Hm a. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hm. reflexivity. Qed.
Lemma c23_apresent_mem : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, apresent H m a -> apresent H m' a.
Proof. intros H m m' Hm a [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hm. exact Hb. Qed.
Lemma c23_rdword_mem : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
rdword (aview rsegs H m') a = rdword (aview rsegs H m) a.
Proof. intros H m m' a Hm. apply rdword_ext. intros k _. apply c23_aview_mem. exact Hm. Qed.

(* ---- an 8-byte cell as a word of the view (the converse of YCbq.val_mem_of_rdword) ---- *)
Lemma c23_rdword_of_val_mem : forall H mem a v, 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict H mem) a 8 v -> rdword (aview rsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold val_mem in Hm.
pose proof (Hm 0%nat ltac:(lia)) as H0. pose proof (Hm 1%nat ltac:(lia)) as H1. pose proof (Hm 2%nat ltac:(lia)) as H2.
pose proof (Hm 3%nat ltac:(lia)) as H3. pose proof (Hm 4%nat ltac:(lia)) as H4. pose proof (Hm 5%nat ltac:(lia)) as H5.
pose proof (Hm 6%nat ltac:(lia)) as H6. pose proof (Hm 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
unfold rdword, aview. cbv beta.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. cbn [option_map].
assert (Hb : forall k, bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 8 k)) = YG0f.le_byte v 8 k).
{ intros k. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). rewrite YG0s.le_byte_8. apply Z.mod_mod. lia. }
rewrite !Hb. f_equal. apply YG0s.le_bytes8. exact Hv.
Qed.
(* a cell fact of HPgBase as a word of the view *)
Lemma c23_hd_cell : forall H mem regs e b o v, 0 <= v < 2 ^ 64 ->
hd_at rsegs H mem regs e (LCell b o) v -> rdword (aview rsegs H mem) (hd_xv e b + o) = Some v.
Proof.
intros H mem regs e b o v Hv Hc. cbn [hd_at] in Hc. rewrite Z.mod_small in Hc by exact Hv.
apply c23_rdword_of_val_mem; assumption.
Qed.

(* ---- register names: a literal and Z_to_bv 5 of its number name the same register ---- *)
Lemma c23_getr_eq : forall regs (b b' : bv 5), bv_unsigned b = bv_unsigned b' -> getr regs b = getr regs b'.
Proof. intros regs b b' E. apply bv_eq in E. subst b'. reflexivity. Qed.
Lemma c23_csaved : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r) = r.
Proof.
intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
apply Z.mod_small. unfold acallee_saved in Hr. lia.
Qed.

(* ---- the caller chain at a call from the harness frame [knock APgRt.v rt_chain] ---- *)
Lemma hq_c23_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- exact (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal ltac:(lia) Hsp').
- left. split; [right; left; lia | reflexivity].
Qed.

Lemma c23_acall_kept_mem : forall B ly S W (m m' : word -> option byte) W3 m3 slo shi (E : Z -> Prop),
(forall x, m' x = m x) ->
acall_kept rsegs B ly S W m' W3 m3 slo shi E -> acall_kept rsegs B ly S W m W3 m3 slo shi E.
Proof.
intros B ly S W m m' W3 m3 slo shi E Hm (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (c23_aview_mem (w_H W) m m' Hm) as Hv.
split; [intros a Ha Hs; rewrite <- Hv; exact (K1 a Ha Hs)|].
split; [intros b n i Hb Hi HE; rewrite <- Hv; exact (K2 b n i Hb Hi HE)|].
split; [intros a Ha Ho He; rewrite <- Hv; exact (K3 a Ha Ho He)|].
split; [intros cid pos a Hf Hr HE; rewrite <- Hv; exact (K4 cid pos a Hf Hr HE)|].
split; [intros a Ha Hs Hp; exact (K5 a Ha Hs (c23_apresent_mem (w_H W) m m' Hm a Hp))|].
exact K6.
Qed.
End h.

(* the side goals of a register a run did not touch (clob = [ra]) *)
Ltac c23_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros [Hx|[]]; apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx] ].

(* lia without the context's disjunctions *)
Local Ltac zl := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

(* a heap block lies in the application range, apart from the shadow bytes of the frame for locals (the route of
   HPgE01M.e01m_sh_app, restated here for the pod block) *)
Section g. Context {rc : YM05.RunCeil}.
Lemma c23_sh_app : forall F i p n, 4096 <= F -> F + 1024 <= alloc_ceiling -> 0 <= i < 128 -> in_app p n ->
~ (p <= shadow_addr F + i < p + n).
Proof.
intros F i p n HF1 HF2 Hi Happ. pose proof alloc_ceiling_value as [HC _].
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ. unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le F 8 ltac:(lia)). lia.
Qed.
End g.

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : forall fx : YK11.FPState, @amalloc_realizes fx rc rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x53060.
Hypothesis HSTK_C23 : ASTACK + HQ_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C23 : 2 <= EV_LIB.
Hypothesis HLIVE_C23 : Layout.PP_SIZE + 5440 <= LIVE_LIB.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
  raZ regsT = HQ_C3 -> (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).

Theorem hq_A_S_C23 : hq_S_C23_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C23 HEV_C23 HLIVE_C23 HTRACE_C23.
intros hx fx2 pos e r ly2 S2 W2 regs2 mem2 md2 HB HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof alloc_ceiling_value as (HCv & _). pose proof ASAN_CEIL_range as (HAC & _).
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HAC2 & Hfrm & Hrec).
destruct HAC2 as (HJ & Hperm & Hfresh2 & Hsp2 & Hgp2 & Htp2 & Hgeo & Hcut & Hfsh & Hkept).
pose proof Hrec as (Hwf & HlenB & Hlen8 & Hppb & Hcap & Hnull & Hrc).
pose proof Hgeo as (HeS & HeR & HeF).
unfold hq_j in HJ.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EFl & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof HSTK_C23 as HSTK. unfold ASTACK, HQ_RSZ in HSTK.
(* the geometry: S = 16 t, R = 32 q with S - 0x1e0 = 32 q + r', 0 <= r' < 32 *)
rewrite HeS in HeR. unfold HQ_RSZ in HeR.
pose proof (Z.div_mod (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (h_regs rsegs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= e_R e /\ e_R e + 0x1e0 <= spZ (h_regs rsegs hx) /\
  spZ (h_regs rsegs hx) - e_R e <= 0x1f0) by lia.
assert (HR64 : 0 <= e_R e < 2 ^ 64) by zl.
assert (HS64 : 0 <= spZ (h_regs rsegs hx) < 2 ^ 64) by zl.
assert (HAL : (e_R e - spZ (h_regs rsegs hx)) mod 16 = 0).
{ replace (e_R e - spZ (h_regs rsegs hx))
    with ((2 * ((spZ (h_regs rsegs hx) - 0x1e0) / 32) - spZ (h_regs rsegs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (h_regs rsegs hx) mod 8 = 0).
{ replace (spZ (h_regs rsegs hx)) with ((2 * (spZ (h_regs rsegs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* the C2 values a0 = len and s0 = S *)
pose proof Hcut as Hcut0.
unfold hd_cut in Hcut. cbn [hi_L2 headamp_himg_A] in Hcut. unfold headamp_A_L23 in Hcut.
apply Forall_cons_iff in Hcut as [C10 Hcut]. apply Forall_cons_iff in Hcut as [C8 _].
cbn [fst snd hd_at hd_xv] in C10, C8.
replace (e_len e =? 0) with false in C10 by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r in C10.
rewrite HeS in C8.
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
pose proof Hkept as (Hk' & _).
unfold hq_cells, hq_saves_L in Hk'. cbn [seq map app] in Hk'.
apply Forall_cons_iff in Hk' as [K0 Hk']. apply Forall_cons_iff in Hk' as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (c23_hd_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (c23_hd_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [hd_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs rsegs hx) - 8) = Some (raZ (h_regs rsegs hx))).
{ replace (spZ (h_regs rsegs hx) - 8) with (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs rsegs hx) - 16) = Some (s0Z (h_regs rsegs hx))).
{ replace (spZ (h_regs rsegs hx) - 16) with (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the `jal`: one engine step to 0x53060 *)
assert (HS : @st_ok rsegs fx2 (Ereg regs2 HPgSteps.rt_extra) (mkSS HQ_C2 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fx2 regs2 (Z_to_bv 64 HQ_C2) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - unfold facts_ok. cbn. tauto. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs2 HPgSteps.rt_extra) (mrestrict (w_H W2) mem2)) by constructor.
assert (HAE : env_agree 32 (Ereg regs2 HPgSteps.rt_extra) (Ereg regs2 HPgSteps.rt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 HQ_C2) with (Z_to_bv 64 HQ_C2).
aj_run_tok c23_tbl_ok HS HJ SHOK HPgSteps.RTBspan; [awr_ok_tac |].
(* no byte written; every register but ra its own atom; ra the literal 0x82e64 *)
assert (Hm : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [Z_to_bv 5 1] -> getr (ms_regs ms) r = getr regs2 r).
{ eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 HPgSteps.rt_extra (w_H W2) _ HS HAE). vm_compute. reflexivity. }
assert (HRA : getr (ms_regs ms) 1 = Z_to_bv 64 0x82e64).
{ rewrite (c23_getr_eq (ms_regs ms) 1 (Z_to_bv 5 1)) by reflexivity.
  lazymatch type of HS with st_ok _ ?E ?ss _ =>
    let e1 := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 1)) in
    assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = sv_denot E e1)
      by exact (st_ok_restrict_reg rsegs (w_H W2) E ss ms (Z_to_bv 5 1) HS) end.
  cbn [sv_denot] in R1. rewrite R1. reflexivity. }
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (e_len e)).
{ rewrite RK by c23_rk. rewrite (c23_getr_eq regs2 10 (Z_to_bv 5 10)) by reflexivity. exact C10. }
assert (HN : 0 <= e_len e < MALLOC_MAX) by (change MALLOC_MAX with 268435456; lia).
assert (HLV : blocks_bytes S2 + e_len e <= LIVE_MAX).
{ assert (EB : forall ly S, blocks_bytes S = bsum (ablocks B ly S)) by (intros; apply blocks_bytes_bsum).
  rewrite (EB ly2 S2), (bsum_perm _ _ Hperm), bsum_app, <- (EB (h_ly rsegs hx) (h_S rsegs hx)).
  change (bsum [(e_pp e, Layout.PP_SIZE)]) with (Layout.PP_SIZE + 0). lia. }
assert (HSP : spZ (ms_regs ms) = spZ (h_regs rsegs hx) + (e_R e - spZ (h_regs rsegs hx))).
{ unfold spZ at 1. rewrite RK by c23_rk. rewrite Hsp2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : e_R e - spZ (h_regs rsegs hx) <= 0) by lia.
assert (HBUD : ASTACK - (e_R e - spZ (h_regs rsegs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite RK by c23_rk; exact Hgp2).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite RK by c23_rk; exact Htp2).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x82e64)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S2 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x82e64) by (unfold raZ; rewrite HRA; apply unsigned_lit_small; lia).
set (ch := if spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)
  then [(spZ (h_regs rsegs hx), raZ (h_regs rsegs hx), s0Z (h_regs rsegs hx))] else []).
assert (HCH : chain_pre ly2 (aview rsegs (w_H W2) (ms_mem ms)) (ms_regs ms) ch).
{ apply (achain_chain_pre ly2 _ (e_R e) (spZ (h_regs rsegs hx))).
  - apply (achain_ly_top (h_ly rsegs hx) ly2 _ _ _ _ Etop). unfold ch.
    apply (hq_c23_chain (h_ly rsegs hx) (aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx))).
    + exact Hch0.
    + zl.
    + intros a Ha. rewrite (c23_aview_mem (w_H W2) mem2 (ms_mem ms) Hm). apply F1; zl.
    + rewrite (c23_rdword_mem (w_H W2) mem2 (ms_mem ms) _ Hm). exact R8.
    + rewrite (c23_rdword_mem (w_H W2) mem2 (ms_mem ms) _ Hm). exact R16.
    + exact Hra40.
    + lia.
    + exact HS8.
    + lia.
  - rewrite HSP. lia.
  - unfold s0Z. rewrite RK by c23_rk. rewrite (c23_getr_eq regs2 8 (Z_to_bv 5 8)) by reflexivity.
    rewrite C8. unfold w64. apply unsigned_lit_small. lia.
  - rewrite HRAZ. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) ch) (as_universe B)).
{ apply HTRACE_C23; [exact HRAZ |]. unfold ch.
  destruct (spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)); [right | left; reflexivity].
  exists (spZ (h_regs rsegs hx)), (s0Z (h_regs rsegs hx)). rewrite Hra0. reflexivity. }
(* the machine state at 0x53060 = pc_wrap_malloc *)
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems.
rewrite Ems at 1.
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
eapply SRr_mono.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML (AMALLOC fx2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HA10 HN HLV HSP HAL HNEG HBUD HGP HTP HRA HRAOK HEV HCH HTR). }
(* 3. the post at C3 *)
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & res & Ec3 & HJ3 & Hpres3 & H103 & Hfr3 & Hres & Hab3 & Hkept3).
replace (spZ (h_regs rsegs hx) + (e_R e - spZ (h_regs rsegs hx))) with (e_R e) in Hkept3 by lia.
pose proof (c23_acall_kept_mem B ly2 S2 W2 mem2 (ms_mem ms) W3 mem3 _ _ _ Hm Hkept3) as HKA.
assert (Hcs : forall rr, acallee_saved rr -> getr regs3 (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)).
{ intros rr Hr. rewrite (Hpres3 rr Hr). apply RK.
  - rewrite (c23_csaved rr Hr). unfold acallee_saved in Hr. lia.
  - intros [Hx|[]]. apply (f_equal (@bv_unsigned 5)) in Hx. rewrite (c23_csaved rr Hr) in Hx.
    change (bv_unsigned (Z_to_bv 5 1)) with 1 in Hx. unfold acallee_saved in Hr. lia. }
unfold hq_at_C3. exists res, ly3, S3, regs3, mem3, md3.
split; [rewrite Ec3; reflexivity|].
split; [exact Hres|].
split; [exact H103|].
split; [exact Hcs|].
split; [exact Hfr3|].
split; [exact Hab3|].
split; [exact HKA|].
(* 4. C3's cut *)
destruct HKA as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
pose proof (proj1 HJ3) as HAR3.
pose proof HJ3 as (_ & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EFl3 & _).
assert (Ereq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (Efs : fs_frame_bytes HQ_CID = 1024) by reflexivity.
pose proof (req_size_pos (e_len e) ltac:(lia)) as Hrq.
assert (HinR : In (res, e_len e) (ablocks B ly3 S3)) by (rewrite Hab3; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 res (e_len e) HAR3 HinR) as (Hr16 & Hr4096 & Hrceil & Happr & Hpresr & _).
assert (Hpp2 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. apply in_or_app. right. left. reflexivity. }
(* pp and pod are two members of C3's block list: apart *)
assert (Hdpr : zdisjoint (block_rng (e_pp e, Layout.PP_SIZE)) (block_rng (res, e_len e))).
{ apply in_split in Hpp2 as (l1 & l2 & E).
  apply (sep_blocks_pos rsegs B LAWS ly3 S3 W3 mem3 md3 (e_pp e, Layout.PP_SIZE) (res, e_len e) l1 l2 [] HAR3).
  rewrite Hab3, E, <- app_assoc. reflexivity. }
unfold zdisjoint, block_rng in Hdpr. cbn [fst snd] in Hdpr. rewrite Ereq in Hdpr.
(* the frame for locals: the entry layout's, kept by every journal *)
assert (EFa2 : frame_addr ly2 HQ_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EFl; reflexivity).
assert (HinF2 : In (HQ_CID, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
assert (HinF3 : In (HQ_CID, pos) (frames S3)) by (rewrite Hfr3; exact HinF2).
assert (EFa3 : frame_addr ly3 HQ_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EFl3; reflexivity).
destruct (frames_bounds rsegs B LAWS ly3 S3 W3 mem3 md3 HQ_CID pos HAR3 HinF3) as (HF1 & HF2 & _).
rewrite EFa3 in HF1. rewrite EFa3, Efs in HF2.
pose proof (sep_block_frame rsegs B LAWS ly3 S3 W3 mem3 md3 res (e_len e) HQ_CID pos HAR3 HinR HinF3) as HdRF.
rewrite EFa3, Efs in HdRF. unfold zdisjoint in HdRF. cbn [fst snd] in HdRF.
assert (KS : forall a, e_R e <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply KA1; lia. }
assert (KF : forall a, e_F e <= a < e_F e + 1024 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (KA4 HQ_CID pos a HinF2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa2, Efs. lia.
  - cbn beta. lia. }
assert (KSh : forall i, 0 <= i < 128 ->
  aview rsegs (w_H W3) mem3 (shadow_addr (e_F e) + i) = aview rsegs (w_H W2) mem2 (shadow_addr (e_F e) + i)).
{ intros i Hi. apply (KA4 HQ_CID pos _ HinF2).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa2, Efs. change (1024 / 8) with 128. lia.
  - cbn beta. exact (c23_sh_app (e_F e) i res (req_size (e_len e)) HF1 HF2 Hi Happr). }
assert (Hlpp : Z.of_nat (length (Layout.pp_bytes r)) = Layout.PP_SIZE) by (rewrite (Layout.length_pp_bytes _ Hwf); reflexivity).
split; [|split; [exact Hfrm|split; [|split; [|split; [|split]]]]].
- (* hq_at_cut at C3 *)
  unfold hq_at_cut.
  split; [exact HJ3|].
  split.
  { rewrite Hab3. cbn [hq_env_pod e_pp e_pod e_len].
    change [(e_pp e, Layout.PP_SIZE); (res, e_len e)] with ([(e_pp e, Layout.PP_SIZE)] ++ [(res, e_len e)]).
    rewrite app_assoc. apply Permutation_app_tail. exact Hperm. }
  split.
  { cbn [hq_env_pod e_pp e_pod e_len]. apply Forall_cons_iff in Hfresh2 as [Hfp _].
    apply Forall_cons; [exact Hfp|]. apply Forall_cons; [|apply Forall_nil]. cbn [fst]. split; [|lia].
    intros Hold. assert (Hold2 : In (res, e_len e) (ablocks B ly2 S2)).
    { eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. apply in_or_app. left. exact Hold. }
    apply in_split in Hold2 as (l1 & l2 & E).
    pose proof (sep_blocks_pos rsegs B LAWS ly3 S3 W3 mem3 md3 (res, e_len e) (res, e_len e)
      l1 l2 [] HAR3 ltac:(rewrite Hab3, E, <- app_assoc; reflexivity)) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia. }
  split; [exact (eq_trans (Hcs 2 ltac:(unfold acallee_saved; lia)) Hsp2)|].
  split; [exact (eq_trans (Hcs 3 ltac:(unfold acallee_saved; lia)) Hgp2)|].
  split; [exact (eq_trans (Hcs 4 ltac:(unfold acallee_saved; lia)) Htp2)|].
  split; [exact Hgeo|].
  split.
  { (* C3's values: C2's but a0 *)
    unfold hd_cut in Hcut0 |- *. cbn [hi_L2 hi_L3 headamp_himg_A] in Hcut0 |- *. unfold headamp_A_L23 in Hcut0 |- *.
    rewrite !Forall_cons_iff in Hcut0.
    destruct Hcut0 as (_ & D8 & D9 & D18 & D19 & D20 & D21 & D23 & D24 & D26 & G20 & G28 & G40 & G60 & G90 & Ga0 & Gf0 & _).
    cbn [fst snd hd_at hd_xv] in D8, D9, D18, D19, D20, D21, D23, D24, D26, G20, G28, G40, G60, G90, Ga0, Gf0.
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd hd_at hd_xv hq_env_pod e_S e_R e_F e_pp e_pod e_len e_cap e_null].
    all: first
    [ exact H103
    | (erewrite Hcs; [eassumption | unfold acallee_saved; lia])
    | (eapply val_mem_kept; [|eassumption]; intros k Hk; apply KS; lia) ]. }
  split.
  { apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 (e_F e) _ Hfsh). intros i Hi.
    change (Z.of_nat (length (hi_shA headamp_himg_A))) with 80 in Hi. apply KSh. lia. }
  (* the carried cells *)
  destruct Hkept as [Hc (v0 & v1 & v2 & FS0 & FS1 & FS2)].
  split.
  + unfold hq_cells in *. rewrite Forall_forall in *. intros f Hf. pose proof (Hc f Hf) as Hf'.
    apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
    * unfold hq_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
      cbn [fst snd hd_at hd_xv hq_env_pod e_S] in *.
      eapply val_mem_kept; [|exact Hf']. intros k Hk'. apply KS. lia.
    * cbn [fst snd hd_at hd_xv hq_env_pod e_F] in *.
      eapply val_mem_kept; [|exact Hf']. intros k Hk'. apply KF. unfold HQ_FLAG. lia.
  + exists v0, v1, v2. cbn [hd_at hd_xv hq_env_pod e_S] in FS0, FS1, FS2 |- *.
    split; [|split]; (eapply val_mem_kept; [|eassumption]); intros k Hk'; apply KS; lia.
- (* the record's data *)
  unfold hq_recP. cbn [hq_env_pod e_pp e_len e_cap e_null e_rc].
  split; [exact Hwf|]. split; [exact HlenB|]. split; [exact Hlen8|].
  split; [|exact (conj Hcap (conj Hnull Hrc))].
  change (hm_bytes rsegs (w_H W3) mem3 (e_pp e) (Layout.pp_bytes r)).
  apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact Hppb|].
  intros x Hx. rewrite Hlpp in Hx. replace x with (e_pp e + (x - e_pp e)) by lia.
  apply (KA2 (e_pp e) Layout.PP_SIZE (x - e_pp e) Hpp2); [rewrite Ereq; lia |]. cbn beta. lia.
- (* the pod block's shadow *)
  cbn [hq_env_pod e_pod e_len].
  exact (proj1 (hm_blk_ra rsegs B ly3 S3 W3 mem3 md3 res (e_len e) res (e_len e) HAR3 HinR ltac:(lia) ltac:(lia))).
- cbn [hq_env_pod e_pod e_len].
  exact (proj2 (hm_blk_ra rsegs B ly3 S3 W3 mem3 md3 res (e_len e) res (e_len e) HAR3 HinR ltac:(lia) ltac:(lia)) ltac:(lia)).
- cbn [hq_env_pod e_pod e_len]. unfold amem_range.
  unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
- cbn [hq_env_pod e_pod]. exact Hr16.
Qed.
End b.

Print Assumptions hq_A_S_C23.
