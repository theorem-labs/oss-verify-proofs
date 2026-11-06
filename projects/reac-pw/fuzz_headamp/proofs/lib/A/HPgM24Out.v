(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostMal.v at 01f4363fe7d; ported to reac-pw/fuzz_headamp image A: role's C2 -> C3 step (malloc(pod), rh_S_C23_stmt) restated as headamp's C6 -> C7 step (malloc(first), lib/A/HPgSegM.v hq_S_C67_stmt) with the prefix rl_c23 / c23 -> hk, the jal 0x820c0 -> 0x83740, malloc's entry 0x52428 -> 0x53060, role's frame 0x1a0 -> headamp's 0x1e0, k = 1 -> 3 events, role's request len -> 3 max(rc, 0) + (it == 0); the call runs at the float state fx2 the cut states (AMALLOC quantified over the float state); the post is HPgSegM's whole hq_cut_C7 (role's rh_at_C3 asked the call's post only), built from the rule's post with the allocator invariant at the new state, acall_kept and image A's cut lists; the errno cell's readability is new (every byte of image A's four segments has an image byte). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM24Mal.v at be048d930b4; its C6 -> C7 step
   (malloc(first)) restated as the C4 -> C5 step (malloc(out)): the cut C4 and the post hq_at_C5 are stated here in
   the form of lib/A/HPgSegM.v's hq_cut_C6 / hq_at_C7 (image B's lib/AU/HPgSegM.v hqu_cut_C4 / hqu_at_C5 at image A),
   the jal 0x83740 -> 0x82e94, the return 0x83744 -> 0x82e98, k = 3 -> 2 events, the request
   3 max(rc, 0) + (it == 0) -> 3 cap + 3 (hi_L4: (LReg 10, XCap33)), the blocks pp, pod, out -> pp, pod, the cut lists
   hi_L6 / hi_L7 -> hi_L4 / hi_L5 (HPgSiteA headamp_A_site_cut5), the shadow pattern hi_shB -> hi_shA; the post also
   states the out block apart from the pod block; the image helpers (hk_errno_rd, hk_cell, hk_chain, hk_ch,
   hk_shadow_apart, hk_getr_eq, hk_csaved, hk_rk) are Required from HPgM24Mal, not copied. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): THE malloc(out) STEP of the
   walk of LLVMFuzzerTestOneInput, C4 = 0x82e94 -> C5 = 0x82e98 (fuzz_headamp.c:326), its statement hq_S_C45_stmt and
   its proof hq_A_S_C45 at the concrete segments lib/A/Img0.v rsegs. Proves no function (kind: segment lemma).

   THE STATEMENT. hq_cut_C4 is what M02 (lib/A/HPgCSpec.v headamp_dup_contract) delivers at C4, at the harness level
   of lib/A/HPgSegM.v (hq_at_cut with two events and the blocks pp and pod, image A's list hi_L4, the prologue's
   shadow pattern hi_shA, a zero rounding mode, the record's data hq_rec and the pod block's shadow marked usable).
   hq_at_C5 is what the call leaves: the returned block out >= 4096 in a0, the callee-saved registers, the frames,
   the block list with out appended, acall_kept at [R - ASTACK, R), the out block apart from the pod block, and
   HPgSegM's hq_cut_C5 at the env with out (hq_env_out). The errno cell's value at C5 is quantified: the allocator's
   contract lets malloc change it, and headamp_check_contract, which C5 starts, takes the value universally.

   THE CODE. At C4 a0 = 3 cap + 3 (hi_L4: (LReg 10, XCap33), from 0x82e84 .. 0x82e90), in [3, 30] (HPgSiteA
   headamp_A_site_malloc_out with 0 <= cap <= 9). 0x82e94 is `jal 0x53060`: ra := 0x82e98, pc := 0x53060, the
   runtime's malloc entry of image A (pc_wrap_malloc, the 4-byte jump to the wrapper). C5 = 0x82e98 is the return
   address.

   THE ROUTE (HPgM24Mal's).
   1. The engine runs the one `jal` from an entry state with every register an atom (ho_entry, the one-word table
      ho_tbl at 0x82e94); it stops at 0x53060 with ra the literal 0x82e98, every other register its own atom and no
      byte written.
   2. The kernel's journal malloc rule YCbq.aj_malloc_at04 at the harness journal hq_j (STK = LLVMF_STK, sp0 = S,
      FP = [], own = [(4, pos)], k = 2), with o = R - S (16-aligned, -0x1f0 <= o <= -0x1e0), the event and
      live-byte budgets from hq_base, and the caller chain from the harness entry pushed with the frame record the
      prologue stored at S - 8 (ra) and S - 16 (s0), which hq_kept carries (hk_chain), s0 = S at C4 (hi_L4).
   3. The rule's post gives hq_at_C5: the journal at three events, a0 = out, the callee-saved registers of C4 kept,
      frames kept, the block appended, acall_kept; out apart from pp and pod (YCbq.sep_blocks_pos) and fresh; hi_L5
      by headamp_A_site_cut5 over hi_L4 kept by acall_kept; the frame's shadow and flag cell (acall_kept's frame
      clause); the thirteen saves and the three float saves (acall_kept's stack clause); the pp / pod bytes
      (acall_kept's block clause); the shadow of pod and out (HPgMem.hm_blk_ra at the new state); the errno cell
      readable (HPgM24Mal.hk_errno_rd).

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     forall fx', amalloc_realizes rsegs B   the runtime's malloc against the model, at every float
                                                         state (the call runs at the state C4 states, fx2)
     errno_low   api_env rsegs B                        errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)             the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x53060   the code record: malloc's entry is the jal's target
     HSTK_C45    ASTACK + HQ_RSZ + 16 <= LLVMF_STK      the call's stack budget: ASTACK - o <= LLVMF_STK
     HEV_C45     3 <= EV_LIB                            room for this event (the third): st_nev < EV_MAX
     HLIVE_C45   Layout.PP_SIZE + 5440 + 30 <= LIVE_LIB room for out after pp and pod:
                                                         blocks_bytes + 3 cap + 3 <= LIVE_MAX
     HTRACE_C45  the malloc trace at ra = 0x82e98 is in the universe (scene's rt_trace_in_stmt, one site).
   AXIOMS (Print Assumptions below): the primitive int / string / array axioms and Stdlib's
   functional_extensionality_dep. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YK07.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG0s YG0q YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgSteps HPgSiteA HPgM24Mal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= THE STATEMENT ======================================= *)
(* the C4 pc (the `jal` of malloc(out)) is hi_c4 headamp_himg_A; C5 is HPgSegM's HQ_C5 *)
Definition HQ_C4 : Z := 0x82e94.
Lemma hq_c4_himg : hi_c4 headamp_himg_A = HQ_C4.
Proof. reflexivity. Qed.

(* the blocks live at C3 .. C4 (pp, pod) *)
Definition hq_blocks3 (e : hd_env) : list (Z * Z) := [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)].

(* C4's values do not read XOut, so the env gains the returned block only at C5 *)
Definition hq_env_out (e : hd_env) (out : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) (e_pod e) out (e_first e) (e_len e) (e_cap e) (e_null e) (e_rc e)
        (e_src e) (e_left e).
Lemma hq_env_out_xv : forall e out x, x <> XOut -> hd_xv (hq_env_out e out) x = hd_xv e x.
Proof. intros e out x H. destruct x; cbn; try reflexivity. exfalso; exact (H eq_refl). Qed.

Section sb. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ---------------- C4 0x82e94: what M02 (headamp_dup_contract) delivers, before out is asked for ---------------- *)
Definition hq_cut_C4 (hx : hq_hcx segs) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hq_at_cut segs B LLVMF_STK hx pos e 2 (hq_blocks3 e) (hi_L4 headamp_himg_A) (hi_shA headamp_himg_A)
  ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_rec segs e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e).

(* ---------------- the allocator step C4 -> C5: what the `jal` of malloc(out) leaves ---------------- *)
Definition hq_at_C5 (hx : hq_hcx segs) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
(ly4 : alayout) (S4 : astate) (W4 : world segs) (regs4 : bvmap 5 word) (mem4 : word -> option byte)
: world segs -> config -> Prop :=
fun W5 c5 => exists out ev5 ly5 S5 regs5 mem5 md5,
c5 = @cfg_at fx2 segs HQ_C5 regs5 mem5 md5 /\
4096 <= out /\ getr regs5 10 = w64 out /\
(forall rr, acallee_saved rr -> getr regs5 (Z_to_bv 5 rr) = getr regs4 (Z_to_bv 5 rr)) /\
frames S5 = frames S4 /\
ablocks B ly5 S5 = ablocks B ly4 S4 ++ [(out, 3 * (e_cap e + 1))] /\
acall_kept segs B ly4 S4 W4 mem4 W5 mem5 (e_R e - ASTACK) (e_R e)
  (fun a => out <= a < out + req_size (3 * (e_cap e + 1))) /\
(e_pod e + e_len e <= out \/ out + 3 * (e_cap e + 1) <= e_pod e) /\
hq_cut_C5 segs B LLVMF_STK hx fx2 pos (hq_env_out e out) r ev5 ly5 S5 W5 regs5 mem5 md5.

(* the allocator step C4 -> C5 (fuzz_headamp.c:326): a0 = 3 cap + 3 from 0x82e84 .. 0x82e90 *)
Definition hq_S_C45_stmt : Prop :=
forall (hx : hq_hcx segs) (fx2 : YK11.FPState) pos e r ly4 S4 W4 regs4 mem4 md4,
hq_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
hq_cut_C4 hx fx2 pos e r ly4 S4 W4 regs4 mem4 md4 ->
SRr segs W4 (@cfg_at fx2 segs HQ_C4 regs4 mem4 md4) (hq_at_C5 hx fx2 pos e r ly4 S4 W4 regs4 mem4).
End sb.

(* ======================================= THE PROOF AT IMAGE A ======================================= *)
(* ---- the one instruction word the engine runs: the `jal` at C4 ---- *)
Definition HO_PC : Z := 0x82e94.
Definition ho_tbl : ctable := build_table rsegs HO_PC 1 TEmpty.
Lemma ho_tbl_ok : table_ok rsegs ho_tbl.
Proof. apply build_table_ok0. unfold HO_PC. lia. Qed.

(* the entry state at C4: the registers as atoms, no region, no fact (at any float state) *)
Definition ho_ss : sstate := mkSS HO_PC sr_atoms [] None (mkFacts [] [] []).
Lemma ho_entry : forall (fx' : YK11.FPState) (W : world rsegs) regs memc,
@st_ok rsegs fx' (Ereg regs rt_extra) ho_ss
  (restrict (w_H W) (@mkst fx' regs (Z_to_bv 64 HO_PC) memc (seg_rom rsegs))).
Proof.
intros fx' W regs memc. rewrite restrict_mkst_fx. unfold ho_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x53060.
Hypothesis HSTK_C45 : ASTACK + HQ_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C45 : 3 <= EV_LIB.
Hypothesis HLIVE_C45 : Layout.PP_SIZE + 5440 + 30 <= LIVE_LIB.
Hypothesis HTRACE_C45 : forall (regsT : bvmap 5 word) (hx : hq_hcx rsegs),
raZ (h_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQ_C5 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hk_ch hx)) (as_universe B).

Theorem hq_A_S_C45 : hq_S_C45_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C45 HEV_C45 HLIVE_C45 HTRACE_C45.
unfold hq_S_C45_stmt. intros hx fx2 pos e r ly4 S4 W4 regs4 mem4 md4 HB HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & Hfr0 & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HAC & Hfrm & Hrec & Hrapod).
destruct HAC as (HJ4 & Hperm4 & Hfresh4 & Hsp4 & Hgp4 & Htp4 & Hgeo & HL4 & Hfsh4 & Hkept4).
pose proof Hgeo as (HeS & HeR & HeF).
destruct Hrec as (Hwf & Hlen & Hlenb & Hpp & Hpod & Hpod16 & Hhull & Hamem & Hcap & Hnull & Hrc).
unfold hq_j in HJ4.
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & Hfrs4 & Hnev & _ & F1 & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof HSTK_C45 as HSTK. unfold ASTACK, HQ_RSZ in HSTK.
(* the geometry: S = 16 t, R = 32 q with S - 0x1e0 = 32 q + r, 0 <= r < 32, so S - R is 0x1e0 or 0x1f0 *)
rewrite HeS in HeR. unfold HQ_RSZ in HeR.
pose proof (Z.div_mod (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (h_regs rsegs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= e_R e /\ e_R e + 0x1e0 <= spZ (h_regs rsegs hx) /\
  spZ (h_regs rsegs hx) - e_R e <= 0x1f0) by lia.
assert (HR64 : 0 <= e_R e < 2 ^ 64) by lia.
assert (HS64 : 0 <= spZ (h_regs rsegs hx) < 2 ^ 64) by lia.
assert (HAL : (e_R e - spZ (h_regs rsegs hx)) mod 16 = 0).
{ replace (e_R e - spZ (h_regs rsegs hx))
    with ((2 * ((spZ (h_regs rsegs hx) - 0x1e0) / 32) - spZ (h_regs rsegs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (h_regs rsegs hx) mod 8 = 0).
{ replace (spZ (h_regs rsegs hx)) with ((2 * (spZ (h_regs rsegs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* the C4 values a0 = the request 3 cap + 3 and s0 = S *)
pose proof HL4 as HL4c. unfold hd_cut in HL4c. cbn [hi_L4 headamp_himg_A] in HL4c. unfold headamp_A_L45 in HL4c.
apply Forall_cons_iff in HL4c as [C10 HL4c]. apply Forall_cons_iff in HL4c as [C8 _].
cbn [fst snd hd_at] in C10, C8. cbn [hd_xv] in C10, C8. rewrite HeS in C8.
replace (3 * e_cap e + 3) with (3 * (e_cap e + 1)) in C10 by lia.
assert (HN : 0 <= 3 * (e_cap e + 1) < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
destruct Hkept4 as (Hcl4 & Hfs4).
pose proof Hcl4 as Hcl4c.
unfold hq_cells, hq_saves_L in Hcl4c. cbn [seq map app] in Hcl4c.
apply Forall_cons_iff in Hcl4c as [K0 Hcl4c]. apply Forall_cons_iff in Hcl4c as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (hk_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (hk_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [hd_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W4) mem4) (spZ (h_regs rsegs hx) - 8) = Some (raZ (h_regs rsegs hx))).
{ replace (spZ (h_regs rsegs hx) - 8) with (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W4) mem4) (spZ (h_regs rsegs hx) - 16) = Some (s0Z (h_regs rsegs hx))).
{ replace (spZ (h_regs rsegs hx) - 16) with (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the `jal`: one engine step to 0x53060 *)
pose proof (ho_entry fx2 W4 regs4 mem4) as HS.
assert (SHOK : sh_ok rsegs RTBx [] (Ereg regs4 rt_extra) (mrestrict (w_H W4) mem4)) by constructor.
assert (HAE : env_agree 32 (Ereg regs4 rt_extra) (Ereg regs4 rt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 HQ_C4) with (Z_to_bv 64 HO_PC).
aj_run_tok ho_tbl_ok HS HJ4 SHOK RTBspan; [awr_ok_tac |].
(* no byte written; every register but ra its own atom; ra the literal 0x82e98 *)
assert (Hm : ms_mem ms = mem4).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [Z_to_bv 5 1] -> getr (ms_regs ms) rr = getr regs4 rr).
{ eapply (regs_kept_of_st_ok rsegs _ _ ms regs4 rt_extra (w_H W4) _ HS HAE). vm_compute. reflexivity. }
assert (HRA : getr (ms_regs ms) 1 = Z_to_bv 64 0x82e98).
{ rewrite (hk_getr_eq (ms_regs ms) 1 (Z_to_bv 5 1)) by reflexivity.
  rewrite (st_ok_restrict_reg rsegs (w_H W4) _ _ ms (Z_to_bv 5 1) HS).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    replace (sr_get (ss_regs ss) (Z_to_bv 5 1)) with (SLit 0x82e98) by (vm_compute; reflexivity) end.
  reflexivity. }
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (3 * (e_cap e + 1))).
{ rewrite RK by hk_rk. rewrite (hk_getr_eq regs4 10 (Z_to_bv 5 10)) by reflexivity. exact C10. }
assert (HLV : blocks_bytes S4 + 3 * (e_cap e + 1) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly4 S4), (bsum_perm _ _ Hperm4), bsum_app,
    <- (blocks_bytes_bsum B (h_ly rsegs hx) (h_S rsegs hx)).
  unfold hq_blocks3, bsum. cbn [fold_right snd]. change Layout.PP_SIZE with 19744 in *. lia. }
assert (HSP : spZ (ms_regs ms) = spZ (h_regs rsegs hx) + (e_R e - spZ (h_regs rsegs hx))).
{ unfold spZ at 1. rewrite RK by hk_rk. rewrite Hsp4. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : e_R e - spZ (h_regs rsegs hx) <= 0) by lia.
assert (HBUD : ASTACK - (e_R e - spZ (h_regs rsegs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RK by hk_rk; exact Hgp4).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RK by hk_rk; exact Htp4).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x82e98)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S4 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x82e98) by (unfold raZ; rewrite HRA; apply unsigned_lit_small; lia).
assert (HCH : chain_pre ly4 (aview rsegs (w_H W4) mem4) (ms_regs ms) (hk_ch hx)).
{ apply (achain_chain_pre ly4 _ (e_R e) (spZ (h_regs rsegs hx))).
  - apply (achain_ly_top (h_ly rsegs hx) ly4 _ _ _ _ Etop). unfold hk_ch.
    apply (hk_chain (h_ly rsegs hx) (aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx))).
    + exact Hch0.
    + lia.
    + intros a Ha. apply F1; lia.
    + exact R8.
    + exact R16.
    + exact Hra40.
    + lia.
    + exact HS8.
    + lia.
  - rewrite HSP. lia.
  - unfold s0Z. rewrite RK by hk_rk. rewrite (hk_getr_eq regs4 8 (Z_to_bv 5 8)) by reflexivity.
    rewrite C8. unfold w64. apply unsigned_lit_small. lia.
  - rewrite HRAZ. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) (hk_ch hx)) (as_universe B)).
{ apply HTRACE_C45; [exact Hra0 | rewrite HRAZ; reflexivity]. }
(* the machine state at 0x53060 = pc_wrap_malloc *)
rewrite (st_ok_restrict_mkst rsegs (w_H W4) _ _ ms HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
rewrite Hm. rewrite Hm in HJ4.
eapply SRr_mono.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML (AMALLOC fx2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ4 HA10 HN HLV HSP HAL HNEG HBUD HGP HTP HRA HRAOK HEV HCH HTR). }
(* 3. the post at C5 *)
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & out & Ec5 & HJ5 & Hpres5 & H105 & Hfr5 & Hout & Hab5 & Hkept5).
replace (spZ (h_regs rsegs hx) + (e_R e - spZ (h_regs rsegs hx))) with (e_R e) in Hkept5 by lia.
pose proof Hkept5 as (KK1 & KK2 & _ & KK4 & _ & _).
pose proof HJ5 as (HAR5 & Hly5 & _).
pose proof Hly5 as (_ & _ & _ & _ & _ & EF5 & _).
(* the callee-saved registers of C4 *)
assert (KR : forall rr, acallee_saved rr -> getr regs5 (Z_to_bv 5 rr) = getr regs4 (Z_to_bv 5 rr)).
{ intros rr Hr. rewrite (Hpres5 rr Hr). apply RK.
  - rewrite (hk_csaved rr Hr). unfold acallee_saved in Hr. lia.
  - intros [Hx|[]]. apply (f_equal (@bv_unsigned 5)) in Hx. rewrite (hk_csaved rr Hr) in Hx.
    change (bv_unsigned (Z_to_bv 5 1)) with 1 in Hx. unfold acallee_saved in Hr. lia. }
(* the blocks: pp and pod live at C4, out appended, each apart from out *)
assert (Hin4 : forall b, In b (hq_blocks3 e) -> In b (ablocks B ly4 S4)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm4)). apply in_or_app. right. exact Hb. }
assert (Hin5 : forall b, In b (ablocks B ly4 S4) -> In b (ablocks B ly5 S5)).
{ intros b Hb. rewrite Hab5. apply in_or_app. left. exact Hb. }
assert (Hpp4 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly4 S4)) by (apply Hin4; cbn; left; reflexivity).
assert (Hpod4 : In (e_pod e, e_len e) (ablocks B ly4 S4)) by (apply Hin4; cbn; right; left; reflexivity).
assert (Hout5 : In (out, 3 * (e_cap e + 1)) (ablocks B ly5 S5))
  by (rewrite Hab5; apply in_or_app; right; left; reflexivity).
assert (Hapart : forall p m, In (p, m) (ablocks B ly4 S4) ->
  p + req_size m <= out \/ out + req_size (3 * (e_cap e + 1)) <= p).
{ intros p m Hb. apply in_split in Hb as (l1 & l2 & El).
  pose proof (sep_blocks_pos rsegs B LAWS ly5 S5 W5 mem5 md5 (p, m) (out, 3 * (e_cap e + 1)) l1 l2 [] HAR5
    ltac:(rewrite Hab5, El, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
assert (Hfresh : ~ In (out, 3 * (e_cap e + 1)) (ablocks B (h_ly rsegs hx) (h_S rsegs hx))).
{ intros Hx. assert (Hx4 : In (out, 3 * (e_cap e + 1)) (ablocks B ly4 S4))
    by (apply (Permutation_in _ (Permutation_sym Hperm4)); apply in_or_app; left; exact Hx).
  pose proof (Hapart _ _ Hx4) as Hd. rewrite Hrq in Hd. lia. }
(* the frame for locals: at F in both layouts, apart from out and from out's range in the shadow *)
assert (HinF4 : In (HQ_CID, pos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
assert (HinF5 : In (HQ_CID, pos) (frames S5)) by (rewrite Hfr5; exact HinF4).
assert (FA4 : frame_addr ly4 HQ_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EF4; reflexivity).
assert (FA5 : frame_addr ly5 HQ_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EF5; reflexivity).
assert (Hfb : fs_frame_bytes HQ_CID = 1024) by reflexivity.
pose proof (sep_block_frame rsegs B LAWS ly5 S5 W5 mem5 md5 out (3 * (e_cap e + 1)) HQ_CID pos HAR5 Hout5 HinF5)
  as HdF.
rewrite FA5, Hfb in HdF. unfold zdisjoint in HdF. cbn [fst snd] in HdF.
destruct (al_frames _ _ LAWS ly4 S4 W4 mem4 md4 HQ_CID pos HAR4 HinF4) as (HF32 & HFapp & _).
rewrite FA4, Hfb in HFapp.
destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 out (3 * (e_cap e + 1)) HAR5 Hout5) as (_ & _ & _ & Hoapp & _).
assert (HshF : forall i, 0 <= i < 128 ->
  ~ (out <= shadow_addr (e_F e) + i < out + req_size (3 * (e_cap e + 1)))).
{ intros i Hi. pose proof C1 as [_ C1h]. exact (hk_shadow_apart _ _ _ _ HFapp Hoapp C1h Hi). }
(* the two blocks' bytes: kept by the call when they lie apart from out *)
assert (Hkb : forall p m i, In (p, m) (ablocks B ly4 S4) -> 0 <= i < req_size m ->
  aview rsegs (w_H W5) mem5 (p + i) = aview rsegs (w_H W4) mem4 (p + i)).
{ intros p m i Hb Hi. apply (KK2 p m i Hb Hi). pose proof (Hapart p m Hb). cbv beta. lia. }
assert (Hrq_pod : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
(* the real frame above R: kept by the call *)
assert (Hkr : forall a, e_R e <= a < spZ (h_regs rsegs hx) -> aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. apply KK1; lia. }
(* the errno cell: readable at the new memory *)
destruct (hk_errno_rd B (w_H W5) mem5 errno_low) as (ev5 & Hev5).
(* ===== hq_at_C5 ===== *)
unfold hq_at_C5. exists out, ev5, ly5, S5, regs5, mem5, md5.
split; [rewrite Ec5; reflexivity|].
split; [exact Hout|].
split; [exact H105|].
split; [exact KR|].
split; [exact Hfr5|].
split; [exact Hab5|].
split; [exact Hkept5|].
split.
{ pose proof (Hapart _ _ Hpod4) as Hd. rewrite Hrq_pod, Hrq in Hd. exact Hd. }
(* ===== hq_cut_C5 at the env with out ===== *)
unfold hq_cut_C5, hq_at_cut.
split.
{ split; [exact HJ5|].
  split.
  { change (hq_blocks5 (hq_env_out e out)) with (hq_blocks3 e ++ [(out, 3 * (e_cap e + 1))]).
    rewrite Hab5, app_assoc. apply Permutation_app_tail. exact Hperm4. }
  split.
  { change (hq_blocks5 (hq_env_out e out)) with (hq_blocks3 e ++ [(out, 3 * (e_cap e + 1))]).
    apply Forall_app. split; [exact Hfresh4|].
    apply Forall_cons; [|apply Forall_nil]. cbv beta. cbn [fst]. split; [exact Hfresh | lia]. }
  split.
  { rewrite (hk_getr_eq regs5 2 (Z_to_bv 5 2)) by reflexivity. rewrite (KR 2) by (unfold acallee_saved; lia).
    rewrite (hk_getr_eq regs4 (Z_to_bv 5 2) 2) by reflexivity. exact Hsp4. }
  split.
  { rewrite (hk_getr_eq regs5 3 (Z_to_bv 5 3)) by reflexivity. rewrite (KR 3) by (unfold acallee_saved; lia).
    rewrite (hk_getr_eq regs4 (Z_to_bv 5 3) 3) by reflexivity. exact Hgp4. }
  split.
  { rewrite (hk_getr_eq regs5 4 (Z_to_bv 5 4)) by reflexivity. rewrite (KR 4) by (unfold acallee_saved; lia).
    rewrite (hk_getr_eq regs4 (Z_to_bv 5 4) 4) by reflexivity. exact Htp4. }
  split; [exact Hgeo|].
  split.
  { (* hi_L5: hi_L4 kept (its cells lie above R), then a0 = out *)
    assert (HcutA : hd_cut rsegs (w_H W5) mem5 regs4 e (hi_L4 headamp_himg_A)).
    { apply (hm_cut_kept rsegs (w_H W4) mem4 (w_H W5) mem5 regs4 regs4 e _ HL4).
      intros f Hf. cbn [hi_L4 headamp_himg_A] in Hf. unfold headamp_A_L45 in Hf. cbn [In] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv]; first [reflexivity | (intros i Hi; apply Hkr; lia)] |]).
      destruct Hf. }
    assert (HcutA' : hd_cut rsegs (w_H W5) mem5 regs4 (hq_env_out e out) (hi_L4 headamp_himg_A)).
    { unfold hd_cut in HcutA |- *. apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) HcutA f Hf) as Hx.
      cbn [hi_L4 headamp_himg_A] in Hf. unfold headamp_A_L45 in Hf. cbn [In] in Hf.
      repeat (destruct Hf as [<-|Hf]; [exact Hx|]). destruct Hf. }
    apply (headamp_A_site_cut5 rsegs (w_H W5) mem5 mem5 regs4 regs5 (hq_env_out e out) HcutA').
    - rewrite (hk_getr_eq regs5 (Z_to_bv 5 10) 10) by reflexivity. exact H105.
    - intros rr _ Hrr. apply KR. cbn [In] in Hrr. unfold acallee_saved. lia.
    - intros o _ i _. reflexivity. }
  split.
  { (* the frame's shadow, kept by the call's frame clause *)
    apply (hm_fsh_kept rsegs (w_H W4) mem4 (w_H W5) mem5 (e_F e) _ Hfsh4).
    intros i Hi. assert (Hl : length (hi_shA headamp_himg_A) = 80%nat) by (vm_compute; reflexivity).
    rewrite Hl in Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi.
    apply (KK4 HQ_CID pos); [exact HinF4 | right | cbv beta; apply HshF; lia].
    unfold in_zr. cbn [fst snd]. rewrite FA4, Hfb. change (1024 / 8) with 128. lia. }
  { (* the thirteen saves and the flag cell, and the three float saves *)
    split.
    - assert (Hcl5 : Forall (fun f => hd_at rsegs (w_H W5) mem5 regs5 e (fst f) (snd f))
        (hq_cells (h_regs rsegs hx) (flag_addr (h_ly rsegs hx) HQ_CID pos))).
      { apply (hm_atl_kept rsegs (w_H W4) mem4 (w_H W5) mem5 regs4 regs5 e _ Hcl4).
        intros f Hf. unfold hq_cells, hq_saves_L in Hf. apply in_app_or in Hf as [Hf|Hf].
        + apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj. cbn [fst hm_keeps hd_xv].
          intros i Hi. apply Hkr. lia.
        + destruct Hf as [<-|[]]. cbn [fst hm_keeps hd_xv]. intros i Hi. unfold HQ_FLAG.
          apply (KK4 HQ_CID pos); [exact HinF4 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA4, Hfb; lia
          | cbv beta; lia]. }
      apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) Hcl5 f Hf) as Hx.
      unfold hq_cells, hq_saves_L in Hf. apply in_app_or in Hf as [Hf|Hf].
      + apply in_map_iff in Hf as (j & <- & _). exact Hx.
      + destruct Hf as [<-|[]]. exact Hx.
    - destruct Hfs4 as (v0 & v1 & v2 & G0 & G1 & G2). exists v0, v1, v2.
      cbn [hd_at hd_xv hq_env_out e_S] in G0, G1, G2 |- *.
      split; [|split];
      (eapply (hd_val_mem_kept rsegs (w_H W4) (w_H W5) mem4 mem5); [|eassumption]);
      intros i Hi; apply Hkr; lia. } }
split; [exact Hfrm|].
split.
{ (* the record's data *)
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hlenb|].
  split.
  { apply (hd_garr8_kept rsegs (w_H W4) (w_H W5) mem4 mem5 (e_pp e)); [|exact Hpp].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    pose proof (Layout.length_pp_bytes r Hwf) as HLp.
    apply (Hkb _ _ _ Hpp4). change (req_size Layout.PP_SIZE) with 19744. change Layout.PP_SIZE with 19744 in HLp. lia. }
  split.
  { apply (hd_garr8_kept rsegs (w_H W4) (w_H W5) mem4 mem5 (e_pod e)); [|exact Hpod].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    apply (Hkb _ _ _ Hpod4). rewrite Hrq_pod. lia. }
  split; [exact Hpod16|].
  split.
  { exact (proj2 (hm_blk_ra rsegs B ly5 S5 W5 mem5 md5 (e_pod e) (e_len e) (e_pod e) (e_len e) HAR5 (Hin5 _ Hpod4)
      ltac:(lia) ltac:(rewrite Hrq_pod; lia)) ltac:(lia)). }
  split; [exact Hamem|]. split; [exact Hcap|]. split; [exact Hnull | exact Hrc]. }
split.
{ exact (proj1 (hm_blk_ra rsegs B ly5 S5 W5 mem5 md5 (e_pod e) (e_len e) (e_pod e) (e_len e) HAR5 (Hin5 _ Hpod4)
    ltac:(lia) ltac:(rewrite Hrq_pod; lia))). }
split.
{ exact (proj1 (hm_blk_ra rsegs B ly5 S5 W5 mem5 md5 out (3 * (e_cap e + 1)) out (3 * (e_cap e + 1))
    HAR5 Hout5 ltac:(lia) ltac:(rewrite Hrq; lia))). }
exact Hev5.
Qed.
(* inside the Section: the kernel's axioms and the Section hypotheses named in the header *)
Print Assumptions hq_A_S_C45.
End d.
End b.
Print Assumptions hq_A_S_C45.
