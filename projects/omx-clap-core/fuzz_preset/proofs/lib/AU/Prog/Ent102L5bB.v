(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, PIN sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa5):
   SEGMENT L5b of LLVMFuzzerTestOneInput (entry 0x816cc), the call check_round_trip (&doc), proved against
   lib/A/Ent102CutsB.v's `seg_L5b_stmt` (cut_rm E fk t D -> cut_crt E fk t D; budget index 7 -> 8):
     +0x300  mv a0, s5                  a0 := &doc = fk + 32 (ec_rkd)
    +0x304  jal ra, check_round_trip   the batch kit's ENTRY-KEYED check_round_trip text (lib/A/PRH_FnCheck.v
                                       tcheck_round_trip_specX through ec_texts' et_check_round_trip; the retired
                                       grant form and its Section argument are gone, owner decision (A)) by
                                       YCbqGcallW.v aj_call_xWF at the callee window e1 = 0, FP = [] (the text's own),
                                       at the run position of cut_rm with its run premise round_trip t
                                       (Ent102TailB.v ec_rt_run) and its consumer window (Ent102TailB.v ec_rt_window,
                                       from lib/A/Prog/Ent102Win.v cons_from_after_cno)
     +0x308  the return site = EC_AR_CRT, where cut_crt (r = 0 only) is assembled from the composed journal, the
             callee's journal (frame, saved block, frame shadow, flag word) and the kit's post (Lam' ~ Lam, the blocks
             unchanged, the ledger, the tree at &doc, g_most kept, own' = 0, ran' = 0, the count growth
             ck_crt_count t cset, the exact advance by |round_trip t|).
   (A' 0x818e0 -> 0x818e8; B' 0x819cc -> 0x819d4.)
   STATEMENT: lib/A/Ent102CutsB.v blob 856984d6c3cd (a working branch b1bc025047ea, CUT STABLE of the
   decff kit sync on the exact room position: ec_inv's ledger is `exists most own, prh_ledger .. most own`):
   seg_L5b_stmt, cut_rm, cut_crt,
   ec_hyps (ech_texts / ech_img / ech_univ / ech_ccut_ok
   / ech_lcut_ok / ech_pay, by name), ec_pre's parts by TYPE (l5b_pre: the e_i0 and e_sm ties among them); ec_img's
   ei_sio / ei_sio_frame / ei_frame / ei_pst_ro / ei_lits / ei_fp / ei_rets, ec_texts' et_stk, ec_univ's eu_crt,
   ec_pay's epay_crt / ecov_crt.
   LISTING: lib/B/Listing_prog.v blob 1ab147923c5d with the PAListing PL_102_B of lib/A/Ent102PLB.v; the image half
   stays generic ({PA : PAImg B_prog_listing}; lib/A/PAImg_prog.v is not loaded, no vm_compute on pa_val / pa_sigma).
   THE BATCH KIT'S TEXT: lib/A/PRH_FnCheck.v tcheck_round_trip_specX, read at
   commit b1ed4e6c944d + the CallA / CallB re-fit
   3ea93d01b97c. THE WILD BUDGET: ec_inv's journal is budgeted
   (`exists WS, ajournal_xw .. WS /\ wbudget [] wk WS`); each step's materialized model keeps the same WS (the local
   l5b_ajw_wvb: rebase, materialize, unbase0); the call goes through YCbqGwild.aj_call_xWFb with P := wbudget []
   (prh_wk F_check_round_trip), its room by Ent102CutsB.v ec_room_at from ec_wk_rm, and cut_crt's budget ec_wk_crt
   by YCbqGwild.wbudget_app. The text's LAST premise (the kit 4b8f95c0455c), the live real stack `YGcallStackUp.astack_up_x
   segs ly W (spZ regs) mem` at the call, is ec_pre's entry fact at e_sp0 E carried by the cut's journal to the
   callee's sp e_B E (a Theorem Labs lane's YGcallStackUp.astack_up_at_xw, any wild budget; the step of a Theorem Labs lane's
   crt_up_at_call_B, a working branch dd5c35f62c70). No DW; its run is at ReaderRes.jr_strtod (no rp_sm binder), so
   the cut's facts over e_sm E are rewritten through ec_pre's tie Hsm, including the post's position (an `exact`
   across the two strtod terms does not terminate). Its ledger premise `prh_ledger .. most 0` is ec_inv's ledger at
   the cut's ec_most / ec_own_is cells (lib/AU/Prog/Ent102CallB.v ec_ledger_cells, the shared copy). cut_crt's new
   ec_pjf (the free order) is kept across the call by PRH_PjOrder.pj_foR_frame: the root node by the callee
   journal's frame clause, the blocks by its block clause, writability by l6f_geom and the block law.
   PURE FACTS CITED: lib/A/Ent102ReqA.v ec_req_bound_holds (RQA_crt t <= g_most and RQ_crt t + cf_head <
   cf_malloc_max), lib/Prog/SlotSizes.v wlen_false_read / wlen_true_read (the two writer lengths).
   ONE NAMED PREMISE: sat_rq_crt, Ent102ReqA.v's own premise in its exact text (owner a Theorem Labs lane). It is DISCHARGED at
   the preset instance by Ent102ReqA.v ec_req_bound_holds_preset (a working branch 1d8b9491bb66), through
   a Theorem Labs lane's lib/Spec/PjReqBoundC.v (blob 196cc949112c) rq_crt_abs `RQ_crt t + cf_head <= 352321446` /
   rq_crt_cf_bound, stated at cp := CfParamsPreset.CfParams_preset. This Section is generic over {cp : CfParams},
   where the fact is not derivable, so the premise stays named here and the instantiation cites that lemma.
   TEMPLATES TAKEN (by path): the call and the cut's register / journal handling follow lib/A/Prog/Ent102L6Af.v of
   a working branch (seg_L6f_B); the step rules, the frame geometry and the pure list facts are
   lib/A/Prog/Ent102L6BfLem.v's (blob a37e0dc13d12, by path); the chain and the call context are
   lib/A/Prog/Ent102CallB.v's (ec_chain_at, ec_ctx_call_img).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L5b (reuse search: proof-index LLVMFuzzerTestOneInput
   check_round_trip check_reject_clean_starved on main / ossv/recipes / ossv/candidates / release/pau-projects-recipes,
   exit=0, + 364 cold refs by name and by every cut address, checker CONFIRM; NEW walk on the #102 pins).
   NUMERALS: 0x300 / 0x304 / 0x308 are this lane's slot offsets (DERIVED: EC_AR_RM - EC_BASE, +4, +8); 128 / 120 / 104
   / 88 / 56 / 32 / 16 / 8 are LENGTHs; 144 is EC_SAVE + 16; 32768 is LLVMF_STK; 3 * 2 ^ 20 is the text's length
   bound; 2 ^ 40, 2 ^ 47, 2 ^ 62, 2 ^ 64 and the ASan band constants are the engine's range facts. No ADDRESS.    THE B' TWIN of lib/A/Prog/Ent102L5bA.v (row LL5b, seg_L5b_A, Qed at 499d46f7590a (a working branch)), made with
   a Theorem Labs lane's port/a2b.py and then re-pointed at image B' by hand: L := B_prog_listing with the PAListing
   PL_102_B of lib/B/Ent102PLB.v, the statement from lib/AU/Ent102CutsB.v, and the two image-side helper
   modules swapped for their B twins (lib/AU/Prog/Ent102CallB.v, Ent102L6BfLem.v, same lemma names). The kit
   texts (lib/A/PRH_*.v) and the image-free lane helpers (Ent102TailA, Ent102GrantA, Ent102ReqA) are generic
   over the listing class, so both images take the same ones.
   THE CUT: +0x300 at 0x819cc -> cut_crt +0x308 at 0x819d4.
   THE OFFSETS the internal file a2b.py REPORTS UNTRANSLATED (+0x1bc, +0x300 .. +0x320) ARE OFFSETS, NOT ADDRESSES, and the
   row's own table says one offset table serves both images. Checked against the ACCEPTED twin pair
   Ent102L5aA / Ent102L5aB: both carry 0x2f8 / 0x2fc / 0x300 unchanged, while every real address differs
   (A' 0x815e0 vs B' 0x816cc).
*)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YGcfTreeVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger PjWriteHyp SlotSizes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102ReqA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102L6BfLem Ent102CallB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102TailB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102GrantA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section L5B. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
(* the cut file's two budget functions (this lane goes from cut 7 to cut 8) *)
Variables ec_ccut ec_lcut : @ecx rc B_prog_listing PA -> nat -> Z.
(* THE ONE NAMED PREMISE: check_round_trip's per-request ceiling, lib/A/Ent102ReqA.v's own premise sat_rq_crt in its
   exact text. At cp := CfParams_preset it is Ent102ReqA.v ec_req_bound_holds_preset's (via PjReqBoundC.v
   rq_crt_cf_bound; header); this Section is generic over cp, where it is not derivable (owner a Theorem Labs lane) *)
Hypothesis sat_rq_crt :
  forall (x : list Z) (t : PjTree.jv), Z.of_nat (length x) <= EC_NMAX -> ck_read x = Some t ->
  RQ_crt t + cf_head < cf_malloc_max.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).
(* lane L5b is after check_no_overread's frees: its cuts, journals and lane are at wle' over the fixed zone
   (Ent102CutsB.v ec_invR / ec_laneR WLE') *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).

(* one conjunct of ec_pre by its TYPE (Ent102CallB.v ec_conj_pick), so this row does not depend on ec_pre's order *)
Local Ltac l5b_pre H := clear - H; unfold ec_pre in H; ec_conj_pick H.

(* The cut's journal is budgeted (YCbqGwild.ajournal_xw at the spent wild budget WS). A step's
   materialized model keeps it at the same WS: rebased to the empty budget (YCbqGwild.ajournal_xw_rebase),
   materialized there (YCbqG.ajournal_x_materialize), put back on WS by its own wild inclusion
   (YCbqGwild.ajournal_xw_unbase0 with ajx_wild) - a Theorem Labs lane's l5d_ajw_wvb (LL5dB at commit 1e05beefe2a1) *)
(* over the world relation R of the journal (this lane's is wle', the free move) *)
Lemma l5b_ajw_wvb : forall {R : world SEGS -> world SEGS -> Prop} STK sp0 FP ly S Hp (W : world SEGS) mem md own ly' S'
  Hp' (W' : world SEGS) mem' md' k WS X,
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  ajournal_xwR (SK := SK) SEGS B PST ARc R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem'
    (with_vm_backing (m_vm_lazy md') X md') k WS.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS X HJ.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARc R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem'
  (with_vm_backing (m_vm_lazy md') X md') k (st_depot S') WS).
- apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS pa_segs_low R).
  exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARc R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md'
    k WS HJ).
- exact (ajxR_wild HJ).
Qed.

Theorem seg_L5b_B :
  @seg_L5b_stmt fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L5b_stmt, ec_laneR.
intros E fk t D HYP W c Hcut.
pose proof (ech_texts B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut HYP) as HTX.
pose proof (ech_img B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut HYP) as HIMG.
pose proof (ech_univ B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut HYP) as HUNIV.
pose proof (ech_ccut_ok B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut HYP) as HCC.
pose proof (ech_lcut_ok B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut HYP) as HLC.
pose proof (ech_pay B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut HYP) as HPAY.
pose proof (ei_sio B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hsio.
pose proof (ei_sio_frame B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hsioframe.
pose proof (ei_frame B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hfrm.
pose proof (ei_pst_ro B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hpstro.
pose proof (ei_lits B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG HIMG) as Hlits.
pose proof (eu_crt B EC_RA HUNIV) as HUCRT.
pose proof (et_stk B SK EC_RA EC_A_MOD_AT EC_A_STAMP HTX) as HSTKT.
pose proof (et_check_round_trip B SK EC_RA EC_A_MOD_AT EC_A_STAMP HTX) as CRT.
pose proof (epay_crt ec_ccut ec_lcut HPAY) as PCRT.
pose proof (ecov_crt ec_ccut ec_lcut HPAY) as VCRT.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt & k & tk & trp & Hat & Hinv & Hrof & HCC7
  & HLC7 & Hrkd & Hfr & HnN & R23 & Htk & Hread & HLD & HND & HPJF & Hmost & Hown0).
destruct Hat as (fy & Hfz & Hkept & Hc). subst c.
destruct Hinv as ((WS0 & HJ & HWB) & HOWN & HLED0 & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY0 & HPERM & HBYTES & HMN).
(* the ledger at the cut's two harness cells: g_most = PJ_ALLOC_BOUND n (ec_most), g_own_ran_out = 0 *)
destruct HLED0 as (mostL & ownL & HLED0).
pose proof (ec_ledger_cells B ly S Hp W mem Lam peak cnt SIZE_MAX 0 mostL ownL _ _ HLED0 Hmost Hown0) as HLED.
clear HLED0.
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & Hflagw). subst own.
assert (HPREX : afn_pre_x SEGS B ARc LLVMF_STK (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [])
  by (l5b_pre HPRE).
assert (HS0E : s0Z (e_regs E) < YM05.alloc_ceiling) by (l5b_pre HPRE).
assert (HRAE : raZ (e_regs E) = EC_RA) by (l5b_pre HPRE).
assert (HNC : (e_n E = 0 /\ e_p E = EC_EMPTY) \/
  (0 < e_n E < 2 ^ 26 /\ In (e_p E, e_n E) (ablocks B (e_ly E) (e_S E)))) by (l5b_pre HPRE).
assert (HNL : e_n E = Z.of_nat (length (e_pl E))) by (l5b_pre HPRE).
assert (HFR0 : frames (e_S E) = []) by (l5b_pre HPRE).
assert (HRO0 : arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B
  (aview SEGS (w_H (e_W E)) (e_mem E))) by (l5b_pre HPRE).
assert (HSIO0 : EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E))) by (l5b_pre HPRE).
assert (HC62 : e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30) by (l5b_pre HPRE).
assert (Hi0E : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E))) by (l5b_pre HPRE).
assert (Hsm : e_sm E = ReaderRes.jr_strtod) by (l5b_pre HPRE).
pose proof HPREX as (_ & _ & Hra40 & Hgp0 & Htp0 & _ & _ & _ & _).
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARc WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJb.
pose proof HJb as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
repeat lazymatch type of Hfrs with context [frames (set_depot ?d ?s)] =>
  change (frames (set_depot d s)) with (frames s) in Hfrs end.
pose proof HAR as (HARcf & HXS).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (l6f_LAWS B).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfrs1 : frames S = [(LLVMF_FS_CLASS, pos)]) by (rewrite Hfrs, HFR0; reflexivity).
destruct (l6f_geom B ly S Hp W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh).
change (EC_FRAME_BYTES / 8) with 16 in Gsh.
unfold EC_FRAME_BYTES in Gceil, Gfr, Gapp.
destruct Hrkd as (Hrk & R21).
pose proof Hrk as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
pose proof Hfr as (Hsaved & Hshv & Hal32).
pose proof Hsaved as (Sra & S8 & _).
destruct HROOM as (hist0 & HR0).
(* the input: its length is e_n E <= EC_NMAX, and a reading of it exists (ck_read) *)
assert (HLX : Z.of_nat (length (e_x E)) = e_n E) by (unfold e_x, ec_bytes; rewrite length_map; lia).
assert (HLXN : Z.of_nat (length (e_x E)) <= EC_NMAX) by lia.
pose proof (Ent102ReqA.ec_req_bound_holds sat_rq_crt (e_x E) HLXN) as (_ & HRQ).
destruct (HRQ t Hread) as (_ & _ & HRQA & HRQC).
(* ---- the arithmetic of the cut: sp0, A = (sp0 - 128) & -32, the frame fk ---- *)
assert (Rsp : YM05.alloc_ceiling + 32768 <= e_sp0 E <= 2 ^ 47) by lia.
assert (Hsp16 : e_sp0 E = 16 * (e_sp0 E / 16))
  by (pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D0; rewrite Hal16 in D0; lia).
assert (EA : e_B E = (e_sp0 E - 128) / 32 * 32).
{ unfold e_B, ec_B, EC_SAVE. apply l6f_land_neg32. lia. }
assert (HA32 : e_B E mod 32 = 0) by (rewrite EA; apply Z.mod_mul; lia).
assert (HAb : e_sp0 E - 144 <= e_B E <= e_sp0 E - 128).
{ rewrite EA.
  pose proof (Z.div_mod (e_sp0 E - 128) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (e_sp0 E - 128) 32 ltac:(lia)) as D2. lia. }
assert (Hfk32 : fk = 32 * (fk / 32))
  by (pose proof (Z.div_mod fk 32 ltac:(lia)) as D0; rewrite Gal in D0; lia).
assert (Hfk8 : fk = 8 * (fk / 8)).
{ pose proof (Z.div_mod fk 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound fk 8 ltac:(lia)) as D1. lia. }
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
assert (HSPr : spZ regs = e_B E).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
(* ======== +0x300  mv a0, s5 ======== *)
unfold cfg_at.
change (w64 EC_AR_RM) with (Z_to_bv 64 (BASE + 0x300)).
l6f_fd 0x300 Hpl1 Hd1.
eapply (l6f_step_addiR (fx := fy) WLE' W regs mem md _ 0x300 _ _ _ _ (10%bv : bv 5) (getr regs (21%bv : bv 5))
  ltac:(lia) Hpl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (21%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (l5b_ajw_wvb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJm1.
(* ======== +0x304  jal ra, check_round_trip ======== *)
change (0x300 + 4) with 0x304.
l6f_fdc 0x304 Hpl2.
eapply (l6f_step_callR (fx := fy) WLE' W _ mem _ _ 0x304 _ _ (1%bv : bv 5) ltac:(lia) Hpl2).
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (l5b_ajw_wvb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJm1) as HJm2.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
(* ---- the callee's registers ---- *)
assert (HSPC : spZ regsc = e_sp0 E + (e_B E - e_sp0 E)).
{ unfold spZ. rewrite Eregsc, !getr_other by l6f_regne. rewrite R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HS0C : s0Z regsc = e_sp0 E).
{ unfold s0Z. rewrite Eregsc, !getr_other by l6f_regne. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by l6f_regne. rewrite R3. exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by l6f_regne. rewrite R4. exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + 0x308)).
{ rewrite Eregsc. apply getr_same. l6f_regne. }
assert (HA10 : getr regsc 10 = w64 (ec_doc fk)).
{ rewrite Eregsc, getr_other by l6f_regne. rewrite getr_same by l6f_regne. exact R21. }
l6f_fd 0x308 Hpl3 Hd3.
pose proof (l6f_img_bounds B ly S Hp W mem md (BASE + 0x308) HAR
  (l6f_slot_img (PA := PA) 0x308 _ ltac:(lia) Hpl3)) as HRIMG.
unfold kImgLo, kImgEnd in HRIMG.
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x308)))
  by exact (ret_ok_codeptr_v (PI := PA) 0x308 ltac:(lia) eq_refl).
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 0x308))) by (rewrite unsigned_lit_small by lia; lia).
assert (HRAZ : raZ regsc = EC_AR_CRT) by (unfold raZ; rewrite HRA1, unsigned_lit_small by lia; reflexivity).
assert (HRAC : raZ regsc < YM05.alloc_ceiling) by (rewrite HRAZ; unfold EC_AR_CRT, EC_BASE; lia).
(* ---- the callee's stack: STK_check_round_trip - (A - sp0) <= LLVMF_STK (et_stk, ei_frame) ---- *)
assert (HSTKF : 0 <= STK_check_round_trip).
{ unfold STK_check_round_trip. apply Z.add_nonneg_nonneg; [apply pi_frame_nonneg | apply l6f_zmaxl_nonneg]. }
assert (HBUD : STK_check_round_trip - (e_B E - e_sp0 E) <= LLVMF_STK).
{ unfold STK_LLVMFuzzerTestOneInput in HSTKT.
  lazymatch type of HSTKT with _ + zmaxl ?l <= _ =>
    assert (Hz : STK_check_round_trip <= zmaxl l)
      by (apply l6f_zmaxl_in; cbn [In]; do 6 right; left; reflexivity) end.
  unfold EC_SAVE in Hfrm. pose proof (pi_frame_nonneg F_LLVMFuzzerTestOneInput). lia. }
assert (HO16 : (e_B E - e_sp0 E) mod 16 = 0).
{ pose proof (Z.div_mod (e_B E) 32 ltac:(lia)) as D1. rewrite HA32 in D1.
  replace (e_B E - e_sp0 E) with ((2 * (e_B E / 32) - e_sp0 E / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
(* ---- the frame chain at the call (Ent102CallB.v ec_chain_at) and the call's context ---- *)
assert (Hra0 : 0 <= raZ (e_regs E) < 2 ^ 64) by (unfold raZ; apply u64_range).
assert (Hs00 : 0 <= s0Z (e_regs E) < 2 ^ 64) by (unfold s0Z; apply u64_range).
destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (e_sp0 E + (e_B E - e_sp0 E)) (e_sp0 E) (raZ (e_regs E))
  (s0Z (e_regs E)) Sra S8 Hra0 Hs00 HS0E Hra40 ltac:(lia)
  ltac:(rewrite Hsp16; replace (16 * (e_sp0 E / 16)) with ((2 * (e_sp0 E / 16)) * 8) by lia; apply Z.mod_mul; lia)
  ltac:(rewrite Etop; lia) ltac:(lia)) as (ch1 & Hch0 & Hsp1).
assert (Hch : achain ly (aview SEGS (w_H W) mem) (e_sp0 E + (e_B E - e_sp0 E)) (s0Z regsc) ch1)
  by (rewrite HS0C; exact Hch0).
rewrite HRAE in Hsp1.
assert (HCTX : prh_ctx (ec_ctx0 EC_RA) F_check_round_trip (raZ regsc :: spine ch1)).
{ rewrite HRAZ. apply (ec_ctx_call_img B EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    F_check_round_trip EC_AR_CRT ch1 HIMG); [|exact Hsp1].
  unfold ec_call_rets. cbn [In]. do 16 right. left. reflexivity. }
(* ---- the callee's view of the doc: the tree, its blocks, their visibility, the root in this call's frame ---- *)
assert (HTREE : ck_tree_ok ly S Lam W mem (ec_doc fk) t D).
{ split; [exact HND|].
  split; [intros bk Hbk; exact (Permutation_in _ (Permutation_sym HLD) Hbk)|].
  split.
  { unfold PRH_FnWriter.prhWriter_tree_vis.
    apply (YGcfTreeVis.tree_vis_of_blocks_cf SEGS B ly S Hp W mem md D HARcf).
    intros a k0 HinD.
    assert (HinL : In (a, k0) Lam) by exact (Permutation_in _ (Permutation_sym HLD) HinD).
    pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAX 0 a k0 _ _ HLED HinL) as (_ & Hb & Hh & _).
    split; [exact Hb | exact Hh]. }
  split; [unfold ec_doc; rewrite Hfk32; replace (32 * (fk / 32) + 32) with ((4 * (fk / 32) + 4) * 8) by lia;
          apply Z.mod_mul; lia|].
  split.
  { exists LLVMF_FS_CLASS, pos. split; [exact Hin|]. rewrite <- Hfkeq.
    change (fs_frame_bytes LLVMF_FS_CLASS) with 128. unfold ec_doc. lia. }
  intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  replace (SHADOW_OFF + x / 8) with (shadow_addr fk + (x / 8 - fk / 8)) by (rewrite Esh; lia).
  apply (l6f_shadow_zero (PA := PA) (w_H W) mem (shadow_addr fk) Hshv).
  unfold ec_doc in Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2. lia. }
(* ---- the live real stack at the call (the text's last premise): ec_pre's entry fact at e_sp0 E, carried to the
   callee's sp e_B E (<= e_sp0 E - 128) by the cut's journal from the entry, at its wild budget WS0
   (YGcallStackUp.astack_up_at_xw at STK1 = 0; e_sp0 E - e_B E <= 144 <= LLVMF_STK) ---- *)
assert (HUPE : YGcallStackUp.astack_up_x SEGS (e_ly E) (e_W E) (e_sp0 E) (e_mem E)) by (l5b_pre HPRE).
assert (HUPC : YGcallStackUp.astack_up_x SEGS ly W (spZ regsc) mem).
{ pose proof (YGcallStackUp.astack_up_at_xwR SEGS B PST ARc (@pa_segs_low rc B_prog_listing PA) WLE' LLVMF_STK (e_sp0 E) []
    (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) _ _ _ _ _ _ _ _ WS0 (e_B E) 0 HJm2 HUPE ltac:(lia) ltac:(lia)
    ltac:(lia)) as Hd.
  rewrite HSPC. replace (e_sp0 E + (e_B E - e_sp0 E)) with (e_B E - 0) by lia. exact Hd. }
(* ======== the call: the kit's check_round_trip text at the callee window 0 ======== *)
(* the run has at most 4 calls (the text's (length rp_os <= 4)%nat): ec_pre's length (e_os E) <= 3 and this call's triple *)
assert (HOS3 : (length (e_os E) <= 3)%nat) by (l5b_pre HPRE).
eapply SRrG_mono.
{ eapply (YCbqGwild.aj_call_xWFbR (fx := fy) (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc B_prog_listing PA) WLE'
    (wle'_refl SEGS _) (wle'_trans SEGS _) W regsc mem
    (@pa_sigma rc B_prog_listing PA AS_check_round_trip)
    LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)] ly S Hp mdc k WS0
    STK_check_round_trip 0 [] (e_B E - e_sp0 E) (Z_to_bv 64 (BASE + 0x308)) ch1
    (YCbqGwild.wbudget [] (prh_wk F_check_round_trip)) _
    HJm2 HSPC HO16 ltac:(lia) HSTKF HBUD ltac:(lia) eq_refl ltac:(lia) HGP HTP HRA1 HRAW HRA4 Hch).
  - (* the callee: tcheck_round_trip_specX at doc = &doc, x = the input, most = PJ_ALLOC_BOUND n *)
    intros HPRE1 HWIN1.
    eapply SRrG_mono.
    { eapply (CRT fy (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat
        (e_H0 E) hist0 ly S Hp W regsc mem mdc ch1 (ec_doc fk) t D (e_x E) Lam peak cnt 0 (PJ_ALLOC_BOUND (e_n E))).
      - split; [exact HPRE1|]. split; [exact HRO|].
        split; [rewrite HSPC, Eshi; lia |].
        (* kit f97c: fpre's frame clause gained `frm_zero fp_csr` beside the return-address bound; the cut
           supplies it (Hfz, at the callee's float state) *)
        first [ exact (conj HRAC Hfz) | split; [exact HRAC | assumption] ].
      - exact HMN.
      - exact HUCRT.
      - exact HCTX.
      - exact HA10.
      - exact HTREE.
      - exact Hread.
      - unfold EC_NMAX in HLXN. lia.
      - exact (proj1 Hlits).
      - exact (proj2 Hlits).
      - exact (SlotSizes.wlen_false_read ReaderRes.jr_strtod (e_x E) t Hread).
      - exact (SlotSizes.wlen_true_read ReaderRes.jr_strtod (e_x E) t Hread).
      - exact HLED.
      - lia.
      - (* ITS RUN EVENTS: the model's round_trip t, the accepted tail's first piece at cut_rm's index *)
        rewrite <- Hsm. exact (ec_rt_run E trp t Hi0E Hsm HLXN Hrof Hread).
      - reflexivity.
      - rewrite <- HLX. exact HRQA.
      - pose proof (VCRT E t HLXN Hread). lia.
      - exact HRQC.
      - rewrite Hfrs1. cbn [length]. unfold ck_FRAMES_CAP, FR_check_round_trip, FR_round_trip_text, FR_pj_parse,
          DOC_D, PjGrammar.MAXD. lia.
      - exact HLIVE.
      - rewrite <- Hsm. exact HR0.
      - exact Hfz.
      - rewrite length_app. cbn [length]. lia.
      - (* the callee's wild room, from the cut's spent budget ec_wk_rm (Ent102CutsB.v ec_room_at) *)
        eapply (ec_room_atR (fx := fx)); [exact HPRE | exact HJ | exact HWB |].
        apply Nat.leb_le. vm_compute. reflexivity.
      - (* The batch kit's consumer window (Ent102Win.cons_from_after_cno): every allocation of round_trip t at cut_rm's
           index is a consumer event, because none of check_no_overread's three readings ran out *)
        rewrite <- Hsm. exact (ec_rt_window E trp t Hi0E Hsm HLXN Hrof Hread).
      - (* THE LIVE REAL STACK at the call (the kit 4b8f95c0455c's last premise; HUPC above) *)
        exact HUPC. }
    intros W' c' _ HPOST. unfold fpostFbm, fpostFb, YCbqGwild.apost_base_xbF in HPOST.
    destruct HPOST as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & WS' & Hc' & Hz' & Hfk' & HPW' & HJ' & Hpr'
      & HQ').
    exists fx', ly', S', Hp', regs', mem', md', k', WS'. split; [exact Hc'|]. split; [exact Hz'|]. split; [exact Hfk'|].
    split; [exact HPW'|].
    rewrite !Z.add_0_r.
    split; [exact HJ'|]. split; [intros a Ha; lia|]. split; [exact Hpr'|]. exact HQ'.
  - (* the footprint is empty *)
    intros a (r0 & Hr0 & _). destruct Hr0. }
(* ======== +0x308: the cut after the call ======== *)
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW1 & HJcW & HJ1W & _
  & HP2 & HK).
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARc WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1W) as HJ1.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARc WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJcW) as HJc.
destruct HK as (HK & HKmn). cbv beta in HK.
destruct HK as (HRL2 & Lam' & peak' & cset & cnt' & ran' & own' & HpLam & HpBlk & Hpk & Hcset & _
  & HLED2 & HND2 & r & HR10 & Hr0eq & Harms).
pose proof HLED2 as ((_ & _ & _ & _ & _ & Hmost2 & Hown2 & _) & _).
destruct Harms as [(Hr1 & _) | (HrA & Ho0 & Hcnt & Hran & h2 & HR2)]; [subst r; discriminate Hr1|].
subst r ran'.
pose proof HJ1 as (HAR2 & Hly1 & _ & _ & _ & Hfrs2 & _ & _ & F1 & F2 & _ & F4 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & EF2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2c & F3c & _).
assert (Hfa2 : frame_addr ly2 LLVMF_FS_CLASS pos = frame_addr ly LLVMF_FS_CLASS pos)
  by (unfold frame_addr; rewrite EF2; reflexivity).
assert (Hga2 : flag_addr ly2 LLVMF_FS_CLASS pos = flag_addr ly LLVMF_FS_CLASS pos)
  by (unfold flag_addr; rewrite EF2; reflexivity).
assert (HNF0 : forall a, ~ inFP [] a) by (intros a (r0 & Hr0 & _); destruct Hr0).
(* the budgets: the count grows by at most ck_crt_count t cset, paid by epay_crt; the blocks are unchanged *)
destruct (PCRT E t cset HLXN Hread Hcset) as (Hpay8 & Hlpay8).
destruct (HCC E 8%nat 8%nat) as (Hc80 & _).
assert (Hcc0 : 0 <= ck_crt_count t cset).
{ unfold ck_crt_count, PjWriteHyp.wcalls.
  destruct t; cbv beta iota; lia. }
assert (Hcnt' : cnt <= cnt' <= cnt + ck_crt_count t cset) by (rewrite Hcnt; lia).
assert (HBB2 : blocks_bytes S2 = blocks_bytes S).
{ rewrite (prh_blocks_bytes_ablocks B ly2 S2), (l6f_bsum_perm _ _ HpBlk), <- (prh_blocks_bytes_ablocks B ly S).
  reflexivity. }
assert (HBLK2 : Permutation (ablocks B ly2 S2) (ck_hblks Lam' ++ ablocks B (e_ly E) (e_S E))).
{ apply (Permutation_trans HpBlk). apply (Permutation_trans HPERM).
  apply Permutation_app_tail. unfold ck_hblks. apply Permutation_map. exact (Permutation_sym HpLam). }
(* ---- THE FREE ORDER KEPT (ec_pjf, the batch kit): the tree's footprint - the root node at &doc in this frame and the
   reading's blocks D - is not written by check_round_trip (FP = []): the root by the callee journal's frame clause,
   the blocks by its block clause (they survive: the blocks are unchanged up to Permutation); writability by the frame
   geometry and the block law at the return. The same two facts as lib/A/Prog/Ent102L3AHelp.v's KD / KB. ---- *)
pose proof HAR2 as (HAR2cf & _).
assert (Hin2 : In (LLVMF_FS_CLASS, pos) (frames S2)) by (rewrite Hfrs2; apply in_or_app; right; exact Hin).
destruct (l6f_geom B ly2 S2 Hp2 W2 mem2 md2 pos fk HAR2cf Hin2 ltac:(rewrite Hfa2; exact Hfkeq))
  as (_ & _ & _ & _ & Gfr2 & _).
assert (KD : forall x, ec_doc fk <= x < ec_doc fk + 56 ->
  mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H W) mem) x /\
  (writable_at SEGS (mrestrict (w_H W) mem) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x)).
{ intros x Hx. unfold ec_doc in Hx. split.
  - apply prh_mbyte_of_aview. apply (F4 LLVMF_FS_CLASS pos x Hin); [|apply HNF0].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq.
    change (fs_frame_bytes LLVMF_FS_CLASS) with 128. lia.
  - intros _. apply (apresent_writable SEGS). exact (proj1 (Gfr2 x ltac:(unfold EC_FRAME_BYTES; lia))). }
assert (KB : forall a0 k0 x, In (a0, k0) Lam -> a0 <= x < a0 + k0 ->
  mbyte SEGS (mrestrict (w_H W2) mem2) x = mbyte SEGS (mrestrict (w_H W) mem) x /\
  (writable_at SEGS (mrestrict (w_H W) mem) x -> writable_at SEGS (mrestrict (w_H W2) mem2) x)).
{ intros a0 k0 x HinL Hx.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lam _ _ _ _ a0 k0 _ _ HLED HinL) as (Hk0 & Hb & _).
  assert (Hb2 : In (a0 - cf_head, k0 + cf_head) (ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym HpBlk) Hb).
  pose proof cf_head_nonneg as C0.
  assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  split.
  - apply prh_mbyte_of_aview.
    replace x with (a0 - cf_head + (x - (a0 - cf_head))) by (lia).
    apply (F2 (a0 - cf_head) (k0 + cf_head) (x - (a0 - cf_head)) Hb Hb2); [lia | apply HNF0].
  - intros _. apply (apresent_writable SEGS).
    pose proof (AR_blocks_law_ok_cf SEGS B ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2cf Hb2) as (_ & _ & _ & _ & Hpr & _).
    exact (proj1 (Hpr x ltac:(lia))). }
assert (HPJF2 : ec_pjf E fk W2 mem2 Lam' D t).
{ unfold ec_pjf in HPJF |- *. intros n Hn. destruct (HPJF n Hn) as (F & HF & HFm). exists F. split; [|exact HFm].
  eapply PRH_PjOrder.pj_foR_frame; [exact HF | |].
  - intros a0 k0 HinD. unfold prh_lin.
    exact (Permutation_in _ (Permutation_sym HpLam) (Permutation_in _ (Permutation_sym HLD) HinD)).
  - intros x [Hx | ((a0 & k0) & HinD & Hx)].
    + exact (KD x Hx).
    + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      exact (KB a0 k0 x (Permutation_in _ (Permutation_sym HLD) HinD) Hx). }
exists ly2, S2, Hp2, regs2, mem2, md2, [(LLVMF_FS_CLASS, pos)], Lam', peak', cnt', 0, (k + k1), tk, 0, trp.
split; [exists fx2; split; [exact HFZ2|]; split;
        [intros rr Hrr; rewrite (HFK2 rr Hrr); exact (Hkept rr Hrr) | reflexivity]|].
split.
{ (* ec_inv at the return site *)
  split; [exists (WS0 ++ WS1); split; [exact HJcW | exact (YCbqGwild.wbudget_app _ _ _ _ _ HWB HPW1)]|].
  split.
  { exists pos. split; [reflexivity|]. split; [rewrite Hfa2; exact Hfkeq|]. split; [exact Hfk0|].
    rewrite Hga2. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hflagw].
    intros i Hi. apply (F4 LLVMF_FS_CLASS pos _ Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq.
      change (fs_frame_bytes LLVMF_FS_CLASS) with 128. unfold EC_FRAME_BYTES. lia.
    - apply HNF0. }
  split; [exists (PJ_ALLOC_BOUND (e_n E)), own'; exact HLED2|].
  split.
  { apply (Hsioframe (aview SEGS (w_H (e_W E)) (e_mem E)) (aview SEGS (w_H W2) mem2)); [|exact HSIO0].
    intros a Ha. destruct (Hsio a Ha) as ((Ho & He) & Hi & Hnp).
    apply F3c; [exact Hi | exact Ho | exact He | exact Hnp | apply fp_spares_closed; exact sink_closed_nil]. }
  split.
  { intros a Hro Ho He.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr];
      [exists s; split; [exact Hs | lia] | exact (@pa_relro_img rc B_prog_listing PA a Hr)]. }
    assert (Hsp : fp_spares (SK := SK) [] a) by (apply fp_spares_closed; exact sink_closed_nil).
    rewrite (F3c a Hi Ho He (fun Hp' => Hpstro a Hp' Hro) Hsp).
    exact (HRO0 a Hro Ho He). }
  split; [exact HRL2|].
  split.
  { exists h2.
    replace (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t))%nat
      with (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E) + length (PresetReqAt.round_trip (e_sm E) t))%nat
      by (unfold ec_rt; rewrite !length_app; lia).
    (* The batch kit's post states the position over ReaderRes.jr_strtod (it has no rp_sm); the cut's is over e_sm E. Rewrite
       first: an `exact` across the two strtod terms makes the kernel unfold iface_room_pos and never returns. *)
    rewrite <- Hsm in HR2. exact HR2. }
  split; [lia|].
  split; [exact HPRE|].
  split.
  { destruct HPAY0 as [Hn0 | Hinp]; [left; exact Hn0|].
    right. exact (Permutation_in _ (Permutation_sym HpBlk) Hinp). }
  split; [exact HBLK2|].
  split.
  { intros i Hi. destruct HNC as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
    pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
    apply (F2c (e_p E) (e_n E) i Hinp (Permutation_in _ (Permutation_sym HBLK2) (in_or_app _ _ _ (or_intror Hinp)))
      ltac:(lia)).
    intros (r0 & Hr0 & _). destruct Hr0. }
  exact (HKmn HMN). }
split; [exact Hrof|].
split; [lia|].
split; [rewrite HBB2; lia|].
split.
{ (* ec_rkd: every register the cut reads is callee-saved *)
  split; [split|].
  - rewrite (l6f_pres regsc regs2 (2%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne. exact R2.
  - split; [rewrite (l6f_pres regsc regs2 (3%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R3|].
    split; [rewrite (l6f_pres regsc regs2 (4%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R4|].
    split; [rewrite (l6f_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R8|].
    split; [rewrite (l6f_pres regsc regs2 (9%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R9|].
    split; [rewrite (l6f_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R18|].
    split; [rewrite (l6f_pres regsc regs2 (19%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R19|].
    split; [rewrite (l6f_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R20|].
    split; [rewrite (l6f_pres regsc regs2 (26%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
            exact R26|].
    rewrite (l6f_pres regsc regs2 (27%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne. exact R27.
  - rewrite (l6f_pres regsc regs2 (21%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne. exact R21. }
split.
{ (* ec_frame: the saved block is above the callee's window, the frame's shadow is outside its footprint *)
  split; [|split; [|exact Hal32]].
  - assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
      rd64 (aview SEGS (w_H W) mem) a v -> rd64 (aview SEGS (w_H W2) mem2) a v).
    { intros a v Ha1 Ha2 Hr. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hr].
      intros j Hj. apply F1; lia. }
    unfold ec_saved in Hsaved |- *.
    repeat (split; [apply KS; [lia | lia | exact (proj1 Hsaved)] | apply proj2 in Hsaved]).
    apply KS; [lia | lia | exact Hsaved].
  - apply (l6f_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hshv].
    intros i Hi. change (Z.of_nat (length ec_frame_shadow)) with 16 in Hi.
    apply (F4 LLVMF_FS_CLASS pos _ Hin).
    + right. unfold in_zr. cbn [fst snd]. rewrite <- Hfkeq. change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16. lia.
    + apply HNF0. }
split; [exact HnN|].
split; [rewrite (l6f_pres regsc regs2 (23%bv : bv 5) HP2 ltac:(l6f_cs)), Eregsc, !getr_other by l6f_regne;
        exact R23|].
split; [exact Htk|].
split; [exact Hread|].
split; [exact (Permutation_trans HpLam HLD)|].
split; [exact HND2|].
split; [exact HPJF2|].
split; [exact Hmost2|].
split; [exact HR10|].
exists own'. split; [exact Hown2|].
split; [reflexivity|]. split; [exact Ho0 | reflexivity].
Qed.

End L5B.

Print Assumptions seg_L5b_B.
About seg_L5b_B.
