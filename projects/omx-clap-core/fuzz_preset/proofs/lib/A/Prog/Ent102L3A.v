(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L3A.v, with its module paths changed; 355 of its 560 lines of code are new or changed and 105 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4):
   SEGMENT L3 of LLVMFuzzerTestOneInput (entry 0x815e0), listing +0x178 .. +0x1b8, against lib/A/Ent102CutsA.v's
   `seg_L3_stmt` (cut_pno E fk -> cut_caw E fk \/ cut_free E fk), EXACT ROOM POSITION form:
     +0x178 mv s8,a0; +0x17c jal fuzz_alloc_peak               the kit's tfuzz_alloc_peak_specX (a0 = peak)
     +0x180 sub a0,a0,s6; +0x184 mv a1,s3; +0x188 jal check_bounded_alloc
                                                              tcheck_bounded_alloc_specX at held = peak (s6 = 0),
                                                              size = n: cut_pno's peak <= PJ_ALLOC_BOUND (e_n E)
     +0x18c jal fuzz_alloc_count                              tfuzz_alloc_count_specX (a0 = cnt)
     +0x190 lbu a1,-0x1c4(s9); +0x194 bnez a1                 the cell at pa_val (A_HI 4) - 0x1c4 = g_own_ran_out
                                                              (ei_own), which reads 0 (cut_pno's ec_own_is, kept by
                                                              every accessor post): the arm to FREE is not taken
     +0x198 mv s9,a0; +0x19c jal fuzz_alloc_ran_out           tfuzz_alloc_ran_out_specX (a0 = ran = 0, cut_pno's
     +0x1a0 bnez a0                                           ledger at ran = 0): the arm to FREE is not taken
     +0x1a4 .. +0x1b0 mv a0,s4; mv a1,s3; mv a2,s8; mv a3,s5; +0x1b4 jal check_as_written
                                                              at e_i0 + |cno ++ pn| with the run premise ec_sc E
                                                              (Ent102PosA: ec_supply_run / ec_run_split), return at
                                                              +0x1b8 at e_i0 + |cno ++ pn ++ sc| (cut_caw, r = 0)
  NO PROVISIONAL PLACE, NO HYPOTHESIS: check_as_written's call takes Ent102GrantA.v's
  tcheck_as_written_grantX (the batch kit's tcheck_as_written_specX with the post's r = 1 disjunct deleted and the batch kit's consumer window
  `PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 2` at entry), DERIVED from ec_texts' et_check_as_written (the batch kit's text)
  by lib/A/Prog/Ent102OfPost.v tcheck_as_written_grantX_of_post (zero hypotheses), at the call's fy and CTX0 =
  ec_ctx0 (l3_p5). The window is supplied by l3_win_caw from the shared lib/A/Prog/Ent102Win.v cons_from_after_cno
  (cut_pno's ec_ranout E trp = false).
  STATEMENT: lib/A/Ent102CutsA.v (blob 9443156fe336) with lib/A/Prog/Ent102CallA.v (blob ee3e7a0cd978),
  lib/A/Prog/Ent102GrantA.v (blob e91f2a41093b) and lib/A/Prog/Ent102OfPost.v (blob 2f3d35673a04):
  seg_L3_stmt over ec_hyps (no DW), cut_pno (ran = 0), cut_caw (r = 0 arm only), ec_invR with `exists most own,
  prh_ledger ..` and THE WILD BUDGET: its journal is `exists WS, ajournal_xwR .. WS /\ wbudget [] wk WS` at cut_pno's
  ec_wk_pno and cut_caw's ec_wk_caw = ec_wk_pno + prh_wk F_check_as_written.
  THE FREE MOVE (fuzz_preset #102): this lane runs after check_no_overread, the first callee that frees a live block,
  so seg_L3_stmt is ec_laneR WLE' (SRrG at WLE' = YA0nH.wle' segs RZ_cf) and its cuts carry ec_invR at WLE'. The three
  accessors' and check_bounded_alloc's texts conclude SRr with a post at wle (lifted by Ent102L3AHelp.v l3h_site);
  check_as_written's granted text concludes SRr' segs RZ_cf with apost_base_xFR at WLE' (l3h_siteF); the plain steps
  of lib/A/Prog/Ent102L3ASteps.v (SRr) run inside the lane by Ent102L3AHelp.v l3h_lift.
  THE HULL: check_as_written's text takes `length rp_os <= 4` (from ec_pre's `length (e_os E) <= 3`: the position
  e_os E ++ [trp]) and the hull budget of expected ()'s buffer pair ec_sc E (its malloc of n + 1 bytes and that
  block's free), paid by ec_hyps' ech_hull_pay at the cut's position with lib/A/PresetHullPay.v hull_nt_one_mal (the
  malloc, n + 1 <= 2 ^ 30) and lib/Spec/PresetHullBudget.v hull_count_fr (the free counts 0).
  Every call of this lane is to a
  budget-free text (the three accessors, check_bounded_alloc, check_as_written's grant form), so each runs under the
  cut file's ec_journal_rebaseR / ec_journal_unbaseR and the budget WS passes unchanged (Ent102L3AHelp.v l3h_site /
  l3h_siteF); the model's materialization by the cut file's ec_inv_wk_growR (l3h_inv_mat); cut_caw's wider wk by
  l3h_inv_wk. The tree's free order ec_pjf_res in cut_pno / cut_caw is KEPT across
  all four calls by Ent102L3AHelp.v l3h_core_after (PRH_PjOrder.pj_foR_frame over the tree's footprint, the same
  agreement as the document's pj_nodeR_frame); positions by lib/A/Ent102PosA.v; ec_invR's ledger read BY NAME
  (Ent102CallA.v ec_inv_ledgerR) and set at the cut's g_most / g_own_ran_out by the shared
  Ent102CallA.v ec_ledger_cells.
   LISTING: lib/A/Listing_prog.v (blob 1ab147923c5d) with the PAListing PL_102_A of lib/A/Ent102PLA.v (blob
   a55fa7414ddf); the image half stays generic ({PA : PAImg A_prog_listing}; lib/A/PAImg_prog.v, PresetCfnA and
   PresetCfnB are not loaded, no vm_compute on pa_val / pa_sigma).
   THE KIT TEXTS: lib/A/PRH_FnAlloc.v blob edb8665a8078 (tfuzz_alloc_peak / _count / _ran_out_specX),
   lib/A/PRH_FnCheck.v blob de94d3f3a7f1 (tcheck_bounded_alloc_specX; tcheck_as_written_specX, read through (C)),
   lib/A/PRH_Base.v (prh_ledger and its named projections prh_ledger_most / _own / _bounds, prh_run_at).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L3 (reuse search: main / ossv/recipes / ossv/candidates /
   release/* + the internal lemma index / proof-index LLVMFuzzerTestOneInput exit=0, seg_L3_A / seg_L3_stmt / the
   segment addresses: no proof anywhere, the lane's internal file rule24-LL3.txt; the lane's index output, the internal file idx-llvm-newpin.txt
   exit=0: NEW walk). The re-fit to the free move: proof-index seg_L3_A LLVMFuzzerTestOneInput 0x81844, index
   v5: seg_L3_A only on this lane's own cold branches.
   FILES: the step layer lib/A/Prog/Ent102L3ASteps.v, the support lemmas lib/A/Prog/Ent102L3AHelp.v, the shared
   lib/A/Prog/Ent102L6AfLem.v / Ent102CallA.v.
   NUMERALS: 0x178 .. 0x1bc are this lane's slot offsets (EC_AR_PNO - EC_BASE .. EC_FREE - EC_BASE); 0x1c4 is the load's
   displacement; 144 is EC_SAVE + 16; 256 / 2 ^ 31 / 2 ^ 40 / 2 ^ 62 / 2 ^ 64 are byte, int, code-span and word ranges.
   No ADDRESS. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YGcfTreeVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import
S1Ledger Ent102L6AfLem Ent102CallA Ent102GrantA Ent102OfPost Ent102L3ASteps Ent102L3AHelp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102Win.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section L3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
(* the cut file's two budget functions (count and live bytes per cut index; this lane goes from cut 3 to cuts 4 / 10) *)
Variables ec_ccut ec_lcut : @ecx rc A_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
#[local] Notation ECX := (@ecx rc A_prog_listing PA).
(* the world relation after a free (lib/A/Ent102CutsA.v's WLE'): this lane and its cuts are at it *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).
#[local] Notation INV := (ec_invR (fx := fx) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing) (PA := PA)
  B SK EC_RA EC_EMPTY EC_SIO WLE').
#[local] Notation IMG := (ec_img (L := A_prog_listing) (PA := PA) B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO
  EC_SIO_IMG).
#[local] Notation HYPS := (ec_hyps (ci := ci) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing)
  (PA := PA) B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut).
(* the records' projections by NAME, with the section's parameters (ec_hyps, ec_img, ec_texts, ec_univ, ec_pay) *)
#[local] Notation PH p H := (p B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut H).
#[local] Notation PIM p H := (p B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG H).
#[local] Notation PTX p H := (p B SK EC_RA EC_A_MOD_AT EC_A_STAMP H).
#[local] Notation PUN p H := (p B EC_RA H).
#[local] Notation PPY p H := (p ec_ccut ec_lcut H).
#[local] Notation CF fy regs pc mem md :=
  (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md).
#[local] Notation QF E fk := (fun W c =>
  cut_caw (fx := fx) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing) (PA := PA)
    B SK EC_RA EC_EMPTY EC_SIO ec_ccut ec_lcut E fk W c \/
  cut_free (fx := fx) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing) (PA := PA)
    B SK EC_RA EC_EMPTY EC_SIO ec_ccut ec_lcut E fk W c).
(* the exact position of the cuts after check_no_overread: grants e_os E ++ [trp], indices from e_i0 E *)
#[local] Notation POS E trp := (e_os E ++ [trp]).
#[local] Notation IPN E trp := (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E))%nat.
#[local] Notation ICAW E trp := (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat.
(* the ledger every text of this lane takes: ran = 0, g_most = PJ_ALLOC_BOUND n, g_own_ran_out = 0 *)
#[local] Notation LED E ly S Hp W mem Lam peak cnt :=
  (prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAX 0 (PJ_ALLOC_BOUND (e_n E)) 0).

(* ---------------------------------------------------------------------- *)
(* 1. The two budgets and the live-bytes cover of check_as_written, each behind ONE lemma (the record line moves). *)
Lemma l3_ccut_le : forall (HYP : HYPS) (E : ECX) i j, (i <= j)%nat -> ec_ccut E j <= ec_ccut E i.
Proof.
intros HYP E i j Hij. pose proof (PH ech_ccut_ok HYP) as HC. destruct (HC E i j) as (_ & H). exact (H Hij).
Qed.
Lemma l3_lcut_le : forall (HYP : HYPS) (E : ECX) i j, (i <= j)%nat -> ec_lcut E j <= ec_lcut E i.
Proof.
intros HYP E i j Hij. pose proof (PH ech_lcut_ok HYP) as HC. destruct (HC E i j) as (_ & H). exact (H Hij).
Qed.
Lemma l3_cov_caw : forall (HYP : HYPS) (E : ECX),
  e_n E <= EC_NMAX -> e_n E = Z.of_nat (length (e_pl E)) -> LIVE_check_as_written (e_n E) <= ec_lcut E 3.
Proof.
intros HYP E Hn Hl. pose proof (PH ech_pay HYP) as HP.
apply (PPY ecov_caw HP); [unfold e_x, ec_bytes; rewrite length_map; lia | exact Hn].
Qed.

(* the stack each callee may use is within LLVMF_STK - 144 (et_stk, ei_frame) *)
Ltac l3_stk_tac HSTKT Hfrm :=
  lazymatch goal with |- ?s + 144 <= LLVMF_STK =>
    let H := fresh "H" in pose proof HSTKT as H; unfold STK_LLVMFuzzerTestOneInput in H;
    lazymatch type of H with _ + zmaxl ?l <= _ =>
      let Hz := fresh "Hz" in
      assert (Hz : s <= zmaxl l) by (apply l6f_zmaxl_in; cbn [In]; repeat (first [left; reflexivity | right]));
      unfold EC_SAVE in Hfrm; lia
    end
  end.

(* ---------------------------------------------------------------------- *)
(* 2. THE REGISTERS of the lane: the cut's callee-saved set, s6 = 0, s7 = cnt0, s8 = rc, s9. *)
Definition l3_rg (E : ECX) (fk rcv cnt0 s9 : Z) (regs : bvmap 5 word) : Prop :=
  ec_rkd E fk regs /\ getr regs 22 = w64 0 /\ getr regs 23 = w64 cnt0 /\ getr regs 24 = w64 rcv /\
  getr regs 25 = w64 s9.

Ltac l3_kp HP :=
  lazymatch goal with |- getr ?r' ?x = _ => rewrite (l6f_pres _ r' x HP) by l6f_cs end.
(* read a register back through a chain of register updates *)
Ltac l3_gr := repeat (first [rewrite getr_same by l6f_regne | rewrite getr_other by l6f_regne]).

Lemma l3_rg_pres : forall (E : ECX) fk rcv cnt0 s9 regs regs', l3_rg E fk rcv cnt0 s9 regs ->
  aregs_preserved regs regs' -> l3_rg E fk rcv cnt0 s9 regs'.
Proof.
intros E fk rcv cnt0 s9 regs regs' H HP. unfold l3_rg, ec_rkd, ec_rk in *.
destruct H as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27) & R21) & R22 & R23 & R24 & R25).
repeat split; l3_kp HP; assumption.
Qed.

Lemma l3_rg_upd : forall (E : ECX) fk rcv cnt0 s9 regs (r : bv 5) v, l3_rg E fk rcv cnt0 s9 regs ->
  (r = 1%bv \/ r = 10%bv \/ r = 11%bv \/ r = 12%bv \/ r = 13%bv) -> l3_rg E fk rcv cnt0 s9 (regupd regs r v).
Proof.
intros E fk rcv cnt0 s9 regs r v H Hr. unfold l3_rg, ec_rkd, ec_rk in *.
destruct Hr as [->|[->|[->|[->| ->]]]]; rewrite !getr_other by l6f_regne; exact H.
Qed.

Lemma l3_rg_s9 : forall (E : ECX) fk rcv cnt0 s9 s9' regs, l3_rg E fk rcv cnt0 s9 regs ->
  l3_rg E fk rcv cnt0 s9' (regupd regs 25 (w64 s9')).
Proof.
intros E fk rcv cnt0 s9 s9' regs H. unfold l3_rg, ec_rkd, ec_rk in *.
rewrite getr_same by l6f_regne. rewrite !getr_other by l6f_regne.
destruct H as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27) & R21) & R22 & R23 & R24 & R25).
repeat split; first [assumption | reflexivity].
Qed.

Lemma l3_rg_start : forall (E : ECX) fk rcv cnt0 s9 regs,
  ec_rkd E fk regs -> getr regs 22 = w64 0 -> getr regs 23 = w64 cnt0 -> getr regs 25 = w64 s9 ->
  l3_rg E fk rcv cnt0 s9 (regupd regs 24 (w64 rcv)).
Proof.
intros E fk rcv cnt0 s9 regs Hrkd R22 R23 R25. unfold l3_rg, ec_rkd, ec_rk in *.
rewrite getr_same by l6f_regne. rewrite !getr_other by l6f_regne.
destruct Hrkd as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27) & R21).
repeat split; first [assumption | reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. THE MEMORY SIDE of the lane: cut_pno's facts, kept across the accessors and check_bounded_alloc. *)
Definition l3_ms (E : ECX) (fk : Z) ly S Hp (W : world SEGS) mem md own Lam peak cnt k
  (cnt0 : Z) (ok : list bool) (res : option jv) (tr : list ev) (D : list (Z * Z)) (trp : ec_trip) : Prop :=
  INV E fk ly S Hp W mem md own Lam peak cnt 0 k (POS E trp) (IPN E trp) ec_wk_pno /\
  cnt + ec_ccut E 3 <= e_cnt E + LCNT /\ blocks_bytes S + ec_lcut E 3 <= LIVE_MAX /\
  ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  cnt = cnt0 + Z.of_nat (calls tr) /\
  ec_parsed E ok res tr D /\ ec_doc_state fk W mem Lam res D /\ ec_pjf_res E fk W mem Lam res D /\
  peak <= PJ_ALLOC_BOUND (e_n E) /\
  (res = ck_read (e_x E) /\ Z.of_nat (calls tr) = ck_ncalls (e_x E)) /\
  LED E ly S Hp W mem Lam peak cnt /\ ec_ranout E trp = false.

Lemma l3_ms_mat : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt k cnt0 ok res tr D trp X,
  l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp ->
  l3_ms E fk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) own Lam peak cnt k cnt0 ok res tr D trp.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp X (HI & R). split; [|exact R].
exact (l3h_inv_mat (fx := fx) B SK EC_RA EC_EMPTY EC_SIO E fk ly S Hp W mem md own Lam peak cnt 0 k _ _ _ X HI).
Qed.

(* across a callee that keeps S, Hp, the blocks and the ledger at (ran, most, own) = (0, PJ_ALLOC_BOUND n, 0) (the three
   accessors and check_bounded_alloc); both journals at WLE' *)
Lemma l3_ms_acc : forall (E : ECX) fk ly S Hp (W : world SEGS) mem md own Lam peak cnt k cnt0 ok res tr D trp
  STK1 ly2 (W2 : world SEGS) mem2 md2 k1,
  IMG ->
  l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp ->
  (exists WS2, ajournal_xwR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly2 S Hp W2 mem2 md2 (k + k1) WS2 /\ YCbqGwild.wbudget [] ec_wk_pno WS2) ->
  ajournal_xR (SK := SK) SEGS B PST ARc WLE' STK1 (e_sp0 E + (e_A E - e_sp0 E)) [] ly S Hp W mem md [] ly2 S Hp W2
    mem2 md2 k1 ->
  ablocks B ly2 S = ablocks B ly S ->
  LED E ly2 S Hp W2 mem2 Lam peak cnt ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  l3_ms E fk ly2 S Hp W2 mem2 md2 own Lam peak cnt (k + k1) cnt0 ok res tr D trp.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp STK1 ly2 W2 mem2 md2 k1
  HIMG HMS HJc HJ1 Eab HL2 HMN2.
destruct HMS as (HI & HCC3 & HLC3 & HF & Hn & Hcnt & Hparsed & HDS & HPJ & Hpeak & Hlink & HLED & Hro).
pose proof HI as (_ & _ & _ & _ & _ & HLIVE & HROOM & _).
(* the callee keeps S, so the cut's exact position passes through unchanged *)
destruct (l3h_core_after (fx := fx) B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG E fk ly S Hp W mem
  md own Lam peak cnt 0 k (POS E trp) (IPN E trp) ec_wk_pno res D (POS E trp) (IPN E trp) STK1 ly2 S Hp W2 mem2 md2 k1
  HIMG HI HF HDS HPJ HJc HJ1 Eab (ex_intro _ _ (ex_intro _ _ HL2)) HLIVE HROOM HMN2) as (HI2 & HF2 & HDS2 & HPJ2 & _).
refine (conj HI2 (conj HCC3 (conj HLC3 (conj HF2 (conj Hn (conj Hcnt (conj Hparsed (conj HDS2 (conj HPJ2
  (conj Hpeak (conj Hlink (conj HL2 Hro)))))))))))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. THE ROOM POSITION (the only place this file computes an index): check_as_written's run premise at cut_pno's
       index, and its exact advance (+ 2 = |ec_sc E|) to cut_caw's index. The accessors and check_bounded_alloc keep
       S, so their calls pass the cut's position through unchanged (l3_ms_acc). *)
Lemma l3_run_caw : forall (E : ECX) (trp : ec_trip),
  ec_pre (fx := fx) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing) (PA := PA) B EC_RA EC_EMPTY EC_SIO E ->
  Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB -> ec_ranout E trp = false ->
  prh_run_at (e_sm E) (e_x E) (POS E trp) (IPN E trp) (ec_sc E).
Proof.
intros E trp HPRE Hx Hro.
assert (Hi0 : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E))) by (unfold ec_pre in HPRE; ec_conj_pick HPRE).
destruct trp as [[o1 o2] o0].
pose proof (ec_supply_run (e_sm E) (e_x E) (e_os E) o1 o2 o0) as H.
rewrite <- Hi0 in H.
change (PresetRun.call_evs (e_sm E) (e_x E) o1 o2 o0) with (ec_call_evs E (o1, o2, o0)) in H.
rewrite (ec_call_evs_ranout_false rc A_prog_listing PA E (o1, o2, o0) Hx Hro) in H.
apply (ec_run_split (e_sm E) (e_x E) (POS E (o1, o2, o0)) (e_i0 E) (ec_cno_evs E (o1, o2, o0) ++ ec_pn E) (ec_sc E)
  (PresetRun.call_tail (e_sm E) (e_x E))).
rewrite <- app_assoc. exact H.
Qed.

(* check_as_written's consumer window (the batch kit's grant condition in the batch's text): both of its events are consumer
   positions of the run, the shared Ent102Win.cons_from_after_cno at cut_pno's index (k = |ec_sc E| = 2) *)
Lemma l3_win_caw : forall (E : ECX) (trp : ec_trip),
  ec_pre (fx := fx) (cp := cp) (PI := PI) (RL := RL) (L := A_prog_listing) (PA := PA) B EC_RA EC_EMPTY EC_SIO E ->
  Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB -> ec_ranout E trp = false ->
  PRH_Base.prh_cons_from (e_sm E) (e_x E) (POS E trp) (IPN E trp) 2.
Proof.
intros E trp HPRE Hx Hro.
assert (Hi0 : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E))) by (unfold ec_pre in HPRE; ec_conj_pick HPRE).
pose proof (ec_call_evs_ranout_false rc A_prog_listing PA E trp Hx Hro) as Hce.
destruct trp as [[o1 o2] o0].
unfold ec_ranout in Hro. apply Bool.orb_false_iff in Hro as (Hro12 & H0). apply Bool.orb_false_iff in Hro12 as (H1 & H2).
apply (Ent102Win.cons_from_after_cno (e_sm E) (e_x E) (e_os E) o1 o2 o0); [exact Hx | exact H1 | exact H2 | exact H0 | |].
- rewrite <- Hi0. change (Ent102Win.cno_part (e_sm E) (e_x E) o1 o2 o0) with (ec_cno_evs E (o1, o2, o0)).
  rewrite length_app. lia.
- rewrite Ent102Win.hruns_snoc, (length_app (PresetRun.hruns (e_sm E) (e_x E) (e_os E))), <- Hi0.
  change (PresetRun.call_evs (e_sm E) (e_x E) o1 o2 o0) with (ec_call_evs E (o1, o2, o0)). rewrite Hce.
  unfold PresetRun.call_rest. rewrite !length_app. unfold ec_pn, ec_sc. cbn [length]. lia.
Qed.

Lemma l3_idx_caw : forall (E : ECX) (trp : ec_trip), (IPN E trp + 2)%nat = ICAW E trp.
Proof.
intros E trp. rewrite (app_assoc (ec_cno_evs E trp) (ec_pn E) (ec_sc E)), (length_app _ (ec_sc E)).
change (length (ec_sc E)) with 2%nat. lia.
Qed.

Lemma l3_pos_caw : forall (E : ECX) (trp : ec_trip) S2,
  (exists h, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (POS E trp) (IPN E trp + 2)%nat (e_H0 E) h S2) ->
  exists h, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (POS E trp) (ICAW E trp) (e_H0 E) h S2.
Proof. intros E trp S2 H. rewrite <- l3_idx_caw. exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. THE LANE, backwards from its last call. *)

(* +0x1a0: fuzz_alloc_ran_out has returned ran = 0 (cut_pno's ledger): `bnez a0` not taken, the arguments of
   check_as_written, its call under (C), the return at +0x1b8 = cut_caw *)
Lemma l3_p5 : forall (HYP : HYPS) (E : ECX) fk (fy : YK11.FPState) ly S Hp
  (W : world SEGS) mem md own Lam peak cnt k cnt0 ok res tr D trp regs,
  YK0o.frm_zero (@YK11.fp_csr fy) -> fregs_kept_x fx fy ->
  l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp ->
  l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 cnt regs ->
  getr regs 10 = w64 0 ->
  SRrG SEGS WLE' W (CF fy regs (BASE + 0x1a0) mem md) (QF E fk).
Proof.
intros HYP E fk fy ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp regs Hfz Hkept HMS HRG H10.
pose proof (PH ech_img HYP) as HIMG. pose proof (PH ech_texts HYP) as HTX. pose proof (PH ech_univ HYP) as HUNIV.
pose proof HMS as (HI & HCC3 & HLC3 & HF & Hn & Hcnt & Hparsed & HDS & HPJ & Hpeak & Hlink & HLED & Hro).
pose proof HI as ((WSj & HJ & HWB) & HOWN & _ & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES & HMN).
pose proof HRG as (Hrkd & R22 & R23 & R24 & R25).
(* `bnez a0` not taken (a0 = 0), the arguments of check_as_written: plain steps (SRr) inside the lane (l3h_lift) *)
apply (l3h_lift SEGS).
eapply (l3_s_1a0_ft (fx := fy) W regs mem md _).
{ rewrite H10. reflexivity. }
intros X1. apply l3_s_1a4. intros X2. apply l3_s_1a8. intros X3. apply l3_s_1ac. intros X4. apply l3_s_1b0.
intros X5. apply l3_s_1b4. intros X6.
apply SRr_ret. cbv beta.
(* the call *)
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; remember m as mdc eqn:Emdc end.
pose proof Hrkd as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27) & R21).
assert (G10 : getr regsc 10 = w64 (e_p E)) by (subst regsc; l3_gr; exact R20).
assert (G11 : getr regsc 11 = w64 (e_n E)) by (subst regsc; l3_gr; exact R19).
assert (G12 : getr regsc 12 = w64 (match res with Some _ => 0 | None => -1 end)) by (subst regsc; l3_gr; exact R24).
assert (G13 : getr regsc 13 = w64 (ec_doc fk)) by (subst regsc; l3_gr; exact R21).
assert (HRGc : l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 cnt regsc).
{ subst regsc. repeat (apply l3_rg_upd; [|first [left; reflexivity | right; left; reflexivity |
    right; right; left; reflexivity | right; right; right; left; reflexivity | right; right; right; right; reflexivity]]).
  exact HRG. }
pose proof HRGc as (((C2 & C3 & C4 & C8 & _) & _) & _).
assert (HIc : INV E fk ly S Hp W mem mdc own Lam peak cnt 0 k (POS E trp) (IPN E trp) ec_wk_pno)
  by (subst mdc; repeat apply (l3h_inv_mat (fx := fx) B SK EC_RA EC_EMPTY EC_SIO); exact HI).
(* the facts check_as_written's text asks *)
pose proof HPRE as (HPREX & _ & _ & _ & _ & _ & HPN & HNL & _ & HfrE & _).
pose proof (PIM ei_empty HIMG) as HEMP. pose proof (PIM ei_malloc_max HIMG) as HMAL.
pose proof YCbq.asan_consts as (AC1 & _).
assert (HLX : Z.of_nat (length (e_x E)) = e_n E) by (unfold e_x, ec_bytes; rewrite length_map; lia).
assert (Hsrc : src_rd W mem (e_p E) (e_x E) /\ 0 < e_p E /\ e_p E + Z.of_nat (length (e_x E)) < 2 ^ 62 /\
  (0 < Z.of_nat (length (e_x E)) -> PRH_FnEx.prhex_inblk B ly S Hp (e_p E) (Z.of_nat (length (e_x E))))).
{ destruct HPN as [(Hn0 & Hp0) | (Hnp & Hin0)].
  - assert (Ex : e_x E = []) by (apply length_zero_iff_nil; lia).
    rewrite Ex, Hp0. cbn [length Z.of_nat].
    pose proof (proj1 HEMP) as (HE1 & HE2). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HE1, HE2.
    split; [exact (l3h_src0 EC_EMPTY W mem (proj1 HEMP))|].
    split; [lia|]. split; [lia | intros H0; lia].
  - destruct (ec_src_home_cutR (fx := fx) (cp := cp) (PI := PI) (RL := RL) B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly S Hp
      W mem mdc own Lam peak cnt 0 k _ _ _ HIc ltac:(lia)) as (Hs & _).
    pose proof Hs as (_ & Hp4096 & Hp8 & _). rewrite HLX in Hp8 |- *.
    split; [exact Hs|]. split; [lia|]. split; [lia|].
    intros _. exact (l3h_inblk (fx := fx) B SK EC_RA EC_EMPTY EC_SIO E fk ly S Hp W mem md own Lam peak cnt 0 k _ _ _ HI
      ltac:(lia)). }
destruct Hsrc as (Hsrc & Hp0 & Hp62 & Hblk).
pose proof (l3h_doc_home (fx := fx) B SK EC_RA EC_EMPTY EC_SIO E fk ly S Hp W mem md own Lam peak cnt 0 k _ _ _ HI HF)
  as Hhome.
destruct Hlink as (Hres & Hcalls).
destruct HROOM as (hist0 & HR0).
(* the run premise [HMal (n + 1); HFr (n + 1)] = ec_sc E at cut_pno's index *)
assert (Hrun : prh_run_at (e_sm E) (e_x E) (POS E trp) (IPN E trp) (ec_sc E))
  by (apply (l3_run_caw E trp HPRE); [rewrite HLX; unfold EC_NMAX in Hn; unfold PresetReqAt.MAXB; lia | exact Hro]).
(* its consumer window (the batch kit's grant condition, the batch's tcheck_as_written_grantX): Ent102Win.cons_from_after_cno *)
assert (Hwin : PRH_Base.prh_cons_from (e_sm E) (e_x E) (POS E trp) (IPN E trp) 2)
  by (apply (l3_win_caw E trp HPRE); [rewrite HLX; unfold EC_NMAX in Hn; unfold PresetReqAt.MAXB; lia | exact Hro]).
(* THE HULL ROW: the run has at most 4 calls at this cut (ec_pre's `length (e_os E) <= 3`, the position
   e_os E ++ [trp]), and the hull budget of expected ()'s buffer pair ec_sc E is paid at the cut's position by ec_hyps'
   ech_hull_pay: one call's worth by PresetHullPay.hull_nt_one_mal (malloc of n + 1 <= 2 ^ 30 bytes) and
   PresetHullBudget.hull_count_fr (the free counts 0) *)
assert (Hos4 : (length (POS E trp) <= 4)%nat).
{ assert (Hos3 : (length (e_os E) <= 3)%nat) by (unfold ec_pre in HPRE; ec_conj_pick HPRE).
  rewrite length_app. cbn [length]. lia. }
assert (Hhull : @PresetHullBudget.hull_budget cp S
  [PresetReqAt.HMal (Z.of_nat (length (e_x E)) + 1); PresetReqAt.HFr (Z.of_nat (length (e_x E)) + 1)]).
{ destruct (PresetHullPay.hull_nt_one_mal (Z.of_nat (length (e_x E)) + 1) ltac:(unfold EC_NMAX in Hn; lia))
    as (HN1 & HT1).
  destruct (PresetHullBudget.hull_count_fr (Z.of_nat (length (e_x E)) + 1)) as (HN2 & HT2).
  apply (PH ech_hull_pay HYP (e_sm E) (e_x E) (POS E trp) (IPN E trp) (e_H0 E) hist0 S); [exact Hos4 | exact HR0 | |].
  - change [PresetReqAt.HMal (Z.of_nat (length (e_x E)) + 1); PresetReqAt.HFr (Z.of_nat (length (e_x E)) + 1)]
      with ([PresetReqAt.HMal (Z.of_nat (length (e_x E)) + 1)] ++ [PresetReqAt.HFr (Z.of_nat (length (e_x E)) + 1)]).
    rewrite PresetSecTotal.nsec_app, HN2, Nat.add_0_r. exact HN1.
  - change [PresetReqAt.HMal (Z.of_nat (length (e_x E)) + 1); PresetReqAt.HFr (Z.of_nat (length (e_x E)) + 1)]
      with ([PresetReqAt.HMal (Z.of_nat (length (e_x E)) + 1)] ++ [PresetReqAt.HFr (Z.of_nat (length (e_x E)) + 1)]).
    rewrite PresetSecTotal.tsec_app, HT2, Z.add_0_r. exact HT1. }
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HAR as (HARcf & _).
pose proof HOWN as (pos & Hown & Hfkeq & Hfk0 & _).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE, Hown; left; reflexivity).
destruct (l6f_geom B ly S Hp W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & _).
unfold EC_FRAME_BYTES in Gceil.
assert (HFR1 : Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_as_written).
{ rewrite Hfrs, HfrE, Hown. cbn [length app Z.of_nat]. unfold ck_FRAMES_CAP, FR_check_as_written, FR_ex_value.
  change (Z.of_nat DOC_D) with 33. lia. }
pose proof (PTX et_stk HTX) as HSTKT. pose proof (PIM ei_frame HIMG) as Hfrm.
eapply (l3h_siteF (fx := fx) B SK EC_RA EC_EMPTY EC_SIO fy E fk ly S Hp W mem mdc own Lam peak cnt 0 k _ _ _ regsc 0x1b8
  STK_check_as_written (SIGMA AS_check_as_written) _ _ HIc HF C2 C8 C3 C4 Hfz).
{ subst regsc. apply getr_same. l6f_regne. }
{ lia. }
{ reflexivity. }
{ vm_compute. discriminate. }
{ unfold STK_check_as_written. apply Z.add_nonneg_nonneg; [apply pi_frame_nonneg | apply l6f_zmaxl_nonneg]. }
{ l3_stk_tac HSTKT Hfrm. }
{ (* THE TEXT: Ent102GrantA.tcheck_as_written_grantX, DERIVED from ec_texts' et_check_as_written (the batch kit's text) by
     Ent102OfPost.tcheck_as_written_grantX_of_post (zero hypotheses) *)
  intros ch Hfpre.
  exact (tcheck_as_written_grantX_of_post (fx := fy) (L := A_prog_listing) (PA := PA) B ARc SK (ec_ctx0 EC_RA)
    (et_check_as_written _ _ _ _ _ HTX fy) (e_sm E) (e_x E) (POS E trp) (IPN E trp) (e_H0 E) hist0 ly S Hp W regsc mem mdc ch (e_p E) (e_x E)
    (match res with Some _ => 0 | None => -1 end) (ec_doc fk)
    (match res with Some t => t | None => PjTree.JNull end) D Lam peak cnt SIZE_MAX 0 (PJ_ALLOC_BOUND (e_n E))
    Hfpre (HMN) (PUN eu_caw HUNIV) G10 ltac:(rewrite HLX; exact G11) G12 G13
    ltac:(destruct res; lia) ltac:(unfold ec_doc; lia)
    ltac:(rewrite HLX; unfold EC_NMAX in Hn; lia) Hp0 Hp62 Hsrc Hblk
    ltac:(rewrite Hres; destruct (ck_read (e_x E)) as [t0|];
          [left; split; reflexivity | right; split; [lia | reflexivity]])
    ltac:(destruct res as [t0|]; [|intros H0; lia]; intros _;
          destruct HDS as (HPLD & Hnode);
          split; [exact Hnode|];
          split; [intros bk Hbk; exact (Permutation_in _ (Permutation_sym HPLD) Hbk)|];
          split; [|exact Hhome];
          unfold prhWriter_tree_vis; apply (YGcfTreeVis.tree_vis_of_blocks_cf SEGS B ly S Hp W mem md D HARcf);
          intros a0 k0 HinD;
          pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAX 0 a0 k0 _ _ HLED
            (Permutation_in _ (Permutation_sym HPLD) HinD)) as (_ & Hb & Hh & _);
          split; [exact Hb | exact Hh])
    HLED Hrun Hwin eq_refl
    ltac:(rewrite HLX; pose proof (l3_cov_caw HYP E Hn ltac:(exact HNL)); lia)
    ltac:(rewrite HLX; unfold PRH_FnWriter.prhWriter_WMAX in HMAL; pose proof cf_head_nonneg; unfold EC_NMAX in Hn; lia)
    HFR1
    HLIVE HR0 Hos4 Hhull Hfz). }
(* +0x1b8: the return, cut_caw at e_i0 + |cno ++ pn ++ sc| *)
intros fz W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HFZ HFK HJc HJ1 HP HQ HMN2.
destruct HQ as (HRL2 & -> & Eab & own' & HL2 & _ & r & H10' & Hr0 & Ho0 & HRP2 & _).
destruct (l3h_core_after (fx := fx) B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG E fk ly S Hp W mem
  mdc own Lam peak cnt 0 k (POS E trp) (IPN E trp) ec_wk_pno res D (POS E trp) (ICAW E trp) STK_check_as_written ly2 S2 Hp
  W2 mem2 md2 k1 HIMG HIc HF HDS HPJ HJc HJ1 Eab (ex_intro _ _ (ex_intro _ _ HL2)) HRL2 (l3_pos_caw E trp S2 HRP2) HMN2)
  as (HI2 & HF2 & HDS2 & HPJ2 & Hbb).
(* g_most and g_own_ran_out after the call, from its ledger (PRH_Base's named projections) *)
assert (Hmost2 : ec_most E W2 mem2) by (unfold ec_most; eapply PRH_Base.prh_ledger_most; exact HL2).
assert (Hown2 : ec_own_is W2 mem2 own') by (unfold ec_own_is; eapply PRH_Base.prh_ledger_own; exact HL2).
pose proof (l3_rg_pres E fk _ cnt0 cnt regsc regs2 HRGc HP) as (Hrkd2 & Q22 & Q23 & Q24 & Q25).
apply (SRrG_ret SEGS WLE' (wle'_refl SEGS _)). left.
exists ly2, S2, Hp, regs2, mem2, md2, own, Lam, peak, cnt0, cnt, 0, (k + k1), ok, res, tr, D, r, trp.
split; [exists fz; split; [exact HFZ|]; split; [exact (l3h_fk_trans fx fy fz Hkept HFK) | reflexivity]|].
(* the spent budget: cut_caw's ec_wk_caw = ec_wk_pno + prh_wk F_check_as_written (check_as_written's text is
   budget-free) *)
split; [exact (l3h_inv_wk (fx := fx) B SK EC_RA EC_EMPTY EC_SIO E fk ly2 S2 Hp W2 mem2 md2 own Lam peak cnt 0 (k + k1)
  _ _ ec_wk_pno ec_wk_caw ltac:(unfold ec_wk_caw; lia) HI2)|].
split; [exact Hro|].
split; [pose proof (l3_ccut_le HYP E 3 4 ltac:(lia)); lia|].
split; [rewrite Hbb; pose proof (l3_lcut_le HYP E 3 4 ltac:(lia)); lia|].
split; [exact Hrkd2|]. split; [exact HF2|]. split; [exact Hn|].
split; [exact Q22|]. split; [exact Q23|]. split; [exact Q24|].
split; [rewrite <- Hcnt; exact Q25|].
split; [exact Hparsed|]. split; [exact HDS2|]. split; [exact HPJ2|].
split; [exact Hmost2|].
split; [exact H10'|].
exists own'. split; [exact Hown2|].
split; [exact Hr0|]. split; [exact Ho0|]. split; [reflexivity|]. split; [exact Hres | exact Hcalls].
Qed.

(* +0x190: fuzz_alloc_count has returned cnt; the inlined g_own_ran_out test (it reads 0), s9 := cnt, the call of
   fuzz_alloc_ran_out *)
Lemma l3_p4 : forall (HYP : HYPS) (E : ECX) fk (fy : YK11.FPState) ly S Hp
  (W : world SEGS) mem md own Lam peak cnt k cnt0 ok res tr D trp regs,
  YK0o.frm_zero (@YK11.fp_csr fy) -> fregs_kept_x fx fy ->
  l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp ->
  l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 (VAL (A_HI 4)) regs ->
  getr regs 10 = w64 cnt ->
  SRrG SEGS WLE' W (CF fy regs (BASE + 0x190) mem md) (QF E fk).
Proof.
intros HYP E fk fy ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp regs Hfz Hkept HMS HRG H10.
pose proof (PH ech_img HYP) as HIMG. pose proof (PH ech_texts HYP) as HTX.
pose proof HMS as (HI & _ & _ & HF & _ & _ & _ & _ & _ & _ & _ & HLED & _).
(* g_own_ran_out = 0, from the lane's ledger (PRH_Base's named projection) *)
assert (Hown0 : ec_own_is W mem 0) by (unfold ec_own_is; eapply PRH_Base.prh_ledger_own; exact HLED).
pose proof HRG as (Hrkd & R22 & R23 & R24 & R25).
pose proof (PIM ei_own HIMG) as (Eown & Wown).
(* +0x190 `lbu a1,-0x1c4(s9)`: g_own_ran_out, which is 0 (plain steps inside the lane, l3h_lift) *)
apply (l3h_lift SEGS).
eapply (l3_s_190 (fx := fy) W regs mem md _ (VAL (A_HI 4)) 0 R25).
{ destruct Hown0 as (Hv & _). rewrite Eown. rewrite Wown in Hv. exact Hv. }
{ lia. }
intros X1.
(* +0x194 `bnez a1` not taken *)
eapply (l3_s_194_ft (fx := fy) W _ mem _ _).
{ rewrite getr_same by l6f_regne. reflexivity. }
intros X2.
(* +0x198 `mv s9,a0`; +0x19c `jal fuzz_alloc_ran_out` *)
apply l3_s_198. intros X3. apply l3_s_19c. intros X4.
apply SRr_ret. cbv beta.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; remember m as mdc eqn:Emdc end.
assert (HRGc : l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 cnt regsc).
{ subst regsc. apply l3_rg_upd; [|left; reflexivity].
  assert (E10 : getr (regupd regs 11 (Z_to_bv 64 0)) 10 = w64 cnt) by (l3_gr; exact H10).
  rewrite E10. apply (l3_rg_s9 E fk _ cnt0 (VAL (A_HI 4))).
  apply l3_rg_upd; [exact HRG | right; right; left; reflexivity]. }
pose proof HRGc as (((C2 & C3 & C4 & C8 & _) & _) & _).
assert (HMSc : l3_ms E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp)
  by (subst mdc; repeat apply l3_ms_mat; exact HMS).
pose proof HMSc as (HIc & _ & _ & HFc & _).
pose proof (PTX et_stk HTX) as HSTKT. pose proof (PIM ei_frame HIMG) as Hfrm.
eapply (l3h_site (fx := fx) B SK EC_RA EC_EMPTY EC_SIO fy E fk ly S Hp W mem mdc own Lam peak cnt 0 k _ _ _ regsc 0x1a0
  STK_fuzz_alloc_ran_out (SIGMA AS_fuzz_alloc_ran_out) _ _ HIc HFc C2 C8 C3 C4 Hfz).
{ subst regsc. apply getr_same. l6f_regne. }
{ lia. }
{ reflexivity. }
{ vm_compute. discriminate. }
{ unfold STK_fuzz_alloc_ran_out. apply pi_frame_nonneg. }
{ l3_stk_tac HSTKT Hfrm. }
{ intros ch Hfpre.
  exact (PTX et_fuzz_alloc_ran_out HTX fy ly S Hp W regsc mem mdc ch Lam peak cnt SIZE_MAX 0 (PJ_ALLOC_BOUND (e_n E))
    0 Hfpre HLED). }
intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJc HJ1 HP HQ HMN2.
destruct HQ as (_ & H10' & -> & -> & Eab & HL2).
apply (l3_p5 HYP E fk fy ly2 S Hp W2 mem2 md2 own Lam peak cnt (k + k1) cnt0 ok res tr D trp regs2 Hfz
  Hkept).
- exact (l3_ms_acc E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp STK_fuzz_alloc_ran_out ly2 W2
    mem2 md2 k1 HIMG HMSc HJc HJ1 Eab HL2 HMN2).
- exact (l3_rg_pres E fk _ cnt0 cnt regsc regs2 HRGc HP).
- exact H10'.
Qed.

(* +0x18c: check_bounded_alloc has returned; the call of fuzz_alloc_count *)
Lemma l3_p3 : forall (HYP : HYPS) (E : ECX) fk (fy : YK11.FPState) ly S Hp
  (W : world SEGS) mem md own Lam peak cnt k cnt0 ok res tr D trp regs,
  YK0o.frm_zero (@YK11.fp_csr fy) -> fregs_kept_x fx fy ->
  l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp ->
  l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 (VAL (A_HI 4)) regs ->
  SRrG SEGS WLE' W (CF fy regs (BASE + 0x18c) mem md) (QF E fk).
Proof.
intros HYP E fk fy ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp regs Hfz Hkept HMS HRG.
pose proof (PH ech_img HYP) as HIMG. pose proof (PH ech_texts HYP) as HTX.
pose proof HMS as (HI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED & _).
apply (l3h_lift SEGS). apply l3_s_18c. intros X1. apply SRr_ret. cbv beta.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; remember m as mdc eqn:Emdc end.
assert (HRGc : l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 (VAL (A_HI 4)) regsc)
  by (subst regsc; apply l3_rg_upd; [exact HRG | left; reflexivity]).
pose proof HRGc as (((C2 & C3 & C4 & C8 & _) & _) & _).
assert (HMSc : l3_ms E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp)
  by (subst mdc; repeat apply l3_ms_mat; exact HMS).
pose proof HMSc as (HIc & _ & _ & HFc & _).
pose proof (PTX et_stk HTX) as HSTKT. pose proof (PIM ei_frame HIMG) as Hfrm.
eapply (l3h_site (fx := fx) B SK EC_RA EC_EMPTY EC_SIO fy E fk ly S Hp W mem mdc own Lam peak cnt 0 k _ _ _ regsc 0x190
  STK_fuzz_alloc_count (SIGMA AS_fuzz_alloc_count) _ _ HIc HFc C2 C8 C3 C4 Hfz).
{ subst regsc. apply getr_same. l6f_regne. }
{ lia. }
{ reflexivity. }
{ vm_compute. discriminate. }
{ unfold STK_fuzz_alloc_count. apply pi_frame_nonneg. }
{ l3_stk_tac HSTKT Hfrm. }
{ intros ch Hfpre.
  exact (PTX et_fuzz_alloc_count HTX fy ly S Hp W regsc mem mdc ch Lam peak cnt SIZE_MAX 0 (PJ_ALLOC_BOUND (e_n E))
    0 Hfpre HLED). }
intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJc HJ1 HP HQ HMN2.
destruct HQ as (_ & H10' & -> & -> & Eab & HL2).
apply (l3_p4 HYP E fk fy ly2 S Hp W2 mem2 md2 own Lam peak cnt (k + k1) cnt0 ok res tr D trp regs2 Hfz
  Hkept).
- exact (l3_ms_acc E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp STK_fuzz_alloc_count ly2 W2
    mem2 md2 k1 HIMG HMSc HJc HJ1 Eab HL2 HMN2).
- exact (l3_rg_pres E fk _ cnt0 _ regsc regs2 HRGc HP).
- exact H10'.
Qed.

(* +0x180: fuzz_alloc_peak has returned peak; held = peak - live (s6 = 0), size = n, the call of
   check_bounded_alloc *)
Lemma l3_p2 : forall (HYP : HYPS) (E : ECX) fk (fy : YK11.FPState) ly S Hp
  (W : world SEGS) mem md own Lam peak cnt k cnt0 ok res tr D trp regs,
  YK0o.frm_zero (@YK11.fp_csr fy) -> fregs_kept_x fx fy ->
  l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp ->
  l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 (VAL (A_HI 4)) regs ->
  getr regs 10 = w64 peak ->
  SRrG SEGS WLE' W (CF fy regs (BASE + 0x180) mem md) (QF E fk).
Proof.
intros HYP E fk fy ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp regs Hfz Hkept HMS HRG H10.
pose proof (PH ech_img HYP) as HIMG. pose proof (PH ech_texts HYP) as HTX.
pose proof HMS as (HI & _ & _ & _ & Hn & _ & _ & _ & _ & Hpeak & _ & HLED & _).
pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & HNL & _).
(* the peak's range, from the lane's ledger (PRH_Base's named projection) *)
pose proof HLED as HBD. eapply PRH_Base.prh_ledger_bounds in HBD. destruct HBD as (Hlp & Hp64 & _).
pose proof HRG as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27) & R21) & R22 & R23 & R24 & R25).
apply (l3h_lift SEGS). apply l3_s_180. intros X1. apply l3_s_184. intros X2. apply l3_s_188. intros X3.
apply SRr_ret. cbv beta.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; remember m as mdc eqn:Emdc end.
assert (G10 : getr regsc 10 = w64 peak).
{ subst regsc. l3_gr. rewrite H10, R22. unfold w64. apply l3_vsub0. }
assert (G11 : getr regsc 11 = w64 (e_n E)) by (subst regsc; l3_gr; exact R19).
assert (HRGc : l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 (VAL (A_HI 4)) regsc).
{ subst regsc. apply l3_rg_upd; [|left; reflexivity]. apply l3_rg_upd; [|right; right; left; reflexivity].
  apply l3_rg_upd; [exact HRG | right; left; reflexivity]. }
pose proof HRGc as (((C2 & C3 & C4 & C8 & _) & _) & _).
assert (HMSc : l3_ms E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp)
  by (subst mdc; repeat apply l3_ms_mat; exact HMS).
pose proof HMSc as (HIc & _ & _ & HFc & _).
pose proof (PTX et_stk HTX) as HSTKT. pose proof (PIM ei_frame HIMG) as Hfrm.
eapply (l3h_site (fx := fx) B SK EC_RA EC_EMPTY EC_SIO fy E fk ly S Hp W mem mdc own Lam peak cnt 0 k _ _ _ regsc 0x18c
  STK_check_bounded_alloc (SIGMA AS_check_bounded_alloc) _ _ HIc HFc C2 C8 C3 C4 Hfz).
{ subst regsc. apply getr_same. l6f_regne. }
{ lia. }
{ reflexivity. }
{ vm_compute. discriminate. }
{ unfold STK_check_bounded_alloc. apply pi_frame_nonneg. }
{ l3_stk_tac HSTKT Hfrm. }
{ intros ch Hfpre.
  exact (PTX et_check_bounded_alloc HTX fy ly S Hp W regsc mem mdc ch peak (e_n E) Lam peak cnt SIZE_MAX 0
    (PJ_ALLOC_BOUND (e_n E)) 0 Hfpre G10 G11 ltac:(lia) ltac:(unfold EC_NMAX in Hn; lia) Hpeak HLED). }
intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJc HJ1 HP HQ HMN2.
destruct HQ as (-> & -> & Eab & _ & HL2).
apply (l3_p3 HYP E fk fy ly2 S Hp W2 mem2 md2 own Lam peak cnt (k + k1) cnt0 ok res tr D trp regs2 Hfz
  Hkept).
- exact (l3_ms_acc E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp STK_check_bounded_alloc ly2 W2
    mem2 md2 k1 HIMG HMSc HJc HJ1 Eab HL2 HMN2).
- exact (l3_rg_pres E fk _ cnt0 _ regsc regs2 HRGc HP).
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE SEGMENT: cut_pno at +0x178, `mv s8,a0`, the call of fuzz_alloc_peak, then the lane above, all at WLE'
   (ec_laneR). No argument, no hypothesis: check_as_written's text is ec_texts' (l3_p5). *)
Theorem seg_L3_A :
  @seg_L3_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L3_stmt, ec_laneR.
intros E fk HYP W c Hcut.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt0 & cnt & k & ok & res & tr & D & trp & Hat &
  Hinv & Hro & HCC3 & H25 & HLC3 & Hrkd & Hfr & Hn & R22 & R23 & Hcnt & Hparsed & HDS & HPJ & R10 & Hpeak & Hlink &
  Hmost & Hown0).
destruct Hat as (fy & Hfz & Hkept & ->).
unfold cfg_at. change (w64 (EC_AR_PNO (L := A_prog_listing) (PA := PA))) with (Z_to_bv 64 (BASE + 0x178)).
pose proof (PH ech_img HYP) as HIMG. pose proof (PH ech_texts HYP) as HTX.
(* the lane's ledger: cut_pno's ledger (read BY NAME, Ent102CallA.ec_inv_ledgerR) at g_most = PJ_ALLOC_BOUND n and
   g_own_ran_out = 0 (cut_pno's ec_most / ec_own_is), by the shared Ent102CallA.ec_ledger_cells *)
destruct (ec_inv_ledgerR (fx := fx) (cp := cp) (PI := PI) (RL := RL) B SK EC_RA EC_EMPTY EC_SIO Hinv)
  as (most0 & own0 & HL0).
pose proof (ec_ledger_cells B ly S Hp W mem Lam peak cnt SIZE_MAX 0 most0 own0 _ _ HL0 Hmost Hown0) as HLED.
assert (HMS : l3_ms E fk ly S Hp W mem md own Lam peak cnt k cnt0 ok res tr D trp)
  by exact (conj Hinv (conj HCC3 (conj HLC3 (conj Hfr (conj Hn (conj Hcnt (conj Hparsed (conj HDS (conj HPJ
    (conj Hpeak (conj Hlink (conj HLED Hro)))))))))))).
(* +0x178 `mv s8,a0`; +0x17c `jal fuzz_alloc_peak` (plain steps inside the lane, l3h_lift) *)
apply (l3h_lift SEGS). apply l3_s_178. intros X1. apply l3_s_17c. intros X2. apply SRr_ret. cbv beta.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; remember m as mdc eqn:Emdc end.
assert (HRGc : l3_rg E fk (match res with Some _ => 0 | None => -1 end) cnt0 (VAL (A_HI 4)) regsc).
{ subst regsc. apply l3_rg_upd; [|left; reflexivity]. rewrite R10. apply l3_rg_start; assumption. }
pose proof HRGc as (((C2 & C3 & C4 & C8 & _) & _) & _).
assert (HMSc : l3_ms E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp)
  by (subst mdc; repeat apply l3_ms_mat; exact HMS).
pose proof HMSc as (HIc & _ & _ & HFc & _).
pose proof (PTX et_stk HTX) as HSTKT. pose proof (PIM ei_frame HIMG) as Hfrm.
eapply (l3h_site (fx := fx) B SK EC_RA EC_EMPTY EC_SIO fy E fk ly S Hp W mem mdc own Lam peak cnt 0 k _ _ _ regsc 0x180
  STK_fuzz_alloc_peak (SIGMA AS_fuzz_alloc_peak) _ _ HIc HFc C2 C8 C3 C4 Hfz).
{ subst regsc. apply getr_same. l6f_regne. }
{ lia. }
{ reflexivity. }
{ vm_compute. discriminate. }
{ unfold STK_fuzz_alloc_peak. apply pi_frame_nonneg. }
{ l3_stk_tac HSTKT Hfrm. }
{ intros ch Hfpre.
  exact (PTX et_fuzz_alloc_peak HTX fy ly S Hp W regsc mem mdc ch Lam peak cnt SIZE_MAX 0 (PJ_ALLOC_BOUND (e_n E)) 0
    Hfpre HLED). }
intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle HJc HJ1 HP HQ HMN2.
destruct HQ as (_ & H10' & -> & -> & Eab & HL2).
apply (l3_p2 HYP E fk fy ly2 S Hp W2 mem2 md2 own Lam peak cnt (k + k1) cnt0 ok res tr D trp regs2 Hfz
  Hkept).
- exact (l3_ms_acc E fk ly S Hp W mem mdc own Lam peak cnt k cnt0 ok res tr D trp STK_fuzz_alloc_peak ly2 W2
    mem2 md2 k1 HIMG HMSc HJc HJ1 Eab HL2 HMN2).
- exact (l3_rg_pres E fk _ cnt0 _ regsc regs2 HRGc HP).
- exact H10'.
Qed.

End L3.
