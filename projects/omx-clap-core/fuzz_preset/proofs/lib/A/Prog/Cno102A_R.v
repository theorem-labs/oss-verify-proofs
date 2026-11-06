(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module names changed; 1639 of its 1698 lines of code are new or changed and 467 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsU.v, with its module paths and module names changed; 1141 of its 1186 lines of code are new or changed and 1653 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Cno102A_R5.v; 118 of its 172 lines of code are new or changed and 1132 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): lane CnoA102r's
   SEGMENTS CA5-CA9 of the re-walk of check_no_overread (plan, the internal file PLAN-cno-caw-102.md 5.1), COMPOSED: from the two
   CA5 cuts (CN_INIT 0x81b64 / CN_INIT3 0x81c1c) to the free cut CN_FREE 0x81d28, where CnoA102f's CA10 takes over.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   THE PIECES (each forward, generic in the memory invariant P; contract lib/A/Prog/Cno102A_Base.v):
     Cno102A_R5.v   CA5 Init        cn_init_seg (CN_INIT -> CN_READ1), cn_init3_seg (CN_INIT3 -> CN_READ2)
     Cno102A_R6.v   CA6-CA8 guards  cn_read1_seg / cn_read2_seg / cn_read3_seg (the fuzz_alloc_ran_out call steps
                                    of Cno102A_Ro.v)
     Cno102A_Rpn.v  the three parse_noting call steps cn_pn1_step / cn_pn2_step / cn_pn3_step (against the
                                    tparse_noting_specX, the kit cut 7cdbb61b5fa0, PRH_FnCheck.v c40cf3fdcd2a)
     Cno102A_R9.v   CA9 Cmp         cn_cmp_seg, cn_same1_step, cn_same2_step (the four abort edges refuted there)
   This file proves no new step: it binds the pieces. Contract: Cno102A_Base.v on the kit cut
   7cdbb61b5fa0 (the cuts carry cn_prog, the grants o1 o2 o0, the wild budget, cn_cdead and cn_fo).
   THE FREE / REALLOC MOVE: the restated tparse_noting_specX crosses a free (pj_parse frees on refusal) and concludes
   SRr' segs RZ_cf with its post at wle', so every composed statement here from CN_INIT / CN_INIT3 / CN_READ1 on is
   SRr' SEGS RZ_cf and the pieces bind by SRr'_bind (YSRrG.v). The cuts after the first parse_noting are the base's R
   forms at wle' SEGS RZ_cf (cn_ex_read2R, cn_ex_pn2R, cn_ex_read3R, cn_ex_pn3R, cn_ex_cmpR, cn_ex_freeR). The pieces
   before the first parse_noting (CA5 cn_init_seg / cn_init3_seg, CA6 cn_read1_seg) stay at SRr and lift by
   SRr_SRr'; their CN_READ2 exit (cn_ex_read2, at wle) lifts into cn_ex_read2R at wle' by the base's
   cn_ex_read2R_mono (cnR_up2), where CA7 and the pn1 step meet. THE HULL: this file makes no call; the cuts carry
   their stage's budget conjunct and the pieces thread it (the pn steps pay tparse_noting_specX's hull premise from
   it).
   SECTION HYPOTHESES (the pieces' own, by name): LAWS (the journal's laws), IMG (cn_img: the image facts, proved at
   the instance), HW (the prh_head_wide), MEMSET (the __asan_memset row: its witness at the A' instance PI_prog_A is
   Cno102A_Mset.cn_memset_A B ARx LAWS TB, by citation of a Theorem Labs lane's prow_asan_memset_xm_A, rows102 599a4cefc740
   lib/A/PRowSet.v 4eac5264e9e8, given TfibSyms B), HRO / HSAME / HPN (the texts of fuzz_alloc_ran_out, same,
   parse_noting, for any float state); P with srr_inv_laws / srr_inv_call / srr_inv_mn (the top instantiates P :=
   cn_mn D: cn_mn_laws / cn_mn_call / cn_mn_mn of the base). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Cno102A_Base Cno102A_Ro
  Cno102A_R5 Cno102A_R6 Cno102A_Rpn Cno102A_R9.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cn_img B.
Hypothesis HW : prh_head_wide.
Hypothesis MEMSET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARx OSet (SIGMA AS___asan_memset).
Hypothesis HRO : forall fz : YK11.FPState, @tfuzz_alloc_ran_out_specX fz rc cp prh_img_A RL A_prog_listing PA B ARx SK.
Hypothesis HSAME : forall fz : YK11.FPState, @tsame_specX fz rc cp prh_img_A RL A_prog_listing PA B ARx SK DOC_D.
Hypothesis HPN : forall fz : YK11.FPState,
  @tparse_noting_specX fz rc ci cp prh_img_A RL A_prog_listing PA B ARx SK CTX0.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Hypothesis PCALL : srr_inv_call SEGS P.
Hypothesis PMN : srr_inv_mn SEGS P.
#[local] Notation CNPRE := (@cn_pre fx rc ci cp RL PA B ARx CTX0).
#[local] Notation FIN D := (fun W' c' =>
  @cn_ex_freeR fx rc cp RL SK PA B ARx (wle' SEGS YGcfRehidePost.RZ_cf) D W' c' /\ P (ms_mem (cfg_ms c'))).
(* the zone and the world relation of the cuts after the first parse_noting *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
#[local] Notation RCF := (wle' SEGS YGcfRehidePost.RZ_cf).

(* a CN_READ2 exit reached before any free (CA5's 3rd-NULL arm, CA6's skip arm: cn_ex_read2, at wle) is one at wle',
   where CA7 starts (the base's mono lemma over the world relation, by wle_wle') *)
Lemma cnR_up2 : forall D W c, @cn_ex_read2 fx rc cp RL SK PA B ARx D W c ->
  @cn_ex_read2R fx rc cp RL SK PA B ARx RCF D W c.
Proof.
intros D W c H. exact (cn_ex_read2R_mono (fx := fx) (SK := SK) B ARx (@wle SEGS) RCF (wle_wle' SEGS RZ) D W c H).
Qed.

(* ---- CA9: CN_CMP -> CN_FREE, through the two same calls when the input reads ---- *)
Lemma cnR_cmp : forall D W c, CNPRE D -> @cn_ex_cmpR fx rc cp RL SK PA B ARx RCF D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & rc2 & rc3
  & st1 & st2 & st3 & o1 & o2 & o0 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [eapply (cn_cmp_seg (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [[HF | HS1] HP1]; [apply SRr'_ret; split; assumption|].
destruct HS1 as (fxk1 & ly1 & S1 & Hp1 & regs1 & mem1 & md1 & k1 & Lam1 & peak1 & cnt1 & r11 & r21 & r31 & t1
  & D11 & D21 & D31 & o11 & o21 & o01 & -> & HAT1).
assert (HPm1 : P mem1) by exact HP1.
eapply SRr'_bind; [eapply (cn_same1_step (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W2 c2 _ [HS2 HP2].
destruct HS2 as (fxk2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & Lam2 & peak2 & cnt2 & r12 & r22 & r32 & t2
  & D12 & D22 & D32 & o12 & o22 & o02 & -> & HAT2).
assert (HPm2 : P mem2) by exact HP2.
eapply (cn_same2_step (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption.
Qed.

(* ---- parse_noting 3, then CA9 ---- *)
Lemma cnR_pn3 : forall D W c, CNPRE D -> @cn_ex_pn3R fx rc cp RL SK PA B ARx RCF D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & r1 & r2 & r3 & rc1 & rc2 & st1 & st2
  & o1 & o2 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [eapply (cn_pn3_step (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [HC HP1]. exact (cnR_cmp D W1 c1 HPRE HC HP1).
Qed.

(* ---- CA8: CN_READ3 -> CN_FREE / CN_CMP / parse_noting 3 ---- *)
Lemma cnR_read3 : forall D W c, CNPRE D -> @cn_ex_read3R fx rc cp RL SK PA B ARx RCF D W c ->
  P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & rc2 & st1
  & st2 & o1 & o2 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [eapply (cn_read3_seg (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [[HF | [HC | HN]] HP1].
- apply SRr'_ret. split; assumption.
- exact (cnR_cmp D W1 c1 HPRE HC HP1).
- exact (cnR_pn3 D W1 c1 HPRE HN HP1).
Qed.

(* ---- parse_noting 2, then CA8 ---- *)
Lemma cnR_pn2 : forall D W c, CNPRE D -> @cn_ex_pn2R fx rc cp RL SK PA B ARx RCF D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & r1 & r2 & r3 & rc1 & st1 & o1 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [eapply (cn_pn2_step (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [HC HP1]. exact (cnR_read3 D W1 c1 HPRE HC HP1).
Qed.

(* ---- CA7: CN_READ2 -> CN_FREE / CN_READ3 / parse_noting 2 (the cut at wle': it holds after parse_noting 1) ---- *)
Lemma cnR_read2 : forall D W c, CNPRE D -> @cn_ex_read2R fx rc cp RL SK PA B ARx RCF D W c ->
  P (ms_mem (cfg_ms c)) -> SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & own0 & rc1 & st1
  & o1 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [eapply (cn_read2_seg (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [[HF | [HC | HN]] HP1].
- apply SRr'_ret. split; assumption.
- exact (cnR_read3 D W1 c1 HPRE HC HP1).
- exact (cnR_pn2 D W1 c1 HPRE HN HP1).
Qed.

(* ---- parse_noting 1 (the first free in the walk: SRr' from here on), then CA7 ---- *)
Lemma cnR_pn1 : forall D W c, CNPRE D -> @cn_ex_pn1 fx rc cp RL SK PA B ARx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [eapply (cn_pn1_step (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [HC HP1]. exact (cnR_read2 D W1 c1 HPRE HC HP1).
Qed.

(* ---- CA6: CN_READ1 -> CN_READ2 / parse_noting 1 (CA6 runs before any free: lifted by SRr_SRr', its CN_READ2 exit by
   cnR_up2) ---- *)
Lemma cnR_read1 : forall D W c, CNPRE D -> @cn_ex_read1 fx rc cp RL SK PA B ARx D W c -> P (ms_mem (cfg_ms c)) ->
  SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE HEX HPc.
destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & own0 & -> & HAT).
assert (HPm : P mem) by exact HPc.
eapply SRr'_bind; [apply SRr_SRr';
  eapply (cn_read1_seg (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [[HC | HN] HP1].
- exact (cnR_read2 D W1 c1 HPRE (cnR_up2 D W1 c1 HC) HP1).
- exact (cnR_pn1 D W1 c1 HPRE HN HP1).
Qed.

(* ---- CA5-CA9 from the two CA5 cuts to the free cut (CA5 runs before any free: lifted by SRr_SRr') ---- *)
Theorem cn_R_init : forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  CNPRE D -> @cn_at_init fx rc cp RL SK PA B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 -> P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (cn_pc CN_INIT) regs mem md) (FIN D).
Proof.
intros D fxk ly S Hp W regs mem md k r1 r2 r3 own0 HPRE HAT HPm.
eapply SRr'_bind; [apply SRr_SRr';
  eapply (cn_init_seg (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [HC HP1]. exact (cnR_read1 D W1 c1 HPRE HC HP1).
Qed.
Theorem cn_R_init3 : forall D fxk ly S Hp W regs mem md k r1 r2,
  CNPRE D -> @cn_at_init3 fx rc cp RL SK PA B ARx D fxk ly S Hp W regs mem md k r1 r2 -> P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (cn_pc CN_INIT3) regs mem md) (FIN D).
Proof.
intros D fxk ly S Hp W regs mem md k r1 r2 HPRE HAT HPm.
eapply SRr'_bind; [apply SRr_SRr';
  eapply (cn_init3_seg (fx := fx) (SK := SK)) with (B := B) (ARx := ARx) (CTX0 := CTX0) (P := P); eassumption|].
intros W1 c1 _ [HC HP1]. exact (cnR_read2 D W1 c1 HPRE (cnR_up2 D W1 c1 HC) HP1).
Qed.
(* the same in the exit form of CA4 (cn_ex_init \/ cn_ex_init3), for the composition with CA0-CA4 *)
Theorem cn_R : forall D W c, CNPRE D ->
  (@cn_ex_init fx rc cp RL SK PA B ARx D W c \/ @cn_ex_init3 fx rc cp RL SK PA B ARx D W c) ->
  P (ms_mem (cfg_ms c)) -> SRr' SEGS RZ W c (FIN D).
Proof.
intros D W c HPRE [HEX | HEX] HPc.
- destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & own0 & -> & HAT).
  exact (cn_R_init D fxk ly S Hp W regs mem md k r1 r2 r3 own0 HPRE HAT HPc).
- destruct HEX as (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & -> & HAT).
  exact (cn_R_init3 D fxk ly S Hp W regs mem md k r1 r2 HPRE HAT HPc).
Qed.
End r.
