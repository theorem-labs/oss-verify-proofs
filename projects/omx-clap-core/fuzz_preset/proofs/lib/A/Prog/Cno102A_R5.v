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
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): segment CA5 Init of the re-walk of
   check_no_overread (plan, the internal file PLAN-cno-caw-102.md 5.1, both arms), by a Theorem Labs lane; refit to the cn_pst
   interface by a Theorem Labs lane; re-fit to the kit's Batch 2 (the ledger carries g_most / g_own_ran_out, cn_pst deleted) and
   to the #102 kit (the cuts carry cn_prog, the events made since entry, in place of a room position) by
   a Theorem Labs lane; re-fit to the kit cut 7cdbb61b5fa0 (no DW, the journal at a wild budget, cn_cdead) by
   a Theorem Labs lane.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma)
   INPUTS (by path): contract lib/A/Prog/Cno102A_Base.v ba76a7bc31c9 (cn_pre CTX0 D without DW, read by name:
     cn_pre_fpre; cn_J / cn_base at a wild budget wk, LAST: CN_INIT / CN_INIT3 / CN_READ1 at 0, CN_READ2 at 2;
     cn_J_of_x; cn_at_init / cn_at_read1 carry `own0 <> 0 -> cn_cdead D`, cn_at_init3 `cn_cdead D`, cn_at_read2's
     own0 <> 0 arm `.. /\ st1 = None /\ cn_cdead D`; each cut's LAST conjunct, the hull budget
     `PresetHullBudget.hull_budget S (cn_hrest_<stage> (ci_x D))`, and the split equation cn_hrest_rd1_split; cn_at_read2
     is the wle form beside cn_at_read2R); the cut of record at its blobs: lib/A/PRH_FnCheck.v c40cf3fdcd2a,
     lib/A/PRH_Base.v ef7c8ca98529 (prh_most / prh_own,
     prh_glob / prh_ledger and their projections; fpre's last conjunct frm_zero), lib/A/PRH_Img.v 934516a622e8;
     listing lib/A/Listing_prog.v; engine YC80x.v, YCbqG.v (ajournal_xw, the journal at the wild-trace list WS;
     ajournal_x its WS = [] instance; the projections ajx_ar / ajx_ly / ajx_stk), YCbqGwild.v (wbudget,
     wfresh_nil_set), YCbq.v, YSRrMemnorm.v, YGcallMxmn.v, YN01.v, YK11.v, YK14.v; kit lib/A/Prog/S1Ledger.v; the hull
     kit lib/Spec/PresetHullBudget.v (hull_budget_app, hull_used_refl).
   WHAT: two forward segment lemmas over the contract (form the internal file lane-102.md :29-31), P abstract with srr_inv_laws, and
   srr_inv_call for the three __asan_memset calls (the row's keep is the memnorm one; S6PjString.v's PCALL):
     cn_init_seg       CN_INIT  (0x81b64) -> cn_ex_read1 (0x81bf0), the third copy non-NULL;
     cn_init3_seg      CN_INIT3 (0x81c1c) -> cn_ex_read2 (0x81cb4), the third copy NULL;
     cn_init3_seg_at   the same with the exit's values named: rc1 = -1, st1 = None, own0 = 1, r3 = 0, nr = 1,
                       Lam / peak / cnt / ran the entry's, the grant o1 = None (no reading was made).
   Both exits keep ly, S, Hp, k of the cut (no allocation: S' = S) and the world W. CA5 makes no model event (the
   memsets are runtime rows), so the cut's cn_prog D (cn_cevs D r1 r2 r3) S is the exit's, at the same S.
   THE WILD BUDGET: both entry cuts are at cn_J .. 0, whose wbudget [] 0 WS forces WS = [] (YCbqGwild.wfresh_nil_set:
   wfresh [] WS = length WS), so the journal is the plain ajournal_x (r5_J, by r5_J_of_cn) and CA5 runs the plain
   journal steps and memset rows on it; no step stores a trace (S' = S), and the exits' cn_J at 0 (CN_READ1) / 2
   (CN_READ2) is cn_J_of_x of the plain journal. CNO-COPY: cn_at_init's `own0 <> 0 -> cn_cdead D` is CN_READ1's,
   cn_at_init3's `cn_cdead D` is CN_READ2's own0 <> 0 arm's (own0 = 1 there); cn_cdead names only the entry state.
   THE FREE / REALLOC MOVE: CA5 runs before every free, so its statements stay at SRr with the cuts at wle; the exits
   are the base's wle forms cn_ex_read1 / cn_ex_read2 (a consumer lifts the CN_READ2 exit into wle' by the base's mono
   lemma over the world relation, where the walk meets the cut after parse_noting 1).
   THE HULL: each cut carries LAST `PresetHullBudget.hull_budget S (cn_hrest_<stage> (ci_x D))`, the part of the
   all-granted events still to pay (stage copies at CN_INIT / CN_INIT3 / CN_READ1, rd1 at CN_READ2). CA5 makes no
   allocator call (S' = S): the first arm passes cn_at_init's conjunct to CN_READ1 (the same stage); the 3rd-NULL arm
   skips reading 1, which pays nothing, so its exit drops that reading's events from the budget (the base's
   cn_hrest_rd1_split, then PresetHullBudget.hull_budget_app with nothing used, hull_used_refl).
   SECTION HYPOTHESES: LAWS (AR_laws_x .. cf_head); IMG (the contract's cn_img: cni_hi9, cni_own, cni_pst_rw,
   cni_pst_seg, cni_pst_ok); HW (the kit's prh_head_wide, PRH_Base.v: the ledger's head words lie in their blocks); MEMSET
   (YGcallMxmn.v aintrin_realizes_xm OSet at SIGMA AS___asan_memset, at any float state).
   METHOD: hand steps over `@YK11.mkst fz` configs (section 2: addi / ld / lbu / sb / jal at a PCall slot, each slot
   decided by a closed vm_compute on PL_cno_A's table), the journal carried by YCbqG.v ajournal_x_exec (the shadow
   stores, F's shadow is in the journal's own frame) / ajournal_x_pst_write (the store to g_own_ran_out) /
   ajournal_x_materialize (model-only steps) and by YGcallMxmn.v aj_intrin_at_xm (the memsets, dest in the own
   frame); the exit facts from one invariant r5_inv (every byte off F's first 504 bytes, F's shadow and the memset
   window below sp is the cut's) by r5_exit. The ledger's statics (the kit's Batch 2: prh_glob carries g_most and
   g_own_ran_out): every cell is an image byte off those writes (YCbq.v val_mem_kept); r5_exit rebuilds the exit's
   ledger with the own cell the exit holds (r5_own_kept: the cut's own0 on the first arm; on the 3rd-NULL arm the
   `sb 1` gives prh_own 1, the stored byte, pi_gz_own_ran_out = 1, and g_most 0xa65e0 is apart from g_own_ran_out
   0x5dd540, PRH_Img.v's values, so the ledger's other cells are kept).
   THE CODE (DERIVED offsets inside check_no_overread, pc = BASE + CN_OFF + off):
     608 `lbu s10, -0x558(s8)` (g_own_ran_out, cni_hi9); 612-636 seven `sb zero, 4..10(s2)` (d1's shadow, F's
     shadow is in the journal's own frame); 640 `li a2, 56`; 644 `ld a0, 56(s1)` (d1); 648 `mv a1, zero`; 652
     `jal __asan_memset`; 656-680 `sb zero, 16..22(s2)`; 684 li; 688 `ld s5, 48(s1)` (d2); 692 `mv a0, s5`; 696 mv;
     700 jal; 704-728 `sb zero, 28..34(s2)`; 732 li; 736 `mv a0, s3` (d3); 740 mv; 744 jal; 748 = CN_READ1.
     792 `li a0, 1`; 796 `sb a0, -0x558(s8)` (a prh_pst cell: ajournal_x_pst_write under IMG's cni_pst_ok); 800-824
     the d1 shadow; 828 li; 832 `mv a0, s9`; 836 mv; 840 jal; 844-868 the d2 shadow; 872 li; 876 `mv a0, s5`; 880 mv;
     884 jal; 888-912 the d3 shadow; 916 li; 920 `mv a0, s10`; 924 mv; 928 jal; 932 `li s7, -1`; 936 `mv s3, s10`;
     940 `ld s10, 24(s1)` (r1); 944 = CN_READ2.
   No call here but the memset intrinsic; no abort edge, no ASan report site in these offsets.
   Numerals: offsets above (DERIVED); 56 / 48 / 24 / 1368 / 512 (LENGTH: struct, slot, lo12, frame-class-3 bytes);
   0 / 1 / -1 / 256 (WORD); 0 / 2 (the cuts' wild budgets, LENGTH); register numbers (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallMxmn YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Cno102A_Base.
(* YF0v.v (through YGcallMxmn) sets the zify euclidean-division flag to false globally; lia here reads Z.div / Z.modulo
   with their equations *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== 1. image-free facts ======== *)
Lemma r5_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod x 32 ltac:(lia)). change (2 ^ 5) with 32. lia.
Qed.

Section u. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma r5_apr_aview : forall H (m : word -> option byte) a, apresent H m a -> aview segs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma r5_apr_wr : forall H (m : word -> option byte) a, apresent H m a -> writable_at segs (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma r5_grows_of_apr : forall H (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *.
destruct (H x) eqn:Ehx; [exfalso; exact (Hx eq_refl)|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ehx | exists b; exact Em]).
destruct (Hp _ Ha) as [Hh' [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hh', Hb'. rewrite Hh' in Ehx. rewrite Hb'. discriminate.
Qed.

Lemma r5_grows_trans : forall (m1 m2 m3 : word -> option byte), mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. exact (H2 x (H1 x Hx)). Qed.

Lemma r5_aview_vis : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros H m m' a Hg Hv. unfold aview, mbyte in *.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E1.
- pose proof (Hg (Z_to_bv 64 a) ltac:(rewrite E1; discriminate)) as Hg'.
  destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; exact (Hg' eq_refl)].
- destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.

Lemma r5_mbyte_of_aview : forall H (m : word -> option byte) a v, aview segs H m a = Some v -> 0 <= v < 256 ->
  mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
intros H m a v Ha Hv. unfold aview in Ha. destruct (mbyte segs (mrestrict H m) a) as [b|]; cbn in Ha; [|discriminate].
injection Ha as Hb. f_equal. apply bv_eq. rewrite <- Hb. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 8) with 256. lia.
Qed.

Lemma r5_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by exact Hv. apply Z.mod_small. exact Hv.
Qed.

Lemma r5_val_mem1_of_aview : forall H (m : word -> option byte) a v, aview segs H m a = Some v -> 0 <= v < 256 ->
  val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Ha Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, r5_le_byte1 by exact Hv.
exact (r5_mbyte_of_aview H m a v Ha Hv).
Qed.

Lemma r5_aview_of_val_mem1 : forall H (m : word -> option byte) a v, val_mem segs (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview segs H m a = Some v.
Proof.
intros H m a v Hm Hv. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r, r5_le_byte1 in Hm by exact Hv.
unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma r5_rdn1 : forall (m : word -> option byte) a v, val_mem segs m a 1 v -> 0 <= v < 256 ->
  rdn segs m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof.
intros m a v Hm Hv. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r, r5_le_byte1 in Hm by exact Hv.
unfold mbyte in Hm. cbn [rdn]. destruct (m (Z_to_bv 64 a)) as [b|]; [injection Hm as ->; reflexivity|].
rewrite Hm. reflexivity.
Qed.
End u.

(* ======== 2. the hand steps over `@YK11.mkst fz` configs (one step per instruction at its listing slot: the register
   and memory steps at a PW slot, the pc advanced by 4; `jal ra` at a PCall slot, the pc the callee's; the continuation
   takes any model the step may materialize) ======== *)
Section stp. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).
#[local] Abbreviation hcfg regs pc mem md := (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md).

Lemma r5_pc4 : forall k, 0 <= k -> k + 4 < 2 ^ 40 -> v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof.
intros k Hk0 Hk4. pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma h_addi : forall (W : world SEGS) regs mem md Q w k k' (rd rs : bv 5) (imm : bv 12),
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rd rs imm Hpl Hdec Hrd Hk0 Hk4 -> HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (r5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  exact (HK model' Hsame).
Qed.

Lemma h_ld : forall (W : world SEGS) regs mem md Q w k k' (rd rs : bv 5) (imm : bv 12) a v,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rd rs imm a v Hpl Hdec Hrd Hk0 Hk4 -> Ha Ha0 Ha8 Hw HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hw) as Hv.
apply val_mem_word_mem in Hv.
destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hv Ha0 Ha8) as (bs & Hbs & Hle).
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_ld SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm bs (Z_to_bv 64 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) by first [rewrite Ha; exact Hbs | exact Hle].
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (r5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  exact (HK model' Hsame).
Qed.

Lemma h_lbu : forall (W : world SEGS) regs mem md Q w k k' (rd rs : bv 5) (imm : bv 12) a v,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v -> 0 <= v < 256 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rd rs imm a v Hpl Hdec Hrd Hk0 Hk4 -> Ha Hm Hv HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (r5_rdn1 SEGS (mrestrict (w_H W) mem) a v Hm Hv) as Hr.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_lbu SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd rs imm (Z_to_bv 8 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) by (rewrite Ha; exact Hr).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (r5_pc4 k Hk0 Hk4). cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 v))) with (Z_to_bv 64 v); [exact (HK model' Hsame)|].
  rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 8) with 256. lia.
Qed.

(* one byte store: the new memory is the old one but at a, which now reads the low byte of rs2 *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Lemma h_sb : forall (W : world SEGS) regs mem md Q w k k' (rs1 rs2 : bv 5) (imm : bv 12) a,
  plookup pl_tpi k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  w_H W (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict (w_H W) mem) a -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, bv_unsigned x <> a -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     aview SEGS (w_H W) mem' a = Some (bv_unsigned (getr regs rs2) mod 256) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + k') mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q w k k' rs1 rs2 imm a Hpl Hdec Hk0 Hk4 -> Ha Ha64 Hh Hwv HPm HK.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
set (addr := v_addi (getr regs rs1) (bv_signed imm)) in *.
set (bt := Z_to_bv 8 (bv_unsigned (getr regs rs2))).
assert (Hok : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) addr 1 = true).
{ cbn [RiscvSemantics.store_ok]. unfold writable_at in Hwv. rewrite Ha.
  destruct (wview SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 a)); [reflexivity | contradiction]. }
eapply (SRr_step_inv SEGS pa_wx P PLAW W); [reflexivity | | exact HPm |].
- rewrite restrict_mkst_fx.
  rewrite (step_sb SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hok).
  reflexivity.
- intros model' Hsame HP'. rewrite (r5_pc4 k Hk0 Hk4).
  set (mem' := munrestrict (w_H W) mem (fun x : word => if bv_eqb x addr then Some bt else mrestrict (w_H W) mem x)).
  refine (HK model' mem' Hsame _ _ _ _ HP').
  + intros x Hx. unfold mem', munrestrict, mrestrict. cbv beta. destruct (w_H W x) eqn:Ex; [reflexivity|].
    destruct (bv_eqb x addr) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_true_iff in Eb. apply Hx.
    rewrite Eb, Ha, unsigned_lit_small by exact Ha64. reflexivity.
  + intros x Hx. unfold mem', munrestrict, mrestrict in *. cbv beta in *. destruct (w_H W x) eqn:Ex; [exact Hx|].
    destruct (bv_eqb x addr); [discriminate | exact Hx].
  + intros x Hx. unfold mem', munrestrict. cbv beta. rewrite Hx. reflexivity.
  + unfold aview, mbyte, mem', munrestrict, mrestrict. cbv beta. rewrite <- Ha. rewrite <- Ha in Hh. rewrite Hh.
    replace (bv_eqb addr addr) with true by (symmetry; apply bv_eqb_true_iff; reflexivity).
    cbn [option_map]. unfold bt. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* `jal ra, s` at a PCall slot: the callee's entry with ra = the return slot *)
Lemma h_call : forall (W : world SEGS) regs mem md Q k k' (s : asym),
  plookup pl_tpi k = Some (PCall s 1%bv) -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs 1%bv (Z_to_bv 64 (BASE + k'))) (pa_sigma s) mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' s Hpl Hk0 Hk4 -> HK.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- pl_tpi_eq in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with context [Jal ?r ?im] => rename r into rdj; rename im into imm end.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd _]. apply reg_eqb_eq in Hrd. subst rdj.
apply Z.eqb_eq in Ht.
eapply (SRr_step SEGS pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 wz) 1%bv imm (pa_fetch_ok _ _ Hfw)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  reflexivity.
- intros model' Hsame. cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (1%bv : bv 5) 0) with false by reflexivity. rewrite (r5_pc4 k Hk0 Hk4).
  replace (btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)) with (Z_to_bv 64 (pa_sigma s)); [exact (HK model' Hsame)|].
  unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Ht. unfold zcanon.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, M64. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ---- the slot checks: a closed boolean on the listing, decided by vm_compute at the use (no evar) ---- *)
Definition r5_slot (k : Z) (f : instr -> bool) : bool :=
  match plookup pl_tpi k with
  | Some (PW w) => match decode_any (Z_to_bv 32 w) with Some (i, isz) => (isz =? 4) && f i | None => false end
  | _ => false
  end.
Definition f_addi (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with OpImm ALU_ADD rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition f_ld (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with Load SZ8 true rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition f_lbu (rd rs : bv 5) (n : Z) (i : instr) : bool :=
  match i with Load SZ1 false rd' rs' imm => bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? n) | _ => false end.
Definition f_sb (rs1 rs2 : bv 5) (n : Z) (i : instr) : bool :=
  match i with Store SZ1 rs1' rs2' imm => bv_eqb rs1' rs1 && bv_eqb rs2' rs2 && (bv_signed imm =? n) | _ => false end.

Lemma r5_slot_ok : forall k f, r5_slot k f = true ->
  exists w i, plookup pl_tpi k = Some (PW w) /\ decode_any (Z_to_bv 32 w) = Some (i, 4%Z) /\ f i = true.
Proof.
intros k f H. unfold r5_slot in H.
destruct (plookup pl_tpi k) as [[w| | | | | ]|]; try discriminate H.
destruct (decode_any (Z_to_bv 32 w)) as [[i isz]|] eqn:Hd; [|discriminate H].
apply andb_prop in H as [Hz Hf]. apply Z.eqb_eq in Hz. subst isz. exists w, i. auto.
Qed.

Lemma s_addi : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) n,
  r5_slot k (f_addi rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (v_addi (getr regs rs) n)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs n Hs Hrd Hk0 Hk4 Hk' HK.
destruct (r5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf. lazymatch type of Hf with f_addi _ _ _ (OpImm ?al _ _ _) = true => destruct al; try discriminate Hf end.
unfold f_addi in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (h_addi W regs mem md Q w k _ _ _ _ Hpl Hdec Hrd Hk0 Hk4 eq_refl HK).
Qed.

Lemma s_ld : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) n a v,
  r5_slot k (f_ld rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) n = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs n a v Hs Hrd Hk0 Hk4 Hk' Ha Ha0 Ha8 Hw HK.
destruct (r5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with f_ld _ _ _ (Load ?sz ?sg _ _ _) = true => destruct sz; try discriminate Hf; destruct sg; try discriminate Hf end.
unfold f_ld in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (h_ld W regs mem md Q w k _ _ _ _ a v Hpl Hdec Hrd Hk0 Hk4 eq_refl Ha Ha0 Ha8 Hw HK).
Qed.

Lemma s_lbu : forall (W : world SEGS) regs mem md Q k k' (rd rs : bv 5) n a v,
  r5_slot k (f_lbu rd rs n) = true -> bv_eqb rd 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs) n = Z_to_bv 64 a ->
  val_mem SEGS (mrestrict (w_H W) mem) a 1 v -> 0 <= v < 256 ->
  (forall md', same_but_materialized md md' ->
     SRr SEGS W (hcfg (regupd regs rd (Z_to_bv 64 v)) (BASE + k') mem md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rd rs n a v Hs Hrd Hk0 Hk4 Hk' Ha Hm Hv HK.
destruct (r5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with f_lbu _ _ _ (Load ?sz ?sg _ _ _) = true => destruct sz; try discriminate Hf; destruct sg; try discriminate Hf end.
unfold f_lbu in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (h_lbu W regs mem md Q w k _ _ _ _ a v Hpl Hdec Hrd Hk0 Hk4 eq_refl Ha Hm Hv HK).
Qed.

Lemma s_sb : forall (W : world SEGS) regs mem md Q k k' (rs1 rs2 : bv 5) n a,
  r5_slot k (f_sb rs1 rs2 n) = true -> 0 <= k -> k + 4 < 2 ^ 40 -> k' = k + 4 ->
  v_addi (getr regs rs1) n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  w_H W (Z_to_bv 64 a) = false -> writable_at SEGS (mrestrict (w_H W) mem) a -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, bv_unsigned x <> a -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     aview SEGS (w_H W) mem' a = Some (bv_unsigned (getr regs rs2) mod 256) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + k') mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
intros W regs mem md Q k k' rs1 rs2 n a Hs Hk0 Hk4 Hk' Ha Ha64 Hh Hwv HPm HK.
destruct (r5_slot_ok k _ Hs) as (w & i & Hpl & Hdec & Hf).
destruct i; try discriminate Hf.
lazymatch type of Hf with f_sb _ _ _ (Store ?sz _ _ _) = true => destruct sz; try discriminate Hf end.
unfold f_sb in Hf. apply andb_prop in Hf as [Hf Hn]. apply andb_prop in Hf as [E1 E2].
apply reg_eqb_eq in E1. apply reg_eqb_eq in E2. apply Z.eqb_eq in Hn. subst.
exact (h_sb W regs mem md Q w k _ _ _ _ a Hpl Hdec Hk0 Hk4 eq_refl Ha Ha64 Hh Hwv HPm HK).
Qed.

Lemma r5_apr_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|]. specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh, Hb in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; [discriminate | reflexivity]].
Qed.

(* n stores of zero to n consecutive bytes s2v + j .. through s2 (the shadow unpoison runs) *)
Fixpoint r5_sb_slots (k j : Z) (n : nat) : bool :=
  match n with O => true | S n' => r5_slot k (f_sb 18%bv 0%bv j) && r5_sb_slots (k + 4) (j + 1) n' end.

Lemma h_sbn : forall n (W : world SEGS) regs mem md Q k j s2v,
  getr regs 18%bv = Z_to_bv 64 s2v -> 0 <= s2v < 2 ^ 64 ->
  0 <= k -> k + 4 * Z.of_nat n < 2 ^ 40 -> 0 <= s2v + j -> s2v + j + Z.of_nat n <= 2 ^ 64 ->
  r5_sb_slots k j n = true ->
  (forall i, 0 <= i < Z.of_nat n -> apresent (w_H W) mem (s2v + j + i)) -> P mem ->
  (forall md' mem', same_but_materialized md md' ->
     (forall x : word, ~ (s2v + j <= bv_unsigned x < s2v + j + Z.of_nat n) ->
        mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x : word, w_H W x = true -> mem' x = mem x) ->
     (forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W) mem' (s2v + j + i) = Some 0) ->
     P mem' ->
     SRr SEGS W (hcfg regs (BASE + (k + 4 * Z.of_nat n)) mem' md') Q) ->
  SRr SEGS W (hcfg regs (BASE + k) mem md) Q.
Proof.
induction n as [|n IH]; intros W regs mem md Q k j s2v Hs2 Hs2r Hk0 Hk4 Hj0 Hj1 Hsl Hpr HPm HK.
- replace (k + 4 * Z.of_nat 0) with k in HK by lia.
  apply (HK md mem (same_but_materialized_refl md)); [intros x _; reflexivity | intros x Hx; exact Hx |
    intros x _; reflexivity | intros i Hi; cbn in Hi; lia | exact HPm].
- rewrite Nat2Z.inj_succ in Hk4, Hj1, Hpr, HK. cbn [r5_sb_slots] in Hsl. apply andb_prop in Hsl as [Hs Hsl].
  pose proof (Hpr 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  apply (s_sb W regs mem md Q k (k + 4) 18%bv 0%bv j (s2v + j) Hs Hk0 ltac:(lia) eq_refl); [| lia | exact (proj1 H0) |
    exact (r5_apr_wr _ _ _ _ H0) | exact HPm |].
  { rewrite Hs2. unfold v_addi. rewrite unsigned_lit_small by lia. reflexivity. }
  intros md1 mem1 Hs1 Hf1 Hg1 Hh1 Hv1 HP1. change (getr regs 0%bv) with (Z_to_bv 64 0) in Hv1.
  change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in Hv1.
  apply (IH W regs mem1 md1 Q (k + 4) (j + 1) s2v Hs2 Hs2r ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsl).
  { intros i Hi. apply (r5_apr_grows _ mem mem1 _ Hg1). replace (s2v + (j + 1) + i) with (s2v + j + (i + 1)) by lia.
    apply Hpr. lia. }
  { exact HP1. }
  intros md' mem' Hs' Hf' Hg' Hh' Hv' HP'.
  replace (k + 4 + 4 * Z.of_nat n) with (k + 4 * (Z.of_nat n + 1)) in * by lia.
  apply (HK md' mem' (same_but_materialized_trans _ _ _ Hs1 Hs')).
  + intros x Hx. rewrite Hf' by lia. apply Hf1. lia.
  + exact (r5_grows_trans _ _ _ Hg1 Hg').
  + intros x Hx. rewrite (Hh' x Hx). exact (Hh1 x Hx).
  + intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    * rewrite Z.add_0_r. rewrite <- Hv1. apply aview_eq_of. apply Hf'.
      rewrite unsigned_lit_small by lia. lia.
    * replace (s2v + j + i) with (s2v + (j + 1) + (i - 1)) by lia. apply Hv'. lia.
  + exact HP'.
Qed.
End stp.

(* ======== 3. CA5 over the contract ======== *)
Lemma r5_cs : forall z : Z, ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%bool = true ->
  acallee_saved z.
Proof.
intros z H. unfold acallee_saved.
repeat (apply Bool.orb_prop in H as [H|H]); try (apply Z.eqb_eq in H; lia).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma r5_pres : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Ltac r5_bvne := let E := fresh "E" in intro E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E.
(* a register of a later state, back to an earlier one: through regupd and the memset's aregs_preserved *)
Ltac r5_rs := repeat first
  [ rewrite getr_same by r5_bvne
  | rewrite getr_other by r5_bvne
  | match goal with H : aregs_preserved ?r1 ?r2 |- context [getr ?r2 ?r] =>
      rewrite (r5_pres r1 r2 r H) by (apply r5_cs; reflexivity) end ].
Ltac r5_in := solve [repeat (first [left; reflexivity | right])].
Ltac r5_consts := unfold kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd, kHighMemEnd, SHADOW_OFF, ESTACK in *.

Section cn5. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instance PL_cno_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the contract's image facts (Cno102A_Base.v cn_img: cni_hi9, cni_own, cni_pst_rw, cni_pst_seg, cni_pst_ok) *)
Hypothesis IMG : cn_img B.
(* The kit's head-width fact, the Section hypothesis the kit owner rules for walks (PRH_Base.v ef7c8ca98529 :241, `8 <= cf_head`): the
   ledger's head words lie in their blocks *)
Hypothesis HW : prh_head_wide.
(* the memset row with the memnorm keep (YGcallMxmn.v aintrin_realizes_xm), at ANY float state *)
Hypothesis MEMSET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARx OSet (SIGMA AS___asan_memset).
(* the plain journal from entry (YCbqG.v ajournal_x, the WS = [] instance of ajournal_xw), the journal CA5 runs on:
   the entry cuts' cn_J .. 0 is it (r5_J_of_cn), and it is cn_J at any wild budget (Cno102A_Base.v cn_J_of_x) *)
Definition r5_J (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (md : Model) (k : Z) : Prop :=
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D)
    (ci_mem D) (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp W mem md k.
#[local] Notation CNJ := r5_J.

(* the budget 0 forces the empty wild-trace list: wbudget [] 0 WS is length WS <= 0 (YCbqGwild.wfresh_nil_set) *)
Lemma r5_J_of_cn : forall D ly S Hp W mem md k,
  @cn_J rc SK PA B ARx D ly S Hp W mem md k 0 -> r5_J D ly S Hp W mem md k.
Proof.
intros D ly S Hp W mem md k (WS & HJ & HBu).
unfold YCbqGwild.wbudget in HBu. rewrite YCbqGwild.wfresh_nil_set in HBu.
destruct WS as [|t WS]; [exact HJ | cbn [length] in HBu; lia].
Qed.

Lemma r5_stk : STK_check_no_overread = 27424.
Proof. vm_compute. reflexivity. Qed.

(* where the frame, the stack and sp0 lie (from the cut's journal and frame facts) *)
Definition r5_geo (D : cn_in) (ly : alayout) : Prop :=
  frame_addr ly CN_CID (ci_fpos D) = cn_F D /\
  4096 <= cn_F D /\ cn_F D + 512 <= YM05.alloc_ceiling /\ cn_F D mod 32 = 0 /\
  (cn_F D + 512 <= kLowShadowBeg \/ kHighMemBeg <= cn_F D) /\
  cn_sp0 D mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo ly /\ kHighMemBeg <= ly_stk_lo ly /\
  ly_stk_lo ly + 27424 <= cn_sp0 D /\ cn_sp0 D <= 2 ^ 47.

Lemma r5_geo_of_base : forall D fxk ly S Hp W regs mem md k wk,
  @cn_base fx rc SK PA B ARx D fxk ly S Hp W regs mem md k wk -> r5_geo D ly /\ ARx ly S Hp W mem md.
Proof.
intros D fxk ly S Hp W regs mem md k wk (_ & _ & (WS & HJ & _) & HF & _).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_stk HJ) as Hstk.
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & _).
destruct HF as (Hfrs & _ & _ & _ & _).
assert (Hin : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin) as (F0 & F1 & Fapp).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin) as (F32 & _ & _ & _).
destruct (stk_bounds_x SEGS B ARx LAWS ly S Hp W mem md HAR) as [Hkb _].
rewrite EFa in F0, F1, Fapp, F32.
change (fs_frame_bytes CN_CID) with 512 in F1, Fapp.
rewrite r5_stk in Hslo.
split; [|exact HAR].
unfold r5_geo. split; [exact EFa|]. split; [lia|]. split; [lia|]. split; [exact F32|].
split; [unfold in_app in Fapp; destruct Fapp as (_ & [Hl | [Hh _]]); [left; exact Hl | right; exact Hh]|].
rewrite Elo in Hkb |- *. repeat split; lia.
Qed.

Lemma r5_S1 : forall D, cn_sp0 D mod 16 = 0 ->
  (cn_S1 D - cn_sp0 D) mod 16 = 0 /\ cn_sp0 D - 223 <= cn_S1 D <= cn_sp0 D - 192.
Proof.
intros D H16. unfold cn_S1. rewrite r5_land32.
pose proof (Z.mod_pos_bound (cn_sp0 D - 192) 32 ltac:(lia)).
split; [|lia].
replace (cn_sp0 D - 192 - (cn_sp0 D - 192) mod 32 - cn_sp0 D) with ((2 * ((cn_sp0 D - 192) / 32) - cn_sp0 D / 16) * 16).
- apply Z.mod_mul. lia.
- pose proof (Z.div_mod (cn_sp0 D - 192) 32 ltac:(lia)). pose proof (Z.div_mod (cn_sp0 D) 16 ltac:(lia)). lia.
Qed.

(* CA5's writes: F's first 504 bytes (the three structs and the bytes between them; the flag word F + 504 is outside)
   and F's 64 shadow bytes; the memset's own stack window below the realigned sp *)
Definition r5_wall (D : cn_in) (a : Z) : Prop :=
  cn_F D <= a < cn_F D + 504 \/ shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64.
Definition r5_sw (D : cn_in) (a : Z) : Prop := cn_S1 D - ESTACK <= a < cn_S1 D.

Lemma r5_wall_sw : forall D ly a, r5_geo D ly -> r5_wall D a -> ~ r5_sw D a /\ 0 <= a < 2 ^ 64.
Proof.
intros D ly a G Hw. destruct G as (_ & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _].
unfold r5_wall, r5_sw, shadow_addr in *. r5_consts. lia.
Qed.

(* the own byte is a program static: an image byte, below the shadow and the stack *)
Lemma r5_own_pst : Exists (in_zr (VAL (A_OBJ 13))) prh_pst.
Proof.
rewrite (cni_own B IMG). unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. change (Z.of_nat pi_gz_own_ran_out) with 1. lia.
Qed.
Lemma r5_own_img : in_img SEGS (VAL (A_OBJ 13)) /\ 0 <= VAL (A_OBJ 13) < kLowMemEnd.
Proof.
destruct (cni_pst_ok B IMG _ r5_own_pst) as [Hi _]. split; [exact Hi | exact (@pa_segs_low _ _ PA _ Hi)].
Qed.

Lemma r5_cell_img : forall a w q, (forall kk, (kk < w)%nat -> Exists (in_zr (a + Z.of_nat kk)) prh_pst) ->
  0 <= q < Z.of_nat w -> in_img SEGS (a + q).
Proof. intros a w q H Hq. replace q with (Z.of_nat (Z.to_nat q)) by lia. exact (proj1 (cni_pst_ok B IMG _ (H (Z.to_nat q) ltac:(lia)))). Qed.

(* the classes of addresses the exit reads, each off the writes *)
Lemma r5_cls_stack : forall D ly a, r5_geo D ly -> cn_S1 D <= a < 2 ^ 47 ->
  ~ r5_wall D a /\ ~ r5_sw D a /\ a <> VAL (A_OBJ 13).
Proof.
intros D ly a G Ha. pose proof G as (_ & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _]. pose proof r5_own_img as [_ Ho].
unfold r5_wall, r5_sw, shadow_addr in *. r5_consts. lia.
Qed.

Lemma r5_cls_img : forall D ly S Hp W mem md a, r5_geo D ly -> ARx ly S Hp W mem md ->
  In (CN_CID, ci_fpos D) (frames S) -> in_img SEGS a -> ~ r5_wall D a /\ ~ r5_sw D a.
Proof.
intros D ly S Hp W mem md a G HAR Hin Hi. pose proof G as (EFa & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow.
pose proof (frm_img_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) a HAR Hin) as Hf.
rewrite EFa in Hf. change (fs_frame_bytes CN_CID) with 512 in Hf.
split.
- intros [Hw | Hw]; [exact (Hf ltac:(lia) Hi)|]. unfold shadow_addr in Hw. r5_consts. lia.
- unfold r5_sw. r5_consts. lia.
Qed.

(* the ledger's g_own_ran_out cell (prh_own) across CA5's writes: an image byte (S1Ledger.v prh_pst_own), off F's
   first 504 bytes, F's shadow and the memset window (YCbq.v val_mem_kept over r5_cls_img) *)
Lemma r5_own_kept : forall D ly S Hp W mem md (m0 m1 : word -> option byte) own,
  r5_geo D ly -> ARx ly S Hp W mem md -> In (CN_CID, ci_fpos D) (frames S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ r5_wall D a -> ~ r5_sw D a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
  prh_own W m0 own -> prh_own W m1 own.
Proof.
intros D ly S Hp W mem md m0 m1 own G HAR Hin HK (Ho & Ho01).
assert (KI : forall a, in_img SEGS a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a).
{ intros a Hi. destruct (r5_cls_img D ly S Hp W mem md a G HAR Hin Hi) as [H1 H2].
  pose proof (@pa_segs_low _ _ PA _ Hi). apply HK; [r5_consts; lia | exact H1 | exact H2]. }
split; [|exact Ho01].
apply (val_mem_kept SEGS (w_H W) (w_H W) m0 m1); [|exact Ho].
intros q Hq. apply KI. exact (r5_cell_img _ _ q prh_pst_own Hq).
Qed.

Lemma r5_cls_blk : forall D ly S Hp W mem md p n a, r5_geo D ly -> ARx ly S Hp W mem md ->
  In (CN_CID, ci_fpos D) (frames S) -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ r5_wall D a /\ ~ r5_sw D a /\ a <> VAL (A_OBJ 13) /\ ~ (cn_F D <= a < cn_F D + 512) /\ a < YM05.alloc_ceiling.
Proof.
intros D ly S Hp W mem md p n a G HAR Hin Hb Ha. pose proof G as (EFa & F0 & F1 & F32 & _ & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md p n CN_CID (ci_fpos D) HAR Hb Hin) as Hd.
rewrite EFa in Hd. change (fs_frame_bytes CN_CID) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hb) as (_ & H4096 & Hce & Happ & _).
pose proof (in_app_addr p (req_size n) a Happ Ha) as Hap.
pose proof (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n a HAR Hb Ha) as Hni.
pose proof r5_own_img as [Hoi _].
split; [|split; [|split; [|split]]].
- intros [Hw | Hw]; [lia|]. unfold app_addr, ASAN_CEIL, shadow_addr in *. r5_consts. lia.
- unfold r5_sw. r5_consts. lia.
- intros ->. exact (Hni Hoi).
- lia.
- lia.
Qed.

(* the shadow byte of an address off F is not one of F's shadow bytes (F is 8-aligned) *)
Lemma r5_sh_off : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 512) ->
  ~ (shadow_addr F <= shadow_addr x < shadow_addr F + 64).
Proof. intros F x HF Hx Hs. unfold shadow_addr in Hs. lia. Qed.

Lemma r5_cls_sh : forall D ly x, r5_geo D ly -> 0 <= x < YM05.alloc_ceiling -> ~ (cn_F D <= x < cn_F D + 512) ->
  ~ r5_wall D (shadow_addr x) /\ ~ r5_sw D (shadow_addr x) /\ shadow_addr x <> VAL (A_OBJ 13) /\
  0 <= shadow_addr x < 2 ^ 64.
Proof.
intros D ly x G Hx Hxf. pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [_ HS1]. pose proof alloc_ceiling_val as [AC _]. pose proof r5_own_img as [_ Ho].
pose proof (r5_sh_off (cn_F D) x ltac:(lia) Hxf) as Hso.
split; [|split; [|split]].
- intros [Hw | Hw]; [|exact (Hso Hw)]. unfold shadow_addr in *. r5_consts. lia.
- unfold r5_sw, shadow_addr in *. r5_consts. lia.
- unfold shadow_addr in *. r5_consts. lia.
- unfold shadow_addr in *. r5_consts. lia.
Qed.

(* ---- the invariant carried from the cut (memory mem0) through CA5: the journal, P, every byte off the writes kept,
   the visible memory grows, and the bytes written so far (Done, inside the writes) read 0 ---- *)
Definition r5_inv (P : (word -> option byte) -> Prop) (D : cn_in) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world SEGS) (mem0 : word -> option byte) (k : Z) (Done : Z -> Prop) (memi : word -> option byte) (mdi : Model)
  : Prop :=
  CNJ D ly S Hp W memi mdi k /\ P memi /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ r5_wall D a -> ~ r5_sw D a ->
     aview SEGS (w_H W) memi a = aview SEGS (w_H W) mem0 a) /\
  mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) memi) /\
  (forall a, Done a -> r5_wall D a /\ aview SEGS (w_H W) memi a = Some 0).

Lemma r5_inv_md : forall P D ly S Hp W mem0 k Done memi mdi mdi',
  r5_inv P D ly S Hp W mem0 k Done memi mdi -> same_but_materialized mdi mdi' ->
  r5_inv P D ly S Hp W mem0 k Done memi mdi'.
Proof.
intros P D ly S Hp W mem0 k Done memi mdi mdi' (HJ & HR) Hs. split; [|exact HR].
rewrite (same_but_materialized_wvb _ _ Hs). unfold r5_J in *.
exact (ajournal_x_materialize SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

Lemma r5_inv_init : forall P D ly S Hp W mem md k, CNJ D ly S Hp W mem md k -> P mem ->
  r5_inv P D ly S Hp W mem k (fun _ => False) mem md.
Proof.
intros P D ly S Hp W mem md k HJ HP. split; [exact HJ|]. split; [exact HP|]. split; [intros; reflexivity|].
split; [intros x Hx; exact Hx | intros a []].
Qed.

(* seven `sb zero, j..j+6(s2)`: F's shadow bytes s2 + j .. s2 + j + 6 now 0 *)
Lemma r5_sb7 : forall (fz : YK11.FPState) P, srr_inv_laws SEGS P ->
  forall D ly S Hp W mem0 k Done regs memi mdi Q kpc j,
  r5_geo D ly -> 0 <= j -> j + 7 <= 64 ->
  (forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 -> apresent (w_H W) mem0 a) ->
  getr regs 18%bv = w64 (shadow_addr (cn_F D)) ->
  r5_sb_slots kpc j 7 = true -> 0 <= kpc -> kpc + 28 < 2 ^ 40 ->
  r5_inv P D ly S Hp W mem0 k Done memi mdi ->
  (forall memo mdo,
     r5_inv P D ly S Hp W mem0 k
       (fun a => Done a \/ shadow_addr (cn_F D) + j <= a < shadow_addr (cn_F D) + j + 7) memo mdo ->
     SRr SEGS W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (BASE + (kpc + 28))) memo (YK11.seg_rom SEGS)) mdo) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 (BASE + kpc)) memi (YK11.seg_rom SEGS)) mdi) Q.
Proof.
intros fz P PLAW D ly S Hp W mem0 k Done regs memi mdi Q kpc j G Hj0 Hj7 Hshp Hs2 Hsl Hk0 Hk28 (HJ & HPm & HK & HG & HZ) HKont.
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
pose proof alloc_ceiling_val as [AC _].
assert (Hs2r : 0 <= shadow_addr (cn_F D) /\ shadow_addr (cn_F D) + 64 <= 2 ^ 47) by (unfold shadow_addr; r5_consts; lia).
apply (h_sbn (fz := fz) P PLAW 7 W regs memi mdi Q kpc j (shadow_addr (cn_F D)) Hs2 ltac:(lia) Hk0 ltac:(cbn; lia)
  ltac:(lia) ltac:(cbn; lia) Hsl).
- intros i Hi. apply (r5_apr_grows _ mem0 memi _ HG). apply Hshp. cbn in Hi. lia.
- exact HPm.
- intros mdo memo Hsame Hfr Hgr Hhid Hz HPo. change (kpc + 4 * Z.of_nat 7) with (kpc + 28). cbn [Z.of_nat Pos.of_succ_nat] in Hfr, Hz.
  apply HKont. split; [|split; [exact HPo|]; split; [|split]].
  + unfold r5_J in *.
    apply (ajournal_x_exec SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun a => shadow_addr (cn_F D) + j <= a < shadow_addr (cn_F D) + j + 7) HJ Hfr Hgr Hhid Hsame).
    intros a Ha. right; right; right. exists CN_CID, (ci_fpos D). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes CN_CID / 8) with 64. lia.
  + intros a Ha Hw Hs. rewrite <- (HK a Ha Hw Hs). apply aview_eq_of. apply Hfr.
    rewrite unsigned_lit_small by exact Ha. intros Hx. apply Hw. right. lia.
  + exact (r5_grows_trans _ _ _ HG Hgr).
  + intros a [Hd | Hd].
    * destruct (HZ a Hd) as [Hwa Ha0]. split; [exact Hwa|]. destruct (r5_wall_sw D ly a G Hwa) as [_ Hab].
      destruct (Z_lt_le_dec a (shadow_addr (cn_F D) + j)) as [Hlt|Hge];
        [| destruct (Z_lt_le_dec a (shadow_addr (cn_F D) + j + 7)) as [Hlt2|Hge2]].
      -- rewrite <- Ha0. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by exact Hab. lia.
      -- replace a with (shadow_addr (cn_F D) + j + (a - (shadow_addr (cn_F D) + j))) by lia. apply Hz. lia.
      -- rewrite <- Ha0. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by exact Hab. lia.
    * split; [unfold r5_wall; right; lia|].
      replace a with (shadow_addr (cn_F D) + j + (a - (shadow_addr (cn_F D) + j))) by lia. apply Hz. lia.
Qed.

(* the shadow of a struct's bytes: F 8-aligned, the struct at F + off (off a multiple of 8) *)
Lemma r5_sh_struct : forall F off x, F mod 8 = 0 -> off mod 8 = 0 -> F + off <= x < F + off + 56 ->
  shadow_of_addr SHADOW_OFF x = shadow_addr F + off / 8 + (x - (F + off)) / 8 /\ 0 <= (x - (F + off)) / 8 < 7.
Proof. intros F off x HF Ho Hx. unfold shadow_of_addr, shadow_addr. split; lia. Qed.

(* one zeroing memset of a struct (d = F + off, 56 bytes), its shadow already zero *)
Lemma r5_memset : forall (fz : YK11.FPState) P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D ly S Hp W mem0 k Done regsT memT mdT Q kret off,
  r5_geo D ly -> (off = 32 \/ off = 128 \/ off = 224) ->
  (forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 -> apresent (w_H W) mem0 a) ->
  (forall i, 0 <= i < 7 -> Done (shadow_addr (cn_F D) + off / 8 + i)) ->
  getr regsT 10%bv = w64 (cn_F D + off) -> getr regsT 11%bv = w64 0 -> getr regsT 12%bv = w64 56 ->
  getr regsT 2%bv = w64 (cn_S1 D) -> getr regsT 3%bv = w64 (as_gp B) -> getr regsT 4%bv = w64 (as_tp B) ->
  getr regsT 1%bv = Z_to_bv 64 (BASE + kret) -> 0 <= kret < 2 ^ 40 -> kret mod 2 = 0 ->
  r5_inv P D ly S Hp W mem0 k Done memT mdT ->
  (forall regs2 mem2 md2, aregs_preserved regsT regs2 ->
     r5_inv P D ly S Hp W mem0 k (fun a => Done a \/ cn_F D + off <= a < cn_F D + off + 56) mem2 md2 ->
     SRr SEGS W (mkCfg (@YK11.mkst fz regs2 (Z_to_bv 64 (BASE + kret)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fz regsT (Z_to_bv 64 (SIGMA AS___asan_memset)) memT (YK11.seg_rom SEGS)) mdT) Q.
Proof.
intros fz P PLAW PCALL D ly S Hp W mem0 k Done regsT memT mdT Q kret off G Hoff Hshp HDn R10 R11 R12 R2 R3 R4 R1 Hkr Hkr2
  (HJ & HPm & HK & HG & HZ) HKont.
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
pose proof alloc_ceiling_val as [AC _].
destruct (r5_S1 D S16) as [HS16 HS1].
assert (Ho8 : off mod 8 = 0) by (destruct Hoff as [-> | [-> | ->]]; reflexivity).
assert (Hoff' : 32 <= off <= 224) by (destruct Hoff as [-> | [-> | ->]]; lia).
unfold r5_J in HJ.
eapply SRr_bind.
{ apply (@aj_intrin_at_xm fz rc SK SEGS B prh_pst ARx cf_head LAWS (@pa_segs_low _ _ PA) OSet (SIGMA AS___asan_memset)
    (MEMSET fz) W regsT memT STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D)
    (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp mdT k (cn_F D + off) 0 56 (cn_S1 D - cn_sp0 D) (Z_to_bv 64 (BASE + kret))
    HJ R10 R11 R12); [lia | lia | lia | | exact HS16 | lia | | exact R3 | exact R4 | exact R1 | | | | | | exact I].
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - unfold ESTACK. rewrite r5_stk. lia.
  - apply (@ret_ok_codeptr_v rc A_prog_listing PA); [lia | exact Hkr2].
  - intros a Ha. split.
    + right; right; right. exists CN_CID, (ci_fpos D). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite EFa. change (fs_frame_bytes CN_CID) with 512. lia.
    + unfold ESTACK. lia.
  - unfold amem_range. destruct Fapp as [Fl | Fh]; [left | right]; r5_consts; lia.
  - intros x Hx. exists 0. split; [| left; reflexivity].
    destruct (r5_sh_struct (cn_F D) off x ltac:(lia) Ho8 Hx) as [Ex Hi]. rewrite Ex.
    exact (proj2 (HZ _ (HDn _ Hi))).
  - intros _ s Hs. apply (r5_aview_vis SEGS _ mem0 memT s HG). apply r5_apr_aview. apply Hshp.
    clear - Hs F32 Hoff'. unfold shadow_addr, SHADOW_OFF in *. lia. }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Hset & Hfr & Hpres & Hmn).
apply (HKont regs2 mem2 md2 HP2).
split; [unfold r5_J; exact HJ2|]. split; [exact (PCALL _ _ Hmn HPm)|]. split; [|split].
- intros a Ha Hw Hs. rewrite Hfr; [exact (HK a Ha Hw Hs) | exact Ha | |].
  + intros Hd. apply Hw. left. lia.
  + intros Hd. apply Hs. unfold r5_sw. lia.
- exact (r5_grows_trans _ _ _ HG (r5_grows_of_apr _ _ _ Hpres)).
- intros a [Hd | Hd].
  + destruct (HZ a Hd) as [Hwa Ha0]. split; [exact Hwa|]. destruct (r5_wall_sw D ly a G Hwa) as [Hns Hab].
    destruct (Z_lt_le_dec a (cn_F D + off)) as [Hl|Hge]; [|destruct (Z_lt_le_dec a (cn_F D + off + 56)) as [Hl2|Hge2]].
    * rewrite Hfr; [exact Ha0 | exact Hab | lia | intros Hx; apply Hns; unfold r5_sw; lia].
    * replace a with (cn_F D + off + (a - (cn_F D + off))) by lia. rewrite Hset by lia. reflexivity.
    * rewrite Hfr; [exact Ha0 | exact Hab | lia | intros Hx; apply Hns; unfold r5_sw; lia].
  + split; [unfold r5_wall; left; lia|]. replace a with (cn_F D + off + (a - (cn_F D + off))) by lia.
    rewrite Hset by lia. reflexivity.
Qed.

(* ---- THE EXIT FACTS from the cut's: the exit memory memE keeps every byte off the writes, off the stack window and
   off X (the own byte on the 3rd-NULL arm); the structs' shadow bytes and the structs' bytes read 0; the exit's
   ledger holds the cut's statics but the own cell, which holds the exit's own' (prh_own at memE); the exit's journal
   is the plain one, so cn_base holds at any wild budget wk (cn_J_of_x) ---- *)
Lemma r5_exit : forall D fxk ly S Hp W regs mem md k memE mdE regsE (X : Z -> Prop) (Done : Z -> Prop) r1 r2 r3 nr
  own own' wk,
  @cn_base fx rc SK PA B ARx D fxk ly S Hp W regs mem md k 0 ->
  cn_slots D W mem r1 r2 ->
  @cn_copy rc PA B D ly S Hp W mem r1 -> @cn_copy rc PA B D ly S Hp W mem r2 -> @cn_copy rc PA B D ly S Hp W mem r3 ->
  prh_ledger B ly S Hp W mem (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own ->
  prh_own W memE own' ->
  Permutation (ablocks B ly S) (cn_cblks D r1 r2 r3 ++ ablocks B (ci_ly D) (ci_S D)) ->
  room_live_cf S ->
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (ci_x D) <= LIVE_MAX ->
  (nr <= 3)%nat ->
  (forall a, X a -> a = VAL (A_OBJ 13)) ->
  CNJ D ly S Hp W memE mdE k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ r5_wall D a -> ~ r5_sw D a -> ~ X a ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memE) ->
  (forall a, Done a -> aview SEGS (w_H W) memE a = Some 0) ->
  (forall off i, (off = 32 \/ off = 128 \/ off = 224) -> 0 <= i < 7 -> Done (shadow_addr (cn_F D) + off / 8 + i)) ->
  (forall off i, (off = 32 \/ off = 128 \/ off = 224) -> 0 <= i < 56 -> Done (cn_F D + off + i)) ->
  getr regsE 3%bv = getr regs 3%bv -> getr regsE 4%bv = getr regs 4%bv ->
  @cn_base fx rc SK PA B ARx D fxk ly S Hp W regsE memE mdE k wk /\ cn_slots D W memE r1 r2 /\
  @cn_mid rc cp RL PA B D ly S Hp W memE (ci_Lam D) (ci_peak D) (ci_cnt D) (ci_ran D) own' nr r1 r2 r3 None None None.
Proof.
intros D fxk ly S Hp W regs mem md k memE mdE regsE X Done r1 r2 r3 nr own own' wk HB HSL HC1 HC2 HC3 HLG HOE HPERM
  HROOM HLIVE Hnr HX HJE KK GR HZ HDs HDz G3 G4.
destruct (r5_geo_of_base D fxk ly S Hp W regs mem md k 0 HB) as [G HAR].
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3c & G4c & HRO).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
change (fs_frame_bytes CN_CID / 8) with 64 in Hshp. change (fs_frame_bytes CN_CID) with 512 in Hflag, Hfpr.
assert (Hin : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [HS16 HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof r5_own_img as [Hoi Hol].
assert (HXo : forall a, a <> VAL (A_OBJ 13) -> ~ X a) by (intros a Hne Hx; exact (Hne (HX a Hx))).
(* a stack byte at or above the realigned sp *)
assert (KS : forall a, cn_S1 D <= a < 2 ^ 47 -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (r5_cls_stack D ly a G Ha) as (H1 & H2 & H3). apply KK; [lia | exact H1 | exact H2 | exact (HXo a H3)]. }
(* an image byte other than the own byte *)
assert (KI : forall a, in_img SEGS a -> a <> VAL (A_OBJ 13) -> aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
{ intros a Hi Hne. destruct (r5_cls_img D ly S Hp W mem md a G HAR Hin Hi) as [H1 H2].
  pose proof (@pa_segs_low _ _ PA _ Hi). apply KK; [r5_consts; lia | exact H1 | exact H2 | exact (HXo a Hne)]. }
(* a byte of a live block *)
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem a).
{ intros p n a Hb Ha. destruct (r5_cls_blk D ly S Hp W mem md p n a G HAR Hin Hb Ha) as (H1 & H2 & H3 & _ & H5).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hb) as (_ & H4096 & _).
  apply KK; [lia | exact H1 | exact H2 | exact (HXo a H3)]. }
(* the shadow byte of a live block's byte *)
assert (KH : forall p n x, In (p, n) (ablocks B ly S) -> p <= x < p + req_size n ->
  aview SEGS (w_H W) memE (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
{ intros p n x Hb Hx. destruct (r5_cls_blk D ly S Hp W mem md p n x G HAR Hin Hb Hx) as (_ & _ & _ & H4 & H5).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hb) as (_ & H4096 & _).
  destruct (r5_cls_sh D ly x G ltac:(lia) H4) as (S1' & S2' & S3' & S4').
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply KK; [exact S4' | exact S1' | exact S2' | exact (HXo _ S3')]. }
(* a struct is open: its shadow bytes 0, its shadow hull visible *)
assert (KO : forall off, (off = 32 \/ off = 128 \/ off = 224) -> cn_open W memE (cn_F D + off)).
{ intros off Hoff. assert (Ho8 : off mod 8 = 0) by (destruct Hoff as [-> | [-> | ->]]; reflexivity).
  assert (Hoff' : 32 <= off <= 224) by (destruct Hoff as [-> | [-> | ->]]; lia).
  split.
  - intros x Hx. exists 0. split; [| left; reflexivity].
    destruct (r5_sh_struct (cn_F D) off x ltac:(lia) Ho8 Hx) as [Ex Hi]. rewrite Ex. apply HZ. apply HDs; [exact Hoff | exact Hi].
  - intros s Hs. apply (r5_aview_vis SEGS _ mem memE s GR). apply r5_apr_aview. apply Hshp.
    clear - Hs F32 Hoff'. unfold shadow_addr, SHADOW_OFF in *. lia. }
(* a struct is the zero struct *)
assert (KZ : forall off, (off = 32 \/ off = 128 \/ off = 224) -> pj_zeroR SEGS (mrestrict (w_H W) memE) (cn_F D + off)).
{ intros off Hoff j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
  apply r5_val_mem1_of_aview; [| lia]. apply HZ. apply HDz; [exact Hoff | lia]. }
(* a padded copy is kept *)
assert (KC : forall r, @cn_copy rc PA B D ly S Hp W mem r -> @cn_copy rc PA B D ly S Hp W memE r).
{ intros r [-> | (Hb & Hnh & (Hby & H4096 & Hce & Hamr & Hra & Hhull))]; [left; reflexivity|].
  right. split; [exact Hb|]. split; [exact Hnh|].
  pose proof (proj1 (req_size_pos (cn_size D + 16) ltac:(unfold cn_size; lia))) as Hrq.
  pose proof (proj2 (req_size_pos (cn_size D + 16) ltac:(unfold cn_size; lia))) as Hrq2.
  split; [|split; [exact H4096|]; split; [exact Hce|]; split; [exact Hamr|]; split].
  - intros j Hj. destruct (Hby j Hj) as [Hv Hbd]. split; [|exact Hbd].
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact Hv].
    intros q Hq. apply (KB r (cn_size D + 16)); [exact Hb |]. unfold cn_size in *. lia.
  - apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hra].
    intros x Hx. apply (KH r (cn_size D + 16)); [exact Hb |]. unfold cn_size in *. lia.
  - intros Hl s Hs. apply (r5_aview_vis SEGS _ mem memE s GR). exact (Hhull Hl s Hs). }
split; [|split].
(* ---- cn_base at the exit ---- *)
- split; [exact Hfz|]. split; [exact Hfk|]. split; [apply cn_J_of_x; exact HJE|]. split; [|split; [|split; [|split]]].
  + split; [exact Hfrs|]. split; [exact Hnin|]. split; [|split].
    * change (fs_frame_bytes CN_CID) with 512. rewrite <- Hflag. apply rdword_ext. intros q Hq.
      pose proof (frm_img_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) (VAL (A_OBJ 13)) HAR Hin) as Hfo.
      rewrite EFa in Hfo. change (fs_frame_bytes CN_CID) with 512 in Hfo.
      apply KK.
      -- lia.
      -- unfold r5_wall, shadow_addr. r5_consts. lia.
      -- unfold r5_sw. unfold ESTACK. lia.
      -- apply HXo. intros E. apply Hfo; [lia | exact Hoi].
    * intros a Ha. apply (r5_apr_grows _ mem memE _ GR). apply Hfpr. exact Ha.
    * intros a Ha. apply (r5_apr_grows _ mem memE _ GR). apply Hshp. change (fs_frame_bytes CN_CID / 8) with 64 in Ha. exact Ha.
  + unfold cn_saved in *.
    repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSV as [H HSV]; apply Forall_cons;
      [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq; apply KS; lia |]).
    apply Forall_nil.
  + rewrite G3. exact G3c.
  + rewrite G4. exact G4c.
  + intros a Hro Hno Herr. rewrite KI; [exact (HRO a Hro Hno Herr) | |].
    * destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)].
    * intros ->. exact (cni_pst_rw B IMG _ r5_own_pst Hro).
(* ---- the slots ---- *)
- unfold cn_slots in *.
  repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSL as [H HSL]; apply Forall_cons;
    [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq; apply KS; lia |]).
  apply Forall_nil.
(* ---- the state facts ---- *)
- split; [exact (KC r1 HC1)|]. split; [exact (KC r2 HC2)|]. split; [exact (KC r3 HC3)|].
  split.
  { (* the statics at memE: g_live .. g_ran_out and g_most are image bytes off the writes and off the own byte, so
       kept; the own cell holds own' (HOE); Lam's heads are block bytes off the writes (S1Ledger.v prh_lblocks_kept) *)
    pose proof (prh_ledger_bounds B ly S Hp W mem _ _ _ _ _ _ _ HLG) as (Bl & Bp & Bc & Bf & Br).
    assert (Gl : val_mem SEGS (mrestrict (w_H W) memE) pi_g_live pi_gz_live (Ledger.lsum (ci_Lam D))).
    { apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact (prh_ledger_live B ly S Hp W mem _ _ _ _ _ _ _ HLG)].
      intros q Hq. apply KI; [exact (r5_cell_img _ _ q prh_pst_live Hq) |].
      change (Z.of_nat pi_gz_live) with 8 in Hq.
      rewrite (cni_own B IMG). change pi_g_live with 6149472. change pi_g_own_ran_out with 6149440. lia. }
    assert (Gp : val_mem SEGS (mrestrict (w_H W) memE) pi_g_peak pi_gz_peak (ci_peak D)).
    { apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact (prh_ledger_peak B ly S Hp W mem _ _ _ _ _ _ _ HLG)].
      intros q Hq. apply KI; [exact (r5_cell_img _ _ q prh_pst_peak Hq) |].
      change (Z.of_nat pi_gz_peak) with 8 in Hq.
      rewrite (cni_own B IMG). change pi_g_peak with 6149504. change pi_g_own_ran_out with 6149440. lia. }
    assert (Gc : val_mem SEGS (mrestrict (w_H W) memE) pi_g_count pi_gz_count (ci_cnt D)).
    { apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact (prh_ledger_count B ly S Hp W mem _ _ _ _ _ _ _ HLG)].
      intros q Hq. apply KI; [exact (r5_cell_img _ _ q prh_pst_count Hq) |].
      change (Z.of_nat pi_gz_count) with 8 in Hq.
      rewrite (cni_own B IMG). change pi_g_count with 6149536. change pi_g_own_ran_out with 6149440. lia. }
    assert (Gf : val_mem SEGS (mrestrict (w_H W) memE) pi_g_fail pi_gz_fail SIZE_MAXZ).
    { apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact (prh_ledger_fail B ly S Hp W mem _ _ _ _ _ _ _ HLG)].
      intros q Hq. apply KI; [exact (r5_cell_img _ _ q prh_pst_fail Hq) |].
      change (Z.of_nat pi_gz_fail) with 8 in Hq.
      rewrite (cni_own B IMG). change pi_g_fail with 681408. change pi_g_own_ran_out with 6149440. lia. }
    assert (Gr : val_mem SEGS (mrestrict (w_H W) memE) pi_g_ran_out pi_gz_ran_out (ci_ran D)).
    { apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact (prh_ledger_ran B ly S Hp W mem _ _ _ _ _ _ _ HLG)].
      intros q Hq. apply KI; [exact (r5_cell_img _ _ q prh_pst_ran Hq) |].
      change (Z.of_nat pi_gz_ran_out) with 1 in Hq.
      rewrite (cni_own B IMG). change pi_g_ran_out with 6149568. change pi_g_own_ran_out with 6149440. lia. }
    assert (Gm : prh_most W memE (ci_most D)).
    { destruct (prh_ledger_most B ly S Hp W mem _ _ _ _ _ _ _ HLG) as (Hm & Hmb). split; [|exact Hmb].
      apply (val_mem_kept SEGS (w_H W) (w_H W) mem memE); [|exact Hm].
      intros q Hq. apply KI; [exact (r5_cell_img _ _ q prh_pst_most Hq) |].
      change (Z.of_nat pi_gz_most) with 8 in Hq.
      rewrite (cni_own B IMG). change pi_g_most with 681440. change pi_g_own_ran_out with 6149440. lia. }
    apply (proj2 (prh_ledger_iff B ly S Hp W memE (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) own')).
    split.
    - clear - Gl Gp Gc Gf Gr Gm HOE Bl Bp Bc Bf Br. destruct Gm as (Gm & Gm'). destruct HOE as (Go & Go').
      unfold prh_glob, prh_most, prh_own. repeat split; try assumption; lia.
    - apply (prh_lblocks_kept B ly S Hp W mem ly S Hp W memE (ci_Lam D)).
      + exact (proj2 (proj1 (prh_ledger_iff B ly S Hp W mem _ _ _ _ _ _ _) HLG)).
      + intros a kk i Hin' Hi. apply prh_mbyte_of_aview.
        destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hin') as (Hk0 & Hblk & _).
        pose proof cf_head_nonneg. unfold prh_head_wide in HW.
        apply (KB (a - cf_head) (kk + cf_head)); [exact Hblk|]. unfold req_size.
        destruct (kk + cf_head =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
      + intros a kk _ Hb. exact Hb.
      + apply Permutation_refl. }
  split; [lia|].
  split; [split; [lia|]; assert (0 <= Z.of_nat nr * ck_ncalls (ci_x D)) by (apply Z.mul_nonneg_nonneg; unfold ck_ncalls; lia); lia|].
  split; [exact HROOM|].
  split.
  { assert (HL0 : 0 <= PRH_FnPj.LIVE_pj_parse (ci_x D)).
    { unfold PRH_FnPj.LIVE_pj_parse.
      assert (0 <= hpeakR (PRH_FnPj.prhPj_ptrace (ci_x D))) by (destruct (PRH_FnPj.prhPj_ptrace (ci_x D)); cbn; lia).
      pose proof cf_head_nonneg.
      assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (PRH_FnPj.prhPj_ptrace (ci_x D))) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
    destruct nr as [|[|[|[|nr]]]]; cbn [Nat.sub Z.of_nat]; lia. }
  split; [exact (KO 32 ltac:(left; reflexivity))|]. split; [exact (KO 128 ltac:(right; left; reflexivity))|].
  split; [exact (KO 224 ltac:(right; right; reflexivity))|].
  split; [exact (KZ 32 ltac:(left; reflexivity))|]. split; [exact (KZ 128 ltac:(right; left; reflexivity))|].
  split; [exact (KZ 224 ltac:(right; right; reflexivity))|].
  split; [cbn [cn_Dof app]; apply Permutation_refl|].
  split; [cbn [cn_Dof app ck_hblks map]; exact HPERM|].
  intros a kk Hin'. cbn [cn_Dof app] in Hin'. destruct Hin'.
Qed.


(* ======== 4. THE TWO SEGMENTS ======== *)
#[local] Notation INV := r5_inv.

(* the own byte (a program static) is visible and writable in every memory: a segment byte (cni_pst_seg) of a
   writable segment (cni_pst_rw), so the world hides it not (w_Hoff) and wview falls back to the segment's byte *)
Lemma r5_own_wr : forall (W : world SEGS) (m : word -> option byte),
  w_H W (Z_to_bv 64 (VAL (A_OBJ 13))) = false /\ writable_at SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 13)).
Proof.
intros W m. set (x := Z_to_bv 64 (VAL (A_OBJ 13))).
pose proof (cni_pst_seg B IMG _ r5_own_pst) as Hseg. fold x in Hseg.
unfold YK11.seg_rom, memory_read in Hseg.
destruct (find_segment SEGS (bv_unsigned x) (Z.of_N 1)) as [sg|] eqn:Hf; [|exfalso; apply Hseg; reflexivity].
change (Z.of_N 1) with 1 in Hf.
assert (Hh : w_H W x = false).
{ destruct (w_H W x) eqn:Eh; [|reflexivity]. pose proof (w_Hoff W x Eh) as Hn. rewrite Hn in Hf. discriminate. }
split; [exact Hh|].
unfold writable_at, wview, mrestrict. fold x. rewrite Hh.
destruct (m x) as [b|]; [discriminate|]. rewrite Hf.
destruct (seg_writable sg) eqn:Ew.
- destruct (seg_readable sg); [|exfalso; apply Hseg; reflexivity].
  change (N.to_nat 1) with 1%nat in Hseg. cbn [segment_read_bytes] in Hseg.
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))) as [b|] eqn:Eb;
    [discriminate | exfalso; apply Hseg; reflexivity].
- exfalso. apply (cni_pst_rw B IMG _ r5_own_pst). left. destruct (find_segment_hit _ _ _ _ Hf) as (Hin & Hlo & Hhi).
  exists sg. split; [exact Hin|]. split; [exact Ew|].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)). unfold x in Hlo, Hhi. rewrite unsigned_lit_small in Hlo, Hhi by lia. lia.
Qed.

(* a stack word at or above the realigned sp, through the invariant *)
Lemma r5_rd_stack : forall P D ly S Hp W mem0 k Done memi mdi a v,
  r5_geo D ly -> cn_S1 D <= a -> a + 8 <= 2 ^ 47 -> rdword (aview SEGS (w_H W) mem0) a = Some v ->
  INV P D ly S Hp W mem0 k Done memi mdi -> rdword (aview SEGS (w_H W) memi) a = Some v.
Proof.
intros P D ly S Hp W mem0 k Done memi mdi a v G Ha Ha8 Hr (_ & _ & HK & _). rewrite <- Hr. apply rdword_ext.
intros q Hq. pose proof G as (_ & _ & _ & _ & _ & S16 & Hac & _ & Hlo & _). destruct (r5_S1 D S16) as [_ HS1].
pose proof alloc_ceiling_val as [AC _].
destruct (r5_cls_stack D ly (a + q) G ltac:(lia)) as (H1 & H2 & _). apply HK; [lia | exact H1 | exact H2].
Qed.

Ltac r5_slot_ok := vm_compute; reflexivity.
Ltac inv_done H := lazymatch type of H with r5_inv _ _ _ _ _ _ _ _ ?d _ _ => d end.
Ltac r5_rs' := repeat first [rewrite v_addi_0 | progress r5_rs].

Theorem cn_init_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  @cn_pre fx rc ci cp RL PA B ARx CTX0 D ->
  @cn_at_init fx rc cp RL SK PA B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 ->
  P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_INIT) regs mem md)
    (fun W' c' => @cn_ex_read1 fx rc cp RL SK PA B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 r3 own0 HPRE HAT HPM.
pose proof HAT as (HB & HR & HSL & HC1 & HC2 & HC3 & Hr3 & Hown & Hownv & Hown0 & Hcd & HHp & HLG & HPERM & HROOM & HRP
  & HLIVE & HHB).
destruct (r5_geo_of_base D fxk ly S Hp W regs mem md k 0 HB) as [G HAR].
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3 & G4 & HRO).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
change (fs_frame_bytes CN_CID / 8) with 64 in Hshp.
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [HS16 HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (cn_pre_fpre B ARx CTX0 D HPRE) as HFP. destruct HFP as (HAF & _).
destruct HAF as (_ & _ & _ & Hgp & Htp & _).
assert (R3 : getr regs 3%bv = w64 (as_gp B)) by (rewrite G3; exact Hgp).
assert (R4 : getr regs 4%bv = w64 (as_tp B)) by (rewrite G4; exact Htp).
assert (RG : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D);
  (22%bv, r3); (23%bv, ci_data D); (25%bv, cn_d1 D)]) -> getr regs r = w64 v)
  by (intros r v Hin; exact (proj1 (Forall_forall _ _) HR (r, v) Hin)).
assert (SLT : forall o v, In (o, v) [(24, r1); (32, cn_F D); (40, r2); (48, cn_d2 D); (56, cn_d1 D); (80, cn_F D)] ->
  rdword (aview SEGS (w_H W) mem) (cn_S1 D + o) = Some v)
  by (intros o v Hin; exact (proj1 (Forall_forall _ _) HSL (o, v) Hin)).
Ltac rg RG := apply RG; unfold cn_core, cn_s8; cbn [app In]; r5_in.
Ltac rt RG R3 R4 := r5_rs'; first [exact R3 | exact R4 | rg RG | reflexivity].
unfold cn_cfg, cn_pc. change (w64 (BASE + CN_OFF + CN_INIT)) with (Z_to_bv 64 (BASE + 804 + 608)).
replace (BASE + 804 + 608) with (BASE + 1412) by lia.
(* 608: lbu s10, -1368(s8) (g_own_ran_out) *)
apply (s_lbu W regs mem md _ 1412 1416 26%bv 24%bv (-1368) (VAL (A_OBJ 13)) own0);
  [r5_slot_ok | reflexivity | lia | lia | reflexivity | | exact Hownv | exact Hown |].
{ rewrite (RG 24%bv (VAL (A_HI 9)) ltac:(unfold cn_core, cn_s8; cbn [app In]; r5_in)). unfold v_addi, w64.
  pose proof (@pa_val_range _ _ PA (A_HI 9)). rewrite unsigned_lit_small by lia. rewrite <- (cni_hi9 B IMG). f_equal; lia. }
intros md1 Hs1.
pose proof (r5_inv_md P D ly S Hp W mem k (fun _ => False) mem md md1
  (r5_inv_init P D ly S Hp W mem md k (r5_J_of_cn D ly S Hp W mem md k HJ) HPM) Hs1) as HI1.
(* 612-636: d1's shadow *)
let d := inv_done HI1 in apply (r5_sb7 fxk P PLAW D ly S Hp W mem k d _ mem md1 _ 1416 4 G ltac:(lia) ltac:(lia) Hshp);
  [rt RG R3 R4 | r5_slot_ok | lia | lia | exact HI1 |].
intros mem2 md2 HI2.
(* 640: li a2, 56; 644: ld a0, 56(s1) (d1); 648: mv a1, zero; 652: jal __asan_memset *)
apply (s_addi W _ mem2 md2 _ 1444 1448 12%bv 0%bv 56); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md3 Hs3.
apply (s_ld W _ mem2 md3 _ 1448 1452 10%bv 9%bv 56 (cn_S1 D + 56) (cn_d1 D)); [r5_slot_ok | reflexivity | lia | lia | reflexivity | | lia | lia | |].
{ r5_rs'. rewrite (RG 9%bv (cn_S1 D) ltac:(unfold cn_core, cn_s8; cbn [app In]; r5_in)). unfold v_addi, w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
{ apply (r5_rd_stack P D ly S Hp W mem k _ mem2 md2 (cn_S1 D + 56) (cn_d1 D) G ltac:(lia) ltac:(lia) (SLT 56 (cn_d1 D) ltac:(cbn [In]; r5_in)) HI2). }
intros md4 Hs4.
apply (s_addi W _ mem2 md4 _ 1452 1456 11%bv 0%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md5 Hs5.
apply (h_call W _ mem2 md5 _ 1456 1460 AS___asan_memset); [r5_slot_ok | lia | lia | reflexivity |].
intros md6 Hs6.
pose proof (r5_inv_md P D ly S Hp W mem k _ mem2 md2 md6 HI2
  (same_but_materialized_trans _ _ _ Hs3 (same_but_materialized_trans _ _ _ Hs4
    (same_but_materialized_trans _ _ _ Hs5 Hs6)))) as HI2'.
let d := inv_done HI2' in apply (r5_memset fxk P PLAW PCALL D ly S Hp W mem k d _ mem2 md6 _ 1460 32 G (or_introl eq_refl) Hshp);
  [ intros i Hi; cbv beta; lia | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4
  | rt RG R3 R4 | rt RG R3 R4 | lia | reflexivity | exact HI2' |].
intros regsA memA mdA HPA HIA.
(* 656-680: d2's shadow; 684: li a2; 688: ld s5, 48(s1) (d2); 692: mv a0, s5; 696: mv a1; 700: jal *)
let d := inv_done HIA in apply (r5_sb7 fxk P PLAW D ly S Hp W mem k d _ memA mdA _ 1460 16 G ltac:(lia) ltac:(lia) Hshp);
  [rt RG R3 R4 | r5_slot_ok | lia | lia | exact HIA |].
intros mem3 md7 HI3.
apply (s_addi W _ mem3 md7 _ 1488 1492 12%bv 0%bv 56); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md8 Hs8.
apply (s_ld W _ mem3 md8 _ 1492 1496 21%bv 9%bv 48 (cn_S1 D + 48) (cn_d2 D)); [r5_slot_ok | reflexivity | lia | lia | reflexivity | | lia | lia | |].
{ r5_rs'. rewrite (RG 9%bv (cn_S1 D) ltac:(unfold cn_core, cn_s8; cbn [app In]; r5_in)). unfold v_addi, w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
{ apply (r5_rd_stack P D ly S Hp W mem k _ mem3 md7 (cn_S1 D + 48) (cn_d2 D) G ltac:(lia) ltac:(lia) (SLT 48 (cn_d2 D) ltac:(cbn [In]; r5_in)) HI3). }
intros md9 Hs9.
apply (s_addi W _ mem3 md9 _ 1496 1500 10%bv 21%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md10 Hs10.
apply (s_addi W _ mem3 md10 _ 1500 1504 11%bv 0%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md11 Hs11.
apply (h_call W _ mem3 md11 _ 1504 1508 AS___asan_memset); [r5_slot_ok | lia | lia | reflexivity |].
intros md12 Hs12.
pose proof (r5_inv_md P D ly S Hp W mem k _ mem3 md7 md12 HI3
  (same_but_materialized_trans _ _ _ Hs8 (same_but_materialized_trans _ _ _ Hs9
    (same_but_materialized_trans _ _ _ Hs10 (same_but_materialized_trans _ _ _ Hs11 Hs12))))) as HI3'.
let d := inv_done HI3' in apply (r5_memset fxk P PLAW PCALL D ly S Hp W mem k d _ mem3 md12 _ 1508 128 G (or_intror (or_introl eq_refl)) Hshp);
  [ intros i Hi; cbv beta; lia | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4
  | rt RG R3 R4 | rt RG R3 R4 | lia | reflexivity | exact HI3' |].
intros regsB memB mdB HPB HIB.
(* 704-728: d3's shadow; 732: li a2; 736: mv a0, s3 (d3); 740: mv a1; 744: jal *)
let d := inv_done HIB in apply (r5_sb7 fxk P PLAW D ly S Hp W mem k d _ memB mdB _ 1508 28 G ltac:(lia) ltac:(lia) Hshp);
  [rt RG R3 R4 | r5_slot_ok | lia | lia | exact HIB |].
intros mem4 md13 HI4.
apply (s_addi W _ mem4 md13 _ 1536 1540 12%bv 0%bv 56); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md14 Hs14.
apply (s_addi W _ mem4 md14 _ 1540 1544 10%bv 19%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md15 Hs15.
apply (s_addi W _ mem4 md15 _ 1544 1548 11%bv 0%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md16 Hs16.
apply (h_call W _ mem4 md16 _ 1548 1552 AS___asan_memset); [r5_slot_ok | lia | lia | reflexivity |].
intros md17 Hs17.
pose proof (r5_inv_md P D ly S Hp W mem k _ mem4 md13 md17 HI4
  (same_but_materialized_trans _ _ _ Hs14 (same_but_materialized_trans _ _ _ Hs15
    (same_but_materialized_trans _ _ _ Hs16 Hs17)))) as HI4'.
let d := inv_done HI4' in apply (r5_memset fxk P PLAW PCALL D ly S Hp W mem k d _ mem4 md17 _ 1552 224 G (or_intror (or_intror eq_refl)) Hshp);
  [ intros i Hi; cbv beta; lia | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4
  | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | lia | reflexivity | exact HI4' |].
intros regsC memC mdC HPC HIC.
(* ---- the exit CN_READ1 (748) ---- *)
pose proof HIC as (HJC & HPmC & HKC & HGC & HZC).
(* the ledger's own cell: no step of CA5's first arm writes g_own_ran_out, so the exit's ledger holds own0 *)
assert (HOC : prh_own W memC own0)
  by exact (r5_own_kept D ly S Hp W mem md mem memC own0 G HAR ltac:(rewrite Hfrs; left; reflexivity) HKC
    (PRH_Base.prh_ledger_own B ly S Hp W mem _ _ _ _ _ _ _ HLG)).
destruct (r5_exit D fxk ly S Hp W regs mem md k memC mdC regsC (fun _ => False) _ r1 r2 r3 0 own0 own0 0
  HB HSL HC1 HC2 HC3 HLG HOC HPERM HROOM HLIVE ltac:(lia) (fun a H => False_ind _ H) HJC
  (fun a Ha Hw Hs _ => HKC a Ha Hw Hs) HGC (fun a H => proj2 (HZC a H))) as (HBE & HSLE & HMID).
{ intros off i Hoff Hi. destruct Hoff as [-> | [-> | ->]]; cbv beta; lia. }
{ intros off i Hoff Hi. destruct Hoff as [-> | [-> | ->]]; cbv beta; lia. }
{ rt RG R3 R4. }
{ rt RG R3 R4. }
apply SRr_ret. split; [|exact HPmC].
exists fxk, ly, S, Hp, regsC, memC, mdC, k, r1, r2, r3, own0. split.
{ unfold cn_cfg, cn_pc. change (w64 (BASE + CN_OFF + CN_READ1)) with (Z_to_bv 64 (BASE + 804 + 748)).
  replace (BASE + 804 + 748) with (BASE + 1552) by lia. reflexivity. }
split; [exact HBE|]. split.
{ unfold cn_regsat, cn_core, cn_s8.
  repeat (apply Forall_cons; [cbn [fst snd]; rt RG R3 R4 |]). apply Forall_nil. }
split; [exact HSLE|]. split.
{ split; [exact Hown|]. split; [intros H0; destruct (Hown0 H0) as [Hr1 Hr2]; auto|].
  intros _. apply (val_mem_kept SEGS (w_H W) (w_H W) mem memC); [|exact Hownv].
  intros q Hq. assert (Eq : q = 0) by (cbn in Hq; lia). subst q. rewrite Z.add_0_r.
  destruct (r5_own_img) as [Hoi Hol].
  destruct (r5_cls_img D ly S Hp W mem md _ G HAR ltac:(rewrite Hfrs; left; reflexivity) Hoi) as [Hw Hs].
  apply HKC; [unfold kLowMemEnd in Hol; lia | exact Hw | exact Hs]. }
(* own0 <> 0: the refusal is dead at a consumer run, the cut's (cn_cdead names only the entry state); the hull budget
   is the cut's: the same S, the same stage (copies) *)
split; [exact HHp|]. split; [exact Hcd|]. split; [exact HRP|]. split; [exact HMID | exact HHB].
Qed.

(* the 3rd-NULL arm: own0 = 1 stored, rc1 = -1, st1 = None, r3 = 0, o1 = None (reading 1 skipped) *)
Theorem cn_init3_seg_at : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2,
  @cn_pre fx rc ci cp RL PA B ARx CTX0 D ->
  @cn_at_init3 fx rc cp RL SK PA B ARx D fxk ly S Hp W regs mem md k r1 r2 ->
  P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_INIT3) regs mem md)
    (fun W' c' => (exists regs' mem' md', c' = @cn_cfg SEGS fxk (cn_pc CN_READ2) regs' mem' md' /\
        @cn_at_read2 fx rc cp RL SK PA B ARx D fxk ly S Hp W' regs' mem' md' k (ci_Lam D) (ci_peak D) (ci_cnt D)
          (ci_ran D) r1 r2 0 1 (-1) None None) /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 HPRE HAT HPM.
pose proof HAT as (HB & HR & HSL & HC1 & HC2 & HHp & (own & HLG) & HPERM & HROOM & HRP & HLIVE & Hcd & HHB).
destruct (r5_geo_of_base D fxk ly S Hp W regs mem md k 0 HB) as [G HAR].
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3 & G4 & HRO).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
change (fs_frame_bytes CN_CID / 8) with 64 in Hshp.
pose proof G as (EFa & F0 & F1 & F32 & Fapp & S16 & Hac & Hkb & Hlo & H47).
destruct (r5_S1 D S16) as [HS16 HS1]. pose proof alloc_ceiling_val as [AC _].
pose proof (cn_pre_fpre B ARx CTX0 D HPRE) as HFP. destruct HFP as (HAF & _).
destruct HAF as (_ & _ & _ & Hgp & Htp & _).
assert (R3 : getr regs 3%bv = w64 (as_gp B)) by (rewrite G3; exact Hgp).
assert (R4 : getr regs 4%bv = w64 (as_tp B)) by (rewrite G4; exact Htp).
assert (RG : forall r v, In (r, v) (cn_core D ++ [cn_s8; (19%bv, cn_size D + 16); (20%bv, cn_size D); (21%bv, cn_d2 D);
  (22%bv, 0); (23%bv, ci_data D); (25%bv, cn_d1 D); (26%bv, cn_d3 D)]) -> getr regs r = w64 v)
  by (intros r v Hin; exact (proj1 (Forall_forall _ _) HR (r, v) Hin)).
assert (SLT : forall o v, In (o, v) [(24, r1); (32, cn_F D); (40, r2); (48, cn_d2 D); (56, cn_d1 D); (80, cn_F D)] ->
  rdword (aview SEGS (w_H W) mem) (cn_S1 D + o) = Some v)
  by (intros o v Hin; exact (proj1 (Forall_forall _ _) HSL (o, v) Hin)).
destruct r5_own_img as [Hoi Hol]. unfold kLowMemEnd in Hol.
destruct (r5_cls_img D ly S Hp W mem md _ G HAR ltac:(rewrite Hfrs; left; reflexivity) Hoi) as [Hwo Hso].
unfold cn_cfg, cn_pc. change (w64 (BASE + CN_OFF + CN_INIT3)) with (Z_to_bv 64 (BASE + 804 + 792)).
replace (BASE + 804 + 792) with (BASE + 1596) by lia.
(* 792: li a0, 1; 796: sb a0, -1368(s8) (g_own_ran_out := 1, a program static) *)
apply (s_addi W regs mem md _ 1596 1600 10%bv 0%bv 1); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md1 Hs1.
destruct (r5_own_wr W mem) as [Hoh How].
apply (s_sb P PLAW W _ mem md1 _ 1600 1604 24%bv 10%bv (-1368) (VAL (A_OBJ 13)));
  [r5_slot_ok | lia | lia | reflexivity | | lia | exact Hoh | exact How | exact HPM |].
{ r5_rs'. rewrite (RG 24%bv (VAL (A_HI 9)) ltac:(unfold cn_core, cn_s8; cbn [app In]; r5_in)). unfold v_addi, w64.
  pose proof (@pa_val_range _ _ PA (A_HI 9)). rewrite unsigned_lit_small by lia. rewrite <- (cni_hi9 B IMG). f_equal; lia. }
intros md2 mem1 Hs2 Hfr1 Hgr1 Hhid1 Hv1 HP1.
assert (Hown1 : aview SEGS (w_H W) mem1 (VAL (A_OBJ 13)) = Some 1).
{ rewrite Hv1. f_equal. rewrite getr_same by r5_bvne. reflexivity. }
assert (HJ1 : CNJ D ly S Hp W mem1 md2 k).
{ pose proof (r5_J_of_cn D ly S Hp W mem md k HJ) as HJx. unfold r5_J in *.
  apply (ajournal_x_pst_write SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA) (cni_pst_ok B IMG)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx); [| exact Hgr1 | exact Hhid1 | exact (same_but_materialized_trans _ _ _ Hs1 Hs2)].
  intros x Hx. apply Hfr1. intros E. apply Hx. rewrite E. exact r5_own_pst. }
(* the cut memory and mem1 agree off the own byte *)
assert (K01 : forall a, 0 <= a < 2 ^ 64 -> a <> VAL (A_OBJ 13) -> aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hne. apply aview_eq_of. apply Hfr1. rewrite unsigned_lit_small by exact Ha. exact Hne. }
(* the ledger's own cell after the `sb 1`: prh_own 1 by the stored byte (pi_gz_own_ran_out = 1); the ledger's other
   cells are off the own byte (g_most is apart from g_own_ran_out), so r5_exit rebuilds the exit's ledger at own = 1 *)
assert (HOWN1 : prh_own W mem1 1).
{ split; [|right; reflexivity]. change pi_gz_own_ran_out with 1%nat. rewrite <- (cni_own B IMG).
  apply r5_val_mem1_of_aview; [exact Hown1 | lia]. }
assert (Hshp1 : forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 -> apresent (w_H W) mem1 a)
  by (intros a Ha; exact (r5_apr_grows _ mem mem1 _ Hgr1 (Hshp a Ha))).
assert (SLT1 : forall o v, In (o, v) [(24, r1); (32, cn_F D); (40, r2); (48, cn_d2 D); (56, cn_d1 D); (80, cn_F D)] ->
  rdword (aview SEGS (w_H W) mem1) (cn_S1 D + o) = Some v).
{ intros o v Hin. rewrite <- (SLT o v Hin). apply rdword_ext. intros q Hq.
  assert (Ho : 24 <= o <= 80) by (cbn in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]); destruct Hin).
  apply K01; [lia|]. lia. }
pose proof (r5_inv_init P D ly S Hp W mem1 md2 k HJ1 HP1) as HI1.
(* 800-824: d1's shadow; 828: li a2; 832: mv a0, s9 (d1); 836: mv a1; 840: jal *)
let d := inv_done HI1 in apply (r5_sb7 fxk P PLAW D ly S Hp W mem1 k d _ mem1 md2 _ 1604 4 G ltac:(lia) ltac:(lia) Hshp1);
  [rt RG R3 R4 | r5_slot_ok | lia | lia | exact HI1 |].
intros mem2 md3 HI2.
apply (s_addi W _ mem2 md3 _ 1632 1636 12%bv 0%bv 56); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md4 Hs4.
apply (s_addi W _ mem2 md4 _ 1636 1640 10%bv 25%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md5 Hs5.
apply (s_addi W _ mem2 md5 _ 1640 1644 11%bv 0%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md6 Hs6.
apply (h_call W _ mem2 md6 _ 1644 1648 AS___asan_memset); [r5_slot_ok | lia | lia | reflexivity |].
intros md7 Hs7.
pose proof (r5_inv_md P D ly S Hp W mem1 k _ mem2 md3 md7 HI2
  (same_but_materialized_trans _ _ _ Hs4 (same_but_materialized_trans _ _ _ Hs5
    (same_but_materialized_trans _ _ _ Hs6 Hs7)))) as HI2'.
let d := inv_done HI2' in apply (r5_memset fxk P PLAW PCALL D ly S Hp W mem1 k d _ mem2 md7 _ 1648 32 G (or_introl eq_refl) Hshp1);
  [ intros i Hi; cbv beta; lia | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4
  | rt RG R3 R4 | rt RG R3 R4 | lia | reflexivity | exact HI2' |].
intros regsA memA mdA HPA HIA.
(* 844-868: d2's shadow; 872: li a2; 876: mv a0, s5 (d2); 880: mv a1; 884: jal *)
let d := inv_done HIA in apply (r5_sb7 fxk P PLAW D ly S Hp W mem1 k d _ memA mdA _ 1648 16 G ltac:(lia) ltac:(lia) Hshp1);
  [rt RG R3 R4 | r5_slot_ok | lia | lia | exact HIA |].
intros mem3 md8 HI3.
apply (s_addi W _ mem3 md8 _ 1676 1680 12%bv 0%bv 56); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md9 Hs9.
apply (s_addi W _ mem3 md9 _ 1680 1684 10%bv 21%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md10 Hs10.
apply (s_addi W _ mem3 md10 _ 1684 1688 11%bv 0%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md11 Hs11.
apply (h_call W _ mem3 md11 _ 1688 1692 AS___asan_memset); [r5_slot_ok | lia | lia | reflexivity |].
intros md12 Hs12.
pose proof (r5_inv_md P D ly S Hp W mem1 k _ mem3 md8 md12 HI3
  (same_but_materialized_trans _ _ _ Hs9 (same_but_materialized_trans _ _ _ Hs10
    (same_but_materialized_trans _ _ _ Hs11 Hs12)))) as HI3'.
let d := inv_done HI3' in apply (r5_memset fxk P PLAW PCALL D ly S Hp W mem1 k d _ mem3 md12 _ 1692 128 G (or_intror (or_introl eq_refl)) Hshp1);
  [ intros i Hi; cbv beta; lia | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4
  | rt RG R3 R4 | rt RG R3 R4 | lia | reflexivity | exact HI3' |].
intros regsB memB mdB HPB HIB.
(* 888-912: d3's shadow; 916: li a2; 920: mv a0, s10 (d3); 924: mv a1; 928: jal *)
let d := inv_done HIB in apply (r5_sb7 fxk P PLAW D ly S Hp W mem1 k d _ memB mdB _ 1692 28 G ltac:(lia) ltac:(lia) Hshp1);
  [rt RG R3 R4 | r5_slot_ok | lia | lia | exact HIB |].
intros mem4 md13 HI4.
apply (s_addi W _ mem4 md13 _ 1720 1724 12%bv 0%bv 56); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md14 Hs14.
apply (s_addi W _ mem4 md14 _ 1724 1728 10%bv 26%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md15 Hs15.
apply (s_addi W _ mem4 md15 _ 1728 1732 11%bv 0%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md16 Hs16.
apply (h_call W _ mem4 md16 _ 1732 1736 AS___asan_memset); [r5_slot_ok | lia | lia | reflexivity |].
intros md17 Hs17.
pose proof (r5_inv_md P D ly S Hp W mem1 k _ mem4 md13 md17 HI4
  (same_but_materialized_trans _ _ _ Hs14 (same_but_materialized_trans _ _ _ Hs15
    (same_but_materialized_trans _ _ _ Hs16 Hs17)))) as HI4'.
let d := inv_done HI4' in apply (r5_memset fxk P PLAW PCALL D ly S Hp W mem1 k d _ mem4 md17 _ 1736 224 G (or_intror (or_intror eq_refl)) Hshp1);
  [ intros i Hi; cbv beta; lia | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4 | rt RG R3 R4
  | rt RG R3 R4 | rt RG R3 R4 | lia | reflexivity | exact HI4' |].
intros regsC memC mdC HPC HIC.
(* 932: li s7, -1; 936: mv s3, s10 (d3); 940: ld s10, 24(s1) (r1) *)
apply (s_addi W _ memC mdC _ 1736 1740 23%bv 0%bv (-1)); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md18 Hs18.
apply (s_addi W _ memC md18 _ 1740 1744 19%bv 26%bv 0); [r5_slot_ok | reflexivity | lia | lia | reflexivity |].
intros md19 Hs19.
apply (s_ld W _ memC md19 _ 1744 1748 26%bv 9%bv 24 (cn_S1 D + 24) r1); [r5_slot_ok | reflexivity | lia | lia | reflexivity | | lia | lia | |].
{ r5_rs'. rewrite (RG 9%bv (cn_S1 D) ltac:(unfold cn_core, cn_s8; cbn [app In]; r5_in)). unfold v_addi, w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
{ apply (r5_rd_stack P D ly S Hp W mem1 k _ memC mdC (cn_S1 D + 24) r1 G ltac:(lia) ltac:(lia) (SLT1 24 r1 ltac:(cbn [In]; r5_in)) HIC). }
intros md20 Hs20.
pose proof (r5_inv_md P D ly S Hp W mem1 k _ memC mdC md20 HIC
  (same_but_materialized_trans _ _ _ Hs18 (same_but_materialized_trans _ _ _ Hs19 Hs20))) as HIC'.
(* ---- the exit CN_READ2 (944) ---- *)
pose proof HIC' as (HJC & HPmC & HKC & HGC & HZC).
(* the ledger's own cell at the exit: the stored 1, off CA5's later writes *)
assert (HOC : prh_own W memC 1)
  by exact (r5_own_kept D ly S Hp W mem md mem1 memC 1 G HAR ltac:(rewrite Hfrs; left; reflexivity) HKC HOWN1).
lazymatch goal with |- SRr _ _ {| cfg_ms := @YK11.mkst _ ?rg _ _ _; cfg_model := _ |} _ => set (regsF := rg) end.
let d := inv_done HIC' in destruct (r5_exit D fxk ly S Hp W regs mem md k memC md20 regsF (fun a => a = VAL (A_OBJ 13)) d r1 r2 0 1 own 1 2
  HB HSL HC1 HC2 ltac:(left; reflexivity) HLG HOC HPERM HROOM HLIVE ltac:(lia) (fun a H => H) HJC) as (HBE & HSLE & HMID).
{ intros a Ha Hw Hs Hne. rewrite (HKC a Ha Hw Hs). exact (K01 a Ha Hne). }
{ exact (r5_grows_trans _ _ _ Hgr1 HGC). }
{ intros a H. exact (proj2 (HZC a H)). }
{ intros off i Hoff Hi. destruct Hoff as [-> | [-> | ->]]; cbv beta; lia. }
{ intros off i Hoff Hi. destruct Hoff as [-> | [-> | ->]]; cbv beta; lia. }
{ unfold regsF. rt RG R3 R4. }
{ unfold regsF. rt RG R3 R4. }
apply SRr_ret. split; [|exact HPmC].
exists regsF, memC, md20. split.
{ unfold cn_cfg, cn_pc. change (w64 (BASE + CN_OFF + CN_READ2)) with (Z_to_bv 64 (BASE + 804 + 944)).
  replace (BASE + 804 + 944) with (BASE + 1748) by lia. reflexivity. }
split; [exact HBE|]. split.
{ unfold cn_regsat, cn_core, cn_s8, regsF.
  repeat (apply Forall_cons; [cbn [fst snd]; rt RG R3 R4 |]). apply Forall_nil. }
split; [exact HSLE|]. split.
{ split; [lia|]. split; [intros H0; discriminate H0|]. intros _.
  apply r5_val_mem1_of_aview; [|lia].
  rewrite (HKC (VAL (A_OBJ 13)) ltac:(lia) Hwo Hso). exact Hown1. }
split; [exact HMID|]. split; [intros H0; discriminate H0|].
(* own0 = 1 <> 0: no reading was made, the events since entry are the granted copies' (CA5 makes none), the struct of
   reading 1 is the zero one (st1 = None), and the third copy's refusal is dead at a consumer run (the cut's cn_cdead) *)
split.
{ intros _. split; [exact HRP|]. split; [reflexivity | exact Hcd]. }
(* the hull budget at the same S: reading 1 was skipped and pays nothing, so its events leave the budget (copies ->
   rd1: the base's split equation, then hull_budget_app with nothing used) *)
rewrite (cn_hrest_rd1_split (ci_x D)) in HHB.
exact (PresetHullBudget.hull_budget_app S S _ _ HHB (PresetHullBudget.hull_used_refl S _)).
Qed.

(* the base's exit form: cn_ex_read2 *)
Theorem cn_init3_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2,
  @cn_pre fx rc ci cp RL PA B ARx CTX0 D ->
  @cn_at_init3 fx rc cp RL SK PA B ARx D fxk ly S Hp W regs mem md k r1 r2 ->
  P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_INIT3) regs mem md)
    (fun W' c' => @cn_ex_read2 fx rc cp RL SK PA B ARx D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 HPRE HAT HPM.
eapply SRr_mono; [exact (cn_init3_seg_at P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 HPRE HAT HPM)|].
cbv beta. intros W' c' _ ((regs' & mem' & md' & Hc & HA) & HP). split; [|exact HP].
exists fxk, ly, S, Hp, regs', mem', md', k, (ci_Lam D), (ci_peak D), (ci_cnt D), (ci_ran D), r1, r2, 0, 1, (-1), None,
  None.
split; [exact Hc | exact HA].
Qed.
End cn5.

Check cn_init_seg.
Check cn_init3_seg.
Check cn_init3_seg_at.
Print Assumptions cn_init_seg.
Print Assumptions cn_init3_seg_at.
Print Assumptions cn_init3_seg.
