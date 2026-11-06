(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_Base.v, with its module names changed; 658 of its 729 lines of code are new or changed and 972 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): segment CA9 Cmp
   of the re-walk of check_no_overread (cno, entry 0x81904) against the text tcheck_no_overread_specX, re-fit to the
   cut by a Theorem Labs lane (first walked by another Theorem Labs lane, under a Theorem Labs session; plan, the internal file PLAN-cno-caw-102.md 5.1 row CA9).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (the cut of record 7cdbb61b5fa0; every path at the cut's blob but this row's
   files): the contract lib/A/Prog/Cno102A_Base.v (statements, blob ba76a7bc31c9 at a working branch
   4b59cadb07a1): cn_pre CTX0 D without the run-word list (DW-SPLIT); cn_base .. k wk, the journal cn_J at the wild
   budget wk, 6 from the compare on; cn_at_cmp with own = 0, the readings' grants o1 o2 o0 LAST and the readings'
   free-order ties cn_fo for d1 / d2 / d3; cn_at_free with ownl and, under ownl = 0, the copies non-NULL, the events,
   the structs against the grants and the three ties, under ownl <> 0 the copies' events, the structs zero and cn_cdead
   (every free exit here has ownl = 0, so that arm is refuted). The shared step kit lib/A/Prog/Cno102A_Ro.v,
   in its forms over a world relation R at R := wle' SEGS RZ (below): cn_ro_callR / cn_call_keepR
   take wk after k and keep it (the fixed callees add no wild trace), carry cn_mid at own and the three cn_fo ties
   across the call; cn_call_keepR takes the caller's journal REBASED to the empty budget (YCbqGwild.ajournal_xw_rebaseR,
   entry depot moved to the current one) and unbases it; cn_chainR, cn_entry_facts, cn_base_matR, the hand steps
   cn_hs_*0 / cn_hs_call (plain SRr), ro_getr. The texts: lib/A/PRH_FnEx.v be1dd5ecaaf6 (tsame_specX:
   most / own in the ledger, `S' = S`, and the GUARDED live-stack premise `spZ regs <= pa -> YGcallStackUp.astack_up_x
   ..`, refuted at both calls: the root d1 lies in the class-3 fake frame below alloc_ceiling (cn9_dlo), the callee's sp
   is cn_S1 D above it), lib/A/PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_alloc_ran_out_specX, `S' = S`), lib/A/PRH_Base.v
   ef7c8ca98529 (prh_own, the ledger projections prh_ledger_own / prh_ledger_bounds / prh_ledger_blocks, fpre ending in
   frm_zero (fp_csr fx)), lib/A/PRH_Reader.v; listing lib/A/Listing_prog.v (slots 201 + off / 4: PCall
   AS_fuzz_alloc_ran_out 1 at 1472, PCall AS_same 1 at 1500 / 1520, every other slot of the segment a PW word); engine:
   YCbqG.v (ajournal_xwR, read by the ajxR_* projections; apost_base_x_R_lift), YCbqGwild.v (ajournal_xw_rebaseR),
   YCbqGcallW.v (aj_call_xWR, fpostW_x_of_apostR), YA0n.v (SRr_ret / SRr_mono), YA0nH.v (SRr', wle', SRr_SRr',
   SRr_SRrG, SRrG_bind, wle_wle'), YSRrG.v (SRr'_bind / SRr'_ret), YSRrMemnorm.v (srr_inv_call). The B' twin is
   Cno102B_R7.v: the same shapes, cnb_ for cn_.
   THE RE-HIDING MOVE: the compare cut lies after the first parse_noting, whose text (tparse_noting_specX) crosses a
   free, so every cut here holds its journal from entry at wle' SEGS RZ (RZ := YGcfRehidePost.RZ_cf, the fixed zone):
   the Base's cn_baseR at that relation, cn_at_cmp / cn_at_free / cn_ex_free restated in place at it, and this file's
   cn_at_same1 / cn_at_same2 too (used only after a free). So every segment here concludes SRr' SEGS RZ. tsame_specX
   and tfuzz_alloc_ran_out_specX are NOT crossing texts (unchanged, plain SRr and fpostm): their calls go through the
   call rules' R forms at R := wle' SEGS RZ (aj_call_xWR, cn_ro_callR), the callee's plain post lifted by
   SRr_SRrG / apost_base_x_R_lift at wle_wle'. The hand steps stay plain SRr: before a call Cno102A_Ro.v's
   cn_srrG_lift binds them into the relation, after one SRr_SRr' lifts them. No world conjunct (ajxR_rel) is read here.
   THE HULL: every cut here carries PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)), the Base's suffix of the
   all-granted events still to pay after the three readings. Neither callee here changes S (`S' = S`), so the conjunct
   rides unchanged from cn_at_cmp to every exit (cn_ex_free, cn_at_same1, cn_at_same2).
   THE CODE (DERIVED offsets from the entry; registers at CN_CMP: s3 = d3, s4 = rc3, s5 = 1, s6 = r3, s7 = rc1,
   s9 = rc2, s10 = r1, s8 = the auipc hi of g_own_ran_out):
     1048 lbu a0, -0x558(s8)     the g_own_ran_out byte v (cn_img: cni_hi9, cni_own, cni_pst_seg); the cut's ledger at
                                 own = 0 gives v = 0 (PRH_Base.prh_ledger_own, cn9_own_val)
     1052 beqz a0 -> 1468        always taken: the fall-through 1056 (ld s9, 0x38(s1), CN_FREE with ownl = v <> 0) is
                                 REFUTED by v = 0
     1468 mv s8, s9              rc2
     1472 jal fuzz_alloc_ran_out (cn_ro_call, ret 1476)   1476 ld s9, 0x38(s1)   1480 bnez a0 -> CN_FREE (r = 1, ran = 1)
     1484 bnez s7 -> 1528        1488 bnez s8 -> 1508     1492 mv a0, s9   1496 ld a1, 0x30(s1)   1500 jal same (ret 1504)
     1504 beqz a0 -> 1544 ABORT  1508 bnez s4 -> 1528     1512 mv a0, s9   1516 mv a1, s3   1520 jal same (ret 1524)
     1524 beqz a0 -> 1544 ABORT  1528 bne s7, s4 -> 1544 ABORT   1532 bne s8, s4 -> 1544 ABORT
     1536 mv s5, zero            1540 j CN_FREE (r = 0)
   With g_ran_out = 0 the base's cn_res gives every reading: ck_read x = None: rc1 = rc2 = rc3 = -1 and the structs
   zero, so 1484 jumps to 1528 and both bne fall through (rc's equal); ck_read x = Some t: rc_i = 0 and st_i =
   Some (t, D_i), so the walk reaches the two `same` calls, each with equal trees.
   THE ABORT EDGES, REFUTED (never walked): 1504 and 1524 (beqz a0) by tsame_specX's result disjunct at equal trees,
   cn9_same_one (a0 = 1) in cn9_same_call; 1528 (bne s7, s4) and 1532 (bne s8, s4) by the readings' equal rc's (cn_res:
   -1 / -1 on the None path in cn_cmp_seg, 0 / 0 after the two calls in cn_same2_step).
   WHAT IS HERE: the call states cn_at_same1 / cn_at_same2 (cn_mid at own = 0, the journal at budget 6, the three
   free-order ties, the hull at rd0) and their exits cn_ex_same1 / cn_ex_same2; cn_cmp_seg (CN_CMP -> cn_ex_free \/
   cn_ex_same1; the ledger at own = 0 and the ties across fuzz_alloc_ran_out by cn_ro_callR, across the hand steps by
   the unchanged W and mem); cn9_same_call (one `same` call: the journal rebased, aj_call_xWR, the text HSAME for any
   float state at n = DOC_D, P across by srr_inv_call, the cut's facts, the budget and the ties by cn_call_keepR with
   tsame's S' = S and its ledger at the same most / own); cn_same1_step (cn_ex_same1 -> cn_ex_same2) and cn_same2_step
   (cn_ex_same2 -> cn_ex_free, r = 0, ownl = 0); the pure lemmas cn9_same_one, cn9_depth, cn9_tree (prhex_tree of
   d1 / d2 / d3), cn9_foot (footprints apart from same's window), cn9_dlo (the roots below alloc_ceiling), cn9_own_val
   (the byte read is prh_own's value).
   THE EVENTS (the Base's cn_prog): CA9 makes no model event (fuzz_alloc_ran_out and same keep S, `S' = S`), so the
   compare cut's cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S, ran = cn_ranz D o1 o2 o0, the structs against
   the grants (cn_rds3 D o1 o2 o0 st1 st2 st3: no struct changes here), their free-order ties and the copies' non-NULL
   reach every exit unchanged, with the same grants o1 o2 o0 (LAST, the Base's order); at the two `same` call states
   ran = 0, stated `0 = cn_ranz D o1 o2 o0`.
   Numerals: 1048 .. 1544 (DERIVED: byte offsets inside cno); 192 / 224 / 32 / 16 / 56 / 48 / 512 (LENGTH: frame,
   alignment, slot and struct sizes, the class-3 frame); 27424 / 12544 (DERIVED: STK_check_no_overread and
   STK_same DOC_D at prh_img_A, by reflexivity); 1368 (LENGTH: the lo12 of the hi/lo pair, via cni_hi9); register
   numbers and instruction immediates (WORD, checked against the listing by vm_compute). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit Cno102A_Base Cno102A_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which sets this flag to false GLOBALLY; lia on the frame / slot arithmetic needs it on
   (S4_PsU.v's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* the re-hiding move's fixed zone: after a free the world relation is YA0nH.wle' SEGS RZ *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.

(* ---- the cut offsets of this file (DERIVED byte offsets inside check_no_overread, the twin's listing
   the internal file check_no_overread.A_new.s): the ran-out call, the two `same` calls and their return sites ---- *)
Definition CN_RO : Z := 1472.      (* 0x81ec4 jal fuzz_alloc_ran_out *)
Definition CN_RORET : Z := 1476.   (* 0x81ec8 *)
Definition CN_SAME1 : Z := 1500.   (* 0x81ee0 jal same (d1, d2) *)
Definition CN_RS1 : Z := 1504.     (* 0x81ee4 beqz a0 -> abort *)
Definition CN_SAME2 : Z := 1520.   (* 0x81ef4 jal same (d1, d3) *)
Definition CN_RS2 : Z := 1524.     (* 0x81ef8 beqz a0 -> abort *)
Definition cn9_same_rets : list Z := [CN_RS1; CN_RS2].

(* the instruction word of cno's slot at a DERIVED offset, read out of the listing (no word is typed) *)
Definition cn9_pw (off : Z) : Z :=
  match plookup A_prog_tpi_cno (CN_OFF + off) with Some (PW w) => w | _ => 0 end.

(* ---- small kit pieces Cno102A_Ro.v does not have ---- *)
Lemma cn9_rs_app_l : forall regs l1 l2, cn_regsat regs (l1 ++ l2) -> cn_regsat regs l1.
Proof. intros regs l1 l2 H. unfold cn_regsat in *. apply Forall_app in H. exact (proj1 H). Qed.
(* a list of callee-saved registers, checked by computation *)
Lemma cn9_cs : forall l : list (bv 5 * Z),
  forallb (fun p => let r := bv_unsigned (fst p) in ((r =? 2) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 27)))%bool)
    l = true ->
  Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) l.
Proof.
induction l as [|p l IH]; intros H; [constructor|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
constructor; [|exact (IH H2)]. unfold acallee_saved. cbv zeta in H1.
repeat rewrite orb_true_iff in H1. repeat rewrite andb_true_iff in H1. rewrite !Z.eqb_eq, !Z.leb_le in H1. lia.
Qed.

Section k9. Context {rc : YM05.RunCeil}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
(* `bne rs1, rs2, imm` (two registers; Cno102A_Ro.v has the `bnez` form): falls through when the registers are equal *)
Lemma cn9_hs_bne : forall (W : world SEGS) fxk regs mem md Q off w rs1 rs2 imm (z : bool),
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> 0 <= off + bv_signed imm < 2 ^ 28 ->
  c_eq (getr regs rs1) (getr regs rs2) = z ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc (if z then off + 4 else off + bv_signed imm)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off w rs1 rs2 imm z Hpl Hdec Ho Hj Hc HK.
pose proof (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as He.
destruct z.
- apply (cn_step W fxk regs mem md regs off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_ft fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs1 rs2 imm Hf He Hdec Hc).
  rewrite (cn_pc4 off ltac:(lia)). reflexivity.
- apply (cn_step W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_tk fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs1 rs2 imm Hf He Hdec Hc).
  unfold btgt. rewrite (cn_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
Qed.
End k9.

(* ---- tactics of this file ---- *)
Ltac cn9_in := solve [cbn [cn_core cn_s8 app In]; repeat (first [left; reflexivity | right])].
(* a register snapshot of the current registers: each entry read off the snapshot HR of the same registers, or through
   the updates (ro_getr) down to HR's registers *)
Ltac cn9_rs HR := unfold cn_regsat, cn_core; cbn [app];
  repeat (apply Forall_cons; [cbn [fst snd];
    first [ apply (cn_regsat_get _ _ _ _ HR); cn9_in
          | ro_getr; rewrite ?ro_mv; ro_getr;
            first [reflexivity | apply (cn_regsat_get _ _ _ _ HR); cn9_in | idtac] ] |]);
  try apply Forall_nil.
Ltac cn9_cs := apply cn9_cs; vm_compute; reflexivity.
(* evaluate the instruction immediates of the goal *)
Ltac cn9_bsv := repeat match goal with |- context [bv_signed ?i] =>
  let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end.
(* the pc of the current configuration after a branch, as a literal offset *)
Ltac cn9_pc o := lazymatch goal with |- SRr _ _ (cn_cfg _ (cn_pc ?x) _ _ _) _ =>
  replace x with o by (vm_compute; reflexivity) end.
(* a listing slot or a decode, by computation; a decode compares bv literals through bool_decide (their wf proofs
   differ syntactically: YK1a.v vm_refl_bv) *)
Ltac cn9_lst := first [vm_compute; reflexivity | vm_refl_bv].

Section r9. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation CFG := (@cn_cfg SEGS).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cn_img B.
(* the callee texts, for any float state (the kit cut 7cdbb61b5fa0: PRH_FnAlloc.v 4d8aeba047e5 / PRH_FnEx.v
   be1dd5ecaaf6) *)
Hypothesis HRO : forall fz : YK11.FPState, @tfuzz_alloc_ran_out_specX fz rc cp prh_img_A RL A_prog_listing PA B ARx SK.
Hypothesis HSAME : forall fz : YK11.FPState, @tsame_specX fz rc cp prh_img_A RL A_prog_listing PA B ARx SK DOC_D.
#[local] Notation CNPRE := (cn_pre (fx := fx) B ARx CTX0).
(* every cut of this file lies after the first parse_noting: the base at the re-hiding relation *)
#[local] Notation CNB := (cn_baseR (fx := fx) B ARx (wle' SEGS RZ)).
#[local] Notation CNMID := (@cn_mid rc cp RL PA B).
#[local] Notation CNCMP := (cn_at_cmpR (fx := fx) B ARx (wle' SEGS RZ)).
#[local] Notation CNFREE := (cn_ex_freeR (fx := fx) B ARx (wle' SEGS RZ)).

(* ---- THE TWO `same` CALL STATES (callee entry, ra = the return site): the compare cut's facts with the flag read 0,
   g_ran_out 0 and the input read by the grammar: every reading done, rc1 = rc2 = rc3 = 0, the three trees t, the
   journal at the compare's budget 6 and at the re-hiding relation wle' SEGS RZ (CNB; both states lie after a free, so
   they are stated at that relation in place). The readings' grants o1 o2 o0 LAST (the Base's cn_at_cmp order): the
   events since entry (cn_prog over the granted copies and the three readings), g_ran_out = cn_ranz of them, which is
   0 on this path, the structs against the grants and the three free-order ties (cn_fo, the Base's cn_at_cmp
   spelling), and the hull budget at the compare's stage rd0 (the Base's cn_hrest_rd0, LAST, the Base's cut order).
   Registers: a0 = d1, a1 = d2 (first) or d3 (second), s3 = d3, s4 = rc3, s5 = 1, s6 = r3, s7 = rc1, s8 = rc2 (`mv s8, s9`
   at 1468), s9 = d1 (`ld s9, 0x38(s1)` at 1476), s10 = r1 ---- *)
Definition cn_at_same1 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 : Z) (t : PjTree.jv) (D1 D2 D3 : list (Z * Z)) (o1 o2 o0 : option nat) : Prop :=
  CNB D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RS1); (10%bv, cn_d1 D); (11%bv, cn_d2 D); (19%bv, cn_d3 D);
                                (20%bv, 0); (21%bv, 1); (22%bv, r3); (23%bv, 0); (24%bv, 0); (25%bv, cn_d1 D);
                                (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ 0 = cn_ranz D o1 o2 o0 /\
  cn_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  cn_fo D W mem Lam o1 (cn_d1 D) (Some (t, D1)) /\ cn_fo D W mem Lam o2 (cn_d2 D) (Some (t, D2)) /\
  cn_fo D W mem Lam o0 (cn_d3 D) (Some (t, D3)) /\
  CNMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  ck_read (ci_x D) = Some t /\
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)).
Definition cn_at_same2 (D : cn_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 : Z) (t : PjTree.jv) (D1 D2 D3 : list (Z * Z)) (o1 o2 o0 : option nat) : Prop :=
  CNB D fxk ly S Hp W regs mem md k 6 /\
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RS2); (10%bv, cn_d1 D); (11%bv, cn_d3 D); (19%bv, cn_d3 D);
                                (20%bv, 0); (21%bv, 1); (22%bv, r3); (23%bv, 0); (24%bv, 0); (25%bv, cn_d1 D);
                                (26%bv, r1)]) /\
  cn_slots D W mem r1 r2 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ 0 = cn_ranz D o1 o2 o0 /\
  cn_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  cn_fo D W mem Lam o1 (cn_d1 D) (Some (t, D1)) /\ cn_fo D W mem Lam o2 (cn_d2 D) (Some (t, D2)) /\
  cn_fo D W mem Lam o0 (cn_d3 D) (Some (t, D3)) /\
  CNMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  ck_read (ci_x D) = Some t /\
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)).
(* their forward exits, in the base's style *)
Definition cn_ex_same1 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  c = CFG fxk (SIGMA AS_same) regs mem md /\
  cn_at_same1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0.
Definition cn_ex_same2 (D : cn_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  c = CFG fxk (SIGMA AS_same) regs mem md /\
  cn_at_same2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0.

(* ---- THE PURE LEMMAS the refutation of the compare's abort edges rests on ---- *)
(* same trees: tsame_specX's result disjunct gives a0 = 1 *)
Lemma cn9_same_one : forall (ta tb : PjTree.jv) (regs' : bvmap 5 word),
  (ta = tb /\ getr regs' 10%bv = w64 1 \/ ta <> tb /\ getr regs' 10%bv = w64 0) -> ta = tb ->
  getr regs' 10%bv = w64 1.
Proof. intros ta tb regs' [[_ H] | [Hn _]] He; [exact H | exfalso; exact (Hn He)]. Qed.
(* tsame_specX's depth premise at n = DOC_D from the reading's depth bound (cn_doc) *)
Lemma cn9_depth : forall t : PjTree.jv, (PjTree.depth t <= PjGrammar.MAXD)%nat -> (PjTree.depth t <= DOC_D)%nat.
Proof.
intros t H. assert (E : (PjGrammar.MAXD <= DOC_D)%nat) by (apply Nat.leb_le; vm_compute; reflexivity). lia.
Qed.
(* the stack facts of a cut: the entry sp, the realigned body sp, the layout the journal keeps *)
Lemma cn9_S1_rng : forall D fxk ly S Hp W regs mem md k wk, CNB D fxk ly S Hp W regs mem md k wk ->
  YM05.alloc_ceiling + STK_check_no_overread <= cn_sp0 D /\ cn_sp0 D <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\
  cn_sp0 D mod 16 = 0 /\ cn_S1 D mod 32 = 0 /\ cn_S1 D + 192 <= cn_sp0 D /\ cn_sp0 D < cn_S1 D + 224 /\
  ly_stk_lo ly = ly_stk_lo (ci_ly D) /\ ly_stk_hi ly = ly_stk_hi (ci_ly D) /\ ly_F ly = ly_F (ci_ly D).
Proof.
intros D fxk ly S Hp W regs mem md k wk HB.
destruct HB as (_ & _ & (WS & HJ & _) & _).
pose proof (ajxR_ly HJ) as Hly.
pose proof (ajxR_stk HJ) as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
unfold cn_S1. rewrite ro_land32. pose proof (Z.mod_pos_bound (cn_sp0 D - 192) 32 ltac:(lia)) as Hm.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Elo|]. split; [exact Ehi | exact EF].
Qed.
(* the tree of a done reading at d1 / d2 / d3 is a tree of tsame_specX: its home is the function's own fake frame
   ((CN_CID, fpos) on top of frames S, prhex_home's frame arm), its 56 bytes open (cn_open) *)
Lemma cn9_tree : forall D fxk ly S Hp W regs mem md k wk Lam d t Dd,
  CNB D fxk ly S Hp W regs mem md k wk -> (d = cn_d1 D \/ d = cn_d2 D \/ d = cn_d3 D) ->
  cn_open W mem d -> cn_doc W mem Lam d (Some (t, Dd)) ->
  prhex_tree ly S Lam W regs mem d t Dd.
Proof.
intros D fxk ly S Hp W regs mem md k wk Lam d t Dd HB Hd Hop Hdoc.
pose proof (cn9_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EF).
destruct HB as (_ & _ & _ & HFR & _). destruct HFR as (Efr & _).
assert (E3 : fs_frame_bytes CN_CID = 512) by reflexivity.
destruct Hdoc as [Hnode _]. unfold prhex_tree.
split; [exact Hnode|]. split; [|exact Hop].
right; left. exists CN_CID, (ci_fpos D). split; [rewrite Efr; left; reflexivity|].
rewrite E3. unfold cn_d1, cn_d2, cn_d3, cn_F, frame_addr in *. rewrite EF. lia.
Qed.
(* a struct of the readings (d1 / d2 / d3, in the class-3 fake frame on top of frames S) lies below alloc_ceiling
   (AR_laws_x's frame bound, alx_sep); so below every real-stack address, the callee's sp among them *)
Lemma cn9_dlo : forall D fxk ly S Hp W regs mem md k wk d,
  CNB D fxk ly S Hp W regs mem md k wk -> (d = cn_d1 D \/ d = cn_d2 D \/ d = cn_d3 D) ->
  d + 56 <= YM05.alloc_ceiling.
Proof.
intros D fxk ly S Hp W regs mem md k wk d HB Hd.
pose proof (cn9_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EF).
assert (E3 : fs_frame_bytes CN_CID = 512) by reflexivity.
destruct HB as (_ & _ & (WS & HJ & _) & HFR & _). destruct HFR as (Efr & _).
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md (ajxR_ar HJ)) as (_ & Hfb).
rewrite Forall_forall in Hfb.
assert (Hin3 : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Efr; left; reflexivity).
specialize (Hfb _ Hin3). cbn [fst snd] in Hfb. rewrite E3 in Hfb.
unfold frame_addr in Hfb. rewrite EF in Hfb.
destruct Hd as [-> | [-> | ->]]; unfold cn_d1, cn_d2, cn_d3, cn_F, frame_addr in *; lia.
Qed.
(* the footprint of a done reading's tree lies below alloc_ceiling (a frame byte or a ledger block), same's window
   on the real stack above it: apart *)
Lemma cn9_foot : forall D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 d t Dd z,
  CNB D fxk ly S Hp W regs mem md k wk -> CNMID D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  spZ regs = cn_S1 D ->
  ((d = cn_d1 D /\ st1 = Some (t, Dd)) \/ (d = cn_d2 D /\ st2 = Some (t, Dd)) \/ (d = cn_d3 D /\ st3 = Some (t, Dd))) ->
  PRH_Reader.pj_footR d Dd z -> ~ (spZ regs - STK_same DOC_D <= z < spZ regs).
Proof.
intros D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 d t Dd z HB HM Hsp Hd Hz.
pose proof (cn9_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (Hsp0 & _ & _ & _ & _ & HS1a & HS1b & _ & _ & EF).
assert (ESTK : STK_check_no_overread = 27424) by reflexivity.
assert (ESM : STK_same DOC_D = 12544) by reflexivity.
pose proof cf_head_nonneg as Hh0.
assert (Hlt : z < YM05.alloc_ceiling).
{ pose proof HB as (_ & _ & (WS & HJ & _) & _). pose proof (ajxR_ar HJ) as HAR.
  destruct Hz as [Hz | ((a, kk) & Hin & Hh)].
  - assert (Hd3 : d = cn_d1 D \/ d = cn_d2 D \/ d = cn_d3 D)
      by (destruct Hd as [(-> & _) | [(-> & _) | (-> & _)]]; [left | right; left | right; right]; reflexivity).
    pose proof (cn9_dlo D fxk ly S Hp W regs mem md k wk d HB Hd3) as Hd56. lia.
  - destruct HM as (_ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
    assert (HinL : In (a, kk) Lam).
    { apply (Permutation_in _ (Permutation_sym HPL)).
      destruct Hd as [(_ & ->) | [(_ & ->) | (_ & ->)]]; cbn [cn_Dof]; rewrite !in_app_iff; tauto. }
    pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF. rewrite Forall_forall in HF.
    destruct (HF (a, kk) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & Hce & _).
    unfold pj_holdsR in Hh. cbn [fst snd] in Hh. unfold req_size in Hce.
    destruct (Z.eqb_spec (kk + cf_head) 0); lia. }
rewrite Hsp, ESM. lia.
Qed.

(* ---- the byte of g_own_ran_out the `lbu` at CN_CMP reads: the address is the hi/lo pair's (cni_hi9, cni_own), and a
   program static is a segment byte (cni_pst_seg), so the load reads a value whatever the memory holds ---- *)
Lemma cn9_own_pst : Exists (in_zr pi_g_own_ran_out) prh_pst.
Proof.
apply Exists_exists. exists (pi_g_own_ran_out, 1). split; [vm_compute; repeat (first [left; reflexivity | right])|].
unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma cn9_own_byte : forall (W : world SEGS) mem, exists b, mbyte SEGS (mrestrict (w_H W) mem) pi_g_own_ran_out = Some b.
Proof.
intros W mem. unfold mbyte.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 pi_g_own_ran_out)) as [b|]; [exists b; reflexivity|].
destruct (YK11.seg_rom SEGS (Z_to_bv 64 pi_g_own_ran_out)) as [b|] eqn:Es; [exists b; reflexivity|].
exfalso. exact (cni_pst_seg B IMG pi_g_own_ran_out cn9_own_pst Es).
Qed.
Lemma cn9_own_addr : forall regs, getr regs 24%bv = w64 (VAL (A_HI 9)) ->
  bv_unsigned (getr regs 24%bv) + bv_signed (2728%bv : bv 12) = pi_g_own_ran_out.
Proof.
intros regs H. rewrite H. unfold w64. pose proof (@pa_val_range _ _ PA (A_HI 9)) as Hr.
rewrite unsigned_lit_small by lia. cn9_bsv.
pose proof (cni_hi9 B IMG) as E1. pose proof (cni_own B IMG) as E2. lia.
Qed.
(* the byte a load of g_own_ran_out reads is prh_own's value: prh_own is val_mem of the 1-byte cell
   (pi_gz_own_ran_out = 1), whose byte 0 is le_byte o 1 0 = o (Cno102A_R6.v r6_byte_val's argument) *)
Lemma cn9_byte_val : forall (m : word -> option byte) a b v, mbyte SEGS m a = Some b -> val_mem SEGS m a 1 v ->
  0 <= v < 256 -> bv_unsigned b = v.
Proof.
intros m a b v Hb Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r, Hb in Hv.
injection Hv as ->. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (bv_modulus 8) with 256. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma cn9_own_val : forall (W : world SEGS) mem b o,
  mbyte SEGS (mrestrict (w_H W) mem) pi_g_own_ran_out = Some b -> prh_own W mem o -> bv_unsigned b = o.
Proof. intros W mem b o Hb (Hv & Ho). apply (cn9_byte_val _ _ b o Hb Hv). lia. Qed.
(* a slot of the body's real-stack frame (cn_slots) *)
Lemma cn9_slot : forall D (W : world SEGS) mem r1 r2 o v, cn_slots D W mem r1 r2 ->
  In (o, v) [(24, r1); (32, cn_F D); (40, r2); (48, cn_d2 D); (56, cn_d1 D); (80, cn_F D)] ->
  rdword (aview SEGS (w_H W) mem) (cn_S1 D + o) = Some v.
Proof. intros D W mem r1 r2 o v H Hin. exact (proj1 (Forall_forall _ _) H (o, v) Hin). Qed.
(* the base at a materialised model, same registers *)
Lemma cn9_base_md : forall D fxk ly S Hp W regs mem md k wk X,
  CNB D fxk ly S Hp W regs mem md k wk -> CNB D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros D fxk ly S Hp W regs mem md k wk X H.
exact (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly S Hp W regs regs mem md k wk X H eq_refl eq_refl).
Qed.

(* ---- packing the exits ---- *)
Lemma cn9_mk_free : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  CNB D fxk ly S Hp W regs mem md k 6 ->
  cn_regsat regs (cn_core D ++ [(19%bv, cn_d3 D); (21%bv, r); (22%bv, r3); (25%bv, cn_d1 D); (26%bv, r1)]) ->
  cn_slots D W mem r1 r2 -> CNMID D ly S Hp W mem Lam peak cnt ran ownl 3 r1 r2 r3 st1 st2 st3 ->
  0 <= ownl < 256 -> ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) ->
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
     cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0 /\
     cn_rds3 D o1 o2 o0 st1 st2 st3 /\
     cn_fo D W mem Lam o1 (cn_d1 D) st1 /\ cn_fo D W mem Lam o2 (cn_d2 D) st2 /\ cn_fo D W mem Lam o0 (cn_d3 D) st3) ->
  (ownl <> 0 -> cn_prog D (cn_cevs D r1 r2 r3) S /\ st1 = None /\ st2 = None /\ st3 = None /\ cn_cdead D) ->
  PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)) ->
  CNFREE D W (CFG fxk (cn_pc CN_FREE) regs mem md).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HB HR HSL HM Ho Hr Hpg Hnz
  HHB.
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, r, ownl, st1, st2, st3, o1, o2, o0.
split; [reflexivity|].
exact (conj HB (conj HR (conj HSL (conj HM (conj Ho (conj Hr (conj Hpg (conj Hnz HHB)))))))).
Qed.
Lemma cn9_mk_same1 : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNB D fxk ly S Hp W regs mem md k 6 ->
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RS1); (10%bv, cn_d1 D); (11%bv, cn_d2 D); (19%bv, cn_d3 D);
                                (20%bv, 0); (21%bv, 1); (22%bv, r3); (23%bv, 0); (24%bv, 0); (25%bv, cn_d1 D);
                                (26%bv, r1)]) ->
  cn_slots D W mem r1 r2 -> r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S -> 0 = cn_ranz D o1 o2 o0 ->
  cn_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  cn_fo D W mem Lam o1 (cn_d1 D) (Some (t, D1)) -> cn_fo D W mem Lam o2 (cn_d2 D) (Some (t, D2)) ->
  cn_fo D W mem Lam o0 (cn_d3 D) (Some (t, D3)) ->
  CNMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  ck_read (ci_x D) = Some t -> PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)) ->
  cn_ex_same1 D W (CFG fxk (SIGMA AS_same) regs mem md).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HB HR HSL H1 H2 H3 Hpg Hz Hrd
  F1 F2 F3 HM Ek HHB.
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, t, D1, D2, D3, o1, o2, o0.
split; [reflexivity|].
exact (conj HB (conj HR (conj HSL (conj H1 (conj H2 (conj H3 (conj Hpg (conj Hz (conj Hrd
  (conj F1 (conj F2 (conj F3 (conj HM (conj Ek HHB)))))))))))))).
Qed.
Lemma cn9_mk_same2 : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNB D fxk ly S Hp W regs mem md k 6 ->
  cn_regsat regs (cn_core D ++ [(1%bv, cn_pc CN_RS2); (10%bv, cn_d1 D); (11%bv, cn_d3 D); (19%bv, cn_d3 D);
                                (20%bv, 0); (21%bv, 1); (22%bv, r3); (23%bv, 0); (24%bv, 0); (25%bv, cn_d1 D);
                                (26%bv, r1)]) ->
  cn_slots D W mem r1 r2 -> r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  cn_prog D (cn_cevs D r1 r2 r3 ++ cn_revs3 D o1 o2 o0) S -> 0 = cn_ranz D o1 o2 o0 ->
  cn_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  cn_fo D W mem Lam o1 (cn_d1 D) (Some (t, D1)) -> cn_fo D W mem Lam o2 (cn_d2 D) (Some (t, D2)) ->
  cn_fo D W mem Lam o0 (cn_d3 D) (Some (t, D3)) ->
  CNMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  ck_read (ci_x D) = Some t -> PresetHullBudget.hull_budget S (cn_hrest_rd0 (ci_x D)) ->
  cn_ex_same2 D W (CFG fxk (SIGMA AS_same) regs mem md).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HB HR HSL H1 H2 H3 Hpg Hz Hrd
  F1 F2 F3 HM Ek HHB.
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, t, D1, D2, D3, o1, o2, o0.
split; [reflexivity|].
exact (conj HB (conj HR (conj HSL (conj H1 (conj H2 (conj H3 (conj Hpg (conj Hz (conj Hrd
  (conj F1 (conj F2 (conj F3 (conj HM (conj Ek HHB)))))))))))))).
Qed.

(* ---- CA9: from the compare cut to the free cut (the flag set, g_ran_out set, or no tree read) or to the first
   `same` call state ---- *)
Theorem cn_cmp_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  CNPRE D -> CNCMP D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 ->
  P mem ->
  SRr' SEGS RZ W (CFG fxk (cn_pc CN_CMP) regs mem md)
    (fun W' c' => (CNFREE D W' c' \/ cn_ex_same1 D W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & Hpg & Hranz & Hrds & Hfo1 & Hfo2 & Hfo3 & HM & HRES1 & HRES2 & HRES3 &
  HHB).
pose proof (cn9_S1_rng D fxk ly S Hp W regs mem md k 6 HB) as (Hsp0 & Hhi & H47 & Hal16 & Hal32 & HS1a & HS1b & _).
pose proof asan_consts as (C1 & _).
assert (ESTK : STK_check_no_overread = 27424) by reflexivity.
assert (G24 : getr regs 24%bv = w64 (VAL (A_HI 9))) by (apply (cn_regsat_get _ _ _ _ HR); cn9_in).
assert (U9 : bv_unsigned (w64 (cn_S1 D)) = cn_S1 D) by (unfold w64; apply unsigned_lit_small; lia).
(* the hand steps up to the ran-out call are plain SRr; the call and the rest at wle' SEGS RZ (Cno102A_Ro.v's lift) *)
apply (cn_srrG_lift (wle' SEGS RZ) (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)).
(* 1048: lbu a0, -0x558(s8) *)
destruct (cn9_own_byte W mem) as (b & Hb).
unfold CN_CMP.
apply (cn_hs_lbu0 W fxk regs mem md _ 1048 1052 (cn9_pw 1048) 10%bv 24%bv 2728%bv pi_g_own_ran_out b);
  [cn9_lst | cn9_lst | reflexivity | lia | reflexivity | exact (cn9_own_addr regs G24) | exact Hb |].
intros X1.
(* the cut's ledger at own = 0: g_own_ran_out holds 0 (PRH_Base.prh_ledger_own), so the byte read is 0 and the
   fall-through of 1052 (1056: ld s9, CN_FREE with r = 1 and ownl = the byte <> 0) is REFUTED *)
assert (Hb0 : bv_unsigned b = 0).
{ pose proof HM as (_ & _ & _ & HLED & _).
  exact (cn9_own_val W mem b 0 Hb
    (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) 0 HLED)). }
(* 1052: beqz a0 taken: the flag is clear *)
apply (cn_hs_beqz0 W fxk _ mem _ _ 1052 (cn9_pw 1052) 10%bv 416%bv true);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia | ro_getr; rewrite ro_getr0, Hb0; reflexivity |].
intros X2. cn9_pc 1468.
(* 1468: mv s8, s9; 1472: jal fuzz_alloc_ran_out *)
apply (cn_hs_addi0 W fxk _ mem _ _ 1468 1472 (cn9_pw 1468) 24%bv 25%bv 0%bv);
  [cn9_lst | cn9_lst | reflexivity | lia | reflexivity |].
intros X3.
apply (cn_hs_call W fxk _ mem _ _ 1472 1476 AS_fuzz_alloc_ran_out); [cn9_lst | lia | reflexivity |].
intros X4. apply SRr_ret. cbv beta.
lazymatch goal with |- SRrG _ _ _ (cn_cfg _ _ ?R _ ?M) _ =>
  assert (HR3 : cn_regsat R (cn_core D ++ [(1%bv, cn_pc CN_RORET); (19%bv, cn_d3 D); (20%bv, rc3); (21%bv, 1);
    (22%bv, r3); (23%bv, rc1); (24%bv, rc2); (25%bv, rc2); (26%bv, r1)])) by (cn9_rs HR);
  assert (HB3 : CNB D fxk ly S Hp W R mem M k 6)
    by (apply (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly S Hp W regs); [repeat apply cn9_base_md; exact HB
        | ro_getr; reflexivity | ro_getr; reflexivity]);
  eapply (SRrG_bind SEGS (wle' SEGS RZ) (wle'_trans SEGS RZ));
  [ apply (cn_ro_callR B ARx LAWS IMG HRO (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)
      P PCALL CTX0 D fxk ly S Hp W R mem M k 6 Lam peak cnt ran 0 3 r1 r2 r3 st1 st2 st3 CN_RORET HPRE);
    [ cbv [cn_ro_rets CN_RORET In]; repeat (first [left; reflexivity | right]) | exact HB3
    | exact (cn9_rs_app_l _ _ _ HR3) | apply (cn_regsat_get _ _ _ _ HR3); cn9_in | exact HSL | exact HM | exact HPM ]
  | ]
end.
(* the three free-order ties across the ran-out call (the hand steps before it keep W and mem) *)
intros W' c' _ (ly' & regs' & mem' & md' & k' & -> & HB' & HAP & H10 & Hab & HSL' & HM' & HK1 & HK2 & HK3 & HPM').
specialize (HK1 o1 Hfo1). specialize (HK2 o2 Hfo2). specialize (HK3 o0 Hfo3).
lazymatch type of HAP with aregs_preserved ?R _ =>
  assert (HR' : cn_regsat regs' (cn_core D ++ [(19%bv, cn_d3 D); (20%bv, rc3); (21%bv, 1); (22%bv, r3);
    (23%bv, rc1); (24%bv, rc2); (25%bv, rc2); (26%bv, r1)]))
    by (apply (cn_regsat_pres R regs'); [cn9_rs HR3 | exact HAP | cn9_cs])
end.
assert (G9' : getr regs' 9%bv = w64 (cn_S1 D)) by (apply (cn_regsat_get _ _ _ _ HR'); cn9_in).
(* no call after this point: the plain hand steps, lifted *)
apply (SRr_SRrG SEGS (wle' SEGS RZ) (wle_wle' SEGS RZ)).
(* 1476: ld s9, 0x38(s1) *)
apply (cn_hs_ld0 W' fxk regs' mem' md' _ 1476 1480 (cn9_pw 1476) 25%bv 9%bv 56%bv (cn_S1 D + 56) (cn_d1 D));
  [cn9_lst | cn9_lst | reflexivity | lia | reflexivity | rewrite G9', U9; cn9_bsv; lia | lia | lia
  | exact (cn9_slot D W' mem' r1 r2 56 (cn_d1 D) HSL' ltac:(cn9_in)) |].
intros X5.
assert (Hran : ran = 0 \/ ran = 1).
{ pose proof HM' as (_ & _ & _ & HL' & _).
  exact (proj2 (proj2 (proj2 (proj2 (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL'))))). }
destruct Hran as [-> | ->].
2:{ (* 1480: bnez a0 taken: g_ran_out is 1; CN_FREE with r = 1, ownl = 0 (the byte read at 1048) *)
  apply (cn_hs_bnez0 W' fxk _ mem' _ _ 1480 (cn9_pw 1480) 10%bv 7772%bv false);
    [cn9_lst | cn9_lst | lia | cn9_bsv; lia | ro_getr; rewrite ro_getr0, H10; reflexivity |].
  intros X6. cn9_pc 1060.
  apply SRr_ret. split; [left | exact HPM'].
  apply (cn9_mk_free D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt 1 r1 r2 r3 1 0 st1 st2 st3 o1 o2 o0).
  - apply (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly' S Hp W' regs'); [repeat apply cn9_base_md; exact HB'
    | ro_getr; reflexivity | ro_getr; reflexivity].
  - cn9_rs HR'.
  - exact HSL'.
  - exact HM'.
  - lia.
  - left. split; [reflexivity | right; reflexivity].
  - intros _. exact (conj Hr1 (conj Hr2 (conj Hr3 (conj Hpg (conj Hranz (conj Hrds (conj HK1 (conj HK2 HK3)))))))).
  - (* the refused-copy arm: this exit has ownl = 0 *)
    intros Hn. exfalso. exact (Hn eq_refl).
  - exact HHB. }
(* 1480: bnez a0 falls through: g_ran_out is 0, so every reading is the grammar's (cn_res) *)
apply (cn_hs_bnez0 W' fxk _ mem' _ _ 1480 (cn9_pw 1480) 10%bv 7772%bv true);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia | ro_getr; rewrite ro_getr0, H10; reflexivity |].
intros X6. cn9_pc 1484.
revert HRES1 HRES2 HRES3. unfold cn_res. destruct (ck_read (ci_x D)) as [t|] eqn:Eck; intros HRES1 HRES2 HRES3.
- (* the input is read: rc1 = rc2 = rc3 = 0, three trees t *)
  destruct (HRES1 eq_refl) as [-> (D1 & ->)]. destruct (HRES2 eq_refl) as [-> (D2 & ->)].
  destruct (HRES3 eq_refl) as [-> (D3 & ->)].
  (* 1484: bnez s7; 1488: bnez s8 (both 0) *)
  apply (cn_hs_bnez0 W' fxk _ mem' _ _ 1484 (cn9_pw 1484) 23%bv 44%bv true);
    [cn9_lst | cn9_lst | lia | cn9_bsv; lia
    | ro_getr; rewrite ro_getr0, (cn_regsat_get _ _ 23%bv 0 HR' ltac:(cn9_in)); reflexivity |].
  intros X7. cn9_pc 1488.
  apply (cn_hs_bnez0 W' fxk _ mem' _ _ 1488 (cn9_pw 1488) 24%bv 20%bv true);
    [cn9_lst | cn9_lst | lia | cn9_bsv; lia
    | ro_getr; rewrite ro_getr0, (cn_regsat_get _ _ 24%bv 0 HR' ltac:(cn9_in)); reflexivity |].
  intros X8. cn9_pc 1492.
  (* 1492: mv a0, s9; 1496: ld a1, 0x30(s1); 1500: jal same *)
  apply (cn_hs_addi0 W' fxk _ mem' _ _ 1492 1496 (cn9_pw 1492) 10%bv 25%bv 0%bv);
    [cn9_lst | cn9_lst | reflexivity | lia | reflexivity |].
  intros X9.
  apply (cn_hs_ld0 W' fxk _ mem' _ _ 1496 1500 (cn9_pw 1496) 11%bv 9%bv 48%bv (cn_S1 D + 48) (cn_d2 D));
    [cn9_lst | cn9_lst | reflexivity | lia | reflexivity | ro_getr; rewrite G9', U9; cn9_bsv; lia | lia | lia
    | exact (cn9_slot D W' mem' r1 r2 48 (cn_d2 D) HSL' ltac:(cn9_in)) |].
  intros X10.
  apply (cn_hs_call W' fxk _ mem' _ _ 1500 1504 AS_same); [cn9_lst | lia | reflexivity |].
  intros X11. apply SRr_ret. split; [right | exact HPM'].
  apply (cn9_mk_same1 D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0).
  + apply (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly' S Hp W' regs'); [repeat apply cn9_base_md; exact HB'
    | ro_getr; reflexivity | ro_getr; reflexivity].
  + cn9_rs HR'.
  + exact HSL'.
  + exact Hr1.
  + exact Hr2.
  + exact Hr3.
  + exact Hpg.
  + exact Hranz.
  + exact Hrds.
  + exact HK1.
  + exact HK2.
  + exact HK3.
  + exact HM'.
  + exact Eck.
  + exact HHB.
- (* the grammar refuses the input: rc1 = rc2 = rc3 = -1, the structs zero *)
  destruct (HRES1 eq_refl) as [-> ->]. destruct (HRES2 eq_refl) as [-> ->]. destruct (HRES3 eq_refl) as [-> ->].
  (* 1484: bnez s7 taken (rc1 = -1) *)
  apply (cn_hs_bnez0 W' fxk _ mem' _ _ 1484 (cn9_pw 1484) 23%bv 44%bv false);
    [cn9_lst | cn9_lst | lia | cn9_bsv; lia
    | ro_getr; rewrite ro_getr0, (cn_regsat_get _ _ 23%bv (-1) HR' ltac:(cn9_in)); reflexivity |].
  intros X7. cn9_pc 1528.
  (* 1528: bne s7, s4; 1532: bne s8, s4 fall through (rc1 = rc2 = rc3): the abort at 1544 is not reached *)
  apply (cn9_hs_bne W' fxk _ mem' _ _ 1528 (cn9_pw 1528) 23%bv 20%bv 16%bv true);
    [cn9_lst | cn9_lst | lia | cn9_bsv; lia
    | ro_getr; rewrite (cn_regsat_get _ _ 23%bv (-1) HR' ltac:(cn9_in)), (cn_regsat_get _ _ 20%bv (-1) HR' ltac:(cn9_in));
      reflexivity |].
  intros X8. cn9_pc 1532.
  apply (cn9_hs_bne W' fxk _ mem' _ _ 1532 (cn9_pw 1532) 24%bv 20%bv 12%bv true);
    [cn9_lst | cn9_lst | lia | cn9_bsv; lia
    | ro_getr; rewrite (cn_regsat_get _ _ 24%bv (-1) HR' ltac:(cn9_in)), (cn_regsat_get _ _ 20%bv (-1) HR' ltac:(cn9_in));
      reflexivity |].
  intros X9. cn9_pc 1536.
  (* 1536: mv s5, zero; 1540: j CN_FREE (r = 0) *)
  apply (cn_hs_addi0 W' fxk _ mem' _ _ 1536 1540 (cn9_pw 1536) 21%bv 0%bv 0%bv);
    [cn9_lst | cn9_lst | reflexivity | lia | reflexivity |].
  intros X10.
  apply (cn_hs_j0 W' fxk _ mem' _ _ 1540 1060 (cn9_pw 1540) 2096672%bv); [cn9_lst | cn9_lst | lia | cn9_bsv; lia | lia |].
  intros X11. apply SRr_ret. split; [left | exact HPM'].
  apply (cn9_mk_free D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt 0 r1 r2 r3 0 0 None None None o1 o2 o0).
  + apply (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly' S Hp W' regs'); [repeat apply cn9_base_md; exact HB'
    | ro_getr; reflexivity | ro_getr; reflexivity].
  + cn9_rs HR'.
  + exact HSL'.
  + exact HM'.
  + lia.
  + right. split; [reflexivity | split; reflexivity].
  + intros _. exact (conj Hr1 (conj Hr2 (conj Hr3 (conj Hpg (conj Hranz (conj Hrds (conj HK1 (conj HK2 HK3)))))))).
  + intros Hn. exfalso. exact (Hn eq_refl).
  + exact HHB.
Qed.

(* ---- THE `same` CALL (callee entry, ra = one of the two return sites): aj_call_xWR at R := wle' SEGS RZ over
   tsame_specX at n = DOC_D for any float state (a non-crossing text: its plain SRr and fpostm lift into the rule's R
   form by SRr_SRrG and apost_base_x_R_lift at wle_wle'), with a0 = d1 and a1 = d2 or d3, both trees t of the readings,
   the caller's journal REBASED from its budget to the empty one (same is a fixed-trace text). The text's `S' = S` and
   its kept Hp, blocks and ledger (the same most / own) carry every cut fact, the budget wk and the three free-order
   ties by cn_call_keepR (which unbases); a0 = 1 by cn9_same_one; the text's guarded live-stack premise is refuted (d1
   below the callee's sp, cn9_dlo). ---- *)
(* the two return sites: code words of the listing, below the ceiling (fpre's raZ bound), a closed lemma *)
Lemma cn9_same_ret_ok : forall ret, In ret cn9_same_rets ->
  4096 <= cn_pc ret < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cn_pc ret)) /\ 0 <= ret < 2 ^ 28.
Proof.
intros ret Hin. pose proof (cni_base B IMG) as HB. pose proof cn_off_val as HO.
assert (H : forall kk, 0 <= kk < 2 ^ 40 -> match plookup A_prog_tpi_cno kk with Some _ => true | None => false end = true ->
  BASE + kk < YM05.alloc_ceiling) by (intros kk Hk Hl; exact (@pa_slot_lt_ceil_b _ _ PL_cno_A PA kk Hk Hl)).
unfold cn_pc, w64. replace (BASE + CN_OFF + ret) with (BASE + (CN_OFF + ret)) by lia.
cbv [cn9_same_rets CN_RS1 CN_RS2 In] in Hin.
destruct Hin as [<- | [<- | []]]; (split; [split; [rewrite HB; vm_compute; discriminate | apply H;
  [rewrite HO; lia | vm_compute; reflexivity]] | split; [apply ret_ok_codeptr_v; [rewrite HO; lia | vm_compute; reflexivity] | lia]]).
Qed.

Lemma cn9_same_call : forall P, srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k wk Lam peak cnt own r1 r2 r3 st1 st2 st3 t D1 Db pb ret,
  CNPRE D -> In ret cn9_same_rets -> CNB D fxk ly S Hp W regs mem md k wk ->
  cn_regsat regs (cn_core D) -> getr regs 1%bv = w64 (cn_pc ret) ->
  getr regs 10%bv = w64 (cn_d1 D) -> getr regs 11%bv = w64 pb ->
  cn_slots D W mem r1 r2 -> CNMID D ly S Hp W mem Lam peak cnt 0 own 3 r1 r2 r3 st1 st2 st3 ->
  st1 = Some (t, D1) -> ((pb = cn_d2 D /\ st2 = Some (t, Db)) \/ (pb = cn_d3 D /\ st3 = Some (t, Db))) ->
  P mem ->
  SRr' SEGS RZ W (CFG fxk (SIGMA AS_same) regs mem md) (fun W' c' => exists ly' regs' mem' md' k',
    c' = CFG fxk (cn_pc ret) regs' mem' md' /\ CNB D fxk ly' S Hp W' regs' mem' md' k' wk /\
    aregs_preserved regs regs' /\ getr regs' 10%bv = w64 1 /\ ablocks B ly' S = ablocks B ly S /\
    cn_slots D W' mem' r1 r2 /\ CNMID D ly' S Hp W' mem' Lam peak cnt 0 own 3 r1 r2 r3 st1 st2 st3 /\
    (forall o, cn_fo D W mem Lam o (cn_d1 D) st1 -> cn_fo D W' mem' Lam o (cn_d1 D) st1) /\
    (forall o, cn_fo D W mem Lam o (cn_d2 D) st2 -> cn_fo D W' mem' Lam o (cn_d2 D) st2) /\
    (forall o, cn_fo D W mem Lam o (cn_d3 D) st3 -> cn_fo D W' mem' Lam o (cn_d3 D) st3) /\ P mem').
Proof.
intros P PCALL D fxk ly S Hp W regs mem md k wk Lam peak cnt own r1 r2 r3 st1 st2 st3 t D1 Db pb ret
  HPRE Hret HB HC R1 R10 R11 HSL HM E1 Hpb HPM.
pose proof (cn9_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (Hsp0 & Hhi & H47 & Hal16 & Hal32 & HS1a & HS1b & _).
pose proof asan_consts as (C1 & _).
assert (ESTK : STK_check_no_overread = 27424) by reflexivity.
assert (ESM : STK_same DOC_D = 12544) by reflexivity.
destruct (cn9_same_ret_ok ret Hret) as ((Hr0 & Hrc) & Hrok & Hr28).
destruct (cn_chainR B ARx (wle' SEGS RZ) CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB) as (ch1 & Hch1).
pose proof HB as (Hz & Hk & (WS & HJ & _) & HF & HSV & R3 & R4 & HROD).
destruct (cn_entry_facts B ARx CTX0 D HPRE) as (_ & _ & _ & _ & _ & _ & _ & Hgp0 & Htp0 & _).
assert (G2 : getr regs 2%bv = w64 (cn_S1 D)) by (apply (cn_regsat_get _ _ _ _ HC); cn9_in).
assert (G8 : getr regs 8%bv = w64 (cn_sp0 D)) by (apply (cn_regsat_get _ _ _ _ HC); cn9_in).
assert (Hsp : spZ regs = cn_S1 D) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = cn_sp0 D) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regs = cn_pc ret) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
pose proof HM as (_ & _ & _ & HLED & _ & _ & _ & _ & O1 & O2 & O3 & Do1 & Do2 & Do3 & _).
(* the two trees, their depth and their footprints *)
assert (HT1 : prhex_tree ly S Lam W regs mem (cn_d1 D) t D1).
{ subst st1. exact (cn9_tree D fxk ly S Hp W regs mem md k wk Lam (cn_d1 D) t D1 HB (or_introl eq_refl) O1 Do1). }
assert (HTb : prhex_tree ly S Lam W regs mem pb t Db).
{ destruct Hpb as [(-> & ->) | (-> & ->)].
  - exact (cn9_tree D fxk ly S Hp W regs mem md k wk Lam (cn_d2 D) t Db HB (or_intror (or_introl eq_refl)) O2 Do2).
  - exact (cn9_tree D fxk ly S Hp W regs mem md k wk Lam (cn_d3 D) t Db HB (or_intror (or_intror eq_refl)) O3 Do3). }
assert (Hdep : (PjTree.depth t <= DOC_D)%nat).
{ subst st1. destruct Do1 as [_ Hd]. exact (cn9_depth t Hd). }
assert (Hf1 : forall z, PRH_Reader.pj_footR (cn_d1 D) D1 z -> ~ (spZ regs - STK_same DOC_D <= z < spZ regs)).
{ intros z Hz'. exact (cn9_foot D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 own 3 r1 r2 r3 st1 st2 st3 (cn_d1 D) t
    D1 z HB HM Hsp (or_introl (conj eq_refl E1)) Hz'). }
assert (Hfb : forall z, PRH_Reader.pj_footR pb Db z -> ~ (spZ regs - STK_same DOC_D <= z < spZ regs)).
{ intros z Hz'. destruct Hpb as [(-> & E2) | (-> & E3)].
  - exact (cn9_foot D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 own 3 r1 r2 r3 st1 st2 st3 (cn_d2 D) t Db z
      HB HM Hsp (or_intror (or_introl (conj eq_refl E2))) Hz').
  - exact (cn9_foot D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 own 3 r1 r2 r3 st1 st2 st3 (cn_d3 D) t Db z
      HB HM Hsp (or_intror (or_intror (conj eq_refl E3))) Hz'). }
(* tsame_specX's guarded live-stack premise: its guard `spZ regs <= d1` is false, d1 lies in the fake frame below
   alloc_ceiling and the callee's sp cn_S1 D on the real stack above it *)
assert (HUP : spZ regs <= cn_d1 D -> YGcallStackUp.astack_up_x SEGS ly W (spZ regs) mem).
{ intros Hle. exfalso.
  pose proof (cn9_dlo D fxk ly S Hp W regs mem md k wk (cn_d1 D) HB (or_introl eq_refl)) as Hd56.
  rewrite Hsp in Hle. clear - Hle Hd56 Hsp0 HS1b ESTK. lia. }
unfold cn_cfg, w64.
eapply SRr'_bind.
{ apply (@aj_call_xWR fxk rc SK SEGS B prh_pst ARx cf_head LAWS pa_segs_low (wle' SEGS RZ) (wle'_refl SEGS RZ)
    (wle'_trans SEGS RZ) W regs mem (SIGMA AS_same)
    STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D)
    (ci_md D) [(CN_CID, ci_fpos D)] ly S Hp md k (STK_same DOC_D) 0 [] (cn_S1 D - cn_sp0 D) (w64 (cn_pc ret)) ch1
    (fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       (t = t /\ getr regs' 10 = w64 1 \/ t <> t /\ getr regs' 10 = w64 0) /\
       PRH_Reader.pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) (cn_d1 D) t D1 /\
       PRH_Reader.pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) pb t Db /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ 0 (ci_most D) own))).
  - (* the journal at its budget, rebased: the entry's depot moved to the current one *)
    exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HJ).
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - exact Hrok.
  - unfold w64. rewrite unsigned_lit_small by lia. exact Hr0.
  - replace (cn_sp0 D + (cn_S1 D - cn_sp0 D)) with (cn_S1 D) by lia. rewrite Hs0. exact Hch1.
  - intros HAFN _.
    assert (HFP : fpre (fx := fxk) B ARx (STK_same DOC_D) ly S Hp W regs mem md ch1).
    { split; [exact HAFN|]. split; [exact HROD|]. split; [rewrite Hsp; lia|].
      split; [rewrite Hraz; exact Hrc | exact Hz]. }
    (* the plain text, lifted into the rule's relation *)
    apply (SRr_SRrG SEGS (wle' SEGS RZ) (wle_wle' SEGS RZ)).
    eapply SRr_mono; [exact (HSAME fxk ly S Hp W regs mem md ch1 (cn_d1 D) pb t t D1 Db Lam peak cnt SIZE_MAXZ 0
      (ci_most D) own HFP HUP R10 R11 HT1 HTb Hdep Hf1 Hfb HLED)|].
    intros W' c' _ HPOST. apply (fpostW_x_of_apostR (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ)).
    apply (apost_base_x_R_lift (SK := SK) SEGS B prh_pst ARx (wle' SEGS RZ) (wle_wle' SEGS RZ)). exact HPOST.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & (HQ & HMN)).
destruct HQ as (_ & Hres & _ & _ & -> & -> & HAB & HL2).
rewrite Z.add_0_r in HJ1. replace (cn_sp0 D + (cn_S1 D - cn_sp0 D)) with (cn_S1 D) in HJ1 by lia.
rewrite !Z.add_0_r in HJ1.
assert (HK1 : 0 <= STK_same DOC_D) by lia.
assert (HK2 : STK_same DOC_D + (cn_sp0 D - cn_S1 D) <= STK_check_no_overread) by lia.
(* HJ2 is the rebased journal from the entry: cn_call_keepR unbases it at the cut's budget *)
destruct (cn_call_keepR B ARx LAWS IMG (wle' SEGS RZ) CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 own 3 r1 r2
  r3 st1 st2 st3 (STK_same DOC_D) ly2 W2 regs2 mem2 md2 k1 HPRE HB HC HSL HM HK1 HK2 HJ2 HJ1 HP2 HAB HL2)
  as (HB2 & HSL2 & HM2 & HFo1 & HFo2 & HFo3).
apply SRr'_ret. exists ly2, regs2, mem2, md2, (k + k1).
split; [reflexivity|]. split; [exact HB2|]. split; [exact HP2|].
split; [exact (cn9_same_one t t regs2 Hres eq_refl)|]. split; [exact HAB|].
split; [exact HSL2|]. split; [exact HM2|].
split; [exact HFo1|]. split; [exact HFo2|]. split; [exact HFo3|].
exact (PCALL mem mem2 HMN HPM).
Qed.

(* ---- THE FIRST `same` STEP: the call (d1, d2), then 1504 beqz a0 falls through (a0 = 1: the abort edge at 1504
   REFUTED by cn9_same_one), 1508 bnez s4 falls through (rc3 = 0), the second call state ---- *)
Theorem cn_same1_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNPRE D -> cn_at_same1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 -> P mem ->
  SRr' SEGS RZ W (CFG fxk (SIGMA AS_same) regs mem md) (fun W' c' => cn_ex_same2 D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & Hpg & Hranz & Hrds & Hfo1 & Hfo2 & Hfo3 & HM & Eck & HHB).
eapply SRr'_bind.
{ apply (cn9_same_call P PCALL D fxk ly S Hp W regs mem md k 6 Lam peak cnt 0 r1 r2 r3
    (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) t D1 D2 (cn_d2 D) CN_RS1 HPRE);
  [ cbv [cn9_same_rets In]; left; reflexivity | exact HB | exact (cn9_rs_app_l _ _ _ HR)
  | apply (cn_regsat_get _ _ _ _ HR); cn9_in | apply (cn_regsat_get _ _ _ _ HR); cn9_in
  | apply (cn_regsat_get _ _ _ _ HR); cn9_in | exact HSL | exact HM | reflexivity | left; split; reflexivity
  | exact HPM ]. }
(* the three free-order ties across the call (the hand steps after it keep W' and mem') *)
intros W' c' _ (ly' & regs' & mem' & md' & k' & -> & HB' & HAP & H10 & Hab & HSL' & HM' & HK1 & HK2 & HK3 & HPM').
specialize (HK1 o1 Hfo1). specialize (HK2 o2 Hfo2). specialize (HK3 o0 Hfo3).
assert (HR' : cn_regsat regs' (cn_core D ++ [(19%bv, cn_d3 D); (20%bv, 0); (21%bv, 1); (22%bv, r3);
    (23%bv, 0); (24%bv, 0); (25%bv, cn_d1 D); (26%bv, r1)]))
  by (apply (cn_regsat_pres regs regs'); [cn9_rs HR | exact HAP | cn9_cs]).
(* no call after this point: the plain hand steps, lifted *)
apply (SRr_SRr' SEGS RZ).
unfold CN_RS1.
(* 1504: beqz a0 falls through: a0 = 1 *)
apply (cn_hs_beqz0 W' fxk regs' mem' md' _ 1504 (cn9_pw 1504) 10%bv 40%bv false);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia | rewrite ro_getr0, H10; reflexivity |].
intros X1. cn9_pc 1508.
(* 1508: bnez s4 falls through: rc3 = 0 *)
apply (cn_hs_bnez0 W' fxk _ mem' _ _ 1508 (cn9_pw 1508) 20%bv 20%bv true);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia
  | rewrite ro_getr0, (cn_regsat_get _ _ 20%bv 0 HR' ltac:(cn9_in)); reflexivity |].
intros X2. cn9_pc 1512.
(* 1512: mv a0, s9; 1516: mv a1, s3; 1520: jal same *)
apply (cn_hs_addi0 W' fxk _ mem' _ _ 1512 1516 (cn9_pw 1512) 10%bv 25%bv 0%bv);
  [cn9_lst | cn9_lst | reflexivity | lia | reflexivity |].
intros X3.
apply (cn_hs_addi0 W' fxk _ mem' _ _ 1516 1520 (cn9_pw 1516) 11%bv 19%bv 0%bv);
  [cn9_lst | cn9_lst | reflexivity | lia | reflexivity |].
intros X4.
apply (cn_hs_call W' fxk _ mem' _ _ 1520 1524 AS_same); [cn9_lst | lia | reflexivity |].
intros X5. apply SRr_ret. split; [| exact HPM'].
apply (cn9_mk_same2 D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0).
- apply (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly' S Hp W' regs'); [repeat apply cn9_base_md; exact HB'
  | ro_getr; reflexivity | ro_getr; reflexivity].
- cn9_rs HR'.
- exact HSL'.
- exact Hr1.
- exact Hr2.
- exact Hr3.
- exact Hpg.
- exact Hranz.
- exact Hrds.
- exact HK1.
- exact HK2.
- exact HK3.
- exact HM'.
- exact Eck.
- exact HHB.
Qed.

(* ---- THE SECOND `same` STEP: the call (d1, d3), then 1524 beqz a0 falls through (a0 = 1: the abort edge at 1524
   REFUTED by cn9_same_one), 1528 bne s7, s4 and 1532 bne s8, s4 fall through (rc1 = rc2 = rc3 = 0: the abort edges
   at 1528 / 1532 REFUTED), 1536 mv s5, zero, 1540 j CN_FREE: the free cut with r = 0, ownl = 0 ---- *)
Theorem cn_same2_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNPRE D -> cn_at_same2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 -> P mem ->
  SRr' SEGS RZ W (CFG fxk (SIGMA AS_same) regs mem md) (fun W' c' => CNFREE D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & Hr1 & Hr2 & Hr3 & Hpg & Hranz & Hrds & Hfo1 & Hfo2 & Hfo3 & HM & Eck & HHB).
eapply SRr'_bind.
{ apply (cn9_same_call P PCALL D fxk ly S Hp W regs mem md k 6 Lam peak cnt 0 r1 r2 r3
    (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) t D1 D3 (cn_d3 D) CN_RS2 HPRE);
  [ cbv [cn9_same_rets In]; right; left; reflexivity | exact HB | exact (cn9_rs_app_l _ _ _ HR)
  | apply (cn_regsat_get _ _ _ _ HR); cn9_in | apply (cn_regsat_get _ _ _ _ HR); cn9_in
  | apply (cn_regsat_get _ _ _ _ HR); cn9_in | exact HSL | exact HM | reflexivity | right; split; reflexivity
  | exact HPM ]. }
(* the three free-order ties across the call (the hand steps after it keep W' and mem') *)
intros W' c' _ (ly' & regs' & mem' & md' & k' & -> & HB' & HAP & H10 & Hab & HSL' & HM' & HK1 & HK2 & HK3 & HPM').
specialize (HK1 o1 Hfo1). specialize (HK2 o2 Hfo2). specialize (HK3 o0 Hfo3).
assert (HR' : cn_regsat regs' (cn_core D ++ [(19%bv, cn_d3 D); (20%bv, 0); (21%bv, 1); (22%bv, r3);
    (23%bv, 0); (24%bv, 0); (25%bv, cn_d1 D); (26%bv, r1)]))
  by (apply (cn_regsat_pres regs regs'); [cn9_rs HR | exact HAP | cn9_cs]).
(* no call after this point: the plain hand steps, lifted *)
apply (SRr_SRr' SEGS RZ).
unfold CN_RS2.
(* 1524: beqz a0 falls through: a0 = 1 *)
apply (cn_hs_beqz0 W' fxk regs' mem' md' _ 1524 (cn9_pw 1524) 10%bv 20%bv false);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia | rewrite ro_getr0, H10; reflexivity |].
intros X1. cn9_pc 1528.
(* 1528: bne s7, s4; 1532: bne s8, s4 fall through: 0 = 0 *)
apply (cn9_hs_bne W' fxk _ mem' _ _ 1528 (cn9_pw 1528) 23%bv 20%bv 16%bv true);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia
  | rewrite (cn_regsat_get _ _ 23%bv 0 HR' ltac:(cn9_in)), (cn_regsat_get _ _ 20%bv 0 HR' ltac:(cn9_in)); reflexivity |].
intros X2. cn9_pc 1532.
apply (cn9_hs_bne W' fxk _ mem' _ _ 1532 (cn9_pw 1532) 24%bv 20%bv 12%bv true);
  [cn9_lst | cn9_lst | lia | cn9_bsv; lia
  | rewrite (cn_regsat_get _ _ 24%bv 0 HR' ltac:(cn9_in)), (cn_regsat_get _ _ 20%bv 0 HR' ltac:(cn9_in)); reflexivity |].
intros X3. cn9_pc 1536.
(* 1536: mv s5, zero; 1540: j CN_FREE *)
apply (cn_hs_addi0 W' fxk _ mem' _ _ 1536 1540 (cn9_pw 1536) 21%bv 0%bv 0%bv);
  [cn9_lst | cn9_lst | reflexivity | lia | reflexivity |].
intros X4.
apply (cn_hs_j0 W' fxk _ mem' _ _ 1540 1060 (cn9_pw 1540) 2096672%bv); [cn9_lst | cn9_lst | lia | cn9_bsv; lia | lia |].
intros X5. apply SRr_ret. split; [| exact HPM'].
apply (cn9_mk_free D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt 0 r1 r2 r3 0 0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3))
  o1 o2 o0).
- apply (cn_base_matR B ARx LAWS (wle' SEGS RZ) D fxk ly' S Hp W' regs'); [repeat apply cn9_base_md; exact HB'
  | ro_getr; reflexivity | ro_getr; reflexivity].
- cn9_rs HR'.
- exact HSL'.
- exact HM'.
- lia.
- right. split; [reflexivity | split; reflexivity].
- intros _. exact (conj Hr1 (conj Hr2 (conj Hr3 (conj Hpg (conj Hranz (conj Hrds (conj HK1 (conj HK2 HK3)))))))).
- (* the refused-copy arm: this exit has ownl = 0 *)
  intros Hn. exfalso. exact (Hn eq_refl).
- exact HHB.
Qed.

End r9.

(* the audit: each lemma closed under the Section hypotheses (LAWS, IMG, HRO, HSAME) only *)
Print Assumptions cn_cmp_seg.
Print Assumptions cn9_same_call.
Print Assumptions cn_same1_step.
Print Assumptions cn_same2_step.
Print Assumptions cn9_same_one.
Print Assumptions cn9_depth.
Print Assumptions cn9_tree.
Print Assumptions cn9_foot.
Print Assumptions cn9_dlo.
Print Assumptions cn9_hs_bne.
Print Assumptions cn9_own_val.
Check @cn_cmp_seg.
Check @cn_same1_step.
Check @cn_same2_step.
