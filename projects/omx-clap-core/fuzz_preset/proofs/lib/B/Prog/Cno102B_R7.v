(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1165 of its 1242 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_E2.v, with its module paths and module names changed; 736 of its 849 lines of code are new or changed and 1129 lines of the source are left out. *)
(* rule 24: no function proved *)
(* rule 24: proves no function (kind: segment lemma) *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): segment CB7
   Cmp of the re-walk of check_no_overread (cno, entry B' 0x819f0) against the kit's text tcheck_no_overread_specX, lane
   CnoB102rR.CutR7 (sub-lane of CnoB102rR, a Theorem Labs lane; plan, the internal file PLAN-cno-caw-102.md 5.2 row CB7), re-fitted to the kit
   CUT a working branch 7cdbb61b5fa0. The port of image A''s Cno102A_R9.v (lane CnoA102r.CnoA9) to B'.
   INPUTS (by path): the contract lib/B/Prog/Cno102B_Base.v at a working branch 75415fdb6e76
   (blob 20c89a1d4da2; this file never edits it), in its forms over a world relation R: cnb_baseR / cnb_JR (cnb_base /
   cnb_J are their instances at wle), the compare cut cnb_at_cmpR and the free exit cnb_ex_freeR (over cnb_at_freeR),
   both cuts after a free, used at R := wle' SEGS RZ_cf; the B' step kit lib/B/Prog/Cno102B_Ro.v by path
   (lane CnoB102rR.CutRo: cnb_is_*, cnb_pc4 / cnb_pcj, cnb_regsat_get / _pres,
   cnb_entry_facts, cnb_rcslot_agree, ro_getr, and its forms over a world relation R, used here at R := wle' SEGS
   RZ_cf: the hand steps cnb_hs_*R / cnb_stepR, cnb_base_matR, cnb_chainR, cnb_J_rebaseR, cnb_call_keepR (with
   cnb_J_fixedR and cnb_fo_keep inside), cnb_ro_callR); the kit texts at the cut: lib/A/PRH_FnEx.v be1dd5ecaaf6
   (tsame_specX, with `S' = S`, the ledger kept and the guarded premise `spZ regs <= pa -> YGcallStackUp.astack_up_x
   ..`), lib/A/PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_alloc_ran_out_specX), lib/A/PRH_Base.v ef7c8ca98529 (fpre ending in
   frm_zero (fp_csr fx); prh_ledger_own / prh_ledger_bounds / prh_ledger_blocks, the named projections); listing
   lib/B/Listing_prog.v c97cc46b3e13 (slot 201 + off / 4: PCall AS_fuzz_alloc_ran_out 1 at 1140, PCall AS_same 1 at
   1176 / 1204, every other slot of the segment a PW word); engine: YCbqG.v ajournal_xwR (read by the ajxR_*
   projections only) and apost_base_x_R_lift,
   YCbqGcallW.v aj_call_xWR / fpostW_x_of_apostR, YA0nH.v SRr' / wle' / SRrG_bind / SRrG_ret / SRrG_mono / SRr_SRrG /
   wle_wle', YSRrG.v SRr'_bind / SRr'_ret, YGcfRehidePost.v RZ_cf, YSRrMemnorm.v srr_inv_call; PRW_StepKit.v
   0df3991c13f4 (pa_slot_lt_ceil_b).
   THE RE-HIDING MOVE: the compare cut lies after the three parse_noting calls, whose text (tparse_noting_specX) crosses
   a free, so every state of this file holds its journal from entry at wle' SEGS RZ_cf (YGcfRehidePost.RZ_cf, the
   fixed zone): the Base's cnb_baseR at that relation (CNBB below), the Base's cnb_at_cmpR / cnb_ex_freeR at it, and
   this file's cnb_at_same1 / cnb_at_same2 restated in place at it (used only after a free). So every segment
   here concludes SRr' SEGS RZ_cf, and every hand step is the kit's R form at WLE'. tsame_specX and
   tfuzz_alloc_ran_out_specX are NOT crossing texts (unchanged: plain SRr, fpostm at wle): their calls go through the
   call rules' R forms at R := WLE' (aj_call_xWR here, cnb_ro_callR in the kit), the callee's plain conclusion lifted by
   SRr_SRrG and its post by apost_base_x_R_lift at wle_wle'. No world conjunct (ajxR_rel) is read here.
   THE HULL: every state here carries PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)) LAST, the Base's suffix
   of the all-granted events (cnb_hev_all) still to pay after the three readings. Neither callee here changes S
   (`S' = S`) and no hand step touches it, so the conjunct rides unchanged from cnb_at_cmpR to every exit
   (cnb_ex_freeR, cnb_ex_same1, cnb_ex_same2): no payment and no split here.
   THE CODE (DERIVED byte offsets inside cno, the B' disassembly of check_no_overread; registers at CNB_CMP:
   s7 = rc3, s9 = r1, s8 = the auipc hi of g_own_ran_out, s4 / s5 / s6 = d3 / d2 / d1, s1 + 8 = rc1, s1 + 0 = rc2):
     728 lbu a0, 0x140(s8)       the g_own_ran_out byte: 0 by the cut's ledger own = 0 (prh_ledger_own; cnbi_hi, cnbi_own)
     732 beqz a0 -> 1140         always taken: the fall-through 736 (`li s8, 1`, CNB_FREE with r = 1) is REFUTED
     1140 jal fuzz_alloc_ran_out (cnb_ro_callR, ret 1144)   1144 li s8, 1   1148 bnez a0 -> CNB_FREE (r = 1, ran = 1)
     1152 ld a1, 8(s1) (rc1)     1156 ld a2, 0(s1) (rc2)    1160 bnez a1 -> 1220   1164 bnez a2 -> 1192
     1168 mv a0, s6   1172 mv a1, s5   1176 jal same (ret 1180)   1180 ld a2, 0(s1)   1184 ld a1, 8(s1)
     1188 beqz a0 -> 1236 ABORT  1192 bnez s7 -> 1220   1196 mv a0, s6   1200 mv a1, s4   1204 jal same (ret 1208)
     1208 ld a2, 0(s1)   1212 ld a1, 8(s1)   1216 beqz a0 -> 1236 ABORT   1220 bne a1, s7 -> 1236 ABORT
     1224 bne a2, s7 -> 1236 ABORT   1228 mv s8, zero   1232 j CNB_FREE (r = 0)
   With g_ran_out = 0 the base's cnb_res gives every reading: ck_read x = None: rc1 = rc2 = rc3 = -1 and the structs
   zero, so 1160 jumps to 1220 and both bne fall through (rc's equal); ck_read x = Some t: rc_i = 0 and st_i =
   Some (t, D_i), so the walk reaches the two `same` calls, each with equal trees.
   THE REFUTED SITES (never walked): the fall-through 736 of 732 by cnb7_own_byte (the byte reads 0); the abort edges
   1188 and 1216 (beqz a0) by tsame_specX's result disjunct at equal trees, cnb7_same_one (a0 = 1) in cnb_same_call;
   1220 (bne a1, s7) and 1224 (bne a2, s7) by the readings' equal rc's (cnb_res: -1 / -1 / -1 on the None path in
   cnb_cmp_seg, 0 / 0 / 0 after the two calls in cnb_same2_step), 1192 (bnez s7 -> 1220) by rc3 = 0 in
   cnb_same1_step.
   WHAT IS HERE: the call states cnb_at_same1 / cnb_at_same2 (their journal at WLE') and their exits
   cnb_ex_same1 / cnb_ex_same2; cnb_cmp_seg (CNB_CMP -> cnb_ex_freeR \/ cnb_ex_same1); cnb_same_call (one `same` call:
   aj_call_xWR at WLE', the text HSAME for any float state at n = DOC_D lifted into WLE', P across by srr_inv_call, the
   cut's facts by cnb_call_keepR with tsame's S' = S); cnb_same1_step (cnb_ex_same1 -> cnb_ex_same2 \/ cnb_ex_freeR)
   and cnb_same2_step (cnb_ex_same2 -> cnb_ex_freeR, r = 0), every exit at WLE'; this file's hand step cnb7_hs_bne
   (SRr' SEGS RZ_cf).
   THE EVENTS (the Base's cnb_prog, the post-implication form): CB7 makes no model event (fuzz_alloc_ran_out and
   same keep S, `S' = S`), so the compare cut's cnb_prog D (cnb_cevs .. ++ cnb_revs3 D o1 o2 o0) S,
   ran = cnb_ranz D o1 o2 o0 and the structs against the grants (cnb_rds3 D o1 o2 o0 st1 st2 st3: no struct changes
   here) reach every exit unchanged, with the same grants o1 o2 o0 (LAST, the Base's order).
   AT THE CUT: THE WILD BUDGET is 6 = prh_wk F_check_no_overread at every state of this file (cnb_baseR .. WLE' .. k 6):
   both callees are FIXED-trace texts, so each call keeps the walk's budget (the journal rebased to the empty budget,
   aj_call_xWR, unbased at the same WS). THE TREES' FREE ORDER (the Base's cnb_fo for all three structs) is carried
   through the call states cnb_at_same1 / 2 to the free exit's ownl = 0 arm; the calls write only the stack (same's
   frames and the ran-out call's, outside the trees), so cnb_call_keepR moves it (PRH_PjOrder.pj_foR_frame). The free
   exit's ownl <> 0 arm is vacuous: ownl = 0 on every path (the byte at 728 reads 0). tsame_specX's guarded premise
   (spZ regs <= pa -> astack_up_x ..) holds vacuously at both calls: pa = d1 = F + 32 lies in the fake frame, below
   alloc_ceiling (frames_bounds_x), and the callee's sp = s1 lies above entry sp - 192 >= alloc_ceiling + STK - 192
   (cnb7_d1_below_sp).
   Numerals: 728 .. 1240 (DERIVED: byte offsets inside cno); 160 / 176 / 192 / 32 / 16 / 56 / 512 (LENGTH: frame,
   alignment, struct and class-3 frame sizes); 320 (LENGTH: the lbu offset 0x140 of the hi/lo pair, via cnbi_hi); 8 / 0
   (LENGTH: the rc slots); 6 (COUNT: the spent wild budget, cnb_baseR's wk); register numbers and instruction immediates
   (WORD, checked against the listing by computation on closed terms). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base Cno102B_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which sets this flag to false GLOBALLY; lia on the frame / slot arithmetic (the realigned
   sp's residue mod 32) needs it on (Cno102A_Ro.v's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the offsets of this file (DERIVED byte offsets inside check_no_overread, the B' disassembly): the
   ran-out call, the two `same` calls and their return sites ---- *)
Definition CNB7_RO : Z := 1140.      (* 0x81e64 jal fuzz_alloc_ran_out *)
Definition CNB7_RORET : Z := 1144.   (* 0x81e68 li s8, 1 *)
Definition CNB7_SAME1 : Z := 1176.   (* 0x81e88 jal same (d1, d2) *)
Definition CNB7_RS1 : Z := 1180.     (* 0x81e8c ld a2, 0(s1) *)
Definition CNB7_SAME2 : Z := 1204.   (* 0x81ea4 jal same (d1, d3) *)
Definition CNB7_RS2 : Z := 1208.     (* 0x81ea8 ld a2, 0(s1) *)
Definition cnb7_same_rets : list Z := [CNB7_RS1; CNB7_RS2].
(* the two `same` return sites are code slots of the listing: closed checks (the vm_compute guard) *)
Lemma cnb7_rs1_slot :
  match plookup B_prog_tpi_cno (CNB_OFF + 1180) with Some _ => true | None => false end = true.
Proof.
lazymatch goal with |- match plookup B_prog_tpi_cno (CNB_OFF + 1180) with Some _ => true | None => false end = true =>
  vm_compute; reflexivity end.
Qed.
Lemma cnb7_rs2_slot :
  match plookup B_prog_tpi_cno (CNB_OFF + 1208) with Some _ => true | None => false end = true.
Proof.
lazymatch goal with |- match plookup B_prog_tpi_cno (CNB_OFF + 1208) with Some _ => true | None => false end = true =>
  vm_compute; reflexivity end.
Qed.

(* `bne rs1, rs2, imm` (two registers; the kit has the `bnez` form), checked against the listing on a closed term *)
Definition cnb7_is_bne (off : Z) (rs1 rs2 : bv 5) (i : Z) : bool :=
  match plookup B_prog_tpi_cno (CNB_OFF + off) with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (Branch BC_NE rs1' rs2' imm, sz) => (sz =? 4) && bv_eqb rs1' rs1 && bv_eqb rs2' rs2 && (bv_signed imm =? i)
      | _ => false
      end
  | _ => false
  end.

(* ---- small pure pieces ---- *)
Lemma cnb7_rs_app_l : forall regs l1 l2, cnb_regsat regs (l1 ++ l2) -> cnb_regsat regs l1.
Proof. intros regs l1 l2 H. unfold cnb_regsat in *. apply Forall_app in H. exact (proj1 H). Qed.
Lemma cnb7_mv : forall (x : word), v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma cnb7_c_eq_w64 : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> c_eq (w64 x) (w64 y) = true.
Proof.
intros x y H. unfold c_eq, bv_eqb, w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite H. apply Z.eqb_refl.
Qed.
(* a register list's callee-saved check, entry by entry on the closed register numbers *)
Lemma cnb7_csr : forall (r : bv 5),
  ((bv_unsigned r =? 2) || (bv_unsigned r =? 8) || (bv_unsigned r =? 9) ||
   ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27)))%bool = true ->
  acallee_saved (bv_unsigned r).
Proof.
intros r H. unfold acallee_saved.
repeat rewrite orb_true_iff in H. repeat rewrite andb_true_iff in H. rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
(* same trees: tsame_specX's result disjunct gives a0 = 1 *)
Lemma cnb7_same_one : forall (ta tb : PjTree.jv) (regs' : bvmap 5 word),
  (ta = tb /\ getr regs' 10%bv = w64 1 \/ ta <> tb /\ getr regs' 10%bv = w64 0) -> ta = tb ->
  getr regs' 10%bv = w64 1.
Proof. intros ta tb regs' [[_ H] | [Hn _]] He; [exact H | exfalso; exact (Hn He)]. Qed.
(* tsame_specX's depth premise at n = DOC_D from the reading's depth bound (cnb_doc) *)
Lemma cnb7_depth : forall t : PjTree.jv, (PjTree.depth t <= PjGrammar.MAXD)%nat -> (PjTree.depth t <= DOC_D)%nat.
Proof. intros t H. unfold DOC_D. lia. Qed.
(* ---- the tactics of this file ---- *)
(* a closed listing / decode check (VM_COMPUTE GUARD: only on these closed shapes) *)
Ltac cnb7_dec := lazymatch goal with
  | |- cnb_is_addi _ _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_ld _ _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_lbu _ _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_beqz _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_bnez _ _ _ = true => vm_compute; reflexivity
  | |- cnb_is_j _ _ = true => vm_compute; reflexivity
  | |- cnb7_is_bne _ _ _ _ = true => vm_compute; reflexivity
  | |- plookup B_prog_tpi_cno (CNB_OFF + _) = Some (PCall _ _) => first [vm_compute; reflexivity | vm_refl_bv]
  end.
Ltac cnb7_in := solve [unfold cnb_core, cnb_s8; cbn [app In]; repeat (first [left; reflexivity | right])].
(* a register snapshot of the current registers: each entry read off the snapshot HR, or through the updates (ro_getr)
   down to HR's registers *)
Ltac cnb7_rs HR := unfold cnb_regsat, cnb_core, cnb_s8; cbn [app];
  repeat (apply Forall_cons; [cbn [fst snd];
    first [ apply (cnb_regsat_get _ _ _ _ HR); cnb7_in
          | ro_getr; rewrite ?cnb7_mv; ro_getr;
            first [ reflexivity | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in | idtac ] ] |]);
  try apply Forall_nil.
(* every register of the list callee-saved: per entry, the register number evaluated (closed) *)
Ltac cnb7_cs := unfold cnb_core, cnb_s8; cbn [app];
  repeat (apply Forall_cons; [cbn [fst]; apply cnb7_csr; reflexivity |]); apply Forall_nil.

Section k7. Context {rc : YM05.RunCeil}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
(* the world relation after a free (the re-hiding move): the hidden set may grow only inside the fixed zone RZ_cf *)
#[local] Notation WLE' := (wle' SEGS YGcfRehidePost.RZ_cf).
(* the realigned sp lies 160 or 176 below the entry sp (sp0 mod 16 = 0) *)
Lemma cnb7_S1_gap : forall D, cnb_sp0 D mod 16 = 0 ->
  cnb_S1 D + 160 <= cnb_sp0 D <= cnb_S1 D + 176 /\ cnb_S1 D mod 32 = 0.
Proof.
intros D H16. pose proof (cnb_S1_bounds D H16) as (_ & _ & H32). unfold cnb_S1 in *. rewrite cnb_land_m32 in *.
pose proof (Z.mod_pos_bound (cnb_sp0 D - 160) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod (cnb_sp0 D) 16 ltac:(lia)) as E1. pose proof (Z.div_mod (cnb_sp0 D - 160) 32 ltac:(lia)) as E2.
rewrite H16 in E1. split; [lia | exact H32].
Qed.

(* `bne rs1, rs2, imm`: falls through when the registers are equal. Used only after a free (cnb_cmp_seg,
   cnb_same2_step), so it is stated at SRr' SEGS RZ_cf, by the kit's R step cnb_stepR at WLE' *)
Lemma cnb7_hs_bne : forall (W : world SEGS) fxk regs mem md Q off rs1 rs2 i tk ft (z : bool),
  cnb7_is_bne off rs1 rs2 i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs1) (getr regs rs2) = z ->
  (forall X, SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc (if z then ft else tk)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off rs1 rs2 i tk ft z H.
unfold cnb7_is_bne in H.
destruct (plookup B_prog_tpi_cno (CNB_OFF + off)) as [e|] eqn:Hpl; [|discriminate H].
destruct e; try (cbv beta iota in H; discriminate H).
match type of H with context [decode_any ?x] => destruct (decode_any x) as [[ii sz]|] eqn:Hdec; [|discriminate H] end.
destruct ii; try (cbv beta iota in H; discriminate H).
match type of Hdec with decode_any _ = Some (Branch ?c _ _ _, _) => destruct c; try (cbv beta iota in H; discriminate H) end.
cbv beta iota in H.
repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : bv_eqb _ _ = true |- _ => apply ro_bv_eqb_eq in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end; subst.
match type of Hdec with decode_any _ = Some (Branch BC_NE _ _ ?im, _) => rename im into imm end.
intros Ho Hj -> -> Hc HK.
pose proof (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as He.
destruct z.
- apply (cnb_stepR WLE' W fxk regs mem md regs off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_ft fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ _ _ imm Hf He Hdec Hc).
  rewrite (cnb_pc4 off ltac:(lia)). reflexivity.
- apply (cnb_stepR WLE' W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_tk fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ _ _ imm Hf He Hdec Hc).
  unfold btgt. rewrite (cnb_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
Qed.
End k7.

Section r7. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation CFG := (@cnb_cfg SEGS).
(* the world relation after a free (the re-hiding move): the hidden set may grow only inside the fixed zone RZ_cf *)
#[local] Notation WLE' := (wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cnb_img B.
(* the callee texts, for any float state (the kit cut 7cdbb61b5fa0: PRH_FnAlloc.v 4d8aeba047e5 / PRH_FnEx.v
   be1dd5ecaaf6); neither crosses a free, so both stay plain SRr with posts at wle, lifted into WLE' at each call *)
Hypothesis HRO : forall fz : YK11.FPState, @tfuzz_alloc_ran_out_specX fz rc cp prh_img_B RL B_prog_listing PA B ARx SK.
Hypothesis HSAME : forall fz : YK11.FPState, @tsame_specX fz rc cp prh_img_B RL B_prog_listing PA B ARx SK DOC_D.
#[local] Notation CNBPRE := (cnb_pre (fx := fx) B ARx CTX0).
(* every state of this file lies after the parse_noting calls (a free crossed): the base at the re-hiding relation *)
#[local] Notation CNBB := (cnb_baseR (fx := fx) B ARx WLE').
#[local] Notation CNBMID := (cnb_mid B).
(* the compare cut and the free exit lie after a free too: the Base's R forms at the same relation *)
#[local] Notation CNBCMP := (cnb_at_cmpR (fx := fx) B ARx WLE').
#[local] Notation CNBFREE := (cnb_ex_freeR (fx := fx) B ARx WLE').

(* ---- THE TWO `same` CALL STATES (callee entry, ra = the return site): the compare cut's facts with the flag read 0,
   g_ran_out 0 and the input read by the grammar: every reading done, rc1 = rc2 = rc3 = 0 (s7 = rc3, the slots
   s1 + 8 / s1 + 0 = rc1 / rc2), the three trees t, g_own_ran_out 0 through cnb_mid's ledger (ran 0, own 0). The
   readings' grants o1 o2 o0 (the Base's cnb_at_cmpR order): the events since entry (cnb_prog over the granted
   copies and the three readings) and g_ran_out = cnb_ranz of them, which is 0 on this path; the spent wild budget 6
   (cnb_baseR's wk, the compare cut's) with the journal from entry at WLE' (both states lie after a free, so they are
   stated at that relation in place); the three trees' free order (cnb_fo at their grants, the compare cut's, for
   the free exit's ownl = 0 arm; the A' twin's cn_fo); the hull budget at the compare's stage rd0 LAST (the Base's
   cnb_hrest_rd0, the Base's cut order; S is the compare cut's: neither callee changes it).
   Registers: a0 = d1, a1 = d2 (first) or d3 (second), s7 = 0, s8 = 1 (`li s8, 1` at 1144), s9 = r1 ---- *)
Definition cnb_at_same1 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 : Z) (t : PjTree.jv) (D1 D2 D3 : list (Z * Z)) (o1 o2 o0 : option nat) : Prop :=
  CNBB D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [(1%bv, cnb_pc CNB7_RS1); (10%bv, cnb_d1 D); (11%bv, cnb_d2 D); (23%bv, 0);
                                  (24%bv, 1); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 0 /\ cnb_rcslot D W mem 0 0 /\
  r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ 0 = cnb_ranz D o1 o2 o0 /\
  cnb_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  cnb_fo D W mem Lam o1 (cnb_d1 D) (Some (t, D1)) /\ cnb_fo D W mem Lam o2 (cnb_d2 D) (Some (t, D2)) /\
  cnb_fo D W mem Lam o0 (cnb_d3 D) (Some (t, D3)) /\
  CNBMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  ck_read (bi_x D) = Some t /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)).
Definition cnb_at_same2 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 : Z) (t : PjTree.jv) (D1 D2 D3 : list (Z * Z)) (o1 o2 o0 : option nat) : Prop :=
  CNBB D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [(1%bv, cnb_pc CNB7_RS2); (10%bv, cnb_d1 D); (11%bv, cnb_d3 D); (23%bv, 0);
                                  (24%bv, 1); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 0 /\ cnb_rcslot D W mem 0 0 /\
  r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ 0 = cnb_ranz D o1 o2 o0 /\
  cnb_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  cnb_fo D W mem Lam o1 (cnb_d1 D) (Some (t, D1)) /\ cnb_fo D W mem Lam o2 (cnb_d2 D) (Some (t, D2)) /\
  cnb_fo D W mem Lam o0 (cnb_d3 D) (Some (t, D3)) /\
  CNBMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) /\
  ck_read (bi_x D) = Some t /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)).
(* their forward exits, in the base's style *)
Definition cnb_ex_same1 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  c = CFG fxk (SIGMA AS_same) regs mem md /\
  cnb_at_same1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0.
Definition cnb_ex_same2 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  c = CFG fxk (SIGMA AS_same) regs mem md /\
  cnb_at_same2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0.

(* ---- THE STACK AND TREE FACTS the `same` call rests on ---- *)
(* the stack budget: same's window and the realigned frame fit in check_no_overread's (closed, at prh_img_B) *)
Lemma cnb7_stk : STK_same DOC_D + 176 <= STK_check_no_overread.
Proof. apply Z.leb_le. lazymatch goal with |- (STK_same DOC_D + 176 <=? STK_check_no_overread) = true => vm_compute; reflexivity end. Qed.
Lemma cnb7_stk0 : 0 <= STK_same DOC_D.
Proof. apply Z.leb_le. lazymatch goal with |- (0 <=? STK_same DOC_D) = true => vm_compute; reflexivity end. Qed.
(* NAMED PROJECTIONS of the Base's cnb_baseR at WLE' (one place that reads its conjuncts by position) *)
Lemma cnb7_base_frm0 : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  frm_zero (@YK11.fp_csr fxk).
Proof. intros D fxk ly S Hp W regs mem md k wk H. destruct H as (Z0 & _). exact Z0. Qed.
Lemma cnb7_base_J : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  cnb_JR B ARx WLE' D wk ly S Hp W mem md k.
Proof. intros D fxk ly S Hp W regs mem md k wk H. destruct H as (_ & _ & J & _). exact J. Qed.
Lemma cnb7_base_frame : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  cnb_frame D ly S W mem.
Proof. intros D fxk ly S Hp W regs mem md k wk H. destruct H as (_ & _ & _ & F & _). exact F. Qed.
Lemma cnb7_base_gptp : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  getr regs 3 = getr (bi_regs D) 3 /\ getr regs 4 = getr (bi_regs D) 4.
Proof. intros D fxk ly S Hp W regs mem md k wk H. destruct H as (_ & _ & _ & _ & _ & R3 & R4 & _). exact (conj R3 R4). Qed.
Lemma cnb7_base_rod : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Proof. intros D fxk ly S Hp W regs mem md k wk H. destruct H as (_ & _ & _ & _ & _ & _ & _ & R). exact R. Qed.
(* the frame's position on top of the cut's frames (cnb_frame's first conjunct) *)
Lemma cnb7_frame_top : forall D ly S W mem, cnb_frame D ly S W mem -> frames S = (CNB_CID, bi_fpos D) :: frames (bi_S D).
Proof. intros D ly S W mem H. destruct H as (E & _). exact E. Qed.
(* the journal's current state is an ARx state; its layout and static stack (ajxR_ly, ajxR_stk, ajxR_ar) *)
Lemma cnb7_J_ar : forall D wk ly S Hp W mem md k, cnb_JR B ARx WLE' D wk ly S Hp W mem md k -> ARx ly S Hp W mem md.
Proof. intros D wk ly S Hp W mem md k (WS & HJ & _). exact (ajxR_ar HJ). Qed.
(* NAMED PROJECTIONS of the Base's cnb_mid (one place that reads its conjuncts by position) *)
Lemma cnb7_mid_led : forall D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3,
  CNBMID D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) own.
Proof. intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 H. destruct H as (_ & _ & _ & L & _). exact L. Qed.
Lemma cnb7_mid_open : forall D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3,
  CNBMID D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  cnb_open W mem (cnb_d1 D) /\ cnb_open W mem (cnb_d2 D) /\ cnb_open W mem (cnb_d3 D).
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & _). exact (conj O1 (conj O2 O3)).
Qed.
Lemma cnb7_mid_doc : forall D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3,
  CNBMID D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  cnb_doc W mem Lam (cnb_d1 D) st1 /\ cnb_doc W mem Lam (cnb_d2 D) st2 /\ cnb_doc W mem Lam (cnb_d3 D) st3.
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & _). exact (conj D1 (conj D2 D3)).
Qed.
Lemma cnb7_mid_lam : forall D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3,
  CNBMID D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  Permutation Lam (cnb_Dof st1 ++ cnb_Dof st2 ++ cnb_Dof st3 ++ bi_Lam D).
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L.
Qed.
(* the stack facts of a cut: the entry sp, the realigned body sp, the layout the journal keeps (ajxR_ly, ajxR_stk) *)
Lemma cnb7_S1_rng : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  YM05.alloc_ceiling + STK_check_no_overread <= cnb_sp0 D /\ cnb_sp0 D <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\
  cnb_sp0 D mod 16 = 0 /\ cnb_S1 D mod 32 = 0 /\ cnb_S1 D + 160 <= cnb_sp0 D /\ cnb_sp0 D <= cnb_S1 D + 176 /\
  ly_stk_lo ly = ly_stk_lo (bi_ly D) /\ ly_stk_hi ly = ly_stk_hi (bi_ly D) /\ ly_F ly = ly_F (bi_ly D).
Proof.
intros D fxk ly S Hp W regs mem md k wk HB.
destruct (cnb7_base_J D fxk ly S Hp W regs mem md k wk HB) as (WS & HJ & _).
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_stk HJ) as HSTK.
destruct HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
destruct (cnb7_S1_gap D Hal16) as (HS1 & Hal32).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
split; [exact Hal32|]. split; [lia|]. split; [lia|].
split; [exact Elo|]. split; [exact Ehi | exact EF].
Qed.
(* THE ROOT BELOW THE CALLEE'S sp (tsame_specX's guarded premise at the cut, `spZ regs <= pa -> ..`, is vacuous at
   both calls): d1 = F + 32 lies in the fake frame, which lies below alloc_ceiling (frames_bounds_x at the journal's
   ARx state), and s1 > entry sp - 192 >= alloc_ceiling + STK - 192 (cnb_S1_bounds, cnb7_S1_rng) *)
Lemma cnb7_d1_below_sp : forall D fxk ly S Hp W regs mem md k wk, CNBB D fxk ly S Hp W regs mem md k wk ->
  cnb_d1 D < cnb_S1 D.
Proof.
intros D fxk ly S Hp W regs mem md k wk HB.
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (Hsp0 & _ & _ & Hal16 & _ & _ & HS1b & _ & _ & EF).
pose proof (cnb7_J_ar D wk ly S Hp W mem md k (cnb7_base_J D fxk ly S Hp W regs mem md k wk HB)) as HAR.
assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S))
  by (rewrite (cnb7_frame_top D ly S W mem (cnb7_base_frame D fxk ly S Hp W regs mem md k wk HB)); left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (_ & HFceil & _).
assert (E3 : fs_frame_bytes CNB_CID = 512) by reflexivity.
rewrite E3 in HFceil. unfold frame_addr in HFceil. rewrite EF in HFceil.
pose proof cnb7_stk as HSTK. pose proof cnb7_stk0 as HSTK0.
unfold cnb_d1, cnb_F, frame_addr. lia.
Qed.
(* the tree of a done reading at d1 / d2 / d3 is a tree of tsame_specX: its home is the function's own fake frame
   ((CNB_CID, fpos) on top of frames S, prhex_home's frame arm), its 56 bytes open (cnb_open) *)
Lemma cnb7_tree : forall D fxk ly S Hp W regs mem md k wk Lam d t Dd,
  CNBB D fxk ly S Hp W regs mem md k wk -> (d = cnb_d1 D \/ d = cnb_d2 D \/ d = cnb_d3 D) ->
  cnb_open W mem d -> cnb_doc W mem Lam d (Some (t, Dd)) ->
  prhex_tree ly S Lam W regs mem d t Dd.
Proof.
intros D fxk ly S Hp W regs mem md k wk Lam d t Dd HB Hd Hop Hdoc.
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EF).
pose proof (cnb7_frame_top D ly S W mem (cnb7_base_frame D fxk ly S Hp W regs mem md k wk HB)) as Efr.
assert (E3 : fs_frame_bytes CNB_CID = 512) by reflexivity.
destruct Hdoc as [Hnode _]. unfold prhex_tree.
split; [exact Hnode|]. split; [|exact Hop].
right; left. exists CNB_CID, (bi_fpos D). split; [rewrite Efr; left; reflexivity|].
rewrite E3. unfold cnb_d1, cnb_d2, cnb_d3, cnb_F, frame_addr in *. rewrite EF. lia.
Qed.
(* the footprint of a done reading's tree lies below alloc_ceiling (a frame byte or a ledger block), same's window
   on the real stack above it: apart *)
Lemma cnb7_foot : forall D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 d t Dd z,
  CNBB D fxk ly S Hp W regs mem md k wk -> CNBMID D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  spZ regs = cnb_S1 D ->
  ((d = cnb_d1 D /\ st1 = Some (t, Dd)) \/ (d = cnb_d2 D /\ st2 = Some (t, Dd)) \/ (d = cnb_d3 D /\ st3 = Some (t, Dd))) ->
  PRH_Reader.pj_footR d Dd z -> ~ (spZ regs - STK_same DOC_D <= z < spZ regs).
Proof.
intros D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 d t Dd z HB HM Hsp Hd Hz.
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (Hsp0 & _ & _ & _ & _ & HS1a & HS1b & _ & _ & EF).
pose proof cnb7_stk as HSTK.
assert (E3 : fs_frame_bytes CNB_CID = 512) by reflexivity.
pose proof cf_head_nonneg as Hh0.
assert (Hlt : z < YM05.alloc_ceiling).
{ pose proof (cnb7_J_ar D wk ly S Hp W mem md k (cnb7_base_J D fxk ly S Hp W regs mem md k wk HB)) as HAR.
  pose proof (cnb7_frame_top D ly S W mem (cnb7_base_frame D fxk ly S Hp W regs mem md k wk HB)) as Efr.
  destruct Hz as [Hz | ((a, kk) & Hin & Hh)].
  - destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hfb).
    rewrite Forall_forall in Hfb.
    assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Efr; left; reflexivity).
    specialize (Hfb _ Hin3). cbn [fst snd] in Hfb. rewrite E3 in Hfb.
    unfold frame_addr in Hfb. rewrite EF in Hfb.
    destruct Hd as [(-> & _) | [(-> & _) | (-> & _)]]; unfold cnb_d1, cnb_d2, cnb_d3, cnb_F, frame_addr in *; lia.
  - pose proof (cnb7_mid_led D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HM) as HLED.
    pose proof (cnb7_mid_lam D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 HM) as HPL.
    assert (HinL : In (a, kk) Lam).
    { apply (Permutation_in _ (Permutation_sym HPL)).
      destruct Hd as [(_ & ->) | [(_ & ->) | (_ & ->)]]; cbn [cnb_Dof]; rewrite !in_app_iff; tauto. }
    pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF. rewrite Forall_forall in HF.
    destruct (HF (a, kk) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & Hce & _).
    unfold pj_holdsR in Hh. cbn [fst snd] in Hh. unfold req_size in Hce.
    destruct (Z.eqb_spec (kk + cf_head) 0); lia. }
rewrite Hsp. pose proof cnb7_stk0. lia.
Qed.

(* ---- the byte of g_own_ran_out the `lbu` at CNB_CMP reads: the address is the hi/lo pair's (cnbi_hi, cnbi_own); the
   cut's ledger states own = 0 (prh_ledger_own), which gives the byte 0 (the cell's width at prh_img_B is 1) ---- *)
Lemma cnb7_own_byte : forall (W : world SEGS) mem, prh_own W mem 0 ->
  exists b, mbyte SEGS (mrestrict (w_H W) mem) pi_g_own_ran_out = Some b /\ bv_unsigned b = 0.
Proof.
intros W mem (H & _). unfold val_mem in H.
assert (Ew : (0 < @pi_gz_own_ran_out prh_img_B)%nat) by (cbv; lia).
specialize (H 0%nat Ew). cbn [Z.of_nat] in H. rewrite Z.add_0_r in H.
eexists. split; [exact H|].
change (@pi_gz_own_ran_out prh_img_B) with 1%nat.
lazymatch goal with |- bv_unsigned (Z_to_bv _ (_ 0 1%nat 0%nat)) = 0 => vm_compute; reflexivity end.
Qed.
Lemma cnb7_own_addr : forall regs, getr regs 24%bv = w64 (VAL (A_HI 9)) ->
  bv_unsigned (getr regs 24%bv) + 320 = pi_g_own_ran_out.
Proof.
intros regs H. rewrite H. unfold w64. pose proof (@pa_val_range _ _ PA (A_HI 9)) as Hr.
rewrite unsigned_lit_small by lia.
pose proof (cnbi_hi B IMG) as E1. pose proof (cnbi_own B IMG) as E2. lia.
Qed.
(* the base at a materialised model, same registers *)
Lemma cnb7_base_md : forall D fxk ly S Hp W regs mem md k wk X,
  CNBB D fxk ly S Hp W regs mem md k wk -> CNBB D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros D fxk ly S Hp W regs mem md k wk X H.
exact (cnb_base_matR B ARx LAWS WLE' D fxk ly S Hp W regs regs mem md k wk X H eq_refl eq_refl).
Qed.

(* ---- packing the exits ---- *)
(* the free exit (the Base's cnb_ex_freeR at WLE'): every CB7 arm reaches CNB_FREE with ownl = 0 (the flag at 728
   read 0), so the refused-copy arm of cnb_at_freeR (ownl <> 0 -> ..) holds by contradiction; the ownl = 0 arm takes
   the compare cut's facts and the trees' free order (cnb_fo); the hull budget at rd0 (cnb_at_freeR's last conjunct)
   is the compare cut's, S kept *)
Lemma cnb7_mk_free : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  CNBB D fxk ly S Hp W regs mem md k 6 ->
  cnb_regsat regs (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) ->
  cnb_slots D W mem r2 r3 -> CNBMID D ly S Hp W mem Lam peak cnt ran ownl 3 r1 r2 r3 st1 st2 st3 ->
  ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0)) ->
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
     cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ ran = cnb_ranz D o1 o2 o0 /\
     cnb_rds3 D o1 o2 o0 st1 st2 st3 /\
     cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
     cnb_fo D W mem Lam o0 (cnb_d3 D) st3) ->
  ownl = 0 ->
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)) ->
  CNBFREE D W (CFG fxk (cnb_pc CNB_FREE) regs mem md).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 HB HR HSL HM Hr Hpg Ho
  HHB.
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, 3%nat, r1, r2, r3, r, ownl, st1, st2, st3, o1, o2, o0.
split; [reflexivity|].
split; [exact HB|]. split; [exact HR|]. split; [exact HSL|]. split; [exact HM|]. split; [lia|].
split; [|split; [exact Hpg | split; [intros Hn; exfalso; exact (Hn Ho) | exact HHB]]].
destruct Hr as [Hr | (H1 & H2 & H3)]; [left; exact Hr | right; split; [exact H1 | split; [exact H2 | split; [exact H3 | reflexivity]]]].
Qed.
Lemma cnb7_mk_same1 : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNBB D fxk ly S Hp W regs mem md k 6 ->
  cnb_regsat regs (cnb_core D ++ [(1%bv, cnb_pc CNB7_RS1); (10%bv, cnb_d1 D); (11%bv, cnb_d2 D); (23%bv, 0);
                                  (24%bv, 1); (25%bv, r1)]) ->
  cnb_slots D W mem r2 r3 -> cnb_rcslot D W mem 8 0 -> cnb_rcslot D W mem 0 0 ->
  r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S -> 0 = cnb_ranz D o1 o2 o0 ->
  cnb_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  cnb_fo D W mem Lam o1 (cnb_d1 D) (Some (t, D1)) -> cnb_fo D W mem Lam o2 (cnb_d2 D) (Some (t, D2)) ->
  cnb_fo D W mem Lam o0 (cnb_d3 D) (Some (t, D3)) ->
  CNBMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  ck_read (bi_x D) = Some t -> PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)) ->
  cnb_ex_same1 D W (CFG fxk (SIGMA AS_same) regs mem md).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HB HR HSL HS8 HS0 H1 H2 H3 Hpg Hz Hrd
  HF1 HF2 HF3 HM Ek HHB.
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, t, D1, D2, D3, o1, o2, o0.
split; [reflexivity|].
exact (conj HB (conj HR (conj HSL (conj HS8 (conj HS0 (conj H1 (conj H2 (conj H3 (conj Hpg (conj Hz (conj Hrd
  (conj HF1 (conj HF2 (conj HF3 (conj HM (conj Ek HHB)))))))))))))))).
Qed.
Lemma cnb7_mk_same2 : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNBB D fxk ly S Hp W regs mem md k 6 ->
  cnb_regsat regs (cnb_core D ++ [(1%bv, cnb_pc CNB7_RS2); (10%bv, cnb_d1 D); (11%bv, cnb_d3 D); (23%bv, 0);
                                  (24%bv, 1); (25%bv, r1)]) ->
  cnb_slots D W mem r2 r3 -> cnb_rcslot D W mem 8 0 -> cnb_rcslot D W mem 0 0 ->
  r1 <> 0 -> r2 <> 0 -> r3 <> 0 ->
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S -> 0 = cnb_ranz D o1 o2 o0 ->
  cnb_rds3 D o1 o2 o0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  cnb_fo D W mem Lam o1 (cnb_d1 D) (Some (t, D1)) -> cnb_fo D W mem Lam o2 (cnb_d2 D) (Some (t, D2)) ->
  cnb_fo D W mem Lam o0 (cnb_d3 D) (Some (t, D3)) ->
  CNBMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) ->
  ck_read (bi_x D) = Some t -> PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)) ->
  cnb_ex_same2 D W (CFG fxk (SIGMA AS_same) regs mem md).
Proof.
intros D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HB HR HSL HS8 HS0 H1 H2 H3 Hpg Hz Hrd
  HF1 HF2 HF3 HM Ek HHB.
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, t, D1, D2, D3, o1, o2, o0.
split; [reflexivity|].
exact (conj HB (conj HR (conj HSL (conj HS8 (conj HS0 (conj H1 (conj H2 (conj H3 (conj Hpg (conj Hz (conj Hrd
  (conj HF1 (conj HF2 (conj HF3 (conj HM (conj Ek HHB)))))))))))))))).
Qed.

(* ---- CB7: from the compare cut to the free cut (g_ran_out set, or no tree read) or to the first `same` call
   state. After a free: SRr' SEGS RZ_cf, every hand step the kit's R form at WLE' (after one, the goal shows
   SRrG SEGS WLE', the same term as SRr' SEGS RZ_cf unfolded), the ran-out call by cnb_ro_callR at WLE'; the cut's
   hull budget at rd0 rides to every exit (S kept) ---- *)
Theorem cnb_cmp_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  CNBPRE D -> CNBCMP D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (CFG fxk (cnb_pc CNB_CMP) regs mem md)
    (fun W' c' => (CNBFREE D W' c' \/ cnb_ex_same1 D W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HRC1 & HRC2 & Hr1 & Hr2 & Hr3 & Hpg & Hranz & HM & HRES1 & HRES2 & HRES3 & Hrds
  & HFO1 & HFO2 & HFO3 & HHB).
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k 6 HB) as (Hsp0 & Hhi & H47 & Hal16 & Hal32 & HS1a & HS1b & _).
pose proof asan_consts as (C1 & _). pose proof cnb7_stk as HSTK. pose proof cnb7_stk0 as HSTK0.
assert (G9 : getr regs 9%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get _ _ _ _ HR); cnb7_in).
assert (G24 : getr regs 24%bv = w64 (VAL (A_HI 9))) by (apply (cnb_regsat_get _ _ _ _ HR); cnb7_in).
assert (U9 : bv_unsigned (w64 (cnb_S1 D)) = cnb_S1 D) by (unfold w64; apply unsigned_lit_small; lia).
(* 728: lbu a0, 0x140(s8): the byte 0 (the cut's ledger states g_own_ran_out = 0: prh_ledger_own) *)
pose proof (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ (cnb7_mid_led D ly S Hp W mem Lam peak cnt ran 0 3 r1 r2 r3
  st1 st2 st3 HM)) as Hown.
destruct (cnb7_own_byte W mem Hown) as (b & Hb & Hb0).
unfold CNB_CMP.
apply (cnb_hs_lbuR WLE' W fxk regs mem md _ 728 732 10%bv 24%bv 320 pi_g_own_ran_out b);
  [cnb7_dec | reflexivity | lia | reflexivity | exact (cnb7_own_addr regs G24) | exact Hb |].
intros X1.
(* 732: beqz a0 taken (the fall-through 736 REFUTED: the byte is 0) *)
apply (cnb_hs_beqzR WLE' W fxk _ mem _ _ 732 10%bv 408 1140 736 true);
  [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, Hb0; reflexivity |].
intros X2. cbv iota.
(* 1140: jal fuzz_alloc_ran_out *)
apply (cnb_hs_callR WLE' W fxk _ mem _ _ 1140 1144 AS_fuzz_alloc_ran_out); [cnb7_dec | lia | reflexivity |].
intros X3.
lazymatch goal with |- SRrG _ _ _ (cnb_cfg _ _ ?R _ ?M) _ =>
  assert (HR3 : cnb_regsat R (cnb_core D ++ [(1%bv, cnb_pc CNB7_RORET); (23%bv, rc3); (25%bv, r1)])) by (cnb7_rs HR);
  assert (HB3 : CNBB D fxk ly S Hp W R mem M k 6)
    by (apply (cnb_base_matR B ARx LAWS WLE' D fxk ly S Hp W regs); [repeat apply cnb7_base_md; exact HB
        | ro_getr; reflexivity | ro_getr; reflexivity]);
  eapply (SRrG_bind SEGS WLE' (wle'_trans SEGS YGcfRehidePost.RZ_cf));
  [ apply (cnb_ro_callR B ARx LAWS IMG HRO WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)
      (wle'_trans SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)
      P PCALL CTX0 D fxk ly S Hp W R mem M k 6 Lam peak cnt ran 0 3 r1 r2 r3
      st1 st2 st3 CNB7_RORET HPRE);
    [ cbv [cnb_ro_rets CNB7_RORET In]; repeat (first [left; reflexivity | right]) | exact HB3
    | exact (cnb7_rs_app_l _ _ _ HR3) | apply (cnb_regsat_get _ _ _ _ HR3); cnb7_in | exact HSL | exact HM | exact HPM ]
  | ]
end.
intros W' c' _ (ly' & regs' & mem' & md' & k' & -> & HB' & HAP & H10 & Hab & HSL' & HM' & KF1 & KF2 & KF3 & HKT & HPM').
pose proof (KF1 o1 HFO1) as HFO1'. pose proof (KF2 o2 HFO2) as HFO2'. pose proof (KF3 o0 HFO3) as HFO3'.
clear KF1 KF2 KF3 HFO1 HFO2 HFO3.
lazymatch type of HAP with aregs_preserved ?R _ =>
  assert (HR' : cnb_regsat regs' (cnb_core D ++ [(23%bv, rc3); (25%bv, r1)]))
    by (apply (cnb_regsat_pres R regs'); [cnb7_rs HR3 | exact HAP | cnb7_cs])
end.
pose proof (cnb_rcslot_agree D W mem W' mem' 8 rc1 Hal16 ltac:(lia) HKT HRC1) as HRC1'.
pose proof (cnb_rcslot_agree D W mem W' mem' 0 rc2 Hal16 ltac:(lia) HKT HRC2) as HRC2'.
assert (G9' : getr regs' 9%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get _ _ _ _ HR'); cnb7_in).
(* 1144: li s8, 1 *)
apply (cnb_hs_addiR WLE' W' fxk regs' mem' md' _ 1144 1148 24%bv 0%bv 1); [cnb7_dec | reflexivity | lia | reflexivity |].
intros X4.
assert (Hran : ran = 0 \/ ran = 1).
{ pose proof (cnb7_mid_led D ly' S Hp W' mem' Lam peak cnt ran 0 3 r1 r2 r3 st1 st2 st3 HM') as HL'.
  exact (proj2 (proj2 (proj2 (proj2 (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL'))))). }
destruct Hran as [-> | ->].
2:{ (* 1148: bnez a0 taken: g_ran_out is 1; CNB_FREE with r = 1 *)
  apply (cnb_hs_bnezR WLE' W' fxk _ mem' _ _ 1148 10%bv (-408) 740 1152 false);
    [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, H10; reflexivity |].
  intros X5. cbv iota.
  apply (SRrG_ret SEGS WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)). split; [left | exact HPM'].
  apply (cnb7_mk_free D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt 1 r1 r2 r3 1 0 st1 st2 st3 o1 o2 o0).
  - apply (cnb_base_matR B ARx LAWS WLE' D fxk ly' S Hp W' regs'); [repeat apply cnb7_base_md; exact HB'
    | ro_getr; reflexivity | ro_getr; reflexivity].
  - cnb7_rs HR'.
  - exact HSL'.
  - exact HM'.
  - left. split; [reflexivity | right; reflexivity].
  - intros _. exact (conj Hr1 (conj Hr2 (conj Hr3 (conj Hpg (conj Hranz (conj Hrds (conj HFO1' (conj HFO2' HFO3')))))))).
  - reflexivity.
  - exact HHB. }
(* 1148: bnez a0 falls through: g_ran_out is 0, so every reading is the grammar's (cnb_res) *)
apply (cnb_hs_bnezR WLE' W' fxk _ mem' _ _ 1148 10%bv (-408) 740 1152 true);
  [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, H10; reflexivity |].
intros X5. cbv iota.
(* 1152: ld a1, 8(s1) (rc1); 1156: ld a2, 0(s1) (rc2) *)
apply (cnb_hs_ldR WLE' W' fxk _ mem' _ _ 1152 1156 11%bv 9%bv 8 (cnb_S1 D + 8) (rc1 mod 2 ^ 64));
  [cnb7_dec | reflexivity | lia | reflexivity | ro_getr; rewrite G9', U9; reflexivity | lia | lia | exact HRC1' |].
intros X6.
apply (cnb_hs_ldR WLE' W' fxk _ mem' _ _ 1156 1160 12%bv 9%bv 0 (cnb_S1 D + 0) (rc2 mod 2 ^ 64));
  [cnb7_dec | reflexivity | lia | reflexivity | ro_getr; rewrite G9', U9; reflexivity | lia | lia | exact HRC2' |].
intros X7.
revert HRES1 HRES2 HRES3. unfold cnb_res. destruct (ck_read (bi_x D)) as [t|] eqn:Eck; intros HRES1 HRES2 HRES3.
- (* the input is read: rc1 = rc2 = rc3 = 0, three trees t *)
  destruct (HRES1 eq_refl) as [-> (D1 & ->)]. destruct (HRES2 eq_refl) as [-> (D2 & ->)].
  destruct (HRES3 eq_refl) as [-> (D3 & ->)].
  (* 1160: bnez a1; 1164: bnez a2 (both 0) *)
  apply (cnb_hs_bnezR WLE' W' fxk _ mem' _ _ 1160 11%bv 60 1220 1164 true);
    [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0; reflexivity |].
  intros X8. cbv iota.
  apply (cnb_hs_bnezR WLE' W' fxk _ mem' _ _ 1164 12%bv 28 1192 1168 true);
    [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0; reflexivity |].
  intros X9. cbv iota.
  (* 1168: mv a0, s6; 1172: mv a1, s5; 1176: jal same *)
  apply (cnb_hs_addiR WLE' W' fxk _ mem' _ _ 1168 1172 10%bv 22%bv 0); [cnb7_dec | reflexivity | lia | reflexivity |].
  intros X10.
  apply (cnb_hs_addiR WLE' W' fxk _ mem' _ _ 1172 1176 11%bv 21%bv 0); [cnb7_dec | reflexivity | lia | reflexivity |].
  intros X11.
  apply (cnb_hs_callR WLE' W' fxk _ mem' _ _ 1176 1180 AS_same); [cnb7_dec | lia | reflexivity |].
  intros X12. apply (SRrG_ret SEGS WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)). split; [right | exact HPM'].
  apply (cnb7_mk_same1 D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0).
  + apply (cnb_base_matR B ARx LAWS WLE' D fxk ly' S Hp W' regs'); [repeat apply cnb7_base_md; exact HB'
    | ro_getr; reflexivity | ro_getr; reflexivity].
  + cnb7_rs HR'.
  + exact HSL'.
  + exact HRC1'.
  + exact HRC2'.
  + exact Hr1.
  + exact Hr2.
  + exact Hr3.
  + exact Hpg.
  + exact Hranz.
  + exact Hrds.
  + exact HFO1'.
  + exact HFO2'.
  + exact HFO3'.
  + exact HM'.
  + exact Eck.
  + exact HHB.
- (* the grammar refuses the input: rc1 = rc2 = rc3 = -1, the structs zero *)
  destruct (HRES1 eq_refl) as [-> ->]. destruct (HRES2 eq_refl) as [-> ->]. destruct (HRES3 eq_refl) as [-> ->].
  (* 1160: bnez a1 taken (rc1 = -1) *)
  apply (cnb_hs_bnezR WLE' W' fxk _ mem' _ _ 1160 11%bv 60 1220 1164 false);
    [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0; reflexivity |].
  intros X8. cbv iota.
  (* 1220: bne a1, s7; 1224: bne a2, s7 fall through (rc1 = rc2 = rc3 = -1): the abort at 1236 is not reached *)
  apply (cnb7_hs_bne W' fxk _ mem' _ _ 1220 11%bv 23%bv 16 1236 1224 true);
    [cnb7_dec | lia | lia | reflexivity | reflexivity
    | ro_getr; rewrite (cnb_regsat_get _ _ 23%bv (-1) HR' ltac:(cnb7_in)); apply cnb7_c_eq_w64; reflexivity |].
  intros X9. cbv iota.
  apply (cnb7_hs_bne W' fxk _ mem' _ _ 1224 12%bv 23%bv 12 1236 1228 true);
    [cnb7_dec | lia | lia | reflexivity | reflexivity
    | ro_getr; rewrite (cnb_regsat_get _ _ 23%bv (-1) HR' ltac:(cnb7_in)); apply cnb7_c_eq_w64; reflexivity |].
  intros X10. cbv iota.
  (* 1228: mv s8, zero; 1232: j CNB_FREE (r = 0) *)
  apply (cnb_hs_addiR WLE' W' fxk _ mem' _ _ 1228 1232 24%bv 0%bv 0); [cnb7_dec | reflexivity | lia | reflexivity |].
  intros X11.
  apply (cnb_hs_jR WLE' W' fxk _ mem' _ _ 1232 740 (-492)); [cnb7_dec | lia | reflexivity | lia |].
  intros X12. apply (SRrG_ret SEGS WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)). split; [left | exact HPM'].
  apply (cnb7_mk_free D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt 0 r1 r2 r3 0 0 None None None o1 o2 o0).
  + apply (cnb_base_matR B ARx LAWS WLE' D fxk ly' S Hp W' regs'); [repeat apply cnb7_base_md; exact HB'
    | ro_getr; reflexivity | ro_getr; reflexivity].
  + cnb7_rs HR'.
  + exact HSL'.
  + exact HM'.
  + right. split; [reflexivity | split; reflexivity].
  + intros _. exact (conj Hr1 (conj Hr2 (conj Hr3 (conj Hpg (conj Hranz (conj Hrds (conj HFO1' (conj HFO2' HFO3')))))))).
  + reflexivity.
  + exact HHB.
Qed.

(* ---- THE `same` CALL (callee entry, ra = one of the two return sites): aj_call_xWR at R := WLE' over tsame_specX at
   n = DOC_D for any float state (a non-crossing text: its plain SRr lifts into the rule's relation by SRr_SRrG at
   wle_wle', its fpostm post by apost_base_x_R_lift into fpostW_x_of_apostR's premise), with a0 = d1 and a1 = d2 or
   d3, both trees t of the readings. same is a FIXED-trace text: the walk's budgeted journal is rebased to the empty
   budget (the kit's cnb_J_rebaseR), the call made with aj_call_xWR, and cnb_call_keepR unbases it at the same spent
   budget wk (the kit's cnb_J_fixedR). The text's guarded premise
   (spZ regs <= pa -> astack_up_x ..) is vacuous: pa = d1 < s1 = spZ regs (cnb7_d1_below_sp). The text's `S' = S` and
   its kept Hp, blocks and ledger (with g_most and g_own_ran_out) carry every cut fact by cnb_call_keepR, the trees'
   free order included (cnb_fo, by cnb_fo_keep over each tree's footprint); a0 = 1 by cnb7_same_one; the body stack
   above s1 is kept (cnb_call_keepR's last conjunct). The text's post Q is unchanged, so its positional destruct below
   stands as it was. ---- *)
(* the two return sites: code words of the listing, below the ceiling (fpre's raZ bound), one closed lemma each *)
Lemma cnb7_rs1_ok : 4096 <= cnb_pc CNB7_RS1 < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cnb_pc CNB7_RS1)) /\
  0 <= CNB7_RS1 < 2 ^ 28.
Proof.
pose proof (cnbi_base B IMG) as HB. pose proof cnb_off_val as HO.
assert (Hr2 : (CNB_OFF + CNB7_RS1) mod 2 = 0) by (rewrite HO; reflexivity).
unfold cnb_pc, w64. replace (BASE + CNB_OFF + CNB7_RS1) with (BASE + (CNB_OFF + CNB7_RS1)) by lia.
unfold CNB7_RS1 in *.
split; [split|split].
- rewrite HB. unfold B_prog_base. lia.
- exact (pa_slot_lt_ceil_b (PL := PL_cno_B) (PI := PA) (CNB_OFF + 1180) ltac:(lia) cnb7_rs1_slot).
- apply ret_ok_codeptr_v; [lia | exact Hr2].
- lia.
Qed.
Lemma cnb7_rs2_ok : 4096 <= cnb_pc CNB7_RS2 < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cnb_pc CNB7_RS2)) /\
  0 <= CNB7_RS2 < 2 ^ 28.
Proof.
pose proof (cnbi_base B IMG) as HB. pose proof cnb_off_val as HO.
assert (Hr2 : (CNB_OFF + CNB7_RS2) mod 2 = 0) by (rewrite HO; reflexivity).
unfold cnb_pc, w64. replace (BASE + CNB_OFF + CNB7_RS2) with (BASE + (CNB_OFF + CNB7_RS2)) by lia.
unfold CNB7_RS2 in *.
split; [split|split].
- rewrite HB. unfold B_prog_base. lia.
- exact (pa_slot_lt_ceil_b (PL := PL_cno_B) (PI := PA) (CNB_OFF + 1208) ltac:(lia) cnb7_rs2_slot).
- apply ret_ok_codeptr_v; [lia | exact Hr2].
- lia.
Qed.
Lemma cnb7_same_ret_ok : forall ret, In ret cnb7_same_rets ->
  4096 <= cnb_pc ret < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cnb_pc ret)) /\ 0 <= ret < 2 ^ 28.
Proof.
intros ret Hin. cbv [cnb7_same_rets In] in Hin.
destruct Hin as [<- | [<- | []]]; [exact cnb7_rs1_ok | exact cnb7_rs2_ok].
Qed.

Lemma cnb_same_call : forall P, srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k wk Lam peak cnt r1 r2 r3 st1 st2 st3 t D1 Db pb ret,
  CNBPRE D -> In ret cnb7_same_rets -> CNBB D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D) -> getr regs 1%bv = w64 (cnb_pc ret) ->
  getr regs 10%bv = w64 (cnb_d1 D) -> getr regs 11%bv = w64 pb ->
  cnb_slots D W mem r2 r3 -> CNBMID D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 ->
  st1 = Some (t, D1) -> ((pb = cnb_d2 D /\ st2 = Some (t, Db)) \/ (pb = cnb_d3 D /\ st3 = Some (t, Db))) ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (CFG fxk (SIGMA AS_same) regs mem md) (fun W' c' => exists ly' regs' mem' md' k',
    c' = CFG fxk (cnb_pc ret) regs' mem' md' /\ CNBB D fxk ly' S Hp W' regs' mem' md' k' wk /\
    aregs_preserved regs regs' /\ getr regs' 10%bv = w64 1 /\ ablocks B ly' S = ablocks B ly S /\
    cnb_slots D W' mem' r2 r3 /\ CNBMID D ly' S Hp W' mem' Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 /\
    (forall o, cnb_fo D W mem Lam o (cnb_d1 D) st1 -> cnb_fo D W' mem' Lam o (cnb_d1 D) st1) /\
    (forall o, cnb_fo D W mem Lam o (cnb_d2 D) st2 -> cnb_fo D W' mem' Lam o (cnb_d2 D) st2) /\
    (forall o, cnb_fo D W mem Lam o (cnb_d3 D) st3 -> cnb_fo D W' mem' Lam o (cnb_d3 D) st3) /\
    (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
    P mem').
Proof.
intros P PCALL D fxk ly S Hp W regs mem md k wk Lam peak cnt r1 r2 r3 st1 st2 st3 t D1 Db pb ret
  HPRE Hret HB HC R1 R10 R11 HSL HM E1 Hpb HPM.
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k wk HB) as (Hsp0 & Hhi & H47 & Hal16 & Hal32 & HS1a & HS1b & _).
pose proof asan_consts as (C1 & _).
pose proof cnb7_stk as HSTK. pose proof cnb7_stk0 as HSTK0.
destruct (cnb7_same_ret_ok ret Hret) as ((Hr0 & Hrc) & Hrok & Hr28).
destruct (cnb_chainR B ARx WLE' CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB) as (ch1 & Hch1).
pose proof (cnb7_base_frm0 D fxk ly S Hp W regs mem md k wk HB) as Hz.
pose proof (cnb7_base_rod D fxk ly S Hp W regs mem md k wk HB) as HROD.
destruct (cnb7_base_gptp D fxk ly S Hp W regs mem md k wk HB) as (R3 & R4).
pose proof (cnb7_d1_below_sp D fxk ly S Hp W regs mem md k wk HB) as Hd1.
(* the FIXED-trace call: the journal at the empty budget from the entry state with its depot moved to the current *)
pose proof (cnb_J_rebaseR B ARx WLE' D wk ly S Hp W mem md k (cnb7_base_J D fxk ly S Hp W regs mem md k wk HB)) as HJ.
destruct (cnb_entry_facts B ARx CTX0 D HPRE) as (_ & _ & _ & _ & _ & _ & _ & Hgp0 & Htp0 & _).
assert (G2 : getr regs 2%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get _ _ _ _ HC); cnb7_in).
assert (G8 : getr regs 8%bv = w64 (cnb_sp0 D)) by (apply (cnb_regsat_get _ _ _ _ HC); cnb7_in).
assert (Hsp : spZ regs = cnb_S1 D) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = cnb_sp0 D) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regs = cnb_pc ret) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
(* tsame_specX's guarded premise: the root d1 lies below the callee's sp, so `spZ regs <= pa` is false *)
assert (Hnle : ~ spZ regs <= cnb_d1 D) by (rewrite Hsp; lia).
pose proof (cnb7_mid_led D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 HM) as HLED.
destruct (cnb7_mid_open D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 HM) as (O1 & O2 & O3).
destruct (cnb7_mid_doc D ly S Hp W mem Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 HM) as (Do1 & Do2 & Do3).
(* the two trees, their depth and their footprints *)
assert (HT1 : prhex_tree ly S Lam W regs mem (cnb_d1 D) t D1).
{ subst st1. exact (cnb7_tree D fxk ly S Hp W regs mem md k wk Lam (cnb_d1 D) t D1 HB (or_introl eq_refl) O1 Do1). }
assert (HTb : prhex_tree ly S Lam W regs mem pb t Db).
{ destruct Hpb as [(-> & ->) | (-> & ->)].
  - exact (cnb7_tree D fxk ly S Hp W regs mem md k wk Lam (cnb_d2 D) t Db HB (or_intror (or_introl eq_refl)) O2 Do2).
  - exact (cnb7_tree D fxk ly S Hp W regs mem md k wk Lam (cnb_d3 D) t Db HB (or_intror (or_intror eq_refl)) O3 Do3). }
assert (Hdep : (PjTree.depth t <= DOC_D)%nat).
{ subst st1. destruct Do1 as [_ Hd]. exact (cnb7_depth t Hd). }
assert (Hf1 : forall z, PRH_Reader.pj_footR (cnb_d1 D) D1 z -> ~ (spZ regs - STK_same DOC_D <= z < spZ regs)).
{ intros z Hz'. exact (cnb7_foot D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 (cnb_d1 D) t
    D1 z HB HM Hsp (or_introl (conj eq_refl E1)) Hz'). }
assert (Hfb : forall z, PRH_Reader.pj_footR pb Db z -> ~ (spZ regs - STK_same DOC_D <= z < spZ regs)).
{ intros z Hz'. destruct Hpb as [(-> & E2) | (-> & E3)].
  - exact (cnb7_foot D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 (cnb_d2 D) t Db z
      HB HM Hsp (or_intror (or_introl (conj eq_refl E2))) Hz').
  - exact (cnb7_foot D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 0 3 r1 r2 r3 st1 st2 st3 (cnb_d3 D) t Db z
      HB HM Hsp (or_intror (or_intror (conj eq_refl E3))) Hz'). }
unfold cnb_cfg, w64.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (@aj_call_xWR fxk rc SK SEGS B prh_pst ARx cf_head LAWS pa_segs_low WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (wle'_trans SEGS YGcfRehidePost.RZ_cf) W regs mem (SIGMA AS_same)
    STK_check_no_overread (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D)
    (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp md k (STK_same DOC_D) 0 [] (cnb_S1 D - cnb_sp0 D) (w64 (cnb_pc ret)) ch1
    (fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       (t = t /\ getr regs' 10 = w64 1 \/ t <> t /\ getr regs' 10 = w64 0) /\
       PRH_Reader.pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) (cnb_d1 D) t D1 /\
       PRH_Reader.pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) pb t Db /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ 0 (bi_most D) 0))).
  - exact HJ.
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
  - replace (cnb_sp0 D + (cnb_S1 D - cnb_sp0 D)) with (cnb_S1 D) by lia. rewrite Hs0. exact Hch1.
  - intros HAFN _.
    assert (HFP : fpre B ARx (STK_same DOC_D) ly S Hp W regs mem md ch1).
    { split; [exact HAFN|]. split; [exact HROD|]. split; [rewrite Hsp; lia|].
      split; [rewrite Hraz; exact Hrc | exact Hz]. }
    (* the plain text, lifted into the rule's relation; its post lifted into the R post *)
    eapply (SRrG_mono SEGS WLE');
      [exact (SRr_SRrG SEGS WLE' (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _
        (HSAME fxk ly S Hp W regs mem md ch1 (cnb_d1 D) pb t t D1 Db Lam peak cnt SIZE_MAXZ 0
        (bi_most D) 0 HFP (fun Hle => False_ind _ (Hnle Hle)) R10 R11 HT1 HTb Hdep Hf1 Hfb HLED))|].
    intros W' c' _ HPOST. apply fpostW_x_of_apostR.
    apply apost_base_x_R_lift; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HPOST].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & (HQ & HMN)).
destruct HQ as (_ & Hres & _ & _ & -> & -> & HAB & HL2).
rewrite Z.add_0_r in HJ1. replace (cnb_sp0 D + (cnb_S1 D - cnb_sp0 D)) with (cnb_S1 D) in HJ1 by lia.
rewrite !Z.add_0_r in HJ1.
assert (HK1 : 0 <= STK_same DOC_D) by lia.
assert (HK2 : STK_same DOC_D + (cnb_sp0 D - cnb_S1 D) <= STK_check_no_overread) by lia.
destruct (cnb_call_keepR B ARx LAWS IMG WLE' CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt 0 0 3 r1 r2 r3
  st1 st2 st3 (STK_same DOC_D) ly2 W2 regs2 mem2 md2 k1 HPRE HB HC HSL HM HK1 HK2 HJ2 HJ1 HP2 HAB HL2)
  as (HB2 & HSL2 & HM2 & KF1 & KF2 & KF3 & HKT).
apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). exists ly2, regs2, mem2, md2, (k + k1).
split; [reflexivity|]. split; [exact HB2|]. split; [exact HP2|].
split; [exact (cnb7_same_one t t regs2 Hres eq_refl)|]. split; [exact HAB|].
split; [exact HSL2|]. split; [exact HM2|]. split; [exact KF1|]. split; [exact KF2|]. split; [exact KF3|].
split; [exact HKT|].
exact (PCALL mem mem2 HMN HPM).
Qed.

(* ---- THE FIRST `same` STEP: the call (d1, d2), then 1180 / 1184 reload rc2 / rc1, 1188 beqz a0 falls through
   (a0 = 1: the abort edge at 1188 REFUTED by cnb7_same_one), 1192 bnez s7 falls through (rc3 = 0: the jump to 1220
   REFUTED), the second call state. The free arm of the exit is never reached (the contract's form). After a free:
   SRr' SEGS RZ_cf, the hand steps the kit's R forms at WLE'; the hull budget at rd0 rides to the exit (S kept) ---- *)
Theorem cnb_same1_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNBPRE D -> cnb_at_same1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 -> P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (CFG fxk (SIGMA AS_same) regs mem md)
    (fun W' c' => (cnb_ex_same2 D W' c' \/ CNBFREE D W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HRC1 & HRC2 & Hr1 & Hr2 & Hr3 & Hpg & Hranz & Hrds & HFO1 & HFO2 & HFO3 & HM & Eck
  & HHB).
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k 6 HB) as (Hsp0 & Hhi & H47 & Hal16 & Hal32 & HS1a & HS1b & _).
pose proof asan_consts as (C1 & _). pose proof cnb7_stk as HSTK. pose proof cnb7_stk0 as HSTK0.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (cnb_same_call P PCALL D fxk ly S Hp W regs mem md k 6 Lam peak cnt r1 r2 r3
    (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) t D1 D2 (cnb_d2 D) CNB7_RS1 HPRE);
  [ cbv [cnb7_same_rets In]; left; reflexivity | exact HB | exact (cnb7_rs_app_l _ _ _ HR)
  | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in
  | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in | exact HSL | exact HM | reflexivity | left; split; reflexivity
  | exact HPM ]. }
intros W' c' _ (ly' & regs' & mem' & md' & k' & -> & HB' & HAP & H10 & Hab & HSL' & HM' & KF1 & KF2 & KF3 & HKT & HPM').
pose proof (KF1 o1 HFO1) as HFO1'. pose proof (KF2 o2 HFO2) as HFO2'. pose proof (KF3 o0 HFO3) as HFO3'.
clear KF1 KF2 KF3 HFO1 HFO2 HFO3.
assert (HR' : cnb_regsat regs' (cnb_core D ++ [(23%bv, 0); (24%bv, 1); (25%bv, r1)]))
  by (apply (cnb_regsat_pres regs regs'); [cnb7_rs HR | exact HAP | cnb7_cs]).
pose proof (cnb_rcslot_agree D W mem W' mem' 8 0 Hal16 ltac:(lia) HKT HRC1) as HRC1'.
pose proof (cnb_rcslot_agree D W mem W' mem' 0 0 Hal16 ltac:(lia) HKT HRC2) as HRC2'.
assert (G9' : getr regs' 9%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get _ _ _ _ HR'); cnb7_in).
assert (U9 : bv_unsigned (w64 (cnb_S1 D)) = cnb_S1 D) by (unfold w64; apply unsigned_lit_small; lia).
unfold CNB7_RS1.
(* 1180: ld a2, 0(s1); 1184: ld a1, 8(s1) *)
apply (cnb_hs_ldR WLE' W' fxk regs' mem' md' _ 1180 1184 12%bv 9%bv 0 (cnb_S1 D + 0) (0 mod 2 ^ 64));
  [cnb7_dec | reflexivity | lia | reflexivity | rewrite G9', U9; reflexivity | lia | lia | exact HRC2' |].
intros X1.
apply (cnb_hs_ldR WLE' W' fxk _ mem' _ _ 1184 1188 11%bv 9%bv 8 (cnb_S1 D + 8) (0 mod 2 ^ 64));
  [cnb7_dec | reflexivity | lia | reflexivity | ro_getr; rewrite G9', U9; reflexivity | lia | lia | exact HRC1' |].
intros X2.
(* 1188: beqz a0 falls through: a0 = 1 *)
apply (cnb_hs_beqzR WLE' W' fxk _ mem' _ _ 1188 10%bv 48 1236 1192 false);
  [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, H10; reflexivity |].
intros X3. cbv iota.
(* 1192: bnez s7 falls through: rc3 = 0 *)
apply (cnb_hs_bnezR WLE' W' fxk _ mem' _ _ 1192 23%bv 28 1220 1196 true);
  [cnb7_dec | lia | lia | reflexivity | reflexivity
  | ro_getr; rewrite ro_getr0, (cnb_regsat_get _ _ 23%bv 0 HR' ltac:(cnb7_in)); reflexivity |].
intros X4. cbv iota.
(* 1196: mv a0, s6; 1200: mv a1, s4; 1204: jal same *)
apply (cnb_hs_addiR WLE' W' fxk _ mem' _ _ 1196 1200 10%bv 22%bv 0); [cnb7_dec | reflexivity | lia | reflexivity |].
intros X5.
apply (cnb_hs_addiR WLE' W' fxk _ mem' _ _ 1200 1204 11%bv 20%bv 0); [cnb7_dec | reflexivity | lia | reflexivity |].
intros X6.
apply (cnb_hs_callR WLE' W' fxk _ mem' _ _ 1204 1208 AS_same); [cnb7_dec | lia | reflexivity |].
intros X7. apply (SRrG_ret SEGS WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)). split; [left | exact HPM'].
apply (cnb7_mk_same2 D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0).
- apply (cnb_base_matR B ARx LAWS WLE' D fxk ly' S Hp W' regs'); [repeat apply cnb7_base_md; exact HB'
  | ro_getr; reflexivity | ro_getr; reflexivity].
- cnb7_rs HR'.
- exact HSL'.
- exact HRC1'.
- exact HRC2'.
- exact Hr1.
- exact Hr2.
- exact Hr3.
- exact Hpg.
- exact Hranz.
- exact Hrds.
- exact HFO1'.
- exact HFO2'.
- exact HFO3'.
- exact HM'.
- exact Eck.
- exact HHB.
Qed.

(* ---- THE SECOND `same` STEP: the call (d1, d3), then 1208 / 1212 reload rc2 / rc1, 1216 beqz a0 falls through
   (a0 = 1: the abort edge at 1216 REFUTED by cnb7_same_one), 1220 bne a1, s7 and 1224 bne a2, s7 fall through
   (rc1 = rc2 = rc3 = 0: the abort edges at 1220 / 1224 REFUTED), 1228 mv s8, zero, 1232 j CNB_FREE: the free cut with
   r = 0. After a free: SRr' SEGS RZ_cf, the hand steps the kit's R forms at WLE' and this file's cnb7_hs_bne; the
   hull budget at rd0 rides to the free exit (S kept) ---- *)
Theorem cnb_same2_step : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0,
  CNBPRE D -> cnb_at_same2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 -> P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (CFG fxk (SIGMA AS_same) regs mem md)
    (fun W' c' => CNBFREE D W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 t D1 D2 D3 o1 o2 o0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HRC1 & HRC2 & Hr1 & Hr2 & Hr3 & Hpg & Hranz & Hrds & HFO1 & HFO2 & HFO3 & HM & Eck
  & HHB).
pose proof (cnb7_S1_rng D fxk ly S Hp W regs mem md k 6 HB) as (Hsp0 & Hhi & H47 & Hal16 & Hal32 & HS1a & HS1b & _).
pose proof asan_consts as (C1 & _). pose proof cnb7_stk as HSTK. pose proof cnb7_stk0 as HSTK0.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (cnb_same_call P PCALL D fxk ly S Hp W regs mem md k 6 Lam peak cnt r1 r2 r3
    (Some (t, D1)) (Some (t, D2)) (Some (t, D3)) t D1 D3 (cnb_d3 D) CNB7_RS2 HPRE);
  [ cbv [cnb7_same_rets In]; right; left; reflexivity | exact HB | exact (cnb7_rs_app_l _ _ _ HR)
  | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in
  | apply (cnb_regsat_get _ _ _ _ HR); cnb7_in | exact HSL | exact HM | reflexivity | right; split; reflexivity
  | exact HPM ]. }
intros W' c' _ (ly' & regs' & mem' & md' & k' & -> & HB' & HAP & H10 & Hab & HSL' & HM' & KF1 & KF2 & KF3 & HKT & HPM').
pose proof (KF1 o1 HFO1) as HFO1'. pose proof (KF2 o2 HFO2) as HFO2'. pose proof (KF3 o0 HFO3) as HFO3'.
clear KF1 KF2 KF3 HFO1 HFO2 HFO3.
assert (HR' : cnb_regsat regs' (cnb_core D ++ [(23%bv, 0); (24%bv, 1); (25%bv, r1)]))
  by (apply (cnb_regsat_pres regs regs'); [cnb7_rs HR | exact HAP | cnb7_cs]).
pose proof (cnb_rcslot_agree D W mem W' mem' 8 0 Hal16 ltac:(lia) HKT HRC1) as HRC1'.
pose proof (cnb_rcslot_agree D W mem W' mem' 0 0 Hal16 ltac:(lia) HKT HRC2) as HRC2'.
assert (G9' : getr regs' 9%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get _ _ _ _ HR'); cnb7_in).
assert (U9 : bv_unsigned (w64 (cnb_S1 D)) = cnb_S1 D) by (unfold w64; apply unsigned_lit_small; lia).
unfold CNB7_RS2.
(* 1208: ld a2, 0(s1); 1212: ld a1, 8(s1) *)
apply (cnb_hs_ldR WLE' W' fxk regs' mem' md' _ 1208 1212 12%bv 9%bv 0 (cnb_S1 D + 0) (0 mod 2 ^ 64));
  [cnb7_dec | reflexivity | lia | reflexivity | rewrite G9', U9; reflexivity | lia | lia | exact HRC2' |].
intros X1.
apply (cnb_hs_ldR WLE' W' fxk _ mem' _ _ 1212 1216 11%bv 9%bv 8 (cnb_S1 D + 8) (0 mod 2 ^ 64));
  [cnb7_dec | reflexivity | lia | reflexivity | ro_getr; rewrite G9', U9; reflexivity | lia | lia | exact HRC1' |].
intros X2.
(* 1216: beqz a0 falls through: a0 = 1 *)
apply (cnb_hs_beqzR WLE' W' fxk _ mem' _ _ 1216 10%bv 20 1236 1220 false);
  [cnb7_dec | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, H10; reflexivity |].
intros X3. cbv iota.
(* 1220: bne a1, s7; 1224: bne a2, s7 fall through: 0 = 0 *)
apply (cnb7_hs_bne W' fxk _ mem' _ _ 1220 11%bv 23%bv 16 1236 1224 true);
  [cnb7_dec | lia | lia | reflexivity | reflexivity
  | ro_getr; rewrite (cnb_regsat_get _ _ 23%bv 0 HR' ltac:(cnb7_in)); apply cnb7_c_eq_w64; reflexivity |].
intros X4. cbv iota.
apply (cnb7_hs_bne W' fxk _ mem' _ _ 1224 12%bv 23%bv 12 1236 1228 true);
  [cnb7_dec | lia | lia | reflexivity | reflexivity
  | ro_getr; rewrite (cnb_regsat_get _ _ 23%bv 0 HR' ltac:(cnb7_in)); apply cnb7_c_eq_w64; reflexivity |].
intros X5. cbv iota.
(* 1228: mv s8, zero; 1232: j CNB_FREE *)
apply (cnb_hs_addiR WLE' W' fxk _ mem' _ _ 1228 1232 24%bv 0%bv 0); [cnb7_dec | reflexivity | lia | reflexivity |].
intros X6.
apply (cnb_hs_jR WLE' W' fxk _ mem' _ _ 1232 740 (-492)); [cnb7_dec | lia | reflexivity | lia |].
intros X7. apply (SRrG_ret SEGS WLE' (wle'_refl SEGS YGcfRehidePost.RZ_cf)). split; [| exact HPM'].
apply (cnb7_mk_free D fxk ly' S Hp W' _ mem' _ k' Lam peak cnt 0 r1 r2 r3 0 0 (Some (t, D1)) (Some (t, D2)) (Some (t, D3))
  o1 o2 o0).
- apply (cnb_base_matR B ARx LAWS WLE' D fxk ly' S Hp W' regs'); [repeat apply cnb7_base_md; exact HB'
  | ro_getr; reflexivity | ro_getr; reflexivity].
- cnb7_rs HR'.
- exact HSL'.
- exact HM'.
- right. split; [reflexivity | split; reflexivity].
- intros _. exact (conj Hr1 (conj Hr2 (conj Hr3 (conj Hpg (conj Hranz (conj Hrds (conj HFO1' (conj HFO2' HFO3')))))))).
- reflexivity.
- exact HHB.
Qed.

End r7.

(* the audit: each lemma closed under the Section hypotheses (LAWS, IMG, HRO, HSAME) only *)
Print Assumptions cnb_cmp_seg.
Print Assumptions cnb_same_call.
Print Assumptions cnb_same1_step.
Print Assumptions cnb_same2_step.
Print Assumptions cnb7_hs_bne.
Check @cnb_cmp_seg.
Check @cnb_same_call.
Check @cnb_same1_step.
Check @cnb_same2_step.
