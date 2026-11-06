(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1165 of its 1242 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_E2.v, with its module paths and module names changed; 927 of its 1066 lines of code are new or changed and 1103 lines of the source are left out. *)
(* rule 24: no function proved
   rule 24: proves no function (kind: segment lemma)
   fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): the SHARED STEP KIT of the re-walk of
   check_no_overread (cno, B' entry 0x819f0) against the kit's text tcheck_no_overread_specX, sub-lane CutRo of lane
   CnoB102rR (a Theorem Labs lane, plan, the internal file PLAN-cno-caw-102.md 5.2). Segments CB4-CB7 (Cno102B_R4.v, Cno102B_Rpn.v,
   Cno102B_R7.v) and the CB0-CB3 / CB8-CB9 / top hands cite it. THE PORT of image A''s lib/A/Prog/Cno102A_Ro.v
   (cn_ -> cnb_, ci_ -> bi_, cni_ -> cnbi_, CN_ -> CNB_, the ro_ helpers under their names) to B''s offsets,
   registers, slots and to the #102 texts.
   INPUTS: THE KIT CUT a working branch 7cdbb61b5fa0, merged forward into the row at
   a working branch 75415fdb6e76: the contract lib/B/Prog/Cno102B_Base.v 20c89a1d4da2 (cnb_pre
   CTX0 D with no DW and the entry wild_room, cnb_J D wk the budgeted journal, cnb_base .. k wk, cnb_mid, cnb_fo,
   cnb_slots, cnb_rcslot, cnb_core, cnb_img B, cnb_prog, cnb_S1_bounds / cnb_land_m32 cited, not restated); the cut's
   the kit texts: lib/A/PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_alloc_ran_out_specX: the ledger `.. ran most own` with the same
   values in its post, fpostm, no wild site), lib/A/PRH_Base.v ef7c8ca98529 (fpre with its last conjunct `frm_zero
   (@YK11.fp_csr fx)`; src_rd, bytes_at, prh_ledger and its named projections, prh_hblock, prh_run_at_app_iff),
   lib/A/PRH_FnReader.v f1ae32e3b2cd (prhReader_home), lib/A/PRH_Reader.v 4266e709561a (garr8R_frame, pj_nodeR_frame,
   pj_zeroR_frame, pj_agreeR, pj_footR), lib/A/PRH_PjOrder.v e5917626b82b (pj_foR_frame); the run model
   lib/Spec/PresetReqAt.v 43c958024221 (hlive_from_app), PresetReqAtNoMiss.v f949715d7a12 (hlive_from_perm); listing
   lib/B/Listing_prog.v c97cc46b3e13 (slots 201 + off / 4: PCall AS_fuzz_alloc_ran_out 1 at offsets 604 / 648 / 692 /
   1140); the P'' engine set: lib/Reusable/YCbqG.v 219748197d6b (ajournal_xw read ONLY by the ajx_* projections,
   ajournal_x_materialize, the 25-field AR_laws_x read by its alx_* fields), YCbqGwild.v 0c63874858e4
   (ajournal_xw_rebase / ajournal_xw_unbase0, ajournal_xw_room, wild_room_le, wbudget_app), YCbqGcallW.v fb6aa11676a2
   (aj_call_xW); lib/A/Prog/PRW_StepKit.v 0df3991c13f4 (pa_slot_lt_ceil_b).
   Re-fit history: 9bfc2ee2ce11 (caa965672d2 texts); 881db0c5c1ad (Batch 2: own after ran, carried by the ledger);
   a third fit (this file's blob 812ff405cc0e; the #102 kit: frm_zero at the callee's fpre; the progress lemmas); this one (the cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record): no
   DW, cnb_base's spent wild budget wk kept across the fixed callee fuzz_alloc_ran_out by rebase / aj_call_xW /
   unbase, the journal and the laws read by name, the budget lemmas, the tree's free order cnb_fo carried across a
   call).
   WHAT IS HERE (all generic in {PA : PAImg B_prog_listing}, B, ARx, SK; P abstract):
   - hand steps over cnb_cfg configurations (no engine): cnb_hs_addi / cnb_hs_ld / cnb_hs_lbu / cnb_hs_beqz /
     cnb_hs_bnez / cnb_hs_j by the closed decode checks cnb_is_*, and cnb_hs_call (the PCall jal: pc = SIGMA s,
     ra = the next offset); each step reads memory only, so the memory (and P of it) is unchanged and the model moves
     to a materialised copy;
   - the slot-agree lemmas: the body's real-stack slots (cnb_slots, cnb_rcslot) follow from the bytes of
     [cnb_S1 D, cnb_sp0 D);
   - the progress lemmas over the Base's cnb_prog: cnb_prog_nil, cnb_prog_eq, cnb_prog_same, cnb_prog_app;
   - cnb_pre's conjuncts by type: cnb_pre_fpre, cnb_pre_home, cnb_pre_ledger, cnb_pre_room;
   - THE BUDGETED JOURNAL: cnb_J_mono / cnb_base_mono (a larger spent budget); cnb_J_rebase (the walk's journal as the
     empty-budget journal from the entry with its depot moved to the current one, what a fixed-trace call rule takes)
     and cnb_J_fixed (after a fixed-trace callee, the caller's journal from that rebased entry is cnb_J at the SAME
     wk); cnb_J_wild (after parse_noting, the caller's journal at WS0 ++ WS1 is cnb_J at wk + prh_wk F_parse_noting);
     cnb_room (parse_noting's room from cnb_pre's entry room and the cut's spent budget, a Theorem Labs lane's ec_room_at
     pattern); cnb_J_mat;
   - cnb_fo_keep: the tree's free order (cnb_fo) across a memory change that keeps the tree's footprint, by
     PRH_PjOrder.pj_foR_frame;
   - cnb_base_mat: cnb_base at the materialised model and a register file that keeps gp / tp;
   - cnb_entry_facts, cnb_chain: the frame chain at any cno call state (s0 = the entry sp: the record (sp0, entry ra,
     entry s0) from cnb_saved :152 / :144, then the entry's chain, kept above sp0 by the journal; [] when sp0 is within
     16 bytes of the stack top);
   - cnb_call_keep: across a kit call whose post is fpostm with FP = [] and S' = S, Hp' = Hp, ablocks kept, the ledger
     restated with the same values (g_most = bi_most D and the cut's own among them): from the caller's journal of
     the rebased entry (aj_call_xW's first journal at cnb_J_rebase's), cnb_base at the same wk / cnb_slots / cnb_mid /
     the three structs' cnb_fo at the post state (frame and stack bytes by the callee journal's frame and stack
     clauses, live block bytes by its block clause, block shadow by AR_laws_x's alx_shadow at the post state, tree
     blocks through PRH_Reader's / PRH_PjOrder's frame lemmas, arodata_okP and the input bytes of image homes by the
     image clause with cnb_img's cnbi_pst_rw), and the bytes of [cnb_S1 D, cnb_sp0 D) kept;
   - cnb_ro_call: the call to fuzz_alloc_ran_out at the callee entry (rebase, aj_call_xW, the text HRO for any float
     state, fpre's raZ bound from the closed lemma cnb_ro_ret_ok, P across by srr_inv_call at the text's memnorm keep,
     unbase in cnb_call_keep); its post carries the cut's wk and own, the structs' cnb_fo and the body stack's bytes.
   THE FREE / REALLOC MOVE (a parse_noting call can free or realloc a live block and hide shadow again, so the cuts
   after the first parse_noting hold the journal at wle' SEGS RZ_cf, the Base's cnb_baseR / cnb_JR at that relation,
   and their segments conclude SRr' SEGS RZ_cf): every lemma above that reads the world relation is stated over any
   relation R, and its old name is that form at wle (`Proof. exact (XR (@wle SEGS)). Qed.`): the hand steps
   cnb_stepR / cnb_hs_*R (a step keeps the world: YSRrG.SRrG_step), cnb_J_monoR / cnb_base_monoR, cnb_J_rebaseR /
   cnb_J_fixedR / cnb_J_wildR / cnb_roomR / cnb_J_matR (YCbqGwild.ajournal_xw_rebaseR / _unbase0R / _roomR,
   YCbqG.ajournal_x_materializeR, the ajxR_* projections), cnb_base_matR, cnb_chainR, cnb_call_keepR (no law of R)
   and cnb_ro_callR (R reflexive, transitive and containing wle: aj_call_xWR at R; tfuzz_alloc_ran_out_specX is not
   a crossing text and stays plain, so its SRr is lifted by YA0nH.SRr_SRrG and its post by
   YCbqG.apost_base_x_R_lift, then fpostW_x_of_apostR). The lift of a cut before any free into wle' is the Base's
   cnb_baseR_mono / cnb_JR_mono at YA0nH.wle_wle'. fuzz_alloc_ran_out keeps S, so a cut's allocator hull conjunct (a
   budget at the cut's S, outside cnb_baseR) rides every call here unchanged.
   Numerals: 604 .. 1144 (DERIVED: byte offsets inside cno, the cuts of Cno102B_Base.v and the listing's slots);
   160 / 192 / 32 / 16 / 8 / 56 / 64 / 512 / 48 / 24 / 152 / 144 / 128 / 224 (LENGTH: frame, alignment, slot and
   struct sizes, the class-3 frame and its shadow); register numbers (WORD); 2 ^ 28 / 2 ^ 29 / 2 ^ 40 / 2 ^ 64
   (LENGTH: offset, code span and word bounds). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling (Cno102B_Base.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off globally; this file's arithmetic on the
   frame, struct and shadow offsets needs it on (S4_PsU.v's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- pure helpers ---- *)
(* two distinct-base members of a pairwise-disjoint mapped list are disjoint *)
Lemma ro_pairwise_map : forall (f : Z * Z -> Z * Z) (l : list (Z * Z)) x y,
  pairwise zdisjoint (map f l) -> In x l -> In y l -> fst x <> fst y -> zdisjoint (f x) (f y).
Proof.
intros f l. induction l as [|z t IH]; intros x y H Hx Hy Hne; [destruct Hx|].
cbn [map pairwise] in H. destruct H as [Hz Ht].
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. apply Hne. reflexivity.
- exact (proj1 (Forall_forall _ _) Hz (f y) (in_map f t y Hy)).
- pose proof (proj1 (Forall_forall _ _) Hz (f x) (in_map f t x Hx)) as Hd. unfold zdisjoint in *. lia.
- exact (IH x y Ht Hx Hy Hne).
Qed.

Lemma ro_hull_mono : forall (rd : reader) x n n', 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn H s Hs. apply H.
assert (E1 : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1))
  by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (E2 : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

Lemma ro_div8 : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof.
intros a. pose proof (Z.div_mod a 8 ltac:(lia)) as H1. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as H2.
revert H1 H2. generalize (a / 8) (a mod 8). intros q r H1 H2. lia.
Qed.

Lemma ro_rdword_kept : forall (rd rd' : reader) lo hi x,
  (forall a, lo <= a < hi -> rd' a = rd a) -> lo <= x -> x + 8 <= hi -> rdword rd' x = rdword rd x.
Proof. intros rd rd' lo hi x Hk H1 H2. apply rdword_ext. intros kk Hkk. apply Hk. lia. Qed.

Lemma ro_getr_same : forall regs (r : bv 5) v, bv_eqb r 0%bv = false -> getr (regupd regs r v) r = v.
Proof. intros regs r v H. apply getr_same. intros E. subst r. discriminate H. Qed.
Lemma ro_getr_other : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. apply getr_other. intros E. subst r'. rewrite bv_eqb_refl in H. discriminate H. Qed.
Ltac ro_getr := repeat first [rewrite ro_getr_same by reflexivity | rewrite ro_getr_other by reflexivity].

Lemma ro_getr0 : forall regs, getr regs 0%bv = Z_to_bv 64 0.
Proof. intros regs. reflexivity. Qed.
Lemma ro_li : forall regs (imm : bv 12), v_addi (getr regs 0%bv) (bv_signed imm) = w64 (bv_signed imm).
Proof. intros regs imm. rewrite ro_getr0. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal. Qed.
Lemma ro_mv : forall (x : word), v_addi x (bv_signed (0%bv : bv 12)) = x.
Proof. intros x. unfold v_addi. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma ro_c_eq0 : forall v, 0 <= v < 2 ^ 64 -> c_eq (w64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold c_eq, bv_eqb, w64. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma ro_bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma ro_rdn1 : forall segs (m : word -> option byte) a b, mbyte segs m a = Some b -> rdn segs m (Z_to_bv 64 a) 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. unfold mbyte in H. rewrite H. reflexivity. Qed.

(* the register snapshot *)
Lemma cnb_regsat_get : forall regs l (r : bv 5) v, cnb_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma cnb_regsat_kept : forall regs regs' l, cnb_regsat regs l ->
  Forall (fun p : bv 5 * Z => getr regs' (fst p) = getr regs (fst p)) l -> cnb_regsat regs' l.
Proof.
intros regs regs' l H K. unfold cnb_regsat in *. rewrite Forall_forall in *. intros p Hp.
rewrite (K p Hp). exact (H p Hp).
Qed.
Lemma cnb_regsat_pres : forall regs regs' l, cnb_regsat regs l -> aregs_preserved regs regs' ->
  Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) l -> cnb_regsat regs' l.
Proof.
intros regs regs' l H HP HF. apply (cnb_regsat_kept regs regs' l H). rewrite Forall_forall in *.
intros [r v] Hin. cbn [fst]. specialize (HF (r, v) Hin). cbn [fst] in HF.
pose proof (HP (bv_unsigned r) HF) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.
Ltac ro_in := cbn [app In]; repeat (first [left; reflexivity | right]).
(* a conjunct of a conjunction chain BY ITS TYPE: cnb_pre, the kit texts' fpre / afn_pre_x, layout_le and prh_hblock
   carry no projections, so a read names the conjunct's statement, never its position *)
Ltac ro_pick H := repeat (first [exact H | exact (proj1 H) | apply proj2 in H]).
Ltac ro_from H := let H' := fresh "Hpk" in pose proof H as H'; ro_pick H'.

(* ---- THE RAN-OUT RETURN SITES (B' 0x81c44 / 0x81c70 / 0x81c9c / 0x81e78; the jal at offset - 4) and the closed
   slot check fpre's raZ bound reads (a closed lemma: the vm_compute guard) ---- *)
Definition cnb_ro_rets : list Z := [608; 652; 696; 1144].
Lemma cnb_ro_slots : forall ret, In ret cnb_ro_rets ->
  match plookup B_prog_tpi_cno (CNB_OFF + ret) with Some _ => true | None => false end = true.
Proof.
intros ret Hin. cbn [cnb_ro_rets In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  lazymatch goal with |- match plookup B_prog_tpi_cno (CNB_OFF + _) with Some _ => true | None => false end = true =>
    vm_compute; reflexivity end.
Qed.

Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma cnb_off_val : CNB_OFF = 804.
Proof. reflexivity. Qed.

(* ---- the hand steps: one instruction, memory read only. Each is stated over any world relation R (a step keeps
   the world, so no law of R is used: YSRrG.SRrG_step); the walk before a free uses the plain form, which is the R
   form at wle, and a walk after one the R form at wle' SEGS RZ_cf ---- *)
Lemma cnb_stepR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md regs' off off' Q,
  0 <= off < 2 ^ 29 -> 0 <= off' < 2 ^ 29 ->
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs' (Z_to_bv 64 (BASE + (CNB_OFF + off'))) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md regs' off off' Q Ho Ho' Hst HK.
unfold cnb_cfg, cnb_pc, w64. replace (BASE + CNB_OFF + off) with (BASE + (CNB_OFF + off)) by lia.
eapply (SRrG_step SEGS R pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cnb_cfg, cnb_pc, w64 in HK.
replace (BASE + CNB_OFF + off') with (BASE + (CNB_OFF + off')) in HK by lia. exact HK.
Qed.
Lemma cnb_step : forall (W : world SEGS) fxk regs mem md regs' off off' Q,
  0 <= off < 2 ^ 29 -> 0 <= off' < 2 ^ 29 ->
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CNB_OFF + off))) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs' (Z_to_bv 64 (BASE + (CNB_OFF + off'))) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_stepR (@wle SEGS)). Qed.

Lemma cnb_pc4 : forall off, 0 <= off < 2 ^ 29 ->
  v_addi (Z_to_bv 64 (BASE + (CNB_OFF + off))) 4 = Z_to_bv 64 (BASE + (CNB_OFF + (off + 4))).
Proof.
intros off Ho. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cnb_off_val as HO.
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
Lemma cnb_pcj : forall off (j : Z), 0 <= off < 2 ^ 29 -> 0 <= off + j < 2 ^ 29 ->
  v_addi (Z_to_bv 64 (BASE + (CNB_OFF + off))) j = Z_to_bv 64 (BASE + (CNB_OFF + (off + j))).
Proof.
intros off j Ho Hj. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cnb_off_val as HO.
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma cnb_hs_addi0R : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' w rd rs imm,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' w rd rs imm Hpl Hdec Hrd Ho -> HK.
apply (cnb_stepR R W fxk regs mem md (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_addi fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm
  (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
rewrite Hrd, (cnb_pc4 off ltac:(lia)). reflexivity.
Qed.

Lemma cnb_hs_ld0R : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' w rd rs imm a v,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + bv_signed imm = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (w64 v)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' w rd rs imm a v Hpl Hdec Hrd Ho -> Ha Ha0 Ha8 Hv HK.
apply (cnb_stepR R W fxk regs mem md (regupd regs rd (w64 v)) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hv) as Hvm.
destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hvm Ha0 Ha8) as (bs & Hbs & Hbv).
assert (Eaddr : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
rewrite (@step_ld fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm bs (Z_to_bv 64 v)
  (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
  ltac:(rewrite Eaddr; exact Hbs) Hbv).
rewrite Hrd, (cnb_pc4 off ltac:(lia)). reflexivity.
Qed.

Lemma cnb_hs_lbu0R : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' w rd rs imm a b,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + bv_signed imm = a ->
  mbyte SEGS (mrestrict (w_H W) mem) a = Some b ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' w rd rs imm a b Hpl Hdec Hrd Ho -> Ha Hb HK.
apply (cnb_stepR R W fxk regs mem md (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
assert (Eaddr : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
rewrite (@step_lbu fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm b
  (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
  ltac:(rewrite Eaddr; exact (ro_rdn1 SEGS _ a b Hb))).
rewrite Hrd, (cnb_pc4 off ltac:(lia)). reflexivity.
Qed.

(* `beqz rs, imm`: taken when the register is zero *)
Lemma cnb_hs_beqz0R : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off w rs imm (z : bool),
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> 0 <= off + bv_signed imm < 2 ^ 28 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc (if z then off + bv_signed imm else off + 4)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off w rs imm z Hpl Hdec Ho Hj Hc HK.
pose proof (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as He.
destruct z.
- apply (cnb_stepR R W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_beq_tk fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  unfold btgt. rewrite (cnb_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
- apply (cnb_stepR R W fxk regs mem md regs off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_beq_ft fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  rewrite (cnb_pc4 off ltac:(lia)). reflexivity.
Qed.

(* `bnez rs, imm`: taken when the register is non-zero *)
Lemma cnb_hs_bnez0R : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off w rs imm (z : bool),
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> 0 <= off + bv_signed imm < 2 ^ 28 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc (if z then off + 4 else off + bv_signed imm)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off w rs imm z Hpl Hdec Ho Hj Hc HK.
pose proof (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as He.
destruct z.
- apply (cnb_stepR R W fxk regs mem md regs off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_ft fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  rewrite (cnb_pc4 off ltac:(lia)). reflexivity.
- apply (cnb_stepR R W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_tk fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  unfold btgt. rewrite (cnb_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

(* `j imm` *)
Lemma cnb_hs_j0R : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' w imm,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Jal 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> off' = off + bv_signed imm -> 0 <= off' < 2 ^ 28 ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' w imm Hpl Hdec Ho -> Hj HK.
apply (cnb_stepR R W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 0%bv imm
  (@pa_fetch_pw _ _ PL_cno_B PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
unfold btgt. rewrite (cnb_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

(* the PCall jal of a listing slot: pc = SIGMA s, ra = the next offset *)
Lemma cnb_hs_callR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' s,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PCall s 1%bv) -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (SIGMA s) (regupd regs 1%bv (w64 (cnb_pc off'))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' s Hpl Ho -> HK.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cnb_off_val as HO.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert (CNB_OFF + off) (PCall s 1%bv) Hpl)
  as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (CNB_OFF + off))) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hck & Hsig). apply andb_prop in Hck as (Hrd & _). apply Z.eqb_eq in Hsig.
assert (Erd : rd = 1%bv).
{ unfold bv_eqb in Hrd. apply Z.eqb_eq in Hrd. apply bv_eq. symmetry. exact Hrd. }
subst rd.
pose proof (pa_fetch_ok _ _ Hf) as Hfw.
unfold cnb_cfg, cnb_pc, w64. replace (BASE + CNB_OFF + off) with (BASE + (CNB_OFF + off)) by lia.
eapply (SRrG_step SEGS R pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk);
  exact (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 1%bv imm Hfw
           (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cnb_cfg, cnb_pc, w64 in HK.
replace (BASE + CNB_OFF + (off + 4)) with (BASE + (CNB_OFF + (off + 4))) in HK by lia.
change (bv_eqb (1%bv : bv 5) 0%bv) with false. cbv iota.
rewrite (cnb_pc4 off ltac:(lia)).
replace (btgt (Z_to_bv 64 (BASE + (CNB_OFF + off))) (bv_signed imm)) with (Z_to_bv 64 (SIGMA s)); [exact HK|].
unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Hsig.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma cnb_hs_call : forall (W : world SEGS) fxk regs mem md Q off off' s,
  plookup B_prog_tpi_cno (CNB_OFF + off) = Some (PCall s 1%bv) -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (SIGMA s) (regupd regs 1%bv (w64 (cnb_pc off'))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_callR (@wle SEGS)). Qed.

(* the decoded word of an offset, and the closed boolean checks a walk discharges by vm_compute on the CLOSED goal
   (a decoded bv is convertible to a literal only up to its well-formedness proof, so the checks compare
   bv_unsigned, never the bv) *)
Definition cnb_dec (off : Z) : option (instr * Z) :=
  match plookup B_prog_tpi_cno (CNB_OFF + off) with Some (PW w) => decode_any (Z_to_bv 32 w) | _ => None end.
Definition cnb_is_addi (off : Z) (rd rs : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (OpImm ALU_ADD rd' rs' imm, sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? i)
  | _ => false end.
Definition cnb_is_ld (off : Z) (rd rs : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Load SZ8 true rd' rs' imm, sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? i)
  | _ => false end.
Definition cnb_is_lbu (off : Z) (rd rs : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Load SZ1 false rd' rs' imm, sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? i)
  | _ => false end.
Definition cnb_is_beqz (off : Z) (rs : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Branch BC_EQ rs' r0 imm, sz) => (sz =? 4) && bv_eqb rs' rs && bv_eqb r0 0%bv && (bv_signed imm =? i)
  | _ => false end.
Definition cnb_is_bnez (off : Z) (rs : bv 5) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Branch BC_NE rs' r0 imm, sz) => (sz =? 4) && bv_eqb rs' rs && bv_eqb r0 0%bv && (bv_signed imm =? i)
  | _ => false end.
Definition cnb_is_j (off : Z) (i : Z) : bool :=
  match cnb_dec off with
  | Some (Jal rd' imm, sz) => (sz =? 4) && bv_eqb rd' 0%bv && (bv_signed imm =? i)
  | _ => false end.

Ltac cnb_bools := repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : bv_eqb _ _ = true |- _ => apply ro_bv_eqb_eq in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end; subst.
Ltac cnb_open H := unfold cnb_is_addi, cnb_is_ld, cnb_is_lbu, cnb_is_beqz, cnb_is_bnez, cnb_is_j, cnb_dec in H;
  let Hpl := fresh "Hpl" in let Hdec := fresh "Hdec" in
  let e := fresh "e" in let ii := fresh "ii" in let sz := fresh "sz" in
  match type of H with context [plookup B_prog_tpi_cno ?k] =>
    destruct (plookup B_prog_tpi_cno k) as [e|] eqn:Hpl; [|discriminate H] end;
  destruct e; try (cbv beta iota in H; discriminate H);
  match type of H with context [decode_any ?x] => destruct (decode_any x) as [[ii sz]|] eqn:Hdec; [|discriminate H] end;
  destruct ii; try (cbv beta iota in H; discriminate H);
  repeat match goal with
  | Hd : decode_any _ = Some (OpImm ?o _ _ _, _) |- _ => is_var o; destruct o; try (cbv beta iota in H; discriminate H)
  | Hd : decode_any _ = Some (Load ?z _ _ _ _, _) |- _ => is_var z; destruct z; try (cbv beta iota in H; discriminate H)
  | Hd : decode_any _ = Some (Load _ ?g _ _ _, _) |- _ => is_var g; destruct g; try (cbv beta iota in H; discriminate H)
  | Hd : decode_any _ = Some (Branch ?c _ _ _, _) |- _ => is_var c; destruct c; try (cbv beta iota in H; discriminate H)
  end;
  cbv beta iota in H; cnb_bools.

Lemma cnb_hs_addiR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' rd rs i,
  cnb_is_addi off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (v_addi (getr regs rs) i)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' rd rs i H. cnb_open H. intros Hrd Ho -> HK.
eapply (cnb_hs_addi0R R); [exact Hpl | exact Hdec | exact Hrd | exact Ho | reflexivity | exact HK].
Qed.
Lemma cnb_hs_addi : forall (W : world SEGS) fxk regs mem md Q off off' rd rs i,
  cnb_is_addi off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (v_addi (getr regs rs) i)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_addiR (@wle SEGS)). Qed.
Lemma cnb_hs_ldR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' rd rs i a v,
  cnb_is_ld off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + i = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (w64 v)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' rd rs i a v H. cnb_open H. intros Hrd Ho -> Ha Ha0 Ha8 Hv HK.
eapply (cnb_hs_ld0R R); [exact Hpl | exact Hdec | exact Hrd | exact Ho | reflexivity | exact Ha | exact Ha0 | exact Ha8
  | exact Hv | exact HK].
Qed.
Lemma cnb_hs_ld : forall (W : world SEGS) fxk regs mem md Q off off' rd rs i a v,
  cnb_is_ld off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + i = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (w64 v)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_ldR (@wle SEGS)). Qed.
Lemma cnb_hs_lbuR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' rd rs i a b,
  cnb_is_lbu off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + i = a ->
  mbyte SEGS (mrestrict (w_H W) mem) a = Some b ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' rd rs i a b H. cnb_open H. intros Hrd Ho -> Ha Hb HK.
eapply (cnb_hs_lbu0R R); [exact Hpl | exact Hdec | exact Hrd | exact Ho | reflexivity | exact Ha | exact Hb | exact HK].
Qed.
Lemma cnb_hs_lbu : forall (W : world SEGS) fxk regs mem md Q off off' rd rs i a b,
  cnb_is_lbu off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + i = a ->
  mbyte SEGS (mrestrict (w_H W) mem) a = Some b ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_lbuR (@wle SEGS)). Qed.
(* `beqz rs`: z the register's zero test, tk / ft the taken / fall-through offsets *)
Lemma cnb_hs_beqzR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off rs i tk ft (z : bool),
  cnb_is_beqz off rs i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc (if z then tk else ft)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off rs i tk ft z H. cnb_open H. intros Ho Hj -> -> Hc HK.
eapply (cnb_hs_beqz0R R); [exact Hpl | exact Hdec | exact Ho | exact Hj | exact Hc | exact HK].
Qed.
Lemma cnb_hs_beqz : forall (W : world SEGS) fxk regs mem md Q off rs i tk ft (z : bool),
  cnb_is_beqz off rs i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc (if z then tk else ft)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_beqzR (@wle SEGS)). Qed.
(* `bnez rs`: taken when the register is non-zero (z = false) *)
Lemma cnb_hs_bnezR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off rs i tk ft (z : bool),
  cnb_is_bnez off rs i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc (if z then ft else tk)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off rs i tk ft z H. cnb_open H. intros Ho Hj -> -> Hc HK.
eapply (cnb_hs_bnez0R R); [exact Hpl | exact Hdec | exact Ho | exact Hj | exact Hc | exact HK].
Qed.
Lemma cnb_hs_bnez : forall (W : world SEGS) fxk regs mem md Q off rs i tk ft (z : bool),
  cnb_is_bnez off rs i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc (if z then ft else tk)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_bnezR (@wle SEGS)). Qed.
Lemma cnb_hs_jR : forall (R : world SEGS -> world SEGS -> Prop)
    (W : world SEGS) fxk regs mem md Q off off' i,
  cnb_is_j off i = true -> 0 <= off < 2 ^ 28 -> off' = off + i -> 0 <= off' < 2 ^ 28 ->
  (forall X, SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off') regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof.
intros R W fxk regs mem md Q off off' i H. cnb_open H. intros Ho -> Hj HK.
eapply (cnb_hs_j0R R); [exact Hpl | exact Hdec | exact Ho | reflexivity | exact Hj | exact HK].
Qed.
Lemma cnb_hs_j : forall (W : world SEGS) fxk regs mem md Q off off' i,
  cnb_is_j off i = true -> 0 <= off < 2 ^ 28 -> off' = off + i -> 0 <= off' < 2 ^ 28 ->
  (forall X, SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off') regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc off) regs mem md) Q.
Proof. exact (cnb_hs_jR (@wle SEGS)). Qed.

(* ---- THE BODY'S REAL-STACK SLOTS from the bytes of [s1, entry sp) (world types explicit) ---- *)
Lemma cnb_slot_agree : forall D (W : world SEGS) mem (W2 : world SEGS) mem2 o v,
  cnb_sp0 D mod 16 = 0 -> 0 <= o <= 152 ->
  (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  rdword (aview SEGS (w_H W) mem) (cnb_S1 D + o) = Some v -> rdword (aview SEGS (w_H W2) mem2) (cnb_S1 D + o) = Some v.
Proof.
intros D W mem W2 mem2 o v H16 Ho HA H. pose proof (cnb_S1_bounds D H16) as (Hb1 & Hb2 & _).
rewrite <- H. apply rdword_ext. intros kk Hk. apply HA. lia.
Qed.
Lemma cnb_slots_agree : forall D (W : world SEGS) mem (W2 : world SEGS) mem2 r2 r3,
  cnb_sp0 D mod 16 = 0 ->
  (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  cnb_slots D W mem r2 r3 -> cnb_slots D W2 mem2 r2 r3.
Proof.
intros D W mem W2 mem2 r2 r3 H16 HA HSL. unfold cnb_slots in *.
inversion HSL as [|? ? H48 HSL1]; inversion HSL1 as [|? ? H24 HSL2]; inversion HSL2 as [|? ? H16' _].
cbn [fst snd] in *.
repeat constructor; cbn [fst snd]; eapply cnb_slot_agree; eauto; lia.
Qed.
Lemma cnb_rcslot_agree : forall D (W : world SEGS) mem (W2 : world SEGS) mem2 o v,
  cnb_sp0 D mod 16 = 0 -> 0 <= o <= 152 ->
  (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
  cnb_rcslot D W mem o v -> cnb_rcslot D W2 mem2 o v.
Proof. intros D W mem W2 mem2 o v H16 Ho HA H. unfold cnb_rcslot in *. eapply cnb_slot_agree; eauto. Qed.

(* ---- THE PROGRESS FACT across segments (the Base's cnb_prog: the live set and the run position after the events
   made since entry) ---- *)
(* no event yet, at the entry state *)
Lemma cnb_prog_nil : forall D, cnb_prog D [] (bi_S D).
Proof.
intros D. split; [rewrite PresetReqAt.hlive_from_nil; apply Permutation_refl|].
intros sm x0 os i H0 hist Hpos _. exists hist. replace (i + length (@nil PresetReqAt.hev))%nat with i by (cbn; lia).
exact Hpos.
Qed.
(* an equal event list (app_nil_r at a skipped reading, the pieces' regrouping) *)
Lemma cnb_prog_eq : forall D E E' S, E = E' -> cnb_prog D E S -> cnb_prog D E' S.
Proof. intros D E E' S <- H. exact H. Qed.
(* a call that keeps the allocator state (tsame_specX's and tfuzz_alloc_ran_out_specX's S' = S) keeps the fact *)
Lemma cnb_prog_same : forall D E S S', S' = S -> cnb_prog D E S -> cnb_prog D E S'.
Proof. intros D E S S' -> H. exact H. Qed.
(* a callee that makes events E' (a post-implication text: the exact live set after E' and, for any run position at
   its entry state whose next events are E', the position after them) extends the fact by E' *)
Lemma cnb_prog_app : forall D E E' S S',
  cnb_prog D E S ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E') ->
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist S -> prh_run_at sm x0 os i E' ->
     exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length E')%nat H0 hist' S') ->
  cnb_prog D (E ++ E') S'.
Proof.
intros D E E' S S' (HL & HP) HL' HP'. split.
- rewrite PresetReqAt.hlive_from_app. apply (Permutation_trans HL').
  apply PresetReqAtNoMiss.hlive_from_perm. exact HL.
- intros sm x0 os i H0 hist Hpos Hrun. apply prh_run_at_app_iff in Hrun as (R1 & R2).
  destruct (HP sm x0 os i H0 hist Hpos R1) as (hist1 & Hpos1).
  destruct (HP' sm x0 os (i + length E)%nat H0 hist1 Hpos1 R2) as (hist2 & Hpos2).
  exists hist2. rewrite length_app, Nat.add_assoc. exact Hpos2.
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).
#[local] Notation AJW := (ajournal_xw (SK := SK) SEGS B prh_pst ARx).
#[local] Notation AJR R := (ajournal_xR (SK := SK) SEGS B prh_pst ARx R).
#[local] Notation AJWR R := (ajournal_xwR (SK := SK) SEGS B prh_pst ARx R).
#[local] Notation STK := STK_check_no_overread.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cnb_img B.

Lemma cnb_stk_val : STK = 27392.
Proof. lazymatch goal with |- STK_check_no_overread = _ => vm_compute; reflexivity end. Qed.
Lemma cnb_stk_ro_val : STK_fuzz_alloc_ran_out = 0.
Proof. lazymatch goal with |- STK_fuzz_alloc_ran_out = _ => vm_compute; reflexivity end. Qed.

(* ---- cnb_pre's conjuncts the kit reads, BY TYPE (the Base restates the text's premises verbatim) ---- *)
Lemma cnb_pre_fpre : forall CTX0 D, cnb_pre (fx := fx) B ARx CTX0 D ->
  fpre (fx := fx) B ARx STK (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_regs D) (bi_mem D) (bi_md D) (bi_ch D).
Proof. intros CTX0 D H. unfold cnb_pre in H. cbv zeta in H. ro_pick H. Qed.
Lemma cnb_pre_home : forall CTX0 D, cnb_pre (fx := fx) B ARx CTX0 D ->
  0 < cnb_size D -> PRH_FnReader.prhReader_home B (bi_ly D) (bi_S D) (bi_Hp D) (bi_Lam D) (bi_data D) (cnb_size D).
Proof. intros CTX0 D H. unfold cnb_pre in H. cbv zeta in H. ro_pick H. Qed.
Lemma cnb_pre_ledger : forall CTX0 D, cnb_pre (fx := fx) B ARx CTX0 D ->
  prh_ledger B (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D)
    (bi_most D) 0.
Proof. intros CTX0 D H. unfold cnb_pre in H. cbv zeta in H. ro_pick H. Qed.
Lemma cnb_pre_room : forall CTX0 D, cnb_pre (fx := fx) B ARx CTX0 D ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot (bi_S D)).
Proof. intros CTX0 D H. unfold cnb_pre in H. cbv zeta in H. ro_pick H. Qed.

(* a harness block's facts the transfer reads (PRH_Base.prh_hblock, by type) *)
Lemma ro_hblock : forall ly S Hp (W : world SEGS) mem a kk, prh_hblock B ly S Hp W mem a kk ->
  0 <= kk /\ In (a - cf_head, kk + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof. intros ly S Hp W mem a kk H. unfold prh_hblock in H. split; [|split]; ro_from H. Qed.

(* ---- THE BUDGETED JOURNAL (the Base's cnb_JR R D wk: ajournal_xwR R from the entry at a budget WS with wbudget [] wk
   WS; read only through the ajxR_* projections, YCbqG.v). Each lemma is stated over any world relation R (the walk's
   cuts after the first parse_noting hold the journal at wle' SEGS RZ_cf); the plain name is its form at wle, where
   cnb_J / cnb_base are cnb_JR / cnb_baseR at wle (Cno102B_Base.v cnb_J_R_wle / cnb_base_R_wle) ---- *)
(* a larger spent budget (wbudget is monotone in wk) *)
Lemma cnb_J_monoR : forall (R : world SEGS -> world SEGS -> Prop) D wk wk' ly S Hp W mem md k, (wk <= wk')%nat ->
  cnb_JR B ARx R D wk ly S Hp W mem md k -> cnb_JR B ARx R D wk' ly S Hp W mem md k.
Proof.
intros R D wk wk' ly S Hp W mem md k Hle (WS & HJ & HWB). exists WS. split; [exact HJ|].
unfold YCbqGwild.wbudget in *. lia.
Qed.
Lemma cnb_J_mono : forall D wk wk' ly S Hp W mem md k, (wk <= wk')%nat ->
  cnb_J B ARx D wk ly S Hp W mem md k -> cnb_J B ARx D wk' ly S Hp W mem md k.
Proof. exact (cnb_J_monoR (@wle SEGS)). Qed.
Lemma cnb_base_monoR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs mem md k wk wk',
  (wk <= wk')%nat ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk'.
Proof.
intros R D fxk ly S Hp W regs mem md k wk wk' Hle (Hz & Hk & HJ & HR).
split; [exact Hz|]. split; [exact Hk|]. split; [exact (cnb_J_monoR R D wk wk' ly S Hp W mem md k Hle HJ) | exact HR].
Qed.
Lemma cnb_base_mono : forall D fxk ly S Hp W regs mem md k wk wk', (wk <= wk')%nat ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk'.
Proof. exact (cnb_base_monoR (@wle SEGS)). Qed.
(* THE REBASE: the walk's journal as the empty-budget journal from the entry with its depot moved to the current
   one (YCbqGwild.ajournal_xw_rebaseR), the journal a fixed-trace call rule (YCbqGcallW.aj_call_xWR) takes *)
Lemma cnb_J_rebaseR : forall (R : world SEGS -> world SEGS -> Prop) D wk ly S Hp W mem md k,
  cnb_JR B ARx R D wk ly S Hp W mem md k ->
  AJR R STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly S Hp W mem md k.
Proof.
intros R D wk ly S Hp W mem md k (WS & HJ & _).
eapply YCbqGwild.ajournal_xw_rebaseR. exact HJ.
Qed.
Lemma cnb_J_rebase : forall D wk ly S Hp W mem md k,
  cnb_J B ARx D wk ly S Hp W mem md k ->
  AJ STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly S Hp W mem md k.
Proof. exact (cnb_J_rebaseR (@wle SEGS)). Qed.
(* THE UNBASE after a FIXED-trace callee (fuzz_alloc_ran_out, same, pj_free, the __wrap_free rows): the caller's
   journal from the rebased entry of the call state (aj_call_xWR's first journal) is cnb_JR at the return state at
   the SAME spent budget (YCbqGwild.ajournal_xw_unbase0R with the call state's ajxR_wild) *)
Lemma cnb_J_fixedR : forall (R : world SEGS -> world SEGS -> Prop) D wk ly S Hp W mem md k ly' S' Hp' W' mem' md' k',
  cnb_JR B ARx R D wk ly S Hp W mem md k ->
  AJR R STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly' S' Hp' W' mem' md' k' ->
  cnb_JR B ARx R D wk ly' S' Hp' W' mem' md' k'.
Proof.
intros R D wk ly S Hp W mem md k ly' S' Hp' W' mem' md' k' (WS & HJ & HWB) HJ2.
exists WS. split; [|exact HWB].
eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ2 | exact (ajxR_wild HJ)].
Qed.
Lemma cnb_J_fixed : forall D wk ly S Hp W mem md k ly' S' Hp' W' mem' md' k',
  cnb_J B ARx D wk ly S Hp W mem md k ->
  AJ STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly' S' Hp' W' mem' md' k' ->
  cnb_J B ARx D wk ly' S' Hp' W' mem' md' k'.
Proof. exact (cnb_J_fixedR (@wle SEGS)). Qed.
(* AFTER THE WILD callee parse_noting (the wild call rule at the call state's journal, budget WS0, with P :=
   wbudget [] (prh_wk F_parse_noting)): the caller's journal at WS0 ++ WS1 is cnb_JR at wk + the callee's budget
   (YCbqGwild.wbudget_app) *)
Lemma cnb_J_wildR : forall (R : world SEGS -> world SEGS -> Prop) D wk ly' S' Hp' W' mem' md' k' WS0 WS1,
  AJWR R STK (cnb_sp0 D) [] (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)]
    ly' S' Hp' W' mem' md' k' (WS0 ++ WS1) ->
  YCbqGwild.wbudget [] wk WS0 -> YCbqGwild.wbudget [] (prh_wk F_parse_noting) WS1 ->
  cnb_JR B ARx R D (wk + prh_wk F_parse_noting) ly' S' Hp' W' mem' md' k'.
Proof.
intros R D wk ly' S' Hp' W' mem' md' k' WS0 WS1 HJ H0 H1.
exists (WS0 ++ WS1). split; [exact HJ|].
exact (YCbqGwild.wbudget_app [] wk (prh_wk F_parse_noting) WS0 WS1 H0 H1).
Qed.
Lemma cnb_J_wild : forall D wk ly' S' Hp' W' mem' md' k' WS0 WS1,
  AJW STK (cnb_sp0 D) [] (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)]
    ly' S' Hp' W' mem' md' k' (WS0 ++ WS1) ->
  YCbqGwild.wbudget [] wk WS0 -> YCbqGwild.wbudget [] (prh_wk F_parse_noting) WS1 ->
  cnb_J B ARx D (wk + prh_wk F_parse_noting) ly' S' Hp' W' mem' md' k'.
Proof. exact (cnb_J_wildR (@wle SEGS)). Qed.
(* THE ROOM OF A parse_noting CALL (tparse_noting_specX's premise): cnb_pre's entry room wild_room [] (prh_wk
   F_check_no_overread) across the journal so far (YCbqGwild.ajournal_xw_roomR) leaves prh_wk F_parse_noting whenever
   the spent budget leaves it (a Theorem Labs lane's ec_room_at, Ent102CutsB.v) *)
Lemma cnb_roomR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 D wk ly S Hp W mem md k,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_JR B ARx R D wk ly S Hp W mem md k ->
  (wk + prh_wk F_parse_noting <= prh_wk F_check_no_overread)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S).
Proof.
intros R CTX0 D wk ly S Hp W mem md k HPRE (WS & HJ & HWB) Hle.
pose proof (cnb_pre_room CTX0 D HPRE) as Hr.
unfold YCbqGwild.wbudget in HWB.
assert (Hk : (YCbqGwild.wfresh [] WS <= prh_wk F_check_no_overread)%nat) by lia.
pose proof (YCbqGwild.ajournal_xw_roomR (SK := SK) SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HJ Hr Hk) as Hr'.
eapply YCbqGwild.wild_room_le; [|exact Hr'].
revert HWB Hle. generalize (YCbqGwild.wfresh [] WS) (prh_wk F_parse_noting) (prh_wk F_check_no_overread).
intros a b c H1 H2. lia.
Qed.
Lemma cnb_room : forall CTX0 D wk ly S Hp W mem md k,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_J B ARx D wk ly S Hp W mem md k ->
  (wk + prh_wk F_parse_noting <= prh_wk F_check_no_overread)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot S).
Proof. exact (cnb_roomR (@wle SEGS)). Qed.
(* the budgeted journal at the materialised model (rebase, YCbqG's materialize, unbase) *)
Lemma cnb_J_matR : forall (R : world SEGS -> world SEGS -> Prop) D wk ly S Hp W mem md k X,
  cnb_JR B ARx R D wk ly S Hp W mem md k ->
  cnb_JR B ARx R D wk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) k.
Proof.
intros R D wk ly S Hp W mem md k X HJ.
apply (cnb_J_fixedR R D wk ly S Hp W mem md k _ _ _ _ _ _ _ HJ).
exact (ajournal_x_materializeR SEGS B prh_pst ARx LAWS pa_segs_low R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X
  (cnb_J_rebaseR R D wk ly S Hp W mem md k HJ)).
Qed.
Lemma cnb_J_mat : forall D wk ly S Hp W mem md k X,
  cnb_J B ARx D wk ly S Hp W mem md k -> cnb_J B ARx D wk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) k.
Proof. exact (cnb_J_matR (@wle SEGS)). Qed.

(* ---- THE TREE'S FREE ORDER (the Base's cnb_fo) across a memory change that keeps the tree's footprint (bytes and
   writability) and keeps its blocks in the harness list (PRH_PjOrder.pj_foR_frame) ---- *)
Lemma cnb_fo_keep : forall D (W : world SEGS) mem Lam (W' : world SEGS) mem' Lam' o d st,
  cnb_fo D W mem Lam o d st ->
  pj_agreeR SEGS (rdW W mem) (rdW W' mem') (pj_footR d (cnb_Dof st)) ->
  (forall b, In b (cnb_Dof st) -> In b Lam') ->
  cnb_fo D W' mem' Lam' o d st.
Proof.
intros D W mem Lam W' mem' Lam' o d st.
destruct st as [(t & Dd)|]; cbn [cnb_fo cnb_Dof]; [|intros; exact I].
intros Hfo HA HL Hh n Hn. destruct (Hfo Hh n Hn) as (F & HF & HM).
exists F. split; [|exact HM].
eapply PRH_PjOrder.pj_foR_frame; [exact HF | | exact HA].
intros a kk Hin. exact (HL (a, kk) Hin).
Qed.

(* cnb_baseR at the materialised model, at a register file that keeps gp / tp (over any world relation R; cnb_base_mat
   at wle) *)
Lemma cnb_base_matR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs regs' mem md k wk X,
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs' mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros R D fxk ly S Hp W regs regs' mem md k wk X (Hz & Hk & HJ & HF & HSV & R3 & R4 & HRO) E3 E4.
split; [exact Hz|]. split; [exact Hk|]. split; [exact (cnb_J_matR R D wk ly S Hp W mem md k X HJ)|].
split; [exact HF|]. split; [exact HSV|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact HRO.
Qed.
Lemma cnb_base_mat : forall D fxk ly S Hp W regs regs' mem md k wk X,
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs' mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof. exact (cnb_base_matR (@wle SEGS)). Qed.

(* the facts of the entry the steps use *)
Lemma cnb_entry_facts : forall CTX0 D, cnb_pre (fx := fx) B ARx CTX0 D ->
  cnb_sp0 D mod 16 = 0 /\ YM05.alloc_ceiling <= ly_stk_lo (bi_ly D) /\ ly_stk_lo (bi_ly D) + STK <= cnb_sp0 D /\
  cnb_sp0 D <= ly_top (bi_ly D) /\ ly_top (bi_ly D) <= ly_stk_hi (bi_ly D) /\ ly_stk_hi (bi_ly D) <= 2 ^ 47 /\
  cnb_sp0 D + 64 <= ly_stk_hi (bi_ly D) /\
  getr (bi_regs D) 3%bv = w64 (as_gp B) /\ getr (bi_regs D) 4%bv = w64 (as_tp B) /\ 4096 <= raZ (bi_regs D) /\
  achain (bi_ly D) (aview SEGS (w_H (bi_W D)) (bi_mem D)) (cnb_sp0 D) (s0Z (bi_regs D)) (bi_ch D) /\
  ARx (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D).
Proof.
intros CTX0 D HPRE. pose proof (cnb_pre_fpre CTX0 D HPRE) as HFP. unfold fpre in HFP.
assert (HAF : afn_pre_x SEGS B ARx STK (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_regs D) (bi_mem D) (bi_md D) (bi_ch D))
  by ro_from HFP.
assert (HHI : spZ (bi_regs D) + 64 <= ly_stk_hi (bi_ly D)) by ro_from HFP.
unfold afn_pre_x in HAF.
assert (HST : astk_ok STK (bi_ly D) (spZ (bi_regs D))) by ro_from HAF.
unfold astk_ok in HST. unfold cnb_sp0.
repeat split; first [solve [ro_from HAF] | solve [ro_from HST] | solve [ro_from HHI] | lia].
Qed.

(* ---- THE FRAME CHAIN at a cno call state: s0 = the entry sp (over any world relation R; cnb_chain at wle) ---- *)
Lemma cnb_chainR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 D fxk ly S Hp W regs mem md k wk,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cnb_S1 D) (cnb_sp0 D) ch1.
Proof.
intros R CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB.
destruct (cnb_entry_facts CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & Hra40 & Hch0 & _).
pose proof cnb_stk_val as HSTKv.
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
destruct HB as (_ & _ & (WS & HJ & _) & _ & HSV & _).
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_hi HJ) as F1.
assert (Etop : ly_top ly = ly_top (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
destruct (Z_lt_le_dec (cnb_sp0 D) (ly_top (bi_ly D) - 16)) as [Hlt|Hge].
- exists ((cnb_sp0 D, raZ (bi_regs D), s0Z (bi_regs D)) :: bi_ch D).
  apply (achain_ly_top (bi_ly D) ly); [exact Etop|].
  pose proof (proj1 (Forall_forall _ _) HSV (152, 1%bv) ltac:(ro_in)) as V1.
  pose proof (proj1 (Forall_forall _ _) HSV (144, 8%bv) ltac:(ro_in)) as V8.
  cbn [fst snd] in V1, V8.
  apply (achain_push (bi_ly D) (aview SEGS (w_H (bi_W D)) (bi_mem D)) (aview SEGS (w_H W) mem) (cnb_sp0 D)
    (s0Z (bi_regs D)) (raZ (bi_regs D)) (bi_ch D) (cnb_S1 D) Hch0).
  + lia.
  + intros a Ha. apply F1; lia.
  + replace (cnb_sp0 D - 8) with (cnb_sp0 D - 160 + 152) by lia. exact V1.
  + replace (cnb_sp0 D - 16) with (cnb_sp0 D - 160 + 144) by lia. exact V8.
  + exact Hra40.
  + lia.
  + lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
Lemma cnb_chain : forall CTX0 D fxk ly S Hp W regs mem md k wk,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cnb_S1 D) (cnb_sp0 D) ch1.
Proof. exact (cnb_chainR (@wle SEGS)). Qed.

(* ---- THE TRANSFER across a kit call with an empty footprint that keeps S, Hp and the blocks ---- *)
Lemma cnb_open_keep : forall (rd rd' : reader) F c, F mod 32 = 0 -> 0 <= F -> 32 <= c <= 224 ->
  c mod 8 = 0 ->
  (forall a, shadow_addr F <= a < shadow_addr F + 64 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF (F + c) 56 /\ shadow_hull_vis rd (F + c) 56 ->
  range_addressable rd' SHADOW_OFF (F + c) 56 /\ shadow_hull_vis rd' (F + c) 56.
Proof.
intros rd rd' F c HF HF0 Hc Hc8 Hk (Hra & Hhv).
assert (Ef : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
set (f := F / 32) in *. clearbody f. subst F.
split.
- apply (range_addressable_agree rd rd' SHADOW_OFF (32 * f + c) 56); [|exact Hra].
  intros x Hx. apply Hk. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
- intros s Hs. rewrite Hk; [apply Hhv; exact Hs|].
  assert (Ec : c = 8 * (c / 8)) by (pose proof (Z.div_mod c 8 ltac:(lia)); lia).
  set (c' := c / 8) in *. clearbody c'. subst c.
  assert (E0 : 32 * f / 8 = 4 * f) by (replace (32 * f) with ((4 * f) * 8) by lia; apply Z.div_mul; lia).
  assert (E1 : (32 * f + 8 * c') / 8 = 4 * f + c')
    by (replace (32 * f + 8 * c') with ((4 * f + c') * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (32 * f + 8 * c' + 56 - 1) / 8 = 4 * f + c' + 6).
  { replace (32 * f + 8 * c' + 56 - 1) with (7 + (4 * f + c' + 6) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  unfold shadow_addr, SHADOW_OFF in *. rewrite E1, E2 in Hs. rewrite E0.
  pose proof (ro_div8 (2147450880 + (4 * f + c'))) as D1. pose proof (ro_div8 (2147450880 + (4 * f + c' + 6))) as D2.
  revert Hs D1 D2. generalize ((2147450880 + (4 * f + c')) / 8) ((2147450880 + (4 * f + c' + 6)) / 8).
  intros q1 q2 Hs D1 D2. clear - Hs D1 D2 Hc. lia.
Qed.

(* the cut facts across a kit call with FP = [] that keeps S, Hp and the blocks, from the caller's journal of the
   REBASED entry (aj_call_xWR's first journal when its caller journal is cnb_J_rebaseR's) and the callee's journal:
   cnb_baseR at the same spent budget wk (cnb_J_fixedR), cnb_slots, cnb_mid (the ledger with g_most = bi_most D and
   the cut's own is the callee text's), each struct's free order cnb_fo (cnb_fo_keep over the tree's footprint), and
   the bytes of [s1, entry sp) kept (the rc slots cross by cnb_rcslot_agree). Over any world relation R (both
   journals and cnb_baseR at R, read by the ajxR_* projections; no law of R is used); cnb_call_keep is its form at
   wle *)
Lemma cnb_call_keepR : forall (R : world SEGS -> world SEGS -> Prop)
    CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 STK1 ly2 W2 regs2 mem2 md2 k1,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D) -> cnb_slots D W mem r2 r3 ->
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  0 <= STK1 -> STK1 + (cnb_sp0 D - cnb_S1 D) <= STK ->
  AJR R STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly2 S Hp W2 mem2 md2 (k + k1) ->
  AJR R STK1 (cnb_S1 D) [] ly S Hp W mem md [] ly2 S Hp W2 mem2 md2 k1 ->
  aregs_preserved regs regs2 -> ablocks B ly2 S = ablocks B ly S ->
  prh_ledger B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (bi_most D) own ->
  cnb_baseR (fx := fx) B ARx R D fxk ly2 S Hp W2 regs2 mem2 md2 (k + k1) wk /\ cnb_slots D W2 mem2 r2 r3 /\
  cnb_mid B D ly2 S Hp W2 mem2 Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
  (forall o, cnb_fo D W mem Lam o (cnb_d1 D) st1 -> cnb_fo D W2 mem2 Lam o (cnb_d1 D) st1) /\
  (forall o, cnb_fo D W mem Lam o (cnb_d2 D) st2 -> cnb_fo D W2 mem2 Lam o (cnb_d2 D) st2) /\
  (forall o, cnb_fo D W mem Lam o (cnb_d3 D) st3 -> cnb_fo D W2 mem2 Lam o (cnb_d3 D) st3) /\
  (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
Proof.
intros R CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 STK1 ly2 W2 regs2 mem2
  md2 k1 HPRE HB HC HSL HM HSTK1 HSTKb HJ2 HJ1 HP HAB HL2.
destruct (cnb_entry_facts CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & _ & _ & HAR0).
pose proof cnb_stk_val as HSTKv. pose proof (@cf_head_nonneg cp) as Hh0. pose proof asan_consts as (C1 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
pose proof (cnb_pre_home CTX0 D HPRE) as HHOME. pose proof (cnb_pre_ledger CTX0 D HPRE) as HLED0.
destruct HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
pose proof (cnb_J_fixedR R D wk ly S Hp W mem md k ly2 S Hp W2 mem2 md2 (k + k1) HJ HJ2) as HJ2'.
pose proof HJ as (WS & HJW & _). pose proof HJ2' as (WS2 & HJW2 & _).
pose proof (ajxR_ar HJW) as HAR. pose proof (ajxR_ly HJW) as Hly.
pose proof (ajxR_ar HJW2) as HAR2. pose proof (ajxR_ly HJW2) as Hly2.
pose proof (ajxR_hi HJ1) as G1. pose proof (ajxR_blk HJ1) as G2. pose proof (ajxR_img HJ1) as G3.
pose proof (ajxR_frm HJ1) as G4.
assert (EF1 : ly_F ly = ly_F (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
assert (EF2 : ly_F ly2 = ly_F (bi_ly D)) by (unfold layout_le in Hly2; ro_from Hly2).
assert (EFa1 : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF1; reflexivity).
assert (EFa2 : frame_addr ly2 CNB_CID (bi_fpos D) = cnb_F D) by (unfold cnb_F, frame_addr; rewrite EF2; reflexivity).
assert (EFl : flag_addr ly2 CNB_CID (bi_fpos D) = flag_addr ly CNB_CID (bi_fpos D))
  by (unfold flag_addr; rewrite EF1, EF2; reflexivity).
assert (EFB : fs_frame_bytes CNB_CID = 512) by reflexivity.
destruct HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
assert (Hin3 : In (CNB_CID, bi_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (Hal32 & _ & _ & _).
destruct (alx_frames SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 CNB_CID (bi_fpos D) HAR2 Hin3)
  as (_ & _ & Hfb2 & Hsh2).
rewrite EFa1 in Hal32. rewrite EFa2, EFB in Hfb2, Hsh2.
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa1 in HF4096, HFceil. rewrite EFB in HFceil.
(* the kept byte ranges *)
assert (KF : forall a, cnb_F D <= a < cnb_F D + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CNB_CID (bi_fpos D) a Hin3); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa1, EFB; lia |].
  exact (inFP_nil a). }
assert (KS : forall a, shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + 64 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CNB_CID (bi_fpos D) a Hin3); [right; unfold in_zr; cbn [fst snd]; rewrite EFa1, EFB; lia |].
  exact (inFP_nil a). }
assert (KT : forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply G1; lia. }
assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)).
{ intros p n i Hin Hi. apply (G2 p n i Hin); [rewrite HAB; exact Hin | exact Hi | exact (inFP_nil _)]. }
(* an image byte that is read-only, not runtime-owned and not errno's is kept (the image clause; PST is writable) *)
assert (KI : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a ->
  ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Hro Hown Herr. apply G3.
  + destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img a Hrel)].
  + exact Hown.
  + exact Herr.
  + intros Hpst. exact (cnbi_pst_rw B IMG a Hpst Hro).
  + intros (r & Hr & _). destruct Hr. }
destruct HM as (HC1 & HC2 & HC3 & HLED & Hpk & Hcnt & Hroom & Hbb & HO1 & HO2 & HO3 & HD1 & HD2 & HD3 & HPL & HPA
  & HNO & HDAT).
(* the copies *)
assert (KC : forall r, cnb_copy B D ly S Hp W mem r -> cnb_copy B D ly2 S Hp W2 mem2 r).
{ intros r [Hr0 | (Hin & Hnh & Hsrc)]; [left; exact Hr0|]. right.
  assert (Hin2 : In (r, cnb_size D + 16) (ablocks B ly2 S)) by (rewrite HAB; exact Hin).
  split; [exact Hin2|]. split; [exact Hnh|].
  destruct Hsrc as (Hby & H4096 & Hceil' & Hamr & Hra & Hhv).
  pose proof (req_size_pos (cnb_size D + 16) ltac:(unfold cnb_size; lia)) as (Hreq1 & Hreq2).
  assert (HnoH : forall h, In h Hp -> ~ (r <= h < r + req_size (cnb_size D + 16))).
  { intros h Hh Hhr.
    pose proof (prh_ledger_heads B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (bi_most D) own HL2) as HPm.
    apply (Permutation_in _ HPm) in Hh. apply in_map_iff in Hh as ((a & kk) & Ea & Hak). cbn [fst] in Ea.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (bi_most D) own HL2)
      (a, kk) Hak) as Hhb. cbn [fst snd] in Hhb.
    destruct (ro_hblock ly2 S Hp W2 mem2 a kk Hhb) as (Hkk0 & Hab & Hahp).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 _ _ HAR2 Hab) as (_ & _ & _ & _ & _ & Hpw).
    assert (Hne : fst (a - cf_head, kk + cf_head) <> fst (r, cnb_size D + 16)).
    { cbn [fst]. intros E. apply Hnh. rewrite <- E. exact Hahp. }
    pose proof (ro_pairwise_map (fun b => (fst b, req_size (snd b))) _ _ _ Hpw Hab Hin2 Hne) as Hdj.
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
    pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (Hq1 & _). lia. }
  destruct (alx_shadow SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 r (cnb_size D + 16) HAR2 Hin2 HnoH) as (Hbs & Hhull).
  unfold cnb_size in *.
  split; [|split; [exact H4096|]; split; [exact Hceil'|]; split; [exact Hamr|]; split].
  - unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) r (bi_x D) Hby).
    intros x Hx. apply (mbyte_of_aview SEGS). replace x with (r + (x - r)) by lia. apply (KB r _ (x - r) Hin). lia.
  - apply (block_shadow_range _ SHADOW_OFF r (req_size (Z.of_nat (length (bi_x D)) + 16))); [exact Hbs | lia | lia].
  - intros Hl. apply (ro_hull_mono _ r (req_size (Z.of_nat (length (bi_x D)) + 16))); [lia | exact Hhull]. }
(* the struct opening *)
assert (KO : forall c, 32 <= c <= 224 -> c mod 8 = 0 ->
  cnb_open W mem (cnb_F D + c) -> cnb_open W2 mem2 (cnb_F D + c)).
{ intros c Hc Hc8 Ho. apply (cnb_open_keep _ _ (cnb_F D) c Hal32 ltac:(lia) Hc Hc8 KS Ho). }
(* a tree's footprint keeps its bytes and writability: the struct's 56 bytes inside F, the tree's blocks in Lam *)
assert (KA : forall st c, 0 <= c -> c + 56 <= 512 -> (forall b, In b (cnb_Dof st) -> In b Lam) ->
  pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR (cnb_F D + c) (cnb_Dof st))).
{ intros st c Hc0 Hc HDL x Hx. destruct Hx as [Hx | ((a & kk) & Hb & Hhold)].
  + split.
    * apply (mbyte_of_aview SEGS). apply KF. lia.
    * intros _. apply (apresent_writable SEGS). exact (proj1 (Hfb2 x ltac:(lia))).
  + unfold pj_holdsR in Hhold. cbn [fst snd] in Hhold.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) own HLED)
      (a, kk) (HDL _ Hb)) as Hhb. cbn [fst snd] in Hhb.
    destruct (ro_hblock ly S Hp W mem a kk Hhb) as (Hkk0 & Hab & _).
    pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (_ & Hq2).
    split.
    * apply (mbyte_of_aview SEGS). replace x with ((a - cf_head) + (x - a + cf_head)) by lia.
      apply (KB _ _ _ Hab). lia.
    * intros _. apply (apresent_writable SEGS).
      assert (Hab2 : In (a - cf_head, kk + cf_head) (ablocks B ly2 S)) by (rewrite HAB; exact Hab).
      destruct (alx_blocks SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr x ltac:(lia))). }
(* the structs' contents *)
assert (KD : forall st c, 0 <= c -> c + 56 <= 512 -> (forall b, In b (cnb_Dof st) -> In b Lam) ->
  cnb_doc W mem Lam (cnb_F D + c) st -> cnb_doc W2 mem2 Lam (cnb_F D + c) st).
{ intros st c Hc0 Hc HDL Hd. pose proof (KA st c Hc0 Hc HDL) as HA.
  destruct st as [(t & Dd)|]; cbn [cnb_doc cnb_Dof] in Hd, HDL, HA |- *.
  - destruct Hd as (Hn & Hdep). split; [|exact Hdep].
    exact (pj_nodeR_frame SEGS t (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (cnb_F D + c) Dd Hn HA).
  - apply (pj_zeroR_frame SEGS (rdW W mem) (rdW W2 mem2) (cnb_F D + c) Hd).
    intros x Hx. apply (mbyte_of_aview SEGS). apply KF. lia. }
assert (HL1 : forall b, In b (cnb_Dof st1) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
assert (HL2' : forall b, In b (cnb_Dof st2) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HL3 : forall b, In b (cnb_Dof st3) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; left; exact Hb).
(* the input's bytes (cnb_pre's home of the text: a harness block of the entry ledger, a read-only image range, or
   an allocator block of the entry, each a block or an image byte the call keeps) *)
assert (KX : forall x, bi_data D <= x < bi_data D + cnb_size D ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx.
  assert (HE : forall b, In b (ablocks B (bi_ly D) (bi_S D)) -> In b (ablocks B ly S))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPA)); apply in_or_app; right; apply in_or_app; right;
        exact Hb).
  destruct (HHOME ltac:(lia)) as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]]
    | (b & m & Hin & Hnh & Hb & Hm)].
  - pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D)
      (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) 0 HLED0) (b, m) Hin) as Hhb.
    cbn [fst snd] in Hhb. destruct (ro_hblock _ _ _ _ _ b m Hhb) as (Hm0 & Hab & _).
    pose proof (req_size_pos (m + @cf_head cp) ltac:(lia)) as (_ & Hq2).
    replace x with ((b - cf_head) + (x - b + cf_head)) by lia. apply (KB _ _ _ (HE _ Hab)). lia.
  - destruct (Hro x ltac:(lia)) as (Hrop & Hown & Herr). exact (KI x Hrop Hown Herr).
  - destruct (Hro x ltac:(lia)) as (Hrop & Hown & Herr & _). exact (KI x Hrop Hown Herr).
  - pose proof (req_size_pos m ltac:(lia)) as (_ & Hq2).
    replace x with (b + (x - b)) by lia. apply (KB _ _ _ (HE _ Hin)). lia. }
split.
{ (* cnb_base, at the same spent budget *)
  split; [exact Hz|]. split; [exact Hk|]. split; [exact HJ2'|].
  split.
  { split; [exact Hfrs|]. split; [exact Hnin|]. split.
    - rewrite EFl, <- Hflag. apply (ro_rdword_kept _ _ (cnb_F D) (cnb_F D + 512)); [exact KF| rewrite EFB; lia | rewrite EFB; lia].
    - split.
      + intros a Ha. rewrite EFB in Ha. exact (proj1 (Hfb2 a Ha)).
      + intros a Ha. rewrite EFB in Ha. replace a with (shadow_addr (cnb_F D) + (a - shadow_addr (cnb_F D))) by lia.
        apply (proj1 (Hsh2 (a - shadow_addr (cnb_F D)) ltac:(change (512 / 8) with 64 in *; lia))). }
  split.
  { unfold cnb_saved in *. apply Forall_forall. intros [o r] Hin.
    pose proof (proj1 (Forall_forall _ _) HSV (o, r) Hin) as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho : 56 <= o <= 152) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
    rewrite <- Hv. apply (ro_rdword_kept _ _ (cnb_S1 D) (cnb_sp0 D)); [exact KT | lia | lia]. }
  split; [exact (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) R3)|].
  split; [exact (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) R4)|].
  intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr). exact (KI a Hro Hown Herr). }
split; [exact (cnb_slots_agree D W mem W2 mem2 r2 r3 Hal16 KT HSL)|].
split.
{ (* cnb_mid *)
  split; [exact (KC _ HC1)|]. split; [exact (KC _ HC2)|]. split; [exact (KC _ HC3)|].
  split; [exact HL2|]. split; [exact Hpk|]. split; [exact Hcnt|]. split; [exact Hroom|].
  split; [exact Hbb|].
  split; [exact (KO 32 ltac:(lia) ltac:(reflexivity) HO1)|].
  split; [exact (KO 128 ltac:(lia) ltac:(reflexivity) HO2)|].
  split; [exact (KO 224 ltac:(lia) ltac:(reflexivity) HO3)|].
  split; [exact (KD st1 32 ltac:(lia) ltac:(lia) HL1 HD1)|].
  split; [exact (KD st2 128 ltac:(lia) ltac:(lia) HL2' HD2)|].
  split; [exact (KD st3 224 ltac:(lia) ltac:(lia) HL3 HD3)|].
  split; [exact HPL|]. split; [rewrite HAB; exact HPA|]. split; [exact HNO|].
  unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) (bi_data D) (bi_x D) HDAT).
  intros x Hx. apply (mbyte_of_aview SEGS). apply KX. unfold cnb_size. lia. }
(* the structs' free order *)
split; [intros o Hfo; exact (cnb_fo_keep D W mem Lam W2 mem2 Lam o (cnb_d1 D) st1 Hfo
  (KA st1 32 ltac:(lia) ltac:(lia) HL1) HL1)|].
split; [intros o Hfo; exact (cnb_fo_keep D W mem Lam W2 mem2 Lam o (cnb_d2 D) st2 Hfo
  (KA st2 128 ltac:(lia) ltac:(lia) HL2') HL2')|].
split; [intros o Hfo; exact (cnb_fo_keep D W mem Lam W2 mem2 Lam o (cnb_d3 D) st3 Hfo
  (KA st3 224 ltac:(lia) ltac:(lia) HL3) HL3)|].
exact KT.
Qed.
Lemma cnb_call_keep : forall CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3
    STK1 ly2 W2 regs2 mem2 md2 k1,
  cnb_pre (fx := fx) B ARx CTX0 D -> cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D) -> cnb_slots D W mem r2 r3 ->
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  0 <= STK1 -> STK1 + (cnb_sp0 D - cnb_S1 D) <= STK ->
  AJ STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly2 S Hp W2 mem2 md2 (k + k1) ->
  AJ STK1 (cnb_S1 D) [] ly S Hp W mem md [] ly2 S Hp W2 mem2 md2 k1 ->
  aregs_preserved regs regs2 -> ablocks B ly2 S = ablocks B ly S ->
  prh_ledger B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (bi_most D) own ->
  cnb_base (fx := fx) B ARx D fxk ly2 S Hp W2 regs2 mem2 md2 (k + k1) wk /\ cnb_slots D W2 mem2 r2 r3 /\
  cnb_mid B D ly2 S Hp W2 mem2 Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
  (forall o, cnb_fo D W mem Lam o (cnb_d1 D) st1 -> cnb_fo D W2 mem2 Lam o (cnb_d1 D) st1) /\
  (forall o, cnb_fo D W mem Lam o (cnb_d2 D) st2 -> cnb_fo D W2 mem2 Lam o (cnb_d2 D) st2) /\
  (forall o, cnb_fo D W mem Lam o (cnb_d3 D) st3 -> cnb_fo D W2 mem2 Lam o (cnb_d3 D) st3) /\
  (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
Proof. exact (cnb_call_keepR (@wle SEGS)). Qed.

(* ---- THE CALL to fuzz_alloc_ran_out from cno (return sites 0x81c44 / 0x81c70 / 0x81c9c / 0x81e78) ---- *)
Hypothesis HRO : forall fz : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fz rc cp prh_img_B RL B_prog_listing PA B ARx SK.

(* the return sites: code words of the listing below the ceiling (fpre's raZ bound), even, small offsets *)
Lemma cnb_ro_ret_ok : forall ret, In ret cnb_ro_rets ->
  4096 <= cnb_pc ret < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cnb_pc ret)) /\ 0 <= ret < 2 ^ 28.
Proof.
intros ret Hin. pose proof (cnbi_base B IMG) as HB. pose proof cnb_off_val as HO.
pose proof (cnb_ro_slots ret Hin) as Hsl.
assert (Hr : 0 <= ret < 2 ^ 28 /\ (CNB_OFF + ret) mod 2 = 0).
{ cbn [cnb_ro_rets In] in Hin. rewrite HO.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; (split; [lia | reflexivity]). }
destruct Hr as (Hr28 & Hr2).
unfold cnb_pc, w64. replace (BASE + CNB_OFF + ret) with (BASE + (CNB_OFF + ret)) by lia.
split; [split|split].
- rewrite HB. unfold B_prog_base. lia.
- exact (pa_slot_lt_ceil_b (PL := PL_cno_B) (PI := PA) (CNB_OFF + ret) ltac:(lia) Hsl).
- apply ret_ok_codeptr_v; [lia | exact Hr2].
- exact Hr28.
Qed.

(* the call (fuzz_alloc_ran_out is a FIXED-trace callee: rebase the walk's journal, aj_call_xWR, unbase in
   cnb_call_keepR at the same wk). Over a world relation R that is reflexive, transitive and contains wle (the call
   rule aj_call_xWR at R; the text HRO is not a crossing text, so its plain SRr and its post at wle are lifted into R
   by YA0nH.SRr_SRrG and YCbqG.apost_base_x_R_lift); cnb_ro_call is its form at wle *)
Lemma cnb_ro_callR : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
  forall P, srr_inv_call SEGS P ->
  forall CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ret,
  cnb_pre (fx := fx) B ARx CTX0 D -> In ret cnb_ro_rets ->
  cnb_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D) -> getr regs 1%bv = w64 (cnb_pc ret) -> cnb_slots D W mem r2 r3 ->
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> P mem ->
  SRrG SEGS R W (@cnb_cfg SEGS fxk (SIGMA AS_fuzz_alloc_ran_out) regs mem md)
    (fun W' c' => exists ly' regs' mem' md' k',
    c' = @cnb_cfg SEGS fxk (cnb_pc ret) regs' mem' md' /\
    cnb_baseR (fx := fx) B ARx R D fxk ly' S Hp W' regs' mem' md' k' wk /\
    aregs_preserved regs regs' /\ getr regs' 10%bv = w64 ran /\ ablocks B ly' S = ablocks B ly S /\
    cnb_slots D W' mem' r2 r3 /\ cnb_mid B D ly' S Hp W' mem' Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
    (forall o, cnb_fo D W mem Lam o (cnb_d1 D) st1 -> cnb_fo D W' mem' Lam o (cnb_d1 D) st1) /\
    (forall o, cnb_fo D W mem Lam o (cnb_d2 D) st2 -> cnb_fo D W' mem' Lam o (cnb_d2 D) st2) /\
    (forall o, cnb_fo D W mem Lam o (cnb_d3 D) st3 -> cnb_fo D W' mem' Lam o (cnb_d3 D) st3) /\
    (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\ P mem').
Proof.
intros R Rr Rt Rs P PCALL CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ret
  HPRE Hret HB HC R1 HSL HM HPM.
destruct (cnb_entry_facts CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & Hgp0 & Htp0 & _ & _ & _).
pose proof cnb_stk_val as HSTKv. pose proof cnb_stk_ro_val as HSTKr. pose proof asan_consts as (C1 & _).
destruct (cnb_S1_bounds D Hal16) as (HS1a & HS1b & HS1c).
destruct (cnb_ro_ret_ok ret Hret) as ((Hr0 & Hrc) & Hrok & Hr28).
destruct (cnb_chainR R CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB) as (ch1 & Hch1).
pose proof HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
pose proof (cnb_J_rebaseR R D wk ly S Hp W mem md k HJ) as HJr.
pose proof HJ as (WS & HJW & _). pose proof (ajxR_ly HJW) as Hly.
assert (Eshi : ly_stk_hi ly = ly_stk_hi (bi_ly D)) by (unfold layout_le in Hly; ro_from Hly).
assert (G2 : getr regs 2%bv = w64 (cnb_S1 D)) by (apply (cnb_regsat_get regs (cnb_core D)); [exact HC | ro_in]).
assert (G8 : getr regs 8%bv = w64 (cnb_sp0 D)) by (apply (cnb_regsat_get regs (cnb_core D)); [exact HC | ro_in]).
assert (Hsp : spZ regs = cnb_S1 D) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = cnb_sp0 D) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regs = cnb_pc ret) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
pose proof HM as (_ & _ & _ & HLED & _).
unfold cnb_cfg, w64.
eapply (SRrG_bind SEGS R Rt).
{ apply (@aj_call_xWR fxk rc SK SEGS B prh_pst ARx cf_head LAWS pa_segs_low R Rr Rt W regs mem
    (SIGMA AS_fuzz_alloc_ran_out)
    STK (cnb_sp0 D) [] (bi_ly D) (set_depot (st_depot S) (bi_S D)) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D)
    [(CNB_CID, bi_fpos D)] ly S Hp md k
    STK_fuzz_alloc_ran_out 0 [] (cnb_S1 D - cnb_sp0 D) (w64 (cnb_pc ret)) ch1
    (fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 ran /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ ran (bi_most D) own))).
  - exact HJr.
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
    assert (HFP : fpre (fx := fxk) B ARx STK_fuzz_alloc_ran_out ly S Hp W regs mem md ch1).
    { split; [exact HAFN|]. split; [exact HROD|]. split; [rewrite Hsp, Eshi; lia|].
      split; [rewrite Hraz; exact Hrc | exact Hz]. }
    (* the text is not a crossing text: its plain SRr and its post at wle lift into R *)
    eapply (SRrG_mono SEGS R);
      [exact (SRr_SRrG SEGS R Rs _ _ _
                (HRO fxk ly S Hp W regs mem md ch1 Lam peak cnt SIZE_MAXZ ran (bi_most D) own HFP HLED))|].
    intros W' c' _ HPOST. apply fpostW_x_of_apostR. apply apost_base_x_R_lift; [exact Rs | exact HPOST].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & (HQ & HMN)).
destruct HQ as (_ & R10 & -> & -> & HAB & HL2).
rewrite Z.add_0_r in HJ1. replace (cnb_sp0 D + (cnb_S1 D - cnb_sp0 D)) with (cnb_S1 D) in HJ1 by lia.
rewrite HSTKr, !Z.add_0_r in HJ1.
destruct (cnb_call_keepR R CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3
  0 ly2 W2 regs2 mem2 md2 k1 HPRE HB HC HSL HM ltac:(lia) ltac:(lia) HJ2 HJ1 HP2 HAB HL2)
  as (HB2 & HSL2 & HM2 & HFO1 & HFO2 & HFO3 & KT2).
apply (SRrG_ret SEGS R Rr). exists ly2, regs2, mem2, md2, (k + k1).
split; [reflexivity|]. split; [exact HB2|]. split; [exact HP2|]. split; [exact R10|]. split; [exact HAB|].
split; [exact HSL2|]. split; [exact HM2|]. split; [exact HFO1|]. split; [exact HFO2|]. split; [exact HFO3|].
split; [exact KT2|]. exact (PCALL mem mem2 HMN HPM).
Qed.
Lemma cnb_ro_call : forall P, srr_inv_call SEGS P ->
  forall CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ret,
  cnb_pre (fx := fx) B ARx CTX0 D -> In ret cnb_ro_rets ->
  cnb_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cnb_regsat regs (cnb_core D) -> getr regs 1%bv = w64 (cnb_pc ret) -> cnb_slots D W mem r2 r3 ->
  cnb_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (SIGMA AS_fuzz_alloc_ran_out) regs mem md) (fun W' c' => exists ly' regs' mem' md' k',
    c' = @cnb_cfg SEGS fxk (cnb_pc ret) regs' mem' md' /\
    cnb_base (fx := fx) B ARx D fxk ly' S Hp W' regs' mem' md' k' wk /\
    aregs_preserved regs regs' /\ getr regs' 10%bv = w64 ran /\ ablocks B ly' S = ablocks B ly S /\
    cnb_slots D W' mem' r2 r3 /\ cnb_mid B D ly' S Hp W' mem' Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
    (forall o, cnb_fo D W mem Lam o (cnb_d1 D) st1 -> cnb_fo D W' mem' Lam o (cnb_d1 D) st1) /\
    (forall o, cnb_fo D W mem Lam o (cnb_d2 D) st2 -> cnb_fo D W' mem' Lam o (cnb_d2 D) st2) /\
    (forall o, cnb_fo D W mem Lam o (cnb_d3 D) st3 -> cnb_fo D W' mem' Lam o (cnb_d3 D) st3) /\
    (forall a, cnb_S1 D <= a < cnb_sp0 D -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\ P mem').
Proof. exact (cnb_ro_callR (@wle SEGS) (wle_refl SEGS) (wle_trans SEGS) (fun W W' H => H)). Qed.

End ro.
