(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB.v, with its module paths and module names changed; 1139 of its 1188 lines of code are new or changed and 209 lines of the source are left out. *)
(* fuzz_preset, slice S5b, image A' (asan 1be0f53d96cb, the #102 pins): THE TWO TOP THEOREMS of the reader's recursive
   unit, parse_value and parse_items, against the texts tparse_value_specX / tparse_items_specX of lib/A/PRH_FnParse.v,
   with the reader texts of lib/A/PRH_FnReader.v, the allocator texts of lib/A/PRH_FnAlloc.v and the kit of
   lib/A/PRH_Base.v.

   rule 24: proves function parse_value and parse_items (reuse search: proof-index parse_value / parse_items, index v5
   built 2026-10-30T09:06:38Z, its result confirmed by a second checker; ported from lib/Prog/ParseUnit.v /
   parse_value.v / parse_items.v / PvItems.v of the released recipes, the induction shape only).

   PORTED (the shape only): the released plain ParseUnit.v closes the two contracts by DESCENDING induction on the
   nesting d from the depth bound MAXD, parse_value at d from parse_items at d, parse_items at d from parse_value at
   S d. The segments are NOT ported: image A' is the ASan build, with different code, and every segment is proved for
   A' in lib/A (Vrd*.v) against the kit texts.

   THE CHAIN AT ONE DEPTH d (parse_value):
     VrdPro.vrd_pro_a_P (entry to the dispatch, with the memory invariant P)
     -> one arm: the string arm VrdArmStrOk.vrd_str_a_okP, the number arm VrdNumA.vrd_num_a_P (vrd_num_a_stmt_P), the
        container arm VrdArmLC.vrd_cont_aLC_P_holds (parse_items at the same d), the literal arm
        VrdArmLC.vrd_lit_aLC_P_holds, and the END-OF-TEXT arm vrd_eof_a_P (below; rows 123..124, `li s5, -1` and the
        jump to the join);
     -> the epilogue VrdEpiP.vrd_epi_step_P (the BUDGETED post fpostWFb at the text's wbudget CW 0), its transfer
        premise by vrd_pv_close (below).
   P is instantiated ONCE, at the function's top, as `fun m => memnorm segs mem -> memnorm segs m` (a Theorem Labs lane's
   12:19Z ruling; YSRrMemnorm.srr_inv_laws_imp / srr_inv_call_imp / srr_inv_mn_imp), which turns fpostWFb into the
   text's fpostWFbm.

   THE CALLEES AT THE INSTANCE (section 5): parse_string by S4_PsTop.ps_K0_of_counts, grow by PwGrow.grow_holds_Aprime,
   fuzz_realloc by FuzzReallocAp.fuzz_realloc_holds_Ap, fuzz_malloc by FuzzMalloc.fuzz_malloc_holds, fuzz_free by
   FuzzFree.fuzz_free_holds, hex4 by S3_Hex4Bridge.hex4_holds, put_utf8 by ExUtf8WA.pb_put_utf8X_Ap and literal by
   literal_bridge.literal_holds. The runtime wrappers of realloc, malloc and free stay named Section hypotheses of
   Section top (AREAL_cf, AMALLOC, AFREE). Section 6 (vt_ARA_init) shows that this ARcf, the relation of the theorems'
   fpre, holds at the run's initial state at image A'.

   REASON (quoted in every converted file, a Theorem Labs lane 12:19Z): an SRr post is opaque once Qed, so an end-state memory
   invariant must be in the segment's STATEMENT; the generic SRr_memnorm was measured NOT provable (a Theorem Labs lane), so it
   cannot be added afterwards.

   NUMERALS: 123 / 225 are ROWS of parse_value (DERIVED: listing slots, row r at slot r + 4682); -1 is the return
   WORD; 56 / 64 / 8 are LENGTHs (struct pj, the class-0 frame, a word); 33 is the kit's depth slack, cited. ADDRESSES,
   each checked by vm_compute against the listing / TfibB, never assumed: 700096 / 663568 / 663656 / 700088 (vt_uarc:
   the use-after-return cell and the three GOT / shadow-cell words), 0x52880 (vt_aim: __asan_memset's entry). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* the re-hiding move's SRr' / wle' (YA0nH, YSRrG) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoom PresetReqAt PresetLiveBounds
  PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog VrdPro VrdNum.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import VrdArmStrOk VrdArmLC VrdEpi VrdEpiA VrdEpiP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import VrdIElem VrdIPro VrdILoop.
(* the real instance: Required, cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0scf YG0lawscf YGcallcf YGcallScf
  YImgShadowCoverCf FCifaceCf YGcallRoStr YGcfHp YG0dcf YGcallMxmn YGcfMallocComposeKeep YGcfInstReallocKKeep
  YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l PALibA CfParamsPreset AImgShadowVis PRH_Img
  VrdArmLCWit CfPoison102 PRowSet CfImgA CfAroPresetA.
(* S8aNumberW.v (an earlier source of the number arm's image witnesses) is NOT Required: its closure
   S8aNumber.v -> S8aNumA.v does not compile on the kit's cut (S8aNumA.v:390, "No applicable tactic"); vt_num_arm cites
   the facts those witnesses are made of directly (a Theorem Labs lane's strtod_row_sat, AE22.canary_cell_in, vt_pst) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck CrsWitAp strtod_row_sat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AE22.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require VrdNumA PRowCpy PRowCmp PSstrRo.
(* the callee proofs cited at the instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S4_PsTop PwGrow literal_bridge S3_Hex4Bridge
  FuzzMalloc FuzzFree FuzzReallocAp ExUtf8WA.
(* the start-up of image A' (section 6, vt_ARA_init only) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0c YK09 YA0e YA01 YA02 YGcfNilInit
  YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1h AB12 AB01 AD1f AD1g AD1d AD2i PWorldH8
  CfIalApartPreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Local Open Scope Z_scope.
(* PRW_StepKit (through VrdArmLC / VrdIStep / PwGrow) loads YF0v.v, which sets Zify's euclidean-division flag off
   GLOBALLY; this file's lia goals over `/` and `mod` need it on (VrdArmStrOk.v does the same) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* lia over the arithmetic facts only (VstrD's slia, lib/A/VrdArmStrOk.v) *)
#[local] Ltac slia_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with Prop => idtac | _ => fail end;
      lazymatch T with
      | @eq _ _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
      | le _ _ => fail | lt _ _ => fail | ge _ _ => fail | gt _ _ => fail
      | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail | _ <> _ => fail
      | _ => clear H
      end
  end.
#[local] Ltac slia := slia_clear; lia.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. THE END-OF-TEXT ARM, rows 123..124 (`addi s5, zero, -1` and `j` to row 225): no load, no store, no call.       *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section eof.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* the symbolic state at a listing offset: the registers as atoms, no region, no fact *)
Definition vt_ss (off : Z) : sstate := mkSS off sr_atoms [] None (mkFacts [] [] []).
Definition vt_env (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PI_prog_A (Ereg regs []).

Lemma vt_entry : forall (W : world SEGS) regs mem off,
  st_ok_pi SEGS VAL (vt_env regs) (vt_ss off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem off. rewrite restrict_mkst_fx. unfold vt_ss, vt_env.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat (split || exact I || constructor).
Qed.

(* the value's grammar on an empty rest: refused, no event *)
Lemma vt_jr_value_nil : forall (sm : list Z -> Z * Z) d x ok, PjGrammar.skip x = [] ->
  PjGrammar.jr_value sm d x ok = (None, [], ok).
Proof. intros sm d x ok H. unfold PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite H. reflexivity. Qed.

Lemma vrd_eof_a_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p
    (tb : list Z) (Lam : list (Z * Z)) peak cnt fail ran most own W c,
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  PjGrammar.skip (rest_atR tb text p) = [] ->
  P (ms_mem (cfg_ms c)) ->
  SRr SEGS W c (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
      (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv) W' c') /\
    P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW d CTX0 CW ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran most own W c
  HD Hsk HP0.
destruct HD as (arm & pos & p' & k & ly & S & Hp & regs & mem & md & Hc & HB).
unfold vrd_disp_body in HB. decompose [and] HB. clear HB.
lazymatch goal with X : rest_atR tb text p' = PjGrammar.skip (rest_atR tb text p) |- _ => rename X into Hrest end.
lazymatch goal with X : match PjGrammar.skip (rest_atR tb text p) with _ => _ end |- _ => rename X into Hmatch end.
lazymatch goal with X : context [ajournal_x] |- _ => rename X into HJ end.
lazymatch goal with X : frames S = _ |- _ => rename X into Hfr end.
lazymatch goal with X : ablocks B ly S = ablocks B ly0 S0 |- _ => rename X into Hab end.
lazymatch goal with X : exists _, S = set_fs _ S0 |- _ => rename X into Hsetfs end.
lazymatch goal with X : forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a -> _ |- _ =>
  rename X into Hwin end.
lazymatch goal with X : context [vrd_frame] |- _ => rename X into Hframe end.
lazymatch goal with X : context [vrd_saved] |- _ => rename X into Hsaved end.
lazymatch goal with X : context [vrd_regs] |- _ => rename X into Hregs end.
lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W) mem) q text len p' _ tb |- _ => rename X into Hin end.
lazymatch goal with X : context [prhPv_node] |- _ => rename X into Hnode end.
lazymatch goal with X : YK0s.ret_ok _ |- _ => rename X into Hra0 end.
lazymatch goal with X : context [prh_ledger] |- _ => rename X into Hled end.
lazymatch goal with X : context [rd_room] |- _ => rename X into Hroom end.
lazymatch goal with X : frm_zero _ |- _ => rename X into Hfrm end.
lazymatch goal with X : (d <= PjGrammar.MAXD)%nat |- _ => rename X into HMAXD end.
rewrite Hsk in Hmatch. destruct Hmatch as (Harm & Hpe). subst arm.
pose proof Hregs as (Rsp & R9 & R8 & R18 & R26 & R19 & R20 & R21 & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
subst c. unfold cfg_at. cbn [cfg_ms ms_mem mkst] in HP0.
replace (pa_sigma AS_parse_value + vrd_arm_off VA_eof) with (A_prog_base + vrd_row 123) by (vm_compute; reflexivity).
pose proof (vt_entry W regs mem (vrd_row 123)) as HS.
assert (EB : @pa_val _ A_prog_listing PI_prog_A A_TEXT = A_prog_base) by reflexivity.
rewrite EB in HS.
change (w64 (A_prog_base + vrd_row 123)) with (Z_to_bv 64 (A_prog_base + vrd_row 123)).
assert (HEI : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (vt_env regs)) by (unfold vt_env; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SLit 0) [] (vt_env regs) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
pose (RUNTO := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (vrd_row 225).
{ unfold vt_ss; cbn [ss_mem]. apply awr_ok_nil. }
pmkst HS.
prreg HS (8%bv : bv 5) Q8. prreg HS (18%bv : bv 5) Q18. prreg HS (26%bv : bv 5) Q26.
prreg HS (24%bv : bv 5) Q24. prreg HS (21%bv : bv 5) Q21. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (EW : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
               ew (vt_env regs) n = getr regs r).
{ intros n r Hn Hr. unfold vt_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
  unfold vt_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
apply SRr_ret. split; [|rewrite EM; exact HP0].
exists fx, pos, (-1).
unfold vrd_epi_a.
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md), ly, S, Hp, k.
split; [rewrite vrd_pc_epi; reflexivity|].
(* the join's journal at the EMPTY budget (no allocator call on this arm): ajournal_x IS ajournal_xw at [] *)
split; [exists []; split; [exact HJ | unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh; cbn; lia]|].
split; [intros a Ha Hn; rewrite EM; exact (Hwin a Ha Hn)|].
split; [rewrite Q8, (EW 8%nat (8%bv : bv 5)) by (vm_compute; reflexivity || lia); exact R8|].
split; [rewrite Q18, (EW 18%nat (18%bv : bv 5)) by (vm_compute; reflexivity || lia); exact R18|].
split; [rewrite Q26, (EW 26%nat (26%bv : bv 5)) by (vm_compute; reflexivity || lia); exact R26|].
split; [rewrite Q24, (EW 24%nat (24%bv : bv 5)) by (vm_compute; reflexivity || lia); exact R24|].
split; [rewrite Q21; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [rewrite Q3, (EW 3%nat (3%bv : bv 5)) by (vm_compute; reflexivity || lia); exact R3|].
split; [rewrite Q4, (EW 4%nat (4%bv : bv 5)) by (vm_compute; reflexivity || lia); exact R4|].
split; [exact Hra0|].
split; [rewrite EM; exact Hsaved|].
split; [rewrite EM; exact (proj1 (proj2 (proj2 Hframe)))|].
split; [exact Hfrm|].
split; [intros r _; reflexivity|].
(* ---- RQ: no event, the node untouched, the cursor at the end of the text ---- *)
rewrite EM.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ Hled) as (Hlp & Hpk & Hcn & Hfl & Hrn).
pose proof Hnode as (Hv4096 & Hval8 & Hvrw & Hvzero & Hvat & Hvamr & Hvown & Hvra).
pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hgarr & Hqt & Hd32).
destruct Hsetfs as (fz & Efz).
unfold vrd_pv_post.
exists [], None, [], [], [], Lam, peak, cnt, fail, ran.
assert (EG0 : prhPv_gtrace d (rest_atR tb text p) = []).
{ unfold prhPv_gtrace. rewrite (vt_jr_value_nil _ d _ [] Hsk). reflexivity. }
split; [exact (vt_jr_value_nil _ d _ [] Hsk)|].
split; [exact Hled|].
split; [exact (proj1 Hroom)|].
(* the hull use: no allocator call on this arm, the allocator's secondary entries are the entry's *)
split; [apply PresetHullBudget.hull_used_secs; rewrite Efz; reflexivity|].
split.
{ rewrite Efz. change (PresetReqAt.rd_hevs []) with (@nil PresetReqAt.hev).
  rewrite PresetReqAt.hlive_from_nil.
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
    with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
  apply Permutation_refl. }
split.
{ intros sm x os i Hz0 hist Hpos _. exists hist. rewrite Efz.
  change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
  apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
split.
{ intros sm x os i Hz0 hist Hpos _ _ _. split; [reflexivity|].
  split; [rewrite (vt_jr_value_nil _ d _ [] Hsk); reflexivity|].
  exists hist. rewrite EG0, Efz.
  change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
  apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
(* the outcome of an injected reading: the value's all-granted trace makes no call here, so no failure lies in its
   window *)
split.
{ intros sm x os i Hz0 hist _ _ _ Hw. rewrite EG0 in Hw. change (Z.of_nat (calls [])) with 0 in Hw. lia. }
split.
{ unfold rd_ledger_move. rewrite EG0. cbn [PjGrammar.calls lszR nliveR hpeakR map length app].
  split; [split; [intros i Hi; cbn in Hi; lia | split; [left; reflexivity | intros i Hi; cbn in Hi; lia]]|].
  split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
  split; [split; intros Hc; cbn in Hc; [lia | reflexivity]|].
  split; [apply Permutation_refl|].
  split; [constructor|].
  split; [reflexivity|].
  unfold prh_refused_peak. cbn [List.seq map fold_right]. clear - Hlp. lia. }
split; [intros aa kk Hak; destruct Hak|].
split; [rewrite Hab; cbn [prhReader_ab map app]; apply Permutation_refl|].
split; [rewrite Hfr; apply Permutation_refl|].
split; [cbn [hpeakR]; lia|].
split.
{ rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B ly0 S0), Hab.
  unfold prh_held. cbn [PjGrammar.held PjGrammar.calls fold_right map Z.of_nat]. lia. }
split; [reflexivity|].
split; [reflexivity|].
(* the free order of the untouched node: no block (vrd_zero_fo), and the model's list at end of text is empty
   (VrdNum.vrd_frees_eof) *)
split.
{ intros _ n _. exists []. split; [apply vrd_zero_fo; [exact Hvrw | exact Hvzero]|].
  rewrite (vrd_frees_eof d (rest_atR tb text p) [] Hsk). reflexivity. }
split.
{ exists p', (Z.of_nat d). split; [lia|]. split; [lia|].
  split; [exact Vp|]. split; [exact Ve|]. split; [exact Vd|]. exact Hrw. }
apply vrd_zero_fd; [exact Hvrw | exact Hvzero].
Qed.
End eof.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. THE EPILOGUE'S TRANSFER PREMISE: the arm's answer vrd_pv_post at row 225, read after the tail's writes (inside   *)
(*    this call's own fake frame, its shadow and the flag byte) and the frame's release, IS the text's post body.      *)
(*    Every byte the post reads - the statics, the ledger's block heads, the subtree's blocks, the node, the cursor,   *)
(*    the text - is in a live allocator block, in ANOTHER live frame, in the image, or on the real stack, and none of  *)
(*    those meets the released frame, its shadow or its flag byte (AR_laws_x at the join state).                      *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section close.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* the epilogue's own Section hypotheses (VrdEpi.v / VrdEpiP.v FFLX and SFX, verbatim) *)
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* IMAGE FACT (S1ImgA.pst_in_img_A at the instance): the ledger statics are image bytes *)
Hypothesis PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
(* PARAMETER FACT (CfParamsPreset.preset_head_wide at the instance) *)
Hypothesis H_cfhead : 8 <= cf_head.

(* a byte off the image keeps writability when its view is kept (the view is the overlay byte there) *)
Lemma vt_wr_keep : forall (H : word -> bool) m m' x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  aview SEGS H m' x = aview SEGS H m x -> writable_at SEGS (mrestrict H m) x -> writable_at SEGS (mrestrict H m') x.
Proof.
intros H m m' x Hx Hn Hav Hw. unfold writable_at, wview in *.
pose proof (seg_rom_none SEGS x Hx Hn) as Hrom.
pose proof (find_segment_none SEGS x Hn) as Hfs.
rewrite unsigned_lit_small in Hw |- * by lia. rewrite Hfs in Hw |- *.
unfold aview, mbyte in Hav. rewrite Hrom in Hav.
destruct (mrestrict H m (Z_to_bv 64 x)) eqn:E1; [|exfalso; exact (Hw eq_refl)].
destruct (mrestrict H m' (Z_to_bv 64 x)) eqn:E2; [discriminate | cbn in Hav; discriminate].
Qed.

(* two entries of a frame list around a released frame are apart from it *)
Lemma vt_frames_apart : forall ly S Hp W mem md pos l1 l2 f,
  ARx ly S Hp W mem md -> frames S = l1 ++ (0, pos) :: l2 -> In f (l1 ++ l2) ->
  zdisjoint (frame_rng ly (0, pos)) (frame_rng ly f).
Proof.
intros ly S Hp W mem md pos l1 l2 f HAR Hfr Hf.
apply in_app_or in Hf as [Hf | Hf]; apply in_split in Hf as (la & lb & ->).
- assert (E : frames S = la ++ f :: lb ++ (0, pos) :: l2) by (rewrite Hfr, <- app_assoc; reflexivity).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md f (0, pos) la lb l2 HAR E) as Hd.
  unfold zdisjoint in *. lia.
- exact (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) f l1 la lb HAR Hfr).
Qed.

(* WHERE A BYTE OF THE POST CAN BE, at the join state: a live allocator block, another live frame, the image, or the
   real stack *)
Definition vt_cls (ly : alayout) (S : astate) (l1 l2 : list (Z * Z)) (x : Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m) \/
  (exists cid pos', In (cid, pos') (l1 ++ l2) /\
     frame_addr ly cid pos' <= x < frame_addr ly cid pos' + fs_frame_bytes cid) \/
  in_img SEGS x \/
  (alloc_ceiling <= x < 2 ^ 47 /\ ly_stk_lo ly <= x < ly_stk_hi ly).

Lemma vt_apart : forall ly S Hp W mem md pos l1 l2 x,
  ARx ly S Hp W mem md -> frames S = l1 ++ (0, pos) :: l2 -> vt_cls ly S l1 l2 x ->
  0 <= x < 2 ^ 64 /\ ~ in_frames ly [(0, pos)] x /\ x <> flag_addr ly 0 pos.
Proof.
intros ly S Hp W mem md pos l1 l2 x HAR Hfr Hx.
assert (Hin : In (0, pos) (frames S)) by (rewrite Hfr; apply in_or_app; right; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR Hin) as (HF4 & HFc & HFapp).
destruct (FFLX ly S Hp W mem md 0 pos HAR Hin) as (Hfo & Hfapp & Hfimg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
rewrite Hfb in HFc, HFapp.
assert (HinS : forall f, In f (l1 ++ l2) -> In f (frames S)).
{ intros f Hf. rewrite Hfr. apply in_app_or in Hf as [Hf | Hf]; apply in_or_app; [left | right; right]; exact Hf. }
(* the byte's own bounds, and app / shadow facts per class *)
assert (HB : 0 <= x < 2 ^ 64 /\
             ((4096 <= x /\ (x < kLowShadowBeg \/ (kHighMemBeg <= x /\ x < ASAN_CEIL))) \/ x < kLowMemEnd \/
              alloc_ceiling <= x < 2 ^ 47)).
{ destruct Hx as [(b & m & Hbm & Hr) | [(cid & pos' & Hc & Hr) | [Hi | (Hc & Hs1 & Hs2)]]].
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & Hb4 & _ & Happ & _).
    unfold in_app in Happ. split; [unfold ASAN_CEIL, kLowShadowBeg in *; lia|]. left. unfold ASAN_CEIL in *. lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR (HinS _ Hc)) as (_ & _ & Happ).
    unfold in_app in Happ. split; [unfold ASAN_CEIL, kLowShadowBeg in *; lia|]. left. unfold ASAN_CEIL in *. lia.
  - pose proof (@pa_segs_low _ A_prog_listing PI_prog_A x Hi). split; [lia|]. right; left; lia.
  - split; [lia|]. right; right; lia. }
split; [exact (proj1 HB)|].
split.
- intros (cid & pos0 & Hc & Hr). destruct Hc as [Ec | []]. injection Ec as <- <-.
  rewrite Hfb in Hr. change (64 / 8) with 8 in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
  destruct Hr as [Hr | Hr].
  + destruct Hx as [(b & m & Hbm & Hbr) | [(cid & pos' & Hc & Hcr) | [Hi | (Hc & Hs1 & Hs2)]]].
    * apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) b m x HAR Hin Hbm); [|exact Hbr].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfb. lia.
    * pose proof (vt_frames_apart ly S Hp W mem md pos l1 l2 (cid, pos') HAR Hfr Hc) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb in Hd. lia.
    * exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md 0 pos x HAR Hin ltac:(rewrite Hfb; lia) Hi).
    * lia.
  + unfold shadow_addr in Hr.
    assert (Hs : SHADOW_OFF <= x < kHighMemBeg).
    { pose proof (Z.div_le_mono 4096 (frame_addr ly 0 pos) 8 ltac:(lia) HF4).
      pose proof (Z.div_lt_upper_bound (frame_addr ly 0 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold SHADOW_OFF in *. lia. }
    destruct HB as (_ & [Ha | [Ha | Ha]]); unfold SHADOW_OFF, kLowShadowBeg, ASAN_CEIL in *; lia.
- intros ->.
  destruct Hx as [(b & m & Hbm & Hbr) | [(cid & pos' & Hc & Hcr) | [Hi | (Hc & Hs1 & Hs2)]]].
  + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbm) as (_ & _ & _ & _ & Hown & _).
    exact (proj2 (Hown _ Hbr) Hfo).
  + destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR (HinS _ Hc)) as (_ & _ & Hown & _).
    exact (proj2 (Hown _ Hcr) Hfo).
  + exact (Hfimg Hi).
  + exact (alx_stack SEGS B ARx LAWS ly S Hp W mem md (flag_addr ly 0 pos) HAR ltac:(lia) Hfo).
Qed.


(* THE BODY OF tparse_value_specX's POST, by name: the text's own named post tpvP_Q (PRH_FnParse.v, whose tpvP_Q_check
   fails to build if the two ever differ), at this file's listing instance and with this file's argument order. The top
   theorem meets the text through it by conversion, and every conjunct the text adds (the hull use, the outcome of an
   injected reading) comes with it. *)
Definition vrd_value_q (d : nat) (q v text len p : Z) (tb : list Z) (ly : alayout) (S : astate)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tpvP_Q (L := A_prog_listing) (PA := PI_prog_A) B d ly S q text len p tb v Lam peak cnt fail ran most own.

(* the text bytes at the entry state: an allocator block, or an image byte (VrdPro.vrd_text_where's argument). The
   text's home is read at the image's own listing instance, named: no argument of prhReader_home fixes it *)
Lemma vt_text_where : forall ly0 S0 Hp0 (W0 : world SEGS) mem0 Lam peak cnt fail ran most own text len i,
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own ->
  prhReader_home (L := A_prog_listing) (PA := PI_prog_A) B ly0 S0 Hp0 Lam text len ->
  0 <= i < len ->
  (exists b m, In (b, m) (ablocks B ly0 S0) /\ b <= text + i < b + req_size m) \/ in_img SEGS (text + i).
Proof.
intros ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own text len i HLED HHOME Hi.
pose proof cf_head_nonneg as Hch.
assert (RO : forall a, PresetRodata.in_roP SEGS (@pa_relro_lo _ A_prog_listing PI_prog_A)
                         (@pa_relro_hi _ A_prog_listing PI_prog_A) a -> in_img SEGS a).
{ intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] |
    exact (@pa_relro_img _ _ PI_prog_A a Hr)]. }
destruct HHOME as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnhp & Hb & Hm)].
- left. pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ b m _ _ HLED Hin)
    as (Hm0 & Hab & _). cbn [fst snd] in *.
  exists (b - cf_head), (m + cf_head). split; [exact Hab|].
  assert (Hmc : 0 <= m + cf_head) by lia. pose proof (req_size_pos (m + cf_head) Hmc). lia.
- right. exact (RO _ (proj1 (Hro (text + i) ltac:(lia)))).
- right. exact (RO _ (proj1 (Hro (text + i) ltac:(lia)))).
- left. exists b, m. split; [exact Hin|]. pose proof (req_size_pos m ltac:(lia)). lia.
Qed.

(* THE TRANSFER: vrd_pv_post at the join, with the join's journal (at the budget WS the arm's vrd_epi_aR names, at the
   re-hiding relation wle' SEGS RZ_cf of the texts' posts), gives the text's post body after the release *)
Lemma vrd_pv_close : forall d e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 ch Lam peak cnt fail ran most own pos rv
    ly S Hp W mem md k WS (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_value d + e) (spZ regs0 + e)
    (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k WS ->
  vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv ly S Hp W mem ->
  getr regs' 10 = w64 rv ->
  frames (stack_free_state 0 pos S) = frames S0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  vrd_value_q d q v text len p tb ly0 S0 Lam peak cnt fail ran most own ly (stack_free_state 0 pos S) Hp W regs' mem' md'.
Proof.
intros d e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 ch Lam peak cnt fail ran most own pos rv ly S Hp W mem md k WS
  regs' mem' md' HFP HRD HJ HRQ H10 HFRS HKEEP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hch.
destruct HRQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HJV & HLED & HRL & HHU & HLV & HRP &
  HOC & HINJ & HLM & HDF & HAB & HFR & HHP & HBB & HLS & HM).
(* the journal read by its named projections (YCbqG.ajxR_ar / ajxR_ly), never positionally *)
pose proof (YCbqG.ajxR_ar HJ) as HAR. cbv beta in HAR.
pose proof (YCbqG.ajxR_ly HJ) as HLY.
assert (EF : ly_F ly = ly_F ly0) by (destruct HLY as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Elo : ly_stk_lo ly = ly_stk_lo ly0) by (destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & _); exact Elo).
assert (Ehi : ly_stk_hi ly = ly_stk_hi ly0) by (destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _); exact Ehi).
assert (HinJ : In (0, pos) (frames S)) by (apply (Permutation_in _ (Permutation_sym HFR)); left; reflexivity).
destruct (SFX ly S Hp W mem md 0 pos HAR HinJ) as (l1 & l2 & Efr & Efr').
rewrite HFRS in Efr'.
assert (HinS : forall f, In f (l1 ++ l2) -> In f (frames S)).
{ intros f Hf. rewrite Efr. apply in_app_or in Hf as [Hf | Hf]; apply in_or_app; [left | right; right]; exact Hf. }
(* the entry facts the classification reads *)
pose proof HFP as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HRD as (_ & _ & _ & _ & HIN0 & HWIN & Hq1 & Hq2 & _ & HSRC & HHOME & _ & HNODE & _ & _ & HVW & HLED0 & _).
pose proof HWIN as (He0 & _ & Hetop & _).
(* every block of the entry, and every harness block of the join's ledger, is a block of the join *)
assert (AB0 : forall b m, In (b, m) (ablocks B ly0 S0) -> In (b, m) (ablocks B ly S)).
{ intros b m Hb. apply (Permutation_in _ (Permutation_sym HAB)). apply in_or_app. right. exact Hb. }
assert (LB : forall a kk, In (a, kk) Lam' -> 0 <= kk /\ In (a - cf_head, kk + cf_head) (ablocks B ly S)).
{ intros a kk Hin. destruct (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ a kk _ _ HLED Hin)
    as (Hk0 & Hab & _). exact (conj Hk0 Hab). }
assert (DL : forall b, In b D -> In b Lam').
{ intros b Hb. destruct HLM as (_ & _ & _ & HPL & _).
  apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hb. }
assert (LL : forall b, In b Lam -> In b Lam').
{ intros b Hb. destruct HLM as (_ & _ & _ & HPL & _).
  apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. exact Hb. }
(* THE CLASSES of the post's bytes: a block or another frame (the harness blocks, the node), the image (the statics,
   an image text), the real stack (the cursor) *)
assert (BF : forall x, ((exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m) \/
                        (exists cid pos', In (cid, pos') (l1 ++ l2) /\
                           frame_addr ly cid pos' <= x < frame_addr ly cid pos' + fs_frame_bytes cid)) ->
                       vt_cls ly S l1 l2 x /\ ~ in_img SEGS x).
{ intros x [(b & m & Hb & Hr) | (cid & pos' & Hc & Hr)].
  - split; [left; exists b, m; exact (conj Hb Hr)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HAR Hb Hr).
  - split; [right; left; exists cid, pos'; exact (conj Hc Hr)|].
    exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos' x HAR (HinS _ Hc) Hr). }
assert (CB : forall a kk x, In (a, kk) Lam' -> a - cf_head <= x < a + kk -> vt_cls ly S l1 l2 x /\ ~ in_img SEGS x).
{ intros a kk x Hin Hx. apply BF. left. destruct (LB a kk Hin) as (Hk0 & Hab).
  exists (a - cf_head), (kk + cf_head). split; [exact Hab|].
  assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (req_size_pos (kk + cf_head) Hkc). lia. }
assert (CQ : forall x, q <= x < q + 24 -> vt_cls ly S l1 l2 x /\ ~ in_img SEGS x).
{ intros x Hx. pose proof (vrd_stk_nonneg (PIm := PIm) d) as Hs0.
  split; [right; right; right; rewrite Elo, Ehi; lia|].
  intros Hi. pose proof (@pa_segs_low _ A_prog_listing PI_prog_A x Hi). lia. }
assert (CV : forall x, v <= x < v + 56 -> vt_cls ly S l1 l2 x /\ ~ in_img SEGS x).
{ intros x Hx. pose proof HNODE as (_ & _ & _ & _ & Hat & _).
  destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                  [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
  - apply (CB a0 k0 x (LL _ HinL)). lia.
  - apply BF. left. exists b0, m0. split; [exact (AB0 _ _ Hinb)|].
    assert (Hm00 : 0 <= m0) by lia. pose proof (req_size_pos m0 Hm00). lia.
  - apply BF. right. exists cid, pos'. split; [rewrite <- Efr'; exact Hinf|].
    unfold frame_addr in *. rewrite EF. lia.
  - exfalso. destruct HVW as [Hv | Hv]; lia. }
assert (CT : forall x, text <= x < text + len -> vt_cls ly S l1 l2 x).
{ intros x Hx. destruct (vt_text_where ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own text len (x - text)
    HLED0 HHOME ltac:(lia)) as [(b & m & Hb & Hr) | Hi].
  - left. exists b, m. split; [exact (AB0 _ _ Hb) | lia].
  - right; right; left. replace x with (text + (x - text)) by lia. exact Hi. }
(* the kept view on each class, and writability off the image *)
assert (KV : forall x, vt_cls ly S l1 l2 x -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x).
{ intros x Hx. destruct (vt_apart ly S Hp W mem md pos l1 l2 x HAR Efr Hx) as (Hr & Hnf & Hnfl).
  exact (HKEEP x Hr Hnf Hnfl). }
assert (KW : forall x, vt_cls ly S l1 l2 x /\ ~ in_img SEGS x ->
          writable_at SEGS (rdW W mem) x -> writable_at SEGS (rdW W mem') x).
{ intros x (Hx & Hn). destruct (vt_apart ly S Hp W mem md pos l1 l2 x HAR Efr Hx) as (Hr & _).
  exact (vt_wr_keep (w_H W) mem mem' x Hr Hn (KV x Hx)). }
assert (KQ : forall a n x, q <= a -> a + Z.of_nat n <= q + 24 ->
          val_mem SEGS (rdW W mem) a n x -> val_mem SEGS (rdW W mem') a n x).
{ intros a n x H1 H2 Hv. eapply val_mem_kept; [|exact Hv]. intros kk Hk. apply KV. apply CQ. lia. }
assert (AGR : pj_agreeR SEGS (rdW W mem) (rdW W mem') (pj_footR v D)).
{ intros x Hx. assert (Hc : vt_cls ly S l1 l2 x /\ ~ in_img SEGS x).
  { destruct Hx as [Hx | ((a, kk) & Hb & Hx)]; [exact (CV x Hx)|].
    unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply (CB a kk x (DL _ Hb)). lia. }
  split; [apply (mbyte_of_aview SEGS); exact (KV x (proj1 Hc)) | exact (KW x Hc)]. }
assert (EAB : ablocks B ly (stack_free_state 0 pos S) = ablocks B ly S)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
unfold vrd_value_q, tpvP_Q.
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
split; [exact HJV|].
split.
{ apply (S1Ledger.prh_ledger_kept_aview (PA := PI_prog_A) B ly S Hp W mem ly (stack_free_state 0 pos S) Hp W mem'
    Lam' peak' cnt' fail' ran' most own HLED).
  - intros a Ha. apply KV. right; right; left. exact (PST_IMG a Ha).
  - intros a kk i Hin Hi. destruct (LB a kk Hin) as (Hk0 & _).
    assert (Hx : a - cf_head <= a - cf_head + i < a + kk) by (pose proof H_cfhead; lia).
    exact (KV _ (proj1 (CB a kk (a - cf_head + i) Hin Hx))).
  - intros a kk _ Hab. rewrite EAB. exact Hab.
  - apply Permutation_refl. }
split; [exact (RL_stack_free S 0 pos HRL)|].
(* the hull use: the frame's release sets only the fake stack, so the allocator's secondary entries are the join's
   (hull_used reads st_secs only) *)
split; [exact HHU|].
split; [exact HLV|].
split.
{ intros sm x os i H0 hist HP HR. destruct (HRP sm x os i H0 hist HP HR) as (hist' & H').
  exists hist'. apply PresetRoomPosKeep.room_pos_stack_free. exact H'. }
split.
{ intros sm x os i H0 hist HP HR HC Hw. destruct (HOC sm x os i H0 hist HP HR HC Hw) as (Hr & Hf & hist' & H').
  split; [exact Hr|]. split; [exact Hf|]. exists hist'. apply PresetRoomPosKeep.room_pos_stack_free. exact H'. }
(* the outcome of an injected reading: it speaks of the entry state, the outcomes and the trace only *)
split; [exact HINJ|].
split; [exact HLM|].
split.
{ unfold rd_blocks_move. split; [exact HDF|]. split; [rewrite EAB; exact HAB|].
  split; [rewrite HFRS; apply Permutation_refl | exact HHP]. }
split; [rewrite (blocks_bytes_bsum B ly (stack_free_state 0 pos S)), EAB, <- (blocks_bytes_bsum B ly S); exact HBB|].
split; [exact HLS|].
(* the free order (both arms) moves with the footprint, as pj_nodeR / pj_fdR do (PRH_PjOrder.pj_foR_frame) *)
assert (FO : forall n F, PRH_PjOrder.pj_foR SEGS (rdW W mem) (prh_lin Lam') n v D F ->
               PRH_PjOrder.pj_foR SEGS (rdW W mem') (prh_lin Lam') n v D F).
{ intros n F HF. exact (PRH_PjOrder.pj_foR_frame SEGS n _ _ _ _ v D F HF
    (PRH_PjOrder.pj_foR_lblk SEGS _ _ n v D F HF) AGR). }
destruct res as [[t r]|].
- destruct HM as (Hrv & HFO & HIN & HND & HNC & HLD). unfold tpvP_ASome.
  split; [rewrite H10, Hrv; reflexivity|].
  split; [intros Hh n Hn; destruct (HFO Hh n Hn) as (F & HF & HFm); exists F; exact (conj (FO n F HF) HFm)|].
  split; [|split; [exact (pj_nodeR_frame SEGS t _ _ _ v D HND AGR) |
                   split; [exact (vrd_ncapR_frame SEGS t _ _ _ v D HND HNC AGR) | exact HLD]]].
  destruct HIN as (Vq & Vq8 & Vq16 & Hrw & Hq8 & Ht0 & Htl & Hpr & Hlen & GT & Hdj & Hd).
  split; [apply (KQ q 8%nat); [lia | cbn; lia | exact Vq]|].
  split; [apply (KQ (q + 8) 8%nat); [lia | cbn; lia | exact Vq8]|].
  split; [apply (KQ (q + 16) 4%nat); [lia | cbn; lia | exact Vq16]|].
  split; [intros x Hx; apply KW; [apply CQ; lia | exact (Hrw x Hx)]|].
  split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hpr|]. split; [exact Hlen|].
  split; [|split; [exact Hdj | exact Hd]].
  apply (garr8R_frame SEGS _ _ text tb GT). intros x Hx. apply (mbyte_of_aview SEGS).
  apply KV. apply CT. lia.
- destruct HM as (Hrv & HFO & HAF & HFD). unfold tpvP_ANone.
  split; [rewrite H10, Hrv; reflexivity|].
  split; [intros Hh n Hn; destruct (HFO Hh n Hn) as (F & HF & HFm); exists F; exact (conj (FO n F HF) HFm)|].
  split; [|exact (vrd_fdR_frame SEGS _ _ _ _ _ _ HFD AGR)].
  destruct HAF as (p0 & d0 & Hpa0 & Hda0 & Vq & Vq8 & Vq16 & Hrw).
  exists p0, d0. split; [exact Hpa0|]. split; [exact Hda0|].
  split; [apply (KQ q 8%nat); [lia | cbn; lia | exact Vq]|].
  split; [apply (KQ (q + 8) 8%nat); [lia | cbn; lia | exact Vq8]|].
  split; [apply (KQ (q + 16) 4%nat); [lia | cbn; lia | exact Vq16]|].
  intros x Hx. apply KW; [apply CQ; lia | exact (Hrw x Hx)].
Qed.
End close.

(* the keyword of a literal byte, and its node tag *)
Definition vt_kw_cw (b : Z) : list Z :=
  if b =? 116 then PjGrammar.w_true else if b =? 102 then PjGrammar.w_false else PjGrammar.w_null.
Definition vt_kw_ty (b : Z) : Z := if b =? 116 then 2 else if b =? 102 then 1 else 0.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. parse_value AT ONE DEPTH d, from parse_items at the same d: the entry segment, the five arms, the epilogue.     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section value.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* VrdPro.vrd_pro_a_P's Section hypotheses, verbatim *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
Hypothesis UARC : 4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kLowMemEnd /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell B).
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis FSI : fs_iface SEGS B ARx.
Hypothesis TB : AF0m.TfibSyms B.
Hypothesis HLc : HL = cf_head.
Hypothesis SYMS : asyms_ok B.
Hypothesis H_imgvis : forall ly' S' Hp' W' mem' md' a, ARx ly' S' Hp' W' mem' md' -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W') mem' (shadow_addr a) <> None.
Hypothesis H_pst : forall a, Exists (in_zr a) prh_pst ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis H_cfhead : 8 <= cf_head.
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.
(* the epilogue's (VrdEpi.v / VrdEpiP.v Section c), verbatim *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis FPRES : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* the arms' image facts (witnessed at prh_img_A below / in VrdArmLCWit.v) *)
Hypothesis H_s0ps : pi_s0cur F_parse_string = Some 0.
Hypothesis H_s0pi : pi_s0cur F_parse_items = Some 0.
Hypothesis H_stk_str : forall d, STK_parse_string + 176 <= STK_parse_value d.
Hypothesis H_stk_items : forall d, STK_parse_items d + 176 <= STK_parse_value d.
Hypothesis H_stk_items0 : forall d, 0 <= STK_parse_items d.
Hypothesis H_stk_lit : forall d, STK_literal + 176 <= STK_parse_value d.
Hypothesis H_stk_lit0 : 0 <= STK_literal.
(* the literal arm's keyword bytes: the kit's tliteral_specX read premise at a state with the read-only view (image facts
   of the three .rodata keywords, decided at the instance below), for the keyword slack vt_slack the instance picks *)
Variable vt_slack : Z -> list Z.
Hypothesis H_kw : forall b ly' S' Hp' (W' : world SEGS) mem' md', ARx ly' S' Hp' W' mem' md' ->
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PI_prog_A) (@pa_relro_hi _ A_prog_listing PI_prog_A) B
    (aview SEGS (w_H W') mem') -> YAkMemnorm.memnorm SEGS mem' ->
  (b = 116 \/ b = 102 \/ b = 110) ->
  cstr_ok W' mem' (vrd_kw_addr b) (vt_kw_cw b) /\
  garr8 SEGS (mrestrict (w_H W') mem') (vrd_kw_addr b) (vt_kw_cw b ++ 0 :: vt_slack b).
Hypothesis H_kw_num : forall b, (b = 116 \/ b = 102 \/ b = 110) ->
  vrd_kw_addr b + Z.of_nat (length (vt_kw_cw b)) + 1 + Z.of_nat (length (vt_slack b)) <= 2 ^ 46 /\
  ~ In 0 (vt_kw_cw b) /\
  (- (vrd_kw_addr b + Z.of_nat (length (vt_kw_cw b)) + 1)) mod 8 <= Z.of_nat (length (vt_slack b)).
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
(* THE CALLEE TEXTS (the kit's cut, PRH_FnReader.v / PRH_FnAlloc.v): named here, discharged at the instance (Section top) *)
Hypothesis H_parse_string : tparse_string_specX B ARx SK CTX0 CW.
Hypothesis H_literal : tliteral_specX B ARx SK.
Hypothesis H_fuzz_malloc : tfuzz_malloc_specX B ARx SK.
(* THE NUMBER ARM, by the statement's own name (VrdNum.vrd_num_a_stmt_P: the arm with the generic memory invariant P
   and its three laws, P of the dispatch memory to P of the join memory; no memnorm stand-in). Discharged at the
   instance by VrdNumA.vrd_num_a_P (vt_value_step below). *)
Hypothesis H_num_arm : vrd_num_a_stmt_P B ARx SK.

(* the join state with its own journal in the arm's answer (vrd_epi_aR carries both at the same state; the journal at
   the budget WS it names, at the re-hiding relation wle' SEGS RZ_cf: every arm reaches the join there) *)
Lemma vt_epi_aJ : forall fx2 d CW' e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c,
  vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW' e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
    RQ W c ->
  vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW' e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
    (fun ly S Hp W' mem => RQ ly S Hp W' mem /\ exists md k WS,
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_value d + e)
         (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W' mem md k WS) W c.
Proof.
intros fx2 d CW' e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c HE.
(* vrd_epi_aR read and built BY NAME through VrdNum's record vrd_epi_R (vrd_epi_R_of, its vepi_* projections, and
   vrd_epi_aR_of_R), never positionally on the definition *)
apply vrd_epi_R_of in HE. destruct HE as (regs & mem & md & ly & S & Hp & k & HR).
apply vrd_epi_aR_of_R with (regs := regs) (mem := mem) (md := md) (ly := ly) (S := S) (Hp := Hp) (k := k).
destruct (vepi_jrn HR) as (WS & HJ & HWB).
refine {| vepi_cfg := vepi_cfg HR; vepi_jrn := vepi_jrn HR; vepi_win := vepi_win HR; vepi_s0 := vepi_s0 HR;
  vepi_s2 := vepi_s2 HR; vepi_s10 := vepi_s10 HR; vepi_s8 := vepi_s8 HR; vepi_s5 := vepi_s5 HR; vepi_gp := vepi_gp HR;
  vepi_tp := vepi_tp HR; vepi_ra := vepi_ra HR; vepi_saved := vepi_saved HR; vepi_flag := vepi_flag HR;
  vepi_frm := vepi_frm HR; vepi_fregs := vepi_fregs HR; vepi_rq := ?[rq] |}.
[rq]: { cbv beta. split; [exact (vepi_rq HR)|]. exists md, k, WS. exact HJ. }
Qed.

(* the dispatch byte a literal arm starts at, and the number arm's default *)
Lemma vt_arm_num : forall b, b <> 34 -> b <> 91 -> b <> 123 -> b <> 116 -> b <> 102 -> b <> 110 ->
  vrd_arm_of b = VA_num.
Proof.
intros b H34 H91 H123 H116 H102 H110. unfold vrd_arm_of.
rewrite (proj2 (Z.eqb_neq b 34) H34), (proj2 (Z.eqb_neq b 91) H91), (proj2 (Z.eqb_neq b 102) H102),
  (proj2 (Z.eqb_neq b 110) H110), (proj2 (Z.eqb_neq b 116) H116), (proj2 (Z.eqb_neq b 123) H123).
reflexivity.
Qed.

Theorem vrd_value_at : forall d : nat,
  (forall CTX' : list (list Z), tparse_items_specX B ARx SK d CTX' CTX0 CW) ->
  forall CTX : list (list Z), tparse_value_specX B ARx SK d CTX CTX0 CW.
Proof.
intros d HPI CTX. unfold tparse_value_specX.
intros ly S Hp W regs mem md ch e q text len p tb v Lam peak cnt fail ran most own
  HFP HMN HCTX HCLO HCUR HCW HCHN HCUC H10 H11 HRD HROOM HWR HSEC HL24 HHULL HFRC.
set (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS P)
  by exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)).
assert (PCALL : srr_inv_call SEGS P) by exact (srr_inv_call_imp SEGS mem).
assert (PMN : srr_inv_mn SEGS P) by exact (srr_inv_mn_imp SEGS mem HMN).
(* the text concludes SRr' SEGS RZ_cf: the entry segment (no call) runs at wle and is lifted *)
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  exact (vrd_pro_a_P B ARx LAWS PAL UARC SK OWNLOW FSI TB HLc SYMS H_imgvis H_pst H_cfhead HI_head P PLAW PCALL
    d ly S Hp W regs mem md ch CTX0 CW e q text len p tb v Lam peak cnt fail ran most own
    HFP HCLO HCUR HCW HCHN HCUC H10 H11 HRD HROOM HWR HSEC HL24 HFRC (fun H => H)). }
intros W1 c1 _ (HD & HP1).
(* an arm that crosses no free reaches the join at wle: lifted to the re-hiding relation (SRr_SRr' for the run,
   VrdEpiA.vrd_epi_a_wle' for the join's journal) *)
assert (LIFT : forall W' c',
  SRr SEGS W' c' (fun W2 c2 => (exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly S Hp W regs mem md pos rv
      (vrd_pv_post B d e q v text len p tb ly S Lam peak cnt fail ran most own pos rv) W2 c2) /\
    P (ms_mem (cfg_ms c2))) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W' c' (fun W2 c2 => (exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly S Hp W regs mem md pos rv
      (vrd_pv_post B d e q v text len p tb ly S Lam peak cnt fail ran most own pos rv) W2 c2) /\
    P (ms_mem (cfg_ms c2)))).
{ intros W' c' H. eapply (SRr'_mono SEGS YGcfRehidePost.RZ_cf); [exact (SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _ H)|].
  intros W2 c2 _ ((fx2 & pos & rv & HE) & HPc). split; [|exact HPc].
  exists fx2, pos, rv. exact (vrd_epi_a_wle' B ARx SK HE). }
(* ---- THE ARM, chosen by the first byte after the white space ---- *)
assert (ARM : SRr' SEGS YGcfRehidePost.RZ_cf W1 c1 (fun W2 c2 => (exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly S Hp W regs mem md pos rv
      (vrd_pv_post B d e q v text len p tb ly S Lam peak cnt fail ran most own pos rv) W2 c2) /\
    P (ms_mem (cfg_ms c2)))).
{ destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y] eqn:Hsk.
  - apply LIFT.
    exact (vrd_eof_a_P B ARx SK LAWS P PLAW d CTX0 CW ly S Hp W regs mem md ch e q v text len p tb Lam peak cnt fail
      ran most own W1 c1 HD Hsk HP1).
  - destruct (Z.eq_dec b 34) as [E34|N34]; [subst b|].
    { exact (vrd_str_a_okP B ARx SK LAWS d CTX0 CW H_parse_string HI_head P PLAW PCALL HLc H_cfhead
        (fun a Ha => proj1 (H_pst a Ha)) H_s0ps H_s0pi ly S Hp W regs mem md ch e q v text len p tb Lam peak cnt
        fail ran most own W1 c1 y HFP HD HHULL Hsk (H_stk_str d) HP1). }
    assert (CONT : forall o : bool, b = (if o then 123 else 91) ->
      SRr' SEGS YGcfRehidePost.RZ_cf W1 c1 (fun W2 c2 => (exists (fx2 : YK11.FPState) (pos rv : Z),
        vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly S Hp W regs mem md pos rv
          (vrd_pv_post B d e q v text len p tb ly S Lam peak cnt fail ran most own pos rv) W2 c2) /\
        P (ms_mem (cfg_ms c2)))).
    { intros o Hb.
      set (CTXc := [A_prog_base + 4 * Z.of_nat (A_prog_slot AS_parse_value + 215) :: raZ regs :: spine ch]).
      exact (vrd_cont_aLC_P_holds B ARx SK LAWS P d CTXc CTX0 CW PCALL PMN ly S Hp W regs mem md ch e q v text len p
        tb Lam peak cnt fail ran most own W1 c1 o b y (HPI CTXc) HFP HD HHULL Hsk Hb (or_introl eq_refl)
        (H_stk_items d) (H_stk_items0 d) H_s0ps H_s0pi HP1). }
    destruct (Z.eq_dec b 123) as [E123|N123]; [exact (CONT true E123)|].
    destruct (Z.eq_dec b 91) as [E91|N91]; [exact (CONT false E91)|].
    assert (LIT : b = 116 \/ b = 102 \/ b = 110 ->
      SRr' SEGS YGcfRehidePost.RZ_cf W1 c1 (fun W2 c2 => (exists (fx2 : YK11.FPState) (pos rv : Z),
        vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly S Hp W regs mem md pos rv
          (vrd_pv_post B d e q v text len p tb ly S Lam peak cnt fail ran most own pos rv) W2 c2) /\
        P (ms_mem (cfg_ms c2)))).
    { intros Hb3. apply LIFT.
      destruct (H_kw_num b Hb3) as (Hw46 & Hnul & Hslack).
      pose proof HFP as ((_ & _ & _ & _ & _ & Hstk & _) & _).
      pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & _).
      pose proof asan_consts as (C1 & _).
      apply (vrd_lit_aLC_P_holds B ARx SK LAWS P d CTX0 CW PCALL ly S Hp W regs mem md ch e q v text len p tb Lam
        peak cnt fail ran most own W1 c1 b (vt_kw_ty b) y (vt_kw_cw b) (vt_slack b) H_literal HFP HD Hsk).
      - destruct Hb3 as [-> | [-> | ->]]; [left | right; left | right; right]; repeat split; reflexivity.
      - intros regs' mem' md' Hc'.
        pose proof HD as (arm & pos & p' & k & lyd & Sd & Hpd & regsd & memd & mdd & Hcd & HBd).
        unfold vrd_disp_body in HBd. decompose [and] HBd. clear HBd.
        lazymatch goal with X : context [ajournal_x] |- _ => rename X into HJd end.
        lazymatch goal with X : context [PresetRodata.arodata_okP] |- _ => rename X into Hrod end.
        assert (Em : memd = mem') by (rewrite Hcd in Hc'; exact (f_equal (fun c => ms_mem (cfg_ms c)) Hc')).
        assert (HMd : YAkMemnorm.memnorm SEGS memd).
        { pose proof HP1 as HPm. rewrite Hcd in HPm. exact (HPm HMN). }
        subst mem'. exact (H_kw b lyd Sd Hpd W1 memd mdd (YCbqG.ajx_ar HJd) Hrod HMd Hb3).
      - lia.
      - exact Hnul.
      - exact Hslack.
      - lia.
      - exact (H_stk_lit d).
      - exact H_stk_lit0.
      - exact HP1. }
    destruct (Z.eq_dec b 116) as [E|N116]; [exact (LIT (or_introl E))|].
    destruct (Z.eq_dec b 102) as [E|N102]; [exact (LIT (or_intror (or_introl E)))|].
    destruct (Z.eq_dec b 110) as [E|N110]; [exact (LIT (or_intror (or_intror E)))|].
    apply LIFT.
    apply (H_num_arm P PLAW PCALL PMN ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
      most own W1 c1 H_fuzz_malloc HFP H10 H11 HRD HD HHULL); [|exact HP1].
    rewrite Hsk. exact (vt_arm_num b N34 N91 N123 N116 N102 N110). }
(* ---- THE EPILOGUE (VrdEpiP.vrd_epi_step_P: the budgeted post at the text's wbudget CW 0, the join at wle' SEGS
   RZ_cf), with the transfer vrd_pv_close and the memory keep from P ---- *)
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf); [exact ARM|].
intros W2 c2 _ ((fx2 & pos & rv & HEA) & HP2).
pose proof (vt_epi_aJ fx2 d CW e q v ly S Hp W regs mem md pos rv _ W2 c2 HEA) as HEA'.
eapply (SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ eapply (vrd_epi_step_P (fx := fx) B ARx SK LAWS ASFX FFLX FPRES SFX P PLAW fx2 d CW e q v ly S Hp W regs mem md
    pos rv _ (vrd_value_q B d q v text len p tb ly S Lam peak cnt fail ran most own) W2 c2);
    [| |exact HEA' | exact HP2].
  - pose proof (vrd_stk_big (PIm := PIm) d). lia.
  - intros ly' S' Hp' mem' regs' mem'' md' (HRQ & md1 & k1 & WS1 & HJ1) H10' _ HFRS HKEEP.
    exact (vrd_pv_close B ARx SK LAWS FFLX SFX (fun a Ha => proj1 (H_pst a Ha)) H_cfhead d e q v text len p tb
      ly S Hp W regs mem md ch Lam peak cnt fail ran most own pos rv ly' S' Hp' W2 mem' md1 k1 WS1 regs' mem'' md'
      HFP HRD HJ1 HRQ H10' HFRS HKEEP). }
intros W3 c3 _ (HF & HP3).
(* fpostWFb (nine witnesses, the budget WS with wbudget CW 0 WS) to the text's m-form fpostWFbm = fpostWFb at fQmn *)
destruct HF as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & WS' & -> & F1 & F2 & F3 & F4 & F5 & F6 & FQ).
unfold fpostWFbm, fQmn.
exists fx', ly', S', Hp', regs', mem', md', k', WS'.
split; [reflexivity|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
split; [exact F5|]. split; [exact F6|]. split; [exact FQ | exact HP3].
Qed.

End value.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. THE REAL INSTANCE: image A' (prh_img_A; the listing A_prog_listing / PI_prog_A), CfParams_preset, CfImg_A,      *)
(*    a Theorem Labs lane's room instance prh_room_live_a8, B := AD2l.TfibB, ARx := ARcf with the error buffers placed           *)
(*    (YGcallcf.v's ARxs, the relation FuzzFree.fuzz_free_holds is stated at), laws YGcallcf.AR_laws_x_xs of           *)
(*    YG0lawscf.AR_laws_ok_cf. fx, rc, SK stay free (the texts quantify them).                                         *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section real.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance PRH_Img.prh_img_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Notation CP := CfParamsPreset.CfParams_preset.
#[local] Notation RLA := (@prh_room_live_a8 CfParamsPreset.CfParams_preset).
#[local] Notation TA := AD2l.TfibB.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).

Definition vt_ARA : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => YG0ncf.ARcf SEGS TA ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S.

(* ---- the engine's and the epilogue's Section hypotheses at the instance ---- *)
Lemma vt_laws : AR_laws_x SEGS TA vt_ARA (@cf_head CP).
Proof. unfold vt_ARA. exact (YGcallcf.AR_laws_x_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.
Lemma vt_ownlow : ARx_owned_low_law SEGS TA vt_ARA.
Proof. unfold vt_ARA. exact (YGcallcf.ARx_owned_low_law_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.
Lemma vt_asfx : forall ly S Hp W mem md mem' md' cid pos,
  vt_ARA ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TA ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  vt_ARA ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. unfold vt_ARA. exact (YGcallScf.astack_free_x_xs SEGS TA). Qed.
Lemma vt_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
  vt_ARA ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TA ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Proof. unfold vt_ARA. exact (YGcallScf.frame_flag_x_xs SEGS TA). Qed.
Lemma vt_fpres : forall ly S Hp (W : world SEGS) mem md cid pos,
  vt_ARA ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Proof.
intros ly S Hp W mem md cid pos [HAR _] Hin.
exact (proj1 (YG0scf.AR_flag_law_ok_cf SEGS TA ly S Hp W mem md cid pos HAR Hin)).
Qed.
Lemma vt_sfx : forall ly S Hp W mem md cid pos, vt_ARA ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGS vt_ARA). Qed.
(* the frame-class interface at ARxs: every field is FCifaceCf.fs_iface_ARcf's at the ARcf half; the two fields that
   produce a state keep the placement half, which reads no fake-stack field (set_fs) and no memory *)
Lemma vt_fsi : fs_iface SEGS TA vt_ARA.
Proof.
destruct (FCifaceCf.fs_iface_ARcf SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA))
  as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16].
constructor; unfold vt_ARA.
- intros ly S Hp W mem md [HAR _]. exact (F1 ly S Hp W mem md HAR).
- intros ly S Hp W mem md [HAR _]. exact (F2 ly S Hp W mem md HAR).
- intros ly S Hp W mem md sg [HAR _]. exact (F3 ly S Hp W mem md sg HAR).
- intros ly S Hp W mem md [HAR _]. exact (F4 ly S Hp W mem md HAR).
- intros ly S Hp W mem md [HAR _]. exact (F5 ly S Hp W mem md HAR).
- intros ly S Hp W mem md [HAR _]. exact (F6 ly S Hp W mem md HAR).
- intros ly S Hp W mem md [HAR _]. exact (F7 ly S Hp W mem md HAR).
- intros ly S Hp W mem md [HAR _]. exact (F8 ly S Hp W mem md HAR).
- intros ly S Hp W mem md [HAR _]. exact (F9 ly S Hp W mem md HAR).
- intros ly S Hp W mem md cid pos a [HAR _]. exact (F10 ly S Hp W mem md cid pos a HAR).
- intros ly S Hp W mem md cid pos a [HAR _]. exact (F11 ly S Hp W mem md cid pos a HAR).
- intros ly S Hp W mem md a [HAR _]. exact (F12 ly S Hp W mem md a HAR).
- intros ly S Hp W mem md mem' md' cid pos hint' [HAR HX] Hc Hpr. cbv zeta.
  intros K1 K2 K3 K4 K5 K6 K7 K8.
  split; [exact (F13 ly S Hp W mem md mem' md' cid pos hint' HAR Hc Hpr K1 K2 K3 K4 K5 K6 K7 K8) | exact HX].
- intros ly S Hp W mem md a [HAR _]. exact (F14 ly S Hp W mem md a HAR).
- intros ly S Hp W mem md mem' md' [HAR HX] K1 K2 K3 K4 K5 K6.
  split; [exact (F15 ly S Hp W mem md mem' md' HAR K1 K2 K3 K4 K5 K6) | exact HX].
- intros ly S Hp W mem md cid pos [HAR _]. exact (F16 ly S Hp W mem md cid pos HAR).
Qed.

(* ---- the image facts at A' ---- *)
(* UARC: the use-after-return cell (700096 on A') off the three GOT / shadow-cell words (663568, 663656, 700088),
   by computation *)
Lemma vt_uarc : 4096 <= as_uar_cell TA /\ as_uar_cell TA + 4 <= kLowMemEnd /\
  (as_uar_cell TA + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell TA) /\
  (as_uar_cell TA + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell TA) /\
  (as_uar_cell TA + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell TA).
Proof.
assert (E : as_uar_cell TA = 700096) by (vm_compute; reflexivity).
assert (E0 : VAL (A_OBJ 0) = 663568) by (vm_compute; reflexivity).
assert (E1 : VAL (A_OBJ 1) = 663656) by (vm_compute; reflexivity).
assert (E12 : VAL (A_OBJ 12) = 700088) by (vm_compute; reflexivity).
rewrite E, E0, E1, E12. unfold kLowMemEnd. lia.
Qed.
(* the image's shadow cover at ARcf (CrsTopAp.v's crs_Ap_img_shadow, at this file's relation) *)
Lemma vt_imgvis : forall ly S Hp W mem md a, vt_ARA ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HAR _] Ha.
exact (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover SEGS TA AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow
  IMG_LO IMG_TOP AImgShadowVis.tfib_img_shadow_cover
  (AImgShadowVis.tfib_zsh_incl TA (AF0m.ts_zsh _ AD2l.TfibB_syms))
  (AImgShadowVis.tfib_const_shadow_incl TA (AF0m.ts_const _ AD2l.TfibB_syms))
  ly S Hp W mem md a HAR Ha).
Qed.
Lemma vt_pst : forall a, Exists (in_zr a) prh_pst ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TA) /\ ~ (as_errno TA <= a < as_errno TA + 4).
Proof. intros a Ha. exact (conj (S1ImgA.pst_in_img_A a Ha) (CrsWitAp.crs_wit_pal_pst_static_A' a Ha)). Qed.
Lemma vt_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TA).
Proof.
rewrite (AF0m.ts_zsh _ AD2l.TfibB_syms).
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) AF0m.Tfib_zero_shadow = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. exact (conj H1 H2).
Qed.
(* the string arm's frame budget: STK_parse_string = 16560 and the least STK_parse_value is 16880 *)
Lemma vt_stk_str : forall d, STK_parse_string + 176 <= STK_parse_value d.
Proof.
intros d. assert (Es : STK_parse_string = 16560) by (vm_compute; reflexivity).
unfold STK_parse_value. rewrite VrdArmLCWit.vrd_img_leaf_exact, VrdArmLCWit.vrd_img_fr_pv_exact,
  VrdArmLCWit.vrd_img_fr_pi_exact, Es, Nat2Z.inj_succ.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)). lia.
Qed.

(* ---- the literal arm's keyword bytes at A': the three .rodata strings (136288 "true", 136320 "false", 136352
   "null", each 32-aligned with zero fill), decided by YGcallRoStr's checks over AF0m's tables (S8aWord.v's
   ev_lit_img / ev_lit_cstr route), and the fill bytes up to the granule end ---- *)
Definition vt_slack_A (b : Z) : list Z := if b =? 102 then [0; 0] else [0; 0; 0].
(* a read-only image byte reads the rom at EVERY state: the world's map is off the segments (w_Hoff), so the
   restricted memory is None there and mbyte falls back to the rom. This is what reads the slack: its bytes are
   asan global redzones, owned statics, so arodata_okP says nothing of them, but they are rom bytes. *)
Definition vt_rom_bytes (a : Z) (l : list Z) : bool :=
  forallb (fun j => YAkMemnorm.ro_addr SEGS (Z_to_bv 64 (a + Z.of_nat j)) &&
                    match seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat j)) with
                    | Some x => bv_unsigned x =? nth j l 0 | None => false end) (seq 0 (length l)).
Lemma vt_rom_bytes_ok : forall a l, vt_rom_bytes a l = true ->
  forall (W : world SEGS) mem j, YAkMemnorm.memnorm SEGS mem -> (j < length l)%nat ->
  aview SEGS (w_H W) mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros a l H W mem j HMN Hj. unfold vt_rom_bytes in H. rewrite forallb_forall in H.
assert (Hin : In j (seq 0 (length l))) by (apply in_seq; lia).
specialize (H j Hin). apply andb_true_iff in H as [Hro H].
destruct (seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat j))) as [x|] eqn:Er; [|discriminate].
apply Z.eqb_eq in H.
unfold aview, mbyte, mrestrict.
destruct (w_H W (Z_to_bv 64 (a + Z.of_nat j))) eqn:Eh;
  destruct (mem (Z_to_bv 64 (a + Z.of_nat j))) as [y|] eqn:Em.
- exfalso. rewrite ((proj1 HMN) _ y Em) in Hro. discriminate.
- rewrite Er, <- H. reflexivity.
- exfalso. rewrite ((proj1 HMN) _ y Em) in Hro. discriminate.
- rewrite Er, <- H. reflexivity.
Qed.
Lemma vt_kw_check : forall b, (b = 116 \/ b = 102 \/ b = 110) ->
  YGcallRoStr.ro_str_check SEGS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
    (vrd_kw_addr b) (vt_kw_cw b) = true /\
  vt_rom_bytes (vrd_kw_addr b) (vt_kw_cw b ++ 0 :: vt_slack_A b) = true.
Proof. intros b [-> | [-> | ->]]; split; vm_compute; reflexivity. Qed.
Lemma vt_kw : forall b ly' S' Hp' (W' : world SEGS) mem' md', vt_ARA ly' S' Hp' W' mem' md' ->
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PI_prog_A) (@pa_relro_hi _ A_prog_listing PI_prog_A) TA
    (aview SEGS (w_H W') mem') -> YAkMemnorm.memnorm SEGS mem' ->
  (b = 116 \/ b = 102 \/ b = 110) ->
  cstr_ok W' mem' (vrd_kw_addr b) (vt_kw_cw b) /\
  garr8 SEGS (mrestrict (w_H W') mem') (vrd_kw_addr b) (vt_kw_cw b ++ 0 :: vt_slack_A b).
Proof.
intros b ly' S' Hp' W' mem' md' HAR HRO HMN Hb. destruct (vt_kw_check b Hb) as (HC & HBY).
split.
- (* the cut's cstr_ok bounds the string's own bytes (`+ 1`, SRC-CEIL): the kit's PRH_Base.cstr_ok_ro carries
     a Theorem Labs lane's ro_cstr_x (`+ 8`) to it *)
  apply (cstr_ok_ro TA vt_ARA vt_laws _ _ ly' S' Hp' W' mem' md' HAR HRO).
  apply (YGcallRoStr.ro_str_check_ok SEGS _ _ _ _ TA _ _ HC (AF0m.ts_owned _ AD2l.TfibB_syms)
    (AF0m.ts_errno _ AD2l.TfibB_syms) (AF0m.ts_zsh _ AD2l.TfibB_syms)).
  exact (AImgShadowVis.tfib_const_shadow_incl TA (AF0m.ts_const _ AD2l.TfibB_syms)).
- apply YGcallRoStr.rostr_garr8. intros j Hj. exact (vt_rom_bytes_ok _ _ HBY W' mem' j HMN Hj).
Qed.
Lemma vt_kw_num : forall b, (b = 116 \/ b = 102 \/ b = 110) ->
  vrd_kw_addr b + Z.of_nat (length (vt_kw_cw b)) + 1 + Z.of_nat (length (vt_slack_A b)) <= 2 ^ 46 /\
  ~ In 0 (vt_kw_cw b) /\
  (- (vrd_kw_addr b + Z.of_nat (length (vt_kw_cw b)) + 1)) mod 8 <= Z.of_nat (length (vt_slack_A b)).
Proof.
intros b Hb.
assert (H : (vrd_kw_addr b + Z.of_nat (length (vt_kw_cw b)) + 1 + Z.of_nat (length (vt_slack_A b)) <=? 2 ^ 46) = true /\
            negb (existsb (Z.eqb 0) (vt_kw_cw b)) = true /\
            ((- (vrd_kw_addr b + Z.of_nat (length (vt_kw_cw b)) + 1)) mod 8 <=? Z.of_nat (length (vt_slack_A b))) = true)
  by (destruct Hb as [-> | [-> | ->]]; vm_compute; repeat split).
destruct H as (H1 & H2 & H3).
split; [exact (proj1 (Z.leb_le _ _) H1)|]. split; [|exact (proj1 (Z.leb_le _ _) H3)].
intros Hin. apply negb_true_iff in H2.
assert (He : existsb (Z.eqb 0) (vt_kw_cw b) = true)
  by (apply existsb_exists; exists 0; split; [exact Hin | apply Z.eqb_refl]).
congruence.
Qed.

(* ---- fuzz_realloc's static set at A' (FuzzReallocAp.v Section f / top, at PST := FuzzReallocAp.ra_cells, the five
   statics the walk writes): PST_sub, PST_own_out and PST_most_out are range inclusions / exclusions decided by
   vm_compute (S1ImgCheck.pst_allb); PST_ok, PST_errno, MOST_ok and OWN_ok are vt_pst at a byte of prh_pst. The method
   of a Theorem Labs lane's allocator tops (a working branch 90ea33abfff6, lib/A/Prog/AllocTopsA102.v at_pst_sub /
   at_own_out / at_most_out), restated here at vt_pst ---- *)
Definition vt_mem_b (a : Z) (P : list (Z * Z)) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) P.
Lemma vt_mem_b_sound : forall a P, vt_mem_b a P = true -> Exists (in_zr a) P.
Proof.
intros a P H. unfold vt_mem_b in H. apply existsb_exists in H as [r [Hr Hb]].
apply Exists_exists. exists r. split; [exact Hr|]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold in_zr. lia.
Qed.
Lemma vt_mem_b_complete : forall a P, Exists (in_zr a) P -> vt_mem_b a P = true.
Proof.
intros a P H. apply Exists_exists in H as [r [Hr Ha]]. unfold vt_mem_b. apply existsb_exists.
exists r. split; [exact Hr|]. unfold in_zr in Ha. apply andb_true_intro.
split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
(* every byte of P is a byte of Q *)
Lemma vt_sub_ok : forall P Q, S1ImgCheck.pst_allb (fun a => vt_mem_b a Q) P = true ->
  forall a, Exists (in_zr a) P -> Exists (in_zr a) Q.
Proof. intros P Q H a Ha. apply vt_mem_b_sound. exact (S1ImgCheck.pst_allb_sound _ _ a H Ha). Qed.
(* no byte of P is a byte of Q *)
Lemma vt_out_ok : forall P Q, S1ImgCheck.pst_allb (fun a => negb (vt_mem_b a Q)) P = true ->
  forall a, Exists (in_zr a) P -> ~ Exists (in_zr a) Q.
Proof.
intros P Q H a Ha HQ. pose proof (S1ImgCheck.pst_allb_sound _ _ a H Ha) as Hb. cbv beta in Hb.
rewrite (vt_mem_b_complete a Q HQ) in Hb. discriminate.
Qed.
(* PST_sub: the walk's static set lies in the kit's prh_pst *)
Lemma vt_ra_sub : forall a, Exists (in_zr a) FuzzReallocAp.ra_cells -> Exists (in_zr a) prh_pst.
Proof. apply vt_sub_ok. vm_compute. reflexivity. Qed.
(* PST_ok / PST_errno: vt_pst through vt_ra_sub *)
Lemma vt_ra_pst_ok : forall a, Exists (in_zr a) FuzzReallocAp.ra_cells ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TA).
Proof. intros a Ha. destruct (vt_pst a (vt_ra_sub a Ha)) as (H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma vt_ra_pst_errno : forall a, Exists (in_zr a) FuzzReallocAp.ra_cells -> ~ (as_errno TA <= a < as_errno TA + 4).
Proof. intros a Ha. exact (proj2 (proj2 (vt_pst a (vt_ra_sub a Ha)))). Qed.
(* PST_aro: no byte of the walk's static set is a byte the call memory's arodata_ok_cf covers. Each covered byte is a
   RELRO byte or a report read inside a non-writable segment (CfAroPresetA.ro_reads_nw_preset_A), so a read-only image
   byte, and no byte of prh_pst is read-only (S1ImgA.pst_not_ro_A) *)
Lemma vt_ra_pst_aro : forall a, YG0dcf.aro_addr_cf a -> ~ Exists (in_zr a) FuzzReallocAp.ra_cells.
Proof.
intros a Ha Hx. apply (S1ImgA.pst_not_ro_A a (vt_ra_sub a Hx)). destruct Ha as [Ha | Ha].
- right. unfold PAImg_prog.A_prog_relro_lo, PAImg_prog.A_prog_relro_hi.
  cbv [cf_relro_lo cf_relro_hi CfImgA.CfImg_A] in Ha. exact Ha.
- left. pose proof CfAroPresetA.ro_reads_nw_preset_A as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite Forall_forall in RONW.
  apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.
(* RELRO_EQ: CfImg_A's RELRO range is the listing's, by computation *)
Lemma vt_relro_eq : @cf_relro_lo CfImgA.CfImg_A = @pa_relro_lo _ A_prog_listing PI_prog_A /\
  @cf_relro_hi CfImgA.CfImg_A = @pa_relro_hi _ A_prog_listing PI_prog_A.
Proof. split; vm_compute; reflexivity. Qed.
(* MOST_ok / OWN_ok: g_most's eight bytes (A_OBJ 14) and g_own_ran_out's one byte (A_OBJ 13) are bytes of prh_pst *)
Lemma vt_ra_most_ok : forall o, 0 <= o < 8 ->
  (in_img SEGS (A_prog_val (A_OBJ 14) + o)) /\ (~ Exists (in_zr (A_prog_val (A_OBJ 14) + o)) (as_owned_static TA)) /\
  (~ (as_errno TA <= A_prog_val (A_OBJ 14) + o < as_errno TA + 4)).
Proof.
intros o Ho. apply vt_pst. apply (vt_sub_ok [(A_prog_val (A_OBJ 14), 8)]); [vm_compute; reflexivity|].
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma vt_ra_own_ok : (in_img SEGS (A_prog_val (A_OBJ 13))) /\
  (~ Exists (in_zr (A_prog_val (A_OBJ 13))) (as_owned_static TA)) /\
  (~ (as_errno TA <= A_prog_val (A_OBJ 13) < as_errno TA + 4)).
Proof.
apply vt_pst. apply (vt_sub_ok [(A_prog_val (A_OBJ 13), 1)]); [vm_compute; reflexivity|].
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* PST_own_out / PST_most_out: the walk's static set holds neither g_own_ran_out nor g_most *)
Lemma vt_ra_own_out : ~ Exists (in_zr (A_prog_val (A_OBJ 13))) FuzzReallocAp.ra_cells.
Proof.
apply (vt_out_ok [(A_prog_val (A_OBJ 13), 1)]); [vm_compute; reflexivity|].
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma vt_ra_most_out : forall o, 0 <= o < 8 -> ~ Exists (in_zr (A_prog_val (A_OBJ 14) + o)) FuzzReallocAp.ra_cells.
Proof.
intros o Ho. apply (vt_out_ok [(A_prog_val (A_OBJ 14), 8)]); [vm_compute; reflexivity|].
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* CF_unpoison / CF_poison: CfImg_A's two shadow-call targets are the listing's entries, by computation *)
Lemma vt_cf_unpoison :
  @cf_pc_unpoison CfImgA.CfImg_A = @pa_sigma _ A_prog_listing PI_prog_A AS___asan_unpoison_memory_region.
Proof. vm_compute. reflexivity. Qed.
Lemma vt_cf_poison :
  @cf_pc_poison CfImgA.CfImg_A = @pa_sigma _ A_prog_listing PI_prog_A AS___asan_poison_memory_region.
Proof. vm_compute. reflexivity. Qed.

End real.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. THE TWO TOP THEOREMS, by DESCENDING induction on the nesting d from the depth bound (the released              *)
(*    lib/Prog/ParseUnit.v's shape): parse_value holds vacuously beyond MAXD (VrdILoop.vrd_pv_beyond: rd_pre bounds   *)
(*    d); parse_items at d from parse_value at S d (VrdILoop.vrd_items_at_steps); parse_value at d from parse_items at *)
(*    d (vrd_value_at above). Every Section hypothesis of the chain is discharged at the instance by name, and the    *)
(*    callee texts by their walks; the allocator's runtime wrappers are named below.                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section top.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance PRH_Img.prh_img_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Notation CP := CfParamsPreset.CfParams_preset.
#[local] Notation RLA := (@prh_room_live_a8 CfParamsPreset.CfParams_preset).
#[local] Notation TA := AD2l.TfibB.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).

(* the caller's context list and the cursor set CW, fixed for the whole induction (the callee texts are needed at these
   only) *)
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
(* ---- THE NAMED HYPOTHESES LEFT ---- *)
(* The allocator's runtime wrappers at the instance, at every float state, in the forms the callee walks take: realloc's
   keep row at every ghost set and headroom (YGcfInstReallocKKeep.v), free's row under the re-hide and malloc's row,
   each with the memnorm keep at the leaf (YGcfMallocComposeKeep.v). *)
Hypothesis AREAL_cf : forall (fxA : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fxA) SEGS TA Hp
    (@pa_sigma _ A_prog_listing PI_prog_A AS___wrap_realloc) k.
Hypothesis AMALLOC : forall fxA : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fxA) SEGS TA.
Hypothesis AFREE : forall fxA : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fxA) SEGS TA.
(* fuzz_free's text at the instance: FuzzFree.fuzz_free_holds (its relation ARcfx is vt_ARA's body) at AFREE, with
   AUNPOISON := CfPoison102.preset_aunpoison_cf102, the image binding palib_A, the statics' facts
   CrsWitAp.crs_wit_pal_pst_static_A' and the symbol binding TfibB_syms *)
Lemma vt_fuzz_free : forall fxP : YK11.FPState, tfuzz_free_specX (fx := fxP) (RL := RLA) TA vt_ARA SK.
Proof.
intros fxP.
exact (FuzzFree.fuzz_free_holds (fx := fxP) TA (AFREE fxP)
  (CfPoison102.preset_aunpoison_cf102 (fx := fxP) TA (YG0lawscf.AR_laws_ok_cf AB1v.tfibsegs TA) AD2l.TfibB_syms)
  PALibA.palib_A CrsWitAp.crs_wit_pal_pst_static_A' AD2l.TfibB_syms).
Qed.

(* the checked memset's row at A' (S6ImgWit.s6w_aim's argument: a Theorem Labs lane's PRowSet row for __asan_memset, whose
   entry the listing's pc of AS___asan_memset is, by vm_compute on the closed term) *)
Lemma vt_aim : forall fx' : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx') SEGS TA vt_ARA OSet (@pa_sigma _ A_prog_listing PI_prog_A AS___asan_memset).
Proof.
intros fx'.
assert (E : @pa_sigma _ A_prog_listing PI_prog_A AS___asan_memset = 0x52880)
  by (cbn [pa_sigma PI_prog_A]; lazymatch goal with |- A_prog_sigma AS___asan_memset = _ => vm_compute; reflexivity end).
rewrite E. exact (PRowSet.prow_asan_memset_xm_A_lit (fx := fx') TA vt_ARA cf_head vt_laws AD2l.TfibB_syms).
Qed.

(* the checked memcpy's row at A' (a Theorem Labs lane's PRowCpy row for __asan_memcpy; the listing's pc of
   AS___asan_memcpy is the row's pc_asan_memcpy (as_code TfibB), by vm_compute on the closed terms) *)
Lemma vt_aim_cpy : forall fx' : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx') SEGS TA vt_ARA OCpy (@pa_sigma _ A_prog_listing PI_prog_A AS___asan_memcpy).
Proof.
intros fx'.
assert (E : @pa_sigma _ A_prog_listing PI_prog_A AS___asan_memcpy = pc_asan_memcpy (as_code TA))
  by (cbn [pa_sigma PI_prog_A];
      lazymatch goal with |- A_prog_sigma AS___asan_memcpy = _ => vm_compute; reflexivity end).
rewrite E. exact (PRowCpy.prow_asan_memcpy_xm_A (fx := fx') TA vt_ARA cf_head vt_laws AD2l.TfibB_syms).
Qed.

(* ---- THE CALLEE TEXTS AT THE INSTANCE ---- *)
(* fuzz_malloc's text: FuzzMalloc.fuzz_malloc_holds (its relation ARcfx is vt_ARA's body) at AMALLOC, with
   APOISON := CfPoison102.preset_apoison_cf102, the image binding palib_A, the statics' facts
   CrsWitAp.crs_wit_pal_pst_static_A' and the symbol binding TfibB_syms *)
Lemma vt_fuzz_malloc : forall fxM : YK11.FPState, tfuzz_malloc_specX (fx := fxM) (RL := RLA) TA vt_ARA SK.
Proof.
intros fxM.
exact (FuzzMalloc.fuzz_malloc_holds (fx := fxM) (SK := SK) TA PALibA.palib_A CrsWitAp.crs_wit_pal_pst_static_A'
  (AMALLOC fxM)
  (CfPoison102.preset_apoison_cf102 (fx := fxM) TA (YG0lawscf.AR_laws_ok_cf AB1v.tfibsegs TA) AD2l.TfibB_syms)
  AD2l.TfibB_syms).
Qed.

(* fuzz_realloc's text (grow's callee): FuzzReallocAp.fuzz_realloc_holds_Ap at B := TfibB, its relation ARcfx being
   vt_ARA's body. Its Section hypotheses at the instance: PAL palib_A; PST := ra_cells, PST_ok / PST_errno / MOST_ok /
   OWN_ok / PST_sub / PST_own_out / PST_most_out / PST_aro by Section real's vt_ra_*, PST_cells by ra_cell_in; the
   RELRO image rows RELRO_SEG / ERRNO_RELRO / RELRO_TOP / RO_READS_NW by CfAroPresetA and RELRO_EQ by vt_relro_eq;
   FMALLOC vt_fuzz_malloc; AUNPOISON / APOISON CfPoison102.preset_aunpoison_cf102 / preset_apoison_cf102; AREAL_cf the
   named hypothesis above; CF_unpoison / CF_poison vt_cf_unpoison / vt_cf_poison (by computation) *)
Lemma vt_fuzz_realloc : forall fxR : YK11.FPState, tfuzz_realloc_specX (fx := fxR) (RL := RLA) TA vt_ARA SK.
Proof.
intros fxR.
exact (FuzzReallocAp.fuzz_realloc_holds_Ap (fx := fxR) (ci := CfImgA.CfImg_A) (SK := SK) TA PALibA.palib_A
  FuzzReallocAp.ra_cells vt_ra_pst_ok FuzzReallocAp.ra_cell_in vt_ra_pst_errno vt_ra_most_ok
  CfAroPresetA.relro_seg_preset_A (CfAroPresetA.errno_relro_preset_A TA AD2l.TfibB_syms)
  CfAroPresetA.relro_top_preset_A CfAroPresetA.ro_reads_nw_preset_A vt_relro_eq vt_ra_pst_aro
  vt_ra_own_ok vt_ra_sub vt_ra_own_out vt_ra_most_out (vt_fuzz_malloc fxR)
  (CfPoison102.preset_aunpoison_cf102 (fx := fxR) TA (YG0lawscf.AR_laws_ok_cf AB1v.tfibsegs TA) AD2l.TfibB_syms)
  (CfPoison102.preset_apoison_cf102 (fx := fxR) TA (YG0lawscf.AR_laws_ok_cf AB1v.tfibsegs TA) AD2l.TfibB_syms)
  (AREAL_cf fxR) vt_cf_unpoison vt_cf_poison).
Qed.

(* hex4's text, one of parse_string's two \u-stretch callees: S3_Hex4Bridge.hex4_holds, Section hypotheses LAWS / TL /
   HW only *)
Lemma vt_hex4 : forall fxH : YK11.FPState, thex4_specX (fx := fxH) (RL := RLA) TA vt_ARA SK.
Proof.
intros fxH.
exact (S3_Hex4Bridge.hex4_holds (fx := fxH) (cp := CP) (RL := RLA) TA vt_ARA SK vt_laws PALibA.palib_A
  CfParamsPreset.preset_head_wide).
Qed.
(* put_utf8's text, parse_string's other \u-stretch callee: ExUtf8WA.pb_put_utf8X_Ap, Section hypotheses LAWS / TL
   (PALibCore, YC1fP.palib_core of PALibA.palib_A) only *)
Lemma vt_putu : forall fxU : YK11.FPState, tput_utf8_specX (fx := fxU) (RL := RLA) TA vt_ARA SK.
Proof.
intros fxU.
exact (ExUtf8WA.pb_put_utf8X_Ap (fx := fxU) (RL := RLA) TA vt_ARA SK vt_laws
  (palib_core (PI := PI_prog_A) TA PALibA.palib_A)).
Qed.

(* parse_string's text: S4_PsTop.ps_K0_of_counts at the instance; its Section hypotheses: LAWS vt_laws, TL palib_A,
   PST_ok vt_pst_ok, HW preset_head_wide, the callee texts HMALLOC vt_fuzz_malloc, HFREE vt_fuzz_free, HHEX4 vt_hex4,
   HPUTU vt_putu, ZSA vt_zsa and IMGV vt_imgvis *)
Lemma vt_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TA).
Proof. intros a Ha. destruct (vt_pst a Ha) as (H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma vt_zsa : forall q m, In (q, m) (as_zero_shadow TA) -> q mod 8 = 0 /\ m mod 8 = 0.
Proof. intros q m Hin. pose proof vt_zsal as H. rewrite Forall_forall in H. exact (H (q, m) Hin). Qed.
Lemma vt_parse_string : forall fxP : YK11.FPState,
  tparse_string_specX (fx := fxP) (RL := RLA) TA vt_ARA SK CTX0 CW.
Proof.
intros fxP.
exact (S4_PsTop.ps_K0_of_counts (fx := fxP) (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLA) TA vt_ARA SK CTX0 CW
  vt_laws PALibA.palib_A vt_pst_ok CfParamsPreset.preset_head_wide (vt_fuzz_malloc fxP) (vt_fuzz_free fxP)
  (vt_hex4 fxP) (vt_putu fxP) vt_zsa vt_imgvis).
Qed.

(* grow's text: PwGrow.grow_holds_Aprime at the placed relation (vt_ARA's body), with its callee text
   HREALLOC := vt_fuzz_realloc *)
Lemma vt_grow : forall fxg : YK11.FPState, tgrow_specX (fx := fxg) (RL := RLA) TA vt_ARA SK CTX0.
Proof.
intros fxg.
exact (PwGrow.grow_holds_Aprime (fx := fxg) (ci := CfImgA.CfImg_A) (RL := RLA) SK (vt_fuzz_realloc fxg) CTX0).
Qed.

(* literal's text: literal_bridge.literal_holds (in the cut) at the instance; its call texts are the runtime rows of
   __wrap_strlen (PSstrRo.ps_strlen_xrom_xs_A, at CfImgA's cf_pc_strlen) and __wrap_bcmp (PRowCmp.pr_bcmp_xm_A_pc, at
   pc_wrap_bcmp (as_code TfibB)), whose pcs are the listing's by vm_compute on the closed terms *)
Lemma vt_astrlen : forall fx' : YK11.FPState,
  YGcallMxmn.astrlen_realizes_xrom (fx := fx') SEGS TA vt_ARA (@pa_relro_lo _ A_prog_listing PI_prog_A)
    (@pa_relro_hi _ A_prog_listing PI_prog_A) (@pa_sigma _ A_prog_listing PI_prog_A AS___wrap_strlen).
Proof.
intros fx'.
assert (E : @pa_sigma _ A_prog_listing PI_prog_A AS___wrap_strlen = @cf_pc_strlen CfImgA.CfImg_A)
  by (cbn [pa_sigma PI_prog_A];
      lazymatch goal with |- A_prog_sigma AS___wrap_strlen = _ => vm_compute; reflexivity end).
rewrite E. exact (PSstrRo.ps_strlen_xrom_xs_A (fx := fx') (cp := CP) TA AD2l.TfibB_syms _ _).
Qed.
Lemma vt_abcmp : forall fx' : YK11.FPState,
  YGcallMxmn.abcmp_realizes_xm (fx := fx') SEGS TA vt_ARA (@pa_sigma _ A_prog_listing PI_prog_A AS___wrap_bcmp).
Proof.
intros fx'.
assert (E : @pa_sigma _ A_prog_listing PI_prog_A AS___wrap_bcmp = pc_wrap_bcmp (as_code TA))
  by (cbn [pa_sigma PI_prog_A];
      lazymatch goal with |- A_prog_sigma AS___wrap_bcmp = _ => vm_compute; reflexivity end).
rewrite E. exact (PRowCmp.pr_bcmp_xm_A_pc (fx := fx') TA vt_ARA cf_head vt_laws AD2l.TfibB_syms).
Qed.
Lemma vt_literal : forall fxL : YK11.FPState, tliteral_specX (fx := fxL) (RL := RLA) TA vt_ARA SK.
Proof.
intros fxL.
exact (literal_bridge.literal_holds (fx := fxL) SK TA vt_ARA vt_laws PALibA.palib_A
  (vt_astrlen fxL) (vt_abcmp fxL)).
Qed.
(* parse_value's frame at A' *)
Lemma vt_pv_frame : 176 <= pi_frame F_parse_value.
Proof. vm_compute. congruence. Qed.
(* the number arm at the instance: VrdNumA.vrd_num_a_P with each Section hypothesis discharged by name. The strtod
   row's image facts B_tp / B_errno / B_errno_own are a Theorem Labs lane's strtod_row_sat.strtod_sat_tp_A / _errno_A /
   _owned_A, computed at TfibB's fields and carried by TfibSyms' ts_tp / ts_errno / ts_owned; PST_ERRNO is vt_pst's
   third conjunct; the GOT canary const cell is AE22.canary_cell_in (its address / value are strtod's GOT guard by
   conversion of the closed constants) *)
Lemma vt_num_arm : forall fx : YK11.FPState, vrd_num_a_stmt_P (fx := fx) (RL := RLA) TA vt_ARA SK.
Proof.
intros fx.
refine (VrdNumA.vrd_num_a_P (fx := fx) (ci := CfImgA.CfImg_A) (cp := CP) (PIm := PRH_Img.prh_img_A) (RL := RLA)
  TA vt_ARA SK vt_laws S1ImgA.pst_in_img_A (vt_aim_cpy fx) _ _ _ eq_refl vt_zsal vt_imgvis S1ImgA.pst_not_ro_A
  CfParamsPreset.preset_head_wide vt_pv_frame (fun a Ha => proj2 (proj2 (vt_pst a Ha))) _ vrd_loop_HI_head_preset).
- rewrite (AF0m.ts_tp TA AD2l.TfibB_syms). exact strtod_row_sat.strtod_sat_tp_A.
- rewrite (AF0m.ts_errno TA AD2l.TfibB_syms). exact strtod_row_sat.strtod_sat_errno_A.
- intros a Ha. rewrite (AF0m.ts_owned TA AD2l.TfibB_syms). rewrite (AF0m.ts_errno TA AD2l.TfibB_syms) in Ha.
  exact (strtod_row_sat.strtod_sat_owned_A a Ha).
- intros ly. exact (AE22.canary_cell_in TA AD2l.TfibB_syms ly).
Qed.

(* parse_items at d, from parse_value at S d at every float state *)
Lemma vt_items_step : forall (fx : YK11.FPState) (d : nat),
  (forall (CTX' : list (list Z)) (fx' : YK11.FPState),
     tparse_value_specX (fx := fx') (RL := RLA) TA vt_ARA SK (S d) CTX' CTX0 CW) ->
  forall CTX : list (list Z), tparse_items_specX (fx := fx) (RL := RLA) TA vt_ARA SK d CTX CTX0 CW.
Proof.
intros fx d HV.
exact (vrd_items_at_steps (fx := fx) TA vt_ARA SK vt_laws PALibA.palib_A vrd_loop_H_img_A CTX0 CW
  vt_grow CfParamsPreset.preset_head_wide S1ImgA.pst_in_img_A vrd_loop_HI_head_preset
  vrd_loop_H_s0_A vrd_loop_H_s0g_A eq_refl vt_zsal vt_imgvis S1ImgA.pst_not_ro_A vrd_loop_H_s0s_A
  vt_fuzz_free vrd_loop_H_ffret_A vt_parse_string
  vt_aim d HV).
Qed.

(* parse_value at d, from parse_items at d *)
Lemma vt_value_step : forall (fx : YK11.FPState) (d : nat),
  (forall CTX' : list (list Z), tparse_items_specX (fx := fx) (RL := RLA) TA vt_ARA SK d CTX' CTX0 CW) ->
  forall CTX : list (list Z), tparse_value_specX (fx := fx) (RL := RLA) TA vt_ARA SK d CTX CTX0 CW.
Proof.
intros fx d HI.
exact (vrd_value_at (fx := fx) TA vt_ARA SK vt_laws PALibA.palib_A vt_uarc vt_ownlow vt_fsi AD2l.TfibB_syms eq_refl
  AD2l.TfibB_ok vt_imgvis vt_pst CfParamsPreset.preset_head_wide vrd_loop_HI_head_preset vt_asfx vt_fflx vt_fpres
  vt_sfx vrd_loop_H_s0s_A vrd_loop_H_s0_A vt_stk_str VrdArmLCWit.vrd_img_stk_items_drop
  VrdArmLCWit.vrd_img_stk_items_nonneg VrdArmLCWit.vrd_img_stk_literal_drop VrdArmLCWit.vrd_img_stk_literal_nonneg
  vt_slack_A vt_kw vt_kw_num CTX0 CW (vt_parse_string fx) (vt_literal fx) (vt_fuzz_malloc fx)
  (vt_num_arm fx) d HI).
Qed.

(* the descending induction: k bounds the distance S MAXD - d *)
Lemma vt_value_desc : forall (k d : nat), (S PjGrammar.MAXD - d <= k)%nat ->
  forall (fx : YK11.FPState) (CTX : list (list Z)),
  tparse_value_specX (fx := fx) (RL := RLA) TA vt_ARA SK d CTX CTX0 CW.
Proof.
intros k. induction k as [|k IH]; intros d Hd fx CTX.
- exact (vrd_pv_beyond (ci := CfImgA.CfImg_A) (cp := CP) (PIm := PRH_Img.prh_img_A) (RL := RLA) TA vt_ARA SK CTX0 CW
    d ltac:(lia) CTX fx).
- destruct (Nat.lt_ge_cases PjGrammar.MAXD d) as [Hlt | Hle].
  + exact (vrd_pv_beyond (ci := CfImgA.CfImg_A) (cp := CP) (PIm := PRH_Img.prh_img_A) (RL := RLA) TA vt_ARA SK CTX0
      CW d Hlt CTX fx).
  + apply (vt_value_step fx d). apply (vt_items_step fx d).
    intros CTX' fx'. exact (IH (S d) ltac:(lia) fx' CTX').
Qed.

(* ==== THE TWO TOP THEOREMS ==== *)
Theorem vrd_parse_value_holds : forall (fx : YK11.FPState) (d : nat) (CTX : list (list Z)),
  @tparse_value_specX fx rc CfImgA.CfImg_A CP PRH_Img.prh_img_A RLA A_prog_listing PI_prog_A TA vt_ARA SK
    d CTX CTX0 CW.
Proof.
intros fx d CTX.
exact (vt_value_desc (S PjGrammar.MAXD - d) d (le_n _) fx CTX).
Qed.

Theorem vrd_parse_items_holds : forall (fx : YK11.FPState) (d : nat) (CTX : list (list Z)),
  @tparse_items_specX fx rc CfImgA.CfImg_A CP PRH_Img.prh_img_A RLA A_prog_listing PI_prog_A TA vt_ARA SK
    d CTX CTX0 CW.
Proof.
intros fx d CTX.
apply (vt_items_step fx d). intros CTX' fx'. exact (vrd_parse_value_holds fx' (S d) CTX').
Qed.

End top.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. NOT VACUOUS: the top theorems' fpre is stated at vt_ARA, that is combine6's ARcf (YG0ncf.v 6748bee76f02, whose  *)
(*    abudget_ok_cf carries cls1_band_vis_cf: class 1's shadow band is visible) with the error buffers placed.       *)
(*    vt_ARA_init: vt_ARA holds at the run's initial state at image A', from the process-entry facts of the start-up  *)
(*    (AD1f.tfib_AR at the start-up layout AD1g.ly0 and AD1d.tfib_AI, both at AD2i.W1's world; the first premises     *)
(*    below are tfib_AR's, at B := TfibB, the last three the start-up rows the conversion takes), through the        *)
(*    conversion YGcfNilInit.ARcf_nil_init (it exposes the band) and YG0ncf.xs_placed_of_ARcf. The world is the one   *)
(*    ARcf_nil_init returns.                                                                                         *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section init.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance PRH_Img.prh_img_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Notation TA := AD2l.TfibB.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).

(* the allocator switch's image rows at CfImg_A / TfibB (YG0ncf.v, cf layer field rounds 2-3): the exhausted byte's
   offset, the errbuf object's ownership by computation over TfibB's owned statics, its distance from the internal
   allocator (CfIalApartPreset), and Printf's two cells likewise *)
Lemma vt_errb_rows : YGcfImgRows.EXH_OFF_t /\ YG0ncf.errb_obj_owned_t TA /\ YG0ncf.errb_ial_apart_t TA.
Proof.
split; [reflexivity|]. split; [|exact (CfIalApartPreset.errb_ial_apart_A TA AD2l.TfibB_syms)].
intros a Ha. rewrite (AF0m.ts_owned TA AD2l.TfibB_syms).
apply (vt_sub_ok [(@cf_errbuf_obj CfImgA.CfImg_A, 56)]); [vm_compute; reflexivity|].
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma vt_pf_rows : YG0ncf.pf_cells_owned_t TA.
Proof.
split; [|exact (CfIalApartPreset.pf_ial_apart_A TA AD2l.TfibB_syms)].
intros a Ha. rewrite (AF0m.ts_owned TA AD2l.TfibB_syms), (AF0m.ts_inst TA AD2l.TfibB_syms).
split.
- destruct Ha as [Ha | Ha].
  + apply (vt_sub_ok [(@cf_toolname_cell CfImgA.CfImg_A, 8)]); [vm_compute; reflexivity|].
    apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (vt_sub_ok [(@cf_pfcb_cell CfImgA.CfImg_A, 8)]); [vm_compute; reflexivity|].
    apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- cbn [cf_toolname_cell cf_pfcb_cell CfImgA.CfImg_A] in Ha. unfold AF0m.TFIB_INST, YG0ncf.kInstObjSize. lia.
Qed.

(* the allocator switch YGcfNilInit.ARcf_nil_init takes, beside AR and AI at the start-up world, the start-up rows of
   the cf layer (field rounds 2-3): the model's lazy and no-access maps lie in its maps, and the start witnesses of
   the RegionInfo / errbuf cells and of Printf's two cells at the start-up layout and world. They are premises here,
   facts of the start-up state; the image rows are vt_errb_rows / vt_pf_rows. The layout is the start-up layout
   AD1g.ly0, at which AD1f.tfib_AR gives AR. *)
Lemma vt_ARA_init : forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
  (Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) (Hve : valid_envp (in_envp inp))
  (Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp))
  (h : nat) (ch : YK09.APC.acs) (E : YK0c.AX2.env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
  (Hch : AB01.HS_tfib h = Some ch)
  (HC : YA0e.APSG.cs_ok AB1h.TSEGS AB12.TFIB YA02.LIMIT (YA02.TOP sp)
     (YA02.SINV0 AB1h.TSEGS AB1h.TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
     (YA02.argH0 AB1h.TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL
     model),
  (forall n, (n < YA01.NX0G)%nat -> YK0c.AX2.ev E n =
     YK0c.AX2.ev (YA02.E0 AB1h.TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 AB1h.TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
     FULL a = wrap_mem AB1h.TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  (forall x, YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true ->
     YK0g.covered (vm_maps (m_vmmaps model)) x = true) ->
  YG0ncf.start_cells_cf AB1h.TSEGS TA (AD1g.ly0 ch E model) init_state
    (AD2i.W1 sp rdraw inp Hsp Hva ch E model
       (PWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC)) FULL ->
  YG0ncf.start_pf_cf AB1h.TSEGS TA (AD1g.ly0 ch E model)
    (AD2i.W1 sp rdraw inp Hsp Hva ch E model
       (PWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC)) FULL ->
  exists ly (W : world SEGS), vt_ARA ly init_state [] W FULL model.
Proof.
intros sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM Hceil Hlazy Hcells Hpf.
assert (HAR : AR AB1h.TSEGS TA (AD1g.ly0 ch E model) init_state
  (AD2i.W1 sp rdraw inp Hsp Hva ch E model
    (PWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC)) FULL model)
  by (eapply (AD1f.tfib_AR TA AD2l.TfibB_syms); eassumption).
assert (HAI : AI AB1h.TSEGS
  (w_H (AD2i.W1 sp rdraw inp Hsp Hva ch E model
    (PWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC)))
  (w_A (AD2i.W1 sp rdraw inp Hsp Hva ch E model
    (PWorldH8.H1_H8 sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC))) model).
{ eapply AD1d.tfib_AI; first [eassumption | exact AD2l.TfibB_syms]. }
destruct (YGcfNilInit.ARcf_nil_init AB1h.TSEGS TA (AD1g.ly0 ch E model) _ FULL model HAR HAI Hlazy Hcells Hpf
  vt_errb_rows vt_pf_rows) as (W' & _ & _ & HARcf).
exists (AD1g.ly0 ch E model), W'. unfold vt_ARA. split; [exact HARcf|].
exact (YG0ncf.xs_placed_of_ARcf _ _ _ _ _ _ _ _ HARcf).
Qed.
End init.

Print Assumptions vrd_parse_value_holds.
Print Assumptions vrd_parse_items_holds.
Print Assumptions vt_ARA_init.
