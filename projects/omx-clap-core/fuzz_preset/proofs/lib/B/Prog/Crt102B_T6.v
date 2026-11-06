(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module names changed; 989 of its 1047 lines of code are new or changed and 456 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): row T6 at the re-hiding contract.
   crtB_T6's text is unchanged (CRT_B_SEG_T6 now means CRT_B_AT_C -> CRT_B_AT_L3 at the step
   relation YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf); the stretches ct6_at_M / _R / _K and the notations ATC / ATL3 are
   SRr'; the journals (AJ / AJW) are at R := YA0nH.wle' SEGS RZ_cf. same's text (tsame_specX, still plain SRr / fpostm)
   enters cb7k_call's R premise by YA0nH.SRr_SRr' and apost_base_xF_R_lift at YA0nH.wle_wle'. strcmp's rule is the
   engine's YGcallMxmn.aj_strcmp_at_xromR (the local copy ct6_aj_strcmp_at_xromR is deleted, the engine lemma
   cited, here and in Crt102B_T5_L1.v), lifted by SRr_SRr' under YSRrG.SRr'_bind. No HOS4 and no
   hull: neither callee asks either. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T6 (CRT-B-L3): the member loop, B' entry + 0x5b4 ->
   + 0x6f4 (81 instructions, fuzz_preset.c new:750-755), crtB_T6 : CRT_B_SEG_T6 (lib/A/Prog/Crt102Glue.v, the frozen
   text) at the B' instance.

   proves no function (kind: segment lemma).

   THE WALK. One pass from L3 at index i (crt_at_L3_B .. i) is
     L3 (+0x5b4) --run--> jal __wrap_strcmp (back.keys[i], doc->keys[i]) +0x648 --> K (+0x64c), a0 = 0
     K --run, i = at--> M (+0x6d4)
     K --run, i <> at--> jal same (&back.kids[i], &doc->kids[i]) +0x6cc --> R (+0x6d0), a0 = 1 --run--> M
     M --run--> L3 at i + 1 (i + 1 < doc->n) or C (+0x6f8)
   with crt_at_L3_B itself the state at L3, K, R and M (the loop writes no memory: only the callees change it, below sp1),
   so crt_at_L3_B IS the loop invariant (no counterexample found). The 14 UBSan branches to +0x810 and the 5 report
   branches are decided by the symbolic runner (the state's atom facts and aliases); the two compare aborts to +0x824 are
   not taken: the read-back's key i is doc's key i (Crt102Model.cm_set_member), its value too unless i = at.

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): crt_at_L3_B and crt_at_C_B carry crt_live at kb =
   prh_wk F_check_round_trip (the notation liveB) and its journal at a budget WS with wbudget [] (prh_wk
   F_check_round_trip) WS. The runs keep WS (Crt102Kit.crt_run_xw_inv / crt_run_to_xw_inv), strcmp keeps it (its
   empty-budget rule over the journal rebased by YCbqGwild.ajournal_xw_rebase, stepped back by ajournal_xw_unbase0),
   and same's call through cb7k_call hands it on packaged. ct6_live_md / ct6_side_after / ct6_live_keep read the
   journal at a budget WS (the A' twin's convention, Crt102Loops.cl_live_keep); crtB_T6's statement is unchanged.

   INPUTS OF RECORD (taken by path where named):
   - base commit cbe6d10993c2 (candidate base) (Crt102Glue.v: the frozen crt_at_L3_B / crt_at_C_B /
     CRT_B_SEG_T6 in the permutation form; Crt102Img.v; Crt102Model.v; lib/B/Prog/Crt102KitB.v: cb4_sp, cb4_ff,
     cb4_doc_home, cb4_ar0, cb4_fb, cb4_live_call, cb4_fregs_trans, cb4_ro_img; lib/A/Prog/Crt102Kit.v:
     crt102rw_fdR_frame).
   - lib/B/Prog/Crt102B_T7_kit.v blob 6eb58703733e and lib/B/Prog/Crt102B_T7_tree.v blob b95480cf94ff, BY PATH from
     commit b91538550ad (row T7's call rule cb7k_call / cb7k_ret and reader layer cb7t_str_prem /
     cb7t_garr8_at).
   - lib/B/Prog/Crt102B_T6_st.v (this row): the symbolic state ct6_ssx and ct6_entry.
   - callee texts: NAMED HYPOTHESIS ASTRCMP (owner: the libc strcmp row; discharge ps_strcmp_xrom_B, lib/AU/PSstrRo.v
     45e63604063e at commit ebb41f4e9efa, at the top where ARx is fixed) and SAME
     (the contract text tsame_specX at DOC_D); text premises HPRE, HTREE, HMN, HREAD (tcheck_round_trip_specX's own).

   NUMERALS. DERIVED: 27632 (STK_check_round_trip, by computation), 240 (A_TEXT, the engine's base atom), the return
   sites CRT_K_OFF6R_B = 0x64c / CRT_R_OFF6_B = 0x6d0 and CRT_M_OFF6_B = 0x6d4 (4 * the slot inside the function).
   LENGTH: 240 / 255 (the realignment drop), 16 / 32 / 8 (alignments), 56 / 8 (strides, struct pj), 512 / 64 (the
   class-3 frame and its shadow), 4096 (ESTACK; the bound on the function's own offsets), 2 ^ 16 / 2 ^ 30 / 2 ^ 32 /
   2 ^ 44 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (bounds). WORD: register numbers. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6_st Crt102B_T7_kit Crt102B_T7_tree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* The re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the
   zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* the loop's two exits as conditions of the symbolic state at M (+0x6d4): i + 1 < doc->n (back to L3) or not (C) *)
Definition ct6_CLT : acond := mkAC BC_LTU (SOff 53 1) (SOff 75 0).
Definition ct6_CGE : acond := mkAC BC_GEU (SOff 53 1) (SOff 75 0).
(* after the key compare (+0x64c): a0 = 0, and at = i or not *)
Definition ct6_A0 : acond := mkAC BC_EQ (SOff 42 0) (SLit 0).
Definition ct6_AEQ : acond := mkAC BC_EQ (SOff 76 0) (SOff 53 0).
Definition ct6_ANE : acond := mkAC BC_NE (SOff 76 0) (SOff 53 0).
(* after the value compare (+0x6d0): a0 <> 0 *)
Definition ct6_A1 : acond := mkAC BC_NE (SOff 42 0) (SLit 0).
Definition CRT_K_OFF6R_B : Z := 0x64c.   (* +0x64c: `bnez a0`, strcmp's return site *)
Definition CRT_R_OFF6_B : Z := 0x6d0.    (* +0x6d0: `beqz a0`, same's return site *)

Lemma ct6_U : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
intros E n v c H H1 H2. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64.
lia.
Qed.

Lemma ct6_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. apply bv_eq. change (U E (SOff n 0) = bv_unsigned (ew E n)). apply ts_U0. Qed.

(* a register of the end state of a run, as the symbolic state names it (unnormalized) *)
Ltac ct6_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.
(* a register the run did not write: its symbolic value is the current atom 32 + r *)
Ltac ct6_keep HS := lazymatch goal with |- getr _ ?rr = getr ?rg ?rr =>
  let H := fresh in ct6_reg HS rr H; rewrite H, ct6_soff0;
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let k := eval vm_compute in (n - 32)%nat in
    exact (te_cur r0 rc mo rr k eq_refl) end end.

Ltac ct6_ro := lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own');
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end.

(* ======================================================================================================== *)
(* image B' at the B instance (lib/B/PAImg_prog.v PI_prog_B, PL_prog_B) *)
Section t6w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Lemma ct6_env : forall regs rg doc' kb kd xb xd kib kid nn atv (i : nat),
  ew (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) 53 = getr rg 21 /\
  ew (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) 42 = getr rg 10 /\
  ew (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) 75 = w64 nn /\
  ew (TEB regs rg (ct6_more doc' kb kd xb xd kib kid nn atv i)) 76 = w64 atv.
Proof.
intros. set (mo := ct6_more doc' kb kd xb xd kib kid nn atv i).
split; [exact (te_cur regs rg mo 21%bv 21 eq_refl)|].
split; [exact (te_cur regs rg mo 10%bv 10 eq_refl)|].
split; [exact (te_more_lt regs rg mo 11 ltac:(lia)) | exact (te_more_lt regs rg mo 12 ltac:(lia))].
Qed.

Definition CT6_BREGS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 27]%bv.
Lemma ct6_bregs_eq : forall regs rg rg' F, crt_bregs_B (regs := regs) rg F ->
  (forall r, In r CT6_BREGS -> getr rg' r = getr rg r) -> crt_bregs_B (regs := regs) rg' F.
Proof.
intros regs rg rg' F HB HE.
pose proof (crt_bregs_B_sp HB) as R2. pose proof (crt_bregs_B_gp HB) as R3. pose proof (crt_bregs_B_tp HB) as R4.
pose proof (crt_bregs_B_s0 HB) as R8. pose proof (crt_bregs_B_s1 HB) as R9. pose proof (crt_bregs_B_s2 HB) as R18.
pose proof (crt_bregs_B_s4 HB) as R20. pose proof (crt_bregs_B_s3 HB) as R19. pose proof (crt_bregs_B_s7 HB) as R23.
pose proof (crt_bregs_B_s9 HB) as R25. pose proof (crt_bregs_B_s11 HB) as R27. clear HB.
unfold CT6_BREGS in HE.
refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
          crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
          crt_bregs_B_s11 := _ |}; rewrite HE by (cbn [In]; tauto); assumption.
Qed.
Lemma ct6_bregs_pres : forall regs rg rg' F, crt_bregs_B (regs := regs) rg F -> aregs_preserved rg rg' ->
  crt_bregs_B (regs := regs) rg' F.
Proof.
intros regs rg rg' F HB HP. apply (ct6_bregs_eq regs rg rg' F HB). intros r Hr. unfold CT6_BREGS in Hr.
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply (ts_ap rg rg' _ HP); ts_cs|]). destruct Hr.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* The re-hiding move: every journal below at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   relation of the glue's crt_live_journal and of QF *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* tcheck_round_trip_specX's premises at the entry this row reads (PRH_FnCheck.v, the text's own; Crt102Top
   discharges them) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HREAD : ck_read x = Some t.
(* THE CALLEE TEXTS, each at ANY float state.
   NAMED HYPOTHESIS ASTRCMP (owner: the libc strcmp row): the __wrap_strcmp row in its read-only-premise form WITH the memnorm
   keep (YGcallMxmn.v:898 astrcmp_realizes_xrom). The _xro form (:849) is not enough here: crt_live's last field
   (Crt102Glue.v crt_live_memnorm, `memnorm mem -> memnorm memc`) must hold again after the call, and astrcmp_realizes_xro's post
   (YGcallMxmn.v:866-873) keeps no memnorm.
   SAME: the contract text of same (PRH_FnEx.v:362 tsame_specX) at nesting DOC_D (owner: the contract kit). *)
Hypothesis ASTRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
Hypothesis SAME : forall fxk : YK11.FPState,
  @tsame_specX fxk rc CfParams_preset prh_img_B RL B_prog_listing PA B ARx SK DOC_D.
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc)
  (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
#[local] Notation L3B := (crt_at_L3_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation CB := (crt_at_C_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).

#[local] Notation ENT := (ct6_entry B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam
  peak cnt most HPRE HTREE).

(* ---- the live state with a new journal at the same memory (a read-only run): every other field is kept ---- *)
Lemma ct6_live_md : forall {lyc Sc Hpc} {Wc : world SEGS} {memc mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc}
    {WS : list (list Z)},
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc' kj' WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  liveB lyc Sc Hpc Wc memc mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc WS HL HJ HB.
exact {| crt_live_journal := ex_intro _ WS (conj HJ HB); crt_live_side := crt_live_side HL;
         crt_live_lam_perm := crt_live_lam_perm HL; crt_live_blocks_perm := crt_live_blocks_perm HL;
         crt_live_dx_apart := crt_live_dx_apart HL; crt_live_saved := crt_live_saved HL;
         crt_live_frame := crt_live_frame HL; crt_live_fspill := crt_live_fspill HL;
         crt_live_copy_open := crt_live_copy_open HL; crt_live_copy_hull := crt_live_copy_hull HL;
         crt_live_memnorm := crt_live_memnorm HL |}.
Qed.

(* ---- a tree whose root bytes are kept and present, and whose blocks are ledger blocks with their bytes kept, is the
   same tree at the new memory (pj_agreeR: bytes kept, writability from presence at the new state) ---- *)
Lemma ct6_agree : forall (Wc : world SEGS) memc ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 Lamc peakc cntc ranc {mostc ownc : Z}
    p Dp,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lamc peakc cntc SIZE_MAXZ ranc mostc ownc ->
  (forall bk, In bk Dp -> In bk Lamc) ->
  (forall y, p <= y < p + 56 -> apresent (w_H W2) mem2 y /\ aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y) ->
  (forall a k y, In (a, k) Lamc -> a <= y < a + k -> aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (pj_footR p Dp).
Proof.
intros Wc memc ly2 S2 Hp2 W2 mem2 md2 Lamc peakc cntc ranc mostc ownc p Dp HAR2 HLED2 HD Hroot Hblk y Hy.
destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
- destruct (Hroot y Hy) as (Hpr & Hv).
  split; [exact (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2 y Hv)|].
  intros _. exact (apresent_writable SEGS (w_H W2) mem2 y Hpr).
- unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
  destruct (ct6_blk B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 Lamc peakc cntc ranc b kb HAR2 HLED2 (HD _ Hb))
    as (_ & _ & _ & _ & _ & _ & _ & _ & Hpres).
  split; [exact (mbyte_of_aview SEGS (w_H Wc) (w_H W2) memc mem2 y (Hblk b kb y (HD _ Hb) Hy))|].
  intros _. exact (apresent_writable SEGS (w_H W2) mem2 y (Hpres y Hy)).
Qed.

(* ---- THE L3 FACTS ACROSS A CALL that kept the allocator state (S2 = Sc) and wrote only below sp1, given the live
   state at the new state (the caller's, per callee): the registers by callee-saving, the spills above sp1, the
   frame's shadow and the document's fake frame by the frames clause, the trees by their footprints ---- *)
Lemma ct6_L3_after : forall fxk fx' lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i
    ly2 Hp2 W2 mem2 md2 k2 regs2,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i ->
  frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
  liveB ly2 Sc Hp2 W2 mem2 md2 k2 pos (Dback ++ (saved, kw) :: Dc) Lamc peakc cntc 0 0 ->
  frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos ->
  aregs_preserved rg regs2 ->
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (forall p n j, In (p, n) (ablocks B lyc Sc) -> 0 <= j < req_size n ->
     aview SEGS (w_H W2) mem2 (p + j) = aview SEGS (w_H Wc) memc (p + j)) ->
  L3B fx' ly2 Sc Hp2 W2 mem2 md2 k2 pos Dc Dback Lamc peakc cntc regs2 ms cset saved kw i.
Proof.
intros fxk fx' lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i ly2 Hp2 W2 mem2 md2 k2 regs2
  HL3 HFZ2 HFK2 HL2 EFA HP KST KFR KBL.
pose proof (crt_at_L3_B_obj HL3) as Ht. pose proof (crt_at_L3_B_frm_zero HL3) as HFZ.
pose proof (crt_at_L3_B_fregs HL3) as HFK. pose proof (crt_at_L3_B_live HL3) as HL.
pose proof (crt_at_L3_B_bregs HL3) as HBR. pose proof (crt_at_L3_B_s5_i HL3) as R21.
pose proof (crt_at_L3_B_s8_i HL3) as R24. pose proof (crt_at_L3_B_s10_i HL3) as R26.
pose proof (crt_at_L3_B_s6_keys HL3) as R22. pose proof (crt_at_L3_B_sp_saved HL3) as SPsv.
pose proof (crt_at_L3_B_sp_shkids HL3) as SPshk. pose proof (crt_at_L3_B_sp_keys HL3) as SPkeys.
pose proof (crt_at_L3_B_sp_back HL3) as SPback. pose proof (crt_at_L3_B_sp_at HL3) as SPat.
pose proof (crt_at_L3_B_sp_kids HL3) as SPkids. pose proof (crt_at_L3_B_sp_shn HL3) as SPshn.
pose proof (crt_at_L3_B_sp_pn HL3) as SPpn. pose proof (crt_at_L3_B_doc_align HL3) as Hd8.
pose proof (crt_at_L3_B_doc_open HL3) as RAd. pose proof (crt_at_L3_B_back_open HL3) as RAb.
pose proof (crt_at_L3_B_v_open HL3) as RAv. pose proof (crt_at_L3_B_i_lt HL3) as Hi.
pose proof (crt_at_L3_B_cset_range HL3) as Hcs1. pose proof (crt_at_L3_B_cset_mod HL3) as Hcs2.
pose proof (crt_at_L3_B_cnt HL3) as Hcnt. pose proof (crt_at_L3_B_saved_nz HL3) as Hsv.
pose proof (crt_at_L3_B_copy HL3) as HTC. pose proof (crt_at_L3_B_copy_fd HL3) as HFD.
pose proof (crt_at_L3_B_back HL3) as HBK. pose proof (crt_at_L3_B_pos HL3) as HPOS0.
pose proof (crt_at_L3_B_kw HL3) as Hkw. pose proof (crt_at_L3_B_back_tblk HL3) as HbP.
destruct (crt_at_L3_B_back_fo HL3) as (Fb & HFo & HFm). pose proof (crt_at_L3_B_copy_tblk HL3) as HcP.
destruct (crt_at_L3_B_copy_fo HL3) as (Fc & HFoc & HFmc). pose proof (crt_at_L3_B_copy_depth HL3) as Hdep.
clear HL3.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_blocks_perm HL) as HPB. pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
destruct (crt_live_journal HL2) as (WS_HJ2 & HJ2 & HB_HJ2). pose proof (crt_live_frame HL2) as HFRM2.
pose proof (crt_side_ledger (crt_live_side HL2)) as HLED2.
pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HJ) as HAR.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hd1 & Hd2 & Hd3 & Hd4).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (crt_frame_present HFRM2) as Hfp2. clear HFRM2. rewrite EFA in Hfp2.
set (F := frame_addr lyc CRT_CID pos) in *.
(* the document's fake frame *)
pose proof HTREE as (_ & _ & _ & (_ & (cid' & pos' & Hin' & Hdf1 & Hdf2) & _)).
pose proof HJ as (_ & Hly & _ & _ & _ & HFR & _).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc (cb4_ar0 B ARx ly S Hp W regs mem md ch HPRE) Hly) as (_ & Efa & _).
rewrite <- (Efa cid' pos') in Hdf1, Hdf2.
assert (Hfr' : In (cid', pos') (frames Sc)) by (rewrite HFR; right; exact Hin').
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid' pos' HAR Hfr') as (Fa32 & _ & _ & _).
destruct (alx_frames _ _ _ LAWS ly2 Sc Hp2 W2 mem2 md2 cid' pos' HAR2 Hfr') as (_ & _ & Fdoc2 & _).
pose proof HJ2 as (_ & Hly2 & _).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md ly2 (cb4_ar0 B ARx ly S Hp W regs mem md ch HPRE) Hly2) as (_ & Efa2 & _).
rewrite (Efa2 cid' pos'), <- (Efa cid' pos') in Fdoc2.
(* every Lam block's bytes are kept *)
assert (KLam : forall a k y, In (a, k) Lamc -> a <= y < a + k ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H Wc) memc y).
{ intros a k y Hak Hy.
  destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 a k HAR HLED Hak)
    as (Hk0 & _ & _ & _ & _ & Hab & _).
  replace y with ((a - 16) + (y - a + 16)) by lia. apply (KBL _ _ _ Hab).
  unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia. }
assert (HDc : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right.
  right. exact Hbk. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left. exact Hbk. }
(* F's frame bytes and shadow *)
assert (KF : forall a, (F <= a < F + 512 \/ shadow_addr F <= a < shadow_addr F + 64) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply (KFR CRT_CID pos a Hin). unfold in_zr, frame_rng. cbn [fst snd]. rewrite cb4_fb.
  change (512 / 8) with 64. fold F. lia. }
(* a range of F's frame: its shadow *)
assert (RAF : forall o, 0 <= o -> o + 56 <= 512 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (F + o) 56 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (F + o) 56).
{ intros o Ho1 Ho2 HR. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HR].
  intros y Hy. unfold shadow_of_addr. apply KF. right. unfold shadow_addr.
  assert (F / 8 <= y / 8) by (apply Z.div_le_mono; lia).
  assert (y / 8 < F / 8 + 64) by (apply Z.div_lt_upper_bound; [lia|]; pose proof (Z.div_mod F 8 ltac:(lia)); lia).
  lia. }
assert (SP : forall off v, 0 <= off < 2 ^ 32 -> crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) Wc memc off v ->
  crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs) W2 mem2 off v).
{ intros off v Hoff Hv. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2 _ 8 _); [|exact Hv].
  intros k Hk. apply KST. lia. }
refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ2;
          crt_at_L3_B_fregs := cb4_fregs_trans fx fxk fx' HFK HFK2; crt_at_L3_B_live := HL2;
          crt_at_L3_B_bregs := _; crt_at_L3_B_s5_i := _; crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _;
          crt_at_L3_B_s6_keys := _;
          crt_at_L3_B_sp_saved := SP CRT_SP_SAVED_B _ ltac:(unfold CRT_SP_SAVED_B; lia) SPsv;
          crt_at_L3_B_sp_shkids := SP CRT_SP_SHKIDS_B _ ltac:(unfold CRT_SP_SHKIDS_B; lia) SPshk;
          crt_at_L3_B_sp_keys := SP CRT_SP_KEYS_B _ ltac:(unfold CRT_SP_KEYS_B; lia) SPkeys;
          crt_at_L3_B_sp_back := _;
          crt_at_L3_B_sp_at := SP CRT_SP_AT_B _ ltac:(unfold CRT_SP_AT_B; lia) SPat;
          crt_at_L3_B_sp_kids := SP CRT_SP_KIDS_B _ ltac:(unfold CRT_SP_KIDS_B; lia) SPkids;
          crt_at_L3_B_sp_shn := SP CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) SPshn;
          crt_at_L3_B_sp_pn := SP CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) SPpn;
          crt_at_L3_B_doc_align := Hd8; crt_at_L3_B_doc_open := _; crt_at_L3_B_back_open := _;
          crt_at_L3_B_v_open := _; crt_at_L3_B_i_lt := Hi; crt_at_L3_B_cset_range := Hcs1;
          crt_at_L3_B_cset_mod := Hcs2; crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv;
          crt_at_L3_B_copy := _; crt_at_L3_B_copy_fd := _; crt_at_L3_B_back := _; crt_at_L3_B_pos := HPOS0;
          crt_at_L3_B_kw := Hkw; crt_at_L3_B_back_tblk := HbP; crt_at_L3_B_back_fo := _;
          crt_at_L3_B_copy_tblk := HcP; crt_at_L3_B_copy_fo := _; crt_at_L3_B_copy_depth := Hdep |}.
all: try rewrite EFA.
{ exact (ct6_bregs_pres regs rg regs2 F HBR HP). }
{ rewrite (ts_ap rg regs2 21%bv HP) by ts_cs. exact R21. }
{ rewrite (ts_ap rg regs2 24%bv HP) by ts_cs. exact R24. }
{ rewrite (ts_ap rg regs2 26%bv HP) by ts_cs. exact R26. }
{ rewrite (ts_ap rg regs2 22%bv HP) by ts_cs. exact R22. }
{ exact (SP CRT_SP_BACK _ ltac:(unfold CRT_SP_BACK; lia) SPback). }
- (* the document's 56 bytes: their shadow lies in its fake frame's shadow *)
  apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact RAd].
  intros y Hy. unfold shadow_of_addr. apply (KFR cid' pos' _ Hfr'). right. unfold in_zr, shadow_addr. cbn [fst snd].
  set (fa := frame_addr lyc cid' pos') in *. set (fb := fs_frame_bytes cid') in *.
  pose proof (Z.div_mod fa 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod y 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod fb 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound fb 8 ltac:(lia)) as M3.
  pose proof (Z.div_mod doc 8 ltac:(lia)) as D4.
  assert (fa mod 8 = 0) by lia.
  lia.
- exact (RAF CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) RAb).
- exact (RAF CRT_OFF_V ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia) RAv).
- (* copy *)
  apply (pj_nodeR_frame SEGS crt_tc (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) _ Dc HTC).
  apply (ct6_agree Wc memc ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc 0 _ Dc HAR2 HLED2 HDc); [|exact KLam].
  intros y Hy. split; [apply Hfp2; rewrite cb4_fb; unfold CRT_OFF_COPY in Hy; lia|].
  apply KF. left. unfold CRT_OFF_COPY in Hy. lia.
- apply (crt102rw_fdR_frame SEGS DOC_D (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) _ Dc HFD).
  apply (ct6_agree Wc memc ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc 0 _ Dc HAR2 HLED2 HDc); [|exact KLam].
  intros y Hy. split; [apply Hfp2; rewrite cb4_fb; unfold CRT_OFF_COPY in Hy; lia|].
  apply KF. left. unfold CRT_OFF_COPY in Hy. lia.
- apply (pj_nodeR_frame SEGS crt_tc (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) _ Dback HBK).
  apply (ct6_agree Wc memc ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc 0 _ Dback HAR2 HLED2 HDb); [|exact KLam].
  intros y Hy. split; [apply Hfp2; rewrite cb4_fb; unfold CRT_OFF_BACK in Hy; lia|].
  apply KF. left. unfold CRT_OFF_BACK in Hy. lia.
- (* back's free order: the same footprint *)
  exists Fb. split; [|exact HFm].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dback Fb HFo).
  + exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFo).
  + apply (ct6_agree Wc memc ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc 0 _ Dback HAR2 HLED2 HDb); [|exact KLam].
    intros y Hy. split; [apply Hfp2; rewrite cb4_fb; unfold CRT_OFF_BACK in Hy; lia|].
    apply KF. left. unfold CRT_OFF_BACK in Hy. lia.
- (* copy's free order: the same footprint (copy's blocks are not written) *)
  exists Fc. split; [|exact HFmc].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dc Fc HFoc).
  + exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFoc).
  + apply (ct6_agree Wc memc ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc 0 _ Dc HAR2 HLED2 HDc); [|exact KLam].
    intros y Hy. split; [apply Hfp2; rewrite cb4_fb; unfold CRT_OFF_COPY in Hy; lia|].
    apply KF. left. unfold CRT_OFF_COPY in Hy. lia.
Qed.

(* ---- the keep clauses of a callee's journal made at sp1 with no footprint, its blocks unchanged ---- *)
Lemma ct6_jkeep : forall STK1 lyc Sc Hpc (Wc : world SEGS) memc mdc ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  AJ STK1 sp1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ablocks B ly2 S2 = ablocks B lyc Sc ->
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall p n j, In (p, n) (ablocks B lyc Sc) -> 0 <= j < req_size n ->
     aview SEGS (w_H W2) mem2 (p + j) = aview SEGS (w_H Wc) memc (p + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
Proof.
intros STK1 lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 HJ1 EAB.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
split; [intros a Ha; apply G1; lia|].
split; [intros cid pos' a Hin Ha; apply (G4 cid pos' a Hin Ha); apply inFP_nil|].
split; [intros p n j Hin Hj; apply (G2 p n j Hin); [rewrite EAB; exact Hin | exact Hj | apply inFP_nil]|].
intros a H1 H2 H3 H4. apply (G3 a H1 H2 H3 H4). apply fp_spares_closed. exact sink_closed_nil.
Qed.

(* ---- the side facts of a boundary at a new state with the same allocator state, from the frames / blocks / image
   keep clauses, the new ledger and the two flags ---- *)
Lemma ct6_side_after : forall lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos Dx Lamc peakc cntc ly2 Hp2 (W2 : world SEGS)
    mem2 md2 k2 {WS : list (list Z)},
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 Sc Hp2 W2 mem2 md2 k2 WS ->
  prh_ledger B ly2 Sc Hp2 W2 mem2 Lamc peakc cntc SIZE_MAXZ 0 most 0 ->
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (forall p n j, In (p, n) (ablocks B lyc Sc) -> 0 <= j < req_size n ->
     aview SEGS (w_H W2) mem2 (p + j) = aview SEGS (w_H Wc) memc (p + j)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  crt_side (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) (B := B) (doc := doc) (t := t) (D := D)
    (peak := peak) (most := most) ly2 Sc Hp2 W2 mem2 Lamc peakc cntc 0 0.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ly2 Hp2 W2 mem2 md2 k2 WS HL HJ2 HLED2 KFR KBL KIMG.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL. clear HSD.
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
refine {| crt_side_ledger := HLED2; crt_side_peak := HPK; crt_side_room := HRL; crt_side_arodata := _;
          crt_side_doc := _; crt_side_doc_blocks := HDL |}.
{ intros a Hro Hno Her. rewrite (KIMG a (cb4_ro_img a Hro) Hno Her (fun Hps => pst_not_ro_B a Hps Hro)).
  exact (HRO a Hro Hno Her). }
(* the document's fake frame *)
pose proof HTREE as (_ & _ & _ & (_ & (cid' & pos' & Hin' & Hdf1 & Hdf2) & _)).
pose proof HJ as (_ & Hly & _ & _ & _ & HFR & _).
pose proof HJ2 as (_ & Hly2 & _).
pose proof (cb4_ar0 B ARx ly S Hp W regs mem md ch HPRE) as HAR0.
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md lyc HAR0 Hly) as (_ & Efa & _).
destruct (alx_layout _ _ _ LAWS ly S Hp W mem md ly2 HAR0 Hly2) as (_ & Efa2 & _).
assert (Hfr' : In (cid', pos') (frames Sc)) by (rewrite HFR; right; exact Hin').
destruct (alx_frames _ _ _ LAWS ly2 Sc Hp2 W2 mem2 md2 cid' pos' HAR2 Hfr') as (_ & _ & Fdoc2 & _).
rewrite (Efa2 cid' pos') in Fdoc2. rewrite <- (Efa cid' pos') in Fdoc2, Hdf1, Hdf2.
apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) doc D HDOC).
apply (ct6_agree Wc memc ly2 Sc Hp2 W2 mem2 md2 Lamc peakc cntc 0 doc D HAR2 HLED2 HDL).
- intros y Hy. split; [exact (proj1 (Fdoc2 y ltac:(lia)))|].
  apply (KFR cid' pos' y Hfr'). left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- intros a k y Hak Hy.
  destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 a k HAR HLED Hak)
    as (Hk0 & _ & _ & _ & _ & Hab & _).
  replace y with ((a - 16) + (y - a + 16)) by lia. apply (KBL _ _ _ Hab).
  unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
Qed.

(* ---- the live state across a change of memory confined to X, a part of the real stack between alloc_ceiling and
   sp1 (a callee's window), the journal and the allocator state unchanged (the strcmp call) ---- *)
Lemma ct6_live_keep : forall lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos Dx Lamc peakc cntc mem2 md2 (X : Z -> Prop)
    {WS : list (list Z)},
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc mem2 md2 kj WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  (forall a, X a -> YM05.alloc_ceiling <= a < sp1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem2 a) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  liveB lyc Sc Hpc Wc mem2 md2 kj pos Dx Lamc peakc cntc 0 0 /\
  (forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) /\
  (forall p n j, In (p, n) (ablocks B lyc Sc) -> 0 <= j < req_size n ->
     aview SEGS (w_H Wc) mem2 (p + j) = aview SEGS (w_H Wc) memc (p + j)).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc mem2 md2 X WS HL HJ2 HB_HJ2 HX Hag Hpres HMN2.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (proj1 HJ) as HAR.
pose proof (crt_side_ledger HSD) as HLED.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hag; [lia|]. intros Hx. pose proof (HX a Hx). lia. }
assert (KST : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hag; [lia|]. intros Hx. pose proof (HX a Hx). lia. }
assert (KFR : forall cid pos' a, In (cid, pos') (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros cid pos' a Hin' Ha. destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HAR Hin') as (G1 & G2 & G3).
  apply KL. unfold in_zr, frame_rng, shadow_addr in Ha. cbn [fst snd] in Ha.
  assert (0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
  assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
  assert (0 <= frame_addr lyc cid pos' / 8 <= frame_addr lyc cid pos') by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold SHADOW_OFF in *. lia. }
assert (KBL : forall p n j, In (p, n) (ablocks B lyc Sc) -> 0 <= j < req_size n ->
  aview SEGS (w_H Wc) mem2 (p + j) = aview SEGS (w_H Wc) memc (p + j)).
{ intros p n j Hab Hj. destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hab) as (_ & H4096 & Hce & _).
  apply KL. lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha _ _ _. pose proof (@pa_segs_low _ _ PA a Ha) as Hl. apply KL. unfold kLowMemEnd in Hl. lia. }
assert (KPST : forall a, Exists (in_zr a) PST -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. pose proof (@pa_segs_low _ _ PA a (pst_in_img_B a Ha)) as Hl. apply KL. unfold kLowMemEnd in Hl. lia. }
assert (HLED2 : prh_ledger B lyc Sc Hpc Wc mem2 Lamc peakc cntc SIZE_MAXZ 0 most 0).
{ apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc lyc Sc Hpc Wc mem2 Lamc peakc cntc SIZE_MAXZ 0 most 0 HLED).
  - exact KPST.
  - intros a k j Hk Hj.
    destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 a k HAR HLED Hk) as (Hk0 & _ & H4 & Hc & _).
    apply KL. change (@cf_head CfParams_preset) with 16. lia.
  - intros a k _ Hab. exact Hab.
  - apply Permutation_refl. }
pose proof (ct6_side_after lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc lyc Hpc Wc mem2 md2 kj HL HJ2 HLED2
  KFR KBL KIMG) as HSD2.
set (F := frame_addr lyc CRT_CID pos) in *.
split; [|split; [exact KST | split; [exact KFR | exact KBL]]].
refine {| crt_live_journal := ex_intro _ WS (conj HJ2 HB_HJ2); crt_live_side := HSD2; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := _ |}.
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact (HSV j Hj)]. intros k Hk. apply KST. lia. }
{ pose proof (crt_frame_listed HFRM) as Hinf. pose proof (crt_frame_flag_word HFRM) as Hfl.
  pose proof (crt_frame_present HFRM) as Hpr.
  refine {| crt_frame_listed := Hinf; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite cb4_fb. apply KL. lia.
  - intros a Ha. exact (Hpres a (Hpr a Ha)). }
{ unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact HSPF]. intros k Hk. apply KST.
  unfold CRT_SP_F. lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply KL.
  assert (0 <= y / 8) by (apply Z.div_pos; lia). assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF. lia. }
{ intros s0 Hs0. rewrite KL; [exact (HCH s0 Hs0)|].
  unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *.
  assert (0 <= (F + 224) / 8) by (apply Z.div_pos; lia).
  assert ((F + 224 + 56 - 1) / 8 <= F + 224 + 56 - 1) by (apply Z.div_le_upper_bound; lia). lia. }
intros H0. exact (HMN2 (HMNc H0)).
Qed.

(* ---- the four stretches, over any fact Pd of the pass's fixed data (Dc, Dback, kw, ms) that the boundaries carry
   unchanged (True for the frozen statement; the copy / read-back facts of the ruling 18:27Z for crtB_T6x) ---- *)
Section p.
Variable Pd : list (Z * Z) -> list (Z * Z) -> Z -> list (list Z * PjTree.jv) -> Prop.
#[local] Notation ATC := (forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw,
  CB fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_C_OFF_B rg memc mdc) QFb).
#[local] Notation ATL3 j ms := (forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw j -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_L3_OFF_B rg memc mdc) QFb).

(* ---- M (+0x6d4) -> L3 (i + 1 < doc->n) or C: re-read doc->n, i += 1, the strides, `bltu s5, a0` ---- *)
Lemma ct6_at_M : ATC -> forall i ms, (forall j, (i < j)%nat -> ATL3 j ms) ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_M_OFF6_B rg memc mdc) QFb.
Proof.
intros HC i ms IH fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw HL3 HPd.
destruct (ENT fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i
  (CRT_PC_B + CRT_M_OFF6_B) HL3)
  as (kb & kd & xb & xd & kib & kid & capb & capd & nm & u & u' & kxb & kxd & Db1 & Dd1 &
      Enth & Enth' & Hcb & Hcd & Hnb & Hnd & Lkib & Lkid & Hib & Hid & Ib & Id & Hn44 & SHOK & HSx).
pose proof (crt_at_L3_B_obj HL3) as Ht. pose proof (crt_at_L3_B_frm_zero HL3) as HFZ.
pose proof (crt_at_L3_B_fregs HL3) as HFK. pose proof (crt_at_L3_B_live HL3) as HL.
pose proof (crt_at_L3_B_bregs HL3) as HBR. pose proof (crt_at_L3_B_s5_i HL3) as R21.
pose proof (crt_at_L3_B_s8_i HL3) as R24. pose proof (crt_at_L3_B_s10_i HL3) as R26.
pose proof (crt_at_L3_B_s6_keys HL3) as R22. pose proof (crt_at_L3_B_sp_saved HL3) as SPsv.
pose proof (crt_at_L3_B_sp_shkids HL3) as SPshk. pose proof (crt_at_L3_B_sp_keys HL3) as SPkeys.
pose proof (crt_at_L3_B_sp_back HL3) as SPback. pose proof (crt_at_L3_B_sp_at HL3) as SPat.
pose proof (crt_at_L3_B_sp_kids HL3) as SPkids. pose proof (crt_at_L3_B_sp_shn HL3) as SPshn.
pose proof (crt_at_L3_B_sp_pn HL3) as SPpn. pose proof (crt_at_L3_B_doc_align HL3) as Hd8.
pose proof (crt_at_L3_B_doc_open HL3) as RAd. pose proof (crt_at_L3_B_back_open HL3) as RAb.
pose proof (crt_at_L3_B_v_open HL3) as RAv. pose proof (crt_at_L3_B_i_lt HL3) as Hi.
pose proof (crt_at_L3_B_cset_range HL3) as Hcs1. pose proof (crt_at_L3_B_cset_mod HL3) as Hcs2.
pose proof (crt_at_L3_B_cnt HL3) as Hcnt. pose proof (crt_at_L3_B_saved_nz HL3) as Hsv.
pose proof (crt_at_L3_B_copy HL3) as HTC. pose proof (crt_at_L3_B_copy_fd HL3) as HFD.
pose proof (crt_at_L3_B_back HL3) as HBK. pose proof (crt_at_L3_B_pos HL3) as HPOS.
pose proof (crt_at_L3_B_kw HL3) as Lkw. pose proof (crt_at_L3_B_back_tblk HL3) as Lbtb.
pose proof (crt_at_L3_B_back_fo HL3) as Lbfo. pose proof (crt_at_L3_B_copy_tblk HL3) as Lctb.
pose proof (crt_at_L3_B_copy_fo HL3) as Lcfo. pose proof (crt_at_L3_B_copy_depth HL3) as Ldep.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
set (mo := ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i) in *.
destruct (ct6_env regs rg doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)
  as (E53 & E42 & E75 & E76).
fold mo in E53, E42, E75, E76. rewrite R21 in E53.
assert (E56 : ew (TEB regs rg mo) 56 = w64 (8 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
assert (E58 : ew (TEB regs rg mo) 58 = w64 (56 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 26%bv 26 eq_refl) R26).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & _ & _).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof (crt_bregs_B_s11 HBR) as R27.
assert (E64 : ew (TEB regs rg mo) 64 = w64 doc) by exact (te_more_lt regs rg mo 0 ltac:(lia)).
assert (E59 : ew (TEB regs rg mo) 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
pose proof (Nat2Z.is_nonneg i) as Hi0.
unfold crt_cfg.
destruct (Nat.lt_ge_cases (Datatypes.S i) (length ms)) as [Hlt | Hge].
- assert (XC : conds_ok (TEB regs rg mo) [ct6_CLT]).
  { split; [|exact I]. unfold acond_ok, ct6_CLT. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U.
    rewrite (ct6_U _ 53 (Z.of_nat i) 1 E53) by lia. rewrite (ct6_U _ 75 _ 0 E75) by lia. apply Z.ltb_lt. lia. }
  pose proof (HSx [] [ct6_CLT] I XC) as HS.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ct6_Bspan (CRT_PC_B + CRT_L3_OFF_B).
  { ct6_ro. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  pmkst HS. rewrite HF in HJ, HPM |- *.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + CRT_L3_OFF_B) end.
  refine (IH (Datatypes.S i) ltac:(lia) fxk lyc Sc Hpc Wc memc _ kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) cset saved
    kw _ HPd).
  refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ; crt_at_L3_B_fregs := HFK;
            crt_at_L3_B_live := ct6_live_md HL HJ HB_HJ; crt_at_L3_B_bregs := _; crt_at_L3_B_s5_i := _;
            crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _; crt_at_L3_B_s6_keys := _;
            crt_at_L3_B_sp_saved := SPsv; crt_at_L3_B_sp_shkids := SPshk; crt_at_L3_B_sp_keys := SPkeys;
            crt_at_L3_B_sp_back := SPback; crt_at_L3_B_sp_at := SPat; crt_at_L3_B_sp_kids := SPkids;
            crt_at_L3_B_sp_shn := SPshn; crt_at_L3_B_sp_pn := SPpn; crt_at_L3_B_doc_align := Hd8;
            crt_at_L3_B_doc_open := RAd; crt_at_L3_B_back_open := RAb; crt_at_L3_B_v_open := RAv;
            crt_at_L3_B_i_lt := _; crt_at_L3_B_cset_range := Hcs1; crt_at_L3_B_cset_mod := Hcs2;
            crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv; crt_at_L3_B_copy := HTC;
            crt_at_L3_B_copy_fd := HFD; crt_at_L3_B_back := HBK; crt_at_L3_B_pos := HPOS;
            crt_at_L3_B_kw := Lkw; crt_at_L3_B_back_tblk := Lbtb; crt_at_L3_B_back_fo := Lbfo;
            crt_at_L3_B_copy_tblk := Lctb; crt_at_L3_B_copy_fo := Lcfo; crt_at_L3_B_copy_depth := Ldep |}.
  { apply (ct6_bregs_eq regs rg _ _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  4:{ ct6_reg HS (22%bv : bv 5) Hr22; rewrite Hr22; unfold PJ_OFF_KEYS, w64. apply (ct6_shx_denot _ 64 32 doc E64 E59); lia. }
  + ct6_reg HS (21%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_off _ 53 1 (Z.of_nat i) E53) by lia. f_equal. lia.
  + ct6_reg HS (24%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_off _ 56 8 (8 * Z.of_nat i)) by (try exact E56; lia). f_equal. lia.
  + ct6_reg HS (26%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_off _ 58 56 (56 * Z.of_nat i)) by (try exact E58; lia). f_equal. lia.
  + exact Hlt.
- assert (XC : conds_ok (TEB regs rg mo) [ct6_CGE]).
  { split; [|exact I]. unfold acond_ok, ct6_CGE. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
    rewrite (ct6_U _ 53 (Z.of_nat i) 1 E53) by lia. rewrite (ct6_U _ 75 _ 0 E75) by lia.
    apply negb_true_iff, Z.ltb_ge. lia. }
  pose proof (HSx [] [ct6_CGE] I XC) as HS.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ct6_Bspan (CRT_PC_B + CRT_C_OFF_B).
  { ct6_ro. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  pmkst HS. rewrite HF in HJ, HPM |- *.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + CRT_C_OFF_B) end.
  refine (HC fxk lyc Sc Hpc Wc memc _ kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) ms cset saved kw _ HPd).
  refine {| crt_at_C_B_obj := Ht; crt_at_C_B_frm_zero := HFZ; crt_at_C_B_fregs := HFK;
            crt_at_C_B_live := ct6_live_md HL HJ HB_HJ; crt_at_C_B_bregs := _; crt_at_C_B_sp_saved := SPsv;
            crt_at_C_B_sp_back := SPback; crt_at_C_B_sp_at := SPat; crt_at_C_B_back_open := RAb;
            crt_at_C_B_v_open := RAv; crt_at_C_B_cset_range := Hcs1; crt_at_C_B_cset_mod := Hcs2;
            crt_at_C_B_cnt := Hcnt; crt_at_C_B_saved_nz := Hsv; crt_at_C_B_copy := HTC; crt_at_C_B_copy_fd := HFD;
            crt_at_C_B_back := HBK; crt_at_C_B_pos := HPOS; crt_at_C_B_kw := Lkw; crt_at_C_B_back_tblk := Lbtb;
            crt_at_C_B_back_fo := Lbfo; crt_at_C_B_copy_tblk := Lctb; crt_at_C_B_copy_fo := Lcfo;
            crt_at_C_B_copy_depth := Ldep |}.
  apply (ct6_bregs_eq regs rg _ _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr.
Qed.

(* ---- R (+0x6d0, same's return site) -> M: `beqz a0` not taken (same answered 1) ---- *)
Lemma ct6_at_R : ATC -> forall i ms, (forall j, (i < j)%nat -> ATL3 j ms) ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i -> Pd Dc Dback kw ms ->
  getr rg 10 <> w64 0 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_R_OFF6_B rg memc mdc) QFb.
Proof.
intros HC i ms IH fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw HL3 HPd Hne.
destruct (ENT fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i
  (CRT_PC_B + CRT_R_OFF6_B) HL3)
  as (kb & kd & xb & xd & kib & kid & capb & capd & nm & u & u' & kxb & kxd & Db1 & Dd1 &
      Enth & Enth' & Hcb & Hcd & Hnb & Hnd & Lkib & Lkid & Hib & Hid & Ib & Id & Hn44 & SHOK & HSx).
pose proof (crt_at_L3_B_obj HL3) as Ht. pose proof (crt_at_L3_B_frm_zero HL3) as HFZ.
pose proof (crt_at_L3_B_fregs HL3) as HFK. pose proof (crt_at_L3_B_live HL3) as HL.
pose proof (crt_at_L3_B_bregs HL3) as HBR. pose proof (crt_at_L3_B_s5_i HL3) as R21.
pose proof (crt_at_L3_B_s8_i HL3) as R24. pose proof (crt_at_L3_B_s10_i HL3) as R26.
pose proof (crt_at_L3_B_s6_keys HL3) as R22. pose proof (crt_at_L3_B_sp_saved HL3) as SPsv.
pose proof (crt_at_L3_B_sp_shkids HL3) as SPshk. pose proof (crt_at_L3_B_sp_keys HL3) as SPkeys.
pose proof (crt_at_L3_B_sp_back HL3) as SPback. pose proof (crt_at_L3_B_sp_at HL3) as SPat.
pose proof (crt_at_L3_B_sp_kids HL3) as SPkids. pose proof (crt_at_L3_B_sp_shn HL3) as SPshn.
pose proof (crt_at_L3_B_sp_pn HL3) as SPpn. pose proof (crt_at_L3_B_doc_align HL3) as Hd8.
pose proof (crt_at_L3_B_doc_open HL3) as RAd. pose proof (crt_at_L3_B_back_open HL3) as RAb.
pose proof (crt_at_L3_B_v_open HL3) as RAv. pose proof (crt_at_L3_B_i_lt HL3) as Hi.
pose proof (crt_at_L3_B_cset_range HL3) as Hcs1. pose proof (crt_at_L3_B_cset_mod HL3) as Hcs2.
pose proof (crt_at_L3_B_cnt HL3) as Hcnt. pose proof (crt_at_L3_B_saved_nz HL3) as Hsv.
pose proof (crt_at_L3_B_copy HL3) as HTC. pose proof (crt_at_L3_B_copy_fd HL3) as HFD.
pose proof (crt_at_L3_B_back HL3) as HBK. pose proof (crt_at_L3_B_pos HL3) as HPOS.
pose proof (crt_at_L3_B_kw HL3) as Lkw. pose proof (crt_at_L3_B_back_tblk HL3) as Lbtb.
pose proof (crt_at_L3_B_back_fo HL3) as Lbfo. pose proof (crt_at_L3_B_copy_tblk HL3) as Lctb.
pose proof (crt_at_L3_B_copy_fo HL3) as Lcfo. pose proof (crt_at_L3_B_copy_depth HL3) as Ldep.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
set (mo := ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i) in *.
destruct (ct6_env regs rg doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)
  as (E53 & E42 & E75 & E76).
fold mo in E53, E42, E75, E76. rewrite R21 in E53.
assert (E56 : ew (TEB regs rg mo) 56 = w64 (8 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
assert (E58 : ew (TEB regs rg mo) 58 = w64 (56 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 26%bv 26 eq_refl) R26).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & _ & _).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof (crt_bregs_B_s11 HBR) as R27.
assert (E64 : ew (TEB regs rg mo) 64 = w64 doc) by exact (te_more_lt regs rg mo 0 ltac:(lia)).
assert (E59 : ew (TEB regs rg mo) 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
pose proof (Nat2Z.is_nonneg i) as Hi0.
unfold crt_cfg.
assert (XC : conds_ok (TEB regs rg mo) [ct6_A1]).
{ split; [|exact I]. unfold acond_ok, ct6_A1. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U.
  rewrite ts_U0, E42, U_lit by lia. apply negb_true_iff, Z.eqb_neq. intros E0. apply Hne. apply bv_eq. rewrite E0.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose proof (HSx [] [ct6_A1] I XC) as HS.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ct6_Bspan (CRT_PC_B + CRT_M_OFF6_B).
{ ct6_ro. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
pmkst HS. rewrite HF in HJ, HPM |- *.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_B + CRT_M_OFF6_B) end.
refine (ct6_at_M HC i ms IH fxk lyc Sc Hpc Wc memc _ kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) cset saved kw _ HPd).
refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ; crt_at_L3_B_fregs := HFK;
          crt_at_L3_B_live := ct6_live_md HL HJ HB_HJ; crt_at_L3_B_bregs := _; crt_at_L3_B_s5_i := _;
          crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _; crt_at_L3_B_s6_keys := _;
          crt_at_L3_B_sp_saved := SPsv; crt_at_L3_B_sp_shkids := SPshk; crt_at_L3_B_sp_keys := SPkeys;
          crt_at_L3_B_sp_back := SPback; crt_at_L3_B_sp_at := SPat; crt_at_L3_B_sp_kids := SPkids;
          crt_at_L3_B_sp_shn := SPshn; crt_at_L3_B_sp_pn := SPpn; crt_at_L3_B_doc_align := Hd8;
          crt_at_L3_B_doc_open := RAd; crt_at_L3_B_back_open := RAb; crt_at_L3_B_v_open := RAv;
          crt_at_L3_B_i_lt := Hi; crt_at_L3_B_cset_range := Hcs1; crt_at_L3_B_cset_mod := Hcs2;
          crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv; crt_at_L3_B_copy := HTC;
          crt_at_L3_B_copy_fd := HFD; crt_at_L3_B_back := HBK; crt_at_L3_B_pos := HPOS;
          crt_at_L3_B_kw := Lkw; crt_at_L3_B_back_tblk := Lbtb; crt_at_L3_B_back_fo := Lbfo;
          crt_at_L3_B_copy_tblk := Lctb; crt_at_L3_B_copy_fo := Lcfo; crt_at_L3_B_copy_depth := Ldep |}.
{ apply (ct6_bregs_eq regs rg _ _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
{ rewrite <- R21. ct6_keep HS. } { rewrite <- R24. ct6_keep HS. } { rewrite <- R26. ct6_keep HS. }
{ ct6_reg HS (22%bv : bv 5) Hr22; rewrite Hr22; unfold PJ_OFF_KEYS, w64. apply (ct6_shx_denot _ 64 32 doc E64 E59); lia. }
Qed.

(* ---- K (+0x64c, strcmp's return site) with a0 = 0 -> M (at = i: `beq a0, s5` skips same) or same's call ---- *)
Lemma ct6_at_K : ATC -> forall i ms, (forall j, (i < j)%nat -> ATL3 j ms) ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i -> Pd Dc Dback kw ms ->
  getr rg 10 = w64 0 ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_K_OFF6R_B rg memc mdc) QFb.
Proof.
intros HC i ms IH fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw HL3 HPd H10.
destruct (ENT fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i
  (CRT_PC_B + CRT_K_OFF6R_B) HL3)
  as (kb & kd & xb & xd & kib & kid & capb & capd & nm & u & u' & kxb & kxd & Db1 & Dd1 &
      Enth & Enth' & Hcb & Hcd & Hnb & Hnd & Lkib & Lkid & Hib & Hid & Ib & Id & Hn44 & SHOK & HSx).
pose proof (crt_at_L3_B_obj HL3) as Ht. pose proof (crt_at_L3_B_frm_zero HL3) as HFZ.
pose proof (crt_at_L3_B_fregs HL3) as HFK. pose proof (crt_at_L3_B_live HL3) as HL.
pose proof (crt_at_L3_B_bregs HL3) as HBR. pose proof (crt_at_L3_B_s5_i HL3) as R21.
pose proof (crt_at_L3_B_s8_i HL3) as R24. pose proof (crt_at_L3_B_s10_i HL3) as R26.
pose proof (crt_at_L3_B_s6_keys HL3) as R22. pose proof (crt_at_L3_B_sp_saved HL3) as SPsv.
pose proof (crt_at_L3_B_sp_shkids HL3) as SPshk. pose proof (crt_at_L3_B_sp_keys HL3) as SPkeys.
pose proof (crt_at_L3_B_sp_back HL3) as SPback. pose proof (crt_at_L3_B_sp_at HL3) as SPat.
pose proof (crt_at_L3_B_sp_kids HL3) as SPkids. pose proof (crt_at_L3_B_sp_shn HL3) as SPshn.
pose proof (crt_at_L3_B_sp_pn HL3) as SPpn. pose proof (crt_at_L3_B_doc_align HL3) as Hd8.
pose proof (crt_at_L3_B_doc_open HL3) as RAd. pose proof (crt_at_L3_B_back_open HL3) as RAb.
pose proof (crt_at_L3_B_v_open HL3) as RAv. pose proof (crt_at_L3_B_i_lt HL3) as Hi.
pose proof (crt_at_L3_B_cset_range HL3) as Hcs1. pose proof (crt_at_L3_B_cset_mod HL3) as Hcs2.
pose proof (crt_at_L3_B_cnt HL3) as Hcnt. pose proof (crt_at_L3_B_saved_nz HL3) as Hsv.
pose proof (crt_at_L3_B_copy HL3) as HTC. pose proof (crt_at_L3_B_copy_fd HL3) as HFD.
pose proof (crt_at_L3_B_back HL3) as HBK. pose proof (crt_at_L3_B_pos HL3) as HPOS.
pose proof (crt_at_L3_B_kw HL3) as Lkw. pose proof (crt_at_L3_B_back_tblk HL3) as Lbtb.
pose proof (crt_at_L3_B_back_fo HL3) as Lbfo. pose proof (crt_at_L3_B_copy_tblk HL3) as Lctb.
pose proof (crt_at_L3_B_copy_fo HL3) as Lcfo. pose proof (crt_at_L3_B_copy_depth HL3) as Ldep.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
set (mo := ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i) in *.
destruct (ct6_env regs rg doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)
  as (E53 & E42 & E75 & E76).
fold mo in E53, E42, E75, E76. rewrite R21 in E53.
assert (E56 : ew (TEB regs rg mo) 56 = w64 (8 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
assert (E58 : ew (TEB regs rg mo) 58 = w64 (56 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 26%bv 26 eq_refl) R26).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & _ & _).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof (crt_bregs_B_s11 HBR) as R27.
assert (E64 : ew (TEB regs rg mo) 64 = w64 doc) by exact (te_more_lt regs rg mo 0 ltac:(lia)).
assert (E59 : ew (TEB regs rg mo) 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
pose proof (Nat2Z.is_nonneg i) as Hi0.
unfold crt_cfg.
assert (XA0 : acond_ok (TEB regs rg mo) ct6_A0).
{ unfold acond_ok, ct6_A0. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
  rewrite ts_U0, E42, H10, U_lit by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hat : (cm_at ms <= length ms)%nat) by apply cm_at_le.
destruct (Nat.eq_dec i (cm_at ms)) as [Eat | Nat].
- assert (XC : conds_ok (TEB regs rg mo) [ct6_A0; ct6_AEQ]).
  { split; [exact XA0|]. split; [|exact I]. unfold acond_ok, ct6_AEQ. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
    rewrite (ct6_U _ 76 _ 0 E76) by lia. rewrite (ct6_U _ 53 _ 0 E53) by lia. apply Z.eqb_eq. lia. }
  pose proof (HSx [] [ct6_A0; ct6_AEQ] I XC) as HS.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ct6_Bspan (CRT_PC_B + CRT_M_OFF6_B).
  { ct6_ro. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  pmkst HS. rewrite HF in HJ, HPM |- *.
  lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
    change n with (CRT_PC_B + CRT_M_OFF6_B) end.
  refine (ct6_at_M HC i ms IH fxk lyc Sc Hpc Wc memc _ kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) cset saved kw _ HPd).
  refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ; crt_at_L3_B_fregs := HFK;
            crt_at_L3_B_live := ct6_live_md HL HJ HB_HJ; crt_at_L3_B_bregs := _; crt_at_L3_B_s5_i := _;
            crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _; crt_at_L3_B_s6_keys := _;
            crt_at_L3_B_sp_saved := SPsv; crt_at_L3_B_sp_shkids := SPshk; crt_at_L3_B_sp_keys := SPkeys;
            crt_at_L3_B_sp_back := SPback; crt_at_L3_B_sp_at := SPat; crt_at_L3_B_sp_kids := SPkids;
            crt_at_L3_B_sp_shn := SPshn; crt_at_L3_B_sp_pn := SPpn; crt_at_L3_B_doc_align := Hd8;
            crt_at_L3_B_doc_open := RAd; crt_at_L3_B_back_open := RAb; crt_at_L3_B_v_open := RAv;
            crt_at_L3_B_i_lt := Hi; crt_at_L3_B_cset_range := Hcs1; crt_at_L3_B_cset_mod := Hcs2;
            crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv; crt_at_L3_B_copy := HTC;
            crt_at_L3_B_copy_fd := HFD; crt_at_L3_B_back := HBK; crt_at_L3_B_pos := HPOS;
            crt_at_L3_B_kw := Lkw; crt_at_L3_B_back_tblk := Lbtb; crt_at_L3_B_back_fo := Lbfo;
            crt_at_L3_B_copy_tblk := Lctb; crt_at_L3_B_copy_fo := Lcfo; crt_at_L3_B_copy_depth := Ldep |}.
  { apply (ct6_bregs_eq regs rg _ _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  { rewrite <- R21. ct6_keep HS. } { rewrite <- R24. ct6_keep HS. } { rewrite <- R26. ct6_keep HS. }
  { ct6_reg HS (22%bv : bv 5) Hr22; rewrite Hr22; unfold PJ_OFF_KEYS, w64. apply (ct6_shx_denot _ 64 32 doc E64 E59); lia. }
- assert (XC : conds_ok (TEB regs rg mo) [ct6_A0; ct6_ANE]).
  { split; [exact XA0|]. split; [|exact I]. unfold acond_ok, ct6_ANE. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U.
    rewrite (ct6_U _ 76 _ 0 E76) by lia. rewrite (ct6_U _ 53 _ 0 E53) by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  pose proof (HSx [] [ct6_A0; ct6_ANE] I XC) as HS.
  pose (RUN := @crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
    (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ct6_Bspan.
  { ct6_ro. }
  apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  pose proof HJ as HJm. rewrite HF in HJm, HPM.
  set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  pose proof (ct6_live_md HL HJm HB_HJ) as HLc.
  (* the boundary at the call: memory and named registers unchanged *)
  assert (HL3c : L3B fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) ms cset saved kw i).
  { refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ; crt_at_L3_B_fregs := HFK;
              crt_at_L3_B_live := HLc; crt_at_L3_B_bregs := _; crt_at_L3_B_s5_i := _;
              crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _; crt_at_L3_B_s6_keys := _;
              crt_at_L3_B_sp_saved := SPsv; crt_at_L3_B_sp_shkids := SPshk; crt_at_L3_B_sp_keys := SPkeys;
              crt_at_L3_B_sp_back := SPback; crt_at_L3_B_sp_at := SPat; crt_at_L3_B_sp_kids := SPkids;
              crt_at_L3_B_sp_shn := SPshn; crt_at_L3_B_sp_pn := SPpn; crt_at_L3_B_doc_align := Hd8;
              crt_at_L3_B_doc_open := RAd; crt_at_L3_B_back_open := RAb; crt_at_L3_B_v_open := RAv;
              crt_at_L3_B_i_lt := Hi; crt_at_L3_B_cset_range := Hcs1; crt_at_L3_B_cset_mod := Hcs2;
              crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv; crt_at_L3_B_copy := HTC;
              crt_at_L3_B_copy_fd := HFD; crt_at_L3_B_back := HBK; crt_at_L3_B_pos := HPOS;
              crt_at_L3_B_kw := Lkw; crt_at_L3_B_back_tblk := Lbtb; crt_at_L3_B_back_fo := Lbfo;
              crt_at_L3_B_copy_tblk := Lctb; crt_at_L3_B_copy_fo := Lcfo; crt_at_L3_B_copy_depth := Ldep |}.
    { apply (ct6_bregs_eq regs rg _ _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
    { rewrite <- R21. ct6_keep HS. } { rewrite <- R24. ct6_keep HS. } { rewrite <- R26. ct6_keep HS. }
    { ct6_reg HS (22%bv : bv 5) Hr22; rewrite Hr22; unfold PJ_OFF_KEYS, w64.
      apply (ct6_shx_denot _ 64 32 doc E64 E59); lia. } }
  pose proof (crt_at_L3_B_bregs HL3c) as HBRc.
  (* the call's arguments: a0 = &back.kids[i], a1 = &doc->kids[i], ra = R *)
  set (pa := kib + 56 * Z.of_nat i). set (pb := kid + 56 * Z.of_nat i).
  destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc' Lamc peakc cntc 0 kib (56 * capb) (proj1 HJm) HLED Lkib)
    as (kib0 & kib16 & kib4 & kibc & kibapp & kibab & kibra & kibhv & kibpr).
  destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc' Lamc peakc cntc 0 kid (56 * capd) (proj1 HJm) HLED Lkid)
    as (kid0 & kid16 & kid4 & kidc & kidapp & kidab & kidra & kidhv & kidpr).
  assert (E73 : ew (TEB regs rg mo) 73 = w64 pa) by exact (te_more_lt regs rg mo 9 ltac:(lia)).
  assert (E74 : ew (TEB regs rg mo) 74 = w64 pb) by exact (te_more_lt regs rg mo 10 ltac:(lia)).
  ct6_reg HS (10%bv : bv 5) Q10. rewrite (ct6_denot_at _ 73 pa E73) in Q10 by (unfold pa; lia).
  ct6_reg HS (11%bv : bv 5) Q11. rewrite (ct6_denot_at _ 74 pb E74) in Q11 by (unfold pb; lia).
  destruct (cb7k_ret CRT_R_OFF6_B ltac:(unfold CRT_R_OFF6_B; lia) ltac:(reflexivity)) as (Hr1 & _ & _).
  ct6_reg HS (1%bv : bv 5) Q1.
  assert (E240 : ew (TEB regs rg mo) 240 = Z_to_bv 64 BASE) by exact (te_img (L := B_prog_listing) (PA := PA) regs rg mo 240 ltac:(vm_compute; lia)).
  lazymatch type of Q1 with context [SOff 240 ?c] =>
    replace c with (CRT_PC_B + CRT_R_OFF6_B) in Q1 by (vm_compute; reflexivity) end.
  assert (HPC : 0 <= CRT_PC_B < 2 ^ 16) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
  assert (HBS : 4096 <= BASE < 2 ^ 30) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
  rewrite (ct6_denot_off _ 240 _ BASE E240) in Q1 by (unfold CRT_R_OFF6_B; lia).
  assert (HE2 : bv_unsigned (ew (TEB regs rg mo) 2) = sp0)
    by (rewrite (te_entry regs rg mo 2%bv 2) by reflexivity; reflexivity).
  pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
  assert (Hs240 : sp0 - 240 <= sp1).
  { pose proof Hal16 as H16. pose proof Hs1a as H32. apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide in H32; [|lia].
    destruct H16 as [q Hq]. destruct H32 as [q' Hq']. lia. }
  assert (HSTK : 0 <= @STK_same prh_img_B DOC_D /\ @STK_same prh_img_B DOC_D + 240 <= STKC)
    by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (Hstkc : STKC = 27632) by (vm_compute; reflexivity).
  assert (Hsp1 : spZ (ms_regs ms0) = sp1).
  { pose proof (crt_bregs_B_sp HBRc) as R2c. unfold spZ. rewrite R2c. unfold w64. apply unsigned_lit_small. lia. }
  (* depth of the read-back's kid i *)
  assert (Hdep : (PjTree.depth u' <= DOC_D)%nat).
  { pose proof (proj1 (proj2 (PjRoundTrip.read_json ReaderRes.jr_strtod x t HREAD))) as Hdt.
    assert (Hl' : (i < length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat)
      by (apply nth_error_Some; rewrite Enth'; discriminate).
    pose proof (cm_crt_member_depth t ms Hdt Ht i (nm, u') Hl') as Hd.
    rewrite (nth_error_nth _ _ (nm, u') Enth') in Hd. cbn [snd] in Hd. lia. }
  assert (Hu : u' = u).
  { destruct (cm_set_member ms (PjTree.JStr ck_STAMP) i nm u Enth) as (u2 & E2 & Hne2 & _).
    rewrite Enth' in E2. injection E2 as <-. exact (Hne2 Nat). }
  eapply (cb7k_call B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D Lam peak cnt ran most LAWS HPRE
    fxk (@STK_same prh_img_B DOC_D) [] CRT_R_OFF6_B (SIGMA AS_same) Wc (TEB regs rg mo) _ ms0 mdc' lyc Sc Hpc kj pos
    (Dback ++ (saved, kw) :: Dc) Lamc peakc cntc 0 0 _ HFZ HS eq_refl eq_refl HE2).
  { rewrite HF. exact HLc. }
  { exact HBRc. }
  { exact Q1. }
  { unfold CRT_R_OFF6_B. lia. }
  { reflexivity. }
  { exact (proj1 HSTK). }
  { exact (proj2 HSTK). }
  { intros a Ha. exfalso. exact (inFP_nil a Ha). }
  { (* same's text at this call: plain (SRr, fpostm), into cb7k_call's R premise by YA0nH.SRr_SRr' and
       apost_base_xF_R_lift at YA0nH.wle_wle' (the contract's recipe R5) *)
    intros ch1 Hch1 HPRE1. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    { apply YA0nH.SRr_SRr'. rewrite HF in HPRE1 |- *.
      refine (SAME fxk lyc Sc Hpc Wc (ms_regs ms0) memc mdc' ch1 pa pb u' u Db1 Dd1 Lamc peakc cntc SIZE_MAXZ 0 most 0
        HPRE1 _ Q10 Q11 _ _ Hdep _ _ HLED).
      - (* the guarded live-stack premise: pa = &back.kids[i] lies in a ledger block, below alloc_ceiling < sp *)
        intros Hle. exfalso. rewrite Hsp1 in Hle. unfold pa in Hle. lia.
      - split; [exact Hnb|]. split; [left; exists kib, (56 * capb); split; [exact Lkib | unfold pa; lia]|].
        split; [apply kibra; unfold pa; lia | apply kibhv; unfold pa; lia].
      - split; [exact Hnd|]. split; [left; exists kid, (56 * capd); split; [exact Lkid | unfold pb; lia]|].
        split; [apply kidra; unfold pb; lia | apply kidhv; unfold pb; lia].
      - intros z Hz. rewrite Hsp1. destruct Hz as [Hz | ((b & kb') & Hb & Hz)]; [unfold pa in Hz; lia|].
        unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
        destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc' Lamc peakc cntc 0 b kb' (proj1 HJm) HLED (Ib _ Hb))
          as (_ & _ & _ & Hbc & _). lia.
      - intros z Hz. rewrite Hsp1. destruct Hz as [Hz | ((b & kb') & Hb & Hz)]; [unfold pb in Hz; lia|].
        unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
        destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc' Lamc peakc cntc 0 b kb' (proj1 HJm) HLED (Id _ Hb))
          as (_ & _ & _ & Hbc & _). lia. }
    intros W' c' _ Hpost. rewrite HF.
    eapply apost_base_xF_R_lift; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)|].
    apply (apost_base_x_F (fx := fxk)). all: first [exact HFZ | exact Hpost | idtac]. }
  (* back at R: the live state again, then the L3 facts, a0 = 1 *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJ2 HJ1 HAP2 HQ.
  rewrite HF in HJ1. try rewrite HF in HQ.
  destruct HQ as ((Hroom2 & Hres & Hna2 & Hnb2 & EHp & ES & EAB & HLED2) & HMN2).
  subst Hp2 S2.
  destruct (ct6_jkeep _ lyc Sc Hpc Wc memc mdc' ly2 Sc Hpc W2 mem2 md2 k1 HJ1 EAB) as (KST & KFR & KBL & KIMG).
  pose proof HJ1 as (_ & HLY1 & _).
  assert (EFA : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos).
  { destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc memc mdc' ly2 (proj1 HJm) HLY1) as (_ & Efa2 & _). apply Efa2. }
  pose proof (crt_live_lam_perm HL) as HPLc. pose proof (crt_live_blocks_perm HL) as HPBc.
  pose proof (crt_live_dx_apart HL) as HAPc.
  (* the caller's journal after same's call is at a budget WS2 with wbudget [] (prh_wk F_check_round_trip) WS2
     (cb7k_call's landing); cb4_live_call takes it packaged *)
  pose proof HJ2 as (WS2 & HJ2w & HB2).
  pose proof (ct6_side_after lyc Sc Hpc Wc memc mdc' kj pos _ Lamc peakc cntc ly2 Hpc W2 mem2 md2 (kj + k1) HLc HJ2w HLED2
    KFR KBL KIMG) as HSD2.
  pose proof (cb4_live_call B ARx ly S Hp W regs mem md ch doc t D Lam peak most LAWS HPRE lyc Sc Hpc Wc memc mdc'
    kj pos _ Lamc peakc cntc 0 0 _ [] ly2 Sc Hpc W2 mem2 md2 k1 _ Lamc peakc cntc 0 0 HLc HJ2 HJ1 (proj1 HSTK)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HSD2 HPLc ltac:(rewrite EAB; exact HPBc) HAPc HMN2) as HL2.
  pose proof (ct6_L3_after fxk fx' lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) ms cset saved kw
    i ly2 Hpc W2 mem2 md2 (kj + k1) regs2 HL3c HFZ2 HFK2 HL2 EFA HAP2 KST KFR KBL) as HL3n.
  apply (ct6_at_R HC i ms IH fx' ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dc Dback Lamc peakc cntc regs2 cset saved kw HL3n HPd).
  destruct Hres as [(_ & E1) | (Hne' & _)]; [|exfalso; exact (Hne' Hu)].
  rewrite E1. intros E. apply (f_equal (@bv_unsigned 64)) in E. unfold w64 in E.
  rewrite !unsigned_lit_small in E by lia. lia.
Qed.

(* ---- L3 (+0x5b4) -> the key compare: `__wrap_strcmp (back.keys[i], doc->keys[i])` at +0x648, back at K (+0x64c)
   with a0 = 0 (the read-back's key i is doc's key i) ---- *)
Lemma ct6_at_L3 : ATC -> forall i ms, (forall j, (i < j)%nat -> ATL3 j ms) -> ATL3 i ms.
Proof.
intros HC i ms IH fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw HL3 HPd.
destruct (ENT fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i
  (CRT_PC_B + CRT_L3_OFF_B) HL3)
  as (kb & kd & xb & xd & kib & kid & capb & capd & nm & u & u' & kxb & kxd & Db1 & Dd1 &
      Enth & Enth' & Hcb & Hcd & Hnb & Hnd & Lkib & Lkid & Hib & Hid & Ib & Id & Hn44 & SHOK & HSx).
pose proof (crt_at_L3_B_obj HL3) as Ht. pose proof (crt_at_L3_B_frm_zero HL3) as HFZ.
pose proof (crt_at_L3_B_fregs HL3) as HFK. pose proof (crt_at_L3_B_live HL3) as HL.
pose proof (crt_at_L3_B_bregs HL3) as HBR. pose proof (crt_at_L3_B_s5_i HL3) as R21.
pose proof (crt_at_L3_B_s8_i HL3) as R24. pose proof (crt_at_L3_B_s10_i HL3) as R26.
pose proof (crt_at_L3_B_s6_keys HL3) as R22. pose proof (crt_at_L3_B_sp_saved HL3) as SPsv.
pose proof (crt_at_L3_B_sp_shkids HL3) as SPshk. pose proof (crt_at_L3_B_sp_keys HL3) as SPkeys.
pose proof (crt_at_L3_B_sp_back HL3) as SPback. pose proof (crt_at_L3_B_sp_at HL3) as SPat.
pose proof (crt_at_L3_B_sp_kids HL3) as SPkids. pose proof (crt_at_L3_B_sp_shn HL3) as SPshn.
pose proof (crt_at_L3_B_sp_pn HL3) as SPpn. pose proof (crt_at_L3_B_doc_align HL3) as Hd8.
pose proof (crt_at_L3_B_doc_open HL3) as RAd. pose proof (crt_at_L3_B_back_open HL3) as RAb.
pose proof (crt_at_L3_B_v_open HL3) as RAv. pose proof (crt_at_L3_B_i_lt HL3) as Hi.
pose proof (crt_at_L3_B_cset_range HL3) as Hcs1. pose proof (crt_at_L3_B_cset_mod HL3) as Hcs2.
pose proof (crt_at_L3_B_cnt HL3) as Hcnt. pose proof (crt_at_L3_B_saved_nz HL3) as Hsv.
pose proof (crt_at_L3_B_copy HL3) as HTC. pose proof (crt_at_L3_B_copy_fd HL3) as HFD.
pose proof (crt_at_L3_B_back HL3) as HBK. pose proof (crt_at_L3_B_pos HL3) as HPOS.
pose proof (crt_at_L3_B_kw HL3) as Lkw. pose proof (crt_at_L3_B_back_tblk HL3) as Lbtb.
pose proof (crt_at_L3_B_back_fo HL3) as Lbfo. pose proof (crt_at_L3_B_copy_tblk HL3) as Lctb.
pose proof (crt_at_L3_B_copy_fo HL3) as Lcfo. pose proof (crt_at_L3_B_copy_depth HL3) as Ldep.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
set (mo := ct6_more doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i) in *.
destruct (ct6_env regs rg doc kb kd xb xd kib kid (Z.of_nat (length ms)) (Z.of_nat (cm_at ms)) i)
  as (E53 & E42 & E75 & E76).
fold mo in E53, E42, E75, E76. rewrite R21 in E53.
assert (E56 : ew (TEB regs rg mo) 56 = w64 (8 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 24%bv 24 eq_refl) R24).
assert (E58 : ew (TEB regs rg mo) 58 = w64 (56 * Z.of_nat i)) by exact (eq_trans (te_cur regs rg mo 26%bv 26 eq_refl) R26).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & _ & _).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof (crt_bregs_B_s11 HBR) as R27.
assert (E64 : ew (TEB regs rg mo) 64 = w64 doc) by exact (te_more_lt regs rg mo 0 ltac:(lia)).
assert (E59 : ew (TEB regs rg mo) 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
pose proof (Nat2Z.is_nonneg i) as Hi0.
unfold crt_cfg.
pose proof (HSx [] [] I I) as HS.
pose (RUN := @crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
paj_run_tok_x_inv RUN HS HJ SHOK HPM ct6_Bspan.
{ ct6_ro. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
pose proof HJ as HJm. rewrite HF in HJm, HPM.
set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
pose proof (ct6_live_md HL HJm HB_HJ) as HLc.
assert (HL3c : L3B fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) ms cset saved kw i).
{ refine {| crt_at_L3_B_obj := Ht; crt_at_L3_B_frm_zero := HFZ; crt_at_L3_B_fregs := HFK;
            crt_at_L3_B_live := HLc; crt_at_L3_B_bregs := _; crt_at_L3_B_s5_i := _;
            crt_at_L3_B_s8_i := _; crt_at_L3_B_s10_i := _; crt_at_L3_B_s6_keys := _;
            crt_at_L3_B_sp_saved := SPsv; crt_at_L3_B_sp_shkids := SPshk; crt_at_L3_B_sp_keys := SPkeys;
            crt_at_L3_B_sp_back := SPback; crt_at_L3_B_sp_at := SPat; crt_at_L3_B_sp_kids := SPkids;
            crt_at_L3_B_sp_shn := SPshn; crt_at_L3_B_sp_pn := SPpn; crt_at_L3_B_doc_align := Hd8;
            crt_at_L3_B_doc_open := RAd; crt_at_L3_B_back_open := RAb; crt_at_L3_B_v_open := RAv;
            crt_at_L3_B_i_lt := Hi; crt_at_L3_B_cset_range := Hcs1; crt_at_L3_B_cset_mod := Hcs2;
            crt_at_L3_B_cnt := Hcnt; crt_at_L3_B_saved_nz := Hsv; crt_at_L3_B_copy := HTC;
            crt_at_L3_B_copy_fd := HFD; crt_at_L3_B_back := HBK; crt_at_L3_B_pos := HPOS;
            crt_at_L3_B_kw := Lkw; crt_at_L3_B_back_tblk := Lbtb; crt_at_L3_B_back_fo := Lbfo;
            crt_at_L3_B_copy_tblk := Lctb; crt_at_L3_B_copy_fo := Lcfo; crt_at_L3_B_copy_depth := Ldep |}.
  { apply (ct6_bregs_eq regs rg _ _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
  { rewrite <- R21. ct6_keep HS. } { rewrite <- R24. ct6_keep HS. } { rewrite <- R26. ct6_keep HS. }
  { ct6_reg HS (22%bv : bv 5) Hr22; rewrite Hr22; unfold PJ_OFF_KEYS, w64.
    apply (ct6_shx_denot _ 64 32 doc E64 E59); lia. } }
pose proof (crt_at_L3_B_bregs HL3c) as HBRc.
pose proof (crt_bregs_B_sp HBRc) as R2c. pose proof (crt_bregs_B_gp HBRc) as R3c. pose proof (crt_bregs_B_tp HBRc) as R4c.
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
assert (Hsp1 : spZ (ms_regs ms0) = sp1) by (unfold spZ; rewrite R2c; unfold w64; apply unsigned_lit_small; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
(* the two key strings: heap strings of the ledger, both nm *)
destruct (@cb7t_str_prem rc prh_img_B B_prog_listing PA B ARx LAWS lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ 0 most 0
  lyc Sc Hpc Wc memc mdc' (ms_regs ms0) xb kxb nm HLED (proj1 HJm) eq_refl eq_refl Hcb ltac:(rewrite Hsp1; lia))
  as (Xb0 & Xb1 & Xb2 & Xb3 & Xbfb & Xbsrc & Xblo & Xbam & Xbra & Xbhv & Xbtl).
destruct (@cb7t_str_prem rc prh_img_B B_prog_listing PA B ARx LAWS lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ 0 most 0
  lyc Sc Hpc Wc memc mdc' (ms_regs ms0) xd kxd nm HLED (proj1 HJm) eq_refl eq_refl Hcd ltac:(rewrite Hsp1; lia))
  as (Xd0 & Xd1 & Xd2 & Xd3 & Xdfb & Xdsrc & Xdlo & Xdam & Xdra & Xdhv & Xdtl).
assert (E69 : ew (TEB regs rg mo) 69 = w64 xb) by exact (te_more_lt regs rg mo 5 ltac:(lia)).
assert (E70 : ew (TEB regs rg mo) 70 = w64 xd) by exact (te_more_lt regs rg mo 6 ltac:(lia)).
ct6_reg HS (10%bv : bv 5) Q10. rewrite (ct6_denot_at _ 69 xb E69) in Q10 by lia.
ct6_reg HS (11%bv : bv 5) Q11. rewrite (ct6_denot_at _ 70 xd E70) in Q11 by lia.
destruct (cb7k_ret CRT_K_OFF6R_B ltac:(unfold CRT_K_OFF6R_B; lia) ltac:(reflexivity)) as (Hr1 & Hr2 & Hr3).
ct6_reg HS (1%bv : bv 5) Q1.
assert (E240 : ew (TEB regs rg mo) 240 = Z_to_bv 64 BASE)
  by exact (te_img (L := B_prog_listing) (PA := PA) regs rg mo 240 ltac:(vm_compute; lia)).
lazymatch type of Q1 with context [SOff 240 ?c] =>
  replace c with (CRT_PC_B + CRT_K_OFF6R_B) in Q1 by (vm_compute; reflexivity) end.
assert (HPC : 0 <= CRT_PC_B < 2 ^ 16) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
assert (HBS : 4096 <= BASE < 2 ^ 30) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
rewrite (ct6_denot_off _ 240 _ BASE E240) in Q1 by (unfold CRT_K_OFF6R_B; lia).
pose proof HPRE as ((_ & _ & _ & Hgp & Htp & _) & _).
assert (Q3 : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite R3c; exact Hgp).
assert (Q4 : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite R4c; exact Htp).
assert (Hstkc : STKC = 27632) by (vm_compute; reflexivity).
pose proof (crt_side_arodata (crt_live_side HL)) as HROc.
pmkst HS. rewrite HF.
(* strcmp's rule over the R journal (the engine's YGcallMxmn.aj_strcmp_at_xromR): the journal
   rebased to the current depot (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its budget after it
   (YCbqGwild.ajournal_xw_unbase0R), as the A' twin Crt102Loops.cl_strcmp_call does; the plain SRr conclusion is lifted
   by YA0nH.SRr_SRr' under YSRrG.SRr'_bind *)
pose proof (crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm) as Hinc.
pose proof HJm as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply YA0nH.SRr_SRr'.
  refine (YGcallMxmn.aj_strcmp_at_xromR (SK := SK) SEGS B PST ARx RLO RHI LAWS (@pa_segs_low rc B_prog_listing PA) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___wrap_strcmp) (ASTRCMP fxk) Wc (ms_regs ms0) memc STKC sp0 [] ly (set_depot (st_depot Sc) S) Hp W mem md
    [(CRT_CID, pos)]
    lyc Sc Hpc mdc' kj xb xd (Z.of_nat (length nm)) (Z.of_nat (length nm)) (sp1 - sp0) _ HJr Q10 Q11
    _ _ _ _ _ _ _ _ _ _ _ _ Q3 Q4 Q1 _ Xbfb Xdfb Xbsrc Xdsrc _ _ Xbam Xdam Xbra Xbhv Xdra Xdhv Xbtl Xdtl HROc).
  all: try lia.
  all: first [ (apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2])
             | (intros a Ha; pose proof (Xblo a Ha); lia)
             | (intros a Ha; pose proof (Xdlo a Ha); lia) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & HMN2).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ3; [|exact Hinc].
destruct (ct6_live_keep lyc Sc Hpc Wc memc mdc' kj pos _ Lamc peakc cntc mem2 md2
  (fun a => sp1 - 2 * ESTACK <= a < sp1) HLc HJ3 HB_HJ ltac:(intros a Ha; cbv beta in Ha; lia)
  ltac:(intros a Ha Hn; cbv beta in Hn; apply Hfr2; [exact Ha | replace (sp0 + (sp1 - sp0)) with sp1 by lia; exact Hn])
  Hpres2 (fun H0 => HMN2 H0)) as (HL2 & KST & KFR & KBL).
pose proof (ct6_L3_after fxk fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms0) ms cset saved kw
  i lyc Hpc Wc mem2 md2 kj regs2 HL3c HFZ ltac:(intros r Hr; reflexivity) HL2 eq_refl HP2 KST KFR KBL) as HL3n.
change (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_K_OFF6R_B regs2 mem2 md2) QFb).
apply (ct6_at_K HC i ms IH fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Dback Lamc peakc cntc regs2 cset saved kw HL3n HPd).
rewrite Hv. apply Hcmp. split; [reflexivity|]. intros j Hj.
destruct Hcb as (_ & _ & _ & _ & Gb). destruct Hcd as (_ & _ & _ & _ & Gd).
assert (Hj' : (Z.to_nat j < length (nm ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (cb7t_garr8_at SEGS (w_H Wc) memc xb (nm ++ [0]) (Z.to_nat j) Gb Hj') as A1.
pose proof (cb7t_garr8_at SEGS (w_H Wc) memc xd (nm ++ [0]) (Z.to_nat j) Gd Hj') as A2.
rewrite Z2Nat.id in A1, A2 by lia. rewrite A1, A2. reflexivity.
Qed.

Lemma ct6_all : ATC -> forall i ms, ATL3 i ms.
Proof.
intros HC.
assert (Hall : forall d i ms, (length ms - i <= d)%nat -> ATL3 i ms).
{ induction d as [|d IHd]; intros i ms Hd.
  - intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw HL3 _. exfalso.
    pose proof (crt_at_L3_B_i_lt HL3) as Hi. lia.
  - apply (ct6_at_L3 HC i ms). intros j Hj. apply IHd. lia. }
intros i ms. exact (Hall _ i ms (le_n _)).
Qed.
End p.

(* ======================================================================================================== *)
(* ROW T6 (CRT-B-L3): the frozen seam statement CRT_B_SEG_T6 (lib/A/Prog/Crt102Glue.v) at the B' instance (PA :=
   PI_prog_B, CRT_PC := CRT_PC_B and Crt102Img.v's cut offsets), under tcheck_round_trip_specX's premises at the entry
   and the two callee texts. By induction on doc->n - i: each pass L3 -> strcmp -> K -> (same -> R ->) M -> L3 / C. *)
Theorem crtB_T6 : CRT_B_SEG_T6 (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (CRT_PC := CRT_PC_B) (CRT_C_OFF := CRT_C_OFF_B) (CRT_L3_OFF := CRT_L3_OFF_B) (B := B) (ARx := ARx)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt)
  (ran := ran) (most := most).
Proof.
intros HC fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i HL3.
exact (ct6_all (fun _ _ _ _ => True)
  (fun fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw H _ =>
     HC fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw H)
  i ms fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw HL3 I).
Qed.

End g.
End f.
End t6w.
