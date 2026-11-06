(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: two lemmas of pj_set's image-B walk (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of
   lib/B/Prog/pj_set_defs.v), the twins of pj_parse's lane PjSegEp.
   proves no function (kind: segment lemma).
   (1) pjs_seg_epi_holds: the epilogue from the cut pjs_EPI (+0x88): `ld ra, 40(sp); ld s0, 32(sp); ld s1, 24(sp);
       ld s2, 16(sp); ld s3, 8(sp); ld s4, 0(sp); addi sp, sp, 48; ret`. The symbolic state at the cut (pjs_st_ok)
       has one READ-ONLY region, pj_set's 48-byte frame at sp (atom 2), whose six chunks hold the entry's ra, s0,
       s1, s2, s3 and s4 as the extra atoms 32 .. 37 (pjs_invR's six val_mem facts). The cut is after pj_set's
       frees, so its journal is at the re-hiding relation WLE' (YA0nH.wle' over preset's zone): the runner is the R
       runner (YC1fPx paj_run_xR at WLE', reflexive and transitive by wle'_refl / wle'_trans), which runs the six
       loads and the addi and stops at the ret; the ret is YC1fP's paj_ret_at, an SRr fact lifted into WLE' by
       YA0nH.SRr_SRrG with wle_wle'. The journal from the entry is pjs_invR's, unchanged by the run (the region has
       an empty write range, so the memory is the cut's); the window clause is pjs_invR's; the callee-saved
       registers are sp = sp1 + 48 = sp0, the five restored ones and PJS_KEPT untouched; pjs_Q is pjs_EPI's (a0
       untouched); the goal is pjs_FIN = fpostWmR at WLE', and fQmn's keep `memnorm mem0 -> memnorm mem'` is
       pjs_invR's last conjunct (mem' is the cut's memory).
   (2) pjs_frame_kept_holdsR: what a program call keeps of pj_set's state, at the one callee window this walk uses
       (e1 = 48 + d, the widest aj_call_xW allows at o = - 48 - d), with both journals at any world relation R: the
       callee's extension clause keeps every byte of [sp1, sp0 + d) outside its footprint, which gives the caller
       window and the six saved registers; the journal's presence clause gives the frame's presence (its window
       [sp1 - STK1, sp0 + d) covers [sp1, sp0)); the read-only view is the journal's image clause (prh_pst is not
       read-only, S1ImgB.v pst_not_ro_B). pjs_frame_kept_holds is its instance at wle.
   Numerals: 0 / 8 / 16 / 24 / 32 / 40 / 48 (LENGTH: the frame's slot offsets and its size); 2 ^ 46 / 2 ^ 47
   (DERIVED: the stack band); atom indices 2 / 32 .. 37 (DERIVED: the engine's numbering). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_set_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Existing Instance prh_img_B.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at pjs_EPI: the frame [sp, sp + 48) read-only, the six saved registers as atoms 32 .. 37 ---- *)
Definition PJSE_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) 0 48 0 0
      [YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0));
       YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
       YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0))] ].
Definition PJSE_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition PJSE_ss : sstate := mkSS PJS_EPI sr_atoms PJSE_regions None PJSE_facts.
Definition PJSE_Bx : sv := SOff 38 0.
Definition PJSE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PJSE_SH : list shent := [].
Definition PJSE_extra (r0 : bvmap 5 word) : list word :=
  [getr r0 1; getr r0 8; getr r0 9; getr r0 18; getr r0 19; getr r0 20].

Ltac pjse_inkept := unfold PJS_KEPT; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).

Section ep. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the allocator laws (lib/Reusable/YCbqG.v AR_laws_x), the engine's premise *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* pjs_Q reads the registers only through a0 and never reads the model *)
Lemma pjse_Q_a0 : forall en ly S Hp (W : world SEGS) regs regs' mem md md',
  getr regs' 10 = getr regs 10 ->
  pjs_Q B en ly S Hp W regs mem md -> pjs_Q B en ly S Hp W regs' mem md'.
Proof.
  intros en ly S Hp W regs regs' mem md md' E10 [HR (Lam' & peak' & fail' & ran' & res & c & ok & Lr & Do & H)].
  split; [exact HR|]. exists Lam', peak', fail', ran', res, c, ok, Lr, Do. rewrite E10. exact H.
Qed.

(* ---- (2) the keep statement, at any world relation R (no conjunct read below is the journal's world conjunct) ---- *)
Theorem pjs_frame_kept_holdsR : forall R dd, pjs_frame_kept_stmtR B ARx R dd.
Proof.
  intros R dd en ly S Hp W regs mem md k STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 HINV HJ1 HX HFPfr HFPwin
    HSTK1 Hd Hsink.
  destruct HINV as (HJ0 & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & _ & _ & _ & _ & HPRES & HROD & _).
  pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_ly HJ1) as Hly1. pose proof (ajxR_img HJ1) as F3. pose proof (ajxR_pres HJ1) as Hpres1. pose proof (ajxR_stk HJ1) as Hast1. clear HJ1.
  pose proof (@pa_segs_low _ _ PA) as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold js_sp1, PJS_FR in *.
  set (sp0 := js_sp0 en) in *.
  assert (KF : forall a, sp0 - 48 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply HX; [lia | exact (HFPfr a Ha)]).
  assert (KV : forall p n v, val_mem SEGS (mrestrict (w_H W) mem) p n v -> sp0 - 48 <= p -> p + Z.of_nat n <= sp0 ->
    val_mem SEGS (mrestrict (w_H W2) mem2) p n v).
  { intros p n v Hv Hlo Hhi kk Hk.
    rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 _ (KF (p + Z.of_nat kk) ltac:(lia))). exact (Hv kk Hk). }
  split.
  { intros a Ha Hfp. rewrite (HX a ltac:(lia) (HFPwin a Ha Hfp)). exact (HWIN a Ha Hfp). }
  split; [exact (KV _ 8%nat _ Hra ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
  split; [exact (KV _ 8%nat _ Hs0 ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
  split; [exact (KV _ 8%nat _ Hs1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
  split; [exact (KV _ 8%nat _ Hs2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
  split; [exact (KV _ 8%nat _ Hs3 ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
  split; [exact (KV _ 8%nat _ Hs4 ltac:(lia) ltac:(cbn [Z.of_nat]; lia))|].
  split.
  { intros a Ha. apply Hpres1. lia. }
  intros a Hro Hos Her.
  rewrite (F3 a); [exact (HROD a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsink].
  - destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
  - intros Hp'. exact (pst_not_ro_B a Hp' Hro).
Qed.
Theorem pjs_frame_kept_holds : forall dd, pjs_frame_kept_stmt B ARx dd.
Proof. intros dd. rewrite pjs_frame_kept_stmt_R_wle. exact (pjs_frame_kept_holdsR (@wle SEGS) dd). Qed.

(* ---- (1) the epilogue segment ---- *)
(* the symbolic state at the cut *)
Lemma pjs_st_ok : forall (W : world SEGS) mem (regs r0 : bvmap 5 word),
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 40) 8 (raZ r0) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 32) 8 (s0Z r0) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 24) 8 (bv_unsigned (getr r0 9)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 16) 8 (bv_unsigned (getr r0 18)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 8) 8 (bv_unsigned (getr r0 19)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs) 8 (bv_unsigned (getr r0 20)) ->
  st_ok_pi (fx := fx) SEGS VAL (Eimg (PI := PA) (Ereg regs (PJSE_extra r0))) PJSE_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + PJS_EPI)) mem (seg_rom SEGS))).
Proof.
  intros W mem regs r0 Hsp Hal Vra Vs0 V9 V18 V19 V20.
  set (E := Eimg (PI := PA) (Ereg regs (PJSE_extra r0))).
  assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (PJSE_extra r0)) i)
    by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = getr r0 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = getr r0 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = getr r0 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = getr r0 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = getr r0 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (E37 : ew E 37 = getr r0 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  rewrite (restrict_mkst_fx (fx := fx)). unfold PJSE_ss.
  apply (pa_entry_st_ok_full (fx := fx) (PI := PA)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold PJSE_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (constructor; [|]).
    + apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 (SOff 37 0) (bv_unsigned (getr r0 20))).
      * cbn [sv_denot]. rewrite E37, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
      * cbn. lia.
      * rewrite Z.add_0_r. exact V20.
    + apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 (SOff 36 0) (bv_unsigned (getr r0 19))).
      * cbn [sv_denot]. rewrite E36, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
      * cbn. lia.
      * exact V19.
    + apply (chunk_ok_val SEGS E _ (spZ regs) 16 8 (SOff 35 0) (bv_unsigned (getr r0 18))).
      * cbn [sv_denot]. rewrite E35, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
      * cbn. lia.
      * exact V18.
    + apply (chunk_ok_val SEGS E _ (spZ regs) 24 8 (SOff 34 0) (bv_unsigned (getr r0 9))).
      * cbn [sv_denot]. rewrite E34, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply u64_range.
      * cbn. lia.
      * exact V9.
    + apply (chunk_ok_val SEGS E _ (spZ regs) 32 8 (SOff 33 0) (s0Z r0)).
      * cbn [sv_denot]. rewrite E33, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold s0Z. apply u64_range.
      * cbn. lia.
      * exact Vs0.
    + apply (chunk_ok_val SEGS E _ (spZ regs) 40 8 (SOff 32 0) (raZ r0)).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold raZ. apply u64_range.
      * cbn. lia.
      * exact Vra.
    + apply Forall_nil.
  - cbn [PJSE_regions pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [PJSE_facts f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia].
Qed.

Theorem pjs_seg_epi_holds : forall CTX0 dd, pjs_seg_epi B ARx CTX0 dd.
Proof.
  intros CTX0 dd en ly S Hp W regs mem md k HPRE [HINV HQ].
  pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & _ & _ & _ & HKEPT & _ & _ & HMN).
  unfold pjs_pre in HPRE. cbv zeta in HPRE.
  destruct HPRE as ((HAFN & _ & _) & _).
  pose proof HAFN as (_ & Hret & _ & _ & _ & Hstk & _ & _ & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (@pa_segs_low _ _ PA) as Hsegs.
  assert (HSTK : 48 <= STK_pj_set dd).
  { unfold STK_pj_set, zmaxl. cbn [fold_right].
    replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
  unfold js_sp1, js_sp0, PJS_FR in *.
  assert (Hsp1 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  assert (Hal1 : spZ regs mod 16 = 0) by (rewrite Hsp; Z.div_mod_to_equations; lia).
  pose proof (pjs_st_ok W mem regs (js_regs en) Hsp1 Hal1
    ltac:(rewrite Hsp; exact Hra) ltac:(rewrite Hsp; exact Hs0) ltac:(rewrite Hsp; exact Hs1)
    ltac:(rewrite Hsp; exact Hs2) ltac:(rewrite Hsp; exact Hs3) ltac:(rewrite Hsp; exact Hs4)) as HS.
  set (E := Eimg (PI := PA) (Ereg regs (PJSE_extra (js_regs en)))) in HS.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (PJSE_extra (js_regs en))) i)
    by (intros i Hi; unfold E; apply Eimg_low; exact Hi).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
  assert (E32 : ew E 32 = getr (js_regs en) 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = getr (js_regs en) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = getr (js_regs en) 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = getr (js_regs en) 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = getr (js_regs en) 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (E37 : ew E 37 = getr (js_regs en) 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (PJSE_extra (js_regs en))) E)
    by (split; [intros n Hn; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (SHOK : sh_ok SEGS PJSE_Bx PJSE_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok, PJSE_SH; apply Forall_nil).
  clearbody E.
  unfold pjs_cfg, YA0nH.SRr'.
  (* the R runner at WLE' (its two laws, YA0nH.wle'_refl / wle'_trans) *)
  pose (RUN := paj_run_xR (fx := fx) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS
    (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RET := paj_ret_at (fx := fx) (PL := PL) (PI := PA)).
  (* +0x88 .. +0xa0: the six loads and the addi; the runner stops at the ret (+0xa4) *)
  paj_run_tok_xR RUN HS HJ SHOK PJSE_Bspan.
  { unfold awr_ok. intros a (r & Hin & Ha). unfold PJSE_ss, PJSE_regions in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  (* the run stored nothing: the memory is the cut's *)
  assert (MM : ms_mem ms = mem).
  { apply functional_extensionality. intros x. apply HF. intros (r & Hin & Ha).
    unfold PJSE_ss, PJSE_regions in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8.
  prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10. prreg HS (18%bv : bv 5) R18.
  prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
  assert (KR : forall r, In r PJS_KEPT -> getr (ms_regs ms) r = getr (js_regs en) r).
  { intros r Hr. rewrite <- (HKEPT r Hr).
    exact (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs (PJSE_extra (js_regs en)) PJS_KEPT HS HAE
      ltac:(vm_compute; reflexivity) r Hr). }
  (* +0xa4: the ret, to the entry's ra: an SRr fact, lifted into WLE' (YA0nH.SRr_SRrG with wle_wle') *)
  apply (YA0nH.SRr_SRrG SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold pjs_FIN, fpostWmR, fpostWR, fQmn.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (YK11.mkst ?r _ ?m _) ?dm = _ /\ _ =>
    exists ly, S, Hp, r, m, dm, k end.
  split.
  { unfold YK0s.ret_ok in Hret. rewrite R1, E32, Hret. reflexivity. }
  split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs
            (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)); exact HJ|].
  split; [intros a Ha Hfp; rewrite MM; exact (HWIN a Ha Hfp)|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R2, Usp, Hsp. replace (spZ (js_regs en) - 48 + 48) with (spZ (js_regs en)) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - apply KR. pjse_inkept.
    - apply KR. pjse_inkept.
    - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8, E33. reflexivity.
    - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9, E34. reflexivity.
    - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [-> | [-> | [-> | Hr'']]].
      + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18, E35. reflexivity.
      + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19, E36. reflexivity.
      + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20, E37. reflexivity.
      + destruct Hr'' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; apply KR; pjse_inkept. }
  rewrite MM. split; [|exact HMN].
  apply (pjse_Q_a0 en ly S Hp W regs _ mem md _); [rewrite R10, E10; reflexivity | exact HQ].
Qed.

End ep.
