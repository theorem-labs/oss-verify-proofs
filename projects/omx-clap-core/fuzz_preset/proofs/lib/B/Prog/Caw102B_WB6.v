(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Disp_word.v, with its module paths and module names changed; 116 of its 154 lines of code are new or changed and 465 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_Kit.v, with its module paths and module names changed; 281 of its 334 lines of code are new or changed and 101 lines of the source are left out. *)
(* fuzz_preset, image B' (#102): check_as_written's End segment WB6 (B' 0x82058 -> ret 0x82070: `mv a0, s1`, the four
   restores, `addi sp, sp, 0x50`, `ret`) from cut_end to the text's post caw_post (Caw102B.v). Lane CawB102; re-proved by
   the #102 re-walk, B'; re-fitted to the re-keyed base by that re-walk.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   BASE OF RECORD: the kit's cut of the #102 batch, preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (the cut + this row's caw
   B' files; prepared at preset-tree-at-2026-10-30T02-53-02Z.tsv (sha256 477c088a7ad3; internal record) on the batch tip preset-tree-at-2026-10-30T02-01-18Z.tsv (sha256 a12cae64b2b5; internal record)), this row's lib/B/Prog/Caw102B.v
   (statements of blob 5a8082469eb1, unchanged here); the cut's kit texts by path: PRH_Base.v
   ef7c8ca98529 (prh_run_at, prh_cons_from), PRH_FnCheck.v c40cf3fdcd2a, whose tcheck_as_written_specX post body
   :874-902 is caw_post's body caw_Q, verbatim at the record (no text is called in this segment); the P'' journal of
   lib/Reusable/YCbqG.v 219748197d6b (carried, materialized by ajournal_x_materialize, read by Caw102B.caw_J_keep).
   WHAT CHANGED (on that batch base) and WHY: (1) the batch text has no run-word list DW (the base
   dropped cawB's c_DW; never read here); (2) it takes the ROOM COUNTS as entry premises after room_live_cf
   (:862-863), so caw_pre now has 27 conjuncts (with the hull budget and HPOS that follow them, Caw102B.v:139-165) and is read BY NAME: fpre is the base's projection caw_pre_fpre (formerly a
   positional destruct); (3) THE OUTCOME (:879-888), a new post conjunct of caw_Q right after `exists r, getr regs'
   10 = w64 r /\`: for any run position i at the ENTRY state whose next events are the scratch pair and whose
   allocation is a consumer event (prh_cons_from .. i 2), r = 0 and S' is the position i + 2. cut_end's r = 1 arm
   now carries the refused arm's exclusion caw_dead C (proved at WB1's NULL arm). HOW here: the destruct of cut_end's
   arms names the new conjunct (Hdead); on the r = 1 arm the outcome is refuted by Hdead (the text's list literal and
   its length are caw_evs C by conversion), on the r = 0 arm r = 0 is reflexivity and the position is the arm's
   progress fact caw_prog C (caw_evs C) S3 at S' := S3. caw_WB6's statement is unchanged.
   EARLIER (base Caw102B.v blob d5668ec173d5, kit text preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record)): that text's tcheck_as_written_specX binds no run position at entry (the
   post-implication form): cut_end's arms carry THE PROGRESS FACT caw_prog C [] S3 (r = 1 /\ own = 1) / caw_prog C
   (caw_evs C) S3 (r = 0 /\ own = 0), and caw_Q's arms are the text's position conjuncts `forall sm x0 os i H0 hist,
   iface_room_pos .. i .. (c_S C) -> prh_run_at .. i E -> exists hist', iface_room_pos .. (i + length E) .. S'` with
   E = [] / [HMal (size + 1); HFr (size + 1)], which IS caw_prog C E S' by conversion: each arm's caw_prog at S3
   closes its arm as it is (S' := S3). FRM0-ENTRY adds fpre's last conjunct frm_zero (fp_csr fx); this segment
   reads only fpre's afn_pre_x, and the post's frm_zero at the return float state is caw_base's first conjunct at fy.
   The room counts (caw_cnt C) are not read (no alloc / free step). caw_Q C is `room /\ Hp /\ ablocks /\ exists own',
   LEDGER .. most own' /\ bytes /\ exists r, a0 = r /\ THE OUTCOME /\ (the two arms, each with its progress fact)`.
   own' := cut_end's own, and the ledger and both progress facts come from cut_end at the return state: the epilogue
   loads and moves sp and writes no memory (HF, Emem: ms_mem ms = mem3), and the return keeps the world (paj_ret_at at
   W3), so W' = W3, mem' = mem3 and ly3 / S3 / Hp3 are cut_end's. Statements take the entry float state explicitly
   (fx := fx).
   SECTION HYPOTHESES: none. Variable B (the walk's asyms, an instance binding; owner the top, Caw102B_Top.v). The
   lemma premise srr_inv_laws SEGS P (owner: the top, which instantiates P). No named argument of this file's own.
   caw_WB6R, beside caw_WB6 (whose statement is unchanged): the same epilogue and return from cut_endR to caw_post at
   RW := YA0nH.wle' SEGS RZ_cf, the world relation past the scratch's free. The journal is caw_JR at RW; the run is
   YC1fPx.v's R runner paj_run_x_invR (RW is reflexive and transitive: YA0nH.wle'_refl / wle'_trans), the return
   YC1fP.paj_ret_at (an SRr fact) lifted into RW by YA0nH.SRr_SRrG with YA0nH.wle_wle'. caw_post is fpostF, the
   engine's apost_base_xFR at wle' = RW (PRH_Base.v), so the post's journal is the run's RW journal, materialized
   (ajournal_x_materializeR); the text's bytes and tree come from Caw102B.caw_J_keepR. Its premises are caw_WB6's.
   Generic P, abstract; call-free (srr_inv_laws only). The text's bytes and tree at the return
   come from the journal (Caw102B.caw_J_keep). Structure: H2CawR.v (the H2-H5 walk, blob
   134b752d22a2), old caw A's epilogue, re-stated at B' and over a generic P.
   Numerals: 48 / 56 / 64 / 72 (LENGTH: the restores' ld offsets), 80 (LENGTH: the frame), 33 .. 36 (DERIVED: the
   engine's extra atoms, 32 the shadow base), 2 ^ 46 / 2 ^ 47 (LENGTH: the stack atom's range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- a frame seat: the 80-byte frame at sp (atom 2), the words a run reads as atoms 33, 34, .. (atom 32 the shadow
   base), every register its own atom (H2CawBase.v's caw_fchunks / caw_st_ok over a generic PAImg) ---- *)
Fixpoint cawR_fchunks (k : nat) (offs : list (Z * N)) : list YP09.chunk :=
  match offs with
  | [] => []
  | (o, w) :: r => YP09.mkChunk o (CVal w (SOff k 0)) :: cawR_fchunks (S k) r
  end.
Definition cawR_fregion (offs : list (Z * N)) : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 CAWB_FRAME 0 0 (cawR_fchunks 33 offs).

Section bld. Context {fz : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGSz := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VALz := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASEz := (@pa_val _ B_prog_listing PA A_TEXT).
Definition cawR_E (regs : bvmap 5 word) (vals : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs (map (Z_to_bv 64) (SHADOW_OFF :: vals))).
Fixpoint cawR_vals_ok (m : word -> option byte) (sp : Z) (offs : list (Z * N)) (vals : list Z) : Prop :=
  match offs, vals with
  | [], [] => True
  | (o, w) :: r, v :: vs =>
      val_mem SEGSz m (sp + o) (N.to_nat w) v /\ 0 <= v < 2 ^ (8 * Z.of_N w) /\ Z.of_N w <= 8 /\
      cawR_vals_ok m sp r vs
  | _, _ => False
  end.
Lemma cawR_E_reg : forall regs vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cawR_E regs vals) n = getr regs r.
Proof.
intros regs vals n r Hn. pose proof (u5_range r) as Hr. unfold cawR_E.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma cawR_E_val : forall regs vals i, (i < 200)%nat -> ew (cawR_E regs vals) (33 + i) = Z_to_bv 64 (nth i vals 0).
Proof.
intros regs vals i Hi. unfold cawR_E. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra.
change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma cawR_fchunks_ok : forall E m sp offs vals k,
  (forall i, (i < length offs)%nat -> ew E (k + i) = Z_to_bv 64 (nth i vals 0)) ->
  cawR_vals_ok m sp offs vals -> Forall (YP09.chunk_ok SEGSz E m sp) (cawR_fchunks k offs).
Proof.
intros E m sp offs. induction offs as [|[o w] r IH]; intros vals k He Hv; [constructor|].
destruct vals as [|v vs]; [destruct Hv|]. destruct Hv as (Hm & Hr & Hw & Hv).
constructor.
- apply (chunk_ok_val SEGSz E m sp o w (SOff k 0) v); [| exact Hr | exact Hw | exact Hm].
  cbn [sv_denot]. specialize (He 0%nat ltac:(cbn; lia)). rewrite Nat.add_0_r in He. rewrite He.
  cbn [nth]. rewrite Z.add_0_r, unsigned_lit_small by (split; [lia|]; apply (Z.lt_le_trans _ _ _ (proj2 Hr)); apply Z.pow_le_mono_r; lia).
  reflexivity.
- apply (IH vs (S k)); [| exact Hv].
  intros i Hi. specialize (He (S i) ltac:(cbn; lia)). rewrite <- Nat.add_succ_comm in He. exact He.
Qed.
Lemma cawR_st_ok : forall (W : world SEGSz) regs mem pc offs vals G,
  regions_wf [cawR_fregion offs] = true -> (length offs <= 100)%nat ->
  0 <= spZ regs -> spZ regs + CAWB_FRAME <= 2 ^ 64 ->
  cawR_vals_ok (mrestrict (w_H W) mem) (spZ regs) offs vals ->
  facts_ok (cawR_E regs vals) G ->
  st_ok_pi SEGSz VALz (cawR_E regs vals) (mkSS pc sr_atoms [cawR_fregion offs] None G)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASEz + pc)) mem (YK11.seg_rom SEGSz))).
Proof.
intros W regs mem pc offs vals G Hwf Hlen Hsp0 Hsp1 Hvals HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold cawR_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- assert (Hb : base_val (cawR_E regs vals) (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite (cawR_E_reg regs vals 2 2%bv eq_refl); reflexivity).
  constructor; [|constructor]. unfold region_ok, cawR_fregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [lia|]. split; [unfold CAWB_FRAME in *; lia|]. split; [intros o Ho; lia|].
  apply (cawR_fchunks_ok _ _ _ offs vals 33); [| exact Hvals].
  intros i Hi. apply cawR_E_val. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
End bld.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation STK := (STK_check_as_written (PI := prh_img_B)).

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B).

Definition cawR_offs : list (Z * N) := [(48, 8%N); (56, 8%N); (64, 8%N); (72, 8%N)].
Definition cawR_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46 - 80) (2 ^ 47) 4)] [] [].

(* WB6 End: from cut_end, the epilogue and the return give the text's post at cut_end's own, P kept *)
Lemma caw_WB6 : forall C P, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C -> caw_K_end_post (fx := fx) B C P.
Proof.
intros C P PLAW Hpre fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r Hcut HPM.
destruct Hcut as (Hbase & R9 & Hr & Eab & HL).
destruct Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as [HPRE HROD].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold c_sp in *. unfold CAWB_FRAME in Hsp.
assert (Rsp : 2 ^ 46 <= spZ (c_regs C) <= 2 ^ 47) by lia.
destruct HSV as (V1 & V8 & V9 & V18).
set (vals := [bv_unsigned (getr (c_regs C) 18); bv_unsigned (getr (c_regs C) 9);
              bv_unsigned (getr (c_regs C) 8); bv_unsigned (getr (c_regs C) 1)]).
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 18)) as R18.
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 9)) as R9'.
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 8)) as R8'.
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 1)) as R1.
unfold bv_modulus in R18, R9', R8', R1. change (2 ^ Z.of_N 64) with (2 ^ 64) in R18, R9', R8', R1.
assert (HS : st_ok_pi (fx := fy) SEGS VAL (cawR_E regs3 vals)
  (mkSS (AF_cawB + CAWB_END) sr_atoms [cawR_fregion cawR_offs] None cawR_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_END))) mem3 (YK11.seg_rom SEGS)))).
{ apply cawR_st_ok.
  - vm_compute. reflexivity.
  - cbn. lia.
  - lia.
  - unfold CAWB_FRAME. lia.
  - cbn [cawR_vals_ok cawR_offs vals]. rewrite Hsp.
    replace (spZ (c_regs C) - 80 + 48) with (spZ (c_regs C) - 32) by lia.
    replace (spZ (c_regs C) - 80 + 56) with (spZ (c_regs C) - 24) by lia.
    replace (spZ (c_regs C) - 80 + 64) with (spZ (c_regs C) - 16) by lia.
    replace (spZ (c_regs C) - 80 + 72) with (spZ (c_regs C) - 8) by lia.
    change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8. change (N.to_nat 8) with 8%nat.
    repeat split; try assumption; lia.
  - unfold facts_ok, cawR_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (cawR_E_reg regs3 vals 2 2%bv eq_refl). fold (spZ regs3). rewrite Hsp.
    change (2 ^ 4) with 16. split; [lia|]. split; [rewrite Zminus_mod, Hal16; reflexivity | lia]. }
set (E := cawR_E regs3 vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawR_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := @paj_run_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RET := @paj_ret_at fy rc B_prog_listing PL_caw_B PA).
unfold caw_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
assert (Emem : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hin & Hrg). cbn in Hin.
  destruct Hin as [<- | []]. cbn in Hrg. lia. }
assert (E33 : ew E 33 = getr (c_regs C) 18)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 0 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E34 : ew E 34 = getr (c_regs C) 9)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 1 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E35 : ew E 35 = getr (c_regs C) 8)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 2 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E36 : ew E 36 = getr (c_regs C) 1)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 3 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E9 : ew E 9 = getr regs3 9) by (subst E; exact (cawR_E_reg regs3 vals 9 9%bv eq_refl)).
assert (E2 : bv_unsigned (ew E 2) = spZ regs3) by (subst E; rewrite (cawR_E_reg regs3 vals 2 2%bv eq_refl); reflexivity).
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (10%bv : bv 5) Q10.
rewrite E36 in Q1. rewrite E35 in Q8. rewrite E34 in Q9. rewrite E33 in Q18. rewrite E9, R9 in Q10.
rewrite E2, Hsp in Q2. replace (spZ (c_regs C) - 80 + 80) with (spZ (c_regs C)) in Q2 by lia.
assert (HKP : forall rr, In rr [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) rr = getr regs3 rr).
{ eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E _ (restrict (w_H W3) ms) regs3
    (map (Z_to_bv 64) (SHADOW_OFF :: vals))); [exact HS | | vm_compute; reflexivity].
  subst E. unfold cawR_E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [cfg_ms]. split; [|exact HPM]. rewrite Emem.
unfold caw_post, fpostF.
apply apost_base_xF_R_lift; [exact (YA0nH.wle_wle' _ _)|].
unfold apost_base_xF.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ =>
  exists fy, ly3, S3, Hp3, rg, m, d, k end.
split; [cbn [ms_regs]; rewrite Q1; rewrite Hra; reflexivity|].
split; [exact Hfz|]. split; [exact Hfk|].
split; [rewrite <- Emem; apply (ajournal_x_materialize (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split.
{ apply caw_aregs. intros rr Hrr. cbn [In] in Hrr.
  destruct Hrr as [<- | [<- | [<- | [<- | [<- | [<- | Hrr]]]]]].
  - rewrite Q2. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite HKP by (left; reflexivity). apply Hk. left; reflexivity.
  - rewrite HKP by (right; left; reflexivity). apply Hk. right; left; reflexivity.
  - exact Q8.
  - exact Q9.
  - exact Q18.
  - assert (Hr' : In rr [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (right; right; exact Hrr).
    rewrite (HKP rr Hr'). exact (Hk rr Hr'). }
destruct (caw_J_keep B C ly3 S3 Hp3 W3 (ms_mem ms) _ k Hpre HJ ltac:(intros x Hx; rewrite Eab; exact Hx)) as [HBY HTR].
rewrite Emem in HBY, HTR.
unfold caw_Q.
(* the ledger at own, THE OUTCOME and the progress fact per arm: cut_end's, at W3 / mem3 (the return state's world and
   memory). On the r = 1 arm the outcome's hypotheses contradict caw_dead C (the text's list literal and its length
   are caw_evs C by conversion); on the r = 0 arm r = 0 holds and the position is the arm's caw_prog C (caw_evs C) S3.
   Each arm's caw_prog C E S3 is the post's position conjunct at S' := S3 by conversion *)
split; [exact HROOM|].
split; [exact EHp|]. split; [exact Eab|].
exists own. split; [exact HL|]. split; [exact HBY|].
exists r. split; [cbn [ms_regs]; exact Q10|].
destruct Hr as [(-> & -> & Hrp & Hdead) | (-> & -> & Hrp)].
- split.
  + intros sm x0 os i H0 hist Hpos Hrun Hcons. exfalso. exact (Hdead sm x0 os i H0 hist Hpos Hrun Hcons).
  + left. split; [reflexivity|]. split; [reflexivity | exact Hrp].
- split.
  + intros sm x0 os i H0 hist Hpos Hrun Hcons. split; [reflexivity | exact (Hrp sm x0 os i H0 hist Hpos Hrun)].
  + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrp | exact HTR].
Qed.

(* the world relation past the scratch's free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* caw_WB6 over RW: cut_endR's journal is at RW, the run is the R runner, the return an SRr step lifted into RW, the
   post (fpostF at wle' = RW) takes the run's RW journal as it is *)
Lemma caw_WB6R : forall C P, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C ->
  caw_K_end_postR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P.
Proof.
intros C P PLAW Hpre fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r Hcut HPM.
destruct Hcut as (Hbase & R9 & Hr & Eab & HL).
destruct Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
unfold caw_JR in HJ.
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as [HPRE HROD].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold c_sp in *. unfold CAWB_FRAME in Hsp.
assert (Rsp : 2 ^ 46 <= spZ (c_regs C) <= 2 ^ 47) by lia.
destruct HSV as (V1 & V8 & V9 & V18).
set (vals := [bv_unsigned (getr (c_regs C) 18); bv_unsigned (getr (c_regs C) 9);
              bv_unsigned (getr (c_regs C) 8); bv_unsigned (getr (c_regs C) 1)]).
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 18)) as R18.
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 9)) as R9'.
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 8)) as R8'.
pose proof (bv_unsigned_in_range _ (getr (c_regs C) 1)) as R1.
unfold bv_modulus in R18, R9', R8', R1. change (2 ^ Z.of_N 64) with (2 ^ 64) in R18, R9', R8', R1.
assert (HS : st_ok_pi (fx := fy) SEGS VAL (cawR_E regs3 vals)
  (mkSS (AF_cawB + CAWB_END) sr_atoms [cawR_fregion cawR_offs] None cawR_facts)
  (restrict (w_H W3) (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + CAWB_END))) mem3 (YK11.seg_rom SEGS)))).
{ apply cawR_st_ok.
  - vm_compute. reflexivity.
  - cbn. lia.
  - lia.
  - unfold CAWB_FRAME. lia.
  - cbn [cawR_vals_ok cawR_offs vals]. rewrite Hsp.
    replace (spZ (c_regs C) - 80 + 48) with (spZ (c_regs C) - 32) by lia.
    replace (spZ (c_regs C) - 80 + 56) with (spZ (c_regs C) - 24) by lia.
    replace (spZ (c_regs C) - 80 + 64) with (spZ (c_regs C) - 16) by lia.
    replace (spZ (c_regs C) - 80 + 72) with (spZ (c_regs C) - 8) by lia.
    change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8. change (N.to_nat 8) with 8%nat.
    repeat split; try assumption; lia.
  - unfold facts_ok, cawR_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (cawR_E_reg regs3 vals 2 2%bv eq_refl). fold (spZ regs3). rewrite Hsp.
    change (2 ^ 4) with 16. split; [lia|]. split; [rewrite Zminus_mod, Hal16; reflexivity | lia]. }
set (E := cawR_E regs3 vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawR_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := @paj_run_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RET := @paj_ret_at fy rc B_prog_listing PL_caw_B PA).
unfold caw_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
assert (Emem : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hin & Hrg). cbn in Hin.
  destruct Hin as [<- | []]. cbn in Hrg. lia. }
assert (E33 : ew E 33 = getr (c_regs C) 18)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 0 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E34 : ew E 34 = getr (c_regs C) 9)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 1 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E35 : ew E 35 = getr (c_regs C) 8)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 2 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E36 : ew E 36 = getr (c_regs C) 1)
  by (subst E vals; rewrite (cawR_E_val regs3 _ 3 ltac:(lia)); apply Z_to_bv_bv_unsigned).
assert (E9 : ew E 9 = getr regs3 9) by (subst E; exact (cawR_E_reg regs3 vals 9 9%bv eq_refl)).
assert (E2 : bv_unsigned (ew E 2) = spZ regs3) by (subst E; rewrite (cawR_E_reg regs3 vals 2 2%bv eq_refl); reflexivity).
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (10%bv : bv 5) Q10.
rewrite E36 in Q1. rewrite E35 in Q8. rewrite E34 in Q9. rewrite E33 in Q18. rewrite E9, R9 in Q10.
rewrite E2, Hsp in Q2. replace (spZ (c_regs C) - 80 + 80) with (spZ (c_regs C)) in Q2 by lia.
assert (HKP : forall rr, In rr [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) rr = getr regs3 rr).
{ eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E _ (restrict (w_H W3) ms) regs3
    (map (Z_to_bv 64) (SHADOW_OFF :: vals))); [exact HS | | vm_compute; reflexivity].
  subst E. unfold cawR_E. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
(* the return to the entry ra, an SRr step (wle is inside RW) *)
eapply (YA0nH.SRr_SRrG SEGS RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [cfg_ms]. split; [|exact HPM]. rewrite Emem.
unfold caw_post, fpostF, apost_base_xFR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ =>
  exists fy, ly3, S3, Hp3, rg, m, d, k end.
split; [cbn [ms_regs]; rewrite Q1; rewrite Hra; reflexivity|].
split; [exact Hfz|]. split; [exact Hfk|].
(* the post's journal at RW: the run's RW journal, materialized *)
split; [rewrite <- Emem; eapply (ajournal_x_materializeR (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) RW);
  exact HJ|].
split.
{ apply caw_aregs. intros rr Hrr. cbn [In] in Hrr.
  destruct Hrr as [<- | [<- | [<- | [<- | [<- | [<- | Hrr]]]]]].
  - rewrite Q2. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite HKP by (left; reflexivity). apply Hk. left; reflexivity.
  - rewrite HKP by (right; left; reflexivity). apply Hk. right; left; reflexivity.
  - exact Q8.
  - exact Q9.
  - exact Q18.
  - assert (Hr' : In rr [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (right; right; exact Hrr).
    rewrite (HKP rr Hr'). exact (Hk rr Hr'). }
destruct (caw_J_keepR B RW C ly3 S3 Hp3 W3 (ms_mem ms) _ k Hpre HJ ltac:(intros x Hx; rewrite Eab; exact Hx))
  as [HBY HTR].
rewrite Emem in HBY, HTR.
unfold caw_Q.
(* the ledger at own, THE OUTCOME and the progress fact per arm: cut_endR's, as in caw_WB6 *)
split; [exact HROOM|].
split; [exact EHp|]. split; [exact Eab|].
exists own. split; [exact HL|]. split; [exact HBY|].
exists r. split; [cbn [ms_regs]; exact Q10|].
destruct Hr as [(-> & -> & Hrp & Hdead) | (-> & -> & Hrp)].
- split.
  + intros sm x0 os i H0 hist Hpos Hrun Hcons. exfalso. exact (Hdead sm x0 os i H0 hist Hpos Hrun Hcons).
  + left. split; [reflexivity|]. split; [reflexivity | exact Hrp].
- split.
  + intros sm x0 os i H0 hist Hpos Hrun Hcons. split; [reflexivity | exact (Hrp sm x0 os i H0 hist Hpos Hrun)].
  + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hrp | exact HTR].
Qed.

End f.
End d.

Print Assumptions caw_WB6.
Print Assumptions caw_WB6R.
