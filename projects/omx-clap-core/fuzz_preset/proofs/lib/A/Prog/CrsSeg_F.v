(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 396 of its 438 lines of code are new or changed and 736 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): row CR-F of the walk of check_reject_clean_starved against the text
   tcheck_reject_clean_starved_specX, the segment F (+680, A' 0x82408 .. 0x82410): `mv a0, s7` then `jal fuzz_free`,
   whose return site 0x82410 is R's entry (CrsKitAp.crs_pc_R_ret). The closing lemma crs_seg_F proves the kit's
   continuation crs_from_F from crs_from_R.
   rule 24: proves function check_reject_clean_starved (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record
   of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A
   or lib/B, its released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan
   Proof.v existed for check_reject_clean_starved). Written new.
   INPUTS.
   - Pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08 (h-verbs-1 listings v3,
     cold/h-verbs-1-listing-pins102 74dcda1eda12); entry 0x82160 = slot 736 (A_entry_check_reject_clean_starved); F
     is slots 906 / 907.
   - The text: tcheck_reject_clean_starved_specX in lib/A/PRH_FnCheck.v blob 9ecd8eb167c6, with lib/A/PRH_Base.v blob
     fdb45545469b (the kit tip of record f97c8b2f046b, by path; its fpre ends with frm_zero (fp_csr fx),
     supplied at the call from crs_base's frm_zero (fp_csr fxk)), through the kit v4 lib/A/Prog/CrsKitAp.v blob
     b66ea3390c64 (kit commit 698a4dc55979); the callee: fuzz_free (NULL)
     through the walk's shared interim lib/A/Prog/CrsFree0Ap.v blob 79d50622a638 (crs_free0 = tfuzz_free_specX of
     lib/A/PRH_FnAlloc.v blob 83fe93bc86e2 at p = 0, no position, no class-24 bound), called at most = c_most C and
     own = 0, the boundary ledger's two cells (crs_core's `LEDGER .. ran3 (c_most C) 0`), which its post keeps.
   THE PREMISES of crs_seg_F (h-w6u-rep's rulings, 2026-10-29), in the ruled order: HT_fuzz_free0 (crs_free0 at
   every float state); HK, the kit's transport record CrsKeep (kp_tree_vis and kp_obj_keep carry the document); then
   crs_from_R. F is entered only on the RAN arm (kit v3.1's crs_from_F: ran3 = 1, q = 0, crs_perm), so its free is
   always of NULL: no position is asked or stated (R's crs_pos is guarded by ran3 = 0) and no run event or class-24
   bound is used, so HT_fuzz_free and crs_cnt24_F are not premises. No engine Section hypothesis beyond the kit's
   LAWS is used (aj_call_x_spR needs only LAWS and pa_segs_low). Every class-implicit argument of a kit predicate in
   the statement is passed by name (crs_from_R / crs_from_F at fx, rc; crs_free0 at fx').
   WHY EVERY BYTE R READS IS KEPT: the free of NULL has footprint [], and the blocks, Hp, S and the ledger are
   unchanged (crs_free0's post); the frame, its flag word and shadow, the saved slots above fuzz_free's window, the
   input and the document are kept by the callee journal's clauses.
   NUMERALS. LENGTH: 27312 / 16416 (STK of check_reject_clean_starved / fuzz_free), 128 (fs_frame_bytes 1), 3632
   (CRS_PC_R, the R offset from A_prog_base), 56 (struct pj), 24 .. 120 (the saved slots), each checked by vm_compute
   against the image; 8 / 16 / 32 (word, shadow granule, frame alignment). No ADDRESS literal: BASE + CRS_PC_R is
   bounded through the kit's crs_pcs_plan. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel CrsKitAp CrsFree0Ap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- image-free facts the segment reads ---- *)

(* the unwinder over a chain whose first record carries the return site r is the pc0-filtered trace of r and the
   rest of the chain's spine (YG00.unwind_of_chain against PRH_Base.prh_trace) *)
Lemma crsf_unwind : forall pc0 a r b ch, unwind_of_chain pc0 ((a, r, b) :: ch) = prh_trace pc0 r (spine ch).
Proof.
intros pc0 a r b ch. unfold unwind_of_chain, prh_trace, spine. do 2 f_equal. cbn [flat_map map].
f_equal. induction ch as [|[[x y] z] t IH]; [reflexivity|]. cbn [flat_map map]. rewrite IH. reflexivity.
Qed.

(* the shadow facts of an n-byte window survive a reader change that keeps the window's shadow hull *)
Lemma crsf_slot_keep : forall (rd rd' : Z -> option Z) x n, 0 < n ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  range_addressable rd SHADOW_OFF x n -> shadow_hull_vis rd x n ->
  range_addressable rd' SHADOW_OFF x n /\ shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n Hn E Hra Hhv. split.
- intros y Hy. destruct (Hra y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite E; [exact Hs|]. unfold shadow_of_addr, shadow_addr.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)) as D1.
  pose proof (Z.div_le_mono y (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D5.
  lia.
- intros s Hs. rewrite E by exact Hs. exact (Hhv s Hs).
Qed.

(* the thirteen saved slots lie at s0 - 104 .. s0 - 8 *)
Lemma crsf_saved_off : forall p, In p CRS_SAVED -> 24 <= fst p <= 120.
Proof. intros p Hp. cbv [CRS_SAVED In] in Hp. repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]). destruct Hp. Qed.

(* the tree over a block predicate that holds wherever the old one did, on the tree's own blocks (h-hpreset-7's
   lib/A/Prog/Crt102Tail.v ct_cstr_lblk / ct_mems_lblk / ct_nodeR_lblk, restated: that file is not on this base) *)
Section ct. Variable segs : list Segment.

Lemma crsf_cstr_lblk : forall m (lblk lblk' : Z -> Z -> Prop) a k s, pj_cstrR segs m lblk a k s ->
  (lblk a k -> lblk' a k) -> pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.

Lemma crsf_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|].
split; [apply (crsf_cstr_lblk m lblk lblk' x k nm Hc); apply HL; left; reflexivity|].
split.
- pose proof (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
  replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. exact (HP0 H1).
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros y kk Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.

Lemma crsf_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (crsf_cstr_lblk m lblk lblk' str k txt Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (crsf_cstr_lblk m lblk lblk' str k s Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hk)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [|exact Hk]. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros x k Hx. apply HL. apply HDi. apply Hinc. exact Hx.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hk & Hy)]; [left; exact Hz | right; split; [exact Hp|]].
    subst D. rewrite (proj2 (Z.eqb_neq cap 0)) in HL by lia.
    split; [apply HL; [left; reflexivity | exact Hk] | apply HL; [right; left; reflexivity | exact Hy]]. }
  exists Di. split; [exact ED|].
  apply (crsf_mems_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros x k Hx. apply HL. apply HDi. exact Hx.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros x k Hx. apply HL. apply HDi. apply Hinc. exact Hx.
Qed.
End ct.

(* ======================================================================================================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

(* the input bytes survive a memory change that keeps each of their addresses *)
Lemma crsf_bytes_keep : forall (W W' : world SEGS) m m' p l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (p + i) = aview SEGS (w_H W) m (p + i)) ->
  PRH_Base.bytes_at W m p l -> PRH_Base.bytes_at W' m' p l.
Proof.
intros W W' m m' p l E H. unfold PRH_Base.bytes_at, garr8 in *. intros j Hj. destruct (H j Hj) as (Hv & Hr).
split; [|exact Hr]. apply (val_mem_kept SEGS (w_H W) (w_H W') m m' (p + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (p + Z.of_nat j + kk) with (p + (Z.of_nat j + kk)) by lia. apply E. lia.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_A)).
(* the re-hiding relation of the free / realloc move: F's cuts (crs_from_F, crs_from_R) are after the walk's first
   free, so F walks at wle' SEGS RZ_cf *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
#[local] Notation WLE' := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* ---- THE SEGMENT: F (+680, 0x82408): `mv a0, s7` (s7 = 0); `jal fuzz_free` (NULL: crs_free0); then R. The run by
   the R runner (paj_run_xR) and the call by the R call rule (aj_call_x_spR), both at WLE', with the plain callee text
   crs_free0 lifted (YA0nH.SRr_SRrG, YCbqG.apost_base_x_R_lift); the journal read through ajxR_*; the kit's
   crs_cF_keepR / crs_obj_keep_dpR ---- *)
Lemma crs_seg_F : forall CTX0 C
  (HT_fuzz_free0 : forall fx' : YK11.FPState, crs_free0 (fx := fx') B ARx)
  (HK : CrsKeep B ARx),
  crs_from_R (fx := fx) (rc := rc) B ARx CTX0 C -> crs_from_F (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HTF0 HK HR.
unfold crs_from_F.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt3 ran3 q HB HRS HCORE Hr1 Hq0 HPm HBY HTREE HCE.
subst q.
pose proof HB as (HPRE & HFZ & HFK & HJ & HFRM & HSAV & HSLOT & HROD & HMN & Hgp3 & Htp3 & Hsp2a & Hsp2b & Hsp2m & HDPk).
pose proof HPRE as (HFP0 & HMN0 & HCL & HCTX & _ & _ & _ & _ & _ & _ & _ & _ & HHOME & _ & HDOC0 & HLED0 & _).
pose proof HFP0 as ((HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hwin0 & Hch0 & _) & _ & _ & _).
pose proof Hstk0 as (Hal0 & _ & Hlo0 & Hstklo0 & Hsphi0 & Hhi0 & _ & Htop0 & Htophi0).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
assert (ESTK : STK = 27312) by (vm_compute; reflexivity).
assert (ESTKF : @STK_fuzz_free prh_img_A = 16416) by (vm_compute; reflexivity).
assert (EFB : fs_frame_bytes CRS_CID = 128) by (vm_compute; reflexivity).
assert (EPR : CRS_PC_R = 3632) by (vm_compute; reflexivity).
pose proof crs_pcs_plan as (_ & _ & _ & _ & _ & _ & _ & ER & _).
pose proof crs_frame_is_pi as EFR.
pose proof cf_head_nonneg as CH0.
(* ---- the registers at F ---- *)
pose proof HRS as HRS'. unfold crs_regsat, crs_rbase, crs_rsh in HRS'. rewrite Forall_forall in HRS'.
pose proof (HRS' (2%bv, sp2) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R2.
pose proof (HRS' (8%bv, spZ (c_regs C)) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R8.
pose proof (HRS' (9%bv, sp2) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R9.
pose proof (HRS' (18%bv, cF C) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R18.
pose proof (HRS' (26%bv, cF C) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R26.
pose proof (HRS' (27%bv, SHADOW_OFF) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R27.
pose proof (HRS' (25%bv, shadow_addr (cF C)) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R25.
pose proof (HRS' (23%bv, 0) ltac:(cbn [In app]; repeat first [left; reflexivity | right])) as R23.
cbn [fst snd] in R2, R8, R9, R18, R26, R27, R25, R23. clear HRS'.
(* ---- the state at F: the frame, the journal's layout, the ledger ---- *)
destruct (crs_cF_keepR B ARx LAWS WLE' CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HPRE HJ) as (EcF3 & Efl3).
unfold crs_JR in HJ.
pose proof (ajxR_ar HJ) as HAR3. pose proof (ajxR_ly HJ) as HLE3. pose proof (ajxR_frs HJ) as HFR3.
pose proof HLE3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & Elo3 & Ehi3 & _).
pose proof HFRM as (HFR3' & HFLW3 & HFP3).
destruct (alx_frames _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID (c_fpos C) HAR3 ltac:(rewrite HFR3'; left; reflexivity))
  as (F32 & _ & _ & _).
rewrite EcF3 in F32.
pose proof HCORE as (HLED3 & _ & _ & _ & _ & HRL3 & HPOS3).
pose proof HPm as (HPL3 & HPA3).
assert (Hent3 : forall bk, In bk (ablocks B (c_ly C) (c_S C)) -> In bk (ablocks B ly3 S3))
  by (intros bk Hbk; exact (Permutation_in _ (Permutation_sym HPA3) Hbk)).
(* ---- the callee's footprint: none (a NULL free writes nothing) ---- *)
set (FP1 := ([] : list (Z * Z))).
assert (HSC : ~ YI16.sink_open_fp FP1).
{ unfold FP1. change ([] : list (Z * Z)) with (ablocks_fp []). apply sink_closed_ablocks_fp. constructor. }
assert (NF : forall x, ~ inFP FP1 x) by (intros x; exact (inFP_nil x)).
assert (NFb : forall b m x, In (b, m) (ablocks B (c_ly C) (c_S C)) -> b <= x < b + req_size m -> ~ inFP FP1 x)
  by (intros b m x _ _; exact (NF x)).
assert (NFf : forall cid pos x, In (cid, pos) (frames S3) ->
  frame_addr ly3 cid pos <= x < frame_addr ly3 cid pos + fs_frame_bytes cid -> ~ inFP FP1 x)
  by (intros cid pos x _ _; exact (NF x)).
assert (NFs : forall cid pos x, In (cid, pos) (frames S3) ->
  in_zr x (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8) -> ~ inFP FP1 x)
  by (intros cid pos x _ _; exact (NF x)).
(* ---- the run: `mv a0, s7`, `jal fuzz_free` (no memory), by the R runner at wle' SEGS RZ_cf ---- *)
unfold crs_cfg.
set (ss_F := mkSS CRS_PC_F cur_atoms [] None (mkFacts [] [] [])).
assert (HS : st_ok_pi SEGS VAL (TE (c_regs C) regs3 []) ss_F
  (restrict (w_H W3) (@YK11.mkst fxk regs3 (Z_to_bv 64 (BASE + CRS_PC_F)) mem3 (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs3 []) (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs3 [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS WLE' (YA0nH.wle'_refl SEGS RZ)
  (YA0nH.wle'_trans SEGS RZ)).
unfold w64.
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_F ss_mem]. apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
pose proof (ajxR_hi HJ) as HK3st.
prreg HS (10%bv : bv 5) Z10. prreg HS (1%bv : bv 5) Z1.
assert (KR : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 25; 26; 27]%bv -> getr (ms_regs ms) r0 = getr regs3 r0).
{ intros r0 Hr0. cbv [In] in Hr0.
  repeat (destruct Hr0 as [<- | Hr0];
    [apply (ts_reg_kept_c (fx := fxk) (c_regs C) regs3 [] _ _ ms _ _ HS); vm_compute; reflexivity |]).
  destruct Hr0. }
assert (A10 : getr (ms_regs ms) 10 = w64 0).
{ rewrite Z10. exact (eq_trans (te_cur (c_regs C) regs3 [] 23%bv 23 eq_refl) R23). }
set (rawR := Z_to_bv 64 (BASE + CRS_PC_R)).
assert (A1 : getr (ms_regs ms) 1 = rawR) by (rewrite Z1; unfold rawR; rewrite EPR; reflexivity).
assert (Esp2 : spZ (ms_regs ms) = sp2).
{ unfold spZ. rewrite (KR 2%bv) by (cbv; tauto). rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
assert (Es0 : s0Z (ms_regs ms) = spZ (c_regs C)).
{ unfold s0Z. rewrite (KR 8%bv) by (cbv; tauto). rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
(* ---- the callee's frame-pointer chain: s0 = the entry sp, the saved ra and s0 below it, the entry's chain ---- *)
assert (Hch1 : exists ch1, achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs C) + (sp2 - spZ (c_regs C)))
    (s0Z (ms_regs ms)) ch1 /\
  (ch1 = [] \/ ch1 = (spZ (c_regs C), raZ (c_regs C), s0Z (c_regs C)) :: c_ch C)).
{ replace (spZ (c_regs C) + (sp2 - spZ (c_regs C))) with sp2 by lia. rewrite Es0, HF.
  destruct (Z_lt_le_dec (spZ (c_regs C)) (ly_top ly3 - 16)) as [Hlt | Hge].
  - exists ((spZ (c_regs C), raZ (c_regs C), s0Z (c_regs C)) :: c_ch C). split; [|right; reflexivity].
    unfold crs_saved in HSAV. rewrite Forall_forall in HSAV.
    pose proof (HSAV (120, 1%bv) ltac:(cbv [CRS_SAVED In]; left; reflexivity)) as V0.
    pose proof (HSAV (112, 8%bv) ltac:(cbv [CRS_SAVED In]; right; left; reflexivity)) as V1.
    cbn [fst snd] in V0, V1.
    replace (spZ (c_regs C) - 128 + 120) with (spZ (c_regs C) - 8) in V0 by lia.
    replace (spZ (c_regs C) - 128 + 112) with (spZ (c_regs C) - 16) in V1 by lia.
    apply (achain_push ly3 (aview SEGS (w_H (c_W C)) (c_mem C)) (aview SEGS (w_H W3) mem3) (spZ (c_regs C))
      (s0Z (c_regs C)) (raZ (c_regs C)) (c_ch C) sp2).
    + apply (achain_ly_top (c_ly C) ly3); [exact Etop3 | exact Hch0].
    + rewrite Etop3. lia.
    + intros a Ha. rewrite <- HF. apply HK3st; lia.
    + exact V0.
    + exact V1.
    + exact Hra40.
    + lia.
    + lia.
    + exact Hlt.
    + lia.
  - exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hge | reflexivity]. }
destruct Hch1 as (ch1 & Hch1 & Ech1).
(* ---- the free's trace, from the universe closure at crcs's observed context ---- *)
assert (HTR : In (call_trace ly3 (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) (as_universe B)).
{ unfold call_trace. destruct (frame0_ok ly3 (ms_regs ms)).
  - rewrite crsf_unwind. unfold raZ. rewrite A1. unfold rawR. rewrite unsigned_lit_small by lia.
    assert (Hx : prh_ctx CTX0 F_check_reject_clean_starved (spine ch1)).
    { destruct Ech1 as [-> | ->]; [|exact HCTX].
      destruct HCTX as (c & j & Hc & _). exists c, 0%nat. split; [exact Hc | reflexivity]. }
    exact (prh_univ_closure_site B CTX0 F_check_reject_clean_starved (spine ch1) RT_fuzz_free (BASE + CRS_PC_R) HCL Hx
      eq_refl ltac:(vm_compute; right; left; reflexivity)).
  - destruct HCL as (H1 & _). exact (H1 RT_fuzz_free). }
(* ---- the call: fuzz_free (NULL), crs_free0 at the boundary ledger's cells (most = c_most C, own = 0), by the R call
   rule at wle' SEGS RZ_cf ---- *)
eapply (YA0nH.SRrG_bind SEGS WLE' (YA0nH.wle'_trans SEGS RZ)).
{ eapply (aj_call_x_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) WLE' (YA0nH.wle'_refl SEGS RZ)
    (YA0nH.wle'_trans SEGS RZ) W3 _ _ ms STK (spZ (c_regs C)) []
    (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly3 S3 Hp3 _ k
    (@STK_fuzz_free prh_img_A) FP1 (sp2 - spZ (c_regs C)) rawR ch1 _ HS eq_refl HJ).
  - rewrite Esp2. lia.
  - lia.
  - lia.
  - rewrite ESTKF. lia.
  - rewrite ESTKF, ESTK. lia.
  - rewrite (KR 3%bv) by (cbv; tauto). rewrite Hgp3. exact Hgp0.
  - rewrite (KR 4%bv) by (cbv; tauto). rewrite Htp3. exact Htp0.
  - exact A1.
  - unfold rawR. apply (ret_ok_codeptr_v (PI := PA)); rewrite EPR; [lia | reflexivity].
  - unfold rawR. rewrite unsigned_lit_small by lia. lia.
  - exact Hch1.
  - intros HPRE1.
    (* the plain callee text, lifted to the caller's relation (YA0nH.SRr_SRrG, YCbqG.apost_base_x_R_lift) *)
    eapply (YA0nH.SRrG_mono SEGS WLE').
    { apply (YA0nH.SRr_SRrG SEGS WLE' (YA0nH.wle_wle' SEGS RZ)).
      refine (HTF0 fxk (c_most C) 0 ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak3 cnt3 SIZE_MAXZ ran3
        (conj HPRE1 (conj _ (conj _ (conj _ HFZ)))) HRL3 HTR A10 _).
      + rewrite HF. exact HROD.
      + rewrite Esp2, Ehi3. lia.
      + unfold raZ. rewrite A1. unfold rawR. rewrite unsigned_lit_small by lia. lia.
      + rewrite HF. exact HLED3. }
    intros W' c' _ HP'.
    exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARx WLE' (YA0nH.wle_wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ HP').
  - intros a Ha. exfalso. exact (NF a Ha). }
cbv beta. intros W2 c2 HWle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HP2 & HQ2).
destruct HQ2 as ((HRL2 & ES2 & EHp2 & EA2 & HLED2) & HMNk).
pose proof (ajxR_ar HJ1) as HAR2. pose proof (ajxR_hi HJ1) as K1st. pose proof (ajxR_blk HJ1) as K1blk.
pose proof (ajxR_img HJ1) as K1img. pose proof (ajxR_frm HJ1) as K1frm.
rewrite HF in K1st, K1blk, K1img, K1frm, HMNk.
pose proof (ajxR_ly HJ2) as HLE2. pose proof (ajxR_frs HJ2) as HFR2.
destruct (crs_cF_keepR B ARx LAWS WLE' CTX0 C ly2 S2 Hp2 W2 mem2 md2 (k + k1) HPRE HJ2) as (EcF2 & Efl2).
(* ---- the ledger, Lam and the blocks after the free: unchanged (NULL), so Lam2 = Lam3 ---- *)
set (Lam2 := Lam3) in *.
assert (HPL2 : Permutation Lam2 (c_Lam C)) by exact HPL3.
assert (HPA2 : Permutation (ablocks B ly2 S2) (ablocks B (c_ly C) (c_S C))) by (rewrite EA2; exact HPA3).
(* R's position: crs_pos asks one only when nothing was refused, and F is entered refused (ran3 = 1) *)
assert (HPOS2 : crs_pos C (crs_evs_at_R C) ran3 S2) by (intros Hr0; lia).
assert (HA2in : forall bk, In bk (ablocks B (c_ly C) (c_S C)) -> In bk (ablocks B ly2 S2))
  by (intros bk Hbk; exact (Permutation_in _ (Permutation_sym HPA2) Hbk)).
(* ---- R (+688, 0x82410): crs_from_R at the post state, its boundary at wle' SEGS RZ_cf ---- *)
apply (HR fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam2 peak3 cnt3 ran3).
- (* crs_baseR *)
  split; [exact HPRE|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HJ2|].
  split.
  { (* the frame: pushed, its flag word kept (outside the freed block), its bytes present *)
    split; [rewrite HFR2; reflexivity|]. split.
    - rewrite Efl2, <- Efl3, <- HFLW3. apply rdword_ext. intros kk Hkk.
      apply (K1frm CRS_CID (c_fpos C)); [rewrite HFR3'; left; reflexivity | left | ].
      + unfold in_zr, frame_rng. cbn [fst snd]. rewrite EcF3, EFB. rewrite EFB in *. lia.
      + apply (NFf CRS_CID (c_fpos C)); [rewrite HFR3'; left; reflexivity|]. rewrite EcF3, EFB. lia.
    - intros a Ha. destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 CRS_CID (c_fpos C) HAR2
        ltac:(rewrite HFR2; left; reflexivity)) as (_ & _ & Ffr2 & _).
      rewrite EcF2 in Ffr2. exact (proj1 (Ffr2 a Ha)). }
  split.
  { (* the saved words: the real stack above the callee's window *)
    unfold crs_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros p Hp.
    rewrite <- (HSAV p Hp). apply rdword_ext. intros kk Hkk. pose proof (crsf_saved_off p Hp) as Hoff.
    apply K1st; rewrite ?ESTKF; lia. }
  split.
  { (* the local's shadow: the frame's shadow bytes, outside the freed block *)
    destruct HSLOT as (Hra3 & Hhv3).
    apply (crsf_slot_keep (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) mem2) (cOut C) 56 ltac:(lia));
      [|exact Hra3 | exact Hhv3].
    intros s Hs. unfold cOut, CRS_OFF_DOC, shadow_addr in Hs. unfold SHADOW_OFF in Hs.
    apply (K1frm CRS_CID (c_fpos C)); [rewrite HFR3'; left; reflexivity | right | ].
    - unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. rewrite EcF3, EFB. lia.
    - apply (NFs CRS_CID (c_fpos C)); [rewrite HFR3'; left; reflexivity|].
      unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. rewrite EcF3, EFB. lia. }
  split.
  { (* the read-only view: the image clause keeps every read-only byte (no static is read-only) *)
    intros a Hro Hns He. rewrite (K1img a); [exact (HROD a Hro Hns He) | | exact Hns | exact He | | ].
    - destruct Hro as [(s & Hs & _ & Hb) | Hb]; [exists s; split; [exact Hs | exact Hb] | exact (@pa_relro_img _ _ PA a Hb)].
    - intros Hp. exact (pst_not_ro_A a Hp Hro).
    - exact (fp_spares_closed FP1 a HSC). }
  split; [exact (HMNk HMN)|].
  split.
  { assert (P3 : getr regs2 3%bv = getr (ms_regs ms) 3%bv) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
    rewrite P3, (KR 3%bv) by (cbv; tauto). exact Hgp3. }
  split.
  { assert (P4 : getr regs2 4%bv = getr (ms_regs ms) 4%bv) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
    rewrite P4, (KR 4%bv) by (cbv; tauto). exact Htp3. }
  split; [exact Hsp2a|]. split; [exact Hsp2b | split; [exact Hsp2m | exact HDPk]].
- (* the frame registers: callee-saved, and kept by the run *)
  unfold crs_regsat, crs_rbase, crs_rsh. cbn [app].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 2%bv); [|exact R2];
    transitivity (getr (ms_regs ms) 2%bv); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 8%bv); [|exact R8];
    transitivity (getr (ms_regs ms) 8%bv); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 9%bv); [|exact R9];
    transitivity (getr (ms_regs ms) 9%bv); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 18%bv); [|exact R18];
    transitivity (getr (ms_regs ms) 18%bv); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 26%bv); [|exact R26];
    transitivity (getr (ms_regs ms) 26%bv); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 27%bv); [|exact R27];
    transitivity (getr (ms_regs ms) 27%bv); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_cons; [cbn [fst snd]; transitivity (getr regs3 25%bv); [|exact R25];
    transitivity (getr (ms_regs ms) 25%bv); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | apply KR; cbv; tauto]|].
  apply Forall_nil.
- (* crs_live: the ledger at Lam2, the counters unchanged, the room, the position *)
  pose proof HCORE as (_ & Hpk & Hrn & Hcn & Hcl & _ & _).
  split.
  + split; [exact HLED2|]. split; [exact Hpk|]. split; [exact Hrn|]. split; [exact Hcn|]. split; [exact Hcl|].
    split; [exact HRL2 | exact HPOS2].
  + split; [exact HPL2 | exact HPA2].
- (* the input bytes: in a harness block, a read-only image range or an entry block, never the freed block *)
  apply (crsf_bytes_keep W3 W2 mem3 mem2 (c_data C) (c_tb C)); [|exact HBY].
  intros i Hi. unfold cSize in HHOME.
  destruct HHOME as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
  + pose proof HLED0 as (_ & _ & HBL0 & _). rewrite Forall_forall in HBL0.
    destruct (HBL0 _ Hbm) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
    assert (RS : 1 <= req_size (m + cf_head) /\ m + cf_head <= req_size (m + cf_head)) by (apply req_size_pos; lia).
    replace (c_data C + i) with (b - cf_head + (c_data C + i - (b - cf_head))) by lia.
    apply (K1blk _ (m + cf_head)); [exact (Hent3 _ Hab) | exact (HA2in _ Hab) | lia | apply (NFb _ _ _ Hab); lia].
  + destruct (Hro (c_data C + i) ltac:(lia)) as (Hro1 & Hns & He).
    apply K1img; [| exact Hns | exact He | intros Hp; exact (pst_not_ro_A _ Hp Hro1) | exact (fp_spares_closed FP1 _ HSC)].
    destruct Hro1 as [(s & Hs & _ & Hb) | Hb]; [exists s; split; [exact Hs | exact Hb] | exact (@pa_relro_img _ _ PA _ Hb)].
  + destruct (Hro (c_data C + i) ltac:(lia)) as (Hro1 & Hns & He & _).
    apply K1img; [| exact Hns | exact He | intros Hp; exact (pst_not_ro_A _ Hp Hro1) | exact (fp_spares_closed FP1 _ HSC)].
    destruct Hro1 as [(s & Hs & _ & Hb) | Hb]; [exists s; split; [exact Hs | exact Hb] | exact (@pa_relro_img _ _ PA _ Hb)].
  + pose proof (req_size_pos m ltac:(lia)) as RS.
    replace (c_data C + i) with (b + (c_data C + i - b)) by lia.
    apply (K1blk _ m); [exact (Hent3 _ Hbm) | exact (HA2in _ Hbm) | lia | apply (NFb _ _ _ Hbm); lia].
- (* the document: its header in an entry fake frame, its blocks entry blocks, neither the freed block *)
  intros Hd. destruct (HTREE Hd) as (HN3 & _ & _ & _).
  destruct HDOC0 as [Hd0 | (_ & HT0 & _)]; [exfalso; exact (Hd Hd0)|].
  pose proof HT0 as (_ & HD0 & _ & HO0).
  assert (HDL2 : forall bk, In bk (c_D C) -> In bk Lam2)
    by (intros bk Hbk; exact (Permutation_in _ (Permutation_sym HPL2) (HD0 bk Hbk))).
  split; [|split; [exact HDL2|]; split].
  + apply (pj_nodeR_frame SEGS (c_t C) (mrestrict (w_H W3) mem3) (mrestrict (w_H W2) mem2) (prh_lin Lam2) (c_doc C) (c_D C)).
    { apply (crsf_nodeR_lblk SEGS (c_t C) _ (prh_lin Lam3)); [exact HN3|]. intros x kk Hx _. exact (HDL2 (x, kk) Hx). }
    pose proof HO0 as (_ & (cid0 & pos0 & Hin0 & Hlo0' & Hhi0') & _).
    destruct (crs_ly_keep B ARx LAWS (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) ly3 cid0 pos0 HAR0 HLE3)
      as (Ef3 & _).
    destruct (crs_ly_keep B ARx LAWS (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) ly2 cid0 pos0 HAR0 HLE2)
      as (Ef2 & _).
    assert (Hin03 : In (cid0, pos0) (frames S3)) by (rewrite HFR3; right; exact Hin0).
    assert (Hin02 : In (cid0, pos0) (frames S2)) by (rewrite HFR2; right; exact Hin0).
    unfold pj_agreeR, pj_footR. intros x [Hx | ((a, kk) & Hb & Hx)].
    * split.
      -- apply (mbyte_of_aview SEGS). apply (K1frm cid0 pos0); [exact Hin03 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Ef3; lia |].
         apply (NFf cid0 pos0); [exact Hin03 | rewrite Ef3; lia].
      -- intros _. apply (apresent_writable SEGS).
         destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 cid0 pos0 HAR2 Hin02) as (_ & _ & Ffr & _).
         rewrite Ef2 in Ffr. exact (proj1 (Ffr x ltac:(lia))).
    * unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      pose proof HLED0 as (_ & _ & HBL0 & _). rewrite Forall_forall in HBL0.
      destruct (HBL0 _ (HD0 _ Hb)) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
      assert (RS : 1 <= req_size (kk + cf_head) /\ kk + cf_head <= req_size (kk + cf_head)) by (apply req_size_pos; lia).
      split.
      -- apply (mbyte_of_aview SEGS). replace x with (a - cf_head + (x - (a - cf_head))) by lia.
         apply (K1blk _ (kk + cf_head)); [exact (Hent3 _ Hab) | exact (HA2in _ Hab) | lia | apply (NFb _ _ _ Hab); lia].
      -- intros _. apply (apresent_writable SEGS).
         destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 (HA2in _ Hab)) as (_ & _ & _ & _ & Hbb & _).
         exact (proj1 (Hbb x ltac:(lia))).
  + exact (kp_tree_vis B ARx HK ly2 S2 Hp2 W2 mem2 md2 Lam2 peak3 cnt3 SIZE_MAXZ ran3 (c_most C) 0 (c_D C) HAR2 HLED2 HDL2).
  + exact (crs_obj_keep_dpR B ARx LAWS WLE' STK (spZ (c_regs C)) (c_ly C) (c_S C) (c_dp C) (c_Hp C) (c_W C)
      (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly2 S2 Hp2 W2 mem2 md2 (k + k1) (c_doc C) HAR0 HJ2 HO0).
- exact HCE.
Qed.

Print Assumptions crs_seg_F.

End f.
End d.
Print Assumptions crs_seg_F.
