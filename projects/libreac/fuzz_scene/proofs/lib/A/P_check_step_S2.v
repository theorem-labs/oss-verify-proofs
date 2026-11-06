(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v; 643 of its 691 lines of code are new or changed and 162 lines of the source are left out. *)
(* Segment lemma cs_S2 of check_step's asan walk (statement by a Theorem Labs lane, 2026-10-28; proof by a Theorem Labs lane,
   2026-10-29), proved against the cut statement of P_check_step_cut.v. Rule 24 is met: this file proves one segment
   of the walk, not the function; the callees are Section hypotheses.

   Segment S2 of the ASan walk of check_step in fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026): 0x8345c .. 0x834d0.
   C3 payload bcmp and C4 trailer bcmp (k = 342) through aj_bcmp_at (Reusable/YCbq.v:2061). Donor: the addframe walk's bcmp (cgif A/ACkh.v:33 tfibX_ABCMP).
   Pre: the cut state at its first pc; post: cs_st3 at the next cut pc
   (P_check_step_cut.v).
   The walk, per k: (k = 0) a0 = blk + 9, a1 = body, a2 = 24; (1 <= k <= 341) a0 = blk + 7, a1 = body + 24 + 26 (k - 1),
   a2 = 26; (k = 342) a0 = blk + 7, a1 = body + 8890, a2 = 14, then a0 = blk + 21, a1 = check_step.trailer, a2 = 12.
   Each bcmp's operands are equal (cs_pre's blk = scene_block b k and body = b), so ABCMP's `v = 0 <-> equal`
   (YG0d.v:370) refutes every `bnez a0`. The trailer's shadow (range_addressable and the 8-aligned hull) comes from
   HB_Z_TR / HB_Z_CF / HB_C_CS through al_zshadow and am_const, at the addresses HB_ADDR fixes (cs2_tr_shadow). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85 YC45.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96). *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by
   al_const (AR_const_law, YG0d.v:461-467), so no flag hypothesis is taken. *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane. *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
(* scene's start-up shadow of check_step's two globals as named facts of B (an internal review, CHECKSTEP-REVIEW item R2): full
   granules in as_zero_shadow, the partial granules and the f9 redzones as constant cells; the walk derives
   range_addressable and shadow_hull_vis from am_const (YG0n.v:211) and al_zshadow (YG0d.v:435-438), as cgif
   A/AE2m.v:20-54 does. shadow_addr 0x20d80 = 0x7fffc1b0, shadow_addr 0x20da0 = 0x7fffc1b4. *)
Hypothesis HB_Z_TR : Exists (zr_sub (A_CS_TRAILER, 8)) (as_zero_shadow B).
Hypothesis HB_Z_CF : Exists (zr_sub (A_CS_CFRAME, 48)) (as_zero_shadow B).
Hypothesis HB_C_CS : forall ly,
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_CFRAME + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr A_CS_CFRAME + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
(* static fact of the listing, closed by vm_compute on scene's PI (a Theorem Labs lane 23:3xZ): the two globals' addresses; with HB_Z_TR / HB_Z_CF / HB_C_CS this pins every shadow byte of the 8-aligned hulls (trailer granules 0..3 and the const frame's from 0x7fffc1b4). *)
Hypothesis HB_ADDR : A_CS_TRAILER = 0x20d80 /\ A_CS_CFRAME = 0x20da0.
Hypothesis HRO_TR : ro_bytes SEGS pa_relro_lo pa_relro_hi B A_CS_TRAILER scene_trailer.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).
(* A fresh symbolic state at a cut: every register an atom, no region, no fact. *)
Lemma cs2_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS (@pa_val _ scene_listing PI) (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn. exact I.
- unfold facts_ok. cbn. tauto.
Qed.
(* ---- pure facts of the block ---- *)
Lemma cs2_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|x l]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma cs2_nth_skipn : forall (l : list byte) m i d, nth i (skipn m l) d = nth (m + i) l d.
Proof.
intros l m. revert l. induction m as [|m IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity | cbn [skipn Nat.add nth]; apply IH].
Qed.
Lemma cs2_block_nth : forall b k j,
  nth (7 + j) (scene_block b k) (Z_to_bv 8 0) =
  nth j (scene_payload b k ++ [Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256)]) (Z_to_bv 8 0).
Proof. intros b k j. reflexivity. Qed.
Lemma cs2_payload_0 : forall b i, length b = Z.to_nat 8904 -> 0 <= i < 24 ->
  nth (Z.to_nat (9 + i)) (scene_block b 0) (Z_to_bv 8 0) = nth (Z.to_nat (0 + i)) b (Z_to_bv 8 0).
Proof.
intros b i Hb Hi. replace (Z.to_nat (9 + i)) with (7 + (2 + Z.to_nat i))%nat by lia. rewrite cs2_block_nth.
change (scene_payload b 0) with ([Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b). cbn [app nth Nat.add].
rewrite app_nth1 by (rewrite length_firstn, Hb; lia).
rewrite cs2_nth_firstn by lia. f_equal; lia.
Qed.
Lemma cs2_payload_mid : forall b k i, length b = Z.to_nat 8904 -> 1 <= k <= 341 -> 0 <= i < 26 ->
  nth (Z.to_nat (7 + i)) (scene_block b k) (Z_to_bv 8 0) = nth (Z.to_nat (24 + 26 * (k - 1) + i)) b (Z_to_bv 8 0).
Proof.
intros b k i Hb Hk Hi. replace (Z.to_nat (7 + i)) with (7 + Z.to_nat i)%nat by lia. rewrite cs2_block_nth.
assert (P : scene_payload b k = firstn 26 (skipn (Z.to_nat (24 + 26 * (k - 1))) b)).
{ unfold scene_payload, scene_off. rewrite (proj2 (Z.eqb_neq k 0)) by lia. rewrite (proj2 (Z.eqb_neq k 342)) by lia. reflexivity. }
rewrite P. rewrite app_nth1 by (rewrite length_firstn, length_skipn, Hb; lia).
rewrite cs2_nth_firstn by lia. rewrite cs2_nth_skipn. f_equal; lia.
Qed.
Lemma cs2_payload_342 : forall b i, length b = Z.to_nat 8904 -> 0 <= i < 14 ->
  nth (Z.to_nat (7 + i)) (scene_block b 342) (Z_to_bv 8 0) = nth (Z.to_nat (8890 + i)) b (Z_to_bv 8 0).
Proof.
intros b i Hb Hi. replace (Z.to_nat (7 + i)) with (7 + Z.to_nat i)%nat by lia. rewrite cs2_block_nth.
change (scene_payload b 342) with (firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer).
rewrite <- app_assoc. rewrite app_nth1 by (rewrite length_firstn, length_skipn, Hb; lia).
rewrite cs2_nth_firstn by lia. rewrite cs2_nth_skipn. f_equal; lia.
Qed.
Lemma cs2_trailer_nth : forall b i, length b = Z.to_nat 8904 -> 0 <= i < 12 ->
  nth (Z.to_nat (21 + i)) (scene_block b 342) (Z_to_bv 8 0) = nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0).
Proof.
intros b i Hb Hi. replace (Z.to_nat (21 + i)) with (7 + (14 + Z.to_nat i))%nat by lia. rewrite cs2_block_nth.
change (scene_payload b 342) with (firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer).
rewrite <- app_assoc. rewrite app_nth2 by (rewrite length_firstn, length_skipn, Hb; lia).
rewrite length_firstn, length_skipn, Hb.
replace (14 + Z.to_nat i - Nat.min 14 (Z.to_nat 8904 - Z.to_nat 8890))%nat with (Z.to_nat i) by lia.
rewrite app_nth1 by (change (length scene_trailer) with 12%nat; lia). reflexivity.
Qed.
(* ---- the window a bcmp call may write: [sp0 - 128 - 2 ESTACK, sp0 - 128) ---- *)
Definition cs2_out (sp0 a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ~ (sp0 - CHECK_STEP_FRAME - 2 * ESTACK <= a < sp0 - CHECK_STEP_FRAME).
Lemma cs2_frame_nil : forall E (H : word -> bool) (m m' : word -> option byte),
  frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E H m m' HF a. apply aview_eq_of. apply HF. intros (r & Hr & _). destruct Hr. Qed.
Lemma cs2_km_run : forall E (H : word -> bool) (m0 m1 mb : word -> option byte) sp0,
  frame_of E [] (mrestrict H m0) (mrestrict H m1) ->
  (forall a, cs2_out sp0 a -> aview SEGS H m0 a = aview SEGS H mb a) ->
  forall a, cs2_out sp0 a -> aview SEGS H m1 a = aview SEGS H mb a.
Proof. intros E H m0 m1 mb sp0 HF HK a Ha. rewrite (cs2_frame_nil E H m0 m1 HF a). exact (HK a Ha). Qed.
Lemma cs2_af : forall E (regsX : bvmap 5 word) k lo hi, ew E 20 = getr regsX 20 -> getr regsX 20 = w64 k ->
  lo <= k <= hi -> 0 <= k <= 342 -> afact_ok E 20 (mkAF lo hi 0).
Proof.
intros E regsX k lo hi H1 H2 Hk Hk0. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite H1, H2. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* ---- the shadow of check_step.trailer from the named B facts ---- *)
Lemma cs2_tr_shadow : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_CS_TRAILER 12 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) A_CS_TRAILER 12.
Proof.
intros ly S W mem md HAR.
destruct HB_ADDR as [ETR ECF].
pose proof (proj1 HAR) as HM.
assert (C1 : forall a v, In (z1 (ANum a) v) (as_const B ly) -> aview SEGS (w_H W) mem a = Some (le_byte v 1 0)).
{ intros a v Hin.
  pose proof (proj1 (Forall_forall (cell_holds B ly (aview SEGS (w_H W) mem)) (as_const B ly)) (am_const B ly S _ HM) _ Hin) as X.
  unfold cell_holds, z1, c1 in X. cbn [c_at c_val c_w aeval] in X. specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X. }
assert (ZS : forall a n, Exists (zr_sub (a, n)) (as_zero_shadow B) -> a mod 8 = 0 -> forall i, 0 <= i < n / 8 ->
  aview SEGS (w_H W) mem (SHADOW_OFF + a / 8 + i) = Some 0).
{ intros a n Hex Ha i Hi. apply Exists_exists in Hex as ([q m] & Hin & Hsub). unfold zr_sub in Hsub; cbn [fst snd] in Hsub.
  destruct (zs_range SEGS B q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & _).
  pose proof (al_zshadow _ _ LAWS ly S W mem md (q, m) HAR (or_intror Hin)) as Hz. cbn [fst snd] in Hz.
  pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod m 8 ltac:(lia)) as Dm.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Bn.
  specialize (Hz (a / 8 - q / 8 + i) ltac:(lia)). unfold shadow_of_addr in Hz.
  replace (SHADOW_OFF + q / 8 + (a / 8 - q / 8 + i)) with (SHADOW_OFF + a / 8 + i) in Hz by lia. exact Hz. }
destruct (HB_C_CS ly) as (K1 & K2 & K3 & _ & _).
assert (T0 : aview SEGS (w_H W) mem 2147467696 = Some 0).
{ pose proof (ZS A_CS_TRAILER 8 HB_Z_TR ltac:(rewrite ETR; reflexivity) 0 ltac:(change (8 / 8) with 1; lia)) as X. rewrite ETR in X. exact X. }
assert (T1 : aview SEGS (w_H W) mem 2147467697 = Some 4).
{ pose proof (C1 _ _ K1) as X. rewrite ETR in X. exact X. }
assert (T2 : aview SEGS (w_H W) mem 2147467698 = Some 0xf9).
{ pose proof (C1 _ _ K2) as X. rewrite ETR in X. exact X. }
assert (T3 : aview SEGS (w_H W) mem 2147467699 = Some 0xf9).
{ pose proof (C1 _ _ K3) as X. rewrite ETR in X. exact X. }
assert (TC : forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (2147467700 + i) = Some 0).
{ intros i Hi. pose proof (ZS A_CS_CFRAME 48 HB_Z_CF ltac:(rewrite ECF; reflexivity) i ltac:(change (48 / 8) with 6; lia)) as X. rewrite ECF in X. exact X. }
split.
- intros x Hx. rewrite ETR in Hx. unfold shadow_of_addr.
  destruct (Z_lt_le_dec x 134536) as [Lx | Lx].
  + assert (Q : x / 8 = 16816) by (symmetry; apply (Z.div_unique x 8 16816 (x - 134528)); lia).
    rewrite Q. exists 0. split; [exact T0 | left; reflexivity].
  + assert (Q : x / 8 = 16817) by (symmetry; apply (Z.div_unique x 8 16817 (x - 134536)); lia).
    rewrite Q. exists 4. split; [exact T1|]. right.
    assert (Hm : x mod 8 = x - 134536) by (rewrite (Z.mod_eq x 8), Q by lia; lia). lia.
- intros s Hs. rewrite ETR in Hs.
  assert (Hlo : shadow_addr 134528 / 8 * 8 = 2147467696) by reflexivity.
  assert (Hhi : shadow_addr (134528 + 12 - 1) / 8 * 8 + 8 = 2147467704) by reflexivity.
  rewrite Hlo, Hhi in Hs.
  assert (C : s = 2147467696 \/ s = 2147467697 \/ s = 2147467698 \/ s = 2147467699 \/ (exists i, 0 <= i < 4 /\ s = 2147467700 + i)).
  { destruct (Z_lt_le_dec s 2147467700) as [L|G]; [lia | right; right; right; right; exists (s - 2147467700); split; lia]. }
  destruct C as [-> | [-> | [-> | [-> | (i & Hi & ->)]]]].
  + rewrite T0. discriminate.
  + rewrite T1. discriminate.
  + rewrite T2. discriminate.
  + rewrite T3. discriminate.
  + rewrite (TC i ltac:(lia)). discriminate.
Qed.
(* ---- the operands of the two bcmp calls ---- *)
Lemma cs2_blk_facts : forall ly S W mem md sp0 ly1 S1 W1 memT mdT fpos blk d n,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 memT mdT 0 ->
  afobj SEGS B ly S W mem blk CS_BLK_LEN -> 0 <= d -> d + n <= CS_BLK_LEN -> 0 < n ->
  4096 <= blk /\ blk + CS_BLK_LEN <= alloc_ceiling /\
  (forall a, blk + d <= a < blk + d + n -> aview SEGS (w_H W1) memT a <> None) /\
  amem_range (blk + d) n /\
  range_addressable (aview SEGS (w_H W1) memT) SHADOW_OFF (blk + d) n /\
  shadow_hull_vis (aview SEGS (w_H W1) memT) (blk + d) n /\
  (forall i, 0 <= i < n -> aview SEGS (w_H W1) memT (blk + d + i) = aview SEGS (w_H W) mem (blk + d + i)).
Proof.
intros ly S W mem md sp0 ly1 S1 W1 memT mdT fpos blk d n HAR0 HJ HFO Hd Hdn Hn.
unfold CS_BLK_LEN in *.
destruct HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hb8 & HRA).
pose proof HJ as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR0 Hfin) as (Hf0 & Hfc & Happ).
destruct (al_layout _ _ LAWS ly S W mem md ly1 HAR0 Hly) as (_ & Efa & _).
assert (Hin1 : In (cid, pos) (frames S1)) by (rewrite Hfrs; right; exact Hfin).
destruct (al_frames _ _ LAWS ly1 S1 W1 memT mdT cid pos HAR1 Hin1) as (_ & _ & Hpres1 & _).
rewrite Efa in Hpres1.
split; [lia|]. split; [lia|].
split. { intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (Hpres1 a ltac:(lia))). }
split. { apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid)); [exact Happ | lia | lia | lia | lia]. }
split.
{ apply (range_addressable_sub _ _ blk 34); [| lia | lia].
  exact (range_addressable_entry_frame SEGS B LAWS TCHECK_STEP_STK sp0 [] ly S W mem md _ ly1 S1 W1 memT mdT 0 cid pos blk 34
    HJ Hfin Hcid Hflo Hfhi Hfal ltac:(intros x (r & Hr & _); destruct Hr) HAR0 HRA). }
split.
{ apply (shadow_hull_vis_of_frame SEGS B LAWS ly1 S1 W1 memT mdT cid pos); [exact HAR1 | exact Hin1 | rewrite Efa; lia | rewrite Efa; lia | lia]. }
intros i Hi. apply (F4 cid pos (blk + d + i) Hfin).
- left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- intros (r & Hr & _). destruct Hr.
Qed.
Lemma cs2_body_facts : forall ly S W mem md sp0 ly1 S1 W1 memT mdT fpos body o n,
  ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 memT mdT 0 ->
  In (body, CS_BODY_LEN) (ablocks B ly S) -> ablocks B ly1 S1 = ablocks B ly S -> 0 <= o -> o + n <= CS_BODY_LEN -> 0 < n ->
  4096 <= body /\ body + CS_BODY_LEN <= alloc_ceiling /\
  (forall a, body + o <= a < body + o + n -> aview SEGS (w_H W1) memT a <> None) /\
  amem_range (body + o) n /\
  range_addressable (aview SEGS (w_H W1) memT) SHADOW_OFF (body + o) n /\
  shadow_hull_vis (aview SEGS (w_H W1) memT) (body + o) n /\
  (forall i, 0 <= i < n -> aview SEGS (w_H W1) memT (body + o + i) = aview SEGS (w_H W) mem (body + o + i)).
Proof.
intros ly S W mem md sp0 ly1 S1 W1 memT mdT fpos body o n HJ Hin Hab Ho Hon Hn. unfold CS_BODY_LEN in *.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hin1 : In (body, 8904) (ablocks B ly1 S1)) by (rewrite Hab; exact Hin).
destruct (al_blocks _ _ LAWS ly1 S1 W1 memT mdT body 8904 HAR1 Hin1) as (_ & H4096 & Hbc & _ & Hpres & _).
pose proof (req_size_pos 8904 ltac:(lia)) as [_ Hrq].
split; [lia|]. split; [lia|].
split. { intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (Hpres a ltac:(lia))). }
split. { apply (amem_range_of_block SEGS B LAWS ly1 S1 W1 memT mdT body 8904); [exact HAR1 | exact Hin1 | lia | lia]. }
split. { apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 memT mdT body 8904); [exact HAR1 | exact Hin1 | lia | lia]. }
split. { apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 memT mdT body 8904); [exact HAR1 | exact Hin1 | lia | lia | lia]. }
intros i Hi. replace (body + o + i) with (body + (o + i)) by lia.
apply (F2 body 8904 (o + i) Hin Hin1); [lia|]. intros (r & Hr & _). destruct Hr.
Qed.
Lemma cs2_tr_facts : forall ly S W mem md sp0 ly1 S1 W1 memT mdT fpos,
  ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 memT mdT 0 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  0 <= A_CS_TRAILER /\ A_CS_TRAILER + 12 <= alloc_ceiling /\
  (forall a, A_CS_TRAILER <= a < A_CS_TRAILER + 12 -> aview SEGS (w_H W1) memT a <> None) /\
  amem_range A_CS_TRAILER 12 /\
  range_addressable (aview SEGS (w_H W1) memT) SHADOW_OFF A_CS_TRAILER 12 /\
  shadow_hull_vis (aview SEGS (w_H W1) memT) A_CS_TRAILER 12 /\
  (forall i, 0 <= i < 12 -> aview SEGS (w_H W1) memT (A_CS_TRAILER + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))).
Proof.
intros ly S W mem md sp0 ly1 S1 W1 memT mdT fpos HJ HROD.
assert (HRO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) memT))
  by (eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B); [exact HJ | exact HROD]).
pose proof HJ as (HAR1 & _).
destruct (cs2_tr_shadow ly1 S1 W1 memT mdT HAR1) as [Hra Hhv].
destruct HB_ADDR as [ETR _].
pose proof asan_consts as (C1 & _).
assert (HV : forall i, 0 <= i < 12 -> aview SEGS (w_H W1) memT (A_CS_TRAILER + i) = Some (bv_unsigned (nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0)))).
{ intros i Hi. destruct (HRO_TR i ltac:(change (length scene_trailer) with 12%nat; lia)) as (Hro & Hno & Hne & Hv).
  rewrite (HRO1 _ Hro Hno Hne). exact Hv. }
split; [rewrite ETR; lia|]. split; [rewrite ETR; lia|].
split.
{ intros a Ha. assert (Hi : 0 <= a - A_CS_TRAILER < 12) by (destruct Ha; split; [apply Z.le_0_sub; exact H | apply Z.lt_sub_lt_add_r; rewrite Z.add_comm; exact H0]).
  pose proof (HV (a - A_CS_TRAILER) Hi) as X. rewrite Zplus_minus in X. rewrite X. discriminate. }
split. { rewrite ETR. unfold amem_range, kLowMemEnd. left. lia. }
split; [exact Hra|]. split; [exact Hhv | exact HV].
Qed.
(* ---- one bcmp call from check_step's frame, through aj_bcmp_at (Reusable/YCbq.v:2061), returning 0 ---- *)
Lemma cs2_bcmp : forall (sp0 : Z) ly S W mem md fpos ly1 S1 W1 (regsT : bvmap 5 word) memT mdT (x y n retk : Z)
  (Q : world SEGS -> config -> Prop),
  ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 memT mdT 0 ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n ->
  getr regsT 1 = Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 2 = w64 (sp0 - CHECK_STEP_FRAME) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= alloc_ceiling -> 0 <= y -> y + n <= alloc_ceiling ->
  (forall a, x <= a < x + n -> aview SEGS (w_H W1) memT a <> None) ->
  (forall a, y <= a < y + n -> aview SEGS (w_H W1) memT a <> None) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview SEGS (w_H W1) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W1) memT) x n) ->
  range_addressable (aview SEGS (w_H W1) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W1) memT) y n) ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W1) memT (x + i) = aview SEGS (w_H W1) memT (y + i)) ->
  (forall regs2 mem2 md2,
     ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 mem2 md2 0 ->
     aregs_preserved regsT regs2 -> getr regs2 10 = Z_to_bv 64 0 ->
     (forall a, cs2_out sp0 a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memT a) ->
     SRr SEGS W1 (mkCfg (mkst regs2 (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W1 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros sp0 ly S W mem md fpos ly1 S1 W1 regsT memT mdT x y n retk Q HJ Ha0 Ha1 Ha2 Hra Hrk Hrk2 Hsp Hgp Htp Hn Hx0 Hxc Hy0 Hyc
  Hvx Hvy Hmx Hmy Hrx Hhx Hry Hhy Heq Hk.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (FFS : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFR : CHECK_STEP_FRAME = 128) by reflexivity.
rewrite FFS in Hslo.
assert (Usp : spZ regsT = sp0 + -128).
{ unfold spZ. rewrite Hsp, HFR. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W1 regsT memT
    TCHECK_STEP_STK sp0 [] ly S W mem md [(CS_CID, fpos)] ly1 S1 mdT 0 x y n (-128)
    (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + retk)) HJ
    Ha0 Ha1 Ha2 Hn Hx0 ltac:(lia) Hy0 ltac:(lia) Usp ltac:(reflexivity) ltac:(lia) ltac:(rewrite Hes, FFS; lia) Hgp Htp Hra
    (ret_ok_codeptr_v retk Hrk Hrk2)).
  - intros a Ha. split; [exact (Hvx a Ha) | rewrite Usp, Hes; lia].
  - intros a Ha. split; [exact (Hvy a Ha) | rewrite Usp, Hes; lia].
  - intros a Ha. rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - exact Hmx.
  - exact Hmy.
  - exact Hrx.
  - exact Hhx.
  - exact Hry.
  - exact Hhy. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2).
apply (Hk regs2 mem2 md2 HJ2 HP2).
- rewrite Hv. apply (proj2 Hcmp). exact Heq.
- intros a [Ha Hna]. apply Hfr; [exact Ha|]. rewrite HFR in Hna. rewrite Hes in *. lia.
Qed.
(* ---- the cut state at 0x834d0 ---- *)
Lemma cs2_final : forall ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 (regsF : bvmap 5 word) memF mdF,
  cs_st2 SK B ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 ->
  ajournal SEGS B TCHECK_STEP_STK (spZ regs) [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 memF mdF 0 ->
  (forall a, cs2_out (spZ regs) a -> aview SEGS (w_H W1) memF a = aview SEGS (w_H W1) mem1 a) ->
  aregs_preserved regs1 regsF ->
  SRr SEGS W1 (mkCfg (mkst regsF (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + 0xc58)) memF (seg_rom SEGS)) mdF)
   (fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS CS_PC3 regs2 mem2 md2 /\
      cs_st3 SK B ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2).
Proof.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 regsF memF mdF HST HJF HKF HPF.
apply SRr_ret.
pose proof HST as (HPRE & HFRM & R19 & R20 & R21 & R24 & R22 & R23 & R16).
pose proof HFRM as (HJ & Hab & Hflag & Hsaved & R2 & R3 & R4 & R8 & R18 & R25 & R26 & R27).
pose proof HJ as (HAR1 & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (FFS : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFR : CHECK_STEP_FRAME = 128) by reflexivity.
rewrite FFS in Hslo.
assert (Hin : In (CS_CID, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly1 S1 W1 mem1 md1 CS_CID fpos HAR1 Hin) as (Hf0 & Hfc & _).
assert (Hfb : fs_frame_bytes CS_CID = 256) by reflexivity.
rewrite Hfb in Hfc.
assert (HKF' : forall a, (spZ regs - 104 <= a < spZ regs \/ frame_addr ly1 CS_CID fpos <= a < frame_addr ly1 CS_CID fpos + 256) ->
  aview SEGS (w_H W1) memF a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. apply HKF. unfold cs2_out. rewrite HFR, Hes. lia. }
exists ly1, S1, regsF, memF, mdF. split.
{ unfold cfg_at, w64. replace CS_PC3 with (@pa_val _ scene_listing PI A_TEXT + 0xc58) by (unfold CS_PC3, A_check_step, AF_check_step; lia).
  reflexivity. }
split; [exact HPRE|].
split.
{ split; [exact HJF|]. split; [exact Hab|].
  split.
  { rewrite (rdword_ext (aview SEGS (w_H W1) mem1) (aview SEGS (w_H W1) memF)); [exact Hflag|].
    intros q Hq. apply HKF'. right. rewrite Hfb. lia. }
  split.
  { intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W1) mem1) (aview SEGS (w_H W1) memF)); [exact (Hsaved j Hj)|].
    intros q Hq. apply HKF'. left. lia. }
  split; [etransitivity; [exact (HPF 2 ltac:(unfold acallee_saved; lia)) | exact R2]|].
  split; [etransitivity; [exact (HPF 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
  split; [etransitivity; [exact (HPF 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
  split; [etransitivity; [exact (HPF 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
  split; [etransitivity; [exact (HPF 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
  split; [etransitivity; [exact (HPF 25 ltac:(unfold acallee_saved; lia)) | exact R25]|].
  split; [etransitivity; [exact (HPF 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
  etransitivity; [exact (HPF 27 ltac:(unfold acallee_saved; lia)) | exact R27]. }
split; [etransitivity; [exact (HPF 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
split; [etransitivity; [exact (HPF 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
split; [etransitivity; [exact (HPF 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
split; [etransitivity; [exact (HPF 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
etransitivity; [exact (HPF 23 ltac:(unfold acallee_saved; lia)) | exact R23].
Qed.
(* ---- the offset and length of the payload ---- *)
Lemma cs2_and0 : forall x : word, alu64 ALU_AND x (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
intros x. rewrite <- (lit_of_word x) at 1. rewrite zalu64_sound. f_equal.
unfold zalu64, zcanon. cbn [zalu_raw]. rewrite Zmod_0_l, Z.land_0_r. apply Zmod_0_l.
Qed.
Lemma cs2_off_mid : forall k, 1 <= k <= 341 ->
  alu64 ALU_AND (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 k) (Z_to_bv 64 26)) (Z_to_bv 64 (-2))) (Z_to_bv 64 18446744073709551615)
  = Z_to_bv 64 (24 + 26 * (k - 1)).
Proof.
intros k Hk. rewrite zmd64_sound, !zalu64_sound. f_equal.
unfold zalu64, zmd64, zcanon, M64. cbn [zalu_raw zmd_raw].
change (2 ^ 64) with 18446744073709551616.
rewrite (Z.mod_small k) by lia.
try change (26 mod 18446744073709551616) with 26.
try change ((-2) mod 18446744073709551616) with 18446744073709551614.
try change (18446744073709551615 mod 18446744073709551616) with (Z.ones 64).
rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.
Lemma cs2_len_mid : forall k, k <> 0 -> k <> 342 -> scene_len k = 26.
Proof. intros k H0 H1. unfold scene_len. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.
(* ---- the walk's tactics ---- *)
Local Ltac cs2_km KM :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let K := fresh "K" in pose proof (cs2_km_run _ _ _ _ _ _ HFr KM) as K; clear KM HFr; rename K into KM end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* a branch whose condition the atoms' known values refute *)
Local Ltac cs2_kill :=
  match goal with Hc : branch_taken _ _ _ = _ |- _ =>
    exfalso; revert Hc; cbn [sv_denot];
    repeat match goal with H : ew ?E ?n = w64 _ |- context [ew ?E ?n] => rewrite H end;
    vm_compute; let X := fresh in intros X; discriminate X end.
(* run to the next call, deciding the branches on the way *)
Local Ltac cs2_loop RUNP RUNC BR KM HS HJ :=
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |];
  cs2_km KM;
  lazymatch goal with
  | H : st_ok_pi _ _ _ _ _ |- _ =>
      psrr_branch_pi RUNP BR H;
      [ first [ solve [cs2_kill] | cs2_loop RUNP RUNC BR KM H HJ ]
      | first [ solve [cs2_kill] | cs2_loop RUNP RUNC BR KM H HJ ] ]
  | _ => idtac
  end.
(* run to the cut pc 0x834d0 (offset 0xc58 = 3160), deciding the branches on the way *)
Local Ltac cs2_loop_to RUNP RUNTOP BR KM HS HJ :=
  paj_run_to_shc RUNTOP HS HJ 3160; [apply awr_ok_nil |];
  cs2_km KM;
  lazymatch goal with H : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 3160 => idtac
    | _ => psrr_branch_pi RUNP BR H;
           [ first [ solve [cs2_kill] | cs2_loop_to RUNP RUNTOP BR KM H HJ ]
           | first [ solve [cs2_kill] | cs2_loop_to RUNP RUNTOP BR KM H HJ ] ]
    end
  end.
(* ---- after a bcmp that returned 0: bnez not taken, then (k <> 342) bne taken, to the cut ---- *)
Lemma cs2_tail : forall ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 (regs2 : bvmap 5 word) mem2 md2 pc,
  (pc = 0xc34 /\ 0 <= k <= 341) \/ pc = 0xc54 ->
  cs_st2 SK B ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 ->
  ajournal SEGS B TCHECK_STEP_STK (spZ regs) [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 mem2 md2 0 ->
  (forall a, cs2_out (spZ regs) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) mem1 a) ->
  aregs_preserved regs1 regs2 -> getr regs2 10 = Z_to_bv 64 0 ->
  SRr SEGS W1 (mkCfg (mkst regs2 (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + pc)) mem2 (seg_rom SEGS)) md2)
   (fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS CS_PC3 regs2 mem2 md2 /\
      cs_st3 SK B ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2).
Proof.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 regs2 mem2 md2 pc Hpc HST HJ2 KM HP H10.
pose proof HST as (HPRE & HFRM & R19 & R20 & _).
pose proof (cs2_entry W1 regs2 mem2 pc) as HS.
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env (@pa_val _ scene_listing PI) A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (F10 : ew E 10 = w64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10).
assert (E20 : ew E 20 = getr regs2 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 [] 20 20%bv eq_refl)).
assert (R20' : getr regs2 20 = w64 k) by (etransitivity; [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
clear HE.
destruct Hpc as [[-> Hk'] | ->].
- pose proof (st_ok_pi_add_fact E _ _ 20 (mkAF 0 341 0) HS (cs2_af E regs2 k 0 341 E20 R20' Hk' ltac:(lia))) as HS0.
  clear HS. rename HS0 into HS.
  cs2_loop_to RUNP RUNTOP BR KM HS HJ2.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS HAE ltac:(vm_compute; reflexivity)) as HPF.
  pmkst HS.
  exact (cs2_final ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 _ _ _ HST HJ2 KM (aregs_preserved_trans _ _ _ HP HPF)).
- cs2_loop_to RUNP RUNTOP BR KM HS HJ2.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS HAE ltac:(vm_compute; reflexivity)) as HPF.
  pmkst HS.
  exact (cs2_final ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 _ _ _ HST HJ2 KM (aregs_preserved_trans _ _ _ HP HPF)).
Qed.
Lemma cs_S2 : CS_S2_stmt SK B.
Proof.
unfold CS_S2_stmt.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 HST.
pose proof HST as (HPRE & HFRM & R19 & R20 & R21 & R24 & R22 & R23 & R16).
pose proof HPRE as (HAFN & Hsp32 & Htop & Hnfr & HROD & A10 & A11 & A12 & Hk & HFO & HBODY & Hlenb & Hbody & Hblk & Hnev & Hlive).
pose proof HFRM as (HJ & Hab & Hflag & Hsaved & R2 & R3 & R4 & R8 & R18 & R25 & R26 & R27).
pose proof HAFN as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
unfold CS_LAST in Hk.
assert (Hlb : length b = Z.to_nat 8904) by exact Hlenb.
assert (KM : forall a, cs2_out (spZ regs) a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W1) mem1 a) by reflexivity.
pose proof (cs2_entry W1 regs1 mem1 0xbe4) as HS.
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env (@pa_val _ scene_listing PI) A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 4 4%bv eq_refl)).
assert (E16 : ew E 16 = getr regs1 16) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 16 16%bv eq_refl)).
assert (E19 : ew E 19 = getr regs1 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 19 19%bv eq_refl)).
assert (E20 : ew E 20 = getr regs1 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 20 20%bv eq_refl)).
assert (E24 : ew E 24 = getr regs1 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 [] 24 24%bv eq_refl)).
clear HE.
pose proof asan_consts as (C1 & _).
change (cfg_at SEGS CS_PC2 regs1 mem1 md1) with (mkCfg (mkst regs1 (Z_to_bv 64 CS_PC2) mem1 (seg_rom SEGS)) md1).
replace CS_PC2 with (@pa_val _ scene_listing PI A_TEXT + 0xbe4) by (unfold CS_PC2, A_check_step, AF_check_step; lia).
destruct (Z.eq_dec k 0) as [Hk0 | Hk0]; [| destruct (Z.eq_dec k 342) as [Hk342 | Hk342]].
- (* k = 0: payload blk[9..33) against body[0..24) *)
  subst k.
  assert (EK : ew E 20 = w64 0) by (rewrite E20; exact R20).
  pose proof (st_ok_pi_add_fact E _ _ 20 (mkAF 0 0 0) HS (cs2_af E regs1 0 0 0 E20 R20 ltac:(lia) ltac:(lia))) as HS0.
  clear HS. rename HS0 into HS.
  cs2_loop RUNP RUNC BR KM HS HJ.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs1 [] HS HAE ltac:(vm_compute; reflexivity)) as KPa.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  pmkst HS.
  destruct (cs2_blk_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos blk 9 24 HAR0 HJ HFO ltac:(lia) ltac:(unfold CS_BLK_LEN; lia) ltac:(lia))
    as (X4 & Xc & Xv & Xm & Xr & Xh & Xe).
  destruct (cs2_body_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos body 0 24 HJ HBODY Hab ltac:(lia) ltac:(unfold CS_BODY_LEN; lia) ltac:(lia))
    as (Y4 & Yc & Yv & Ym & Yr & Yh & Ye).
  unfold CS_BLK_LEN, CS_BODY_LEN in *.
  apply (cs2_bcmp (spZ regs) ly S W mem md fpos ly1 S1 W1 _ _ _ (blk + 9) (body + 0) 24 0xc34 _ HJ).
  + rewrite Q10, E19, R19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q11, E16, E20, R16, R20, cs2_and0. unfold w64. rewrite alu64_add_lit. reflexivity.
  + rewrite Q12, E24, R24. reflexivity.
  + exact Q1.
  + lia.
  + reflexivity.
  + rewrite Q2, E2. exact R2.
  + rewrite Q3, E3, R3. exact Hgp0.
  + rewrite Q4, E4, R4. exact Htp0.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + exact Xv.
  + exact Yv.
  + exact Xm.
  + exact Ym.
  + exact Xr.
  + intros _; exact Xh.
  + exact Yr.
  + intros _; exact Yh.
  + intros i Hi. rewrite (Xe i Hi), (Ye i Hi).
    replace (blk + 9 + i) with (blk + (9 + i)) by lia. replace (body + 0 + i) with (body + (0 + i)) by lia.
    rewrite (Hblk (9 + i)) by lia. rewrite (Hbody (0 + i)) by lia.
    rewrite (cs2_payload_0 b i Hlb Hi). reflexivity.
  + intros regs2 mem2 md2 HJ2 HP2 H10 HK2.
    apply (cs2_tail ly S W regs mem md ch blk body 0 b fpos ly1 S1 W1 regs1 mem1 md1 regs2 mem2 md2 0xc34
      ltac:(left; split; [reflexivity | lia]) HST HJ2).
    * intros a Ha. rewrite (HK2 a Ha). exact (KM a Ha).
    * exact (aregs_preserved_trans _ _ _ KPa HP2).
    * exact H10.
- (* k = 342: payload blk[7..21) against body[8890..8904), then trailer blk[21..33) against check_step.trailer *)
  subst k.
  assert (EK : ew E 20 = w64 342) by (rewrite E20; exact R20).
  pose proof (st_ok_pi_add_fact E _ _ 20 (mkAF 342 342 0) HS (cs2_af E regs1 342 342 342 E20 R20 ltac:(lia) ltac:(lia))) as HS0.
  clear HS. rename HS0 into HS.
  cs2_loop RUNP RUNC BR KM HS HJ.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs1 [] HS HAE ltac:(vm_compute; reflexivity)) as KPa.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  pmkst HS.
  destruct (cs2_blk_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos blk 7 14 HAR0 HJ HFO ltac:(lia) ltac:(unfold CS_BLK_LEN; lia) ltac:(lia))
    as (X4 & Xc & Xv & Xm & Xr & Xh & Xe).
  destruct (cs2_body_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos body 8890 14 HJ HBODY Hab ltac:(lia) ltac:(unfold CS_BODY_LEN; lia) ltac:(lia))
    as (Y4 & Yc & Yv & Ym & Yr & Yh & Ye).
  unfold CS_BLK_LEN, CS_BODY_LEN in *.
  apply (cs2_bcmp (spZ regs) ly S W mem md fpos ly1 S1 W1 _ _ _ (blk + 7) (body + 8890) 14 0xc34 _ HJ).
  + rewrite Q10, E19, R19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q11, E16, R16. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q12, E24, R24. reflexivity.
  + exact Q1.
  + lia.
  + reflexivity.
  + rewrite Q2, E2. exact R2.
  + rewrite Q3, E3, R3. exact Hgp0.
  + rewrite Q4, E4, R4. exact Htp0.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + exact Xv.
  + exact Yv.
  + exact Xm.
  + exact Ym.
  + exact Xr.
  + intros _; exact Xh.
  + exact Yr.
  + intros _; exact Yh.
  + intros i Hi. rewrite (Xe i Hi), (Ye i Hi).
    replace (blk + 7 + i) with (blk + (7 + i)) by lia. replace (body + 8890 + i) with (body + (8890 + i)) by lia.
    rewrite (Hblk (7 + i)) by lia. rewrite (Hbody (8890 + i)) by lia.
    rewrite (cs2_payload_342 b i Hlb Hi). reflexivity.
  + intros regs2 mem2 md2 HJ2 HP2 H10 HK2.
    assert (KM2 : forall a, cs2_out (spZ regs) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) mem1 a)
      by (intros a Ha; rewrite (HK2 a Ha); exact (KM a Ha)).
    pose proof (aregs_preserved_trans _ _ _ KPa HP2) as KP2.
    clear HS Q1 Q2 Q3 Q4 Q10 Q11 Q12 KM HK2 Xe Ye EK.
    pose proof (cs2_entry W1 regs2 mem2 0xc34) as HS.
    remember (Eimg (Ereg regs2 [])) as E' eqn:HE'.
    assert (HEI' : img_env (@pa_val _ scene_listing PI) A_LIM E') by (subst E'; apply Eimg_env).
    assert (HAE' : env_agree 32 (Ereg regs2 []) E') by (split; [intros n Hn; subst E'; apply Eimg_low; unfold A_TEXT; lia | subst E'; reflexivity]).
    assert (F2 : ew E' 2 = w64 (spZ regs - CHECK_STEP_FRAME)) by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 [] 2 2%bv eq_refl); etransitivity; [exact (KP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
    assert (F3 : ew E' 3 = w64 (as_gp B)) by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 [] 3 3%bv eq_refl); etransitivity; [exact (KP2 3 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact R3 | exact Hgp0]]).
    assert (F4 : ew E' 4 = w64 (as_tp B)) by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 [] 4 4%bv eq_refl); etransitivity; [exact (KP2 4 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact R4 | exact Htp0]]).
    assert (F10 : ew E' 10 = w64 0) by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10).
    assert (F19 : ew E' 19 = w64 blk) by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 [] 19 19%bv eq_refl); etransitivity; [exact (KP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
    assert (F20 : ew E' 20 = w64 342) by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 [] 20 20%bv eq_refl); etransitivity; [exact (KP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
    assert (FTR : ew E' 248 = Z_to_bv 64 A_CS_TRAILER)
      by (subst E'; apply Eimg_img; split; [apply Nat.leb_le | apply Nat.ltb_lt]; reflexivity).
    clear HE'.
    cs2_loop RUNP RUNC BR KM2 HS HJ2.
    pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS HAE' ltac:(vm_compute; reflexivity)) as KPb.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    pmkst HS.
    destruct (cs2_blk_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos blk 21 12 HAR0 HJ2 HFO ltac:(lia) ltac:(unfold CS_BLK_LEN; lia) ltac:(lia))
      as (X4' & Xc' & Xv' & Xm' & Xr' & Xh' & Xe').
    destruct (cs2_tr_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos HJ2 HROD) as (T0 & Tc & Tv & Tm & Tr & Th & Te).
    apply (cs2_bcmp (spZ regs) ly S W mem md fpos ly1 S1 W1 _ _ _ (blk + 21) A_CS_TRAILER 12 0xc54 _ HJ2).
    * rewrite Q10, F19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * rewrite Q11, FTR. reflexivity.
    * rewrite Q12. reflexivity.
    * exact Q1.
    * lia.
    * reflexivity.
    * rewrite Q2, F2. reflexivity.
    * rewrite Q3, F3. reflexivity.
    * rewrite Q4, F4. reflexivity.
    * lia.
    * lia.
    * lia.
    * exact T0.
    * exact Tc.
    * exact Xv'.
    * exact Tv.
    * exact Xm'.
    * exact Tm.
    * exact Xr'.
    * intros _; exact Xh'.
    * exact Tr.
    * intros _; exact Th.
    * intros i Hi. rewrite (Xe' i Hi), (Te i Hi).
      replace (blk + 21 + i) with (blk + (21 + i)) by lia.
      rewrite (Hblk (21 + i)) by lia. rewrite (cs2_trailer_nth b i Hlb Hi). reflexivity.
    * intros regs3 mem3 md3 HJ3 HP3 H10' HK3.
      apply (cs2_tail ly S W regs mem md ch blk body 342 b fpos ly1 S1 W1 regs1 mem1 md1 regs3 mem3 md3 0xc54 (or_intror eq_refl) HST HJ3).
      -- intros a Ha. rewrite (HK3 a Ha). exact (KM2 a Ha).
      -- exact (aregs_preserved_trans _ _ _ KP2 (aregs_preserved_trans _ _ _ KPb HP3)).
      -- exact H10'.
- (* 1 <= k <= 341: payload blk[7..33) against body[24 + 26 (k - 1) ..+26) *)
  pose proof (st_ok_pi_add_fact E _ _ 20 (mkAF 1 341 0) HS (cs2_af E regs1 k 1 341 E20 R20 ltac:(lia) ltac:(lia))) as HS0.
  clear HS. rename HS0 into HS.
  cs2_loop RUNP RUNC BR KM HS HJ.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs1 [] HS HAE ltac:(vm_compute; reflexivity)) as KPa.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  pmkst HS.
  destruct (cs2_blk_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos blk 7 26 HAR0 HJ HFO ltac:(lia) ltac:(unfold CS_BLK_LEN; lia) ltac:(lia))
    as (X4 & Xc & Xv & Xm & Xr & Xh & Xe).
  destruct (cs2_body_facts ly S W mem md (spZ regs) ly1 S1 W1 _ _ fpos body (24 + 26 * (k - 1)) 26 HJ HBODY Hab ltac:(lia) ltac:(unfold CS_BODY_LEN; lia) ltac:(lia))
    as (Y4 & Yc & Yv & Ym & Yr & Yh & Ye).
  unfold CS_BLK_LEN, CS_BODY_LEN in *.
  apply (cs2_bcmp (spZ regs) ly S W mem md fpos ly1 S1 W1 _ _ _ (blk + 7) (body + (24 + 26 * (k - 1))) 26 0xc34 _ HJ).
  + rewrite Q10, E19, R19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q11, E16, E20, R16, R20. unfold w64. rewrite (cs2_off_mid k ltac:(lia)), alu64_add_lit. reflexivity.
  + rewrite Q12, E24, R24, (cs2_len_mid k Hk0 Hk342). reflexivity.
  + exact Q1.
  + lia.
  + reflexivity.
  + rewrite Q2, E2. exact R2.
  + rewrite Q3, E3, R3. exact Hgp0.
  + rewrite Q4, E4, R4. exact Htp0.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + exact Xv.
  + exact Yv.
  + exact Xm.
  + exact Ym.
  + exact Xr.
  + intros _; exact Xh.
  + exact Yr.
  + intros _; exact Yh.
  + intros i Hi. rewrite (Xe i Hi), (Ye i Hi).
    replace (blk + 7 + i) with (blk + (7 + i)) by lia.
    replace (body + (24 + 26 * (k - 1)) + i) with (body + (24 + 26 * (k - 1) + i)) by lia.
    rewrite (Hblk (7 + i)) by lia. rewrite (Hbody (24 + 26 * (k - 1) + i)) by lia.
    rewrite (cs2_payload_mid b k i Hlb ltac:(lia) Hi). reflexivity.
  + intros regs2 mem2 md2 HJ2 HP2 H10 HK2.
    apply (cs2_tail ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 regs2 mem2 md2 0xc34
      ltac:(left; split; [reflexivity | lia]) HST HJ2).
    * intros a Ha. rewrite (HK2 a Ha). exact (KM a Ha).
    * exact (aregs_preserved_trans _ _ _ KPa HP2).
    * exact H10.
Qed.
End h.
End f.
End d.
Print Assumptions cs_S2.
About cs_S2.
