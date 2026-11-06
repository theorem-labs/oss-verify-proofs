(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v, with its module names changed; 688 of its 741 lines of code are new or changed and 157 lines of the source are left out. *)
(* Segment lemma cs_S3 of check_step's asan walk (a Theorem Labs lane, 2026-10-29), proved against the cut statement of
   P_check_step_cut.v. Rule 24 is met: this file proves one segment of the walk, not the function; its callees are
   the Section hypotheses AMEMCPY, PARSE, CKV.

   Segment S3 of the ASan walk of check_step in fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026): 0x834d0 .. 0x83570.
   C5: unpoison frame, __asan_memcpy x2 through aj_intrin_at (YCbq.v:1955) (16 + 34 B), unpoison p, reac_ctrl_parse on the journal (PARSE), the four field checks, reac_ctrl_checksum_verify through cl_callS (A/Prog/YC85.v:383, CKV). Donor: newgif's memcpy and RAWNEWX call (cgif A/ACk1.v:364, A/ACjw.v:318-350).
   Pre: the cut state at its first pc; post: cs_st4 at the next cut pc
   (P_check_step_cut.v).
   The walk: run 1 (0x834d0, frame shadow 4..10 := 00 x6, 02) to the first __asan_memcpy (F + 32 <- __const.check_step.frame,
   16 B; source hull from HB_ADDR with HB_Z_TR / HB_Z_CF / HB_C_CS); run 2; __asan_memcpy (F + 48 <- blk, 34 B); run 3
   (p shadow 16..20 := 00 x4, 04); reac_ctrl_parse (F + 32, 50, F + 128) with fr = s3_fr b k (P_check_step_S3_aux.v),
   r = 2 by s3_fr_parse; run 4 with the 36 bytes of p as a read-only region, two field branches refuted (seg, length:
   zero-extended bytes of s5 / s8); reac_ctrl_checksum_verify (F + 32) with BS = s3_bs b k (blocksum 0 by s3_bs_ok);
   run 5 (bnez a0 with a0 = 0) to 0x83570. The 13 saved slots and the flag word are carried by explicit keep facts
   through every write window (runs: the shadow regions; memcpy: destination and [sp0 - 4224, sp0 - 128); parse:
   acall_kept; checksum_verify: its journal). *)
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
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC4b YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame P_check_step_cut P_check_step_S3_aux.
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
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
(* reac_ctrl_parse: a Theorem Labs lane (63ad3e6dcfa). *)
Hypothesis PARSE : tctrl_parse_spec (SK := SK) B.
(* reac_ctrl_checksum_verify (a Theorem Labs lane 61afd7acb1d). *)
Hypothesis CKV : tctrl_checksum_verify_spec (SK := SK) B.
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
(* The two globals' addresses (a Theorem Labs lane's decision, the one static fact this segment adds): the 8-aligned shadow hull
   of __asan_memcpy's source [A_CS_CFRAME, +16) at 0x83500 is 0x7fffc1b0..0x7fffc1b7, the trailer's c1b0..c1b3 and the
   frame's c1b4..c1b7, which HB_Z_TR / HB_Z_CF / HB_C_CS name only at these addresses. Closed by vm_compute on scene's
   PI. *)
Hypothesis HB_ADDR : A_CS_TRAILER = 0x20d80 /\ A_CS_CFRAME = 0x20da0.
Hypothesis HRO_CF : ro_bytes SEGS pa_relro_lo pa_relro_hi B A_CS_CFRAME cs_frame_init.
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
Lemma s3_div8_add : forall x c, x mod 8 = 0 -> (x + 8 * c) / 8 = x / 8 + c.
Proof.
intros x c Hx. rewrite (Z.div_mod x 8) at 1 by lia. rewrite Hx, Z.add_0_r.
replace (8 * (x / 8) + 8 * c) with ((x / 8 + c) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma s3_ra_zero : forall (rd : reader) a n, a mod 8 = 0 -> n mod 8 = 0 ->
(forall i, 0 <= i < n / 8 -> rd (SHADOW_OFF + a / 8 + i) = Some 0) -> range_addressable rd SHADOW_OFF a n.
Proof.
intros rd a n Ha Hn H. apply zero_shadow_range; [exact Ha | exact Hn |]. intros i Hi. unfold shadow_of_addr. apply H. exact Hi.
Qed.
Lemma s3_ra_part : forall (rd : reader) a q r, a mod 8 = 0 -> 0 <= q -> 0 < r < 8 ->
(forall i, 0 <= i < q -> rd (SHADOW_OFF + a / 8 + i) = Some 0) -> rd (SHADOW_OFF + a / 8 + q) = Some r ->
range_addressable rd SHADOW_OFF a (8 * q + r).
Proof.
intros rd a q r Ha Hq Hr H0 Hl x Hx. unfold shadow_of_addr.
assert (Ex : x / 8 = a / 8 + (x - a) / 8).
{ replace x with (a + (x - a)) at 1 by lia. rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r.
  replace (8 * (a / 8) + (x - a)) with ((x - a) + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (Hd : 0 <= (x - a) / 8 < q + 1) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Ex, Z.add_assoc.
destruct (Z.eq_dec ((x - a) / 8) q) as [Eq|Nq].
- rewrite Eq. exists r. split; [exact Hl|]. right.
  assert (Hm : x mod 8 = (x - a) mod 8).
  { rewrite (Z.div_mod a 8) at 1 by lia. rewrite Ha, Z.add_0_r. replace (x - 8 * (a / 8)) with (x + (- (a / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.div_mod (x - a) 8 ltac:(lia)) as Hdm. rewrite Eq in Hdm. lia.
- exists 0. split; [apply H0; lia | left; reflexivity].
Qed.
Lemma s3_kept_run : forall E rs (H : word -> bool) (mA mB : word -> option byte) a,
frame_of E rs (mrestrict H mA) (mrestrict H mB) -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H mB a = aview SEGS H mA a.
Proof. intros E rs H mA mB a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
Lemma s3_shb : forall E (H : word -> bool) mem n b cs lo hi wlo whi od v,
region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
aview SEGS H mem (b + od) = Some v.
Proof.
intros E H mem n b cs lo hi wlo whi od v HR Hn Hc Hv.
apply aview_of_val_mem1; [|exact Hv]. exact (field_of_region E _ n b cs lo hi wlo whi od 1 (SLit v) v HR Hn Hc eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma s3_const1 : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
In (z1 (ANum a) v) (as_const B ly) -> aview SEGS (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as X.
unfold cell_holds in X. cbn [c_at YG0f.c_val c_w aeval z1 c1] in X. specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X.
Qed.
Lemma s3_zs_byte : forall ly S (W : world SEGS) mem md a n x, AR SEGS B ly S W mem md ->
Exists (zr_sub (a, n)) (as_zero_shadow B) -> a <= x < a + n -> aview SEGS (w_H W) mem (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros ly S W mem md a n x HAR HE Hx. apply Exists_exists in HE as ((q & m) & Hin & Hsub). unfold zr_sub in Hsub. cbn [fst snd] in Hsub.
destruct (zs_range SEGS B q m Hin ly S W mem md HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
pose proof (zs_zero SEGS B LAWS q m Hin ly S W mem md HAR) as Hz.
assert (Eq8 : q = 8 * (q / 8)) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
assert (Em8 : m = 8 * (m / 8)) by (pose proof (Z.div_mod m 8 ltac:(lia)); lia).
assert (Ex : x / 8 = q / 8 + (x - q) / 8).
{ replace x with ((x - q) + (q / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
rewrite Ex, Z.add_assoc. apply Hz. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; lia.
Qed.
Lemma s3_cf_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (aview SEGS (w_H W) mem) A_CS_CFRAME 16.
Proof.
intros ly S W mem md HAR s Hs. destruct HB_ADDR as [ET EC].
destruct (HB_C_CS ly) as (C1 & C2 & C3 & _).
assert (K1 : shadow_addr A_CS_CFRAME / 8 * 8 = shadow_addr A_CS_TRAILER) by (rewrite ET, EC; vm_compute; reflexivity).
assert (K2 : shadow_addr (A_CS_CFRAME + 16 - 1) / 8 * 8 + 8 = shadow_addr A_CS_TRAILER + 8) by (rewrite ET, EC; vm_compute; reflexivity).
rewrite K1, K2 in Hs.
assert (Hc : s = shadow_addr A_CS_TRAILER \/ s = shadow_addr A_CS_TRAILER + 1 \/ s = shadow_addr A_CS_TRAILER + 2 \/
  s = shadow_addr A_CS_TRAILER + 3 \/ shadow_addr A_CS_TRAILER + 4 <= s < shadow_addr A_CS_TRAILER + 8) by lia.
destruct Hc as [-> | [-> | [-> | [-> | Hc]]]].
- unfold shadow_addr. assert (Hb : A_CS_TRAILER <= A_CS_TRAILER < A_CS_TRAILER + 8) by lia.
  rewrite (s3_zs_byte ly S W mem md A_CS_TRAILER 8 A_CS_TRAILER HAR HB_Z_TR Hb). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR C1). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR C2). discriminate.
- rewrite (s3_const1 ly S W mem md _ _ HAR C3). discriminate.
- assert (K3 : shadow_addr A_CS_TRAILER + 4 = SHADOW_OFF + A_CS_CFRAME / 8) by (rewrite ET, EC; vm_compute; reflexivity).
  assert (K4 : A_CS_CFRAME mod 8 = 0) by (rewrite EC; reflexivity).
  replace s with (SHADOW_OFF + (A_CS_CFRAME + 8 * (s - (shadow_addr A_CS_TRAILER + 4))) / 8).
  + assert (Hb : A_CS_CFRAME <= A_CS_CFRAME + 8 * (s - (shadow_addr A_CS_TRAILER + 4)) < A_CS_CFRAME + 48) by lia.
    rewrite (s3_zs_byte ly S W mem md A_CS_CFRAME 48 _ HAR HB_Z_CF Hb). discriminate.
  + rewrite s3_div8_add by exact K4. lia.
Qed.
Lemma s3_cf_ra : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_CS_CFRAME 16.
Proof.
intros ly S W mem md HAR x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
exact (s3_zs_byte ly S W mem md A_CS_CFRAME 48 x HAR HB_Z_CF ltac:(lia)).
Qed.
Lemma s3_cf_bytes : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
forall i, 0 <= i < 50 -> aview SEGS (w_H W) mem (A_CS_CFRAME + i) = Some (bv_unsigned (nth (Z.to_nat i) cs_frame_init (Z_to_bv 8 0))).
Proof.
intros W mem HR i Hi. destruct (HRO_CF i ltac:(cbn; lia)) as (H1 & H2 & H3 & H4).
rewrite (HR _ H1 H2 H3). exact H4.
Qed.
Lemma s3_keep : forall regs F fl (rd rd' : reader),
  (forall a, spZ regs - 104 <= a < spZ regs -> rd' a = rd a) ->
  (forall a, F + 248 <= a < F + 256 -> rd' a = rd a) ->
  cs_saved regs rd /\ rdword rd (F + 256 - 8) = Some fl ->
  cs_saved regs rd' /\ rdword rd' (F + 256 - 8) = Some fl.
Proof.
intros regs F fl rd rd' H1 H2 [Hs Hf]. split.
- intros j Hj. rewrite (rdword_ext rd rd'); [apply Hs; exact Hj|]. intros k Hk. apply H1. lia.
- rewrite (rdword_ext rd rd'); [exact Hf|]. intros k Hk. apply H2. lia.
Qed.
(* The registers check_step keeps through S3: sp, gp, tp, s0, s2 (frame), s3 (blk), s5 (segment), s6 (&frame),
   s7 (&p), s8 (length), s9 (frame shadow), s10 (frame), s11 (shadow base). *)
Definition s3_rk (sp0 gp tp F blk seg len : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = w64 (sp0 - 128) /\ getr r 3 = w64 gp /\ getr r 4 = w64 tp /\ getr r 8 = w64 sp0 /\
  getr r 18 = w64 F /\ getr r 19 = w64 blk /\ getr r 21 = w64 seg /\ getr r 22 = w64 (F + 32) /\
  getr r 23 = w64 (F + 128) /\ getr r 24 = w64 len /\ getr r 25 = w64 (SHADOW_OFF + F / 8) /\
  getr r 26 = w64 F /\ getr r 27 = w64 SHADOW_OFF.
Lemma s3_rk_pres : forall sp0 gp tp F blk seg len (r r' : bvmap 5 word),
  aregs_preserved r r' -> s3_rk sp0 gp tp F blk seg len r -> s3_rk sp0 gp tp F blk seg len r'.
Proof.
intros sp0 gp tp F blk seg len r r' H (E2 & E3 & E4 & E8 & E18 & E19 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
unfold s3_rk.
repeat split; match goal with |- getr r' ?x = ?v => transitivity (getr r x);
  [let n := eval vm_compute in (bv_unsigned x) in exact (H n ltac:(unfold acallee_saved; lia)) | assumption] end.
Qed.
Lemma s3_rk_kept : forall sp0 gp tp F blk seg len (r r' : bvmap 5 word),
  (forall x, In x [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x) ->
  s3_rk sp0 gp tp F blk seg len r -> s3_rk sp0 gp tp F blk seg len r'.
Proof.
intros sp0 gp tp F blk seg len r r' H (E2 & E3 & E4 & E8 & E18 & E19 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
repeat split; (etransitivity; [apply H; cbn; tauto | assumption]).
Qed.
Lemma s3_fa : forall n ly ly' c p, layout_le n ly ly' -> frame_addr ly' c p = frame_addr ly c p /\ flag_addr ly' c p = flag_addr ly c p.
Proof. intros n ly ly' c p Hly. destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity. Qed.
Lemma s3_obj_kept : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k p n,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k -> afobj SEGS B ly S W mem p n ->
  forall a, p <= a < p + n -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n HJ ((cid & pos & Hin & _ & _ & Hlo & Hhi) & _ & _) a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros (r & Hr & _); destruct Hr].
Qed.
Lemma s3_obj_ra : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k p n,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md -> afobj SEGS B ly S W mem p n ->
  range_addressable (aview SEGS (w_H W') mem') SHADOW_OFF p n.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n HJ HAR ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & Hra).
eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ | exact Hin | exact Hc | exact Hlo | exact Hhi | exact Hal | | exact HAR | exact Hra].
intros x (r & Hr & _). destruct Hr.
Qed.
Lemma s3_obj_hull : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k p n,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k -> afobj SEGS B ly S W mem p n -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W') mem') p n.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n HJ ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & _) Hn.
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfrs & _).
destruct (s3_fa _ _ _ cid pos Hly) as [EF _].
apply (shadow_hull_vis_of_frame SEGS B LAWS ly' S' W' mem' md' cid pos p n HAR'); [rewrite Hfrs; apply in_or_app; right; exact Hin | lia | lia | exact Hn].
Qed.
Lemma s3_obj_amr : forall ly S W mem md p n, AR SEGS B ly S W mem md -> afobj SEGS B ly S W mem p n -> 0 <= n -> amem_range p n.
Proof.
intros ly S W mem md p n HAR ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & _) Hn.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4 & Hce & Happ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kHighMemBeg. lia.
Qed.
Lemma s3_obj_bounds : forall ly S W mem md p n, AR SEGS B ly S W mem md -> afobj SEGS B ly S W mem p n ->
  4096 <= p /\ p + n <= alloc_ceiling.
Proof.
intros ly S W mem md p n HAR ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4 & Hce & Happ). lia.
Qed.
Lemma s3_obj_disj : forall STK sp0 ly S W mem md c0 p0 ly' S' W' mem' md' k p n,
  ajournal SEGS B STK sp0 [] ly S W mem md [(c0, p0)] ly' S' W' mem' md' k -> afobj SEGS B ly S W mem p n ->
  frame_addr ly' c0 p0 + fs_frame_bytes c0 <= p \/ p + n <= frame_addr ly' c0 p0.
Proof.
intros STK sp0 ly S W mem md c0 p0 ly' S' W' mem' md' k p n HJ ((cid & pos & Hin & Hc & Hal & Hlo & Hhi) & _ & _).
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfrs & _).
destruct (s3_fa _ _ _ cid pos Hly) as [EF _].
destruct (in_split _ _ Hin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly' S' W' mem' md' (c0, p0) (cid, pos) [] l2 l3 HAR' ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. lia.
Qed.
Lemma s3_vm_of_aview : forall (H : word -> bool) (m : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview SEGS H m (a + Z.of_nat k) = Some (le_byte v n k)) -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hk k Hlt. destruct (aview_byte SEGS H m (a + Z.of_nat k) _ (Hk k Hlt)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned | f_equal; rewrite <- Hv; reflexivity].
Qed.
Lemma s3_lb10 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. change (2 ^ 8) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma s3_lb20 : forall v, 0 <= v < 256 -> le_byte v 2 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0. change (2 ^ 16) with 65536.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 65536) by lia. apply Z.mod_small. lia.
Qed.
Lemma s3_lb21 : forall v, 0 <= v < 256 -> le_byte v 2 1 = 0.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8. change (2 ^ 16) with 65536.
rewrite (Z.mod_small v 65536) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma s3_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma s3_soff : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma s3_zext_atom : forall E n w v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ Z.of_N w -> Z.of_N w <= 64 ->
  sv_denot E (SExt false w (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n w v H Hv Hw.
assert (Hv64 : 0 <= v < 2 ^ 64) by (split; [lia|]; eapply Z.lt_le_trans; [apply Hv | apply Z.pow_le_mono_r; lia]).
cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (zext_low_sound false w v) as Z0. cbn iota in Z0. rewrite Z0.
unfold zext_low, zcanon, M64. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Local Ltac s3_kill Hc :=
  exfalso; repeat match goal with H : sv_denot _ _ = Z_to_bv 64 _ |- _ => rewrite H in Hc end;
  cbn [branch_taken] in Hc; rewrite s3_eqb_refl in Hc; discriminate Hc.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma cs_S3 : CS_S3_stmt SK B.
Proof.
unfold CS_S3_stmt.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 HS3.
destruct HS3 as (HPRE & HFR & R19 & R21 & R24 & R22 & R23).
destruct HFR as (HJ & HAB & HFLAG & HSAV & R2 & R3 & R4 & R8 & R18 & R25 & R26 & R27).
pose proof HPRE as (HAFN & Hal32 & Htop32 & Hlen7 & HROD & Ha0 & Ha1 & Ha2 & Hk & HFO & Hbody & Hlenb & Hbodyb & Hblkb & Hev & Hlive).
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR1 & Hly1 & Hsecs1 & Hwle1 & Hio1 & Hfrs1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTK : TCHECK_STEP_STK = 8496) by (vm_compute; reflexivity).
assert (ESTK' : TPARSE_STK = 8352) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
destruct HB_ADDR as [ETR ECF].
change CS_CID with 2 in *. change CHECK_STEP_FRAME with 128 in *.
set (sp0 := spZ regs) in *.
set (F := frame_addr ly1 2 fpos) in *.
assert (Hfin1 : In (2, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly1 S1 W1 mem1 md1 2 fpos HAR1 Hfin1) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly1 S1 W1 mem1 md1 2 fpos HAR1 Hfin1) as (HF32 & _ & HFpres & HFSpres).
pose proof (frm_off_imgP B ly1 S1 W1 mem1 md1 2 fpos HAR1 Hfin1) as HFimg.
change (fs_frame_bytes 2) with 256 in *. fold F in HF4096, HFceil, HFapp, HF32, HFpres, HFSpres, HFimg.
change (256 / 8) with 32 in HFSpres.
unfold shadow_addr in HFSpres.
assert (HF8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HspR : 0 <= sp0 - 128 < 2 ^ 64) by lia.
set (sF := SHADOW_OFF + F / 8) in *.
assert (HsF : 2147450880 + 512 <= sF < 17592186044416 + 2147450880) by (subst sF; unfold SHADOW_OFF; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
  pose proof (Z.div_le_lower_bound F 8 512 ltac:(lia) ltac:(lia)); pose proof (Z.div_lt_upper_bound F 8 17592186044416 ltac:(lia) ltac:(lia)); lia).
assert (HFz : F + 256 <= 2147450880 \/ 17594333495296 <= F) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
assert (HsF2 : sF + 32 <= 17594333495296) by (subst sF; unfold SHADOW_OFF; pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (HWin : alloc_ceiling + 8496 <= sp0) by lia.
(* ---- run 1: 0x834d0 .. jal __asan_memcpy (0x83500) ---- *)
unfold cfg_at, CS_PC3, A_check_step.
replace (w64 (BASE + AF_check_step + 820)) with (Z_to_bv 64 (BASE + (AF_check_step + 820))) by (unfold w64; f_equal; lia).
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U25 : bv_unsigned (ew E 25) = sF) by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_check_step + 820) sr_atoms [YP09.mkRegion (Some 25%nat) 4 11 4 11 []] None (mkFacts [] [] []))
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + (AF_check_step + 820))) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|].
    split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres o ltac:(lia))).
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
  right; right; right. exists 2, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F. fold sF.
  change (fs_frame_bytes 2 / 8) with 32. lia. }
rename ms into msA, HJ into HJA, HFr into HFrA. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (20%bv : bv 5) R20A.
assert (HAG : env_agree 32 (Ereg regs1 []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (RK1 : s3_rk sp0 (as_gp B) (as_tp B) F blk (scene_seg k) (scene_len k) regs1).
{ unfold s3_rk. rewrite R3, R4, Hgp, Htp. repeat split; assumption. }
assert (RKA : s3_rk sp0 (as_gp B) (as_tp B) F blk (scene_seg k) (scene_len k) (ms_regs msA)).
{ eapply s3_rk_kept; [|exact RK1]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W1) msA) regs1 [] [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
assert (ZA : forall j, 4 <= j < 11 -> aview SEGS (w_H W1) (ms_mem msA) (sF + j) = Some (if j =? 10 then 2 else 0)).
{ intros j Hj. assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; cbn [Z.eqb Pos.eqb];
  (eapply s3_shb; [exact HRA | exact U25 | cbn; tauto | lia]). }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sF + 4 <= a < sF + 11) -> aview SEGS (w_H W1) (ms_mem msA) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hn. eapply s3_kept_run; [exact HFrA | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. rewrite U25 in Har. lia. }
clear HFrA HRA.
pmkst HS.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJA HROD) as HRODA.
pose proof RKA as (A2 & A3 & A4 & A8 & A18 & A19 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
assert (EspA : spZ (ms_regs msA) = sp0 + -128) by (unfold spZ; rewrite A2; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* ---- __asan_memcpy (F + 32, __const.check_step.frame, 16) ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W1 (ms_regs msA) (ms_mem msA) TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly1 S1 _ 0 (F + 32) A_CS_CFRAME 16 (-128) (Z_to_bv 64 (BASE + 3212)) HJA).
  - rewrite Ra0, (EE 22%nat 22%bv eq_refl). exact R22.
  - rewrite Ra1, HE, Eimg_img by (unfold A_TEXT, A_LIM; lia). reflexivity.
  - exact Ra2.
  - lia. - lia. - lia.
  - exact EspA.
  - reflexivity. - lia. - rewrite ESTK, Hes. lia.
  - exact A3. - exact A4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia]. right; right; right. exists 2, fpos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 2) with 256. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
  - replace (F + 32) with (F + 8 * 4) by lia. apply s3_ra_zero; [rewrite Z.add_mod, HF8 by lia; reflexivity | reflexivity |].
    intros i Hi. change (16 / 8) with 2 in Hi. rewrite s3_div8_add by exact HF8.
    replace (SHADOW_OFF + (F / 8 + 4) + i) with (sF + (4 + i)) by (unfold sF; lia). rewrite ZA by lia.
    destruct (Z.eqb_spec (4 + i) 10); [lia | reflexivity].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly1 S1 W1 (ms_mem msA) _ 2 fpos (F + 32) 16 (proj1 HJA) Hfin1); fold F;
    [lia | change (fs_frame_bytes 2) with 256; lia | lia].
  - split; [rewrite ECF; lia|]. split; [rewrite ECF; lia|]. split.
    { intros a Ha. split.
      - replace a with (A_CS_CFRAME + (a - A_CS_CFRAME)) by lia. rewrite (s3_cf_bytes W1 (ms_mem msA) HRODA) by lia. discriminate.
      - rewrite EspA, Hes. rewrite ECF in Ha. lia. }
    split; [rewrite ECF; unfold off_img in HFimg; lia|].
    split; [unfold amem_range; rewrite ECF; lia|].
    split; [exact (s3_cf_ra ly1 S1 W1 (ms_mem msA) _ (proj1 HJA))|].
    intros _. exact (s3_cf_hull ly1 S1 W1 (ms_mem msA) _ (proj1 HJA)). }
cbv beta. intros W2 c2 _ (-> & regsB & memB & mdB & -> & HJB & HPB & Ha0B & HeffB & HfrB & HpresB).
pose proof (s3_rk_pres _ _ _ _ _ _ _ _ _ HPB RKA) as RKB.
assert (R20B : getr regsB 20 = getr (ms_regs msA) 20) by exact (HPB 20 ltac:(unfold acallee_saved; lia)).
rewrite Hes in HfrB. replace (sp0 + -128 - 4096) with (sp0 - 4224) in HfrB by lia. replace (sp0 + -128) with (sp0 - 128) in HfrB by lia.
clear HS Ra0 Ra1 Ra2 Rra HE HEI EE U25 HAG E.
(* ---- run 2: 0x83504 .. jal __asan_memcpy (0x83510) ---- *)
remember (Eimg (Ereg regsB [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsB []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsB r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 3212 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W1) (mkst regsB (Z_to_bv 64 (BASE + 3212)) memB (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | unfold facts_ok; cbn; tauto]. }
paj_run_shc RUNP RUNC HS HJB.
{ intros a (r & Hin & _). destruct Hin. }
rename ms into msC, HJB into HJC, HFr into HFrC. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (20%bv : bv 5) R20C. rewrite (EE 20%nat 20%bv eq_refl), R20B, R20A in R20C.
assert (RKC : s3_rk sp0 (as_gp B) (as_tp B) F blk (scene_seg k) (scene_len k) (ms_regs msC)).
{ eapply s3_rk_kept; [|exact RKB]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W1) msC) regsB [] [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem msC) a = aview SEGS (w_H W1) memB a)
  by (intros a Ha; eapply s3_kept_run; [exact HFrC | exact Ha | intros (r & Hin & _); destruct Hin]).
clear HFrC.
pmkst HS.
pose proof RKC as (C2' & C3' & C4' & C8' & C18 & C19 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
pose proof RKB as (B2' & B3' & B4' & B8' & B18 & B19 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
assert (EspC : spZ (ms_regs msC) = sp0 + -128) by (unfold spZ; rewrite C2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (s3_obj_bounds ly S W mem md blk 34 HAR0 HFO) as (Hb4096 & Hbce).
pose proof (s3_obj_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ blk 34 HJC HFO) as HbF. fold F in HbF. change (fs_frame_bytes 2) with 256 in HbF.
assert (ZC : forall j, 4 <= j < 11 -> aview SEGS (w_H W1) (ms_mem msC) (sF + j) = Some (if j =? 10 then 2 else 0)).
{ intros j Hj. rewrite KC by lia. rewrite HfrB by lia. apply ZA. exact Hj. }
(* ---- __asan_memcpy (F + 48, blk, 34) ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) AMEMCPY W1 (ms_regs msC) (ms_mem msC) TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly1 S1 _ 0 (F + 48) blk 34 (-128) (Z_to_bv 64 (BASE + 3228)) HJC).
  - rewrite Ra0, (EE 22%nat 22%bv eq_refl), B22. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  - rewrite Ra1, (EE 19%nat 19%bv eq_refl). exact B19.
  - exact Ra2.
  - lia. - lia. - lia.
  - exact EspC.
  - reflexivity. - lia. - rewrite ESTK, Hes. lia.
  - exact C3'. - exact C4'.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [| rewrite Hes; lia]. right; right; right. exists 2, fpos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 2) with 256. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
  - replace (F + 48) with (F + 8 * 6) by lia. replace 34 with (8 * 4 + 2) by lia.
    apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. rewrite s3_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 6) + i) with (sF + (6 + i)) by (unfold sF; lia). rewrite ZC by lia.
      destruct (Z.eqb_spec (6 + i) 10); [lia | reflexivity].
    + rewrite s3_div8_add by exact HF8. replace (SHADOW_OFF + (F / 8 + 6) + 4) with (sF + 10) by (unfold sF; lia). rewrite ZC by lia. reflexivity.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly1 S1 W1 (ms_mem msC) _ 2 fpos (F + 48) 34 (proj1 HJC) Hfin1); fold F;
    [lia | change (fs_frame_bytes 2) with 256; lia | lia].
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite (s3_obj_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC HFO a Ha).
        replace a with (blk + (a - blk)) by lia. rewrite Hblkb by (unfold CS_BLK_LEN; lia). discriminate.
      - rewrite EspC, Hes. lia. }
    split; [lia|].
    split; [exact (s3_obj_amr ly S W mem md blk 34 HAR0 HFO ltac:(lia))|].
    split; [exact (s3_obj_ra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC HAR0 HFO)|].
    intros _. apply (s3_obj_hull _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC HFO). unfold CS_BLK_LEN. lia. }
cbv beta. intros W2 c2 _ (-> & regsD & memD & mdD & -> & HJD & HPD & Ha0D & HeffD & HfrD & HpresD).
pose proof (s3_rk_pres _ _ _ _ _ _ _ _ _ HPD RKC) as RKD.
assert (R20D : getr regsD 20 = getr (ms_regs msC) 20) by exact (HPD 20 ltac:(unfold acallee_saved; lia)).
rewrite Hes in HfrD. replace (sp0 + -128 - 4096) with (sp0 - 4224) in HfrD by lia. replace (sp0 + -128) with (sp0 - 128) in HfrD by lia.
assert (KEEPD : forall a, (sp0 - 104 <= a < sp0) \/ (F + 248 <= a < F + 256) -> aview SEGS (w_H W1) memD a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite HfrD by lia. rewrite KC by lia. rewrite HfrB by lia. rewrite KA by lia. reflexivity. }
assert (FBD : forall i, 0 <= i < 50 -> aview SEGS (w_H W1) memD (F + 32 + i) = Some (cp_v (s3_fr b k) (Z.to_nat i))).
{ intros i Hi. destruct (Z_lt_le_dec i 16) as [Hlo | Hhi].
  - rewrite HfrD by lia. rewrite KC by lia. rewrite HeffB by lia. rewrite (s3_cf_bytes W1 (ms_mem msA) HRODA) by lia.
    unfold cp_v. rewrite s3_fr_lo by lia. reflexivity.
  - replace (F + 32 + i) with (F + 48 + (i - 16)) by lia. rewrite HeffD by lia.
    rewrite (s3_obj_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJC HFO) by (unfold CS_BLK_LEN; lia).
    rewrite Hblkb by (unfold CS_BLK_LEN; lia). unfold cp_v.
    rewrite s3_fr_hi; [| rewrite Hlenb; reflexivity | unfold CS_LAST in Hk; lia | lia].
    replace (Z.to_nat i - 16)%nat with (Z.to_nat (i - 16)) by lia. reflexivity. }
assert (ZD : forall j, 4 <= j < 11 -> aview SEGS (w_H W1) memD (sF + j) = Some (if j =? 10 then 2 else 0)).
{ intros j Hj. rewrite HfrD by lia. apply ZC. exact Hj. }
clear HeffB HeffD HfrB HfrD KC KA ZA ZC.
clear HS Ra0 Ra1 Ra2 Rra HE HEI EE HAG E.
(* ---- run 3: 0x83514 .. jal reac_ctrl_parse (0x83538) ---- *)
remember (Eimg (Ereg regsD [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsD []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsD r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof RKD as (D2' & D3' & D4' & D8' & D18 & D19 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
assert (U25 : bv_unsigned (ew E 25) = sF) by (rewrite (EE 25%nat 25%bv eq_refl), D25; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS 3228 sr_atoms [YP09.mkRegion (Some 25%nat) 16 21 16 21 []] None (mkFacts [] [] []))
  (restrict (w_H W1) (mkst regsD (Z_to_bv 64 (BASE + 3228)) memD (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|].
    split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
    destruct (al_frames _ _ LAWS ly1 S1 W1 memD mdD 2 fpos (proj1 HJD) Hfin1) as (_ & _ & _ & HFSD).
    change (fs_frame_bytes 2 / 8) with 32 in HFSD. unfold shadow_addr in HFSD. fold F in HFSD. fold sF in HFSD.
    apply (proj1 (HFSD o ltac:(lia))).
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
paj_run_shc RUNP RUNC HS HJD.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
  right; right; right. exists 2, fpos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F. fold sF.
  change (fs_frame_bytes 2 / 8) with 32. lia. }
rename ms into msE, HJD into HJE, HFr into HFrE. clear HF HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (20%bv : bv 5) R20E. rewrite (EE 20%nat 20%bv eq_refl), R20D, R20C in R20E.
assert (RKE : s3_rk sp0 (as_gp B) (as_tp B) F blk (scene_seg k) (scene_len k) (ms_regs msE)).
{ eapply s3_rk_kept; [|exact RKD]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W1) msE) regsD [] [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRA. cbn [ms_mem restrict] in HRA.
assert (ZE2 : forall j, 16 <= j < 21 -> aview SEGS (w_H W1) (ms_mem msE) (sF + j) = Some (if j =? 20 then 4 else 0)).
{ intros j Hj. assert (Hj' : j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20) by lia.
  destruct Hj' as [-> | [-> | [-> | [-> | ->]]]]; cbn [Z.eqb Pos.eqb];
  (eapply s3_shb; [exact HRA | exact U25 | cbn; tauto | lia]). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sF + 16 <= a < sF + 21) -> aview SEGS (w_H W1) (ms_mem msE) a = aview SEGS (w_H W1) memD a).
{ intros a Ha Hn. eapply s3_kept_run; [exact HFrE | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Har. rewrite U25 in Har. lia. }
clear HFrE HRA.
pmkst HS.
pose proof RKE as (E2' & E3' & E4' & E8' & E18 & E19 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
assert (EspE : spZ (ms_regs msE) = sp0 - 128) by (unfold spZ; rewrite E2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Es0E : s0Z (ms_regs msE) = sp0) by (unfold s0Z; rewrite E8'; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJE HROD) as HRODE.
assert (HSAVE : cs_saved regs (aview SEGS (w_H W1) (ms_mem msE)) /\ rdword (aview SEGS (w_H W1) (ms_mem msE)) (F + 256 - 8) = Some (flag_addr ly1 2 fpos)).
{ apply (s3_keep regs F _ (aview SEGS (w_H W1) mem1)); [| | split; [exact HSAV | exact HFLAG]];
  intros a Ha; rewrite KE by lia; apply KEEPD; lia. }
assert (FBE : forall i, 0 <= i < 50 -> aview SEGS (w_H W1) (ms_mem msE) (F + 32 + i) = Some (cp_v (s3_fr b k) (Z.to_nat i))).
{ intros i Hi. rewrite KE by lia. apply FBD. exact Hi. }
assert (ZE1 : forall j, 4 <= j < 11 -> aview SEGS (w_H W1) (ms_mem msE) (sF + j) = Some (if j =? 10 then 2 else 0)).
{ intros j Hj. rewrite KE by lia. apply ZD. exact Hj. }
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & _).
assert (HCH : achain ly1 (aview SEGS (w_H W1) (ms_mem msE)) (sp0 - 128) sp0 ((sp0, raZ regs, s0Z regs) :: ch)).
{ apply (achain_ly_top ly ly1); [first [exact Etop1 | symmetry; exact Etop1] |].
  pose proof HJE as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
  apply (achain_push ly (aview SEGS (w_H W) mem) _ sp0 (s0Z regs) (raZ regs) ch (sp0 - 128) Hch).
  - lia.
  - intros a Ha. apply J9; lia.
  - replace (sp0 - 8) with (spZ regs - 8 - 8 * Z.of_nat 0) by (cbn; lia). exact (proj1 HSAVE 0%nat ltac:(lia)).
  - replace (sp0 - 16) with (spZ regs - 8 - 8 * Z.of_nat 1) by (cbn; lia). exact (proj1 HSAVE 1%nat ltac:(lia)).
  - exact Hra4.
  - lia. - pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). lia.
  - lia. - lia. }
(* ---- reac_ctrl_parse (F + 32, 50, F + 128) ---- *)
eapply SRr_bind.
{ rewrite pa_sigma_reac_ctrl_parse.
  eapply (PARSE TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly1 S1 W1 (ms_mem msE) _ 0 (ms_regs msE) ((sp0, raZ regs, s0Z regs) :: ch) (F + 32) 50 (F + 128) (s3_fr b k) HJE HRODE).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Rra. rewrite unsigned_lit_small by lia. lia.
  - exact E3'. - exact E4'.
  - rewrite Ra0, (EE 22%nat 22%bv eq_refl), D22. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2, (EE 23%nat 23%bv eq_refl), D23. reflexivity.
  - lia.
  - rewrite EspE, Es0E. exact HCH.
  - rewrite EspE. pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 128) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 128) 16 ltac:(lia)). lia.
  - rewrite EspE, ESTK, ESTK'. lia.
  - rewrite EspE. lia.
  - rewrite Hfrs1. cbn [length app]. lia.
  - apply (afobj_of_own SK SEGS B _ _ _ _ _ _ _ _ _ ly1 S1 W1 (ms_mem msE) _ 0 2 fpos (F + 32) 50 HJE); [left; reflexivity | lia | fold F; lia | fold F; change (fs_frame_bytes 2) with 256; lia | rewrite Z.add_mod, HF8 by lia; reflexivity |].
    replace (F + 32) with (F + 8 * 4) by lia. replace 50 with (8 * 6 + 2) by lia.
    apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. rewrite s3_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 4) + i) with (sF + (4 + i)) by (unfold sF; lia). rewrite ZE1 by lia.
      destruct (Z.eqb_spec (4 + i) 10); [lia | reflexivity].
    + rewrite s3_div8_add by exact HF8. replace (SHADOW_OFF + (F / 8 + 4) + 6) with (sF + 10) by (unfold sF; lia). rewrite ZE1 by lia. reflexivity.
  - apply (afobj_of_own SK SEGS B _ _ _ _ _ _ _ _ _ ly1 S1 W1 (ms_mem msE) _ 0 2 fpos (F + 128) 36 HJE); [left; reflexivity | lia | fold F; lia | fold F; change (fs_frame_bytes 2) with 256; lia | rewrite Z.add_mod, HF8 by lia; reflexivity |].
    replace (F + 128) with (F + 8 * 16) by lia. replace 36 with (8 * 4 + 4) by lia.
    apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
    + intros i Hi. rewrite s3_div8_add by exact HF8.
      replace (SHADOW_OFF + (F / 8 + 16) + i) with (sF + (16 + i)) by (unfold sF; lia). rewrite ZE2 by lia.
      destruct (Z.eqb_spec (16 + i) 20); [lia | reflexivity].
    + rewrite s3_div8_add by exact HF8. replace (SHADOW_OFF + (F / 8 + 16) + 4) with (sF + 20) by (unfold sF; lia). rewrite ZE2 by lia. reflexivity.
  - left. lia.
  - intros a Ha. right; right; right. exists 2, fpos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 2) with 256. lia.
  - apply s3_fr_length; [rewrite Hlenb; reflexivity | unfold CS_LAST in Hk; lia].
  - intros i Hi. rewrite FBE by lia. rewrite Nat2Z.id. reflexivity. }
cbv beta. intros W3 c3 _ (ly2 & S2 & regsF & memF & mdF & -> & HJF & HPF & Hfr2 & Hab2 & (ff & ES2) & Ha0F & HoF & HKF).
pose proof (s3_rk_pres _ _ _ _ _ _ _ _ _ HPF RKE) as RKF.
assert (R20F : getr regsF 20 = Z_to_bv 64 2) by (rewrite <- R20E; exact (HPF 20 ltac:(unfold acallee_saved; lia))).
rewrite Rra in *.
assert (Hlenb' : length b = 8904%nat) by (rewrite Hlenb; reflexivity).
assert (Hk' : 0 <= k <= 342) by (unfold CS_LAST in Hk; lia).
pose proof (s3_fr_parse b k Hlenb' Hk') as HP. cbv zeta in HP. destruct HP as (P1 & P22 & P23 & P24 & P25 & P26).
rewrite P1 in Ha0F.
assert (Hseg : 0 <= scene_seg k <= 2) by (unfold scene_seg; destruct (k =? 0); [lia|]; destruct (k =? 342); lia).
assert (Hslen : 14 <= scene_len k <= 26) by (unfold scene_len; destruct (k =? 0); [lia|]; destruct (k =? 342); lia).
assert (HoF' : forall i v, (i < 36)%nat -> nth i (snd (ctrlparse 50 (s3_fr b k))) cp_z = Z_to_bv 8 v -> 0 <= v < 256 ->
  aview SEGS (w_H W3) memF (F + 128 + Z.of_nat i) = Some v).
{ intros i v Hi Hn Hv. rewrite (HoF i Hi), Hn. rewrite bvu8 by lia. reflexivity. }
clear HS Ra0 Ra1 Ra2 HE HEI EE HAG E U25.
(* ---- run 4: 0x8353c .. jal reac_ctrl_checksum_verify (0x83568) ---- *)
remember (Eimg (Ereg regsF [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsF []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof RKF as (F2' & F3' & F4' & F8' & F18 & F19 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
assert (U23 : bv_unsigned (ew E 23) = F + 128) by (rewrite (EE 23%nat 23%bv eq_refl), F23; unfold w64; apply unsigned_lit_small; lia).
assert (V21 : ew E 21 = Z_to_bv 64 (scene_seg k)) by (rewrite (EE 21%nat 21%bv eq_refl), F21; reflexivity).
assert (V24 : ew E 24 = Z_to_bv 64 (scene_len k)) by (rewrite (EE 24%nat 24%bv eq_refl), F24; reflexivity).
assert (HS0 : st_ok_pi SEGS VAL E (mkSS 3268 sr_atoms
  [YP09.mkRegion (Some 23%nat) 0 36 0 0 [YP09.mkChunk 22 (CVal 1 (SLit 1)); YP09.mkChunk 23 (CVal 1 (SOff 21 0));
     YP09.mkChunk 24 (CVal 2 (SOff 24 0)); YP09.mkChunk 26 (CVal 1 (SLit 0))]] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regsF (Z_to_bv 64 (BASE + 3268)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor.
    + apply (chunk_ok_val SEGS E _ _ _ 1 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      apply s3_vm_of_aview. intros k0 Hk0. assert (k0 = 0%nat) as -> by lia. rewrite Z.add_0_r, s3_lb10 by lia.
      apply (HoF' 22%nat); [lia | exact P22 | lia].
    + apply (chunk_ok_val SEGS E _ _ _ 1 (SOff 21 0) (scene_seg k)); [cbn [sv_denot]; rewrite V21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply s3_vm_of_aview. intros k0 Hk0. assert (k0 = 0%nat) as -> by lia. rewrite Z.add_0_r, s3_lb10 by lia.
      apply (HoF' 23%nat); [lia | exact P23 | lia].
    + apply (chunk_ok_val SEGS E _ _ _ 2 (SOff 24 0) (scene_len k)); [cbn [sv_denot]; rewrite V24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply s3_vm_of_aview. intros k0 Hk0. assert (k0 = 0%nat \/ k0 = 1%nat) as [-> | ->] by lia.
      * rewrite Z.add_0_r, s3_lb20 by lia. apply (HoF' 24%nat); [lia | exact P24 | lia].
      * rewrite s3_lb21 by lia. replace (F + 128 + 24 + Z.of_nat 1) with (F + 128 + Z.of_nat 25) by (cbn; lia). apply (HoF' 25%nat); [lia | exact P25 | lia].
    + apply (chunk_ok_val SEGS E _ _ _ 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply s3_vm_of_aview. intros k0 Hk0. assert (k0 = 0%nat) as -> by lia. rewrite Z.add_0_r, s3_lb10 by lia.
      apply (HoF' 26%nat); [lia | exact P26 | lia].
  - cbn. tauto.
  - unfold facts_ok; cbn; tauto. }
assert (HS1 := st_ok_pi_pin_reg' E _ _ 10%bv 2 HS0 ltac:(cbn [restrict ms_regs mkst]; rewrite Ha0F; reflexivity) eq_refl).
assert (HS := st_ok_pi_pin_reg' E _ _ 20%bv 2 HS1 ltac:(cbn [restrict ms_regs mkst]; exact R20F) eq_refl).
clear HS0 HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
paj_run_shc RUNP RUNC HS HJF.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
rename ms into msG, HJF into HJG, HFr into HFrG. clear HF HG.
assert (KG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msG) a = aview SEGS (w_H W3) memF a).
{ intros a Ha. eapply s3_kept_run; [exact HFrG | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []]. cbn in Har. lia. }
clear HFrG.
assert (SD21 : sv_denot E (SOff 21 0) = Z_to_bv 64 (scene_seg k)) by (apply s3_soff; [exact V21 | lia]).
assert (SD24 : sv_denot E (SOff 24 0) = Z_to_bv 64 (scene_len k)) by (apply s3_soff; [exact V24 | lia]).
assert (SX21 : sv_denot E (SExt false 8 (SOff 21 0)) = Z_to_bv 64 (scene_seg k)) by (apply s3_zext_atom; [exact V21 | cbn; lia | cbn; lia]).
assert (SX24 : sv_denot E (SExt false 16 (SOff 24 0)) = Z_to_bv 64 (scene_len k)) by (apply s3_zext_atom; [exact V24 | cbn; lia | cbn; lia]).
psrr_branch_pi RUNP BR HS.
{ s3_kill Hc. }
clear Hc. paj_run_shc RUNP RUNC HS HJG.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. lia. }
rename ms into msH, HJG into HJH, HFr into HFrH. clear HF HG.
assert (KH : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msH) a = aview SEGS (w_H W3) (ms_mem msG) a).
{ intros a Ha. eapply s3_kept_run; [exact HFrH | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []]. cbn in Har. lia. }
clear HFrH.
psrr_branch_pi RUNP BR HS.
{ s3_kill Hc. }
clear Hc. paj_run_shc RUNP RUNC HS HJH.
{ intros a (r & Hin & Ha). destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val add_cond ss_mem] in Ha. lia. }
rename ms into msI, HJH into HJI, HFr into HFrI. clear HF HG.
assert (KI : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msI) a = aview SEGS (w_H W3) (ms_mem msH) a).
{ intros a Ha. eapply s3_kept_run; [exact HFrI | exact Ha |]. intros (r & Hin & Har). destruct Hin as [<- | []]. cbn in Har. lia. }
clear HFrI.
prreg HS (10%bv : bv 5) RaI0. prreg HS (1%bv : bv 5) RraI.
assert (RKI : s3_rk sp0 (as_gp B) (as_tp B) F blk (scene_seg k) (scene_len k) (ms_regs msI)).
{ eapply s3_rk_kept; [|exact RKF]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msI) regsF [] [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
pmkst HS.
pose proof RKI as (I2' & I3' & I4' & I8' & I18 & I19 & I21 & I22 & I23 & I24 & I25 & I26 & I27).
assert (EspI : spZ (ms_regs msI) = sp0 + -128) by (unfold spZ; rewrite I2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Es0I : s0Z (ms_regs msI) = sp0) by (unfold s0Z; rewrite I8'; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof HJI as (HARI & HlyI & _ & _ & _ & HfrsI & _ & _ & JI9 & _).
destruct (s3_fa _ _ _ 2 fpos HlyI) as (EFI & EFLI). destruct (s3_fa _ _ _ 2 fpos Hly1) as (EF1 & EFL1).
assert (EF2 : frame_addr ly2 2 fpos = F) by (unfold F; rewrite EFI, EF1; reflexivity).
assert (EFL2 : flag_addr ly2 2 fpos = flag_addr ly1 2 fpos) by (rewrite EFLI, EFL1; reflexivity).
pose proof HKF as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6). rewrite EspE, ESTK' in HK1.
assert (KEEPI : forall a, (sp0 - 104 <= a < sp0) \/ (F + 248 <= a < F + 256) -> aview SEGS (w_H W3) (ms_mem msI) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite KI, KH, KG by lia. destruct Ha as [Ha | Ha].
  - rewrite HK1 by lia. rewrite KE by lia. apply KEEPD; lia.
  - rewrite (HK4 2 fpos a Hfin1); [rewrite KE by lia; apply KEEPD; lia | left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 2) with 256; lia | cbv beta; lia]. }
assert (FBI : forall i, 0 <= i < 50 -> aview SEGS (w_H W3) (ms_mem msI) (F + 32 + i) = Some (cp_v (s3_fr b k) (Z.to_nat i))).
{ intros i Hi. rewrite KI, KH, KG by lia.
  rewrite (HK4 2 fpos (F + 32 + i) Hfin1); [apply FBE; lia | left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 2) with 256; lia | cbv beta; lia]. }
assert (ZI1 : forall j, 4 <= j < 11 -> aview SEGS (w_H W3) (ms_mem msI) (sF + j) = Some (if j =? 10 then 2 else 0)).
{ intros j Hj. rewrite KI, KH, KG by lia.
  rewrite (HK4 2 fpos (sF + j) Hfin1); [apply ZE1; lia | right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; fold sF; change (fs_frame_bytes 2 / 8) with 32; lia | cbv beta; lia]. }
pose proof HlyI as (_ & _ & _ & _ & _ & _ & _ & _ & EtopI & _).
assert (HCHI : achain ly2 (aview SEGS (w_H W3) (ms_mem msI)) (sp0 + -128) sp0 ((sp0, raZ regs, s0Z regs) :: ch)).
{ apply (achain_ly_top ly ly2); [first [exact EtopI | symmetry; exact EtopI] |].
  apply (achain_push ly (aview SEGS (w_H W) mem) _ sp0 (s0Z regs) (raZ regs) ch (sp0 + -128) Hch).
  - lia.
  - intros a Ha. apply JI9; lia.
  - rewrite (rdword_ext (aview SEGS (w_H W1) mem1)); [| intros q Hq; apply KEEPI; lia].
    replace (sp0 - 8) with (spZ regs - 8 - 8 * Z.of_nat 0) by (cbn; lia). exact (HSAV 0%nat ltac:(lia)).
  - rewrite (rdword_ext (aview SEGS (w_H W1) mem1)); [| intros q Hq; apply KEEPI; lia].
    replace (sp0 - 16) with (spZ regs - 8 - 8 * Z.of_nat 1) by (cbn; lia). exact (HSAV 1%nat ltac:(lia)).
  - exact Hra4.
  - lia. - pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). lia.
  - lia. - lia. }
destruct (s3_bs_ok b k Hlenb' Hk') as (HbsL & HbsR & HbsS).
(* ---- reac_ctrl_checksum_verify (F + 32) ---- *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs msI) (ms_mem msI) _ TCHECK_STEP_STK sp0 [] ly S W mem md [(2, fpos)] ly2 S2 _ 0 TCKV_STK [] 0 (-128) (Z_to_bv 64 (BASE + 3316)) ((sp0, raZ regs, s0Z regs) :: ch)
     (fun ly' S' W' regs' mem' md' => ly' = ly2 /\ S' = S2 /\ W' = W3 /\ getr regs' 10 = w64 0) HJI).
  - exact EspI. - reflexivity. - lia. - unfold TCKV_STK; lia. - rewrite ESTK; unfold TCKV_STK; lia.
  - exact I3'. - exact I4'. - exact RraI. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Es0I. exact HCHI.
  - intros HPRE2. rewrite pa_sigma_reac_ctrl_checksum_verify. eapply SRr_mono.
    + apply (CKV ly2 S2 W3 (ms_regs msI) (ms_mem msI) _ _ (F + 32) (s3_bs b k) HPRE2).
      * rewrite RaI0, (EE 22%nat 22%bv eq_refl), F22. reflexivity.
      * apply (afobj_of_own SK SEGS B _ _ _ _ _ _ _ _ _ ly2 S2 W3 (ms_mem msI) _ 0 2 fpos (F + 32) 50 HJI); rewrite ?EF2;
          [left; reflexivity | lia | lia | change (fs_frame_bytes 2) with 256; lia | rewrite Z.add_mod, HF8 by lia; reflexivity |].
        replace (F + 32) with (F + 8 * 4) by lia. replace 50 with (8 * 6 + 2) by lia.
        apply s3_ra_part; [rewrite Z.add_mod, HF8 by lia; reflexivity | lia | lia | |].
        -- intros i Hi. rewrite s3_div8_add by exact HF8.
           replace (SHADOW_OFF + (F / 8 + 4) + i) with (sF + (4 + i)) by (unfold sF; lia). rewrite ZI1 by lia.
           destruct (Z.eqb_spec (4 + i) 10); [lia | reflexivity].
        -- rewrite s3_div8_add by exact HF8. replace (SHADOW_OFF + (F / 8 + 4) + 6) with (sF + 10) by (unfold sF; lia). rewrite ZI1 by lia. reflexivity.
      * intros j Hj. rewrite HbsL in Hj.
        assert (Ej : nth j (s3_bs b k) 0 = cp_v (s3_fr b k) (18 + j)) by (unfold s3_bs; rewrite nth_map_seq by lia; reflexivity). rewrite Ej.
        replace (F + 32 + 18 + Z.of_nat j) with (F + 32 + Z.of_nat (18 + j)) by lia.
        apply val_mem1_of_aview. rewrite FBI by lia. rewrite Nat2Z.id. reflexivity.
      * exact HbsL.
    + intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & (-> & -> & -> & Ha0')).
      exists ly2, S2, regs', mem', md'. split; [rewrite RraI; reflexivity|]. split; [exact HJ'|]. split; [exact HP'|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. rewrite Ha0', HbsS. reflexivity.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regsJ & memJ & mdJ & -> & HJJ & HJJ' & HPJ & (-> & -> & -> & Ha0J)).
replace (0 + 0) with 0 in HJJ by reflexivity.
pose proof (s3_rk_pres _ _ _ _ _ _ _ _ _ HPJ RKI) as RKJ.
pose proof HJJ' as (_ & _ & _ & _ & _ & _ & _ & _ & JJ9 & _ & _ & JJ4 & _).
rewrite Hfr2 in JJ4.
assert (KEEPJ : forall a, (sp0 - 104 <= a < sp0) \/ (F + 248 <= a < F + 256) -> aview SEGS (w_H W3) memJ a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. destruct Ha as [Ha | Ha].
  - rewrite JJ9 by (unfold TCKV_STK; lia). apply KEEPI. lia.
  - rewrite (JJ4 2 fpos a Hfin1); [apply KEEPI; lia | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF2; change (fs_frame_bytes 2) with 256; lia | intros (r & Hr & _); destruct Hr]. }
clear HS RaI0 RraI HE HEI EE HAG E SD21 SD24 SX21 SX24 V21 V24 U23.
(* ---- run 5: 0x8356c (bnez a0) .. 0x83570 ---- *)
remember (Eimg (Ereg regsJ [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regsJ []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HS0 : st_ok_pi SEGS VAL E (mkSS 3316 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regsJ (Z_to_bv 64 (BASE + 3316)) memJ (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | unfold facts_ok; cbn; tauto]. }
assert (HS := st_ok_pi_pin_reg' E _ _ 10%bv 0 HS0 ltac:(cbn [restrict ms_regs mkst]; rewrite Ha0J; reflexivity) eq_refl).
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
paj_run_to_sh RUNTOP HS HJJ 3320.
{ intros a (r & Hin & _). destruct Hin. }
rename ms into msK, HJJ into HJK. clear HF HG.
assert (KK : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msK) a = aview SEGS (w_H W3) memJ a)
  by (intros a Ha; eapply s3_kept_run; [exact HFr | exact Ha | intros (r & Hin & _); destruct Hin]).
assert (RKK : s3_rk sp0 (as_gp B) (as_tp B) F blk (scene_seg k) (scene_len k) (ms_regs msK)).
{ eapply s3_rk_kept; [|exact RKJ]. intros x Hx.
  exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msK) regsJ [] [2; 3; 4; 8; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv HS HAG eq_refl x Hx). }
pmkst HS.
pose proof RKK as (K2' & K3' & K4' & K8' & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
assert (KEEPK : forall a, (sp0 - 104 <= a < sp0) \/ (F + 248 <= a < F + 256) -> aview SEGS (w_H W3) (ms_mem msK) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite KK by lia. apply KEEPJ. exact Ha. }
apply SRr_ret. eexists ly2, S2, (ms_regs msK), (ms_mem msK), _. split.
{ unfold cfg_at, CS_PC4, A_check_step, w64. do 3 f_equal. unfold AF_check_step. lia. }
split; [exact HPRE|].
unfold cs_frame. change CS_CID with 2. change CHECK_STEP_FRAME with 128. rewrite EF2, EFL2.
split; [exact HJK|].
split; [rewrite Hab2; exact HAB|].
split.
{ change (fs_frame_bytes 2) with 256. rewrite (rdword_ext (aview SEGS (w_H W1) mem1)); [exact HFLAG | intros q Hq; apply KEEPK; lia]. }
split.
{ intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W1) mem1)); [exact (HSAV j Hj) | intros q Hq; apply KEEPK; lia]. }
split; [exact K2'|]. split; [rewrite K3', Hgp; reflexivity|]. split; [rewrite K4', Htp; reflexivity|].
split; [exact K8'|]. split; [exact K18|]. split; [exact K25|]. split; [exact K26 | exact K27].
Qed.
End h.
End f.
End d.
Print Assumptions cs_S3.
