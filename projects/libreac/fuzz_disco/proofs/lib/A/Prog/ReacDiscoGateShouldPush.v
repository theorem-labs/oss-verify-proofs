(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:388-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFfi.v:262-264 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_ingest.v, with its module paths, module names and numbers changed; 4001 of its 4244 lines of code are new or changed and 2822 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YK06 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed disco_classify_c GateModel slot_lib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YK00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Definition REAC_DISCO_GATE_SHOULD_PUSH_STK : Z := 96 + 2 * ESTACK.
Definition treac_disco_gate_should_push_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp g : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < sp) -> ~ (g <= a < g + 264) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (g <= b + i < g + 264) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (g <= a < g + 264) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition treac_disco_gate_should_push_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ getr regs2 1 = getr regs 1 /\
    getr regs2 10 = w64 (snd (GateModel.gate_model G Sg now)) /\
    frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    treac_disco_gate_should_push_kept lyc Sc W memc W2 mem2 (spZ regs) g /\
    garr8 SEGS (mrestrict (w_H W2) mem2) g (map (fun b : byte => bv_unsigned b) (fst (GateModel.gate_model G Sg now))) /\
    disco_classify_c.gate_ok (fst (GateModel.gate_model G Sg now)) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) s (map (fun b : byte => bv_unsigned b) Sg).
Definition treac_disco_gate_should_push_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (g s now : Z) (G Sg : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 g -> getr regs 11 = w64 s -> getr regs 12 = w64 now -> 0 <= now < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK -> spZ regs <= sp0 ->
  0 < g -> g mod 8 = 0 -> g + 264 <= 2 ^ 63 ->
  (spZ regs <= g \/ g + 264 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) ->
  (forall a, g <= a < g + 264 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  amem_range g 264 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 264 -> shadow_hull_vis (aview SEGS (w_H W) memc) g 264 ->
  length G = 264%nat -> garr8 SEGS (mrestrict (w_H W) memc) g (map (fun b : byte => bv_unsigned b) G) ->
  disco_classify_c.gate_ok G ->
  0 < s -> s mod 4 = 0 -> s + 24 <= 2 ^ 63 ->
  (spZ regs <= s \/ s + 24 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) ->
  ((exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= s /\
      s + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 24 <= b + req_size m)) ->
  amem_range s 24 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 -> shadow_hull_vis (aview SEGS (w_H W) memc) s 24 ->
  length Sg = 24%nat -> garr8 SEGS (mrestrict (w_H W) memc) s (map (fun b : byte => bv_unsigned b) Sg) ->
  (g + 264 <= s \/ s + 24 <= g) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_disco_gate_should_push) regs memc mdc)
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).
Lemma gsp_shiftr_le_val : forall (bs : list Z) (j : nat),
  Forall (fun b : Z => 0 <= b < 256) bs -> (j < length bs)%nat ->
  Z.shiftr (Bytes.le_val bs) (8 * Z.of_nat j) mod 256 = nth j bs 0.
Proof.
  induction bs as [|b bs IH]; intros j HF Hj; cbn [length] in Hj; [lia|].
  inversion HF as [|b' bs' Hb HFs Heq]; subst.
  pose proof (Bytes.le_val_range bs HFs) as Hr.
  assert (Hpow : 0 < 256 ^ Z.of_nat (length bs)) by (apply Z.pow_pos_nonneg; lia).
  destruct j as [|j].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. cbn [Bytes.le_val].
    replace (b + 256 * Bytes.le_val bs) with (b + Bytes.le_val bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - cbn [nth]. cbn [Bytes.le_val]. rewrite !Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by (first [lia | apply Z.pow_pos_nonneg; lia]).
    replace (b + 256 * Bytes.le_val bs) with (Bytes.le_val bs * 256 + b) by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small b 256) by lia. rewrite Z.add_0_r.
    rewrite <- Z.shiftr_div_pow2 by lia. apply IH; [exact HFs | cbn [length] in Hj; lia].
Qed.
Lemma gsp_nth_fld : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (j < n)%nat ->
  nth j (CtrlParsed.fld L k n) (CtrlParsed.zb 0) = nth (k + j) L (CtrlParsed.zb 0).
Proof.
  intros L k n j Hk Hj.
  assert (Hne : nth_error (CtrlParsed.fld L k n) j = nth_error L (k + j))
    by (rewrite GateModel.nth_error_fld; destruct (Nat.ltb_spec j n); [reflexivity | lia]).
  destruct (nth_error L (k + j)) as [x|] eqn:Hx.
  - rewrite (nth_error_nth _ _ _ Hne), (nth_error_nth _ _ _ Hx). reflexivity.
  - exfalso. apply nth_error_None in Hx. lia.
Qed.
Lemma gsp_nth_map : forall (L : list byte) (j : nat),
  nth j (map bv_unsigned L) 0 = bv_unsigned (nth j L (CtrlParsed.zb 0)).
Proof.
  intros L j. exact (map_nth bv_unsigned L (CtrlParsed.zb 0) j).
Qed.
Lemma gsp_le_byte_fu : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (j < n)%nat ->
  YO0f.le_byte (CtrlParsed.fu L k n) n j = bv_unsigned (nth (k + j) L (CtrlParsed.zb 0)).
Proof.
  intros L k n j Hk Hj.
  assert (HL : length (map bv_unsigned (CtrlParsed.fld L k n)) = n)
    by (rewrite length_map; apply GateModel.length_fld; lia).
  pose proof (Bytes.bytes_ok_map (CtrlParsed.fld L k n)) as HF. unfold Bytes.bytes_ok in HF.
  pose proof (Bytes.le_val_range _ HF) as Hr. rewrite HL in Hr.
  unfold CtrlParsed.fu. rewrite Bytes.bytes_le_to_Z_le_val. unfold YO0f.le_byte.
  assert (Hp : 2 ^ (8 * Z.of_nat n) = 256 ^ Z.of_nat n)
    by (rewrite (Z.pow_mul_r 2 8 (Z.of_nat n)) by lia; reflexivity).
  rewrite Hp, (Z.mod_small _ _ Hr).
  rewrite (gsp_shiftr_le_val _ j HF ltac:(rewrite HL; lia)).
  rewrite gsp_nth_map. f_equal. apply gsp_nth_fld; lia.
Qed.
Lemma gsp_val_mem : forall (m : word -> option byte) (p : Z) (L : list byte) (k n : nat),
  garr8 SEGS m p (map bv_unsigned L) -> (k + n <= length L)%nat ->
  val_mem SEGS m (p + Z.of_nat k) n (CtrlParsed.fu L k n).
Proof.
  intros m p L k n HG Hk j Hj.
  replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia.
  rewrite (garr8_mbyte SEGS m p (map bv_unsigned L) (k + j)%nat HG ltac:(rewrite length_map; lia)).
  f_equal. f_equal. rewrite gsp_nth_map. symmetry. apply gsp_le_byte_fu; lia.
Qed.
Lemma gsp_aview_byte : forall (W : world SEGS) (mem : word -> option byte) (p : Z) (L : list byte) (j : nat),
  garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned L) -> (j < length L)%nat ->
  aview SEGS (w_H W) mem (p + Z.of_nat j) = Some (bv_unsigned (nth j L (CtrlParsed.zb 0))).
Proof.
  intros W mem p L j HG Hj. unfold aview.
  rewrite (garr8_mbyte SEGS (mrestrict (w_H W) mem) p (map bv_unsigned L) j HG ltac:(rewrite length_map; lia)).
  cbn [option_map]. rewrite gsp_nth_map, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma gsp_cmp_iff : forall (W : world SEGS) (mem : word -> option byte) (L M : list byte) (p q : Z) (k1 k2 n : nat),
  garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned L) ->
  garr8 SEGS (mrestrict (w_H W) mem) q (map bv_unsigned M) ->
  (k1 + n <= length L)%nat -> (k2 + n <= length M)%nat ->
  ((forall i, 0 <= i < Z.of_nat n ->
      aview SEGS (w_H W) mem (p + Z.of_nat k1 + i) = aview SEGS (w_H W) mem (q + Z.of_nat k2 + i)) <->
   CtrlParsed.bytes_eqb (CtrlParsed.fld L k1 n) (CtrlParsed.fld M k2 n) = true).
Proof.
  intros W mem L M p q k1 k2 n HL HM Hk1 Hk2.
  assert (Haux : forall j : nat, (j < n)%nat ->
    (aview SEGS (w_H W) mem (p + Z.of_nat k1 + Z.of_nat j) = aview SEGS (w_H W) mem (q + Z.of_nat k2 + Z.of_nat j)
     <-> bv_unsigned (nth (k1 + j) L (CtrlParsed.zb 0)) = bv_unsigned (nth (k2 + j) M (CtrlParsed.zb 0)))).
  { intros j Hj.
    replace (p + Z.of_nat k1 + Z.of_nat j) with (p + Z.of_nat (k1 + j)) by lia.
    replace (q + Z.of_nat k2 + Z.of_nat j) with (q + Z.of_nat (k2 + j)) by lia.
    rewrite (gsp_aview_byte W mem p L (k1 + j)%nat HL ltac:(lia)).
    rewrite (gsp_aview_byte W mem q M (k2 + j)%nat HM ltac:(lia)).
    split; [intros HH; injection HH as HH; exact HH | intros HH; rewrite HH; reflexivity]. }
  rewrite GateModel.beq_iff. split.
  - intros HA. apply (nth_ext _ _ 0 0).
    + rewrite !length_map, !GateModel.length_fld by lia. reflexivity.
    + intros j Hj. rewrite length_map, (GateModel.length_fld L k1 n) in Hj by lia.
      rewrite !gsp_nth_map, !(gsp_nth_fld L k1 n j), !(gsp_nth_fld M k2 n j) by lia.
      apply (Haux j Hj). apply HA. lia.
  - intros HE i Hi.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    apply (Haux (Z.to_nat i) ltac:(lia)).
    pose proof (f_equal (fun l => nth (Z.to_nat i) l 0) HE) as Hn. cbn beta in Hn.
    rewrite !gsp_nth_map, (gsp_nth_fld L k1 n (Z.to_nat i)), (gsp_nth_fld M k2 n (Z.to_nat i)) in Hn by lia.
    exact Hn.
Qed.
Lemma gsp_img_gap : forall p n, 0 < n -> n <= 1024 ->
  (forall a, p <= a < p + n -> a + 1 <= IMG_LO \/ IMG_TOP <= a) -> p + n <= IMG_LO \/ IMG_TOP <= p.
Proof.
  intros p n Hn Hle H. unfold IMG_LO, IMG_TOP in *.
  destruct (H p ltac:(lia)) as [H1 | H1]; [|right; lia].
  destruct (H (p + n - 1) ltac:(lia)) as [H2 | H2]; [left; lia|]. exfalso. lia.
Qed.
Lemma gsp_wr_fact : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  4096 <= a < 2 ^ 64 /\ (a + 1 <= IMG_LO \/ IMG_TOP <= a).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Hw.
  pose proof (proj1 HJ) as HAR.
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj2 (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Hw)) as Hc.
  unfold IMG_LO, IMG_TOP in *. unfold ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *.
  destruct Hc as [Hs | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hown & [(Happ & Hr) | (Hsh & _)])]].
  - split; [lia | right; lia].
  - pose proof (app_addr_below_ceil a Happ) as Hab. unfold ASAN_CEIL in Hab.
    pose proof (blk_off_imgP B lyc Sc W memc mdc b n HAR Hin) as Hoi.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoi.
    unfold app_addr in Happ. split; lia.
  - pose proof (app_addr_below_ceil a Happ) as Hab. unfold ASAN_CEIL in Hab.
    assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hoi.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoi.
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold app_addr in Happ. split; lia.
  - split; lia.
Qed.
Lemma gsp_range_facts : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k p n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> 0 < n -> n <= 1024 ->
  (forall a, p <= a < p + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  4096 <= p /\ p + n <= 2 ^ 64 /\ (p + n <= IMG_LO \/ IMG_TOP <= p).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p n HJ Hn Hle Hwr.
  assert (Hlo : 4096 <= p) by (exact (proj1 (proj1 (gsp_wr_fact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p HJ (Hwr p ltac:(lia)))))).
  assert (Hhi : p + n <= 2 ^ 64)
    by (pose proof (proj2 (proj1 (gsp_wr_fact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + n - 1) HJ (Hwr (p + n - 1) ltac:(lia))))); lia).
  split; [exact Hlo|]. split; [exact Hhi|].
  apply gsp_img_gap; [lia | lia|].
  intros a Ha. exact (proj2 (gsp_wr_fact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a Ha))).
Qed.
Definition GSP_SBx : sv := SOff 32 0.
Definition GSP_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gsp_regions : smem := [ stack_region 96; got_regionP; bcell_regionP 32 ].
Definition gsp_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 (2 ^ 47 - 264) 3);
            (11%nat, mkAF 0 (2 ^ 47 - 24) 2); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_gsp : sstate := mkSS AF_reac_disco_gate_should_push sr_atoms gsp_regions None gsp_facts.
Definition gsp_SH : list shent := [ mkSHE 10 0 264; mkSHE 11 0 24 ].
Definition gsp_extra (Sg G : list byte) : list word :=
  map (Z_to_bv 64) [SB; CtrlParsed.fu Sg 8 4; CtrlParsed.fb Sg 12; CtrlParsed.fb Sg 13;
                    CtrlParsed.fb Sg 14; CtrlParsed.fb Sg 16; CtrlParsed.fu G 256 4].
Definition EGSP (regs : bvmap 5 word) (Sg G : list byte) : env := Eimg (Ereg regs (gsp_extra Sg G)).
Lemma regs_ok_EGSP : forall regs Sg G, regs_ok (EGSP regs Sg G) sr_atoms regs.
Proof.
  intros. unfold EGSP. apply (regs_ok_agree 32 (Ereg regs (gsp_extra Sg G))).
  - split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply regs_ok_Ereg.
Qed.
Lemma gsp_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s : Z) (G Sg : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 g -> getr regs 11 = w64 s ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK -> spZ regs <= sp0 ->
  0 < g -> g mod 8 = 0 -> amem_range g 264 -> range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 264 ->
  0 < s -> s mod 4 = 0 -> amem_range s 24 -> range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 ->
  st_ok_pi SEGS VAL (EGSP regs Sg G) ss_gsp
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_disco_gate_should_push)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS GSP_SBx gsp_SH (EGSP regs Sg G) (mrestrict (w_H W) memc).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s G Sg
    HJ H10 H11 Hal16 Hbud Hsp Hg0 Hg8 Hgapp Hgra Hs0 Hs4 Hsapp Hsra.
  pose proof (proj1 HJ) as HAR.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pa_obj_img 1%nat ltac:(unfold disco_nobj; lia)) as Hob1.
  pose proof (pa_obj_img 66%nat ltac:(unfold disco_nobj; lia)) as Hob66.
  pose proof (pal_got_cell B TL) as Hgc.
  pose proof (pa_val_range (A_OBJ 1)) as VR1. pose proof (pa_val_range (A_OBJ 66)) as VR66.
  unfold amem_range in Hgapp, Hsapp.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
  rewrite restrict_mkst_fx.
  set (E := EGSP regs Sg G).
  assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (gsp_extra Sg G)) m)
    by (intros m Hm; subst E; unfold EGSP; apply Eimg_low; exact Hm).
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 g)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 s)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (subst E; unfold EGSP; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66)))
    by (subst E; unfold EGSP; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
  { intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_gsp, gsp_regions. apply pa_entry_st_ok_full.
    + apply regs_ok_EGSP.
    + vm_compute. reflexivity.
    + unfold stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
        [cbn [sv_denot]; rewrite EO66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
      * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 GSP_SBx SB);
        [cbn [sv_denot GSP_SBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; lia | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1), (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; exact I]. cbn [gsp_facts f_atoms atoms_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia | reflexivity].
  - assert (HUB : U E GSP_SBx = SHADOW_OFF)
      by (unfold GSP_SBx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
    assert (HU10 : U E (SOff 10 0) = g) by (shent_U_norm; reflexivity).
    assert (HU11 : U E (SOff 11 0) = s) by (shent_U_norm; reflexivity).
    unfold gsp_SH, sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU10, HUB. split.
      * replace (g + 0) with g by lia. replace (264 - 0) with 264 by lia. exact Hgra.
      * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU11, HUB. split.
      * replace (s + 0) with s by lia. replace (24 - 0) with 24 by lia. exact Hsra.
      * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
Lemma gsp_entry_wrange : forall (regs : bvmap 5 word) (Sg G : list byte) (a : Z),
  ~ (spZ regs - 96 <= a < spZ regs) -> ~ in_wrange (EGSP regs Sg G) gsp_regions a.
Proof.
  intros regs Sg G a Hn (r & Hin & Hr).
  assert (E2 : ew (EGSP regs Sg G) 2 = getr regs 2)
    by (unfold EGSP; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  unfold gsp_regions in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
    unfold stack_region, got_regionP, bcell_regionP in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - rewrite E2 in Hr. unfold spZ in Hn. lia.
  - lia.
  - lia.
Qed.
Lemma gsp_entry_mbyte : forall (regs : bvmap 5 word) (Sg G : list byte) (W : world SEGS) (m m' : word -> option byte),
  frame_of (EGSP regs Sg G) gsp_regions (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
  intros regs Sg G W m m' HF a Ha Hn. unfold mbyte.
  rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; apply gsp_entry_wrange; exact Hn)).
  reflexivity.
Qed.
Lemma gsp_garr8_move : forall (W : world SEGS) (m m' : word -> option byte) (p : Z) (l : list Z) (lo hi : Z),
  garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a) ->
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 -> (p + Z.of_nat (length l) <= lo \/ hi <= p) ->
  garr8 SEGS (mrestrict (w_H W) m') p l.
Proof.
  intros W m m' p l lo hi HG HM Hp0 Hp64 Hd.
  apply (garr8_frame SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) m') p l HG).
  intros a Ha. apply HM; lia.
Qed.
Lemma gsp_ra_move : forall (W : world SEGS) (m m' : word -> option byte) (p n lo hi : Z),
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a) ->
  0 <= p -> p + n + 8 <= kHighMemEnd -> kHighMemBeg <= lo ->
  range_addressable (aview SEGS (w_H W) m') SHADOW_OFF p n.
Proof.
  intros W m m' p n lo hi HR HM Hp0 Hpn Hlo x Hx.
  destruct (HR x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hsv. unfold aview. f_equal.
  assert (Hd1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd2 : x / 8 < 17592186044416)
    by (apply Z.div_lt_upper_bound; [lia | unfold kHighMemEnd in *; lia]).
  assert (Heq : shadow_of_addr SHADOW_OFF x = SHADOW_OFF + x / 8) by reflexivity.
  rewrite Heq. unfold SHADOW_OFF, kHighMemBeg in *.
  apply HM; lia.
Qed.
Lemma gsp_fu1 : forall (L : list byte) (k : nat), (k < length L)%nat -> CtrlParsed.fu L k 1 = CtrlParsed.fb L k.
Proof.
  intros L k Hk. unfold CtrlParsed.fu. rewrite (GateModel.fld1 L k Hk).
  rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val]. unfold CtrlParsed.fb. lia.
Qed.
Definition gsp_sreg (n : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 24 0 0
    [YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 12 (CVal 1 (SOff 34 0));
     YP09.mkChunk 13 (CVal 1 (SOff 35 0)); YP09.mkChunk 14 (CVal 1 (SOff 36 0));
     YP09.mkChunk 16 (CVal 1 (SOff 37 0))].
Definition gsp_greg (n : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 264 0 264 [YP09.mkChunk 256 (CVal 4 (SOff 38 0))].
Lemma gsp_ew_extra : forall (regs : bvmap 5 word) (Sg G : list byte),
  ew (EGSP regs Sg G) 32 = Z_to_bv 64 SB /\
  ew (EGSP regs Sg G) 33 = Z_to_bv 64 (CtrlParsed.fu Sg 8 4) /\
  ew (EGSP regs Sg G) 34 = Z_to_bv 64 (CtrlParsed.fb Sg 12) /\
  ew (EGSP regs Sg G) 35 = Z_to_bv 64 (CtrlParsed.fb Sg 13) /\
  ew (EGSP regs Sg G) 36 = Z_to_bv 64 (CtrlParsed.fb Sg 14) /\
  ew (EGSP regs Sg G) 37 = Z_to_bv 64 (CtrlParsed.fb Sg 16) /\
  ew (EGSP regs Sg G) 38 = Z_to_bv 64 (CtrlParsed.fu G 256 4).
Proof.
  intros regs Sg G.
  repeat split; unfold EGSP; rewrite Eimg_low by (unfold A_TEXT; lia); try reflexivity.
Qed.
Lemma gsp_ew_reg : forall (regs : bvmap 5 word) (Sg G : list byte) (r : bv 5) (n : nat) (v : Z),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> getr regs r = w64 v ->
  ew (EGSP regs Sg G) n = Z_to_bv 64 v.
Proof.
  intros regs Sg G r n v Hn Hlt Hv. unfold EGSP. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ n r Hn). exact Hv.
Qed.
Lemma gsp_sreg_ok : forall (n : nat) (regs : bvmap 5 word) (Sg G : list byte) (W : world SEGS)
  (m : word -> option byte) (s : Z),
  ew (EGSP regs Sg G) n = Z_to_bv 64 s -> 0 <= s -> s + 24 <= 2 ^ 64 -> length Sg = 24%nat ->
  garr8 SEGS (mrestrict (w_H W) m) s (map bv_unsigned Sg) ->
  region_ok SEGS (EGSP regs Sg G) (mrestrict (w_H W) m) (gsp_sreg n).
Proof.
  intros n regs Sg G W m s E11 Hs0 Hs64 HSl HSa.
  destruct (gsp_ew_extra regs Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8.
  pose proof (GateModel.fb_rng Sg 12) as R12. pose proof (GateModel.fb_rng Sg 13) as R13.
  pose proof (GateModel.fb_rng Sg 14) as R14. pose proof (GateModel.fb_rng Sg 16) as R16.
  assert (VBs : base_val (EGSP regs Sg G) (Some n) = s)
    by (cbn [base_val]; rewrite E11; apply unsigned_lit_small; lia).
  unfold gsp_sreg, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VBs. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ s 8 4 _ (CtrlParsed.fu Sg 8 4));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact (gsp_val_mem _ s Sg 8 4 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 12 1 _ (CtrlParsed.fb Sg 12));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 12 ltac:(lia)). exact (gsp_val_mem _ s Sg 12 1 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 13 1 _ (CtrlParsed.fb Sg 13));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 13 ltac:(lia)). exact (gsp_val_mem _ s Sg 13 1 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 14 1 _ (CtrlParsed.fb Sg 14));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 14 ltac:(lia)). exact (gsp_val_mem _ s Sg 14 1 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 16 1 _ (CtrlParsed.fb Sg 16));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 16 ltac:(lia)). exact (gsp_val_mem _ s Sg 16 1 HSa ltac:(lia)).
Qed.
Lemma gsp_greg_ok : forall (n : nat) (regs : bvmap 5 word) (Sg G : list byte) (W : world SEGS)
  (m : word -> option byte) (g : Z) (G' : list byte),
  ew (EGSP regs Sg G) n = Z_to_bv 64 g -> 0 <= g -> g + 264 <= 2 ^ 64 -> length G' = 264%nat ->
  CtrlParsed.fu G' 256 4 = CtrlParsed.fu G 256 4 ->
  garr8 SEGS (mrestrict (w_H W) m) g (map bv_unsigned G') ->
  (forall a, g <= a < g + 264 -> writable_at SEGS (mrestrict (w_H W) m) a) ->
  region_ok SEGS (EGSP regs Sg G) (mrestrict (w_H W) m) (gsp_greg n).
Proof.
  intros n regs Sg G W m g G' E10 Hg0 Hg64 HGl HGn HGa HW.
  destruct (gsp_ew_extra regs Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (GateModel.fu_rng4 G' 256 ltac:(lia)) as R256.
  assert (VBg : base_val (EGSP regs Sg G) (Some n) = g)
    by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; lia).
  unfold gsp_greg, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VBg. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ g 256 4 _ (CtrlParsed.fu G' 256 4));
    [cbn [sv_denot]; rewrite E38, <- HGn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia |].
  exact (gsp_val_mem _ g G' 256 4 HGa ltac:(lia)).
Qed.
Lemma gsp_apresent_grow : forall (W : world SEGS) (m m' : word -> option byte) (a : Z),
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HG (Hh & b & Hb). split; [exact Hh|].
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Hb'; [exists b'; reflexivity|]. exfalso.
  apply (HG (Z_to_bv 64 a)).
  - unfold mrestrict. rewrite Hh, Hb. discriminate.
  - unfold mrestrict. rewrite Hh, Hb'. reflexivity.
Qed.
Lemma gsp_writable_of_apresent : forall (W : world SEGS) (m : word -> option byte) (a : Z),
  apresent (w_H W) m a -> writable_at SEGS (mrestrict (w_H W) m) a.
Proof. intros W m a H. apply (apresent_writable SEGS). exact H. Qed.
Definition gsp_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (g s now : Z) (G Sg : list byte) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 10 = w64 g /\ getr regs 11 = w64 s /\ getr regs 12 = w64 now /\ 0 <= now < 2 ^ 64 /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK /\ spZ regs <= sp0 /\
  0 < g /\ g mod 8 = 0 /\ g + 264 <= 2 ^ 63 /\
  (spZ regs <= g \/ g + 264 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) /\
  (forall a, g <= a < g + 264 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  amem_range g 264 /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 264 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) g 264 /\
  length G = 264%nat /\ garr8 SEGS (mrestrict (w_H W) memc) g (map bv_unsigned G) /\
  disco_classify_c.gate_ok G /\
  0 < s /\ s mod 4 = 0 /\ s + 24 <= 2 ^ 63 /\
  (spZ regs <= s \/ s + 24 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) /\
  amem_range s 24 /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) s 24 /\
  length Sg = 24%nat /\ garr8 SEGS (mrestrict (w_H W) memc) s (map bv_unsigned Sg) /\
  (g + 264 <= s \/ s + 24 <= g).
Definition gsp_state (W : world SEGS) (memc mem : word -> option byte) (sp g : Z) (B' : list byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < sp) ->
     ~ (g <= a < g + 264) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem a) /\
  length B' = 264%nat /\ garr8 SEGS (mrestrict (w_H W) mem) g (map bv_unsigned B').
Definition gsp_frame (W : world SEGS) (mem : word -> option byte) (sp : Z) (regs : bvmap 5 word) : Prop :=
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 32) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 40) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 48) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 56) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 64) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 72) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 80) 8 (bv_unsigned (getr regs 24)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 88) 8 (bv_unsigned (getr regs 25)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (sp - 96) 8 (bv_unsigned (getr regs 26)).
Definition gsp_glue_stmt : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 1 = getr regs 1 -> getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s -> getr regs' 11 = w64 (s + 12) ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19584)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Lemma gsp_nodup1 : forall a : bv 5, NoDup [a].
Proof. intros a. apply NoDup_cons_2; [intros H; inversion H | apply NoDup_nil_2]. Qed.
Lemma gsp_nodup2 : forall a b : bv 5, bv_unsigned a <> bv_unsigned b -> NoDup [a; b].
Proof.
  intros a b Hab. apply NoDup_cons_2; [|apply gsp_nodup1].
  intros H. inversion H as [|? ? ? H1]; subst; [congruence | inversion H1].
Qed.
Lemma gsp_nodup3 : forall a b c : bv 5,
  bv_unsigned a <> bv_unsigned b -> bv_unsigned a <> bv_unsigned c -> bv_unsigned b <> bv_unsigned c ->
  NoDup [a; b; c].
Proof.
  intros a b c Hab Hac Hbc. apply NoDup_cons_2; [|apply gsp_nodup2; exact Hbc].
  intros H. inversion H as [|? ? ? H1]; subst; [congruence|].
  inversion H1 as [|? ? ? H2]; subst; [congruence | inversion H2].
Qed.
Lemma gsp_nodup4 : forall a b c d : bv 5,
  bv_unsigned a <> bv_unsigned b -> bv_unsigned a <> bv_unsigned c -> bv_unsigned a <> bv_unsigned d ->
  bv_unsigned b <> bv_unsigned c -> bv_unsigned b <> bv_unsigned d -> bv_unsigned c <> bv_unsigned d ->
  NoDup [a; b; c; d].
Proof.
  intros a b c d Hab Hac Had Hbc Hbd Hcd.
  apply NoDup_cons_2; [|apply gsp_nodup3; assumption].
  intros H. inversion H as [|? ? ? H1]; subst; [congruence|].
  inversion H1 as [|? ? ? H2]; subst; [congruence|].
  inversion H2 as [|? ? ? H3]; subst; [congruence | inversion H3].
Qed.
Lemma gsp_denot_off : forall (regs : bvmap 5 word) (Sg G : list byte) (n : nat) (base c : Z),
  ew (EGSP regs Sg G) n = Z_to_bv 64 base -> 0 <= base < 2 ^ 64 ->
  sv_denot (EGSP regs Sg G) (SOff n c) = w64 (base + c).
Proof.
  intros regs Sg G n base c Hn Hb. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity.
Qed.
Definition gsp_sr (upd : list (bv 5 * sv)) : list sv := sr_sets sr_atoms upd.
Definition gsp_facts2 : facts :=
  mkFacts [ (19%nat, mkAF 0 (2 ^ 47 - 264) 3); (9%nat, mkAF 0 (2 ^ 47 - 24) 2);
            (32%nat, mkAF SB SB 0) ] [] [].
Definition gsp_SH2 : list shent := [ mkSHE 19 0 264; mkSHE 9 0 24 ].
Definition ss_gsp2 (pc : Z) (upd : list (bv 5 * sv)) : sstate :=
  mkSS pc (gsp_sr upd) [gsp_greg 19; gsp_sreg 9] None gsp_facts2.
Lemma gsp_seat : forall (fq : YK11.FPState) (pc : Z) (upd : list (bv 5 * sv)) (regs : bvmap 5 word)
  (W : world SEGS) (mem : word -> option byte) (g s : Z) (G Sg G' : list byte),
  NoDup (map fst upd) ->
  Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs (fst p) = sv_denot (EGSP regs Sg G) (snd p)) upd ->
  getr regs 19 = w64 g -> getr regs 9 = w64 s -> getr regs 21 = w64 SB ->
  0 < g -> g mod 8 = 0 -> amem_range g 264 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF g 264 ->
  0 < s -> s mod 4 = 0 -> amem_range s 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 24 ->
  (g + 264 <= s \/ s + 24 <= g) ->
  length G' = 264%nat -> CtrlParsed.fu G' 256 4 = CtrlParsed.fu G 256 4 ->
  garr8 SEGS (mrestrict (w_H W) mem) g (map bv_unsigned G') ->
  (forall a, g <= a < g + 264 -> apresent (w_H W) mem a) ->
  length Sg = 24%nat -> garr8 SEGS (mrestrict (w_H W) mem) s (map bv_unsigned Sg) ->
  st_ok_pi SEGS VAL (EGSP regs Sg G) (ss_gsp2 pc upd)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS GSP_SBx gsp_SH2 (EGSP regs Sg G) (mrestrict (w_H W) mem).
Proof.
  intros fq pc upd regs W mem g s G Sg G' HND HUPD H19 H9 H21 Hg0 Hg8 Hgapp Hgra Hs0 Hs4 Hsapp Hsra Hds
    HGl HGn HGa HGp HSl HSa.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hgapp, Hsapp. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
  pose proof (gsp_ew_reg regs Sg G 19%bv 19 g eq_refl ltac:(lia) H19) as E19.
  pose proof (gsp_ew_reg regs Sg G 9%bv 9 s eq_refl ltac:(lia) H9) as E9.
  pose proof (gsp_ew_reg regs Sg G 21%bv 21 SB eq_refl ltac:(lia) H21) as E21.
  destruct (gsp_ew_extra regs Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  rewrite restrict_mkst_fx.
  assert (VBg : base_val (EGSP regs Sg G) (Some 19%nat) = g)
    by (cbn [base_val]; rewrite E19; apply unsigned_lit_small; lia).
  assert (VBs : base_val (EGSP regs Sg G) (Some 9%nat) = s)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gsp2. apply pa_entry_st_ok_full.
    + unfold gsp_sr. apply (regs_ok_sets _ sr_atoms regs regs upd);
        [apply regs_ok_EGSP | exact HND | intros r _; reflexivity | exact HUPD].
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (gsp_greg_ok 19 regs Sg G W mem g G' E19 ltac:(lia) ltac:(lia) HGl HGn HGa).
        intros a Ha. apply gsp_writable_of_apresent. apply HGp. exact Ha.
      * exact (gsp_sreg_ok 9 regs Sg G W mem s E9 ltac:(lia) ltac:(lia) HSl HSa).
    + apply pairwise_disjoint_of_extents. unfold gsp_greg, gsp_sreg, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VBg, VBs.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; exact I]. cbn [gsp_facts2 f_atoms atoms_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E19, E9, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia | reflexivity].
  - assert (HUB : U (EGSP regs Sg G) GSP_SBx = SHADOW_OFF)
      by (unfold GSP_SBx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
    assert (HU19 : U (EGSP regs Sg G) (SOff 19 0) = g) by (shent_U_norm; reflexivity).
    assert (HU9 : U (EGSP regs Sg G) (SOff 9 0) = s) by (shent_U_norm; reflexivity).
    unfold gsp_SH2, sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU19, HUB. split.
      * replace (g + 0) with g by lia. replace (264 - 0) with 264 by lia. exact Hgra.
      * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU9, HUB. split.
      * replace (s + 0) with s by lia. replace (24 - 0) with 24 by lia. exact Hsra.
      * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
Lemma gsp_ew_getr : forall (regs : bvmap 5 word) (Sg G : list byte) (r : bv 5) (n : nat),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew (EGSP regs Sg G) n = getr regs r.
Proof.
  intros regs Sg G r n Hn Hlt. unfold EGSP. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma gsp_slot : forall (regs : bvmap 5 word) (Sg G : list byte) (m : word -> option byte)
  (cs : list YP09.chunk) (lo hi wlo whi k : Z) (n : nat) (r : bv 5),
  region_ok SEGS (EGSP regs Sg G) m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  In (YP09.mkChunk (- k) (CVal 8 (SOff n 0))) cs -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  val_mem SEGS m (spZ regs - k) 8 (bv_unsigned (getr regs r)).
Proof.
  intros regs Sg G m cs lo hi wlo whi k n r HR Hin Hn Hlt.
  replace (spZ regs - k) with (spZ regs + - k) by lia.
  apply (slot_of_region (EGSP regs Sg G) m (spZ regs) cs lo hi wlo whi (- k) (SOff n 0)
    (bv_unsigned (getr regs r)) HR).
  - rewrite (gsp_ew_getr regs Sg G 2%bv 2 eq_refl ltac:(lia)). reflexivity.
  - exact Hin.
  - cbn [sv_denot]. rewrite (gsp_ew_getr regs Sg G r n Hn Hlt), Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hq.
    change (bv_modulus 64) with (2 ^ 64) in Hq. exact Hq.
Qed.
Lemma gsp_prologue : gsp_glue_stmt -> treac_disco_gate_should_push_spec.
Proof.
  intros HGLUE.
  unfold treac_disco_gate_should_push_spec.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg
    HJ Hra Hra4 Hgp Htp H10 H11 H12 Hnow Hal16 Hbud Hsp Hg0 Hg8 Hg63 Hgside Hgwr Hgapp Hgra Hghull
    HGlen HGarr HGok Hs0 Hs4 Hs63 Hsside Hsloc Hsapp Hsra Hshull HSlen HSarr Hds.
  assert (HCTX : gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg)
    by (unfold gsp_ctx; repeat (split; [assumption|]); assumption).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (Usp : bv_unsigned (ew (EGSP regs Sg G) 2) = spZ regs)
    by (rewrite (gsp_ew_getr regs Sg G 2%bv 2 eq_refl ltac:(lia)); reflexivity).
  destruct (gsp_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s G Sg
    HJ H10 H11 Hal16 Hbud Hsp Hg0 Hg8 Hgapp Hgra Hs0 Hs4 Hsapp Hsra) as [HS SHOK].
  unfold cfg_at.
  change (w64 (BASE + AF_reac_disco_gate_should_push)) with (Z_to_bv 64 (BASE + AF_reac_disco_gate_should_push)).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  assert (HEI : img_env VAL A_LIM (EGSP regs Sg G)) by (unfold EGSP; apply Eimg_env).
  paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19584.
  { unfold ss_gsp, gsp_regions. cbn [ss_mem].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs)); [reflexivity | exact Usp | |].
    - cbn [YP09.r_wlo YP09.r_whi stack_region]. intros a Ha. left. lia.
    - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
  cbn [ms_mem restrict] in HR0.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3.
  prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
  prreg HS (11%bv : bv 5) R11. prreg HS (19%bv : bv 5) R19. prreg HS (21%bv : bv 5) R21.
  prreg HS (27%bv : bv 5) R27.
  assert (Q1 : getr (ms_regs ms) 1 = getr regs 1)
    by (rewrite R1; exact (gsp_ew_getr regs Sg G 1%bv 1 eq_refl ltac:(lia))).
  assert (Q2 : getr (ms_regs ms) 2 = w64 (spZ regs - 96))
    by (rewrite R2, Usp; unfold w64; f_equal; lia).
  assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
    by (rewrite R3, (gsp_ew_getr regs Sg G 3%bv 3 eq_refl ltac:(lia)); exact Hgp).
  assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
    by (rewrite R4, (gsp_ew_getr regs Sg G 4%bv 4 eq_refl ltac:(lia)); exact Htp).
  assert (Q27 : getr (ms_regs ms) 27 = getr regs 27)
    by (rewrite R27; exact (gsp_ew_getr regs Sg G 27%bv 27 eq_refl ltac:(lia))).
  assert (Q8 : getr (ms_regs ms) 8 = w64 now)
    by (rewrite R8, (gsp_ew_getr regs Sg G 12%bv 12 eq_refl ltac:(lia)); exact H12).
  assert (Q9 : getr (ms_regs ms) 9 = w64 s)
    by (rewrite R9, (gsp_ew_getr regs Sg G 11%bv 11 eq_refl ltac:(lia)); exact H11).
  assert (Q11 : getr (ms_regs ms) 11 = w64 (s + 12))
    by (rewrite R11, (gsp_ew_getr regs Sg G 11%bv 11 eq_refl ltac:(lia)), H11; unfold w64;
        rewrite unsigned_lit_small by lia; reflexivity).
  assert (Q19 : getr (ms_regs ms) 19 = w64 g)
    by (rewrite R19, (gsp_ew_getr regs Sg G 10%bv 10 eq_refl ltac:(lia)); exact H10).
  assert (Q21 : getr (ms_regs ms) 21 = w64 SB)
    by (rewrite R21; destruct (gsp_ew_extra regs Sg G) as (E32 & _); exact E32).
  assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
            mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H W) memc) a)
    by exact (gsp_entry_mbyte regs Sg G W memc (ms_mem ms) HFr).
  assert (ST : gsp_state W memc (ms_mem ms) (spZ regs) g G).
  { unfold gsp_state. split; [|split; [|split]].
    - intros a Ha Hn _. unfold aview. rewrite (MB a Ha) by (rewrite WS in Hn; lia). reflexivity.
    - intros a Ha. exact (gsp_apresent_grow W memc (ms_mem ms) a HG Ha).
    - exact HGlen.
    - apply (gsp_garr8_move W memc (ms_mem ms) g (map bv_unsigned G) (spZ regs - 96) (spZ regs) HGarr MB).
      + lia.
      + rewrite length_map, HGlen. change (Z.of_nat 264) with 264. lia.
      + rewrite length_map, HGlen. change (Z.of_nat 264) with 264. rewrite WS in Hgside. lia. }
  assert (FR : gsp_frame W (ms_mem ms) (spZ regs) regs).
  { unfold gsp_frame.
    repeat split; eapply gsp_slot; try exact HR0;
      try (cbn [In]; repeat (first [left; reflexivity | right]));
      try reflexivity; try lia. }
  pmkst HS.
  exact (HGLUE fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg
    (ms_regs ms) (ms_mem ms) _ HCTX HJ ST FR Q1 Q2 Q3 Q4 Q27 Q8 Q9 Q11 Q19 Q21).
Qed.
Definition gsp_gro (n : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 264 0 0 [YP09.mkChunk 256 (CVal 4 (SOff 38 0))].
Definition ss_gspR (pc : Z) (upd : list (bv 5 * sv)) : sstate :=
  mkSS pc (gsp_sr upd) [gsp_gro 19; gsp_sreg 9] None gsp_facts2.
Lemma gsp_ro : forall (fq : YK11.FPState) E pc upd ms,
  st_ok_pi (fx := fq) SEGS VAL E (ss_gsp2 pc upd) ms -> st_ok_pi (fx := fq) SEGS VAL E (ss_gspR pc upd) ms.
Proof.
  intros fq E pc upd ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (HW & HR & HD) & H9).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj _ H9)))))))).
  split; [vm_compute; reflexivity|]. split.
  - cbn [abs_ss setpc ss_gsp2 ss_gspR ss_mem] in HR |- *.
    inversion HR as [|r0 rs0 Hg HR' Heq]; subst.
    apply Forall_cons; [|exact HR'].
    destruct Hg as (A1 & A2 & _ & A4). split; [exact A1|]. split; [exact A2|].
    split; [intros o Ho; cbn in Ho; lia | exact A4].
  - exact HD.
Qed.
Lemma gsp_nowin_frame : forall E (rs : smem) (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
  intros E rs m m' Hw HF x. apply HF. intros (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ rs) Hw r Hin) as Hr2. apply Z.leb_le in Hr2. lia.
Qed.
Lemma gsp_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  aview SEGS H m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H m') a) as [b1|]; destruct (mbyte SEGS (mrestrict H m) a) as [b2|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma gsp_stk_lo : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  CEIL_MIN <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
  destruct Hst as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof alloc_ceiling_value as (Hc & _). lia.
Qed.
Lemma gsp_view_G : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte) (mem' : word -> option byte),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  gsp_state W memc mem' (spZ regs) g G ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < spZ regs) ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg mem' HC (Hk & Hp & Hl & Ha) a Ha0 Hn.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGlen & HGarr & _).
  destruct (Z_lt_le_dec a g) as [Hlt|Hge]; [apply Hk; lia|].
  destruct (Z_lt_le_dec a (g + 264)) as [Hlt2|Hge2]; [|apply Hk; lia].
  replace a with (g + Z.of_nat (Z.to_nat (a - g))) by lia.
  rewrite (gsp_aview_byte W mem' g G (Z.to_nat (a - g)) Ha ltac:(lia)).
  rewrite (gsp_aview_byte W memc g G (Z.to_nat (a - g)) HGarr ltac:(lia)).
  reflexivity.
Qed.
Lemma gsp_seatR : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (pc : Z) (upd : list (bv 5 * sv)),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  gsp_state W memc mem' (spZ regs) g G ->
  NoDup (map fst upd) ->
  Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot (EGSP regs' Sg G) (snd p)) upd ->
  getr regs' 19 = w64 g -> getr regs' 9 = w64 s -> getr regs' 21 = w64 SB ->
  st_ok_pi SEGS VAL (EGSP regs' Sg G) (ss_gspR pc upd)
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + pc)) mem' (seg_rom SEGS)))
  /\ sh_ok SEGS GSP_SBx gsp_SH2 (EGSP regs' Sg G) (mrestrict (w_H W) mem').
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' pc upd HC HST HND HUPD R19 R9 R21.
  pose proof HC as (HJc & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgside
    & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 & Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  pose proof (gsp_view_G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg mem' HC HST) as HV.
  pose proof (gsp_stk_lo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJc) as (Hc0 & _).
  assert (Hlo : kHighShadowEnd <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) by (unfold kHighShadowEnd; lia).
  assert (Hg47 : g + 264 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp; lia).
  assert (Hs47 : s + 24 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hsapp; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg)).
  { apply (garr8_frame SEGS _ _ s _ HSarr). intros a Ha. rewrite length_map, HSlen in Ha.
    apply gsp_mbyte_of_aview. apply HV; [lia|]. destruct Hsside; lia. }
  destruct (gsp_seat fq pc upd regs' W mem' g s G Sg G HND HUPD R19 R9 R21 Hg0 Hg8 Hgapp
     (range_addressable_kept_win _ _ _ _ g 264 HV Hlo ltac:(lia) Hg47 Hgra)
     Hs0 Hs4 Hsapp (range_addressable_kept_win _ _ _ _ s 24 HV Hlo ltac:(lia) Hs47 Hsra)
     Hds HBl eq_refl HBa (fun a Ha => Hpres a (proj2 (Hgwr a Ha))) HSlen HSa') as [HS SH].
  split; [apply gsp_ro; exact HS | exact SH].
Qed.
Lemma gsp_keep_win : forall (W : world SEGS) (m m' memc : word -> option byte) (sp g lo hi : Z) (B' : list byte)
    (regs : bvmap 5 word),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  sp - REAC_DISCO_GATE_SHOULD_PUSH_STK <= lo -> hi <= sp - 96 -> 96 <= sp -> sp <= 2 ^ 64 ->
  (hi <= g \/ g + 264 <= lo) -> 0 <= g -> g + 264 <= 2 ^ 64 ->
  gsp_state W memc m sp g B' -> gsp_frame W m sp regs ->
  gsp_state W memc m' sp g B' /\ gsp_frame W m' sp regs.
Proof.
  intros W m m' memc sp g lo hi B' regs HV HP Hlo Hhi Hsp0 Hsp1 Hg Hg0 Hg1 (Hk & Hpr & Hl & Ha) HF.
  assert (HM : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
    mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a)
    by (intros a Ha0 Hn; apply gsp_mbyte_of_aview; apply HV; assumption).
  assert (HVM : forall a n v, sp - 96 <= a -> a + Z.of_nat n <= sp ->
    val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v).
  { intros a n v H1 H2 HVm kk Hkk. rewrite HM by lia. apply HVm. exact Hkk. }
  split.
  - split; [intros a Ha0 Hn1 Hn2; rewrite HV by (unfold REAC_DISCO_GATE_SHOULD_PUSH_STK in *; lia); apply Hk; assumption|].
    split; [intros a Hq; apply HP, Hpr, Hq|].
    split; [exact Hl|].
    apply (garr8_frame SEGS _ _ g _ Ha). intros a Hb. rewrite length_map, Hl in Hb. apply HM; lia.
  - unfold gsp_frame in *.
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
    repeat split; (eapply HVM; [lia | lia | eassumption]).
Qed.
Lemma gsp_run_keep : forall (W : world SEGS) (m m' memc : word -> option byte) (sp g : Z) (B' : list byte)
    (regs : bvmap 5 word),
  (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  gsp_state W memc m sp g B' -> gsp_frame W m sp regs ->
  96 <= sp -> sp <= 2 ^ 64 -> 0 <= g -> g + 264 <= 2 ^ 64 ->
  (sp <= g \/ g + 264 <= sp - REAC_DISCO_GATE_SHOULD_PUSH_STK) ->
  gsp_state W memc m' sp g B' /\ gsp_frame W m' sp regs.
Proof.
  intros W m m' memc sp g B' regs HE HG HST HFR Hs0 Hs1 Hg0 Hg1 Hside.
  apply (gsp_keep_win W m m' memc sp g (sp - 96) (sp - 96) B' regs).
  - intros a _ _. unfold aview, mbyte. rewrite HE. reflexivity.
  - intros a Ha. exact (gsp_apresent_grow W m m' a HG Ha).
  - unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK. lia.
  - lia. - lia. - lia.
  - unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hside. lia.
  - lia. - lia. - exact HST. - exact HFR.
Qed.
Lemma gsp_w64U : forall E v z, U E v = z -> sv_denot E v = w64 z.
Proof. intros E v z H. rewrite denot_lit_U, H. reflexivity. Qed.
Lemma gsp_Uzx8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
  intros E n v H Hv. rewrite U_zext, (U_atom E n v H) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma gsp_Udk : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> 0 <= a < 256 -> ew E n2 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff n1 0)) (SLit 8)) (SExt false 8 (SOff n2 0))) = 256 * a + b.
Proof.
  intros E n1 n2 a b H1 Ha H2 Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SLit, (gsp_Uzx8 E n1 a H1 Ha), (gsp_Uzx8 E n2 b H2 Hb).
  change (Z.land (zcanon 8) 63) with 8.
  rewrite (zcanon_id (Z.shiftl a 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
  rewrite slot_lib.lor_byte_shift by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma gsp_denot_reg : forall (regs : bvmap 5 word) (Sg G : list byte) (r : bv 5) (n : nat),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> sv_denot (EGSP regs Sg G) (SOff n 0) = getr regs r.
Proof.
  intros regs Sg G r n Hn Hlt. cbn [sv_denot]. unfold EGSP. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ n r Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Ltac qreg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.
Ltac qatom HS r n H :=
  qreg HS r H; rewrite (gsp_denot_reg _ _ _ r n eq_refl ltac:(lia)) in H.
Ltac gkeep HST HFR :=
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2), HG : mem_grows _ _ |- _ =>
    let X := fresh "X" in
    pose proof (gsp_run_keep Wx m1 m2 _ _ _ _ _ (gsp_nowin_frame _ rs _ _ ltac:(vm_compute; reflexivity) HFr) HG HST HFR
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as X;
    clear HST HFR; destruct X as [HST HFR]; clear HFr HG;
    repeat match goal with HF : frame_of _ _ _ _ |- _ => clear HF end
  end.
Lemma gsp_gn : forall G, disco_classify_c.gate_ok G ->
  CtrlParsed.fu G 256 4 = disco_classify_c.gn G /\ 0 <= disco_classify_c.gn G <= 8.
Proof.
  intros G (HL & Hn & _). pose proof (GateModel.fu_rng4 G 256 ltac:(lia)) as R.
  unfold disco_classify_c.gn, CtrlParsed.s32 in *.
  destruct (Z.ltb_spec (CtrlParsed.fu G 256 4) (2 ^ 31)); lia.
Qed.
Lemma gsp_U_sx32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
  intros E n v H Hv. rewrite U_SExt, (U_atom E n v H) by lia. change (2 ^ Z.of_N 32) with 4294967296.
  rewrite (Z.mod_small v) by lia.
  assert (Hs : bv_swrap 32 v = v).
  { unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
    rewrite Z.mod_small by lia. lia. }
  rewrite Hs. apply zcanon_id. unfold M64. lia.
Qed.
Lemma gsp_U_shadow : forall E g, ew E 19 = Z_to_bv 64 g -> ew E 32 = Z_to_bv 64 SB -> 0 <= g -> g + 256 < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 256) (SLit 3)) (SOff 32 0)) = (g + 256) / 8 + SB.
Proof.
  intros E g H19 H32 Hg0 Hg1. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SLit. rewrite (U_atom_off E 19 g 256 H19) by lia. rewrite (U_atom E 32 SB H32) by (unfold SB; lia).
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (D0 : 0 <= (g + 256) / 8) by (apply Z.div_pos; lia).
  assert (D1 : (g + 256) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  rewrite (zcanon_id ((g + 256) / 8)) by (unfold M64; lia).
  apply zcanon_id. unfold M64, SB. lia.
Qed.
Lemma gsp_U_s10 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 8 ->
  U E (SAlu ALU_SLL (SExt true 32 (SOff n 0)) (SLit 5)) = 32 * v.
Proof.
  intros E n v H Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (gsp_U_sx32 E n v H) by lia.
  change (Z.land (zcanon 5) 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma gsp_bge0 : forall E a v, U E a = v -> 0 <= v <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E a) = (v <=? 0).
Proof.
  intros E a v H Hv. rewrite (denot_lit_U E a), H. cbn [branch_taken sv_denot]. unfold bv_lts.
  rewrite !YK00.bv_signed_small by lia. rewrite Z.leb_antisym. reflexivity.
Qed.
Ltac qregc HS r H :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.
Ltac qatomc HS r n H :=
  qregc HS r H; rewrite (gsp_denot_reg _ _ _ r n eq_refl ltac:(lia)) in H.
Lemma gsp_U_add2 : forall E n k a b, ew E n = Z_to_bv 64 a -> ew E k = Z_to_bv 64 b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff n 0) (SOff k 0)) = a + b.
Proof.
  intros E n k a b Ha Hb Ha0 Hb0 Hab. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n a Ha) by lia. rewrite (U_atom E k b Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma gsp_hull_sub : forall (rd : Z -> option Z) a n a' n', shadow_hull_vis rd a n -> 0 <= a -> a <= a' ->
  a' + n' <= a + n -> 0 < n' -> shadow_hull_vis rd a' n'.
Proof.
  intros rd a n a' n' HV Ha H1 H2 Hn x Hx. apply HV. unfold shadow_addr in *.
  pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1) as D1.
  pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
  lia.
Qed.
Definition gtl_fx (regs : bvmap 5 word) : list word :=
  [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
   getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26].
Definition ETL (regs' regs : bvmap 5 word) : env := Eimg (Ereg regs' (gtl_fx regs)).
Definition gtl_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 96 0 0
    [YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0));
     YP09.mkChunk 72 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0));
     YP09.mkChunk 56 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 37 0));
     YP09.mkChunk 40 (CVal 8 (SOff 38 0)); YP09.mkChunk 32 (CVal 8 (SOff 39 0));
     YP09.mkChunk 24 (CVal 8 (SOff 40 0)); YP09.mkChunk 16 (CVal 8 (SOff 41 0));
     YP09.mkChunk 8 (CVal 8 (SOff 42 0)); YP09.mkChunk 0 (CVal 8 (SOff 43 0))].
Definition gtl_nofacts : facts := mkFacts [] [] [].
Lemma regs_ok_ETL : forall regs' regs, regs_ok (ETL regs' regs) sr_atoms regs'.
Proof.
  intros. unfold ETL. apply (regs_ok_agree 32 (Ereg regs' (gtl_fx regs))).
  - split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply regs_ok_Ereg.
Qed.
Lemma gtl_ew : forall regs' regs (j : nat), (j < 12)%nat ->
  ew (ETL regs' regs) (32 + j) = nth j (gtl_fx regs) (Z_to_bv 64 0).
Proof.
  intros regs' regs j Hj. unfold ETL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
Lemma gtl_seat : forall (fq : YK11.FPState) (pc : Z) (regs' regs : bvmap 5 word) (W : world SEGS)
  (mem : word -> option byte),
  getr regs' 2 = w64 (spZ regs - 96) -> 96 <= spZ regs ->
  gsp_frame W mem (spZ regs) regs ->
  st_ok_pi SEGS VAL (ETL regs' regs) (mkSS pc sr_atoms [gtl_stk] None gtl_nofacts)
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fq pc regs' regs W mem H2 Hsp HF.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R2. change (bv_modulus 64) with (2 ^ 64) in R2.
  assert (VB : base_val (ETL regs' regs) (Some 2%nat) = spZ regs - 96).
  { cbn [base_val]. unfold ETL. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. unfold spZ in *. lia. }
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_ETL.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold gtl_stk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB.
    unfold spZ in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    destruct HF as (F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26).
    repeat apply Forall_cons; try apply Forall_nil.
    all: match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?n 0))) =>
      let j := eval compute in (n - 32)%nat in
      apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (nth j (gtl_fx regs) (Z_to_bv 64 0))));
      [cbn [sv_denot]; change n with (32 + j)%nat; rewrite (gtl_ew regs' regs j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range | lia |] end.
    all: cbn [gtl_fx nth]; change (N.to_nat 8) with 8%nat;
      match goal with |- val_mem _ _ (?b + ?o) 8 _ =>
        let d := eval compute in (96 - o) in
        replace (b + o) with (bv_unsigned (getr regs 2) - d) by lia; assumption end.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; exact I]. exact I.
Qed.
Lemma gtl_ewr : forall (regs' regs : bvmap 5 word) (r : bv 5) (n : nat),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew (ETL regs' regs) n = getr regs' r.
Proof.
  intros regs' regs r n Hn Hlt. unfold ETL. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs' _ n r Hn).
Qed.
Lemma gtl_post : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs2 : bvmap 5 word) (mem' mem2 : word -> option byte) (md2 : Model) (B' : list byte),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  (forall x : word, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem' x) ->
  aregs_preserved regs regs2 -> getr regs2 1 = getr regs 1 ->
  getr regs2 10 = w64 (snd (GateModel.gate_model G Sg now)) -> B' = fst (GateModel.gate_model G Sg now) ->
  treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg W
    (mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs2 mem' mem2 md2 B'
    HC HJ (HSt1 & HSt2 & HBl & HBa) HM HP Hr1 H10 HB.
  pose proof HC as (HJc & Hra & Hra4 & Hgp & Htp & H10c & H11c & H12c & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgd
    & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hsd & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof (proj1 HJc) as HAR.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  rewrite WS in Hgd, Hsd, HSt1. change (96 + 2 * ESTACK) with 8288 in Hbud.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R2. change (bv_modulus 64) with (2 ^ 64) in R2.
  pose proof (gsp_range_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g 264 HJc ltac:(lia) ltac:(lia) (fun a Ha => proj1 (Hgw a Ha)))
    as (GR1 & GR2 & GR3).
  assert (AV : forall a, aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem' a)
    by (intros a; unfold aview, mbyte; rewrite HM; reflexivity).
  assert (AP : forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a).
  { intros a. apply gsp_apresent_grow. intros x Hx. rewrite HM. exact Hx. }
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8288 <= a < spZ regs) -> ~ (g <= a < g + 264) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
    by (intros a Ha H1 H2; rewrite AV; apply HSt1; assumption).
  unfold treac_disco_gate_should_push_post.
  exists lyc, Sc, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|]. split; [exact Hr1|]. split; [exact H10|].
  split; [reflexivity|]. split; [apply Permutation_refl|].
  split; [|split; [|split; [|]]].
  - unfold treac_disco_gate_should_push_kept. rewrite WS.
    split; [intros a Ha H1 H2; apply KA; lia|].
    split; [intros b m i Hin Hi H2; destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4 & Hbc & _);
            apply KA; unfold spZ in *; lia|].
    split; [intros a Ha _ _; pose proof (pa_img_range a Ha) as Hl; pose proof (pa_segs_low a Ha) as Hl2;
            apply KA; unfold spZ, IMG_LO, IMG_TOP in *; lia|].
    split; [intros cid pos a Hin Ha H2; destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4 & Hfc & _);
            pose proof (fs_frame_bytes_nonneg cid) as Hfb; apply KA; [| |exact H2];
            unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in *; cbn [fst snd] in *; unfold spZ in *;
            destruct Ha as [Ha|Ha]; Z.div_mod_to_equations; lia|].
    split; [intros a Ha H1 Hp; apply AP; apply HSt2; exact Hp|].
    intros a Ha. apply Hpres2. unfold spZ in *. lia.
  - subst B'. apply (garr8_frame SEGS _ _ g _ HBa). intros a Ha. unfold mbyte. rewrite HM. reflexivity.
  - exact (GateModel.gate_model_ok G Sg now HGok HSl).
  - apply (garr8_frame SEGS _ _ s _ HSa). intros a Ha. rewrite length_map, HSl in Ha.
    apply gsp_mbyte_of_aview. apply KA; unfold spZ in *; lia.
Qed.
Lemma gsp_epi : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 27 = getr regs 27 ->
  getr regs' 10 = w64 (snd (GateModel.gate_model G Sg now)) ->
  B' = fst (GateModel.gate_model G Sg now) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20252)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' B'
    HC HJ HST HFR H2 H3 H4 H27 H10 HB.
  pose proof HC as (HJc & Hra & _ & _ & _ & _ & _ & _ & _ & _ & Hbud & Hsp & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288 in Hbud.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R2. change (bv_modulus 64) with (2 ^ 64) in R2.
  pose proof (gtl_seat fq 20252 regs' regs W mem' H2 ltac:(lia) HFR) as HS.
  assert (SHOK : sh_ok SEGS (SOff 21 0) [] (ETL regs' regs) (mrestrict (w_H W) mem')) by constructor.
  assert (HEI : img_env VAL A_LIM (ETL regs' regs)) by (unfold ETL; apply Eimg_env).
  assert (E32 : ew (ETL regs' regs) 32 = getr regs 1) by exact (gtl_ew regs' regs 0 ltac:(lia)).
  pose (RUN := paj_run (fx := fq) B LAWS).
  paj_run_tok RUN HS HJ SHOK GSP_span.
  - apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
  - prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
    assert (AP : aregs_preserved regs (ms_regs ms)).
    { intros r Hr. unfold acallee_saved in Hr.
      assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 27 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21
        \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | Hc]]]].
      - prreg HS (Z_to_bv 5 2) Q. rewrite Q, (gtl_ewr regs' regs 2%bv 2 eq_refl ltac:(lia)), H2.
        unfold w64, spZ. rewrite unsigned_lit_small by (unfold spZ in *; lia).
        rewrite Z.sub_add, Z_to_bv_bv_unsigned. reflexivity.
      - prreg HS (Z_to_bv 5 3) Q. rewrite Q, (gtl_ewr regs' regs 3%bv 3 eq_refl ltac:(lia)). exact H3.
      - prreg HS (Z_to_bv 5 4) Q. rewrite Q, (gtl_ewr regs' regs 4%bv 4 eq_refl ltac:(lia)). exact H4.
      - prreg HS (Z_to_bv 5 27) Q. rewrite Q, (gtl_ewr regs' regs 27%bv 27 eq_refl ltac:(lia)). exact H27.
      - repeat destruct Hc as [-> | Hc];
        try match goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
          let Q := fresh "Q" in prreg HS (Z_to_bv 5 n) Q; rewrite Q;
          lazymatch type of Q with _ = ew _ ?m => exact (gtl_ew regs' regs (m - 32) ltac:(lia)) end end.
        subst r.
        let Q := fresh "Q" in prreg HS (Z_to_bv 5 26) Q; rewrite Q;
        lazymatch type of Q with _ = ew _ ?m => exact (gtl_ew regs' regs (m - 32) ltac:(lia)) end. }
    pose (RET := paj_ret_at (PL := PL_disco) (PI := PI)).
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat2.
    rewrite R1, E32, Hra.
    apply (gtl_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_regs ms) mem' (ms_mem ms) _ B'
      HC); [| exact HST | | exact AP | rewrite R1; exact E32 | | exact HB].
    + apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
    + lazymatch type of HFr with frame_of ?E ?rs ?m1 ?m2 =>
        exact (gsp_nowin_frame E rs m1 m2 ltac:(vm_compute; reflexivity) HFr) end.
    + rewrite R10, (gtl_ewr regs' regs 10%bv 10 eq_refl ltac:(lia)). exact H10.
Qed.
Lemma gtl_nth_le : forall (n : nat) (v : Z) (k : nat), 0 <= v -> (k < n)%nat ->
  nth k (Z_to_le_bytes n v) (CtrlParsed.zb 0) = Z_to_bv 8 (YO0f.le_byte v n k).
Proof.
  assert (A : forall (n : nat) (v : Z) (k : nat), (k < n)%nat ->
    nth k (Z_to_le_bytes n v) (CtrlParsed.zb 0) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k))).
  { induction n as [|n IH]; intros v k Hk; [lia|]. destruct k as [|k].
    - cbn [Z_to_le_bytes nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
    - cbn [Z_to_le_bytes nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia. }
  intros n v k Hv Hk. rewrite A by exact Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8). unfold YO0f.le_byte. change 256 with (2 ^ 8).
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.lt_ge_cases j 8) as [Hj8|Hj8].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma gtl_garr8_of : forall (m : word -> option byte) (base : Z) (U : list byte),
  (forall j, (j < length U)%nat -> mbyte SEGS m (base + Z.of_nat j) = Some (nth j U (CtrlParsed.zb 0))) ->
  garr8 SEGS m base (map bv_unsigned U).
Proof.
  intros m base U H j Hj. rewrite length_map in Hj. rewrite (gsp_nth_map U j).
  pose proof (GateModel.byte_rng (nth j U (CtrlParsed.zb 0))) as R.
  split; [|exact R].
  intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, (H j Hj).
  f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small _ 256 R), (Z.mod_small _ 256 R).
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma gtl_vm_move : forall (m m' : word -> option byte) (a : Z) (n : nat) (v : Z),
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v HM H k Hk. unfold mbyte. rewrite (HM k Hk). exact (H k Hk). Qed.
Lemma gtl_frame_move : forall (W : world SEGS) (m m' : word -> option byte) (sp : Z) (regs : bvmap 5 word),
  96 <= sp -> sp <= 2 ^ 64 ->
  (forall a, sp - 96 <= a < sp -> mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a)) ->
  gsp_frame W m sp regs -> gsp_frame W m' sp regs.
Proof.
  intros W m m' sp regs H96 H64 HM (F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26).
  repeat split; eapply gtl_vm_move; try eassumption; intros k Hk; apply HM; lia.
Qed.
Lemma gtl_keep_st : forall (W : world SEGS) (memc m m' : word -> option byte) (sp g : Z) (B' : list byte)
  (regs : bvmap 5 word) (p : nat) (L : list byte),
  (forall x : word, ~ (g + Z.of_nat p <= bv_unsigned x < g + Z.of_nat p + Z.of_nat (length L)) ->
     mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall j, (j < length L)%nat ->
     mbyte SEGS (mrestrict (w_H W) m') (g + Z.of_nat p + Z.of_nat j) = Some (nth j L (CtrlParsed.zb 0))) ->
  (p + length L <= 264)%nat -> 0 <= g -> g + 264 <= 2 ^ 64 -> 96 <= sp -> sp <= 2 ^ 64 ->
  (sp <= g \/ g + 264 <= sp - 96) ->
  gsp_state W memc m sp g B' -> gsp_frame W m sp regs ->
  gsp_state W memc m' sp g (Mem.upd_bytes B' p L) /\ gsp_frame W m' sp regs.
Proof.
  intros W memc m m' sp g B' regs p L HM HG HL Hp Hg0 Hg64 H96 H64 Hd (HSt1 & HSt2 & HBl & HBa) HF.
  split.
  - split; [intros a Ha H1 H2; rewrite <- (HSt1 a Ha H1 H2); unfold aview, mbyte;
            rewrite HM by (rewrite unsigned_lit_small by lia; lia); reflexivity|].
    split; [intros a Hp'; apply (gsp_apresent_grow W m m' a HG); apply HSt2; exact Hp'|].
    assert (HU : length (Mem.upd_bytes B' p L) = 264%nat) by (rewrite GateModel.length_upd by lia; exact HBl).
    split; [exact HU|].
    apply gtl_garr8_of. intros j Hj. rewrite HU in Hj.
    pose proof (GateModel.nth_error_upd B' p L ltac:(lia) j) as NE.
    rewrite (@nth_error_nth' byte (Mem.upd_bytes B' p L) j (CtrlParsed.zb 0) ltac:(rewrite HU; exact Hj)) in NE.
    destruct ((p <=? j)%nat && (j <? p + length L)%nat) eqn:Hw.
    + apply andb_true_iff in Hw as [Hw1 Hw2]. apply Nat.leb_le in Hw1. apply Nat.ltb_lt in Hw2.
      rewrite (@nth_error_nth' byte L (j - p) (CtrlParsed.zb 0) ltac:(lia)) in NE. injection NE as NE. rewrite NE.
      replace (g + Z.of_nat j) with (g + Z.of_nat p + Z.of_nat (j - p)) by lia. apply HL. lia.
    + rewrite (@nth_error_nth' byte B' j (CtrlParsed.zb 0) ltac:(lia)) in NE. injection NE as NE. rewrite NE.
      apply andb_false_iff in Hw.
      unfold mbyte. rewrite HM by (rewrite unsigned_lit_small by lia; destruct Hw as [Hw|Hw];
        [apply Nat.leb_gt in Hw | apply Nat.ltb_ge in Hw]; lia).
      pose proof (garr8_mbyte SEGS _ g _ j HBa ltac:(rewrite length_map; lia)) as Hb. unfold mbyte in Hb.
      rewrite Hb, gsp_nth_map, Z_to_bv_bv_unsigned. reflexivity.
  - apply (gtl_frame_move W m m' sp regs H96 H64); [|exact HF].
    intros a Ha. apply HM. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma gsp_ret0 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 27 = getr regs 27 ->
  GateModel.gate_model G Sg now = (B', 0) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20108)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' B'
    HC HJ HST HFR H2 H3 H4 H27 HM.
  pose proof HC as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgd & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288 in Hbud.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R2r. change (bv_modulus 64) with (2 ^ 64) in R2r.
  pose proof (gtl_seat fq 20108 regs' regs W mem' H2 ltac:(lia) HFR) as HS.
  assert (SHOK : sh_ok SEGS (SOff 21 0) [] (ETL regs' regs) (mrestrict (w_H W) mem')) by constructor.
  assert (HEI : img_env VAL A_LIM (ETL regs' regs)) by (unfold ETL; apply Eimg_env).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20252.
  - apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
  - pmkst HS.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (27%bv : bv 5) R27. prreg HS (10%bv : bv 5) R10.
    lazymatch type of HFr with frame_of ?E ?rs ?m1 ?m2 =>
      pose proof (gsp_nowin_frame E rs m1 m2 ltac:(vm_compute; reflexivity) HFr) as HE end.
    destruct (gsp_run_keep W mem' (ms_mem ms) memc (spZ regs) g B' regs HE HG HST HFR
      ltac:(lia) ltac:(unfold spZ in *; lia) ltac:(lia) ltac:(lia)
      ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia)) as [HST2 HFR2].
    apply (gsp_epi fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_regs ms) (ms_mem ms) _ B'
      HC HJ HST2 HFR2).
    + rewrite R2, (gtl_ewr regs' regs 2%bv 2 eq_refl ltac:(lia)). exact H2.
    + rewrite R3, (gtl_ewr regs' regs 3%bv 3 eq_refl ltac:(lia)). exact H3.
    + rewrite R4, (gtl_ewr regs' regs 4%bv 4 eq_refl ltac:(lia)). exact H4.
    + rewrite R27, (gtl_ewr regs' regs 27%bv 27 eq_refl ltac:(lia)). exact H27.
    + rewrite R10, HM. reflexivity.
    + rewrite HM. reflexivity.
Qed.
Definition gtl_ereg (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 18%nat) 0 32 wlo whi [].
Definition gtl_ffacts : facts := mkFacts [(18%nat, mkAF 0 (2 ^ 47 - 32) 3)] [] [].
Definition gtl_efacts : facts := mkFacts [(18%nat, mkAF 0 (2 ^ 47 - 32) 3); (21%nat, mkAF SB SB 0)] [] [].
Lemma gtl_ffacts_ok : forall (regs' regs : bvmap 5 word) (e : Z),
  getr regs' 18 = w64 e -> 0 <= e <= 2 ^ 47 - 32 -> e mod 8 = 0 -> facts_ok (ETL regs' regs) gtl_ffacts.
Proof.
  intros regs' regs e H18 He He8. split; [|split; exact I].
  cbn [gtl_ffacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18. unfold w64.
  rewrite unsigned_lit_small by lia. change (2 ^ 3) with 8. repeat split; try lia; exact I.
Qed.
Lemma gtl_efacts_ok : forall (regs' regs : bvmap 5 word) (e : Z),
  getr regs' 18 = w64 e -> getr regs' 21 = w64 SB -> 0 <= e <= 2 ^ 47 - 32 -> e mod 8 = 0 ->
  facts_ok (ETL regs' regs) gtl_efacts.
Proof.
  intros regs' regs e H18 H21 He He8. split; [|split; exact I].
  cbn [gtl_efacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18, (gtl_ewr regs' regs 21%bv 21 eq_refl ltac:(lia)), H21.
  unfold w64, SB. rewrite !unsigned_lit_small by lia. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia; exact I.
Qed.
Lemma gtl_eseat : forall (fq : YK11.FPState) (pc : Z) (regs' regs : bvmap 5 word) (W : world SEGS)
  (mem : word -> option byte) (e wlo whi : Z) (G : facts),
  getr regs' 18 = w64 e -> 0 <= e -> e + 32 <= 2 ^ 64 ->
  (forall o, wlo <= o < whi -> writable_at SEGS (mrestrict (w_H W) mem) (e + o)) ->
  region_wf (gtl_ereg wlo whi) = true -> facts_ok (ETL regs' regs) G ->
  st_ok_pi SEGS VAL (ETL regs' regs) (mkSS pc sr_atoms [gtl_ereg wlo whi] None G)
    (restrict (w_H W) (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fq pc regs' regs W mem e wlo whi G H18 He0 He64 HW Hwf HG.
  assert (VB : base_val (ETL regs' regs) (Some 18%nat) = e).
  { cbn [base_val]. rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18. unfold w64.
    apply unsigned_lit_small. lia. }
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_ETL.
  - cbn [regions_wf]. rewrite Hwf. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold gtl_ereg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB.
    split; [lia|]. split; [lia|]. split; [exact HW | apply Forall_nil].
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - exact HG.
Qed.
Lemma gsp_st_fin : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> (i < 8)%nat -> getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  GateModel.gate_model G Sg now = (Mem.upd_bytes B' (32 * i + 24) (Mem.le8 (Z_to_bv 64 now)), 1) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20244)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' B' i
    HC HJ HST HFR H2 H3 H4 H27 H8 Hi H18 HM.
  pose proof HC as (HJc & _ & _ & _ & _ & _ & _ & _ & Hnow & _ & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgd
    & Hgw & Hgapp & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288 in Hbud, Hgd.
  pose proof HST as (HSt1 & HSt2 & HBl & HBa).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp.
  pose proof (gtl_eseat fq 20244 regs' regs W mem' (g + 32 * Z.of_nat i) 24 32 gtl_ffacts H18 ltac:(lia) ltac:(lia)
    ltac:(intros o Ho; apply gsp_writable_of_apresent; apply HSt2; exact (proj2 (Hgw (g + 32 * Z.of_nat i + o) ltac:(lia))))
    eq_refl (gtl_ffacts_ok regs' regs (g + 32 * Z.of_nat i) H18 ltac:(lia) ltac:(Z.div_mod_to_equations; lia))) as HS.
  assert (SHOK : sh_ok SEGS (SOff 21 0) [] (ETL regs' regs) (mrestrict (w_H W) mem')) by constructor.
  assert (HEI : img_env VAL A_LIM (ETL regs' regs)) by (unfold ETL; apply Eimg_env).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  paj_run_to_tok RUNTO HS HJ SHOK (2 ^ 47, 2 ^ 47) 20252.
  - apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (g + 32 * Z.of_nat i)); [reflexivity | | | apply awr_ok_nil].
    + rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. cbn [gtl_ereg YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (Hgw a ltac:(lia))).
  - pmkst HS.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (27%bv : bv 5) R27. prreg HS (10%bv : bv 5) R10.
    assert (E18 : bv_unsigned (ew (ETL regs' regs) 18) = g + 32 * Z.of_nat i).
    { rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18. unfold w64. apply unsigned_lit_small. lia. }
    assert (RO : region_ok SEGS (ETL regs' regs) (mrestrict (w_H W) (ms_mem ms))
      (YP09.mkRegion (Some 18%nat) 0 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 8 0))]))
      by exact (st_ok_region_nth _ _ _ 0 _ HS eq_refl).
    pose proof (field_of_region (ETL regs' regs) _ 18 (g + 32 * Z.of_nat i) _ 0 32 24 32 24 8 (SOff 8 0) now RO E18
      ltac:(left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite (gtl_ewr regs' regs 8%bv 8 eq_refl ltac:(lia)), H8; unfold w64;
            rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as VM.
    destruct (gtl_keep_st W memc mem' (ms_mem ms) (spZ regs) g B' regs (32 * i + 24) (Mem.le8 (Z_to_bv 64 now)))
      as [HST2 HFR2].
    + intros x Hx. apply HFr. intros (r & Hin & Hr). destruct Hin as [<- | []].
      cbn [gtl_ereg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E18 in Hr.
      rewrite Mem.length_le8 in Hx. lia.
    + exact HG.
    + intros j Hj. rewrite Mem.length_le8 in Hj.
      replace (g + Z.of_nat (32 * i + 24) + Z.of_nat j) with (g + 32 * Z.of_nat i + 24 + Z.of_nat j) by lia.
      rewrite (VM j Hj). unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit_small by lia.
      rewrite gtl_nth_le by lia. reflexivity.
    + rewrite Mem.length_le8. lia.
    + lia.
    + lia.
    + lia.
    + unfold spZ in *. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia.
    + lia.
    + exact HST.
    + exact HFR.
    + apply (gsp_epi fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_regs ms) (ms_mem ms) _
        (Mem.upd_bytes B' (32 * i + 24) (Mem.le8 (Z_to_bv 64 now))) HC HJ HST2 HFR2).
      * rewrite R2, (gtl_ewr regs' regs 2%bv 2 eq_refl ltac:(lia)). exact H2.
      * rewrite R3, (gtl_ewr regs' regs 3%bv 3 eq_refl ltac:(lia)). exact H3.
      * rewrite R4, (gtl_ewr regs' regs 4%bv 4 eq_refl ltac:(lia)). exact H4.
      * rewrite R27, (gtl_ewr regs' regs 27%bv 27 eq_refl ltac:(lia)). exact H27.
      * rewrite R10, HM. reflexivity.
      * rewrite HM. reflexivity.
Qed.
Lemma gtl_ra : forall (W : world SEGS) (memc m : word -> option byte) (sp g : Z) (B' : list byte) (p n : Z),
  gsp_state W memc m sp g B' ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 264 ->
  amem_range g 264 -> 0 <= g -> g <= p -> p + n <= g + 264 ->
  0x10007fff8000 <= sp - REAC_DISCO_GATE_SHOULD_PUSH_STK ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p n.
Proof.
  intros W memc m sp g B' p n (HSt1 & _) Hra Happ Hg0 Hp Hpn Hsp x Hx.
  destruct (Hra x ltac:(lia)) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite <- Hsv.
  assert (Heq : shadow_of_addr SHADOW_OFF x = SHADOW_OFF + x / 8) by reflexivity.
  rewrite Heq. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
  apply HSt1; Z.div_mod_to_equations; lia.
Qed.
Lemma gtl_shok : forall (regs' regs : bvmap 5 word) (W : world SEGS) (m : word -> option byte) (e : Z),
  getr regs' 18 = w64 e -> getr regs' 21 = w64 SB -> 0 <= e -> e + 32 <= 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF e 32 ->
  (forall a, e <= a < e + 32 -> a + 1 <= SB \/ SB + 2 ^ 44 <= a) ->
  sh_ok SEGS (SOff 21 0) [mkSHE 18 0 32] (ETL regs' regs) (mrestrict (w_H W) m).
Proof.
  intros regs' regs W m e H18 H21 He0 He64 Hra Hap.
  assert (U18 : U (ETL regs' regs) (SOff 18 0) = e).
  { unfold U. cbn [sv_denot]. rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18. unfold w64.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
  assert (U21 : U (ETL regs' regs) (SOff 21 0) = SB).
  { unfold U. cbn [sv_denot]. rewrite (gtl_ewr regs' regs 21%bv 21 eq_refl ltac:(lia)), H21. unfold w64, SB.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
  apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite U18, U21. split.
  - replace (e + 0) with e by lia. replace (32 - 0) with 32 by lia. exact Hra.
  - intros a Ha. cbn [Z.min Z.max] in Ha. destruct (Hap a ltac:(lia)); lia.
Qed.
Lemma gsp_st_last : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 21 = w64 SB -> (i < 8)%nat -> getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  GateModel.gate_model G Sg now = (Mem.upd_bytes B' (32 * i + 24) (Mem.le8 (Z_to_bv 64 now)), 1) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20224)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' B' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H21 Hi H18 HM.
  pose proof HC as (HJc & _ & _ & _ & _ & _ & _ & _ & Hnow & _ & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgd
    & Hgw & Hgapp & Hgra & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288 in Hbud, Hgd.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R2r. change (bv_modulus 64) with (2 ^ 64) in R2r.
  pose proof (gtl_ra W memc mem' (spZ regs) g B' (g + 32 * Z.of_nat i) 32 HST Hgra Hgapp ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288; lia)) as Hra.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp.
  pose proof (gtl_eseat fq 20224 regs' regs W mem' (g + 32 * Z.of_nat i) 0 0 gtl_efacts H18 ltac:(lia) ltac:(lia)
    ltac:(intros o Ho; lia) eq_refl
    (gtl_efacts_ok regs' regs (g + 32 * Z.of_nat i) H18 H21 ltac:(lia) ltac:(Z.div_mod_to_equations; lia))) as HS.
  pose proof (gtl_shok regs' regs W mem' (g + 32 * Z.of_nat i) H18 H21 ltac:(lia) ltac:(lia) Hra
    ltac:(intros a Ha; unfold SB; lia)) as SHOK.
  assert (HEI : img_env VAL A_LIM (ETL regs' regs)) by (unfold ETL; apply Eimg_env).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20244.
  - apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
  - pmkst HS.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (27%bv : bv 5) R27. prreg HS (8%bv : bv 5) R8. prreg HS (18%bv : bv 5) R18.
    lazymatch type of HFr with frame_of ?E ?rs ?m1 ?m2 =>
      pose proof (gsp_nowin_frame E rs m1 m2 ltac:(vm_compute; reflexivity) HFr) as HE end.
    destruct (gsp_run_keep W mem' (ms_mem ms) memc (spZ regs) g B' regs HE HG HST HFR
      ltac:(lia) ltac:(unfold spZ in *; lia) ltac:(lia) ltac:(lia)
      ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia)) as [HST2 HFR2].
    apply (gsp_st_fin fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_regs ms) (ms_mem ms) _
      B' i HC HJ HST2 HFR2).
    + rewrite R2, (gtl_ewr regs' regs 2%bv 2 eq_refl ltac:(lia)). exact H2.
    + rewrite R3, (gtl_ewr regs' regs 3%bv 3 eq_refl ltac:(lia)). exact H3.
    + rewrite R4, (gtl_ewr regs' regs 4%bv 4 eq_refl ltac:(lia)). exact H4.
    + rewrite R27, (gtl_ewr regs' regs 27%bv 27 eq_refl ltac:(lia)). exact H27.
    + rewrite R8, (gtl_ewr regs' regs 8%bv 8 eq_refl ltac:(lia)). exact H8.
    + exact Hi.
    + rewrite R18, (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)). exact H18.
    + exact HM.
Qed.
Lemma gsp_edge_dk : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 21 = w64 SB -> getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = true ->
  B' = (if CtrlParsed.fb Sg 16 =? 0
        then (if CtrlParsed.fu Sg 8 4 =? 0 then G else Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4))
        else Mem.upd_bytes (if CtrlParsed.fu Sg 8 4 =? 0 then G else Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4))
               (32 * i + 16) [nth 16 Sg (CtrlParsed.zb 0)]) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20196)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' B' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H21 H18 H22 Hf Hed HB.
  pose proof HC as (HJc & _ & _ & _ & _ & _ & _ & _ & Hnow & _ & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgd
    & Hgw & Hgapp & Hgra & _ & _ & _ & HGok & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288 in Hbud, Hgd.
  pose proof HGok as (_ & HGn & _).
  pose proof (proj1 (GateModel.gfind_Some _ _ _ _ _ Hf)) as Hi0.
  assert (Hi : (i < 8)%nat) by lia.
  pose proof (GateModel.gm_edge G Sg now i Hf Hed) as HM.
  pose proof (GateModel.gdk_rng Sg) as Rdk.
  pose proof HST as (HSt1 & HSt2 & HBl & HBa).
  pose proof (gtl_ra W memc mem' (spZ regs) g B' (g + 32 * Z.of_nat i) 32 HST Hgra Hgapp ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(change (REAC_DISCO_GATE_SHOULD_PUSH_STK) with 8288; lia)) as Hra.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp.
  pose proof (gtl_shok regs' regs W mem' (g + 32 * Z.of_nat i) H18 H21 ltac:(lia) ltac:(lia) Hra
    ltac:(intros a Ha; unfold SB; lia)) as SHOK.
  assert (HEI : img_env VAL A_LIM (ETL regs' regs)) by (unfold ETL; apply Eimg_env).
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (PI := PI)).
  assert (BT : branch_taken BC_LT (sv_denot (ETL regs' regs) (SOff 22 0)) (sv_denot (ETL regs' regs) (SLit 0)) =
    (GateModel.gdk Sg <? 0)).
  { cbn [branch_taken sv_denot]. rewrite (gtl_ewr regs' regs 22%bv 22 eq_refl ltac:(lia)), H22, Z.add_0_r.
    unfold w64. rewrite Z_to_bv_bv_unsigned. apply GateModel.lts_lit; lia. }
  assert (E18 : bv_unsigned (ew (ETL regs' regs) 18) = g + 32 * Z.of_nat i).
  { rewrite (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)), H18. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R2r. change (bv_modulus 64) with (2 ^ 64) in R2r.
  destruct (Z.ltb_spec (GateModel.gdk Sg) 0) as [Hdk | Hdk].
  - pose proof (gtl_eseat fq 20196 regs' regs W mem' (g + 32 * Z.of_nat i) 0 0 gtl_efacts H18 ltac:(lia) ltac:(lia)
      ltac:(intros o Ho; lia) eq_refl
      (gtl_efacts_ok regs' regs (g + 32 * Z.of_nat i) H18 H21 ltac:(lia) ltac:(Z.div_mod_to_equations; lia))) as HS.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20224.
      * apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
      * pmkst HS.
        prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
        prreg HS (27%bv : bv 5) R27. prreg HS (8%bv : bv 5) R8. prreg HS (21%bv : bv 5) R21.
        prreg HS (18%bv : bv 5) R18.
        lazymatch type of HFr with frame_of ?E ?rs ?m1 ?m2 =>
          pose proof (gsp_nowin_frame E rs m1 m2 ltac:(vm_compute; reflexivity) HFr) as HE end.
        destruct (gsp_run_keep W mem' (ms_mem ms) memc (spZ regs) g B' regs HE HG HST HFR
          ltac:(lia) ltac:(unfold spZ in *; lia) ltac:(lia) ltac:(lia)
          ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia)) as [HST2 HFR2].
        apply (gsp_st_last fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_regs ms)
          (ms_mem ms) _ B' i HC HJ HST2 HFR2).
        -- rewrite R2, (gtl_ewr regs' regs 2%bv 2 eq_refl ltac:(lia)). exact H2.
        -- rewrite R3, (gtl_ewr regs' regs 3%bv 3 eq_refl ltac:(lia)). exact H3.
        -- rewrite R4, (gtl_ewr regs' regs 4%bv 4 eq_refl ltac:(lia)). exact H4.
        -- rewrite R27, (gtl_ewr regs' regs 27%bv 27 eq_refl ltac:(lia)). exact H27.
        -- rewrite R8, (gtl_ewr regs' regs 8%bv 8 eq_refl ltac:(lia)). exact H8.
        -- rewrite R21, (gtl_ewr regs' regs 21%bv 21 eq_refl ltac:(lia)). exact H21.
        -- exact Hi.
        -- rewrite R18, (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)). exact H18.
        -- rewrite HM, HB; try rewrite (proj2 (Z.ltb_lt _ _) Hdk); reflexivity.
    + rewrite BT in Hc. discriminate Hc.
  - pose proof (gtl_eseat fq 20196 regs' regs W mem' (g + 32 * Z.of_nat i) 12 16 gtl_efacts H18 ltac:(lia) ltac:(lia)
      ltac:(intros o Ho; apply gsp_writable_of_apresent; apply HSt2; exact (proj2 (Hgw (g + 32 * Z.of_nat i + o) ltac:(lia))))
      eq_refl
      (gtl_efacts_ok regs' regs (g + 32 * Z.of_nat i) H18 H21 ltac:(lia) ltac:(Z.div_mod_to_equations; lia))) as HS.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + rewrite BT in Hc. discriminate Hc.
    + paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20224.
      * apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (g + 32 * Z.of_nat i)); [reflexivity | exact E18 | | apply awr_ok_nil].
        intros a Ha. cbn [gtl_ereg YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (Hgw a ltac:(lia))).
      * pmkst HS.
        prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
        prreg HS (27%bv : bv 5) R27. prreg HS (8%bv : bv 5) R8. prreg HS (21%bv : bv 5) R21.
        prreg HS (18%bv : bv 5) R18.
        assert (RO : region_ok SEGS (ETL regs' regs) (mrestrict (w_H W) (ms_mem ms))
          (YP09.mkRegion (Some 18%nat) 0 32 12 16 [YP09.mkChunk 12 (CVal 4 (SOff 22 0))]))
          by exact (st_ok_region_nth _ _ _ 0 _ HS eq_refl).
        pose proof (field_of_region (ETL regs' regs) _ 18 (g + 32 * Z.of_nat i) _ 0 32 12 16 12 4 (SOff 22 0)
          (GateModel.gdk Sg) RO E18 ltac:(left; reflexivity)
          ltac:(cbn [sv_denot]; rewrite (gtl_ewr regs' regs 22%bv 22 eq_refl ltac:(lia)), H22, Z.add_0_r;
                unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
          ltac:(cbn; lia) ltac:(cbn; lia)) as VM.
        destruct (gtl_keep_st W memc mem' (ms_mem ms) (spZ regs) g B' regs (32 * i + 12)
          (Mem.le4 (Z_to_bv 64 (GateModel.gdk Sg)))) as [HST2 HFR2].
        -- intros x Hx. apply HFr. intros (r & Hin & Hr). destruct Hin as [<- | []].
           cbn [gtl_ereg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E18 in Hr.
           rewrite Mem.length_le4 in Hx. lia.
        -- exact HG.
        -- intros j Hj. rewrite Mem.length_le4 in Hj.
           replace (g + Z.of_nat (32 * i + 12) + Z.of_nat j) with (g + 32 * Z.of_nat i + 12 + Z.of_nat j) by lia.
           rewrite (VM j Hj). unfold Mem.le4. rewrite unsigned_lit_small by lia.
           rewrite gtl_nth_le by lia. reflexivity.
        -- rewrite Mem.length_le4. lia.
        -- lia.
        -- lia.
        -- unfold spZ in *. lia.
        -- unfold spZ in *. lia.
        -- unfold spZ in *. lia.
        -- exact HST.
        -- exact HFR.
        -- apply (gsp_st_last fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_regs ms)
             (ms_mem ms) _ (Mem.upd_bytes B' (32 * i + 12) (Mem.le4 (Z_to_bv 64 (GateModel.gdk Sg)))) i HC HJ HST2 HFR2).
           ++ rewrite R2, (gtl_ewr regs' regs 2%bv 2 eq_refl ltac:(lia)). exact H2.
           ++ rewrite R3, (gtl_ewr regs' regs 3%bv 3 eq_refl ltac:(lia)). exact H3.
           ++ rewrite R4, (gtl_ewr regs' regs 4%bv 4 eq_refl ltac:(lia)). exact H4.
           ++ rewrite R27, (gtl_ewr regs' regs 27%bv 27 eq_refl ltac:(lia)). exact H27.
           ++ rewrite R8, (gtl_ewr regs' regs 8%bv 8 eq_refl ltac:(lia)). exact H8.
           ++ rewrite R21, (gtl_ewr regs' regs 21%bv 21 eq_refl ltac:(lia)). exact H21.
           ++ exact Hi.
           ++ rewrite R18, (gtl_ewr regs' regs 18%bv 18 eq_refl ltac:(lia)). exact H18.
           ++ rewrite HM, HB; try rewrite (proj2 (Z.ltb_ge _ _) Hdk); reflexivity.
Qed.
Definition gsp_mextra (B' : list byte) (i : nat) : list word :=
  map (Z_to_bv 64) [CtrlParsed.fu B' (32 * i + 8) 4; CtrlParsed.fu B' (32 * i + 12) 4;
                    CtrlParsed.fb B' (32 * i + 16); CtrlParsed.fu B' (32 * i + 24) 8].
Definition EGSPM (regs : bvmap 5 word) (Sg G B' : list byte) (i : nat) : env :=
  Eimg (Ereg regs (gsp_extra Sg G ++ gsp_mextra B' i)).
Definition gsp_ereg (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 32 wlo whi
    [YP09.mkChunk 8 (CVal 4 (SOff 39 0)); YP09.mkChunk 12 (CVal 4 (SOff 40 0));
     YP09.mkChunk 16 (CVal 1 (SOff 41 0)); YP09.mkChunk 24 (CVal 8 (SOff 42 0))].
Definition gsp_facts3 : facts :=
  mkFacts [ (18%nat, mkAF 0 (2 ^ 47 - 32) 3); (9%nat, mkAF 0 (2 ^ 47 - 24) 2);
            (32%nat, mkAF SB SB 0) ] [] [].
Definition gsp_SH3 : list shent := [ mkSHE 18 0 32; mkSHE 9 0 24 ].
Definition ss_gspm (pc : Z) (upd : list (bv 5 * sv)) (wlo whi : Z) : sstate :=
  mkSS pc (gsp_sr upd) [gsp_ereg wlo whi; gsp_sreg 9] None gsp_facts3.
Lemma regs_ok_EGSPM : forall regs Sg G B' i, regs_ok (EGSPM regs Sg G B' i) sr_atoms regs.
Proof.
  intros. unfold EGSPM. apply (regs_ok_agree 32 (Ereg regs (gsp_extra Sg G ++ gsp_mextra B' i))).
  - split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity.
  - apply regs_ok_Ereg.
Qed.
Lemma gsp_ew_extraM : forall (regs : bvmap 5 word) (Sg G B' : list byte) (i : nat),
  ew (EGSPM regs Sg G B' i) 32 = Z_to_bv 64 SB /\
  ew (EGSPM regs Sg G B' i) 33 = Z_to_bv 64 (CtrlParsed.fu Sg 8 4) /\
  ew (EGSPM regs Sg G B' i) 34 = Z_to_bv 64 (CtrlParsed.fb Sg 12) /\
  ew (EGSPM regs Sg G B' i) 35 = Z_to_bv 64 (CtrlParsed.fb Sg 13) /\
  ew (EGSPM regs Sg G B' i) 36 = Z_to_bv 64 (CtrlParsed.fb Sg 14) /\
  ew (EGSPM regs Sg G B' i) 37 = Z_to_bv 64 (CtrlParsed.fb Sg 16) /\
  ew (EGSPM regs Sg G B' i) 38 = Z_to_bv 64 (CtrlParsed.fu G 256 4) /\
  ew (EGSPM regs Sg G B' i) 39 = Z_to_bv 64 (CtrlParsed.fu B' (32 * i + 8) 4) /\
  ew (EGSPM regs Sg G B' i) 40 = Z_to_bv 64 (CtrlParsed.fu B' (32 * i + 12) 4) /\
  ew (EGSPM regs Sg G B' i) 41 = Z_to_bv 64 (CtrlParsed.fb B' (32 * i + 16)) /\
  ew (EGSPM regs Sg G B' i) 42 = Z_to_bv 64 (CtrlParsed.fu B' (32 * i + 24) 8).
Proof.
  intros regs Sg G B' i.
  repeat split; unfold EGSPM; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity.
Qed.
Lemma gsp_ew_regM : forall (regs : bvmap 5 word) (Sg G B' : list byte) (i : nat) (r : bv 5) (n : nat) (v : Z),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> getr regs r = w64 v ->
  ew (EGSPM regs Sg G B' i) n = Z_to_bv 64 v.
Proof.
  intros regs Sg G B' i r n v Hn Hlt Hv. unfold EGSPM. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ n r Hn). exact Hv.
Qed.
Lemma gsp_ew_getM : forall (regs : bvmap 5 word) (Sg G B' : list byte) (i : nat) (r : bv 5) (n : nat),
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew (EGSPM regs Sg G B' i) n = getr regs r.
Proof.
  intros regs Sg G B' i r n Hn Hlt. unfold EGSPM. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma gsp_sreg_okM : forall (regs : bvmap 5 word) (Sg G B' : list byte) (i : nat) (W : world SEGS)
  (m : word -> option byte) (s : Z),
  ew (EGSPM regs Sg G B' i) 9 = Z_to_bv 64 s -> 0 <= s -> s + 24 <= 2 ^ 64 -> length Sg = 24%nat ->
  garr8 SEGS (mrestrict (w_H W) m) s (map bv_unsigned Sg) ->
  region_ok SEGS (EGSPM regs Sg G B' i) (mrestrict (w_H W) m) (gsp_sreg 9).
Proof.
  intros regs Sg G B' i W m s E9 Hs0 Hs64 HSl HSa.
  destruct (gsp_ew_extraM regs Sg G B' i) as (E32 & E33 & E34 & E35 & E36 & E37 & _).
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8.
  pose proof (GateModel.fb_rng Sg 12) as R12. pose proof (GateModel.fb_rng Sg 13) as R13.
  pose proof (GateModel.fb_rng Sg 14) as R14. pose proof (GateModel.fb_rng Sg 16) as R16.
  assert (VBs : base_val (EGSPM regs Sg G B' i) (Some 9%nat) = s)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  unfold gsp_sreg, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VBs. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ s 8 4 _ (CtrlParsed.fu Sg 8 4));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact (gsp_val_mem _ s Sg 8 4 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 12 1 _ (CtrlParsed.fb Sg 12));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 12 ltac:(lia)). exact (gsp_val_mem _ s Sg 12 1 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 13 1 _ (CtrlParsed.fb Sg 13));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 13 ltac:(lia)). exact (gsp_val_mem _ s Sg 13 1 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 14 1 _ (CtrlParsed.fb Sg 14));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 14 ltac:(lia)). exact (gsp_val_mem _ s Sg 14 1 HSa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ s 16 1 _ (CtrlParsed.fb Sg 16));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 16 ltac:(lia)). exact (gsp_val_mem _ s Sg 16 1 HSa ltac:(lia)).
Qed.
Ltac gsp_zpow := match goal with |- context [2 ^ (8 * Z.of_N ?n)] => let v := eval vm_compute in (2 ^ (8 * Z.of_N n)) in change (2 ^ (8 * Z.of_N n)) with v end; lia.
Lemma gsp_ereg_ok : forall (regs : bvmap 5 word) (Sg G B' : list byte) (i : nat) (W : world SEGS)
  (m : word -> option byte) (g wlo whi : Z),
  ew (EGSPM regs Sg G B' i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i) -> 0 <= g -> g + 264 <= 2 ^ 64 -> (i < 8)%nat ->
  length B' = 264%nat -> garr8 SEGS (mrestrict (w_H W) m) g (map bv_unsigned B') ->
  (forall o, wlo <= o < whi -> writable_at SEGS (mrestrict (w_H W) m) (g + 32 * Z.of_nat i + o)) ->
  region_ok SEGS (EGSPM regs Sg G B' i) (mrestrict (w_H W) m) (gsp_ereg wlo whi).
Proof.
  intros regs Sg G B' i W m g wlo whi E18 Hg0 Hg64 Hi HBl HBa HW.
  destruct (gsp_ew_extraM regs Sg G B' i) as (_ & _ & _ & _ & _ & _ & _ & E39 & E40 & E41 & E42).
  pose proof (GateModel.fu_rng4 B' (32 * i + 8) ltac:(lia)) as R8.
  pose proof (GateModel.fu_rng4 B' (32 * i + 12) ltac:(lia)) as R12.
  pose proof (GateModel.fb_rng B' (32 * i + 16)) as R16.
  pose proof (GateModel.fu_rng8 B' (32 * i + 24) ltac:(lia)) as R24.
  assert (VBe : base_val (EGSPM regs Sg G B' i) (Some 18%nat) = g + 32 * Z.of_nat i)
    by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
  unfold gsp_ereg, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VBe. split; [lia|]. split; [lia|]. split; [exact HW|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ _ 8 4 _ (CtrlParsed.fu B' (32 * i + 8) 4));
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | gsp_zpow | cbn; lia |].
    replace (g + 32 * Z.of_nat i + 8) with (g + Z.of_nat (32 * i + 8)) by lia.
    exact (gsp_val_mem _ g B' (32 * i + 8) 4 HBa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ _ 12 4 _ (CtrlParsed.fu B' (32 * i + 12) 4));
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | gsp_zpow | cbn; lia |].
    replace (g + 32 * Z.of_nat i + 12) with (g + Z.of_nat (32 * i + 12)) by lia.
    exact (gsp_val_mem _ g B' (32 * i + 12) 4 HBa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ _ 16 1 _ (CtrlParsed.fb B' (32 * i + 16)));
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | gsp_zpow | cbn; lia |].
    replace (g + 32 * Z.of_nat i + 16) with (g + Z.of_nat (32 * i + 16)) by lia.
    rewrite <- (gsp_fu1 B' (32 * i + 16) ltac:(lia)).
    exact (gsp_val_mem _ g B' (32 * i + 16) 1 HBa ltac:(lia)).
  - apply (chunk_ok_val SEGS _ _ _ 24 8 _ (CtrlParsed.fu B' (32 * i + 24) 8));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | gsp_zpow | cbn; lia |].
    replace (g + 32 * Z.of_nat i + 24) with (g + Z.of_nat (32 * i + 24)) by lia.
    exact (gsp_val_mem _ g B' (32 * i + 24) 8 HBa ltac:(lia)).
Qed.
Lemma gsp_ra_sub : forall (rd : Z -> option Z) (b p n q m : Z),
  range_addressable rd b p n -> p <= q -> q + m <= p + n -> range_addressable rd b q m.
Proof. intros rd b p n q m H H1 H2 x Hx. apply H. lia. Qed.
Lemma gsp_mseat : forall (fq : YK11.FPState) (pc : Z) (upd : list (bv 5 * sv)) (wlo whi : Z) (regs : bvmap 5 word)
  (W : world SEGS) (mem : word -> option byte) (g s : Z) (i : nat) (G Sg B' : list byte),
  NoDup (map fst upd) ->
  Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs (fst p) = sv_denot (EGSPM regs Sg G B' i) (snd p)) upd ->
  getr regs 18 = w64 (g + 32 * Z.of_nat i) -> getr regs 9 = w64 s -> (i < 8)%nat ->
  0 < g -> g mod 8 = 0 -> amem_range g 264 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF g 264 ->
  0 < s -> s mod 4 = 0 -> amem_range s 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 24 ->
  (g + 264 <= s \/ s + 24 <= g) ->
  0 <= wlo <= whi -> whi <= 32 ->
  (forall o, wlo <= o < whi -> apresent (w_H W) mem (g + 32 * Z.of_nat i + o)) ->
  length B' = 264%nat -> garr8 SEGS (mrestrict (w_H W) mem) g (map bv_unsigned B') ->
  length Sg = 24%nat -> garr8 SEGS (mrestrict (w_H W) mem) s (map bv_unsigned Sg) ->
  st_ok_pi SEGS VAL (EGSPM regs Sg G B' i) (ss_gspm pc upd wlo whi)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS GSP_SBx gsp_SH3 (EGSPM regs Sg G B' i) (mrestrict (w_H W) mem).
Proof.
  intros fq pc upd wlo whi regs W mem g s i G Sg B' HND HUPD H18 H9 Hi Hg0 Hg8 Hgapp Hgra Hs0 Hs4 Hsapp Hsra Hds
    Hw1 Hw2 HWp HBl HBa HSl HSa.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hgapp, Hsapp. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
  pose proof (gsp_ew_regM regs Sg G B' i 18%bv 18 _ eq_refl ltac:(lia) H18) as E18.
  pose proof (gsp_ew_regM regs Sg G B' i 9%bv 9 s eq_refl ltac:(lia) H9) as E9.
  destruct (gsp_ew_extraM regs Sg G B' i) as (E32 & _).
  rewrite restrict_mkst_fx.
  assert (VBe : base_val (EGSPM regs Sg G B' i) (Some 18%nat) = g + 32 * Z.of_nat i)
    by (cbn [base_val]; rewrite E18; apply unsigned_lit_small; lia).
  assert (VBs : base_val (EGSPM regs Sg G B' i) (Some 9%nat) = s)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gspm. apply pa_entry_st_ok_full.
    + unfold gsp_sr. apply (regs_ok_sets _ sr_atoms regs regs upd);
        [apply regs_ok_EGSPM | exact HND | intros r _; reflexivity | exact HUPD].
    + unfold regions_wf, region_wf, gsp_ereg, gsp_sreg.
      cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      destruct (Z.leb_spec whi wlo), (Z.leb_spec 0 wlo), (Z.leb_spec whi 32); try lia; vm_compute; reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (gsp_ereg_ok regs Sg G B' i W mem g wlo whi E18 ltac:(lia) ltac:(lia) Hi HBl HBa).
        intros o Ho. apply gsp_writable_of_apresent. apply HWp. exact Ho.
      * exact (gsp_sreg_okM regs Sg G B' i W mem s E9 ltac:(lia) ltac:(lia) HSl HSa).
    + apply pairwise_disjoint_of_extents. unfold gsp_ereg, gsp_sreg, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VBe, VBs.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; exact I]. cbn [gsp_facts3 f_atoms atoms_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18, E9, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia | reflexivity | (Z.div_mod_to_equations; lia)].
  - assert (HUB : U (EGSPM regs Sg G B' i) GSP_SBx = SHADOW_OFF)
      by (unfold GSP_SBx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
    assert (HU18 : U (EGSPM regs Sg G B' i) (SOff 18 0) = g + 32 * Z.of_nat i).
    { unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
    assert (HU9 : U (EGSPM regs Sg G B' i) (SOff 9 0) = s).
    { unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
    unfold gsp_SH3, sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU18, HUB. split.
      * apply (gsp_ra_sub _ _ g 264); [exact Hgra | lia | lia].
      * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HU9, HUB. split.
      * replace (s + 0) with s by lia. replace (24 - 0) with 24 by lia. exact Hsra.
      * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
Lemma gsp_val_mem_move : forall (m m' : word -> option byte) (p : Z) (n : nat) (v : Z),
  val_mem SEGS m p n v -> (forall k, (k < n)%nat -> mbyte SEGS m' (p + Z.of_nat k) = mbyte SEGS m (p + Z.of_nat k)) ->
  val_mem SEGS m' p n v.
Proof. intros m m' p n v H HM k Hk. rewrite HM by exact Hk. apply H. exact Hk. Qed.
Lemma gsp_ra_state : forall (W : world SEGS) (memc mem : word -> option byte) (sp g : Z) (B' : list byte) (p n : Z),
  gsp_state W memc mem sp g B' ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p n ->
  0 <= p -> p + n <= kHighMemEnd -> kHighMemBeg <= sp - REAC_DISCO_GATE_SHOULD_PUSH_STK -> amem_range g 264 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n.
Proof.
  intros W memc mem sp g B' p n (Hk & _) HR Hp0 Hpn Hsp Hg x Hx.
  destruct (HR x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
  rewrite <- Hv. unfold shadow_of_addr.
  assert (Hd1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd2 : x / 8 < 17592186044416)
    by (apply Z.div_lt_upper_bound; [lia | unfold kHighMemEnd in *; lia]).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *.
  apply Hk; lia.
Qed.
Lemma gsp_garr8_state : forall (W : world SEGS) (memc mem : word -> option byte) (sp g : Z) (B' : list byte)
  (p : Z) (l : list Z),
  gsp_state W memc mem sp g B' -> garr8 SEGS (mrestrict (w_H W) memc) p l ->
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (sp <= p \/ p + Z.of_nat (length l) <= sp - REAC_DISCO_GATE_SHOULD_PUSH_STK) ->
  (g + 264 <= p \/ p + Z.of_nat (length l) <= g) ->
  garr8 SEGS (mrestrict (w_H W) mem) p l.
Proof.
  intros W memc mem sp g B' p l (Hk & _) HG Hp0 Hp64 Hd1 Hd2.
  apply (garr8_frame SEGS _ _ p l HG). intros a Ha. apply gsp_mbyte_of_aview. apply Hk; lia.
Qed.
Lemma gsp_mbyte_frame : forall (W : world SEGS) (E : env) (rs : smem) (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof. intros W E rs m m' Zs HF HW a Ha HZ. apply gsp_mbyte_of_aview. exact (kept_of_frame E rs (w_H W) m m' Zs HF HW a Ha HZ). Qed.
Lemma gsp_frame_keep : forall (W : world SEGS) (mem mem' : word -> option byte) (sp : Z) (regs : bvmap 5 word),
  gsp_frame W mem sp regs ->
  (forall a, sp - 96 <= a < sp -> mbyte SEGS (mrestrict (w_H W) mem') a = mbyte SEGS (mrestrict (w_H W) mem) a) ->
  gsp_frame W mem' sp regs.
Proof.
  intros W mem mem' sp regs (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) HM.
  unfold gsp_frame.
  repeat split; (eapply gsp_val_mem_move; [eassumption | intros k Hk; apply HM; lia]).
Qed.
Lemma gsp_sext32 : forall x, 0 <= x < 2 ^ 32 ->
  sext 64 (bv_extract 0 32 (Z_to_bv 64 x)) = Z_to_bv 64 (CtrlParsed.s32 x).
Proof.
  intros x Hx. rewrite Mem.sext_small, Mem.signed_of_extract by lia. f_equal.
  rewrite unsigned_lit_small by lia. apply GateModel.s32_swrap. exact Hx.
Qed.
Lemma gsp_br_eq : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. apply GateModel.eqb_lit; assumption. Qed.
Lemma gsp_br_ne : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite GateModel.eqb_lit by assumption. reflexivity. Qed.
Lemma gsp_br_lt : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. apply GateModel.lts_lit; assumption. Qed.
Lemma gsp_br_ge : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite GateModel.lts_lit by assumption. reflexivity. Qed.
Lemma gsp_br_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. apply GateModel.ltu_lit; assumption. Qed.
Lemma gsp_br_geu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite GateModel.ltu_lit by assumption. reflexivity. Qed.
Ltac gsp_win := let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; lia|]); destruct Hin.
Ltac gsp_awr_ro :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac gsp_nrm H :=
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in H;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H.
Ltac gsp_rg HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let R := fresh "R" in prreg HS r R; rewrite R; clear R end;
  repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?gsp_sext32 by (apply GateModel.fu_rng4; lia);
  first [assumption | reflexivity | congruence].
Lemma gsp_zext8 : forall x, 0 <= x < 256 -> zext 64 (bv_extract 0 8 (Z_to_bv 64 x)) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite Mem.zext_small, Mem.extract_low_mod by lia. f_equal.
  rewrite unsigned_lit_small by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma gsp_nth_upd : forall (cs bs : list byte) (k j : nat) (d : byte),
  (k + length bs <= length cs)%nat -> (j < length cs)%nat ->
  nth j (Mem.upd_bytes cs k bs) d = if ((k <=? j) && (j <? k + length bs))%nat then nth (j - k) bs d else nth j cs d.
Proof.
  intros cs bs k j d H Hj.
  pose proof (GateModel.nth_error_upd cs k bs H j) as E.
  destruct ((k <=? j) && (j <? k + length bs))%nat eqn:C.
  - apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2.
    apply nth_error_nth. rewrite E. apply nth_error_nth'. lia.
  - apply nth_error_nth. rewrite E. apply nth_error_nth'. exact Hj.
Qed.
Lemma gsp_state_upd : forall (W : world SEGS) (memc mem mem' : word -> option byte) (sp g : Z) (B' X : list byte) (k : nat),
  gsp_state W memc mem sp g B' -> 0 <= g -> g + 264 <= 2 ^ 64 -> (k + length X <= 264)%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + Z.of_nat k <= a < g + Z.of_nat k + Z.of_nat (length X)) ->
     mbyte SEGS (mrestrict (w_H W) mem') a = mbyte SEGS (mrestrict (w_H W) mem) a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  garr8 SEGS (mrestrict (w_H W) mem') (g + Z.of_nat k) (map bv_unsigned X) ->
  gsp_state W memc mem' sp g (Mem.upd_bytes B' k X).
Proof.
  intros W memc mem mem' sp g B' X k (Hk & Hp & HL & HG) Hg0 Hg64 HkX HM Hgr HX.
  split; [|split; [|split]].
  - intros a Ha N1 N2. rewrite <- (Hk a Ha N1 N2). unfold aview. rewrite (HM a Ha) by lia. reflexivity.
  - intros a Ha. apply (gsp_apresent_grow W mem mem' a Hgr). apply Hp. exact Ha.
  - rewrite GateModel.length_upd by lia. exact HL.
  - intros j Hj. rewrite length_map, GateModel.length_upd in Hj by lia.
    rewrite gsp_nth_map, (gsp_nth_upd B' X k j) by lia.
    destruct ((k <=? j) && (j <? k + length X))%nat eqn:C.
    + apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2.
      destruct (HX (j - k)%nat ltac:(rewrite length_map; lia)) as [HV HR].
      rewrite gsp_nth_map in HV, HR.
      replace (g + Z.of_nat k + Z.of_nat (j - k)) with (g + Z.of_nat j) in HV by lia.
      split; [exact HV | exact HR].
    + destruct (HG j ltac:(rewrite length_map; lia)) as [HV HR].
      rewrite gsp_nth_map in HV, HR. split; [|exact HR].
      eapply gsp_val_mem_move; [exact HV|]. intros q Hq. apply HM; [lia|].
      apply andb_false_iff in C. destruct C as [C|C]; [apply Nat.leb_gt in C | apply Nat.ltb_ge in C]; lia.
Qed.
Lemma gsp_garr8_chunk : forall (E : env) (m : word -> option byte) (base off : Z) (n : N) (v : sv) (X : list byte),
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n v)) -> length X = N.to_nat n ->
  (forall j, (j < N.to_nat n)%nat -> byte_of_word (sv_denot E v) (Z.of_nat j) = nth j X (CtrlParsed.zb 0)) ->
  garr8 SEGS m (base + off) (map bv_unsigned X).
Proof.
  intros E m base off n v X HC HL HB j Hj. rewrite length_map, HL in Hj.
  destruct (HC (Z.of_nat j) ltac:(unfold c_len; cbn [YP09.c_val cv_len]; lia)) as (b & Hb & Hm).
  cbn [cbyte YP09.c_val c_off] in Hb, Hm. injection Hb as Hb. rewrite HB in Hb by exact Hj.
  rewrite gsp_nth_map. pose proof (GateModel.byte_rng (nth j X (CtrlParsed.zb 0))) as Hr.
  split; [|exact Hr].
  intros q Hq. replace q with 0%nat by lia. rewrite Z.add_0_r. rewrite Hm, <- Hb.
  f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, Z.mod_mod by lia. rewrite Z.mod_small by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma gsp_bow_fu : forall (L : list byte) (k n j : nat), (k + n <= length L)%nat -> (n <= 8)%nat -> (j < n)%nat ->
  byte_of_word (Z_to_bv 64 (CtrlParsed.fu L k n)) (Z.of_nat j) = nth j (CtrlParsed.fld L k n) (CtrlParsed.zb 0).
Proof.
  intros L k n j Hk Hn Hj.
  pose proof (gsp_le_byte_fu L k n j Hk Hj) as HB. unfold YO0f.le_byte in HB.
  assert (Hp : 2 ^ (8 * Z.of_nat n) = 256 ^ Z.of_nat n) by (rewrite (Z.pow_mul_r 2 8 (Z.of_nat n)) by lia; reflexivity).
  assert (Hr : 0 <= CtrlParsed.fu L k n < 2 ^ (8 * Z.of_nat n)).
  { unfold CtrlParsed.fu. pose proof (GateModel.ble_range (CtrlParsed.fld L k n)) as R.
    rewrite GateModel.length_fld in R by lia. rewrite Hp. exact R. }
  assert (H64 : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (CtrlParsed.fu L k n)) in HB by lia.
  unfold byte_of_word. rewrite unsigned_lit_small by lia.
  rewrite (gsp_nth_fld L k n j Hk Hj).
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite HB. reflexivity.
Qed.
Lemma gsp_shr_mod : forall x y i, 0 <= i <= 3 -> x mod 2 ^ 32 = y mod 2 ^ 32 ->
  Z.shiftr x (8 * i) mod 256 = Z.shiftr y (8 * i) mod 256.
Proof.
  intros x y i Hi Hxy. change 256 with (2 ^ 8).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z.ltb_spec n 8).
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite <- (Z.mod_pow2_bits_low x 32 (n + 8 * i)) by lia.
    rewrite <- (Z.mod_pow2_bits_low y 32 (n + 8 * i)) by lia.
    rewrite Hxy. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma gsp_bow_low32 : forall (w1 w2 : word) (i : Z), 0 <= i <= 3 ->
  bv_unsigned w1 mod 2 ^ 32 = bv_unsigned w2 mod 2 ^ 32 -> byte_of_word w1 i = byte_of_word w2 i.
Proof.
  intros w1 w2 i Hi H. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply gsp_shr_mod; assumption.
Qed.
Lemma gsp_s32_mod : forall x, 0 <= x < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (CtrlParsed.s32 x)) mod 2 ^ 32 = bv_unsigned (Z_to_bv 64 x) mod 2 ^ 32.
Proof.
  intros x Hx. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  unfold CtrlParsed.s32. destruct (Z.ltb_spec x (2 ^ 31)); [reflexivity|].
  Z.div_mod_to_equations. lia.
Qed.
Lemma gsp_edge_tail : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = true ->
  B' = (if CtrlParsed.fu Sg 8 4 =? 0 then G else Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20144)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' B' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf Hed HB.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g B' g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g B' s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g B' s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  destruct (gsp_mseat fq 20144 [(21%bv, SOff 32 0)] 0 0 regs' W mem' g s i G Sg B'
    ltac:(apply gsp_nodup1)
    ltac:(apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite H21; cbn [sv_denot]; rewrite (proj1 (gsp_ew_extraM regs' Sg G B' i)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G B' i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G B' i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G B' i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G B' i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G B' i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G B' i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G B' i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G B' i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G B' i 21%bv 21 eq_refl ltac:(lia)) as Er21.
  pose proof (gsp_ew_getM regs' Sg G B' i 22%bv 22 eq_refl ltac:(lia)) as Er22.
  pose proof (gsp_ew_getM regs' Sg G B' i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  destruct (gsp_ew_extraM regs' Sg G B' i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  remember (EGSPM regs' Sg G B' i) as E eqn:HE. clear HE.
  pose proof (GateModel.fb_rng Sg 16) as R16.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
  gkeep HST HFR.
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - gsp_nrm Hc. rewrite Ex37, gsp_zext8 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20196; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_edge_dk fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ _ i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hf | exact Hed | rewrite Hc; exact HB].
  - gsp_nrm Hc. rewrite Ex37, gsp_zext8 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20172; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (11%bv : bv 5) R11.
    prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (21%bv : bv 5) R21.
    prreg HS (22%bv : bv 5) R22. prreg HS (27%bv : bv 5) R27.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into ms1 end.
    clear HS SHOK.
    remember (ms_regs ms1) as rg1 eqn:Erg1. remember (ms_mem ms1) as m1 eqn:Em1.
    clear Erg1 Em1. try clear ms1.
    rewrite Er18, H18 in R18. rewrite Er9, H9 in R9. rewrite Ex32 in R21. rewrite Ex37, gsp_zext8 in R11 by lia.
    assert (Hgra1 : range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF g 264)
      by (apply (gsp_ra_state W memc m1 (spZ regs) g B' g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
    assert (Hsra1 : range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF s 24)
      by (apply (gsp_ra_state W memc m1 (spZ regs) g B' s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
    assert (HSa1 : garr8 SEGS (mrestrict (w_H W) m1) s (map bv_unsigned Sg))
      by (apply (gsp_garr8_state W memc m1 (spZ regs) g B' s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
    pose proof HST as (Hkeep1 & Hpres1 & HBl1 & HBa1).
    destruct (gsp_mseat fq 20172 [(21%bv, SOff 32 0)] 16 17 rg1 W m1 g s i G Sg B'
      ltac:(apply gsp_nodup1)
      ltac:(apply Forall_cons; [|apply Forall_nil];
            cbn [fst snd]; split; [reflexivity|];
            rewrite R21; cbn [sv_denot]; rewrite (proj1 (gsp_ew_extraM rg1 Sg G B' i)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      R18 R9 Hi Hg0 Hg8 Hgapp Hgra1 Hs0 Hs4 Hsapp Hsra1 Hds ltac:(lia) ltac:(lia)
      ltac:(intros o Ho; apply Hpres1; exact (proj2 (Hgw (g + 32 * Z.of_nat i + o) ltac:(lia))))
      HBl1 HBa1 HSl HSa1) as [HS SHOK].
    assert (HEI2 : img_env VAL A_LIM (EGSPM rg1 Sg G B' i)) by (unfold EGSPM; apply Eimg_env).
    pose proof (gsp_ew_getM rg1 Sg G B' i 2%bv 2 eq_refl ltac:(lia)) as Fr2.
    pose proof (gsp_ew_getM rg1 Sg G B' i 3%bv 3 eq_refl ltac:(lia)) as Fr3.
    pose proof (gsp_ew_getM rg1 Sg G B' i 4%bv 4 eq_refl ltac:(lia)) as Fr4.
    pose proof (gsp_ew_getM rg1 Sg G B' i 8%bv 8 eq_refl ltac:(lia)) as Fr8.
    pose proof (gsp_ew_getM rg1 Sg G B' i 11%bv 11 eq_refl ltac:(lia)) as Fr11.
    pose proof (gsp_ew_getM rg1 Sg G B' i 18%bv 18 eq_refl ltac:(lia)) as Fr18.
    pose proof (gsp_ew_getM rg1 Sg G B' i 22%bv 22 eq_refl ltac:(lia)) as Fr22.
    pose proof (gsp_ew_getM rg1 Sg G B' i 27%bv 27 eq_refl ltac:(lia)) as Fr27.
    destruct (gsp_ew_extraM rg1 Sg G B' i) as (Fx32 & _).
    remember (EGSPM rg1 Sg G B' i) as E2 eqn:HE2. clear HE2.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20196.
    + lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
      eapply awr_ok_cons_gen with (n := 18%nat) (b := g + 32 * Z.of_nat i).
      * reflexivity.
      * rewrite Fr18, R18. unfold w64. apply unsigned_lit_small. lia.
      * intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. exact (proj1 (Hgw a ltac:(lia))).
      * apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
    + pmkst HS.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into ms2 end.
      lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
        let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
        lazymatch r with Some ?rr => pose proof (st_ok_pi_region_nth _ _ _ 0 rr HS ltac:(vm_compute; reflexivity)) as HR0 end end.
      cbn [ms_mem restrict] in HR0.
      destruct HR0 as (_ & _ & _ & Hcs).
      lazymatch type of Hcs with context [YP09.mkChunk 16 (CVal 1 ?v)] =>
        pose proof (proj1 (Forall_forall _ _) Hcs (YP09.mkChunk 16 (CVal 1 v)) ltac:(cbn; repeat (first [left; reflexivity | right]))) as HCk end.
      cbn [YP09.r_base base_val] in HCk. rewrite Fr18, R18 in HCk. unfold w64 in HCk. rewrite unsigned_lit_small in HCk by lia.
      pose proof (gsp_garr8_chunk _ _ _ 16 1 _ [nth 16 Sg (CtrlParsed.zb 0)] HCk eq_refl) as HX.
      assert (HX' : garr8 SEGS (mrestrict (w_H W) (ms_mem ms2)) (g + Z.of_nat (32 * i + 16)) (map bv_unsigned [nth 16 Sg (CtrlParsed.zb 0)])).
      { replace (g + Z.of_nat (32 * i + 16)) with (g + 32 * Z.of_nat i + 16) by lia. apply HX.
        intros j Hj. change (N.to_nat 1) with 1%nat in Hj. replace j with 0%nat by lia.
        cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, Fr11, R11.
        rewrite <- (gsp_fu1 Sg 16) by lia. rewrite (gsp_bow_fu Sg 16 1 0) by lia.
        rewrite GateModel.fld1 by lia. reflexivity. }
      assert (HMF : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat i + 16 <= a < g + 32 * Z.of_nat i + 17) ->
        mbyte SEGS (mrestrict (w_H W) (ms_mem ms2)) a = mbyte SEGS (mrestrict (w_H W) m1) a).
      { apply (gsp_mbyte_frame W E2 _ m1 (ms_mem ms2) (fun a => g + 32 * Z.of_nat i + 16 <= a < g + 32 * Z.of_nat i + 17) HFr).
        intros b wlo whi a Hin Ha. cbv beta. vm_compute in Hin.
        repeat (destruct Hin as [Hin|Hin];
          [injection Hin as <- <- <-; cbn [base_val] in Ha;
           first [lia | rewrite Fr18, R18 in Ha; unfold w64 in Ha; rewrite unsigned_lit_small in Ha by lia; lia]|]);
        destruct Hin. }
      assert (HST2 : gsp_state W memc (ms_mem ms2) (spZ regs) g (Mem.upd_bytes B' (32 * i + 16) [nth 16 Sg (CtrlParsed.zb 0)])).
      { apply (gsp_state_upd W memc m1 (ms_mem ms2) (spZ regs) g B' [nth 16 Sg (CtrlParsed.zb 0)] (32 * i + 16) HST Hg0' Hg64
          ltac:(cbn [length]; lia)).
        - intros a Ha Hn. apply HMF; [exact Ha|]. cbn [length] in Hn. lia.
        - exact HG.
        - exact HX'. }
      assert (HFR2 : gsp_frame W (ms_mem ms2) (spZ regs) regs).
      { apply (gsp_frame_keep W m1 (ms_mem ms2) (spZ regs) regs HFR). intros a Ha. apply HMF; lia. }
      eapply (gsp_edge_dk fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ _ i HC HJ HST2 HFR2);
        try (gsp_rg HS; fail); [exact Hf | exact Hed | rewrite Hc, HB; reflexivity].
Qed.
Lemma gsp_edge_w : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  getr regs' 11 = w64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) ->
  GateModel.gedge G Sg i = true ->
  (CtrlParsed.fu Sg 8 4 =? 0) = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20120)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf H11 Hed Hfu.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10c & H11c & H12c & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g G s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  destruct (gsp_mseat fq 20120 [(21%bv, SOff 32 0); (11%bv, SExt true 32 (SOff 33 0))] 8 12 regs' W mem' g s i G Sg G
    ltac:(apply gsp_nodup2; vm_compute; lia)
    ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; (split; [reflexivity|]);
          [rewrite H21; cbn [sv_denot]; rewrite (proj1 (gsp_ew_extraM regs' Sg G G i)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          |rewrite H11; cbn [sv_denot]; rewrite (proj1 (proj2 (gsp_ew_extraM regs' Sg G G i))), Z.add_0_r, Z_to_bv_bv_unsigned;
           rewrite gsp_sext32 by (apply GateModel.fu_rng4; lia); reflexivity])
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia)
    ltac:(intros o Ho; apply Hpres; apply (proj2 (Hgw (g + 32 * Z.of_nat i + o) ltac:(lia))))
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G G i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G G i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G G i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G G i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G G i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G G i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G G i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G G i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G G i 22%bv 22 eq_refl ltac:(lia)) as Er22.
  pose proof (gsp_ew_getM regs' Sg G G i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  destruct (gsp_ew_extraM regs' Sg G G i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  assert (VBe : base_val (EGSPM regs' Sg G G i) (Some 18%nat) = g + 32 * Z.of_nat i)
    by (cbn [base_val]; rewrite Er18, H18; apply unsigned_lit_small; lia).
  remember (EGSPM regs' Sg G G i) as E eqn:HE. clear HE.
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8. pose proof (GateModel.s32_range _ R8) as R8'.
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20144.
  { eapply awr_ok_cons_gen with (n := 18%nat) (b := g + 32 * Z.of_nat i);
      [reflexivity | rewrite Er18, H18; apply unsigned_lit_small; lia
      | intros a Ha; try unfold gsp_ereg in Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; exact (proj1 (Hgw a ltac:(lia))) |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (HWin : forall b wlo whi a,
    In (b, wlo, whi) (windows (ss_mem (ss_gspm 20120 [(21%bv, SOff 32 0); (11%bv, SExt true 32 (SOff 33 0))] 8 12))) ->
    base_val E b + wlo <= a < base_val E b + whi -> g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 12).
  { intros b wlo whi a Hin Ha. vm_compute in Hin.
    destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <- <-; rewrite ?VBe in Ha; lia. }
  pose proof (gsp_mbyte_frame W E _ mem' (ms_mem ms)
    (fun a => g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 12) HFr HWin) as HM.
  cbv beta in HM.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
  cbn [ms_mem restrict] in HR0.
  unfold region_ok in HR0.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in HR0.
  destruct HR0 as (_ & _ & _ & HC0). apply Forall_inv in HC0.
  assert (HX : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (g + Z.of_nat (32 * i + 8))
    (map bv_unsigned (CtrlParsed.fld Sg 8 4))).
  { replace (g + Z.of_nat (32 * i + 8)) with (base_val E (Some 18%nat) + 8) by (rewrite VBe; lia).
    apply (gsp_garr8_chunk E _ _ 8 4 (SExt true 32 (SOff 33 0)) _ HC0).
    - rewrite GateModel.length_fld by lia. reflexivity.
    - intros j Hj. change (N.to_nat 4) with 4%nat in Hj.
      cbn [sv_denot]. rewrite Ex33, Z.add_0_r, Z_to_bv_bv_unsigned, gsp_sext32 by lia.
      rewrite (gsp_bow_low32 (Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4))) (Z_to_bv 64 (CtrlParsed.fu Sg 8 4))
        (Z.of_nat j)) by (try lia; apply gsp_s32_mod; lia).
      apply gsp_bow_fu; lia. }
  assert (HST' : gsp_state W memc (ms_mem ms) (spZ regs) g (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4))).
  { apply (gsp_state_upd W memc mem' (ms_mem ms) (spZ regs) g G (CtrlParsed.fld Sg 8 4) (32 * i + 8) HST Hg0' Hg64).
    - rewrite GateModel.length_fld by lia. lia.
    - intros a Ha Hn. apply HM; [exact Ha|]. rewrite GateModel.length_fld in Hn by lia. lia.
    - exact HG.
    - exact HX. }
  assert (HFR' : gsp_frame W (ms_mem ms) (spZ regs) regs).
  { apply (gsp_frame_keep W mem' (ms_mem ms) (spZ regs) regs HFR). intros a Ha. apply HM; lia. }
  clear HST HFR HFr HG HM.
  pmkst HS.
  eapply (gsp_edge_tail fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _
    (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) i HC HJ HST' HFR');
    try (gsp_rg HS; fail); [exact Hf | exact Hed | rewrite Hfu; reflexivity].
Qed.
Lemma gsp_den_sub : forall (E : env) (na nb : nat) (a b : Z),
  ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= b <= a -> a < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff na 0) (SMd M_MUL (SOff nb 0) (SLit (-1)))) = Z_to_bv 64 (a - b).
Proof.
  intros E na nb a b Ha Hb Rb Ra. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
  rewrite (U_atom E na a Ha), (U_atom E nb b Hb) by lia.
  change (zcanon (-1)) with (2 ^ 64 - 1).
  unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
  replace (a + b * (2 ^ 64 - 1)) with ((a - b) + b * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma gsp_refresh : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20064)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf Hed.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g G s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  destruct (gsp_mseat fq 20064 [(21%bv, SOff 32 0)] 0 0 regs' W mem' g s i G Sg G
    ltac:(apply gsp_nodup1)
    ltac:(apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite H21; cbn [sv_denot]; rewrite (proj1 (gsp_ew_extraM regs' Sg G G i)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G G i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G G i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G G i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G G i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G G i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G G i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G G i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G G i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G G i 22%bv 22 eq_refl ltac:(lia)) as Er22.
  pose proof (gsp_ew_getM regs' Sg G G i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  destruct (gsp_ew_extraM regs' Sg G G i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  remember (EGSPM regs' Sg G G i) as E eqn:HE. clear HE.
  pose proof (GateModel.fu_rng8 G (32 * i + 24) ltac:(lia)) as RL.
  assert (En : ew E 8 = Z_to_bv 64 now) by (rewrite Er8, H8; reflexivity).
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
  gkeep HST HFR.
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - gsp_nrm Hc. rewrite En, Ex42, gsp_br_ltu in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20244; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_st_fin fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ G i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hi | apply (GateModel.gm_refresh G Sg now i Hf Hed); rewrite Hc; reflexivity].
  - gsp_nrm Hc. rewrite En, Ex42, gsp_br_ltu in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hc0.
    paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
    gkeep HST HFR.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + rewrite (gsp_den_sub E 8 42 now _ En Ex42) in Hc by lia. gsp_nrm Hc. rewrite gsp_br_geu in Hc by lia.
      apply negb_true_iff, Z.ltb_ge in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20244; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_st_fin fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ G i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hi | apply (GateModel.gm_refresh G Sg now i Hf Hed)].
      apply orb_true_iff; right; apply Z.leb_le; unfold GateModel.RF; lia.
    + rewrite (gsp_den_sub E 8 42 now _ En Ex42) in Hc by lia. gsp_nrm Hc. rewrite gsp_br_geu in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20108; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_ret0 fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ G HC HJ HST HFR);
        try (gsp_rg HS; fail).
      apply (GateModel.gm_keep G Sg now i Hf Hed).
      apply orb_false_iff; split; [apply Z.ltb_ge; lia | apply Z.leb_gt; unfold GateModel.RF; lia].
Qed.
Lemma gsp_edge_head : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  getr regs' 11 = w64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) ->
  GateModel.gedge G Sg i = true ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20116)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf H11 Hed.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & Hc11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g G s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8. pose proof (GateModel.s32_range _ R8) as R8'.
  destruct (gsp_mseat fq 20116 [(21%bv, SOff 32 0); (11%bv, SExt true 32 (SOff 33 0))] 0 0 regs' W mem' g s i G Sg G
    ltac:(apply gsp_nodup2; intros Hx; vm_compute in Hx; discriminate Hx)
    ltac:(destruct (gsp_ew_extraM regs' Sg G G i) as (X32 & X33 & _);
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; (split; [reflexivity|]);
          [rewrite H21; cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          |rewrite H11; cbn [sv_denot]; rewrite X33, Z.add_0_r, Z_to_bv_bv_unsigned, gsp_sext32 by exact R8; reflexivity])
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G G i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G G i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G G i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G G i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G G i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G G i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G G i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G G i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G G i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  pose proof (gsp_ew_regM regs' Sg G G i 22%bv 22 _ eq_refl ltac:(lia) H22) as Ev22.
  destruct (gsp_ew_extraM regs' Sg G G i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  remember (EGSPM regs' Sg G G i) as E eqn:HE. clear HE.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - gsp_nrm Hc. rewrite Ex33, gsp_sext32 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    rewrite GateModel.s32_eq0 in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20144; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_edge_tail fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ G i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hf | exact Hed | rewrite Hc; reflexivity].
  - gsp_nrm Hc. rewrite Ex33, gsp_sext32 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    rewrite GateModel.s32_eq0 in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20120; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_edge_w fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hf | exact Hed | exact Hc].
Qed.
Lemma gsp_ss_part : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  getr regs' 11 = w64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) ->
  (negb (CtrlParsed.fu Sg 8 4 =? 0) && negb (CtrlParsed.fu Sg 8 4 =? CtrlParsed.fu G (32 * i + 8) 4)) = false ->
  ((0 <=? GateModel.gdk Sg) && negb (GateModel.gdk Sg =? CtrlParsed.s32 (CtrlParsed.fu G (32 * i + 12) 4))) = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20008)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf H11 Hq1 Hq2.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & Hc11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g G s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8. pose proof (GateModel.s32_range _ R8) as R8'.
  pose proof (GateModel.fb_rng Sg 16) as R16. pose proof (GateModel.fb_rng G (32 * i + 16)) as RG16.
  destruct (gsp_mseat fq 20008 [(21%bv, SOff 32 0); (11%bv, SExt true 32 (SOff 33 0))] 0 0 regs' W mem' g s i G Sg G
    ltac:(apply gsp_nodup2; intros Hx; vm_compute in Hx; discriminate Hx)
    ltac:(destruct (gsp_ew_extraM regs' Sg G G i) as (X32 & X33 & _);
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; (split; [reflexivity|]);
          [rewrite H21; cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          |rewrite H11; cbn [sv_denot]; rewrite X33, Z.add_0_r, Z_to_bv_bv_unsigned, gsp_sext32 by exact R8; reflexivity])
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G G i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G G i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G G i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G G i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G G i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G G i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G G i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G G i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G G i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  pose proof (gsp_ew_regM regs' Sg G G i 22%bv 22 _ eq_refl ltac:(lia) H22) as Ev22.
  destruct (gsp_ew_extraM regs' Sg G G i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  remember (EGSPM regs' Sg G G i) as E eqn:HE. clear HE.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
  gkeep HST HFR.
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - gsp_nrm Hc.
    rewrite Ex37 in Hc. rewrite ?gsp_zext8 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20064; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_refresh fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hf | unfold GateModel.gedge; rewrite Hq1, Hq2, Hc; reflexivity].
  - gsp_nrm Hc. rewrite Ex37 in Hc. rewrite ?gsp_zext8 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
    gkeep HST HFR.
    rename Hc into Hc0.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + gsp_nrm Hc.
      rewrite Ex37, Ex41 in Hc. rewrite ?gsp_zext8 in Hc by lia. rewrite gsp_br_ne in Hc by lia.
      apply negb_true_iff in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20116; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_edge_head fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hf | unfold GateModel.gedge; rewrite Hq1, Hq2, Hc0, Hc; reflexivity].
    + gsp_nrm Hc. rewrite Ex37, Ex41 in Hc. rewrite ?gsp_zext8 in Hc by lia. rewrite gsp_br_ne in Hc by lia.
      apply negb_false_iff in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20064; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_refresh fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hf | unfold GateModel.gedge; rewrite Hq1, Hq2, Hc0, Hc; reflexivity].
Qed.
Lemma gsp_dk_part : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  getr regs' 11 = w64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) ->
  (negb (CtrlParsed.fu Sg 8 4 =? 0) && negb (CtrlParsed.fu Sg 8 4 =? CtrlParsed.fu G (32 * i + 8) 4)) = false ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19976)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf H11 Hq1.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & Hc11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g G s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8. pose proof (GateModel.s32_range _ R8) as R8'.
  pose proof (GateModel.gdk_rng Sg) as Rdk.
  pose proof (GateModel.fu_rng4 G (32 * i + 12) ltac:(lia)) as RG12. pose proof (GateModel.s32_range _ RG12) as RG12'.
  destruct (gsp_mseat fq 19976 [(21%bv, SOff 32 0); (11%bv, SExt true 32 (SOff 33 0))] 0 0 regs' W mem' g s i G Sg G
    ltac:(apply gsp_nodup2; intros Hx; vm_compute in Hx; discriminate Hx)
    ltac:(destruct (gsp_ew_extraM regs' Sg G G i) as (X32 & X33 & _);
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; (split; [reflexivity|]);
          [rewrite H21; cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          |rewrite H11; cbn [sv_denot]; rewrite X33, Z.add_0_r, Z_to_bv_bv_unsigned, gsp_sext32 by exact R8; reflexivity])
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G G i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G G i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G G i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G G i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G G i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G G i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G G i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G G i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G G i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  pose proof (gsp_ew_regM regs' Sg G G i 22%bv 22 _ eq_refl ltac:(lia) H22) as Ev22.
  destruct (gsp_ew_extraM regs' Sg G G i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  remember (EGSPM regs' Sg G G i) as E eqn:HE. clear HE.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - gsp_nrm Hc.
    rewrite Ev22 in Hc. rewrite gsp_br_lt in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20008; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_ss_part fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hf | exact Hq1 | rewrite Z.leb_antisym, Hc; reflexivity].
  - gsp_nrm Hc. rewrite Ev22 in Hc. rewrite gsp_br_lt in Hc by lia.
    paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
    gkeep HST HFR.
    rename Hc into Hc0.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + gsp_nrm Hc.
      rewrite Ev22, Ex40, gsp_sext32 in Hc by lia. rewrite gsp_br_ne in Hc by lia.
      apply negb_true_iff in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20116; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_edge_head fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hf | unfold GateModel.gedge; rewrite Hq1, Z.leb_antisym, Hc0, Hc; reflexivity].
    + gsp_nrm Hc. rewrite Ev22, Ex40, gsp_sext32 in Hc by lia. rewrite gsp_br_ne in Hc by lia.
      apply negb_false_iff in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20008; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_ss_part fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hf | exact Hq1 | rewrite Hc; destruct (0 <=? GateModel.gdk Sg); reflexivity].
Qed.
Lemma gsp_arm_found : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19920)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    HC HJ HST HFR H2 H3 H4 H27 H8 H9 H19 H21 H18 H22 Hf.
  pose proof HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63
    & Hgsp & Hgw & Hgapp & Hgra & Hghv & HGl & HGa & HGok & Hs0 & Hs4 & Hs63 & Hssp & Hsapp & Hsra & Hshv & HSl & HSa & Hds).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  destruct (GateModel.gfind_Some _ _ _ _ _ Hf) as [Ri Hmac].
  pose proof HGok as (_ & HnG & _).
  assert (Hi : (i < 8)%nat) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  assert (HspHi : kHighMemBeg <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK).
  { unfold kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd, kLowShadowBeg in *. lia. }
  assert (Hspr : 0 <= spZ regs - 96 /\ spZ regs <= 2 ^ 64) by (unfold kHighMemBeg in HspHi; lia).
  assert (Hg0' : 0 <= g) by lia. assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  assert (Hgra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G g 264 HST Hgra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (Hsra' : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by (apply (gsp_ra_state W memc mem' (spZ regs) g G s 24 HST Hsra); unfold amem_range, kHighMemEnd, kLowMemEnd in *; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg))
    by (apply (gsp_garr8_state W memc mem' (spZ regs) g G s _ HST HSa); rewrite ?length_map, ?HSl; cbn; lia).
  destruct (gsp_mseat fq 19920 [(21%bv, SOff 32 0)] 0 0 regs' W mem' g s i G Sg G
    ltac:(apply gsp_nodup1)
    ltac:(apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite H21; cbn [sv_denot]; rewrite (proj1 (gsp_ew_extraM regs' Sg G G i)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    H18 H9 Hi Hg0 Hg8 Hgapp Hgra' Hs0 Hs4 Hsapp Hsra' Hds ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)
    HBl HBa HSl HSa') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSPM regs' Sg G G i)) by (unfold EGSPM; apply Eimg_env).
  pose proof (gsp_ew_getM regs' Sg G G i 2%bv 2 eq_refl ltac:(lia)) as Er2.
  pose proof (gsp_ew_getM regs' Sg G G i 3%bv 3 eq_refl ltac:(lia)) as Er3.
  pose proof (gsp_ew_getM regs' Sg G G i 4%bv 4 eq_refl ltac:(lia)) as Er4.
  pose proof (gsp_ew_getM regs' Sg G G i 8%bv 8 eq_refl ltac:(lia)) as Er8.
  pose proof (gsp_ew_getM regs' Sg G G i 9%bv 9 eq_refl ltac:(lia)) as Er9.
  pose proof (gsp_ew_getM regs' Sg G G i 18%bv 18 eq_refl ltac:(lia)) as Er18.
  pose proof (gsp_ew_getM regs' Sg G G i 19%bv 19 eq_refl ltac:(lia)) as Er19.
  pose proof (gsp_ew_getM regs' Sg G G i 22%bv 22 eq_refl ltac:(lia)) as Er22.
  pose proof (gsp_ew_getM regs' Sg G G i 27%bv 27 eq_refl ltac:(lia)) as Er27.
  destruct (gsp_ew_extraM regs' Sg G G i) as (Ex32 & Ex33 & Ex34 & Ex35 & Ex36 & Ex37 & Ex38 & Ex39 & Ex40 & Ex41 & Ex42).
  remember (EGSPM regs' Sg G G i) as E eqn:HE. clear HE.
  pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8. pose proof (GateModel.s32_range _ R8) as R8'.
  pose proof (GateModel.fu_rng4 G (32 * i + 8) ltac:(lia)) as RG8. pose proof (GateModel.s32_range _ RG8) as RG8'.
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
  gkeep HST HFR.
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - gsp_nrm Hc. rewrite Ex33, gsp_sext32 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    rewrite GateModel.s32_eq0 in Hc by lia.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19976; [gsp_awr_ro|].
    gkeep HST HFR.
    pmkst HS.
    eapply (gsp_dk_part fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
      try (gsp_rg HS; fail); [exact Hf | rewrite Hc; reflexivity].
  - gsp_nrm Hc. rewrite Ex33, gsp_sext32 in Hc by lia. rewrite gsp_br_eq in Hc by lia.
    rewrite GateModel.s32_eq0 in Hc by lia.
    paj_run_tok RUN HS HJ SHOK GSP_span; [gsp_awr_ro|].
    gkeep HST HFR.
    rename Hc into Hc0.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + gsp_nrm Hc. rewrite Ex33, Ex39, !gsp_sext32 in Hc by lia. rewrite gsp_br_ne in Hc by lia.
      rewrite (GateModel.s32_inj _ _ R8 RG8) in Hc. apply negb_true_iff in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20120; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_edge_w fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hf | unfold GateModel.gedge; rewrite Hc0, Hc; reflexivity | exact Hc0].
    + gsp_nrm Hc. rewrite Ex33, Ex39, !gsp_sext32 in Hc by lia. rewrite gsp_br_ne in Hc by lia.
      rewrite (GateModel.s32_inj _ _ R8 RG8) in Hc. apply negb_false_iff in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19976; [gsp_awr_ro|].
      gkeep HST HFR.
      pmkst HS.
      eapply (gsp_dk_part fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
        try (gsp_rg HS; fail); [exact Hf | rewrite Hc0, Hc; reflexivity].
Qed.
Lemma aw_mod_mod : forall z a b, 0 <= a <= b -> (z mod 2 ^ b) mod 2 ^ a = z mod 2 ^ a.
Proof.
  intros z a b Hab. apply Z.bits_inj'. intros j Hj.
  destruct (Z.lt_ge_cases j a) as [Hja|Hja].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma aw_nth_Z_to_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth_error]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma aw_byte_mod : forall x y i, 0 <= i -> x mod 2 ^ (8 * i + 8) = y mod 2 ^ (8 * i + 8) ->
  Z_to_bv 8 (Z.shiftr x (8 * i)) = Z_to_bv 8 (Z.shiftr y (8 * i)).
Proof.
  intros x y i Hi Hm. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8). apply Z.bits_inj'. intros j Hj.
  destruct (Z.lt_ge_cases j 8) as [Hj8|Hj8].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite <- (Z.mod_pow2_bits_low x (8 * i + 8) (j + 8 * i)) by lia.
    rewrite <- (Z.mod_pow2_bits_low y (8 * i + 8) (j + 8 * i)) by lia.
    rewrite Hm. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma aw_sext_low : forall (v : word) k, 0 <= k <= 32 ->
  bv_unsigned (sext 64 (bv_extract 0 32 v)) mod 2 ^ k = bv_unsigned v mod 2 ^ k.
Proof.
  intros v k Hk.
  assert (Pk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (P32 : 0 < 2 ^ 32) by (apply Z.pow_pos_nonneg; lia).
  unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
  change (bv_half_modulus 32) with (2 ^ 31).
  rewrite (aw_mod_mod _ k 64) by lia.
  rewrite (Z.mod_eq (bv_unsigned v mod 2 ^ 32 + 2 ^ 31) (2 ^ 32)) by lia.
  replace (bv_unsigned v mod 2 ^ 32 + 2 ^ 31 -
           2 ^ 32 * ((bv_unsigned v mod 2 ^ 32 + 2 ^ 31) / 2 ^ 32) - 2 ^ 31)
    with (bv_unsigned v mod 2 ^ 32 +
          (- ((bv_unsigned v mod 2 ^ 32 + 2 ^ 31) / 2 ^ 32) * 2 ^ (32 - k)) * 2 ^ k)
    by (rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia;
        replace (32 - k + k) with 32 by lia; lia).
  rewrite Z_mod_plus_full. apply aw_mod_mod. lia.
Qed.
Lemma aw_byte_sext : forall (v : word) i, 0 <= i < 4 ->
  byte_of_word (sext 64 (bv_extract 0 32 v)) i = byte_of_word v i.
Proof.
  intros v i Hi. unfold byte_of_word. apply aw_byte_mod; [lia|]. apply aw_sext_low. lia.
Qed.
Lemma aw_byte_zext : forall (v : word) (b : byte), bv_unsigned v = bv_unsigned b ->
  byte_of_word (zext 64 (bv_extract 0 8 v)) 0 = b.
Proof.
  intros v b Hv. unfold byte_of_word. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
  unfold zext. rewrite bv_zero_extend_unsigned by lia.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap.
  change (bv_modulus 8) with (2 ^ 8). rewrite Hv.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma aw_nth_le4 : forall (v : word) (k : nat), (k < 4)%nat ->
  nth (Z.to_nat (Z.of_nat k)) (Mem.le4 v) (CtrlParsed.zb 0) = byte_of_word v (Z.of_nat k).
Proof.
  intros v k Hk. rewrite Nat2Z.id. unfold Mem.le4.
  rewrite (nth_error_nth _ _ _ (aw_nth_Z_to_le_bytes 4 (bv_unsigned v) k Hk)). reflexivity.
Qed.
Lemma aw_nth_le8 : forall (v : word) (k : nat), (k < 8)%nat ->
  nth (Z.to_nat (Z.of_nat k)) (Mem.le8 v) (CtrlParsed.zb 0) = byte_of_word v (Z.of_nat k).
Proof.
  intros v k Hk. rewrite Nat2Z.id. unfold Mem.le8, word_to_le_bytes.
  rewrite (nth_error_nth _ _ _ (aw_nth_Z_to_le_bytes 8 (bv_unsigned v) k Hk)). reflexivity.
Qed.
Lemma aw_byte_fu4 : forall (L : list byte) (k : nat) (i : Z), (k + 4 <= length L)%nat -> 0 <= i < 4 ->
  byte_of_word (Z_to_bv 64 (CtrlParsed.fu L k 4)) i = nth (k + Z.to_nat i) L (CtrlParsed.zb 0).
Proof.
  intros L k i Hk Hi. pose proof (GateModel.fu_rng4 L k Hk) as Hr.
  unfold byte_of_word. rewrite unsigned_lit_small by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256.
  rewrite <- (gsp_le_byte_fu L k 4 (Z.to_nat i) Hk ltac:(lia)). unfold YO0f.le_byte.
  rewrite (Z.mod_small (CtrlParsed.fu L k 4) (2 ^ (8 * Z.of_nat 4)))
    by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
  f_equal. f_equal. lia.
Qed.
Lemma aw_byte_fb : forall (L : list byte) (k : nat),
  byte_of_word (zext 64 (bv_extract 0 8 (Z_to_bv 64 (CtrlParsed.fb L k)))) 0 =
  nth k L (CtrlParsed.zb 0).
Proof.
  intros L k. apply aw_byte_zext. unfold CtrlParsed.fb.
  pose proof (bv_unsigned_in_range 8 (nth k L (CtrlParsed.zb 0))) as Hb.
  change (bv_modulus 8) with 256 in Hb. apply unsigned_lit_small. lia.
Qed.
Lemma aw_le_byte1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Zmod_mod. apply Z.mod_small. lia.
Qed.
Lemma aw_st_ok : forall (fq : YK11.FPState) (pc : Z) (upd : list (bv 5 * sv)) (regs : bvmap 5 word)
  (W : world SEGS) (mem : word -> option byte) (Sg G : list byte) (rs : smem) (Gf : facts),
  NoDup (map fst upd) ->
  Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs (fst p) = sv_denot (EGSP regs Sg G) (snd p)) upd ->
  regions_wf rs = true ->
  Forall (region_ok SEGS (EGSP regs Sg G) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (EGSP regs Sg G) rs ->
  facts_ok (EGSP regs Sg G) Gf ->
  st_ok_pi SEGS VAL (EGSP regs Sg G) (mkSS pc (gsp_sr upd) rs None Gf)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros fq pc upd regs W mem Sg G rs Gf HND HUPD Hwf Hrs Hpd HGf.
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; try assumption.
  unfold gsp_sr. apply (regs_ok_sets _ sr_atoms regs regs upd);
    [apply regs_ok_EGSP | exact HND | intros r _; reflexivity | exact HUPD].
Qed.
Lemma aw_shent : forall (regs : bvmap 5 word) (Sg G : list byte) (W : world SEGS)
  (mem : word -> option byte) (n : nat) (p hi : Z),
  ew (EGSP regs Sg G) n = Z_to_bv 64 p -> 0 <= p -> 0 <= hi -> amem_range p hi ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p hi ->
  shent_ok SEGS GSP_SBx (EGSP regs Sg G) (mrestrict (w_H W) mem) (mkSHE n 0 hi).
Proof.
  intros regs Sg G W mem n p hi Hew Hp0 Hhi Hmr Hra.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hmr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
  assert (HUB : U (EGSP regs Sg G) GSP_SBx = SHADOW_OFF)
    by (unfold GSP_SBx; shent_U_norm; unfold SB, SHADOW_OFF; reflexivity).
  assert (Hpr : 0 <= p < 2 ^ 64) by lia.
  assert (HUn : U (EGSP regs Sg G) (SOff n 0) = p).
  { unfold U. cbn [sv_denot]. rewrite Hew, (unsigned_lit_small p Hpr), Z.add_0_r.
    exact (unsigned_lit_small p Hpr). }
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HUn, HUB. split.
  - replace (p + 0) with p by lia. replace (hi - 0) with hi by lia. exact Hra.
  - intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.
Lemma aw_mbyte_frame : forall (W : world SEGS) (E : env) (rs : smem) (m m' : word -> option byte) (a : Z),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> ~ in_wrange E rs a -> 0 <= a < 2 ^ 64 ->
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
  intros W E rs m m' a HF Hn Ha. unfold mbyte.
  rewrite (HF (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.
Lemma aw_aview_of_mbyte : forall (W : world SEGS) (m m' : word -> option byte) (a : Z),
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W m m' a H. unfold aview. rewrite H. reflexivity. Qed.
Lemma aw_mbyte_of_aview : forall (W : world SEGS) (m m' : word -> option byte) (a : Z),
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a ->
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
  intros W m m' a H. unfold aview in H.
  destruct (mbyte SEGS (mrestrict (w_H W) m') a) as [b'|] eqn:E';
  destruct (mbyte SEGS (mrestrict (w_H W) m) a) as [b|] eqn:E;
  cbn [option_map] in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma aw_mbyte_of_byte : forall (W : world SEGS) (m : word -> option byte) (a : Z) (b : byte),
  aview SEGS (w_H W) m a = Some (bv_unsigned b) -> mbyte SEGS (mrestrict (w_H W) m) a = Some b.
Proof.
  intros W m a b H. unfold aview in H.
  destruct (mbyte SEGS (mrestrict (w_H W) m) a) as [b'|] eqn:E; cbn [option_map] in H; [|discriminate].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma aw_garr8_of_bytes : forall (W : world SEGS) (m : word -> option byte) (p : Z) (L : list byte),
  (forall j, (j < length L)%nat ->
     mbyte SEGS (mrestrict (w_H W) m) (p + Z.of_nat j) = Some (nth j L (CtrlParsed.zb 0))) ->
  garr8 SEGS (mrestrict (w_H W) m) p (map bv_unsigned L).
Proof.
  intros W m p L H j Hj. rewrite length_map in Hj.
  pose proof (bv_unsigned_in_range 8 (nth j L (CtrlParsed.zb 0))) as Hb.
  change (bv_modulus 8) with 256 in Hb.
  rewrite gsp_nth_map. split; [|exact Hb].
  intros kk Hk. assert (kk = 0)%nat by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (H j Hj). f_equal. rewrite (aw_le_byte1 _ Hb). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma aw_val_mem_move : forall (W : world SEGS) (m m' : word -> option byte) (a : Z) (n : nat) (v lo hi : Z),
  val_mem SEGS (mrestrict (w_H W) m) a n v ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) ->
     mbyte SEGS (mrestrict (w_H W) m') x = mbyte SEGS (mrestrict (w_H W) m) x) ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
  val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
  intros W m m' a n v lo hi HV HM Ha0 Han Hd k Hk.
  rewrite (HM (a + Z.of_nat k) ltac:(lia) ltac:(lia)). apply HV. exact Hk.
Qed.
Lemma aw_frame_move : forall (W : world SEGS) (m m' : word -> option byte) (sp : Z)
  (regs : bvmap 5 word) (lo hi : Z),
  gsp_frame W m sp regs ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) ->
     mbyte SEGS (mrestrict (w_H W) m') x = mbyte SEGS (mrestrict (w_H W) m) x) ->
  0 <= sp - 96 -> sp <= 2 ^ 64 -> (sp <= lo \/ hi <= sp - 96) ->
  gsp_frame W m' sp regs.
Proof.
  intros W m m' sp regs lo hi HF HM H1 H2 Hd. unfold gsp_frame in *.
  destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  repeat split; (eapply aw_val_mem_move; [eassumption | exact HM | lia | lia | lia]).
Qed.
Lemma aw_state_keep : forall (W : world SEGS) (memc m m' : word -> option byte) (sp g lo hi : Z)
  (B' : list byte),
  gsp_state W memc m sp g B' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) ->
     mbyte SEGS (mrestrict (w_H W) m') x = mbyte SEGS (mrestrict (w_H W) m) x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> g <= lo -> hi <= g + 264 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < sp) ->
     ~ (g <= a < g + 264) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m' a).
Proof.
  intros W memc m m' sp g lo hi B' (S1 & S2 & _ & _) HM HG Hlo Hhi. split.
  - intros a Ha Hs Hgg. rewrite (aw_aview_of_mbyte W m m' a (HM a Ha ltac:(lia))).
    apply S1; assumption.
  - intros a Hp. apply (gsp_apresent_grow W m m' a HG). apply S2. exact Hp.
Qed.
Definition aw_xs8 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 256) (SLit 3)) (SOff 32 0).
Lemma aw_xs8_denot : forall (regs : bvmap 5 word) (Sg G : list byte) (g : Z),
  ew (EGSP regs Sg G) 19 = Z_to_bv 64 g -> 0 <= g -> g + 264 <= 2 ^ 63 ->
  sv_denot (EGSP regs Sg G) aw_xs8 = Z_to_bv 64 ((g + 256) / 8 + SB).
Proof.
  intros regs Sg G g E19 Hg0 Hg63.
  destruct (gsp_ew_extra regs Sg G) as (E32 & _).
  assert (Hd : 0 <= (g + 256) / 8 <= g + 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HU : U (EGSP regs Sg G) aw_xs8 = (g + 256) / 8 + SB).
  { unfold aw_xs8. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3.
    rewrite (U_atom_off (EGSP regs Sg G) 19 g 256 E19 ltac:(lia) ltac:(lia)).
    rewrite (U_atom (EGSP regs Sg G) 32 SB E32 ltac:(unfold SB; lia)).
    unfold zcanon, M64, SB in *. apply Z.mod_small. lia. }
  unfold U in HU. rewrite <- HU, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma aw_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  amem_range p' n'.
Proof. intros p n p' n' H H1 H2 H3. unfold amem_range in *. lia. Qed.
Lemma aw_ra_sub : forall (rd : reader) p n p' n',
  range_addressable rd SHADOW_OFF p n -> p <= p' -> p' + n' <= p + n ->
  range_addressable rd SHADOW_OFF p' n'.
Proof. intros rd p n p' n' H H1 H2 x Hx. apply H. lia. Qed.
Lemma aw_hull_sub : forall (rd : reader) p n p' n',
  shadow_hull_vis rd p n -> p <= p' -> 0 < n' -> p' + n' <= p + n -> shadow_hull_vis rd p' n'.
Proof.
  intros rd p n p' n' H H1 H2 H3 sx Hsx. apply H.
  pose proof (shadow_mono p p' H1) as M1.
  pose proof (shadow_mono (p' + n' - 1) (p + n - 1) ltac:(lia)) as M2.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
    by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma aw_ra_band : forall (W : world SEGS) (m m' : word -> option byte) (p n : Z),
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p n ->
  (forall x, SHADOW_OFF <= x < kHighShadowEnd -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= p -> 0 <= n -> amem_range p n ->
  range_addressable (aview SEGS (w_H W) m') SHADOW_OFF p n.
Proof.
  intros W m m' p n HR HM Hp0 Hn Hmr x Hx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hmr. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, SHADOW_OFF in *.
  destruct (HR x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  assert (Hd1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd2 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  assert (Heq : shadow_of_addr 2147450880 x = 2147450880 + x / 8) by reflexivity.
  change (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr 2147450880 x) in *. rewrite Heq in *.
  rewrite HM by lia. exact Hsv.
Qed.
Lemma aw_hull_band : forall (W : world SEGS) (m m' : word -> option byte) (p n : Z),
  shadow_hull_vis (aview SEGS (w_H W) m) p n ->
  (forall x, SHADOW_OFF <= x < kHighShadowEnd -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= p -> 0 < n -> amem_range p n ->
  shadow_hull_vis (aview SEGS (w_H W) m') p n.
Proof.
  intros W m m' p n HH HM Hp0 Hn Hmr sx Hsx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hmr.
  unfold shadow_addr, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, SHADOW_OFF in *.
  assert (Hp8 : 0 <= p / 8 < 17592186044416)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (He8 : 0 <= (p + n - 1) / 8 < 17592186044416)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hlo8 : 2147450880 <= (2147450880 + p / 8) / 8 * 8).
  { apply (Z.le_trans _ (2147450880 / 8 * 8)).
    - vm_compute. discriminate.
    - apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  assert (Hhi8 : (2147450880 + (p + n - 1) / 8) / 8 * 8 + 8 <= 17594333495296).
  { assert (Hq : 8 * ((2147450880 + (p + n - 1) / 8) / 8) <= 2147450880 + (p + n - 1) / 8)
      by (apply Z.mul_div_le; lia). lia. }
  rewrite HM by lia. exact (HH sx Hsx).
Qed.
Lemma aw_band_state : forall (W : world SEGS) (memc m : word -> option byte) (sp g : Z) (B' : list byte),
  gsp_state W memc m sp g B' -> kHighShadowEnd <= sp - REAC_DISCO_GATE_SHOULD_PUSH_STK ->
  amem_range g 264 -> 0 <= g ->
  forall x, SHADOW_OFF <= x < kHighShadowEnd -> aview SEGS (w_H W) m x = aview SEGS (w_H W) memc x.
Proof.
  intros W memc m sp g B' (S1 & _) Hsp Hmr Hg0 x Hx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hmr.
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, SHADOW_OFF in *.
  apply S1; lia.
Qed.
Lemma aw_branch_lt_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts.
  rewrite (GateModel.signed_lit a Ha), (GateModel.signed_lit b Hb). reflexivity.
Qed.
Lemma aw_ex_step : forall (W : world SEGS) (memc m m' : word -> option byte)
  (regs : bvmap 5 word) (g : Z) (G : list byte),
  gsp_state W memc m (spZ regs) g G -> gsp_frame W m (spZ regs) regs ->
  (forall x, 0 <= x < 2 ^ 64 ->
     mbyte SEGS (mrestrict (w_H W) m') x = mbyte SEGS (mrestrict (w_H W) m) x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  0 <= g -> g + 264 <= 2 ^ 64 -> 96 <= spZ regs -> spZ regs <= 2 ^ 64 ->
  gsp_state W memc m' (spZ regs) g G /\ gsp_frame W m' (spZ regs) regs.
Proof.
  intros W memc m m' regs g G HST HFR HM HGR Hg0 Hg64 Hsp1 Hsp2.
  pose proof HST as (T1 & T2 & T3 & T4). split.
  - destruct (aw_state_keep W memc m m' (spZ regs) g g g G HST
      ltac:(intros x Hx _; apply HM; exact Hx) HGR ltac:(lia) ltac:(lia)) as (K1 & K2).
    split; [exact K1|]. split; [exact K2|]. split; [exact T3|].
    apply (gsp_garr8_move W m m' g (map bv_unsigned G) g g T4
      ltac:(intros x Hx _; apply HM; exact Hx) ltac:(lia)
      ltac:(rewrite length_map; lia) ltac:(lia)).
  - apply (aw_frame_move W m m' (spZ regs) regs 0 0 HFR
      ltac:(intros x Hx _; apply HM; exact Hx) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma aw_keep11 : forall (fq : YK11.FPState) (E : env) (ss : sstate) (ms : machine_state)
  (regs0 : bvmap 5 word) (extra : list word),
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv; 27%bv] = true ->
  getr (ms_regs ms) 2 = getr regs0 2 /\ getr (ms_regs ms) 3 = getr regs0 3 /\
  getr (ms_regs ms) 4 = getr regs0 4 /\ getr (ms_regs ms) 8 = getr regs0 8 /\
  getr (ms_regs ms) 9 = getr regs0 9 /\ getr (ms_regs ms) 19 = getr regs0 19 /\
  getr (ms_regs ms) 20 = getr regs0 20 /\ getr (ms_regs ms) 22 = getr regs0 22 /\
  getr (ms_regs ms) 23 = getr regs0 23 /\ getr (ms_regs ms) 24 = getr regs0 24 /\
  getr (ms_regs ms) 27 = getr regs0 27.
Proof.
  intros fq E ss ms regs0 extra HS HA Hf.
  pose proof (regs_kept_of_st_ok_pi (fx := fq) E ss ms regs0 extra _ HS HA Hf) as K.
  repeat split; apply K; cbn [In]; repeat first [left; reflexivity | right].
Qed.
Lemma gsp_epiA : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 10 = w64 (snd (GateModel.gate_model G Sg now)) ->
  B' = fst (GateModel.gate_model G Sg now) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20252)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros.
  lazymatch goal with HC : gsp_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof HC as (_ & _ & _ & Hgp & Htp & _) end.
  eapply gsp_epi; try eassumption; congruence.
Qed.
Lemma gsp_ret0A : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (B' : list byte),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g B' ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  GateModel.gate_model G Sg now = (B', 0) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 20108)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros.
  lazymatch goal with HC : gsp_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof HC as (_ & _ & _ & Hgp & Htp & _) end.
  eapply gsp_ret0; try eassumption; congruence.
Qed.
Definition aw_appended (G Sg : list byte) (N : nat) : list byte :=
  Mem.upd_bytes (Mem.upd_bytes G 256 (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1)))) (32 * N)
    (CtrlParsed.fld Sg 0 6).
Lemma gsp_app_b : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (N : nat) (d : Z),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g (aw_appended G Sg N) ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 d -> getr regs' 21 = w64 SB ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = None ->
  disco_classify_c.gn G = Z.of_nat N -> (N < 8)%nat -> d = g + 32 * Z.of_nat N ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19772)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' N d
    HCTX HJ HST HFR R2 R3 R4 R27 R8 R9 R19 R21 R22 HFIND HgnN HN8 Hd.
  pose proof HCTX as HC.
  destruct HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp &
    Hg0 & Hg8 & Hg63 & Hgside & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 &
    Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ0 as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ &
    Hpres & Hstatic & _ & HQT).
  destruct Hstatic as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HST as (HSt1 & HSt2 & HAl & HAa).
  pose proof Hgapp as Hga. pose proof Hsapp as Hsa. unfold amem_range in Hga, Hsa.
  assert (HBAND : forall x, SHADOW_OFF <= x < kHighShadowEnd ->
      aview SEGS (w_H W) mem' x = aview SEGS (w_H W) memc x).
  { apply (aw_band_state W memc mem' (spZ regs) g (aw_appended G Sg N) HST); [|exact Hgapp | lia].
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia. }
  unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *.
  assert (Hd8 : d mod 8 = 0) by (clear - Hd Hg8; subst d; Z.div_mod_to_equations; lia).
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg regs' (gsp_extra Sg G)) (EGSP regs' Sg G))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (gsp_ew_reg regs' Sg G 19%bv 19 d eq_refl ltac:(lia) R19) as E19.
  pose proof (gsp_ew_reg regs' Sg G 9%bv 9 s eq_refl ltac:(lia) R9) as E9.
  pose proof (gsp_ew_reg regs' Sg G 8%bv 8 now eq_refl ltac:(lia) R8) as E8.
  pose proof (gsp_ew_reg regs' Sg G 22%bv 22 (GateModel.gdk Sg) eq_refl ltac:(lia) R22) as E22.
  assert (EB : bv_unsigned (ew (EGSP regs' Sg G) 19) = d) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (VBd : base_val (EGSP regs' Sg G) (Some 19%nat) = d) by exact EB.
  assert (VBs : base_val (EGSP regs' Sg G) (Some 9%nat) = s)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  assert (Hwrt : forall a, g <= a < g + 264 -> writable_at SEGS (mrestrict (w_H W) mem') a)
    by (intros a Ha; apply gsp_writable_of_apresent; apply HSt2; exact (proj2 (Hgwr a Ha))).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg)).
  { apply (garr8_frame SEGS _ _ s _ HSarr). intros a Ha. rewrite length_map, HSlen in Ha.
    apply aw_mbyte_of_aview. apply HSt1; lia. }
  assert (RO : Forall (region_ok SEGS (EGSP regs' Sg G) (mrestrict (w_H W) mem'))
    [YP09.mkRegion (Some 19%nat) 8 12 8 12 []; YP09.mkRegion (Some 19%nat) 12 16 12 16 [];
     YP09.mkRegion (Some 19%nat) 16 17 16 17 []; YP09.mkRegion (Some 19%nat) 24 32 24 32 [];
     gsp_sreg 9]).
  { repeat apply Forall_cons; try apply Forall_nil.
    1-4: unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
         rewrite VBd; split; [lia|]; split; [lia|]; split; [intros o Ho; apply Hwrt; lia | apply Forall_nil].
    exact (gsp_sreg_ok 9 regs' Sg G W mem' s E9 ltac:(lia) ltac:(lia) HSlen HSa'). }
  assert (PD : pairwise_disjoint (EGSP regs' Sg G)
    [YP09.mkRegion (Some 19%nat) 8 12 8 12 []; YP09.mkRegion (Some 19%nat) 12 16 12 16 [];
     YP09.mkRegion (Some 19%nat) 16 17 16 17 []; YP09.mkRegion (Some 19%nat) 24 32 24 32 [];
     gsp_sreg 9]).
  { apply pairwise_disjoint_of_extents. unfold gsp_sreg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VBd, VBs.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia. }
  assert (FO : facts_ok (EGSP regs' Sg G)
    (mkFacts [(19%nat, mkAF 0 (2 ^ 47 - 32) 3); (9%nat, mkAF 0 (2 ^ 47 - 24) 2); (32%nat, mkAF SB SB 0)] [] [])).
  { split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E19, E9, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia | reflexivity]. }
  pose proof (aw_st_ok fq 19772 [(21%bv, SOff 32 0)] regs' W mem' Sg G
     [YP09.mkRegion (Some 19%nat) 8 12 8 12 []; YP09.mkRegion (Some 19%nat) 12 16 12 16 [];
      YP09.mkRegion (Some 19%nat) 16 17 16 17 []; YP09.mkRegion (Some 19%nat) 24 32 24 32 [];
      gsp_sreg 9]
     (mkFacts [(19%nat, mkAF 0 (2 ^ 47 - 32) 3); (9%nat, mkAF 0 (2 ^ 47 - 24) 2); (32%nat, mkAF SB SB 0)] [] [])
     ltac:(cbn [map fst]; apply gsp_nodup1)
     ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split; [reflexivity|];
           rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
     ltac:(vm_compute; reflexivity) RO PD FO) as HS.
  assert (RAg : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF g 264)
    by exact (aw_ra_band W memc mem' g 264 Hgra HBAND ltac:(lia) ltac:(lia) Hgapp).
  assert (RAs : range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF s 24)
    by exact (aw_ra_band W memc mem' s 24 Hsra HBAND ltac:(lia) ltac:(lia) Hsapp).
  assert (SHOK : sh_ok SEGS GSP_SBx [mkSHE 19 0 32; mkSHE 9 0 24] (EGSP regs' Sg G) (mrestrict (w_H W) mem')).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - exact (aw_shent regs' Sg G W mem' 19 d 32 E19 ltac:(lia) ltac:(lia)
        (aw_amem_sub g 264 d 32 Hgapp ltac:(lia) ltac:(lia) ltac:(lia))
        (aw_ra_sub _ g 264 d 32 RAg ltac:(lia) ltac:(lia))).
    - exact (aw_shent regs' Sg G W mem' 9 s 24 E9 ltac:(lia) ltac:(lia) Hsapp RAs). }
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20252.
  { do 4 (apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat d);
      [reflexivity | exact EB
      | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; exact (proj1 (Hgwr a ltac:(lia))) | idtac]).
    apply awr_ok_cons_ro; [cbn [gsp_sreg YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
  assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (d + 8 <= a < d + 17) -> ~ (d + 24 <= a < d + 32) ->
     mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H W) mem') a).
  { intros a Ha Hn1 Hn2.
    lazymatch goal with
    | HFrx : frame_of ?Ev ?rs (mrestrict (w_H W) mem') (mrestrict (w_H W) (ms_mem ms)) |- _ =>
      apply (aw_mbyte_frame W Ev rs mem' (ms_mem ms) a HFrx); [|exact Ha]
    end.
    intros (rr & Hin & Hr). cbn in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi gsp_sreg] in Hr; rewrite ?VBd in Hr; lia. }
  assert (RO1 : region_ok SEGS (EGSP regs' Sg G) (mrestrict (w_H W) (ms_mem ms))
      (YP09.mkRegion (Some 19%nat) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SExt true 32 (SOff 33 0)))]))
    by exact (st_ok_region_nth _ _ _ 0 _ HS eq_refl).
  assert (RO2 : region_ok SEGS (EGSP regs' Sg G) (mrestrict (w_H W) (ms_mem ms))
      (YP09.mkRegion (Some 19%nat) 12 16 12 16 [YP09.mkChunk 12 (CVal 4 (SOff 22 0))]))
    by exact (st_ok_region_nth _ _ _ 1 _ HS eq_refl).
  assert (RO3 : region_ok SEGS (EGSP regs' Sg G) (mrestrict (w_H W) (ms_mem ms))
      (YP09.mkRegion (Some 19%nat) 16 17 16 17 [YP09.mkChunk 16 (CVal 1 (SExt false 8 (SOff 37 0)))]))
    by exact (st_ok_region_nth _ _ _ 2 _ HS eq_refl).
  assert (RO4 : region_ok SEGS (EGSP regs' Sg G) (mrestrict (w_H W) (ms_mem ms))
      (YP09.mkRegion (Some 19%nat) 24 32 24 32 [YP09.mkChunk 24 (CVal 8 (SOff 8 0))]))
    by exact (st_ok_region_nth _ _ _ 3 _ HS eq_refl).
  assert (CB : forall (m : word -> option byte) (n : nat) (lo hi wlo whi od : Z) (w : BinNums.N) (e : sv) (i : Z),
     region_ok SEGS (EGSP regs' Sg G) m (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk od (CVal w e)]) ->
     0 <= i < Z.of_N w ->
     mbyte SEGS m (bv_unsigned (ew (EGSP regs' Sg G) n) + od + i) =
     Some (byte_of_word (sv_denot (EGSP regs' Sg G) e) i)).
  { intros m n lo hi wlo whi od w e i (_ & _ & _ & Hcs) Hi.
    cbn [YP09.r_chunks YP09.r_base] in Hcs.
    apply Forall_inv in Hcs. destruct (Hcs i Hi) as (b & Hb & Hm).
    cbn [cbyte YP09.c_val YP09.c_off base_val YP09.r_base] in Hb, Hm.
    injection Hb as Hb. subst b. exact Hm. }
  assert (D1 : forall i, 0 <= i < 4 -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (d + 8 + i) =
      Some (nth (8 + Z.to_nat i) Sg (CtrlParsed.zb 0))).
  { intros i Hi. pose proof (CB _ 19%nat 8 12 8 12 8 4%N (SExt true 32 (SOff 33 0)) i RO1 ltac:(lia)) as Y.
    rewrite EB in Y. cbn [sv_denot] in Y. rewrite E33, !Z.add_0_r, Z_to_bv_bv_unsigned in Y.
    rewrite (aw_byte_sext _ i Hi), (aw_byte_fu4 Sg 8 i ltac:(lia) Hi) in Y. exact Y. }
  assert (D2 : forall kk, (kk < 4)%nat -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (d + 12 + Z.of_nat kk) =
      Some (nth kk (Mem.le4 (Z_to_bv 64 (GateModel.gdk Sg))) (CtrlParsed.zb 0))).
  { intros kk Hkk. pose proof (CB _ 19%nat 12 16 12 16 12 4%N (SOff 22 0) (Z.of_nat kk) RO2 ltac:(lia)) as Y.
    rewrite EB in Y. cbn [sv_denot] in Y. rewrite E22, !Z.add_0_r, Z_to_bv_bv_unsigned in Y.
    rewrite <- (aw_nth_le4 (Z_to_bv 64 (GateModel.gdk Sg)) kk Hkk), Nat2Z.id in Y. exact Y. }
  assert (D3 : mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (d + 16) = Some (nth 16 Sg (CtrlParsed.zb 0))).
  { pose proof (CB _ 19%nat 16 17 16 17 16 1%N (SExt false 8 (SOff 37 0)) 0 RO3 ltac:(lia)) as Y.
    rewrite EB in Y. cbn [sv_denot] in Y. rewrite E37, !Z.add_0_r, Z_to_bv_bv_unsigned in Y.
    rewrite aw_byte_fb in Y. exact Y. }
  assert (D4 : forall kk, (kk < 8)%nat -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (d + 24 + Z.of_nat kk) =
      Some (nth kk (Mem.le8 (Z_to_bv 64 now)) (CtrlParsed.zb 0))).
  { intros kk Hkk. pose proof (CB _ 19%nat 24 32 24 32 24 8%N (SOff 8 0) (Z.of_nat kk) RO4 ltac:(lia)) as Y.
    rewrite EB in Y. cbn [sv_denot] in Y. rewrite E8, !Z.add_0_r, Z_to_bv_bv_unsigned in Y.
    rewrite <- (aw_nth_le8 (Z_to_bv 64 now) kk Hkk), Nat2Z.id in Y. exact Y. }
  assert (NU : forall (cs bs : list byte) (k0 i : nat), (k0 + length bs <= length cs)%nat -> (i < length cs)%nat ->
     nth i (Mem.upd_bytes cs k0 bs) (CtrlParsed.zb 0) =
     if ((k0 <=? i) && (i <? k0 + length bs))%nat then nth (i - k0) bs (CtrlParsed.zb 0)
     else nth i cs (CtrlParsed.zb 0)).
  { intros cs bs k0 i Hk0 Hi.
    pose proof (GateModel.nth_error_upd cs k0 bs Hk0 i) as NE.
    rewrite (@nth_error_nth' byte (Mem.upd_bytes cs k0 bs) i (CtrlParsed.zb 0)
      ltac:(rewrite GateModel.length_upd by exact Hk0; exact Hi)) in NE.
    destruct ((k0 <=? i) && (i <? k0 + length bs))%nat eqn:Hw.
    - apply andb_true_iff in Hw as [Hw1 Hw2]. apply Nat.leb_le in Hw1. apply Nat.ltb_lt in Hw2.
      rewrite (@nth_error_nth' byte bs (i - k0) (CtrlParsed.zb 0) ltac:(lia)) in NE.
      injection NE as NE. exact NE.
    - rewrite (@nth_error_nth' byte cs i (CtrlParsed.zb 0) Hi) in NE. injection NE as NE. exact NE. }
  assert (BT : forall k0 l0 j0 : nat, (k0 <= j0 < k0 + l0)%nat -> ((k0 <=? j0) && (j0 <? k0 + l0))%nat = true)
    by (intros k0 l0 j0 Hk0; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  assert (BF : forall k0 l0 j0 : nat, ~ (k0 <= j0 < k0 + l0)%nat -> ((k0 <=? j0) && (j0 <? k0 + l0))%nat = false).
  { intros k0 l0 j0 Hk0. apply andb_false_iff.
    destruct (Nat.le_gt_cases k0 j0); [right; apply Nat.ltb_ge | left; apply Nat.leb_gt]; lia. }
  set (A := aw_appended G Sg N) in *.
  set (X1 := CtrlParsed.fld Sg 8 4).
  set (X2 := Mem.le4 (Z_to_bv 64 (GateModel.gdk Sg))).
  set (X3 := [nth 16 Sg (CtrlParsed.zb 0)]).
  set (X4 := Mem.le8 (Z_to_bv 64 now)).
  set (B1 := Mem.upd_bytes A (32 * N + 8)%nat X1).
  set (B2 := Mem.upd_bytes B1 (32 * N + 12)%nat X2).
  set (B3 := Mem.upd_bytes B2 (32 * N + 16)%nat X3).
  set (B4 := Mem.upd_bytes B3 (32 * N + 24)%nat X4).
  assert (LX1 : length X1 = 4%nat) by (unfold X1; apply GateModel.length_fld; lia).
  assert (LX2 : length X2 = 4%nat) by (unfold X2; apply Mem.length_le4).
  assert (LX3 : length X3 = 1%nat) by reflexivity.
  assert (LX4 : length X4 = 8%nat) by (unfold X4; apply Mem.length_le8).
  assert (LB1 : length B1 = 264%nat) by (unfold B1; rewrite GateModel.length_upd; lia).
  assert (LB2 : length B2 = 264%nat) by (unfold B2; rewrite GateModel.length_upd; lia).
  assert (LB3 : length B3 = 264%nat) by (unfold B3; rewrite GateModel.length_upd; lia).
  assert (LB4 : length B4 = 264%nat) by (unfold B4; rewrite GateModel.length_upd; lia).
  assert (OUT : forall j, (j < 264)%nat -> ~ (32 * N + 8 <= j < 32 * N + 17)%nat ->
     ~ (32 * N + 24 <= j < 32 * N + 32)%nat ->
     mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (g + Z.of_nat j) = Some (nth j A (CtrlParsed.zb 0))).
  { intros j Hj Hn1 Hn2. rewrite MF by lia.
    rewrite (garr8_mbyte SEGS _ g _ j HAa ltac:(rewrite length_map; lia)).
    rewrite gsp_nth_map, Z_to_bv_bv_unsigned. reflexivity. }
  assert (GB : forall j, (j < 264)%nat ->
     mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (g + Z.of_nat j) = Some (nth j B4 (CtrlParsed.zb 0))).
  { intros j Hj. unfold B4.
    rewrite (NU B3 X4 (32 * N + 24)%nat j) by lia.
    unfold B3. rewrite (NU B2 X3 (32 * N + 16)%nat j) by lia.
    unfold B2. rewrite (NU B1 X2 (32 * N + 12)%nat j) by lia.
    unfold B1. rewrite (NU A X1 (32 * N + 8)%nat j) by lia.
    rewrite LX1, LX2, LX3, LX4.
    assert (CS : ((j < 32 * N + 8)%nat \/ (32 * N + 17 <= j < 32 * N + 24)%nat \/ (32 * N + 32 <= j)%nat) \/
                 (32 * N + 8 <= j < 32 * N + 12)%nat \/ (32 * N + 12 <= j < 32 * N + 16)%nat \/
                 j = (32 * N + 16)%nat \/ (32 * N + 24 <= j < 32 * N + 32)%nat) by lia.
    destruct CS as [CO | [CA | [CB2 | [CC | CD]]]].
    - rewrite (BF (32 * N + 24)%nat 8%nat j), (BF (32 * N + 16)%nat 1%nat j), (BF (32 * N + 12)%nat 4%nat j),
        (BF (32 * N + 8)%nat 4%nat j) by lia.
      cbv beta iota. apply OUT; lia.
    - rewrite (BF (32 * N + 24)%nat 8%nat j), (BF (32 * N + 16)%nat 1%nat j), (BF (32 * N + 12)%nat 4%nat j),
        (BT (32 * N + 8)%nat 4%nat j) by lia.
      cbv beta iota. unfold X1. rewrite (gsp_nth_fld Sg 8 4 (j - (32 * N + 8))) by lia.
      pose proof (D1 (Z.of_nat (j - (32 * N + 8))) ltac:(lia)) as Y.
      rewrite Nat2Z.id in Y.
      replace (d + 8 + Z.of_nat (j - (32 * N + 8))) with (g + Z.of_nat j) in Y by lia.
      exact Y.
    - rewrite (BF (32 * N + 24)%nat 8%nat j), (BF (32 * N + 16)%nat 1%nat j), (BT (32 * N + 12)%nat 4%nat j) by lia.
      cbv beta iota.
      pose proof (D2 (j - (32 * N + 12))%nat ltac:(lia)) as Y.
      replace (d + 12 + Z.of_nat (j - (32 * N + 12))) with (g + Z.of_nat j) in Y by lia.
      exact Y.
    - rewrite (BF (32 * N + 24)%nat 8%nat j), (BT (32 * N + 16)%nat 1%nat j) by lia.
      cbv beta iota. replace (j - (32 * N + 16))%nat with 0%nat by lia.
      pose proof D3 as Y. replace (d + 16) with (g + Z.of_nat j) in Y by lia.
      exact Y.
    - rewrite (BT (32 * N + 24)%nat 8%nat j) by lia.
      cbv beta iota.
      pose proof (D4 (j - (32 * N + 24))%nat ltac:(lia)) as Y.
      replace (d + 24 + Z.of_nat (j - (32 * N + 24))) with (g + Z.of_nat j) in Y by lia.
      exact Y. }
  lazymatch goal with
  | HGx : mem_grows (mrestrict (w_H W) mem') (mrestrict (w_H W) (ms_mem ms)) |- _ =>
    destruct (aw_state_keep W memc mem' (ms_mem ms) (spZ regs) g (d + 8) (d + 32) A HST
      ltac:(intros x Hx Hn; apply MF; lia) HGx ltac:(lia) ltac:(lia)) as (KS1 & KS2)
  end.
  pose proof (aw_frame_move W mem' (ms_mem ms) (spZ regs) regs (d + 8) (d + 32) HFR
    ltac:(intros x Hx Hn; apply MF; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HFR2.
  assert (HST2 : gsp_state W memc (ms_mem ms) (spZ regs) g B4).
  { split; [exact KS1|]. split; [exact KS2|]. split; [exact LB4|].
    apply aw_garr8_of_bytes. intros j Hj. rewrite LB4 in Hj. apply GB. exact Hj. }
  destruct (aw_keep11 fq _ _ _ regs' (gsp_extra Sg G) HS HAG ltac:(vm_compute; reflexivity))
    as (K2 & K3 & K4 & K8 & K9 & K19 & K20 & K22 & K23 & K24 & K27).
  cbn [ms_regs restrict mkst] in K2, K3, K4, K27.
  prreg HS (10%bv : bv 5) K10.
  pmkst HS.
  apply (gsp_epiA fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg
    (ms_regs ms) (ms_mem ms) _ B4 HCTX HJ HST2 HFR2).
  - rewrite K2. exact R2.
  - rewrite K3. exact R3.
  - rewrite K4. exact R4.
  - rewrite K27. exact R27.
  - rewrite K10, (GateModel.gm_app G Sg now N HFIND HgnN HN8). reflexivity.
  - rewrite (GateModel.gm_app G Sg now N HFIND HgnN HN8). reflexivity.
Qed.
Lemma gsp_app_a : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 20 = w64 (g + 256) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  getr regs' 23 = w64 (disco_classify_c.gn G) ->
  getr regs' 24 = w64 ((g + 256) / 8 + SB) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = None ->
  disco_classify_c.gn G < 8 ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19732)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md'
    HCTX HJ HST HFR R2 R3 R4 R27 R8 R9 R19 R21 R20 R22 R23 R24 HFIND Hlt8.
  pose proof HCTX as HC.
  destruct HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp &
    Hg0 & Hg8 & Hg63 & Hgside & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 &
    Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof HGok as (HGL & HGn & HGD).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ0 as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ &
    Hpres & Hstatic & _ & HQT).
  destruct Hstatic as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HST as (HSTk & HSTp & HSTl & HSTa).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8288) by reflexivity.
  rewrite WS in Hbud, Hgside, Hsside.
  assert (Hspr : 4096 <= spZ regs - 96 /\ spZ regs <= 2 ^ 47) by lia.
  assert (Hlo : kHighShadowEnd <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) by (rewrite WS; lia).
  assert (Hg47 : g + 264 <= 2 ^ 47) by (unfold amem_range in Hgapp; lia).
  assert (Hs47 : s + 24 <= 2 ^ 47) by (unfold amem_range in Hsapp; lia).
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (gsp_ew_reg regs' Sg G 19%bv 19 g eq_refl ltac:(lia) R19) as E19.
  pose proof (gsp_ew_reg regs' Sg G 9%bv 9 s eq_refl ltac:(lia) R9) as E9.
  pose proof (gsp_ew_reg regs' Sg G 23%bv 23 (disco_classify_c.gn G) eq_refl ltac:(lia) R23) as E23.
  pose proof (aw_band_state W memc mem' (spZ regs) g G HST Hlo Hgapp ltac:(lia)) as HBD.
  pose proof (aw_ra_band W memc mem' g 264 Hgra HBD ltac:(lia) ltac:(lia) Hgapp) as RAg.
  pose proof (aw_ra_band W memc mem' s 24 Hsra HBD ltac:(lia) ltac:(lia) Hsapp) as RAs.
  pose proof (aw_hull_band W memc mem' g 264 Hghull HBD ltac:(lia) ltac:(lia) Hgapp) as SHg.
  pose proof (aw_hull_band W memc mem' s 24 Hshull HBD ltac:(lia) ltac:(lia) Hsapp) as SHs.
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) mem') s (map bv_unsigned Sg)).
  { apply (garr8_frame SEGS _ _ s _ HSarr). intros a Ha. rewrite length_map, HSlen in Ha.
    apply aw_mbyte_of_aview. apply HSTk; [lia | rewrite WS; lia | lia]. }
  assert (VBg : base_val (EGSP regs' Sg G) (Some 19%nat) = g)
    by (cbn [base_val]; rewrite E19; apply unsigned_lit_small; lia).
  assert (HD20 : getr regs' 20 = sv_denot (EGSP regs' Sg G) (SOff 19 256))
    by (rewrite R20; symmetry; apply (gsp_denot_off regs' Sg G 19 g 256 E19); lia).
  assert (HD24 : getr regs' 24 = sv_denot (EGSP regs' Sg G) aw_xs8)
    by (rewrite R24, (aw_xs8_denot regs' Sg G g E19) by lia; reflexivity).
  assert (HD21 : getr regs' 21 = sv_denot (EGSP regs' Sg G) (SOff 32 0))
    by (rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HND : NoDup (map fst [(21%bv, SOff 32 0); (20%bv, SOff 19 256); (24%bv, aw_xs8)]))
    by (cbn [map fst]; apply gsp_nodup3; vm_compute; discriminate).
  assert (HUPD : Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot (EGSP regs' Sg G) (snd p))
    [(21%bv, SOff 32 0); (20%bv, SOff 19 256); (24%bv, aw_xs8)]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]); assumption. }
  assert (HRO : Forall (region_ok SEGS (EGSP regs' Sg G) (mrestrict (w_H W) mem'))
    [YP09.mkRegion (Some 19%nat) 256 260 256 260 []]).
  { apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite VBg. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply gsp_writable_of_apresent. apply HSTp. exact (proj2 (Hgwr (g + o) ltac:(lia))). }
  assert (HFOK : facts_ok (EGSP regs' Sg G) gsp_facts2).
  { split; [|split; exact I]. cbn [gsp_facts2 f_atoms atoms_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E19, E9, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia | reflexivity]. }
  pose proof (aw_st_ok fq 19732 [(21%bv, SOff 32 0); (20%bv, SOff 19 256); (24%bv, aw_xs8)] regs' W mem' Sg G
     [YP09.mkRegion (Some 19%nat) 256 260 256 260 []] gsp_facts2 HND HUPD eq_refl HRO (conj I I) HFOK) as HS.
  assert (SHOK : sh_ok SEGS GSP_SBx [mkSHE 19 0 264] (EGSP regs' Sg G) (mrestrict (w_H W) mem'))
    by (apply Forall_cons; [|apply Forall_nil]; apply (aw_shent regs' Sg G W mem' 19 g 264 E19); [lia | lia | exact Hgapp | exact RAg]).
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  pose (RUN := paj_run (fx := fq) B LAWS).
  paj_run_tok RUN HS HJ SHOK GSP_span.
  { cbn [ss_mem].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat g); [reflexivity | rewrite E19; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. exact (proj1 (Hgwr a ltac:(lia))). }
  assert (HNex : exists N : nat, disco_classify_c.gn G = Z.of_nat N)
    by (exists (Z.to_nat (disco_classify_c.gn G)); lia).
  destruct HNex as (N & HN).
  assert (DR : forall (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
            sv_denot (EGSP regs' Sg G) (SOff n 0) = getr regs' r).
  { intros r n Hn Hlt. cbn [sv_denot]. unfold EGSP. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs' _ n r Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  assert (HUz : U (EGSP regs' Sg G) (SAlu ALU_ADD (SOff 19 0) (SAlu ALU_SLL (SOff 23 0) (SLit 5)))
            = g + 32 * Z.of_nat N).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
    rewrite U_SLit, (U_atom _ 19 g E19), (U_atom _ 23 _ E23) by lia.
    change (Z.land (zcanon 5) 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
    rewrite (zcanon_id (disco_classify_c.gn G * 32)) by (unfold M64; lia).
    rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (HUd : sv_denot (EGSP regs' Sg G) (SAlu ALU_ADD (SOff 19 0) (SAlu ALU_SLL (SOff 23 0) (SLit 5)))
            = w64 (g + 32 * Z.of_nat N))
    by (rewrite denot_lit_U, HUz; reflexivity).
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (1%bv : bv 5) HS) as Q1.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (2%bv : bv 5) HS) as Q2.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (3%bv : bv 5) HS) as Q3.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (4%bv : bv 5) HS) as Q4.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (8%bv : bv 5) HS) as Q8.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (9%bv : bv 5) HS) as Q9.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (10%bv : bv 5) HS) as Q10.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (11%bv : bv 5) HS) as Q11.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (12%bv : bv 5) HS) as Q12.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (19%bv : bv 5) HS) as Q19.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (21%bv : bv 5) HS) as Q21.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (22%bv : bv 5) HS) as Q22.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ (27%bv : bv 5) HS) as Q27.
  repeat match goal with
  | H : getr _ _ = sv_denot _ (sr_get (ss_regs ?ssx) ?r) |- _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in H
  end.
  rewrite (DR 2%bv 2%nat eq_refl ltac:(lia)) in Q2.
  rewrite (DR 3%bv 3%nat eq_refl ltac:(lia)) in Q3.
  rewrite (DR 4%bv 4%nat eq_refl ltac:(lia)) in Q4.
  rewrite (DR 8%bv 8%nat eq_refl ltac:(lia)) in Q8.
  rewrite (DR 9%bv 9%nat eq_refl ltac:(lia)) in Q9.
  rewrite (DR 9%bv 9%nat eq_refl ltac:(lia)) in Q11.
  rewrite (DR 22%bv 22%nat eq_refl ltac:(lia)) in Q22.
  rewrite (DR 27%bv 27%nat eq_refl ltac:(lia)) in Q27.
  rewrite HUd in Q10, Q19.
  change (SOff 240 19772) with (SOff A_TEXT 19772) in Q1. rewrite (codeptr_val _ 19772 HEI) in Q1.
  assert (Ex12 : getr (ms_regs ms) 12 = w64 6) by (rewrite Q12; reflexivity).
  assert (Ex11 : getr (ms_regs ms) 11 = w64 s) by (rewrite Q11; exact R9).
  assert (Ex3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3; exact R3).
  assert (Ex4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4; exact R4).
  assert (HspT : spZ (ms_regs ms) = sp0 + (spZ regs - 96 - sp0))
    by (unfold spZ at 1; rewrite Q2, R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (Hom16 : (spZ regs - 96 - sp0) mod 16 = 0).
  { assert (Hm : spZ regs - 96 - sp0 = 16 * (spZ regs / 16 - 6 - sp0 / 16)).
    { pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
    rewrite Hm, Z.mul_comm. apply Z.mod_mul. lia. }
  assert (Hret : YK0s.ret_ok (Z_to_bv 64 (BASE + 19772))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as HR0.
  cbn [ms_mem restrict] in HR0.
  assert (HCV : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (g + 256) 4 (disco_classify_c.gn G + 1)).
  { apply (field_of_region (EGSP regs' Sg G) _ 19 g _ _ _ _ _ 256 4%N (SOff 23 1) _ HR0).
    - rewrite E19. apply unsigned_lit_small. lia.
    - cbn [In]. left. reflexivity.
    - rewrite (gsp_denot_off regs' Sg G 23 (disco_classify_c.gn G) 1 E23) by lia. reflexivity.
    - change (2 ^ (8 * Z.of_N 4)) with 4294967296. lia.
    - cbn. lia. }
  assert (HMT : forall x, 0 <= x < 2 ^ 64 -> ~ (g + 256 <= x < g + 260) ->
            mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) x = mbyte SEGS (mrestrict (w_H W) mem') x).
  { intros x Hx Hn. apply (aw_mbyte_frame W _ _ mem' (ms_mem ms) x HFr); [|exact Hx].
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. rewrite VBg in Hr. lia. }
  assert (HBT : forall x, SHADOW_OFF <= x < kHighShadowEnd ->
            aview SEGS (w_H W) (ms_mem ms) x = aview SEGS (w_H W) mem' x).
  { intros x Hx. apply aw_aview_of_mbyte. apply HMT; unfold amem_range in Hgapp; unfold SHADOW_OFF in *; lia. }
  pose proof (aw_ra_band W mem' (ms_mem ms) g 264 RAg HBT ltac:(lia) ltac:(lia) Hgapp) as RTg.
  pose proof (aw_ra_band W mem' (ms_mem ms) s 24 RAs HBT ltac:(lia) ltac:(lia) Hsapp) as RTs.
  pose proof (aw_hull_band W mem' (ms_mem ms) g 264 SHg HBT ltac:(lia) ltac:(lia) Hgapp) as STg.
  pose proof (aw_hull_band W mem' (ms_mem ms) s 24 SHs HBT ltac:(lia) ltac:(lia) Hsapp) as STs.
  assert (A_dest : forall a, g + 32 * Z.of_nat N <= a < g + 32 * Z.of_nat N + 6 ->
      awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
      ~ (sp0 + (spZ regs - 96 - sp0) - ESTACK <= a < sp0 + (spZ regs - 96 - sp0))).
  { intros a Ha. split; [exact (proj1 (Hgwr a ltac:(lia))) | unfold ESTACK; lia]. }
  assert (A_amd : amem_range (g + 32 * Z.of_nat N) 6) by (apply (aw_amem_sub g 264); [exact Hgapp | lia | lia | lia]).
  assert (A_rad : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (g + 32 * Z.of_nat N) 6)
    by (apply (aw_ra_sub _ g 264); [exact RTg | lia | lia]).
  assert (A_hud : 0 < 6 -> shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) (g + 32 * Z.of_nat N) 6)
    by (intros _; apply (aw_hull_sub _ g 264); [exact STg | lia | lia | lia]).
  assert (A_cpy : 0 <= s /\ s + 6 <= 2 ^ 63 /\ src_ok SEGS W (ms_regs ms) (ms_mem ms) s 6 /\
      (g + 32 * Z.of_nat N + 6 <= s \/ s + 6 <= g + 32 * Z.of_nat N) /\ amem_range s 6 /\
      range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF s 6 /\
      (0 < 6 -> shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) s 6)).
  { split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite (aw_aview_of_mbyte W mem' (ms_mem ms) a (HMT a ltac:(lia) ltac:(lia))).
        replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia.
        rewrite (gsp_aview_byte W mem' s Sg _ HSa') by lia. discriminate.
      - rewrite HspT. unfold ESTACK. lia. }
    split; [lia|]. split; [apply (aw_amem_sub s 24); [exact Hsapp | lia | lia | lia]|].
    split; [apply (aw_ra_sub _ s 24); [exact RTs | lia | lia]|].
    intros _. apply (aw_hull_sub _ s 24); [exact STs | lia | lia | lia]. }
  pose proof (pa_segs_low) as Hsegs.
  pmkst HS.
  eapply SRr_bind.
  { exact (aj_intrin_atS (fx := fq) SEGS B LAWS Hsegs OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W
      (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (g + 32 * Z.of_nat N) s 6
      (spZ regs - 96 - sp0) (Z_to_bv 64 (BASE + 19772)) HJ Q10 Ex11 Ex12
      ltac:(lia) ltac:(lia) ltac:(lia) HspT Hom16 ltac:(lia) ltac:(unfold ESTACK; lia) Ex3 Ex4 Q1 Hret
      A_dest A_amd A_rad A_hud A_cpy). }
  cbv beta. intros W2 c2 _ HPP.
  destruct HPP as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10' & Hcpy & Hfr2 & Hpres2 & Hsbm).
  assert (HM2F : forall x, spZ regs - 96 <= x < spZ regs ->
      mbyte SEGS (mrestrict (w_H W) mem2) x = mbyte SEGS (mrestrict (w_H W) mem') x).
  { intros x Hx. apply aw_mbyte_of_aview. rewrite Hfr2 by (unfold ESTACK; lia).
    apply aw_aview_of_mbyte. apply HMT; lia. }
  assert (HFR2 : gsp_frame W mem2 (spZ regs) regs).
  { pose proof HFR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
    assert (HVM : forall a n v, spZ regs - 96 <= a -> a + Z.of_nat n <= spZ regs ->
      val_mem SEGS (mrestrict (w_H W) mem') a n v -> val_mem SEGS (mrestrict (w_H W) mem2) a n v).
    { intros a n v H1 H2 HVm kk Hkk. rewrite HM2F by lia. apply HVm. exact Hkk. }
    unfold gsp_frame. repeat split; (eapply HVM; [lia | lia | eassumption]). }
  assert (HL4 : length (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1))) = 4%nat) by reflexivity.
  assert (HL6 : length (CtrlParsed.fld Sg 0 6) = 6%nat) by (apply GateModel.length_fld; lia).
  assert (HG1L : length (Mem.upd_bytes G 256 (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1)))) = 264%nat)
    by (rewrite Mem.upd_bytes_length; [exact HGlen | rewrite HL4; lia]).
  assert (HAL : length (aw_appended G Sg N) = 264%nat)
    by (unfold aw_appended; rewrite Mem.upd_bytes_length; [exact HG1L | rewrite HL6, HG1L; lia]).
  assert (HA1 : forall j, (32 * N <= j < 32 * N + 6)%nat ->
      nth j (aw_appended G Sg N) (CtrlParsed.zb 0) = nth (j - 32 * N) Sg (CtrlParsed.zb 0)).
  { intros j Hj. apply nth_error_nth. unfold aw_appended.
    rewrite Mem.upd_bytes_nth by (rewrite ?HL6, ?HG1L; lia). rewrite HL6.
    destruct (Nat.leb_spec0 (32 * N) j); [|exfalso; lia].
    destruct (Nat.ltb_spec0 j (32 * N + 6)); [|exfalso; lia]. cbn [andb].
    rewrite GateModel.nth_error_fld. destruct (Nat.ltb_spec0 (j - 32 * N) 6); [|exfalso; lia].
    apply nth_error_nth'. lia. }
  assert (HA2 : forall j, (256 <= j < 260)%nat ->
      nth j (aw_appended G Sg N) (CtrlParsed.zb 0) =
      byte_of_word (Z_to_bv 64 (Z.of_nat N + 1)) (Z.of_nat (j - 256))).
  { intros j Hj. rewrite <- (aw_nth_le4 _ (j - 256)) by lia. rewrite Nat2Z.id. apply nth_error_nth.
    unfold aw_appended. rewrite Mem.upd_bytes_nth by (rewrite ?HL6, ?HG1L; lia). rewrite HL6.
    destruct (Nat.leb_spec0 (32 * N) j); destruct (Nat.ltb_spec0 j (32 * N + 6)); cbn [andb]; try (exfalso; lia).
    all: rewrite Mem.upd_bytes_nth by (rewrite ?HL4; lia); rewrite HL4;
      destruct (Nat.leb_spec0 256 j); [|exfalso; lia]; destruct (Nat.ltb_spec0 j (256 + 4)); [|exfalso; lia];
      cbn [andb]; apply nth_error_nth'; rewrite HL4; lia. }
  assert (HA3 : forall j, (j < 264)%nat -> ~ (32 * N <= j < 32 * N + 6)%nat -> ~ (256 <= j < 260)%nat ->
      nth j (aw_appended G Sg N) (CtrlParsed.zb 0) = nth j G (CtrlParsed.zb 0)).
  { intros j Hj H1 H2. apply nth_error_nth. unfold aw_appended.
    rewrite Mem.upd_bytes_nth by (rewrite ?HL6, ?HG1L; lia). rewrite HL6.
    destruct (Nat.leb_spec0 (32 * N) j); destruct (Nat.ltb_spec0 j (32 * N + 6)); cbn [andb]; try (exfalso; lia).
    all: rewrite Mem.upd_bytes_nth by (rewrite ?HL4; lia); rewrite HL4;
      destruct (Nat.leb_spec0 256 j); destruct (Nat.ltb_spec0 j (256 + 4)); cbn [andb]; try (exfalso; lia);
      apply nth_error_nth'; lia. }
  assert (HGA2 : garr8 SEGS (mrestrict (w_H W) mem2) g (map bv_unsigned (aw_appended G Sg N))).
  { apply aw_garr8_of_bytes. intros j Hj. rewrite HAL in Hj.
    assert (Hcase : (32 * N <= j < 32 * N + 6)%nat \/ (256 <= j < 260)%nat \/
                    (~ (32 * N <= j < 32 * N + 6)%nat /\ ~ (256 <= j < 260)%nat)) by lia.
    destruct Hcase as [Hc | [Hc | (Hc1 & Hc2)]].
    - rewrite (HA1 j Hc). apply aw_mbyte_of_byte.
      replace (g + Z.of_nat j) with (g + 32 * Z.of_nat N + Z.of_nat (j - 32 * N)) by lia.
      rewrite (Hcpy (Z.of_nat (j - 32 * N))) by lia.
      rewrite (aw_aview_of_mbyte W mem' (ms_mem ms) (s + Z.of_nat (j - 32 * N))
                 (HMT (s + Z.of_nat (j - 32 * N)) ltac:(lia) ltac:(lia))).
      exact (gsp_aview_byte W mem' s Sg (j - 32 * N) HSa' ltac:(lia)).
    - rewrite (HA2 j Hc).
      rewrite (aw_mbyte_of_aview W (ms_mem ms) mem2 (g + Z.of_nat j)
                 (Hfr2 (g + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia))).
      replace (g + Z.of_nat j) with (g + 256 + Z.of_nat (j - 256)) by lia.
      rewrite (HCV (j - 256)%nat ltac:(lia)). f_equal.
      unfold YO0f.le_byte, byte_of_word. rewrite HN.
      rewrite (unsigned_lit_small (Z.of_nat N + 1)) by lia.
      rewrite (Z.mod_small (Z.of_nat N + 1) (2 ^ (8 * Z.of_nat 4)))
        by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
      apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      apply Zmod_mod.
    - rewrite (HA3 j Hj Hc1 Hc2). apply aw_mbyte_of_byte.
      rewrite (Hfr2 (g + Z.of_nat j)) by (unfold ESTACK; lia).
      rewrite (aw_aview_of_mbyte W mem' (ms_mem ms) (g + Z.of_nat j) (HMT (g + Z.of_nat j) ltac:(lia) ltac:(lia))).
      exact (gsp_aview_byte W mem' g G j HSTa ltac:(lia)). }
  assert (HST2 : gsp_state W memc mem2 (spZ regs) g (aw_appended G Sg N)).
  { split; [|split; [|split]].
    - intros a Ha Hn Hg. rewrite WS in Hn.
      rewrite Hfr2 by (unfold ESTACK; lia).
      rewrite (aw_aview_of_mbyte W mem' (ms_mem ms) a (HMT a ltac:(lia) ltac:(lia))).
      apply HSTk; [exact Ha | rewrite WS; exact Hn | exact Hg].
    - intros a Hp. apply Hpres2. apply (gsp_apresent_grow W mem' (ms_mem ms) a HG). apply HSTp. exact Hp.
    - exact HAL.
    - exact HGA2. }
  assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  apply (gsp_app_b fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs2 mem2 md2 N
    (g + 32 * Z.of_nat N) HCTX HJ2 HST2 HFR2).
  - rewrite P2, Q2. exact R2.
  - rewrite P3, Q3. exact R3.
  - rewrite P4, Q4. exact R4.
  - rewrite P27, Q27. exact R27.
  - rewrite P8, Q8. exact R8.
  - rewrite P9, Q9. exact R9.
  - rewrite P19, Q19. reflexivity.
  - rewrite P21, Q21. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite P22, Q22. exact R22.
  - exact HFIND.
  - exact HN.
  - lia.
  - reflexivity.
Qed.
Lemma gsp_ex : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 20 = w64 (g + 256) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  getr regs' 23 = w64 (disco_classify_c.gn G) ->
  getr regs' 24 = w64 ((g + 256) / 8 + SB) ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = None ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19724)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md'
    HCTX HJ HST HFR R2 R3 R4 R27 R8 R9 R19 R21 R20 R22 R23 R24 HFIND.
  pose proof HCTX as HC.
  destruct HC as (HJ0 & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp &
    Hg0 & Hg8 & Hg63 & Hgside & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 &
    Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof HGok as (HGL & HGn & HGD).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ0 as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ &
    Hpres & Hstatic & _ & HQT).
  destruct Hstatic as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *.
  assert (Hspr : 4096 <= spZ regs - 96 /\ spZ regs <= 2 ^ 47) by lia.
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (gsp_ew_reg regs' Sg G 23%bv 23 (disco_classify_c.gn G) eq_refl ltac:(lia) R23) as E23.
  pose proof (aw_st_ok fq 19724 [(21%bv, SOff 32 0)] regs' W mem' Sg G [] (mkFacts [] [] [])
     ltac:(cbn [map fst]; apply gsp_nodup1)
     ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split; [reflexivity|];
           rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
     ltac:(reflexivity) (Forall_nil _) I (conj I (conj I I))) as HS.
  assert (SHOK : sh_ok SEGS GSP_SBx [] (EGSP regs' Sg G) (mrestrict (w_H W) mem'))
    by (apply Forall_nil).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (BR := paj_branch (PI := PI)).
  assert (HD23 : sv_denot (EGSP regs' Sg G) (SOff 23 0) = Z_to_bv 64 (disco_classify_c.gn G))
    by (cbn [sv_denot]; rewrite E23, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
  assert (HD7 : sv_denot (EGSP regs' Sg G) (SLit 7) = Z_to_bv 64 7) by reflexivity.
  assert (HAG : env_agree 32 (Ereg regs' (gsp_extra Sg G)) (EGSP regs' Sg G))
    by (split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  apply (BR W (EGSP regs' Sg G) (mkSS 19724 (gsp_sr [(21%bv, SOff 32 0)]) [] None (mkFacts [] [] []))
    (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19724)) mem' (seg_rom SEGS)) md' _
    BC_LT (SLit 7) (SOff 23 0) HS); clear HS; intros Hc HS;
  rewrite HD7, HD23, (aw_branch_lt_lit 7 (disco_classify_c.gn G) ltac:(lia) ltac:(lia)) in Hc.
  - paj_run_to_tok RUNTO HS HJ SHOK GSP_span 20108.
    { apply awr_ok_nil. }
    apply Z.ltb_lt in Hc.
    lazymatch goal with
    | HFrx : frame_of ?Ev ?rs (mrestrict (w_H W) mem') (mrestrict (w_H W) ?m2),
      HGw : mem_grows (mrestrict (w_H W) mem') (mrestrict (w_H W) ?m2) |- _ =>
      destruct (aw_ex_step W memc mem' m2 regs g G HST HFR
        ltac:(intros x Hx; apply (aw_mbyte_frame W Ev rs mem' m2 x HFrx
                ltac:(intros (rr & Hin & _); cbn in Hin; destruct Hin) Hx))
        HGw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (HST2 & HFR2)
    end.
    destruct (aw_keep11 fq _ _ _ regs' (gsp_extra Sg G) HS HAG ltac:(vm_compute; reflexivity))
      as (K2 & K3 & K4 & K8 & K9 & K19 & K20 & K22 & K23 & K24 & K27).
    cbn [ms_regs restrict mkst] in K2, K3, K4, K8, K9, K19, K20, K22, K23, K24, K27.
    pmkst HS.
    eapply gsp_ret0A; try eassumption.
    + rewrite K2. exact R2.
    + rewrite K3. exact R3.
    + rewrite K4. exact R4.
    + rewrite K27. exact R27.
    + apply (GateModel.gm_full G Sg now HFIND ltac:(lia)).
  - paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19732.
    { apply awr_ok_nil. }
    apply Z.ltb_ge in Hc.
    lazymatch goal with
    | HFrx : frame_of ?Ev ?rs (mrestrict (w_H W) mem') (mrestrict (w_H W) ?m2),
      HGw : mem_grows (mrestrict (w_H W) mem') (mrestrict (w_H W) ?m2) |- _ =>
      destruct (aw_ex_step W memc mem' m2 regs g G HST HFR
        ltac:(intros x Hx; apply (aw_mbyte_frame W Ev rs mem' m2 x HFrx
                ltac:(intros (rr & Hin & _); cbn in Hin; destruct Hin) Hx))
        HGw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (HST2 & HFR2)
    end.
    destruct (aw_keep11 fq _ _ _ regs' (gsp_extra Sg G) HS HAG ltac:(vm_compute; reflexivity))
      as (K2 & K3 & K4 & K8 & K9 & K19 & K20 & K22 & K23 & K24 & K27).
    cbn [ms_regs restrict mkst] in K2, K3, K4, K8, K9, K19, K20, K22, K23, K24, K27.
    prreg HS (21%bv : bv 5) K21.
    cbn [ms_regs restrict mkst] in K21.
    rewrite E32 in K21.
    pmkst HS.
    eapply gsp_app_a; try eassumption.
    + rewrite K2. exact R2.
    + rewrite K3. exact R3.
    + rewrite K4. exact R4.
    + rewrite K27. exact R27.
    + rewrite K8. exact R8.
    + rewrite K9. exact R9.
    + rewrite K19. exact R19.
    + rewrite K20. exact R20.
    + rewrite K22. exact R22.
    + rewrite K23. exact R23.
    + rewrite K24. exact R24.
    + lia.
Qed.
Definition gsp_loop_stmt (m : nat) : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  Z.of_nat (Z.to_nat (disco_classify_c.gn G)) - Z.of_nat i <= Z.of_nat m ->
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 20 = w64 (g + 256) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  getr regs' 23 = w64 (disco_classify_c.gn G) ->
  getr regs' 24 = w64 ((g + 256) / 8 + SB) ->
  getr regs' 25 = w64 (32 * Z.of_nat i) ->
  getr regs' 26 = w64 (32 * disco_classify_c.gn G) ->
  Z.of_nat i < disco_classify_c.gn G ->
  (forall j, (j < i)%nat -> CtrlParsed.bytes_eqb (disco_classify_c.gmac G j) (CtrlParsed.fld Sg 0 6) = false) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19692)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Lemma gsp_af_beq : forall (regs : bvmap 5 word) (Sg G : list byte) (b : bool),
  branch_taken BC_EQ (sv_denot (EGSP regs Sg G) (SOff 10 0)) (sv_denot (EGSP regs Sg G) (SLit 0)) = b ->
  (getr regs 10 = w64 0 <-> b = true).
Proof.
  intros regs Sg G b H. rewrite branch_eq_U in H.
  assert (E0 : U (EGSP regs Sg G) (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
  rewrite E0 in H.
  unfold U in H. rewrite (gsp_denot_reg regs Sg G 10%bv 10 eq_refl ltac:(lia)) in H. subst b.
  split; intros H.
  - rewrite H. reflexivity.
  - apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity.
Qed.
Lemma gsp_after : forall m : nat, gsp_loop_stmt m ->
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat) (v : word),
  Z.of_nat (Z.to_nat (disco_classify_c.gn G)) - Z.of_nat i <= Z.of_nat (Datatypes.S m) ->
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) ->
  getr regs' 20 = w64 (g + 256) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  getr regs' 23 = w64 (disco_classify_c.gn G) ->
  getr regs' 24 = w64 ((g + 256) / 8 + SB) ->
  getr regs' 25 = w64 (32 * Z.of_nat i) ->
  getr regs' 26 = w64 (32 * disco_classify_c.gn G) ->
  Z.of_nat i < disco_classify_c.gn G ->
  (forall j, (j < i)%nat -> CtrlParsed.bytes_eqb (disco_classify_c.gmac G j) (CtrlParsed.fld Sg 0 6) = false) ->
  getr regs' 10 = v ->
  (v = w64 0 <-> CtrlParsed.bytes_eqb (disco_classify_c.gmac G i) (CtrlParsed.fld Sg 0 6) = true) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19712)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros m IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i v
    HF HC HJ HST HFR R2 R3 R4 R27 R8 R9 R19 R21 R18 R20 R22 R23 R24 R25 R26 Hi Hpre R10 Hv.
  unfold gsp_loop_stmt in IH.
  pose proof HC as (HJc & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgside
    & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 & Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof (gsp_stk_lo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJc) as (Hc0 & Hc1 & _).
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  destruct (gsp_gn G HGok) as (Hfn & Hn8).
  pose proof (gsp_ew_reg regs' Sg G 25%bv 25 _ eq_refl ltac:(lia) R25) as E25.
  pose proof (gsp_ew_reg regs' Sg G 26%bv 26 _ eq_refl ltac:(lia) R26) as E26.
  assert (Hg47 : g + 264 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp; lia).
  destruct (gsp_seatR fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' 19712
    [(21%bv, SOff 32 0)] HC HST
    ltac:(cbn [map fst]; apply gsp_nodup1)
    ltac:(apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    R19 R9 R21) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  assert (Hsp96 : 96 <= spZ regs) by (unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia).
  assert (Hsp64 : spZ regs <= 2 ^ 64) by lia.
  assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  psrr_branch_tok RUN BR HS SHOK GSP_span.
  - pose proof (proj2 (gsp_af_beq regs' Sg G true Hc) eq_refl) as Hv0. rewrite R10 in Hv0.
    pose proof (proj1 Hv Hv0) as Hbt. clear Hc.
    assert (Hfd : GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i).
    { apply GateModel.gfind_Some_intro; [lia | intros j' Hj'; apply Hpre; lia | exact Hbt]. }
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19920.
    { awr_ok_tac. }
    gkeep HST HFR.
    qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4.
    qatom HS (27%bv : bv 5) 27%nat Q27. qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9.
    qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (21%bv : bv 5) Q21.
    qatom HS (18%bv : bv 5) 18%nat Q18. qatom HS (22%bv : bv 5) 22%nat Q22.
    pmkst HS.
    eapply (gsp_arm_found fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ i HC HJ HST HFR);
      [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
        | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
        | rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Q18; exact R18 | rewrite Q22; exact R22 | exact Hfd ].
  - assert (Hbf : CtrlParsed.bytes_eqb (disco_classify_c.gmac G i) (CtrlParsed.fld Sg 0 6) = false).
    { destruct (CtrlParsed.bytes_eqb (disco_classify_c.gmac G i) (CtrlParsed.fld Sg 0 6)) eqn:Eb; [|reflexivity].
      pose proof (proj2 Hv eq_refl) as Hv0. rewrite <- R10 in Hv0.
      pose proof (proj1 (gsp_af_beq regs' Sg G false Hc) Hv0) as Hff. discriminate Hff. }
    assert (Hlt : forall j, (j < Datatypes.S i)%nat ->
      CtrlParsed.bytes_eqb (disco_classify_c.gmac G j) (CtrlParsed.fld Sg 0 6) = false).
    { intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact Hbf | apply Hpre; lia]. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK GSP_span.
    { awr_ok_tac. }
    gkeep HST HFR.
    psrr_branch_tok RUN BR HS SHOK GSP_span.
    + rewrite branch_ne_U, (U_atom _ 26 _ E26), (U_atom_off _ 25 _ 32 E25) in Hc by lia.
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19692.
      { awr_ok_tac. }
      gkeep HST HFR.
      qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4.
      qatom HS (27%bv : bv 5) 27%nat Q27. qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9.
      qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (21%bv : bv 5) Q21.
      qatom HS (20%bv : bv 5) 20%nat Q20. qatom HS (22%bv : bv 5) 22%nat Q22. qatom HS (23%bv : bv 5) 23%nat Q23.
      qatom HS (24%bv : bv 5) 24%nat Q24. qreg HS (25%bv : bv 5) Q25. qatom HS (26%bv : bv 5) 26%nat Q26.
      pmkst HS.
      eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ (Datatypes.S i)
        ltac:(lia) HC HJ HST HFR);
        [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
        | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
        | rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | rewrite Q20; exact R20 | rewrite Q22; exact R22 | rewrite Q23; exact R23 | rewrite Q24; exact R24
        | rewrite Q25, (gsp_denot_off regs' Sg G 25 _ 32 E25) by lia; f_equal; lia
        | rewrite Q26; exact R26 | lia | exact Hlt ].
    + rewrite branch_ne_U, (U_atom _ 26 _ E26), (U_atom_off _ 25 _ 32 E25) in Hc by lia.
      apply negb_false_iff, Z.eqb_eq in Hc.
      assert (Hnf : GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = None).
      { apply GateModel.gfind_None_intro. intros j Hj. apply Hlt. lia. }
      paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19724.
      { awr_ok_tac. }
      gkeep HST HFR.
      qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4.
      qatom HS (27%bv : bv 5) 27%nat Q27. qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9.
      qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (21%bv : bv 5) Q21.
      qatom HS (20%bv : bv 5) 20%nat Q20. qatom HS (22%bv : bv 5) 22%nat Q22. qatom HS (23%bv : bv 5) 23%nat Q23.
      qatom HS (24%bv : bv 5) 24%nat Q24.
      pmkst HS.
      eapply (gsp_ex fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ HC HJ HST HFR);
        [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
        | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
        | rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | rewrite Q20; exact R20 | rewrite Q22; exact R22 | rewrite Q23; exact R23 | rewrite Q24; exact R24
        | exact Hnf ].
Qed.
Lemma gsp_loop_step : forall m, gsp_loop_stmt m -> gsp_loop_stmt (Datatypes.S m).
Proof.
  intros m IH. unfold gsp_loop_stmt.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i
    Hfuel HC HJ HST HFR R2 R3 R4 R27 R8 R9 R19 R21 R20 R22 R23 R24 R25 R26 Hi Hb.
  pose proof HC as (HJc & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgside
    & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 & Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof (gsp_stk_lo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJc) as (Hc0 & Hc1 & Hc16).
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (gsp_ew_reg regs' Sg G 19%bv 19 g eq_refl ltac:(lia) R19) as E19.
  pose proof (gsp_ew_reg regs' Sg G 25%bv 25 (32 * Z.of_nat i) eq_refl ltac:(lia) R25) as E25.
  destruct (gsp_gn G HGok) as (Hfn & Hn8).
  assert (Hg47 : g + 264 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp; lia).
  destruct (gsp_seatR fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' 19692
    [(21%bv, SOff 32 0)] HC HST
    ltac:(cbn [map fst]; apply gsp_nodup1)
    ltac:(apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    R19 R9 R21) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  pose (RUN := paj_run (fx := fq) B LAWS).
  assert (Hsp96 : 96 <= spZ regs) by (unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia).
  assert (Hsp64 : spZ regs <= 2 ^ 64) by lia.
  assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  paj_run_tok RUN HS HJ SHOK GSP_span.
  { awr_ok_tac. }
  gkeep HST HFR.

  qregc HS (10%bv : bv 5) Qa0. qregc HS (11%bv : bv 5) Qa1. rewrite (gsp_denot_reg _ _ _ (9%bv : bv 5) 9 eq_refl ltac:(lia)) in Qa1. qregc HS (12%bv : bv 5) Qa2. qregc HS (1%bv : bv 5) Qra.
  qatomc HS (2%bv : bv 5) 2%nat Q2. qatomc HS (3%bv : bv 5) 3%nat Q3. qatomc HS (4%bv : bv 5) 4%nat Q4.
  qatomc HS (27%bv : bv 5) 27%nat Q27. qatomc HS (8%bv : bv 5) 8%nat Q8. qatomc HS (9%bv : bv 5) 9%nat Q9.
  qatomc HS (19%bv : bv 5) 19%nat Q19. qregc HS (21%bv : bv 5) Q21. qregc HS (18%bv : bv 5) Q18.
  qatomc HS (20%bv : bv 5) 20%nat Q20. qatomc HS (22%bv : bv 5) 22%nat Q22. qatomc HS (23%bv : bv 5) 23%nat Q23.
  qatomc HS (24%bv : bv 5) 24%nat Q24. qatomc HS (25%bv : bv 5) 25%nat Q25. qatomc HS (26%bv : bv 5) 26%nat Q26.
  change (SOff 240 19712) with (SOff A_TEXT 19712) in Qra. rewrite (codeptr_val _ 19712 HEI) in Qra.
  assert (Hi8 : Z.of_nat i < 8) by lia.
  assert (Ex : getr (ms_regs ms) 10 = w64 (g + 32 * Z.of_nat i))
    by (rewrite Qa0; apply gsp_w64U; apply (gsp_U_add2 _ 19 25 _ _ E19 E25); lia).
  assert (Ex18 : getr (ms_regs ms) 18 = w64 (g + 32 * Z.of_nat i))
    by (rewrite Q18; apply gsp_w64U; apply (gsp_U_add2 _ 19 25 _ _ E19 E25); lia).
  assert (Ex21 : getr (ms_regs ms) 21 = w64 SB)
    by (rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (Ex12 : getr (ms_regs ms) 12 = w64 6) by (rewrite Qa2; reflexivity).
  assert (HspT : spZ (ms_regs ms) = sp0 + (spZ regs - 96 - sp0))
    by (unfold spZ at 1; rewrite Q2, R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
  pose proof HST as (Hkeep & Hpres & HBl & HBa).
  pose proof (gsp_view_G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg (ms_mem ms) HC HST) as HV.
  assert (Hlo : kHighShadowEnd <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) by (unfold kHighShadowEnd; lia).
  assert (Hs47 : s + 24 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hsapp; lia).
  assert (HSa' : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) s (map bv_unsigned Sg)).
  { apply (garr8_frame SEGS _ _ s _ HSarr). intros a Ha. rewrite length_map, HSlen in Ha.
    apply gsp_mbyte_of_aview. apply HV; [lia|]. destruct Hsside; lia. }
  pose proof (range_addressable_kept_win _ _ _ _ g 264 HV Hlo ltac:(lia) Hg47 Hgra) as RAg.
  pose proof (range_addressable_kept_win _ _ _ _ s 24 HV Hlo ltac:(lia) Hs47 Hsra) as RAs.
  pose proof (shadow_hull_vis_kept_win _ _ _ _ g 264 HV Hlo ltac:(lia) Hg47 ltac:(lia) Hghull) as SHg.
  pose proof (shadow_hull_vis_kept_win _ _ _ _ s 24 HV Hlo ltac:(lia) Hs47 ltac:(lia) Hshull) as SHs.
  pose proof (pa_segs_low) as Hsegs.
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_bcmp_at (fx := fq) SEGS B LAWS Hsegs (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W
      (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (g + 32 * Z.of_nat i) s 6
      (spZ regs - 96 - sp0) (Z_to_bv 64 (BASE + 19712)) HJ Ex ltac:(rewrite Qa1; exact R9) Ex12).
    - lia. - lia. - lia. - lia. - lia.
    - exact HspT.
    - assert (Hm : spZ regs - 96 - sp0 = 16 * (spZ regs / 16 - 6 - sp0 / 16)).
      { pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
      rewrite Hm, Z.mul_comm. apply Z.mod_mul. lia.
    - lia.
    - unfold REAC_DISCO_GATE_SHOULD_PUSH_STK in Hbud. lia.
    - rewrite Q3. exact R3.
    - rewrite Q4. exact R4.
    - exact Qra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + replace a with (g + Z.of_nat (Z.to_nat (a - g))) by lia.
        rewrite (gsp_aview_byte W (ms_mem ms) g G _ HBa) by lia. discriminate.
      + rewrite HspT. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia.
    - intros a Ha. split.
      + replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia.
        rewrite (gsp_aview_byte W (ms_mem ms) s Sg _ HSa') by lia. discriminate.
      + rewrite HspT. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia.
    - intros a Ha. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia.
    - intros a Ha. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
    - apply (range_addressable_sub _ _ g 264); [exact RAg | lia | lia].
    - intros _. apply (gsp_hull_sub _ g 264); [exact SHg | lia | lia | lia | lia].
    - apply (range_addressable_sub _ _ s 24); [exact RAs | lia | lia].
    - intros _. apply (gsp_hull_sub _ s 24); [exact SHs | lia | lia | lia | lia]. }
  cbv beta. intros W2 c2 _ HPP. destruct HPP as (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
  destruct (gsp_keep_win W (ms_mem ms) mem2 memc (spZ regs) g (sp0 + (spZ regs - 96 - sp0) - 2 * ESTACK)
    (sp0 + (spZ regs - 96 - sp0)) G regs Hfr2 Hpres2
    ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia) ltac:(lia) ltac:(lia) HST HFR) as [HST2 HFR2].
  assert (HM : v = w64 0 <-> CtrlParsed.bytes_eqb (disco_classify_c.gmac G i) (CtrlParsed.fld Sg 0 6) = true).
  { rewrite Hcmp. unfold disco_classify_c.gmac.
    rewrite <- (gsp_cmp_iff W (ms_mem ms) G Sg g s (32 * i) 0 6 HBa HSa' ltac:(lia) ltac:(lia)).
    split; intros HH i0 Hi0; specialize (HH i0 Hi0).
    - replace (g + Z.of_nat (32 * i) + i0) with (g + 32 * Z.of_nat i + i0) by lia.
      replace (s + Z.of_nat 0 + i0) with (s + i0) by lia. exact HH.
    - replace (g + 32 * Z.of_nat i + i0) with (g + Z.of_nat (32 * i) + i0) by lia.
      replace (s + i0) with (s + Z.of_nat 0 + i0) by lia. exact HH. }
  assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
  assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
  assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  apply (gsp_after m IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs2 mem2 md2 i v
    Hfuel HC HJ2 HST2 HFR2).
  - rewrite P2, Q2. exact R2.
  - rewrite P3, Q3. exact R3.
  - rewrite P4, Q4. exact R4.
  - rewrite P27, Q27. exact R27.
  - rewrite P8, Q8. exact R8.
  - rewrite P9, Q9. exact R9.
  - rewrite P19, Q19. exact R19.
  - rewrite P21. exact Ex21.
  - rewrite P18. exact Ex18.
  - rewrite P20, Q20. exact R20.
  - rewrite P22, Q22. exact R22.
  - rewrite P23, Q23. exact R23.
  - rewrite P24, Q24. exact R24.
  - rewrite P25, Q25. exact R25.
  - rewrite P26, Q26. exact R26.
  - exact Hi.
  - exact Hb.
  - exact Hv.
  - exact HM.
Qed.
Lemma gsp_loop_all : forall m, gsp_loop_stmt m.
Proof.
  induction m as [|m IH].
  - unfold gsp_loop_stmt. intros. exfalso. lia.
  - exact (gsp_loop_step m IH).
Qed.
Lemma gsp_loop : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (i : nat),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 20 = w64 (g + 256) ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  getr regs' 23 = w64 (disco_classify_c.gn G) ->
  getr regs' 24 = w64 ((g + 256) / 8 + SB) ->
  getr regs' 25 = w64 (32 * Z.of_nat i) ->
  getr regs' 26 = w64 (32 * disco_classify_c.gn G) ->
  Z.of_nat i < disco_classify_c.gn G ->
  (forall j, (j < i)%nat -> CtrlParsed.bytes_eqb (disco_classify_c.gmac G j) (CtrlParsed.fld Sg 0 6) = false) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19692)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md' i.
  apply (gsp_loop_all (Z.to_nat (disco_classify_c.gn G)) fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs g s now G Sg regs' mem' md' i). lia.
Qed.
Lemma gsp_at_lw : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (g s now : Z) (G Sg : list byte)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  gsp_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
  gsp_state W memc mem' (spZ regs) g G ->
  gsp_frame W mem' (spZ regs) regs ->
  getr regs' 2 = w64 (spZ regs - 96) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) -> getr regs' 27 = getr regs 27 ->
  getr regs' 8 = w64 now -> getr regs' 9 = w64 s ->
  getr regs' 19 = w64 g -> getr regs' 21 = w64 SB ->
  getr regs' 22 = w64 (GateModel.gdk Sg) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + 19656)) mem' (seg_rom SEGS)) md')
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs g s now G Sg).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md'
    HC HJ HST HFR R2 R3 R4 R27 R8 R9 R19 R21 R22.
  pose proof HC as (HJc & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgside
    & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 & Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof (gsp_stk_lo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJc) as (Hc0 & Hc1 & _).
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  pose proof (gsp_ew_reg regs' Sg G 19%bv 19 g eq_refl ltac:(lia) R19) as E19.
  destruct (gsp_gn G HGok) as (Hfn & Hn8).
  rewrite Hfn in E38.
  assert (Hg47 : g + 264 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp; lia).
  destruct (gsp_seatR fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' 19656
    [(21%bv, SOff 32 0)] HC HST
    ltac:(cbn [map fst]; apply gsp_nodup1)
    ltac:(apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    R19 R9 R21) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  assert (Hsp96 : 96 <= spZ regs) by (unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia).
  assert (Hsp64 : spZ regs <= 2 ^ 64) by lia.
  assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  paj_run_tok RUN HS HJ SHOK GSP_span.
  { awr_ok_tac. }
  gkeep HST HFR.
  psrr_branch_tok RUN BR HS SHOK GSP_span;
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
      rewrite (gsp_bge0 _ _ _ (gsp_U_sx32 _ 38 _ E38 ltac:(lia)) Hn8) in Hc end.
  - apply Z.leb_le in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19732.
    { awr_ok_tac. }
    gkeep HST HFR.
    qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4.
    qatom HS (27%bv : bv 5) 27%nat Q27. qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9.
    qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (21%bv : bv 5) Q21. qreg HS (20%bv : bv 5) Q20.
    qatom HS (22%bv : bv 5) 22%nat Q22. qreg HS (23%bv : bv 5) Q23. qreg HS (24%bv : bv 5) Q24.
    pmkst HS.
    eapply (gsp_app_a fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ HC HJ HST HFR);
      [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
      | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
      | rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Q20; apply (gsp_denot_off regs' Sg G 19 g 256 E19); lia
      | rewrite Q22; exact R22
      | rewrite Q23; apply gsp_w64U; apply (gsp_U_sx32 _ 38 _ E38); lia
      | rewrite Q24; apply gsp_w64U; apply (gsp_U_shadow _ g E19 E32); lia
      | replace (Z.to_nat (disco_classify_c.gn G)) with 0%nat by lia; reflexivity
      | lia ].
  - apply Z.leb_gt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19692.
    { awr_ok_tac. }
    gkeep HST HFR.
    qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4.
    qatom HS (27%bv : bv 5) 27%nat Q27. qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9.
    qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (21%bv : bv 5) Q21. qreg HS (20%bv : bv 5) Q20.
    qatom HS (22%bv : bv 5) 22%nat Q22. qreg HS (23%bv : bv 5) Q23. qreg HS (24%bv : bv 5) Q24.
    qreg HS (25%bv : bv 5) Q25. qreg HS (26%bv : bv 5) Q26.
    pmkst HS.
    eapply (gsp_loop fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ 0%nat HC HJ HST HFR);
      [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
      | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
      | rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Q20; apply (gsp_denot_off regs' Sg G 19 g 256 E19); lia
      | rewrite Q22; exact R22
      | rewrite Q23; apply gsp_w64U; apply (gsp_U_sx32 _ 38 _ E38); lia
      | rewrite Q24; apply gsp_w64U; apply (gsp_U_shadow _ g E19 E32); lia
      | rewrite Q25; reflexivity
      | rewrite Q26; apply gsp_w64U; apply (gsp_U_s10 _ 38 _ E38); lia
      | lia
      | intros j Hj; lia ].
Qed.
Lemma gsp_glue : gsp_glue_stmt.
Proof.
  unfold gsp_glue_stmt.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' md'
    HC HJ HST HFR R1 R2 R3 R4 R27 R8 R9 R11 R19 R21.
  pose proof HC as (HJc & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hnow & Hal16 & Hbud & Hsp & Hg0 & Hg8 & Hg63 & Hgside
    & Hgwr & Hgapp & Hgra & Hghull & HGlen & HGarr & HGok & Hs0 & Hs4 & Hs63 & Hsside & Hsapp & Hsra & Hshull & HSlen & HSarr & Hds).
  pose proof (gsp_stk_lo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJc) as (Hc0 & Hc1 & _).
  pose proof (gsp_ew_reg regs' Sg G 9%bv 9 s eq_refl ltac:(lia) R9) as E9.
  destruct (gsp_ew_extra regs' Sg G) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
  destruct (gsp_seatR fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg regs' mem' 19584
    [(21%bv, SOff 32 0); (11%bv, SOff 9 12)] HC HST
    ltac:(cbn [map fst]; apply gsp_nodup2; vm_compute; discriminate)
    ltac:(apply Forall_cons;
          [cbn [fst snd]; split; [reflexivity|];
           rewrite R21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|];
          apply Forall_cons; [|apply Forall_nil];
          cbn [fst snd]; split; [reflexivity|];
          rewrite R11; cbn [sv_denot]; rewrite E9, unsigned_lit_small by (unfold amem_range in *; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia); reflexivity)
    R19 R9 R21) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (EGSP regs' Sg G)) by (unfold EGSP; apply Eimg_env).
  pose (RUN := paj_run (fx := fq) B LAWS).
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  pose (BR := paj_branch (fx := fq) (PI := PI)).
  assert (Hsp96 : 96 <= spZ regs) by (unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia).
  assert (Hsp64 : spZ regs <= 2 ^ 64) by lia.
  assert (Hg64 : g + 264 <= 2 ^ 64) by lia.
  pose proof (GateModel.fb_rng Sg 12) as F12. pose proof (GateModel.fb_rng Sg 13) as F13.
  pose proof (GateModel.fb_rng Sg 14) as F14.
  paj_run_tok RUN HS HJ SHOK GSP_span.
  { awr_ok_tac. }
  gkeep HST HFR.
  psrr_branch_tok RUN BR HS SHOK GSP_span;
    lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ => rewrite branch_eq_U, (gsp_Uzx8 _ 34 _ E34 F12), U_lit in Hc by lia end.
  - apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19656.
    { awr_ok_tac. }
    gkeep HST HFR.
    qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4. qatom HS (27%bv : bv 5) 27%nat Q27.
    qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9. qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (22%bv : bv 5) Q22.
    pmkst HS.
    eapply (gsp_at_lw fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ HC HJ HST HFR);
      [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
      | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
      | qreg HS (21%bv : bv 5) Q21; rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Q22; unfold GateModel.gdk; rewrite Hc; cbn [Z.eqb sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ].
  - apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GSP_span 19656.
    { awr_ok_tac. }
    gkeep HST HFR.
    qatom HS (2%bv : bv 5) 2%nat Q2. qatom HS (3%bv : bv 5) 3%nat Q3. qatom HS (4%bv : bv 5) 4%nat Q4. qatom HS (27%bv : bv 5) 27%nat Q27.
    qatom HS (8%bv : bv 5) 8%nat Q8. qatom HS (9%bv : bv 5) 9%nat Q9. qatom HS (19%bv : bv 5) 19%nat Q19. qreg HS (22%bv : bv 5) Q22.
    pmkst HS.
    eapply (gsp_at_lw fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg _ _ _ HC HJ HST HFR);
      [ rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q27; exact R27
      | rewrite Q8; exact R8 | rewrite Q9; exact R9 | rewrite Q19; exact R19
      | qreg HS (21%bv : bv 5) Q21; rewrite Q21; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite Q22; apply gsp_w64U; rewrite (gsp_Udk _ 35 36 _ _ E35 F13 E36 F14);
        unfold GateModel.gdk; destruct (Z.eqb_spec (CtrlParsed.fb Sg 12) 0); [lia | reflexivity] ].
Qed.
Theorem pb_reac_disco_gate_should_push : treac_disco_gate_should_push_spec.
Proof. exact (gsp_prologue gsp_glue). Qed.
End h.
End f.
End d.
