(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:388-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFfi.v:262-264 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_ingest.v, with its module paths, module names and numbers changed; 4001 of its 4244 lines of code are new or changed and 2822 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacDiscoGateShouldPush.v, with its numbers changed; 2711 of its 3092 lines of code are new or changed and 3863 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed disco_classify_c GateModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC4b YC1h YC1g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* Build speed: lib/Lib/LiaTwx2.v's lia destructs every Section hypothesis of the form 0 <= _ < _ before each call
   (zify_split_ranges); here that is Rnow, and in these large walk contexts the destruct took 56% of fE2_ok's time.
   This file skips it; lia reads Rnow as it is. *)
#[local] Ltac LiaTwx2.zify_split_ranges ::= idtac.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Definition REAC_DISCO_GATE_SHOULD_PUSH_STK : Z := 112 + 2 * ESTACK.
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
  amem_range s 24 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 -> shadow_hull_vis (aview SEGS (w_H W) memc) s 24 ->
  length Sg = 24%nat -> garr8 SEGS (mrestrict (w_H W) memc) s (map (fun b : byte => bv_unsigned b) Sg) ->
  (g + 264 <= s \/ s + 24 <= g) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_disco_gate_should_push) regs memc mdc)
    (treac_disco_gate_should_push_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg).

Import YP0m YP0l YCbn YP0e YP06 YP03 YA0o YA0q YC4b YC1h YC1g.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Definition GSB : Z := 0x7fff8000.
Definition GBspan : Z * Z := (GSB, GSB + 2 ^ 44 - 1).
Definition ge_cnt : YP09.region := YP09.mkRegion (Some 10%nat) 256 260 0 0 [YP09.mkChunk 256 (CVal 4 (SOff 33 0))].
Definition ge_regions : smem := [stack_region 112; got_regionP; bcell_regionP 32; ge_cnt].
Definition ge_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 265) 3);
  (11%nat, mkAF 4 (2 ^ 47 - 25) 2); (32%nat, mkAF GSB GSB 0); (33%nat, mkAF 0 8 0);
  (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)] [] [].
Definition ss_ge : sstate := mkSS AF_both3_reac_disco_gate_should_push sr_atoms ge_regions None ge_facts.
Definition ge_sig : YP09.region := YP09.mkRegion (Some 11%nat) 12 15 0 0
  [YP09.mkChunk 12 (CVal 1 (SOff 34 0)); YP09.mkChunk 13 (CVal 1 (SOff 35 0)); YP09.mkChunk 14 (CVal 1 (SOff 36 0))].
Definition ge_SH : list shent := [mkSHE 10 0 264; mkSHE 11 0 24].
Definition ge_extra (G Sg : list byte) : list word :=
  map (Z_to_bv 64) [GSB; CtrlParsed.fu G 256 4; CtrlParsed.fb Sg 12; CtrlParsed.fb Sg 13; CtrlParsed.fb Sg 14].
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
Lemma gsp_fu1 : forall (L : list byte) (k : nat), (k < length L)%nat -> CtrlParsed.fu L k 1 = CtrlParsed.fb L k.
Proof.
  intros L k Hk. unfold CtrlParsed.fu. rewrite (GateModel.fld1 L k Hk).
  rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val]. unfold CtrlParsed.fb. lia.
Qed.
Lemma gsp_fu_n : forall G : list byte, disco_classify_c.gate_ok G -> 0 <= CtrlParsed.fu G 256 4 <= 8.
Proof.
  intros G (HL & Hn & _). unfold disco_classify_c.gn, CtrlParsed.s32 in Hn.
  pose proof (GateModel.fu_rng4 G 256 ltac:(lia)) as R.
  destruct (Z.ltb_spec (CtrlParsed.fu G 256 4) (2 ^ 31)); lia.
Qed.
Lemma gsp_off_img : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k p n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> amem_range p n ->
  (forall a, p <= a < p + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  forall a, p <= a < p + n -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k p n HJ Hamr Hwr a Ha.
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a Ha))
    as (_ & [[Hc _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
  - right. unfold YImgTop.IMG_TOP. lia.
  - pose proof (blk_off_imgP B _ _ _ _ _ b m HAR Hbin) as Ho. unfold off_img in Ho. lia.
  - assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
    pose proof (frm_off_imgP B _ _ _ _ _ cid pos HAR Hin') as Ho. unfold off_img in Ho.
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
  - exfalso. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd in *. lia.
Qed.
Lemma gsp_apart : forall lo hi q, lo < hi -> (forall a, lo <= a < hi -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a) ->
  YImgTop.IMG_LO <= q -> q + 8 <= YImgTop.IMG_TOP -> hi <= q \/ q + 8 <= lo.
Proof.
  intros lo hi q Hlh H Hq1 Hq2. destruct (Z.le_gt_cases hi q) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases (q + 8) lo) as [|H2]; [right; lia|]. exfalso.
  destruct (H (Z.max lo q) ltac:(lia)); lia.
Qed.
Lemma gsp_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) (g s : Z) (G Sg : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 g -> getr regs 11 = w64 s ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK -> spZ regs <= sp0 ->
  0 < g -> g mod 8 = 0 -> amem_range g 264 -> (spZ regs <= g \/ g + 264 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK) ->
  (forall a, g <= a < g + 264 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 264 ->
  0 < s -> s mod 4 = 0 -> amem_range s 24 -> range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 ->
  length G = 264%nat -> garr8 SEGS (mrestrict (w_H W) memc) g (map bv_unsigned G) -> disco_classify_c.gate_ok G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (ge_extra G Sg))) ss_ge
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_disco_gate_should_push)) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) ge_SH (Eimg (Ereg regs (ge_extra G Sg))) (mrestrict (w_H W) memc).
Proof.
  intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s G Sg
    HJ H10 H11 Hal16 Hbud Hsp Hg0 Hg8 Hgapp Hgside Hwr Hgra Hs0 Hs4 Hsapp Hsra HGl HGa HGok.
  pose proof (proj1 HJ) as HAR.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8304) by reflexivity.
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
  pose proof (gsp_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k g 264 HJ Hgapp Hwr) as Hoff.
  pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
  pose proof (gsp_fu_n G HGok) as Hn.
  assert (Hg8b : 8 <= g) by (pose proof (Z.div_mod g 8 ltac:(lia)) as Dg; rewrite Hg8 in Dg; lia).
  assert (Hgb : g + 264 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hgapp; lia).
  assert (Hs4b : 4 <= s) by (pose proof (Z.div_mod s 4 ltac:(lia)) as Ds; rewrite Hs4 in Ds; lia).
  assert (Hsb : s + 24 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hsapp; lia).
  assert (DG : g + 260 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= g + 256)
    by (apply (gsp_apart (g + 256) (g + 260)); [lia | intros a Ha; apply Hoff; lia | lia | lia]).
  assert (DC : g + 260 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= g + 256)
    by (apply (gsp_apart (g + 256) (g + 260)); [lia | intros a Ha; apply Hoff; lia | lia | lia]).
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hoff.
  set (E := Eimg (Ereg regs (ge_extra G Sg))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ge_extra G Sg)) n)
    by (intros n Hn0; subst E; apply Eimg_low; exact Hn0).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 g) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E32 : ew E 32 = Z_to_bv 64 GSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (CtrlParsed.fu G 256 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (CtrlParsed.fb Sg 12)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (CtrlParsed.fb Sg 13)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 (CtrlParsed.fb Sg 14)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
  assert (VM : val_mem SEGS (mrestrict (w_H W) memc) (g + 256) 4 (CtrlParsed.fu G 256 4)).
  { exact (gsp_val_mem _ g G 256 4 HGa ltac:(lia)). }
  pose proof (GateModel.fb_rng Sg 12) as R34. pose proof (GateModel.fb_rng Sg 13) as R35. pose proof (GateModel.fb_rng Sg 14) as R36.
  split.
  - rewrite restrict_mkst_fx. unfold ss_ge. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold ge_regions, ge_cnt, stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
      * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) GSB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold GSB; lia | lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
      * rewrite (VB 10%nat g E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ g 256 4 (SOff 33 0) (CtrlParsed.fu G 256 4));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact VM].
    + apply pairwise_disjoint_of_extents. unfold ge_regions, ge_cnt, stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat g E10) by lia.
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
      rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [ge_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold GSB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold GSB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, ge_SH. constructor; [|constructor; [|constructor]].
    + apply (shent_ok_of_range SEGS (w_H W) memc E (SOff 32 0) 10 g 264 g 0 264 Hgra).
      * unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold GSB; lia). reflexivity.
      * unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memc E (SOff 32 0) 11 s 24 s 0 24 Hsra).
      * unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold GSB; lia). reflexivity.
      * unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.


Lemma le_bytes_nth : forall n z kk, (kk < n)%nat ->
  nth_error (Z_to_le_bytes n z) kk = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat kk))).
Proof.
induction n as [|n IH]; intros z kk Hk; [lia|].
destruct kk as [|kk]; cbn [Z_to_le_bytes nth_error].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma z8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_mod. lia.
Qed.
Lemma gle_byte_1_0 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma garr8_byte : forall (M : word -> option byte) p (X : list byte) j b,
  garr8 SEGS M p (map (fun b : byte => bv_unsigned b) X) -> nth_error X j = Some b ->
  mbyte SEGS M (p + Z.of_nat j) = Some b.
Proof.
intros M p X j b HG Hj.
assert (Hl : (j < length (map (fun b : byte => bv_unsigned b) X))%nat)
  by (rewrite length_map; apply nth_error_Some; rewrite Hj; discriminate).
destruct (HG j Hl) as [Hm Hr].
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) X) 0 = bv_unsigned b).
{ apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
rewrite Hn in Hm, Hr. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm.
rewrite Hm, gle_byte_1_0 by exact Hr. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma fld_le : forall (L : list byte) k n, (k + n <= length L)%nat -> CtrlParsed.fld L k n = Z_to_le_bytes n (CtrlParsed.fu L k n).
Proof.
intros L k n H. unfold CtrlParsed.fu. pose proof (GateModel.ble_inv (CtrlParsed.fld L k n)) as E.
rewrite GateModel.length_fld in E by lia. symmetry. exact E.
Qed.
Lemma le8_Z : forall z, 0 <= z < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof. intros z Hz. unfold Mem.le8, word_to_le_bytes. rewrite unsigned_lit_small by lia. reflexivity. Qed.
Lemma le4_Z : forall z, Mem.le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 (z mod 2 ^ 32).
Proof.
intros z. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Mem.Z_to_le_bytes_mod 4 z 64) by lia. rewrite (Mem.Z_to_le_bytes_mod 4 z 32) by lia. reflexivity.
Qed.
Lemma le1_fb : forall (L : list byte) k, [nth k L (CtrlParsed.zb 0)] = Z_to_le_bytes 1 (CtrlParsed.fb L k).
Proof. intros L k. rewrite <- GateModel.le1_fb. unfold Mem.le1. rewrite unsigned_lit_small by (pose proof (GateModel.fb_rng L k); lia). reflexivity. Qed.

Definition ckv (o : Z) (w : N) (a : nat) : YP09.chunk := YP09.mkChunk o (CVal w (SOff a 0)).
Definition sav_chunks : list YP09.chunk :=
  [ckv 0 8 32; ckv 8 8 45; ckv 16 8 44; ckv 24 8 43; ckv 32 8 42; ckv 40 8 41; ckv 48 8 40; ckv 56 8 39;
   ckv 64 8 38; ckv 72 8 37; ckv 80 8 36; ckv 88 8 35; ckv 96 8 34; ckv 104 8 33].
Definition rK_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0 sav_chunks.
Definition SAVSL : list (Z * bv 5) :=
  [(104, 1%bv); (96, 8%bv); (88, 9%bv); (80, 18%bv); (72, 19%bv); (64, 20%bv); (56, 21%bv); (48, 22%bv);
   (40, 23%bv); (32, 24%bv); (24, 25%bv); (16, 26%bv); (8, 27%bv)].
Definition AFNOTG : afact := mkAF (2 ^ 64 - 1 - (2 ^ 47 - 265)) (2 ^ 64 - 9) 0.
Definition fa_L : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 288 288 0); (9%nat, mkAF 4 (2 ^ 47 - 25) 2);
   (19%nat, mkAF 8 (2 ^ 47 - 265) 3); (21%nat, mkAF GSB GSB 0); (23%nat, AFNOTG); (24%nat, mkAF 1 8 0);
   (26%nat, mkAF 0 224 5); (27%nat, mkAF 32 256 5)] [] [].
Definition ss_L (pc : Z) : sstate := mkSS pc sr_atoms [rK_stk] None fa_L.
Definition gdk (Q : list byte) : Z := GateModel.gdk Q.
Section w.
Context {fx : YK11.FPState}.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (g s now : Z) (G Sg : list byte).
Hypothesis HJc : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis H10 : getr regs 10 = w64 g.
Hypothesis H11 : getr regs 11 = w64 s.
Hypothesis H12 : getr regs 12 = w64 now.
Hypothesis Rnow : 0 <= now < 2 ^ 64.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwin : sp0 - STK <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK.
Hypothesis Hspl : spZ regs <= sp0.
Hypothesis Hg0 : 0 < g.
Hypothesis Hg8 : g mod 8 = 0.
Hypothesis Hg63 : g + 264 <= 2 ^ 63.
Hypothesis Hgside : spZ regs <= g \/ g + 264 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK.
Hypothesis Hgw : forall a, g <= a < g + 264 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Hypothesis Hgam : amem_range g 264.
Hypothesis Hgra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF g 264.
Hypothesis Hgsh : shadow_hull_vis (aview SEGS (w_H W) memc) g 264.
Hypothesis HGl : length G = 264%nat.
Hypothesis HGa : garr8 SEGS (mrestrict (w_H W) memc) g (map (fun b : byte => bv_unsigned b) G).
Hypothesis HGok : disco_classify_c.gate_ok G.
Hypothesis Hs0 : 0 < s.
Hypothesis Hs4 : s mod 4 = 0.
Hypothesis Hs63 : s + 24 <= 2 ^ 63.
Hypothesis Hsside : spZ regs <= s \/ s + 24 <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK.
Hypothesis Hsam : amem_range s 24.
Hypothesis Hsra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24.
Hypothesis Hssh : shadow_hull_vis (aview SEGS (w_H W) memc) s 24.
Hypothesis HSl : length Sg = 24%nat.
Hypothesis HSa : garr8 SEGS (mrestrict (w_H W) memc) s (map (fun b : byte => bv_unsigned b) Sg).
Hypothesis Hgs : g + 264 <= s \/ s + 24 <= g.
Definition tQ : world SEGS -> config -> Prop :=
  treac_disco_gate_should_push_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs g s now G Sg.
Definition tJ (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k.
Definition tKP (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK <= a < spZ regs) -> ~ (g <= a < g + 264) ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Definition tPR (m : word -> option byte) : Prop := forall a, apresent (w_H W) memc a -> apresent (w_H W) m a.
Definition tTB (m : word -> option byte) (X : list byte) : Prop :=
  garr8 SEGS (mrestrict (w_H W) m) g (map (fun b : byte => bv_unsigned b) X) /\ length X = 264%nat.
Definition tSV (m : word -> option byte) : Prop :=
  forall o q, In (o, q) SAVSL -> val_mem SEGS (mrestrict (w_H W) m) (spZ regs - 112 + o) 8 (bv_unsigned (getr regs q)).
Definition tOW (m : word -> option byte) : Prop :=
  val_mem SEGS (mrestrict (w_H W) m) (spZ regs - 112 + 0) 8 now.
Lemma stk_lo : alloc_ceiling <= spZ regs - REAC_DISCO_GATE_SHOULD_PUSH_STK /\ spZ regs <= 2 ^ 47.
Proof.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (_ & _ & H3 & H4 & H5 & H6 & _). unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia.
Qed.
Lemma gw_off_img : forall a, g <= a < g + 264 -> ~ in_img SEGS a.
Proof.
intros a Ha Himg. pose proof (gsp_off_img STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k g 264 HJc Hgam
  (fun a Ha => proj1 (Hgw a Ha)) a Ha) as Ho.
pose proof (pa_img_range a Himg) as Hr. lia.
Qed.
Lemma fin_post : forall regs2 m md X ret,
  tJ m md -> tKP m -> tPR m -> tTB m X ->
  aregs_preserved regs regs2 -> getr regs2 1 = getr regs 1 -> getr regs2 10 = w64 ret ->
  GateModel.gate_model G Sg now = (X, ret) ->
  tQ W (mkCfg (mkst regs2 (getr regs 1) m (seg_rom SEGS)) md).
Proof.
intros regs2 m md X ret HJ HK HP [HX HXl] HPR Hr1 Hret HM.
pose proof (proj1 HJc) as HARc. pose proof stk_lo as [Hlo Hhi].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
exists lyc, Sc, regs2, m, md.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact Hr1|].
split; [rewrite HM; exact Hret|].
split; [reflexivity|]. split; [apply Permutation_refl|].
split.
{ unfold treac_disco_gate_should_push_kept. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn Ht. apply HK; [lia | exact Hn | exact Ht].
  - intros b n i Hb Hi Ht. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HARc Hb) as (_ & H4096 & Hce & _).
    apply HK; [lia | lia | exact Ht].
  - intros a Hi _ _. pose proof (pa_segs_low a Hi) as Hl.
    apply HK; [lia | lia | intros Ht; exact (gw_off_img a Ht Hi)].
  - intros cid pos a Hf Ha Ht.
    pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hf) as (Hf1 & Hf2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    assert (Ha2 : 0 <= a < alloc_ceiling).
    { unfold frame_rng, in_zr in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha]; [lia|].
      unfold shadow_addr, SHADOW_OFF in Ha.
      pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)).
      pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)).
      assert (0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
      assert (0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
      lia. }
    apply HK; [lia | lia | exact Ht].
  - intros a Ha Hn Hp. exact (HP a Hp).
  - intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply Hpres. lia. }
rewrite HM. cbn [fst].
split; [exact HX|].
split; [pose proof (GateModel.gate_model_ok G Sg now HGok HSl) as Hok; rewrite HM in Hok; exact Hok|].
apply (garr8_frame SEGS (mrestrict (w_H W) memc)); [exact HSa|].
intros a Ha. rewrite length_map, HSl in Ha. apply (mbyte_of_aview SEGS). pose proof Hsam as Hs. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hs.
apply HK; unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia.
Qed.
Definition xK (X : list byte) (i : nat) : list word :=
  Z_to_bv 64 now :: getr regs 1 :: getr regs 8 :: getr regs 9 :: getr regs 18 :: getr regs 19 :: getr regs 20 ::
  getr regs 21 :: getr regs 22 :: getr regs 23 :: getr regs 24 :: getr regs 25 :: getr regs 26 :: getr regs 27 ::
  map (Z_to_bv 64)
    [CtrlParsed.fu X (32 * i + 8) 4; CtrlParsed.fu X (32 * i + 12) 4; CtrlParsed.fb X (32 * i + 16);
     CtrlParsed.fu X (32 * i + 24) 8; CtrlParsed.fu Sg 8 4; CtrlParsed.fb Sg 16].
Definition EK (regs' : bvmap 5 word) (X : list byte) (i : nat) : env := Eimg (Ereg regs' (xK X i)).
Lemma stk_region_ok : forall regs' m X i,
  tSV m -> tOW m -> spZ regs' = spZ regs - 112 ->
  region_ok SEGS (EK regs' X i) (mrestrict (w_H W) m) rK_stk.
Proof.
intros regs' m X i HSV HOW Hsp.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (B2 : base_val (EK regs' X i) (Some 2%nat) = spZ regs - 112)
  by (cbn [base_val]; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
unfold rK_stk, sav_chunks, ckv, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B2. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: lazymatch goal with
     | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk 0 _) =>
       apply (chunk_ok_val SEGS _ _ _ 0 8 _ now);
       [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
         rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | cbn; lia | cbn; lia | exact HOW ]
     | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
       let q := lazymatch o with 104 => constr:(1%bv : bv 5) | 96 => constr:(8%bv : bv 5) | 88 => constr:(9%bv : bv 5)
         | 80 => constr:(18%bv : bv 5) | 72 => constr:(19%bv : bv 5) | 64 => constr:(20%bv : bv 5)
         | 56 => constr:(21%bv : bv 5) | 48 => constr:(22%bv : bv 5) | 40 => constr:(23%bv : bv 5)
         | 32 => constr:(24%bv : bv 5) | 24 => constr:(25%bv : bv 5) | 16 => constr:(26%bv : bv 5)
         | 8 => constr:(27%bv : bv 5) end in
       apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (getr regs q)));
       [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
         rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; cbn in Hb |- *; lia
       | cbn; lia | apply HSV; cbv [SAVSL In]; tauto ]
     end.
Qed.

Lemma ek_reg : forall regs' X i (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r -> ew (EK regs' X i) n = getr regs' r.
Proof. intros regs' X i r n Hn. unfold EK. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Ltac ekreg n r := lazymatch goal with |- context [ew (EK ?rg ?X ?i) n] => rewrite (ek_reg rg X i r n eq_refl) end.
Lemma kst_L : forall pc regs' m X i n,
  tSV m -> tOW m -> spZ regs' = spZ regs - 112 ->
  getr regs' 8 = w64 288 -> getr regs' 9 = w64 s -> getr regs' 19 = w64 g -> getr regs' 21 = w64 GSB ->
  getr regs' 23 = w64 (2 ^ 64 - 1 - g) -> getr regs' 24 = w64 n -> 1 <= n <= 8 ->
  getr regs' 26 = w64 (32 * Z.of_nat i) -> (i < 8)%nat -> getr regs' 27 = w64 (32 * n) ->
  st_ok_pi SEGS VAL (EK regs' X i) (ss_L pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 21 0) [] (EK regs' X i) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X i n HSV HOW Hsp R8 R9 R19 R21 R23 R24 Hn R26 Hi R27.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
assert (Hg8b : 8 <= g) by (pose proof (Z.div_mod g 8 ltac:(lia)) as Dg; rewrite Hg8 in Dg; lia).
assert (Hs4b : 4 <= s) by (pose proof (Z.div_mod s 4 ltac:(lia)) as Ds; rewrite Hs4 in Ds; lia).
rewrite restrict_mkst_fx. split.
- unfold ss_L. apply pa_entry_st_ok_full.
  + unfold EK. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. exact (stk_region_ok regs' m X i HSV HOW Hsp).
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    unfold fa_L, AFNOTG. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    ekreg 2%nat (2%bv : bv 5). ekreg 8%nat (8%bv : bv 5). ekreg 9%nat (9%bv : bv 5). ekreg 19%nat (19%bv : bv 5). ekreg 21%nat (21%bv : bv 5). ekreg 23%nat (23%bv : bv 5). ekreg 24%nat (24%bv : bv 5). ekreg 26%nat (26%bv : bv 5). ekreg 27%nat (27%bv : bv 5).
    change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite R8, R9, R19, R21, R23, R24, R26, R27.
    unfold w64. rewrite !unsigned_lit_small by (unfold GSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo.
    unfold GSB. repeat match goal with |- _ /\ _ => split end; try lia;
    first [ rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity | idtac ].
- apply Forall_nil.
Qed.

Lemma U_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 -> U E (SOff n c) = x + c.
Proof. intros E n c x Hn Hx Hxc. rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. Qed.
Lemma den_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n c x Hn Hx Hxc. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff n c))). f_equal.
change (U E (SOff n c) = x + c). apply U_off; assumption.
Qed.
Lemma den_add2 : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros E n m x y Hn Hm Hx Hy Hxy.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y). rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), (U_atom E m y Hm) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma vm_kept : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros m m' a n v He Hv j Hj.
assert (Hm : mbyte SEGS (mrestrict (w_H W) m') (a + Z.of_nat j) = mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j))
  by (apply (mbyte_of_aview SEGS); apply He; lia).
rewrite Hm. apply Hv. exact Hj.
Qed.
Lemma ga_kept : forall (m m' : word -> option byte) p (l : list Z),
  (forall x, p <= x < p + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (mrestrict (w_H W) m) p l -> garr8 SEGS (mrestrict (w_H W) m') p l.
Proof.
intros m m' p l He Hg. apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|].
intros a Ha. apply (mbyte_of_aview SEGS). apply He. exact Ha.
Qed.
Lemma ga_aview_byte : forall (m : word -> option byte) p (L : list byte) (j : nat),
  garr8 SEGS (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) L) -> (j < length L)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (CtrlParsed.zb 0))).
Proof.
intros m p L j HG Hj. unfold aview.
rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) p (map bv_unsigned L) j HG ltac:(rewrite length_map; lia)).
cbn [option_map]. rewrite gsp_nth_map, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ga_aview_some : forall (m : word -> option byte) p (L : list byte) a,
  garr8 SEGS (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) L) -> p <= a < p + Z.of_nat (length L) ->
  aview SEGS (w_H W) m a <> None.
Proof.
intros m p L a HG Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (ga_aview_byte m p L _ HG) by lia. discriminate.
Qed.
Lemma gsp_cmp_iff : forall (m : word -> option byte) (L M : list byte) (p q : Z) (k1 k2 n : nat),
  garr8 SEGS (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) L) ->
  garr8 SEGS (mrestrict (w_H W) m) q (map (fun b : byte => bv_unsigned b) M) ->
  (k1 + n <= length L)%nat -> (k2 + n <= length M)%nat ->
  ((forall i, 0 <= i < Z.of_nat n ->
      aview SEGS (w_H W) m (p + Z.of_nat k1 + i) = aview SEGS (w_H W) m (q + Z.of_nat k2 + i)) <->
   CtrlParsed.bytes_eqb (CtrlParsed.fld L k1 n) (CtrlParsed.fld M k2 n) = true).
Proof.
intros m L M p q k1 k2 n HL HM Hk1 Hk2.
assert (Haux : forall j : nat, (j < n)%nat ->
  (aview SEGS (w_H W) m (p + Z.of_nat k1 + Z.of_nat j) = aview SEGS (w_H W) m (q + Z.of_nat k2 + Z.of_nat j)
   <-> bv_unsigned (nth (k1 + j) L (CtrlParsed.zb 0)) = bv_unsigned (nth (k2 + j) M (CtrlParsed.zb 0)))).
{ intros j Hj.
  replace (p + Z.of_nat k1 + Z.of_nat j) with (p + Z.of_nat (k1 + j)) by lia.
  replace (q + Z.of_nat k2 + Z.of_nat j) with (q + Z.of_nat (k2 + j)) by lia.
  rewrite (ga_aview_byte m p L (k1 + j)%nat HL ltac:(lia)).
  rewrite (ga_aview_byte m q M (k2 + j)%nat HM ltac:(lia)).
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
Lemma kp_ra : forall m a n, tKP m -> 0 <= a -> amem_range a n -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n.
Proof.
intros m a n HK Ha Ham Hn H. apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact H].
intros x Hx. pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Ht. unfold shadow_of_addr.
pose proof (Z.mul_div_le x 8 ltac:(lia)). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_succ_div_gt x 8 ltac:(lia)).
apply HK; unfold amem_range, SHADOW_OFF, REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia.
Qed.
Lemma kp_shv : forall m a n, tKP m -> 0 <= a -> amem_range a n -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) memc) a n -> shadow_hull_vis (aview SEGS (w_H W) m) a n.
Proof.
intros m a n HK Ha Ham Hn H x Hx. pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Ht. unfold shadow_addr, SHADOW_OFF in Hx.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (a + n - 1) 8 ltac:(lia)).
pose proof (Z.mul_succ_div_gt a 8 ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_succ_div_gt (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mul_div_le (a + n - 1) 8 ltac:(lia)). pose proof (Z.div_le_mono a (a + n - 1) 8 ltac:(lia) ltac:(lia)).
rewrite HK; [apply H; unfold shadow_addr, SHADOW_OFF; exact Hx | | |];
unfold amem_range, REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia.
Qed.
Lemma gsp_hull_sub : forall rd a n a' n', shadow_hull_vis rd a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> 0 < n' ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' HV Ha H1 H2 Hn s0 Hs. apply HV. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma kp_garr8_S : forall m, tKP m -> garr8 SEGS (mrestrict (w_H W) m) s (map (fun b : byte => bv_unsigned b) Sg).
Proof.
intros m HK. pose proof stk_lo as [Hlo Hhi]. pose proof Hsam as Hs'.
apply (ga_kept memc m s); [|exact HSa]. intros a Ha. rewrite length_map, HSl in Ha.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hs'.
apply HK; unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia.
Qed.
Lemma call_keep : forall m m2 X, tKP m -> tPR m -> tTB m X -> tSV m -> tOW m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 - 2 * ESTACK <= a < spZ regs - 112) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  tKP m2 /\ tPR m2 /\ tTB m2 X /\ tSV m2 /\ tOW m2.
Proof.
intros m m2 X HK HP [HX HXl] HSV HOW Hfr Hpr.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof Hgam as Hg'. pose proof Hsam as Hs'.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *.
split; [|split; [|split; [|split]]].
- intros a Ha Hs Hg. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. rewrite Hfr by (unfold ESTACK; lia). apply HK; [exact Ha | | exact Hg]. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK. lia.
- intros a Ha. apply Hpr. apply HP. exact Ha.
- split; [|exact HXl]. apply (ga_kept m m2 g); [|exact HX]. intros a Ha. rewrite length_map, HXl in Ha.
  apply Hfr; unfold ESTACK; lia.
- intros o q Hin. apply (vm_kept m m2); [|exact (HSV o q Hin)]. intros x Hx.
  assert (Ho : 8 <= o <= 104) by (cbv [SAVSL In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]); destruct Hin).
  apply Hfr; unfold ESTACK; lia.
- apply (vm_kept m m2); [|exact HOW]. intros x Hx. apply Hfr; unfold ESTACK; lia.
Qed.
Definition found_stmt : Prop := forall (i : nat) regs' m md,
  (i < Z.to_nat (disco_classify_c.gn G))%nat ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB ->
  getr regs' 22 = w64 (gdk Sg) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4cb8)) m (seg_rom SEGS)) md) tQ.
Definition after_stmt : Prop := forall regs' m md,
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = None ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 19 = w64 g -> getr regs' 20 = w64 (g + 256) -> getr regs' 21 = w64 GSB ->
  getr regs' 22 = w64 (gdk Sg) -> getr regs' 23 = w64 (2 ^ 64 - 1 - g) -> getr regs' 24 = w64 (disco_classify_c.gn G) ->
  getr regs' 25 = w64 (GSB + (g + 256) / 8) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4bd8)) m (seg_rom SEGS)) md) tQ.
Definition loop_stmt (i : nat) : Prop := forall regs' m md,
  (i < Z.to_nat (disco_classify_c.gn G))%nat ->
  (forall j, (j < i)%nat -> CtrlParsed.bytes_eqb (disco_classify_c.gmac G j) (CtrlParsed.fld Sg 0 6) = false) ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 288 -> getr regs' 9 = w64 s -> getr regs' 19 = w64 g -> getr regs' 20 = w64 (g + 256) ->
  getr regs' 21 = w64 GSB -> getr regs' 22 = w64 (gdk Sg) -> getr regs' 23 = w64 (2 ^ 64 - 1 - g) ->
  getr regs' 24 = w64 (disco_classify_c.gn G) -> getr regs' 25 = w64 (GSB + (g + 256) / 8) ->
  getr regs' 26 = w64 (32 * Z.of_nat i) -> getr regs' 27 = w64 (32 * disco_classify_c.gn G) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4bb0)) m (seg_rom SEGS)) md) tQ.
Ltac preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
Ltac kw0 HFr K := lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a);
  [ let a_ := fresh "a" in let Ha_ := fresh "Ha" in intros a_ Ha_;
    apply (kept_of_frame (segs := SEGS) Ex rs H m m' (fun _ => False) HFr); [ | exact Ha_ | tauto];
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b_ := fresh "b" in let wlo_ := fresh "wlo" in let whi_ := fresh "whi" in let x_ := fresh "x" in
    let Hin_ := fresh "Hin" in let Hx_ := fresh "Hx" in
    intros b_ wlo_ whi_ x_ Hin_ Hx_; cbn [In] in Hin_;
    repeat (destruct Hin_ as [Hin_|Hin_]; [injection Hin_ as <- <- <-; lia|]); try destruct Hin_
  | ] end.

Lemma den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma beq0_iff : forall E kk (v : word), ew E kk = v ->
  (branch_taken BC_EQ (sv_denot E (SOff kk 0)) (sv_denot E (SLit 0)) = true <-> v = w64 0).
Proof.
intros E kk v Hk. rewrite branch_eq_U, U_SOff, U_lit by lia. rewrite Hk, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 v) as Hv. change (bv_modulus 64) with (2 ^ 64) in Hv.
rewrite zcanon_id by (unfold M64; lia). rewrite Z.eqb_eq. unfold w64. rewrite bv_eq, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma bne_off : forall E a b x y c, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= y + c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff a 0)) (sv_denot E (SOff b c)) = negb (x =? y + c).
Proof.
intros E a b x y c Ha Hb Hx Hy Hyc. rewrite branch_ne_U, (U_off E a 0 x Ha), (U_off E b c y Hb) by lia.
rewrite Z.add_0_r. reflexivity.
Qed.
Lemma mod16_sub : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - 112 - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 16 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db. replace (a - 112 - b) with ((a / 16 - 7 - b / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.
Lemma ra_kept_all : forall (m m' : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 47 ->
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n -> range_addressable (aview SEGS (w_H W) m') SHADOW_OFF a n.
Proof.
intros m m' a n Ha Hn HK H. apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact H].
intros x Hx. apply HK. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
change (2 ^ 47 / 8) with (2 ^ 44) in *. lia.
Qed.
Lemma shv_kept_all : forall (m m' : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  shadow_hull_vis (aview SEGS (w_H W) m) a n -> shadow_hull_vis (aview SEGS (w_H W) m') a n.
Proof.
intros m m' a n Ha Hn Hn0 HK H x Hx. rewrite HK; [apply H; exact Hx|]. unfold shadow_addr, SHADOW_OFF in Hx.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (a + n - 1) (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
change (2 ^ 47 / 8) with (2 ^ 44) in *.
pose proof (Z.div_pos (2147450880 + a / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (2147450880 + (a + n - 1) / 8) (2147450880 + 2 ^ 44) 8 ltac:(lia) ltac:(lia)).
lia.
Qed.

Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Lemma loop_step : found_stmt -> after_stmt -> forall i, ((i + 1 < Z.to_nat (disco_classify_c.gn G))%nat -> loop_stmt (i + 1)) -> loop_stmt i.
Proof.
intros FS AS i IH regs' m md Hi Hpre HJ HK HP HT HSV HOW Hsp R3 R4 R8 R9 R19 R20 R21 R22 R23 R24 R25 R26 R27.
pose proof (proj1 (proj2 HGok)) as Hn.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & _).
assert (Hi8 : (i < 8)%nat) by lia.
assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8304) by reflexivity.
destruct (kst_L 0x4bb0 regs' m G i (disco_classify_c.gn G) HSV HOW Hsp R8 R9 R19 R21 R23 R24 ltac:(lia) R26 Hi8 R27) as [HS SHOK].
remember (EK regs' G i) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs' (xK G i)) E) by (subst E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs' rr) by (intros; subst E; apply ek_reg; assumption).
assert (E2 : ew E 2 = getr regs' 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs' 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs' 4) by (apply EE; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 s) by (rewrite (EE 9%nat 9%bv) by reflexivity; exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 g) by (rewrite (EE 19%nat 19%bv) by reflexivity; exact R19).
assert (E26 : ew E 26 = Z_to_bv 64 (32 * Z.of_nat i)) by (rewrite (EE 26%nat 26%bv) by reflexivity; exact R26).
assert (E27 : ew E 27 = Z_to_bv 64 (32 * disco_classify_c.gn G)) by (rewrite (EE 27%nat 27%bv) by reflexivity; exact R27).
clear HE.
paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
kw0 HFr KM.
preg HS (10%bv : bv 5) Ra0. preg HS (11%bv : bv 5) Ra1. preg HS (12%bv : bv 5) Ra2. preg HS (1%bv : bv 5) Rra.
preg HS (2%bv : bv 5) Qsp. preg HS (3%bv : bv 5) Qgp. preg HS (4%bv : bv 5) Qtp.
rewrite (den_add2 E 19 26 g (32 * Z.of_nat i) E19 E26) in Ra0 by lia.
rewrite den_atom0, E9 in Ra1. change (SOff 240 19404) with (SOff A_TEXT 19404) in Rra. rewrite (codeptr_val E 19404 HEI) in Rra.
rewrite den_atom0, E3, R3 in Qgp. rewrite den_atom0, E4, R4 in Qtp.
assert (HspU : spZ (ms_regs ms) = spZ regs - 112) by (unfold spZ at 1; rewrite Qsp, den_atom0, E2; exact Hsp).
assert (HGm : garr8 SEGS (mrestrict (w_H W) m) g (map (fun b : byte => bv_unsigned b) G)) by exact (proj1 HT).
assert (HSm : garr8 SEGS (mrestrict (w_H W) m) s (map (fun b : byte => bv_unsigned b) Sg)) by exact (kp_garr8_S m HK).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_bcmp_at (fx := fx) SEGS B LAWS pa_segs_low (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fx) W (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (g + 32 * Z.of_nat i) s 6 (spZ regs - 112 - sp0) (Z_to_bv 64 (BASE + 19404)) HJ).
  - exact Ra0.
  - exact Ra1.
  - rewrite Ra2. reflexivity.
  - lia. - lia. - lia. - lia. - lia.
  - rewrite HspU. lia.
  - apply mod16_sub; assumption.
  - lia.
  - unfold ESTACK. lia.
  - rewrite Qgp. exact Hgp. - rewrite Qtp. exact Htp. - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. rewrite HspU. split; [rewrite KM by lia; apply (ga_aview_some m g G a HGm); rewrite HGl; lia | unfold ESTACK; lia].
  - intros a Ha. rewrite HspU. split; [rewrite KM by lia; apply (ga_aview_some m s Sg a HSm); rewrite HSl; lia | unfold ESTACK; lia].
  - intros a Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - apply (ra_kept_all m (ms_mem ms)); [lia | lia | exact KM |].
    apply (kp_ra m _ 6 HK); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
    apply (range_addressable_sub _ _ g 264); [exact Hgra | lia | lia].
  - intros _. apply (shv_kept_all m (ms_mem ms)); [lia | lia | lia | exact KM |].
    apply (kp_shv m _ 6 HK); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
    apply (gsp_hull_sub _ g 264); [exact Hgsh | lia | lia | lia | lia].
  - apply (ra_kept_all m (ms_mem ms)); [lia | lia | exact KM |].
    apply (kp_ra m _ 6 HK); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
    apply (range_addressable_sub _ _ s 24); [exact Hsra | lia | lia].
  - intros _. apply (shv_kept_all m (ms_mem ms)); [lia | lia | lia | exact KM |].
    apply (kp_shv m _ 6 HK); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
    apply (gsp_hull_sub _ s 24); [exact Hssh | lia | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
assert (XC : v = w64 0 <-> CtrlParsed.bytes_eqb (disco_classify_c.gmac G i) (CtrlParsed.fld Sg 0 6) = true).
{ rewrite Hcmp. unfold disco_classify_c.gmac.
  rewrite <- (gsp_cmp_iff m G Sg g s (32 * i) 0 6 HGm HSm ltac:(lia) ltac:(lia)).
  split; intros HH i0 Hi0; specialize (HH i0 ltac:(lia)).
  - rewrite <- !KM by lia. replace (g + Z.of_nat (32 * i) + i0) with (g + 32 * Z.of_nat i + i0) by lia.
    replace (s + Z.of_nat 0 + i0) with (s + i0) by lia. exact HH.
  - rewrite !KM by lia. replace (g + 32 * Z.of_nat i + i0) with (g + Z.of_nat (32 * i) + i0) by lia.
    replace (s + i0) with (s + Z.of_nat 0 + i0) by lia. exact HH. }
destruct (call_keep m mem2 G HK HP HT HSV HOW
  ltac:(intros a Ha Hw; rewrite Hfr2 by (unfold ESTACK in *; lia); apply KM; exact Ha)
  ltac:(intros a Ha; apply Hpres2; exact (apresent_grows _ _ _ a HG Ha))) as (HK2 & HP2' & HT2 & HSV2 & HOW2).
let K := run_K_hi HS in jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply region_kept_aview; [rewrite E2; exact Hsp | | exact Hpres2].
  intros a Ha. apply Hfr2; unfold ESTACK in *; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2.
remember (havoc E 512 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS2.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (OLD : forall nn, (nn < 512)%nat -> ew Ev2 nn = ew E nn) by (intros nn Hnn; rewrite HE2; apply ew_havoc_old; exact Hnn).
assert (HAE2 : env_agree 32 (Ereg regs' (xK G i)) Ev2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (EV : ew Ev2 516 = v)
  by (rewrite HE2; replace 516%nat with (512 + 4)%nat by reflexivity; rewrite (ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia); exact Hv).
assert (F19 : ew Ev2 19 = Z_to_bv 64 g) by (rewrite OLD by lia; exact E19).
assert (F26 : ew Ev2 26 = Z_to_bv 64 (32 * Z.of_nat i)) by (rewrite OLD by lia; exact E26).
assert (F27 : ew Ev2 27 = Z_to_bv 64 (32 * disco_classify_c.gn G)) by (rewrite OLD by lia; exact E27).
clear HE2.
pose proof (Forall_nil (shent_ok SEGS (SOff 21 0) Ev2 (mrestrict (w_H W) mem2)) : sh_ok SEGS (SOff 21 0) [] Ev2 (mrestrict (w_H W) mem2)) as SHOK2.
clear SHOK HJ HF HFr HG.
paj_run_tok RUN HS2 HJ2 SHOK2 GBspan; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
kw0 HFr KM2. clear HF HFr.
destruct (call_keep mem2 (ms_mem ms0) G HK2 HP2' HT2 HSV2 HOW2 (fun a Ha _ => KM2 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
  as (HK3 & HP3 & HT3 & HSV3 & HOW3). clear HG.
psrr_branch_tok RUN BR HS2 SHOK2 GBspan.
- apply (proj1 (beq0_iff Ev2 516 v EV)) in Hc. pose proof (proj1 XC Hc) as MI.
  assert (Gf : GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i)
    by (apply GateModel.gfind_Some_intro; [lia | intros j' Hj'; apply Hpre; lia | exact MI]).
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 GBspan 0x4cb8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
  kw0 HFr KM4. clear HF HFr.
  destruct (call_keep (ms_mem ms0) (ms_mem ms1) G HK3 HP3 HT3 HSV3 HOW3 (fun a Ha _ => KM4 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
    as (HK4 & HP4 & HT4 & HSV4 & HOW4). clear HG.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx (restrict _ ?mc) =>
    pose proof (regs_kept_of_st_ok_pi Ev2 ssx (restrict (w_H W) mc) regs' (xK G i) [2; 3; 4; 9; 21; 22]%bv HS2 HAE2 ltac:(vm_compute; reflexivity)) as HKR end.
  cbn [ms_regs restrict] in HKR.
  preg HS2 (18%bv : bv 5) R18'.
  rewrite (den_add2 Ev2 19 26 g (32 * Z.of_nat i) F19 F26) in R18' by lia.
  pmkst HS2.
  apply (FS i _ _ _ ltac:(lia) Gf HJ2 HK4 HP4 HT4 HSV4 HOW4).
  + unfold spZ. rewrite (HKR 2%bv ltac:(cbv; tauto)). exact Hsp.
  + rewrite (HKR 3%bv ltac:(cbv; tauto)). exact R3.
  + rewrite (HKR 4%bv ltac:(cbv; tauto)). exact R4.
  + rewrite (HKR 9%bv ltac:(cbv; tauto)). exact R9.
  + exact R18'.
  + rewrite (HKR 21%bv ltac:(cbv; tauto)). exact R21.
  + rewrite (HKR 22%bv ltac:(cbv; tauto)). exact R22.
- assert (NM : CtrlParsed.bytes_eqb (disco_classify_c.gmac G i) (CtrlParsed.fld Sg 0 6) = false).
  { apply Bool.not_true_iff_false. intros Hb.
    pose proof (proj2 (beq0_iff Ev2 516 v EV) (proj2 XC Hb)) as Ht. rewrite Ht in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS2 HJ2 SHOK2 GBspan; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
  kw0 HFr KM4. clear HF HFr.
  destruct (call_keep (ms_mem ms0) _ G HK3 HP3 HT3 HSV3 HOW3 (fun a Ha _ => KM4 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
    as (HK4 & HP4 & HT4 & HSV4 & HOW4). clear HG.
  psrr_branch_tok RUN BR HS2 SHOK2 GBspan.
  + rewrite (bne_off Ev2 27 26 (32 * disco_classify_c.gn G) (32 * Z.of_nat i) 32 F27 F26) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. assert (Hlt : (i + 1 < Z.to_nat (disco_classify_c.gn G))%nat) by lia.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 GBspan 0x4bb0; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
    kw0 HFr KM5. clear HF HFr.
    lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into msL end.
    destruct (call_keep _ (ms_mem msL) G HK4 HP4 HT4 HSV4 HOW4 (fun a Ha _ => KM5 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
      as (HK5 & HP5 & HT5 & HSV5 & HOW5). clear HG.
    lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx (restrict _ ?mc) =>
      pose proof (regs_kept_of_st_ok_pi Ev2 ssx (restrict (w_H W) mc) regs' (xK G i) [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 27]%bv HS2 HAE2 ltac:(vm_compute; reflexivity)) as HKR end.
    cbn [ms_regs restrict] in HKR.
    preg HS2 (26%bv : bv 5) R26'.
    rewrite (den_off Ev2 26 32 (32 * Z.of_nat i) F26) in R26' by lia.
    pmkst HS2.
    apply (IH Hlt _ _ _ Hlt).
    * intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact NM | apply Hpre; lia].
    * exact HJ2. * exact HK5. * exact HP5. * exact HT5. * exact HSV5. * exact HOW5.
    * unfold spZ. rewrite (HKR 2%bv ltac:(cbv; tauto)). exact Hsp.
    * rewrite (HKR 3%bv ltac:(cbv; tauto)). exact R3.
    * rewrite (HKR 4%bv ltac:(cbv; tauto)). exact R4.
    * rewrite (HKR 8%bv ltac:(cbv; tauto)). exact R8.
    * rewrite (HKR 9%bv ltac:(cbv; tauto)). exact R9.
    * rewrite (HKR 19%bv ltac:(cbv; tauto)). exact R19.
    * rewrite (HKR 20%bv ltac:(cbv; tauto)). exact R20.
    * rewrite (HKR 21%bv ltac:(cbv; tauto)). exact R21.
    * rewrite (HKR 22%bv ltac:(cbv; tauto)). exact R22.
    * rewrite (HKR 23%bv ltac:(cbv; tauto)). exact R23.
    * rewrite (HKR 24%bv ltac:(cbv; tauto)). exact R24.
    * rewrite (HKR 25%bv ltac:(cbv; tauto)). exact R25.
    * rewrite R26'. unfold w64. f_equal. lia.
    * rewrite (HKR 27%bv ltac:(cbv; tauto)). exact R27.
  + rewrite (bne_off Ev2 27 26 (32 * disco_classify_c.gn G) (32 * Z.of_nat i) 32 F27 F26) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. assert (Heq : (i + 1 = Z.to_nat (disco_classify_c.gn G))%nat) by lia.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 GBspan 0x4bd8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
    kw0 HFr KM5. clear HF HFr.
    lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into msL end.
    destruct (call_keep _ (ms_mem msL) G HK4 HP4 HT4 HSV4 HOW4 (fun a Ha _ => KM5 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
      as (HK5 & HP5 & HT5 & HSV5 & HOW5). clear HG.
    lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx (restrict _ ?mc) =>
      pose proof (regs_kept_of_st_ok_pi Ev2 ssx (restrict (w_H W) mc) regs' (xK G i) [2; 3; 4; 9; 19; 20; 21; 22; 23; 24; 25]%bv HS2 HAE2 ltac:(vm_compute; reflexivity)) as HKR end.
    cbn [ms_regs restrict] in HKR.
    pmkst HS2.
    apply AS.
    * apply GateModel.gfind_None_intro. intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact NM | apply Hpre; lia].
    * exact HJ2. * exact HK5. * exact HP5. * exact HT5. * exact HSV5. * exact HOW5.
    * unfold spZ. rewrite (HKR 2%bv ltac:(cbv; tauto)). exact Hsp.
    * rewrite (HKR 3%bv ltac:(cbv; tauto)). exact R3.
    * rewrite (HKR 4%bv ltac:(cbv; tauto)). exact R4.
    * rewrite (HKR 9%bv ltac:(cbv; tauto)). exact R9.
    * rewrite (HKR 19%bv ltac:(cbv; tauto)). exact R19.
    * rewrite (HKR 20%bv ltac:(cbv; tauto)). exact R20.
    * rewrite (HKR 21%bv ltac:(cbv; tauto)). exact R21.
    * rewrite (HKR 22%bv ltac:(cbv; tauto)). exact R22.
    * rewrite (HKR 23%bv ltac:(cbv; tauto)). exact R23.
    * rewrite (HKR 24%bv ltac:(cbv; tauto)). exact R24.
    * rewrite (HKR 25%bv ltac:(cbv; tauto)). exact R25.
Qed.
Lemma loop_all : found_stmt -> after_stmt -> forall d i, (i + d + 1 = Z.to_nat (disco_classify_c.gn G))%nat -> loop_stmt i.
Proof.
intros FS AS d. induction d as [|d IHd]; intros i Hd.
- apply (loop_step FS AS i). intros Hlt. lia.
- apply (loop_step FS AS i). intros _. apply IHd. lia.
Qed.

Definition pro_chunks : list YP09.chunk :=
  [ckv (-112) 8 12; ckv (-104) 8 27; ckv (-96) 8 26; ckv (-88) 8 25; ckv (-80) 8 24; ckv (-72) 8 23; ckv (-64) 8 22;
   ckv (-56) 8 21; ckv (-48) 8 20; ckv (-40) 8 19; ckv (-32) 8 18; ckv (-24) 8 9; ckv (-16) 8 8; ckv (-8) 8 1].
Lemma pro_tsv : forall E m,
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 pro_chunks) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
  tSV m /\ tOW m.
Proof.
intros E m R EE.
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv) by reflexivity; reflexivity).
assert (F : forall od q (n : nat), In (ckv od 8 n) pro_chunks -> Z.of_nat n = bv_unsigned q ->
   val_mem SEGS (mrestrict (w_H W) m) (spZ regs + od) 8 (bv_unsigned (getr regs q))).
{ intros od q n Hin Hn.
  exact (field_of_region E _ 2 (spZ regs) pro_chunks (-112) 0 (-112) 0 od 8 (SOff n 0) (bv_unsigned (getr regs q)) R B2 Hin
     ltac:(rewrite den_atom0, (EE n q Hn), Z_to_bv_bv_unsigned; reflexivity)
     ltac:(pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; cbn in Hb |- *; lia) ltac:(cbn; lia)). }
split.
- intros o q Hin. cbv [SAVSL In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-;
    lazymatch goal with |- val_mem _ _ (spZ regs - 112 + ?o) _ (bv_unsigned (getr regs ?q)) =>
      let od := eval vm_compute in (o - 112) in let nq := eval vm_compute in (Z.to_nat (bv_unsigned q)) in
      replace (spZ regs - 112 + o) with (spZ regs + od) by lia; apply (F od q nq);
      [cbv [pro_chunks]; repeat (first [apply in_eq | apply in_cons]) | reflexivity] end |]).
  destruct Hin.
- unfold tOW. replace (spZ regs - 112 + 0) with (spZ regs + (-112)) by lia.
  pose proof (F (-112) 12%bv 12%nat ltac:(cbv [pro_chunks]; apply in_eq) eq_refl) as V.
  rewrite H12 in V. unfold w64 in V. rewrite unsigned_lit_small in V by lia. exact V.
Qed.
Lemma pro_kept : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
  tKP m /\ tTB m G.
Proof.
intros m HK. pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg'.
split.
- intros a Ha Hs Hg. apply HK; [exact Ha|]. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. lia.
- split; [|exact HGl]. apply (ga_kept memc m g); [|exact HGa]. intros a Ha. rewrite length_map, HGl in Ha.
  apply HK; unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia.
Qed.
Lemma gn_fu : disco_classify_c.gn G = CtrlParsed.fu G 256 4.
Proof.
pose proof (gsp_fu_n G HGok) as Hn. unfold disco_classify_c.gn, CtrlParsed.s32.
destruct (Z.ltb_spec (CtrlParsed.fu G 256 4) (2 ^ 31)); lia.
Qed.
Lemma s11_val : forall E nn, ew E 33 = Z_to_bv 64 nn -> 1 <= nn <= 8 ->
  sv_denot E (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) (SLit 5)) =
  Z_to_bv 64 (32 * nn).
Proof.
intros E nn H Hn.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) (SLit 5)) = 32 * nn).
rewrite !U_SAlu, !U_SLit, U_SOff, H.
assert (C : nn = 1 \/ nn = 2 \/ nn = 3 \/ nn = 4 \/ nn = 5 \/ nn = 6 \/ nn = 7 \/ nn = 8) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma gdk_T : forall E, CtrlParsed.fb Sg 12 = 0 -> sv_denot E (SLit 18446744073709551615) = w64 (gdk Sg).
Proof.
intros E H. unfold gdk, GateModel.gdk. rewrite H. cbn [Z.eqb]. cbn [sv_denot]. unfold w64.
apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.
Lemma gdk_F : forall E, CtrlParsed.fb Sg 12 <> 0 -> ew E 35 = Z_to_bv 64 (CtrlParsed.fb Sg 13) -> ew E 36 = Z_to_bv 64 (CtrlParsed.fb Sg 14) ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 36 0)) = w64 (gdk Sg).
Proof.
intros E H H35 H36. unfold gdk, GateModel.gdk. destruct (Z.eqb_spec (CtrlParsed.fb Sg 12) 0) as [E0|_]; [contradiction|].
pose proof (GateModel.fb_rng Sg 13) as R13. pose proof (GateModel.fb_rng Sg 14) as R14.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). unfold w64. f_equal.
change (U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 36 0)) = 256 * CtrlParsed.fb Sg 13 + CtrlParsed.fb Sg 14).
rewrite !U_SAlu, U_SLit, (U_atom E 35 _ H35), (U_atom E 36 _ H36) by lia. cbn [zalu_raw].
change (Z.land (zcanon 8) 63) with 8.
rewrite Z.lor_comm.
rewrite (zcanon_id (Z.shiftl _ 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite Bytes.lor_shiftl8_add by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma br_ge0 : forall E kk nn, ew E kk = Z_to_bv 64 nn -> 0 <= nn <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff kk 0)) = negb (0 <? nn).
Proof.
intros E kk nn H Hn. cbn [branch_taken]. rewrite den_atom0, H. cbn [sv_denot].
rewrite bv_lts_small by lia. reflexivity.
Qed.
Ltac kwS Usp HFr K :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> aview SEGS H m' a = aview SEGS H m a);
  [ let a_ := fresh "a" in let Ha_ := fresh "Ha" in let Hn_ := fresh "Hn" in intros a_ Ha_ Hn_;
    apply (kept_of_frame (segs := SEGS) Ex rs H m m' (fun a => spZ regs - 112 <= a < spZ regs) HFr); [ | exact Ha_ | exact Hn_];
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b_ := fresh "b" in let wlo_ := fresh "wlo" in let whi_ := fresh "whi" in let x_ := fresh "x" in
    let Hin_ := fresh "Hin" in let Hx_ := fresh "Hx" in
    intros b_ wlo_ whi_ x_ Hin_ Hx_; cbn [In] in Hin_;
    repeat (destruct Hin_ as [Hin_|Hin_]; [injection Hin_ as <- <- <-; cbn [base_val] in Hx_; first [lia | rewrite Usp in Hx_; lia] |]);
    try destruct Hin_
  | ] end.

Lemma den_not : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros E n x Hn Hx. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x). apply U_not; assumption.
Qed.
Ltac awr_pro Usp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
      [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia | ] ].
Ltac pro_step Usp MK PG :=
  let K := fresh "K" in
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HF : frame_of _ _ _ _ |- _ =>
  kwS Usp HFr K;
  lazymatch type of K with forall a, _ -> _ -> aview _ _ ?m' a = aview _ _ ?m a =>
  let MK2 := fresh "MK" in let PG2 := fresh "PG" in
  assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) memc a)
    by (intros a_ Ha_ Hn_; rewrite K by assumption; apply MK; assumption);
  assert (PG2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) m' a)
    by (intros a_ Ha_; apply (apresent_grows _ _ _ a_ HG); apply PG; exact Ha_);
  clear K MK PG HF HFr HG; rename MK2 into MK; rename PG2 into PG end end.

Ltac pro_regs E HS Hz E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn :=
  let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in let Q9 := fresh "Q9" in
  let Q19 := fresh "Q19" in let Q20 := fresh "Q20" in let Q21 := fresh "Q21" in let Q22 := fresh "Q22" in
  let Q23 := fresh "Q23" in let Q24 := fresh "Q24" in let Q25 := fresh "Q25" in
  preg HS (2%bv : bv 5) Q2; preg HS (3%bv : bv 5) Q3; preg HS (4%bv : bv 5) Q4; preg HS (9%bv : bv 5) Q9;
  preg HS (19%bv : bv 5) Q19; preg HS (20%bv : bv 5) Q20; preg HS (21%bv : bv 5) Q21; preg HS (22%bv : bv 5) Q22;
  preg HS (23%bv : bv 5) Q23; preg HS (24%bv : bv 5) Q24; preg HS (25%bv : bv 5) Q25;
  rewrite (den_off E 2 (-112) (spZ regs) E2) in Q2 by lia;
  rewrite den_atom0, E3 in Q3; rewrite den_atom0, E4 in Q4; rewrite den_atom0, E11 in Q9; rewrite den_atom0, E10 in Q19;
  rewrite (den_off E 10 256 g E10) in Q20 by lia; rewrite den_atom0, E32 in Q21;
  first [rewrite (gdk_T E Hz) in Q22 | rewrite (gdk_F E Hz E35 E36) in Q22];
  rewrite (den_not E 10 g E10) in Q23 by lia; rewrite den_atom0, E33, <- Egn in Q24;
  rewrite (denot_shx E 10 32 256 g GSB E10 E32) in Q25 by (unfold GSB; lia).
Ltac pro_mem E HS MK EE HKf HTf HSVf HOWf :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?mc) =>
  destruct (pro_kept (ms_mem mc) MK) as [HKf HTf];
  let RS := fresh "RS" in
  pose proof (st_ok_pi_region_nth E ss _ 1 (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 pro_chunks) HS ltac:(vm_compute; reflexivity)) as RS;
  cbn [ms_mem restrict] in RS;
  destruct (pro_tsv E (ms_mem mc) RS EE) as [HSVf HOWf] end.
Ltac pro_after AS E HS MK PG EE Hz Hc E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn :=
  let HKf := fresh "HKf" in let HTf := fresh "HTf" in let HSVf := fresh "HSVf" in let HOWf := fresh "HOWf" in
  pro_mem E HS MK EE HKf HTf HSVf HOWf;
  pro_regs E HS Hz E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn;
  pmkst HS;
  apply AS;
  [ rewrite Egn; replace (CtrlParsed.fu G 256 4) with 0 by lia; reflexivity
  | eassumption | exact HKf | exact PG | exact HTf | exact HSVf | exact HOWf
  | unfold spZ at 1; match goal with Q : getr _ 2 = _ |- _ => rewrite Q end; rewrite unsigned_lit_small by lia; lia
  | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption | assumption
  | match goal with Q : getr _ 25 = _ |- _ => rewrite Q end; unfold w64; f_equal; lia ].
Ltac pro_loop FS AS E HS MK PG EE Hz Hc E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn :=
  let HKf := fresh "HKf" in let HTf := fresh "HTf" in let HSVf := fresh "HSVf" in let HOWf := fresh "HOWf" in
  pro_mem E HS MK EE HKf HTf HSVf HOWf;
  pro_regs E HS Hz E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn;
  let Q8 := fresh "Q8" in let Q26 := fresh "Q26" in let Q27 := fresh "Q27" in
  preg HS (8%bv : bv 5) Q8; preg HS (26%bv : bv 5) Q26; preg HS (27%bv : bv 5) Q27;
  rewrite (s11_val E (CtrlParsed.fu G 256 4) E33) in Q27 by lia; rewrite <- Egn in Q27;
  pmkst HS;
  apply (loop_all FS AS (Z.to_nat (disco_classify_c.gn G) - 1) 0 ltac:(lia));
  [ lia | intros j Hj; lia
  | eassumption | exact HKf | exact PG | exact HTf | exact HSVf | exact HOWf
  | unfold spZ at 1; match goal with Q : getr _ 2 = _ |- _ => rewrite Q end; rewrite unsigned_lit_small by lia; lia
  | assumption | assumption | rewrite Q8; reflexivity | assumption | assumption | assumption | assumption | assumption | assumption
  | assumption
  | match goal with Q : getr _ 25 = _ |- _ => rewrite Q end; unfold w64; f_equal; lia
  | rewrite Q26; reflexivity | exact Q27 ].
Lemma main_ok : found_stmt -> after_stmt ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_disco_gate_should_push) regs memc mdc) tQ.
Proof.
intros FS AS.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof (gsp_fu_n G HGok) as Hfn. pose proof (proj1 (proj2 HGok)) as Hn. pose proof gn_fu as Egn.
assert (WS : REAC_DISCO_GATE_SHOULD_PUSH_STK = 8304) by reflexivity.
destruct (gsp_entry fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s G Sg HJc H10 H11 Hal Hwin Hspl Hg0 Hg8 Hgam Hgside
  (fun a Ha => proj1 (Hgw a Ha)) Hgra Hs0 Hs4 Hsam Hsra HGl HGa HGok) as [HS SHOK].
remember (Eimg (Ereg regs (ge_extra G Sg))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros; subst E; apply ew_Eimg_Ereg_nat; assumption).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv) by reflexivity; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 g) by (rewrite (EE 10%nat 10%bv) by reflexivity; exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 s) by (rewrite (EE 11%nat 11%bv) by reflexivity; exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 GSB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (CtrlParsed.fu G 256 4)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (CtrlParsed.fb Sg 12)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (CtrlParsed.fb Sg 13)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (CtrlParsed.fb Sg 14)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; apply unsigned_lit_small; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_disco_gate_should_push)) with (Z_to_bv 64 (BASE + AF_both3_reac_disco_gate_should_push)).
pose proof HJc as HJ.
assert (MK : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (PG : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros; assumption).
paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4b08; [awr_pro Usp|].
pro_step Usp MK PG.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let rs := eval vm_compute in [nth 0 (ss_mem ss) (stack_region 0); nth 3 (ss_mem ss) (stack_region 0)] in
  pose proof (st_ok_pi_submem E ss _ rs HS ltac:(lazymatch goal with |- submem ?a ?b => let b' := eval vm_compute in b in change (submem a b') end; submem_tac) ltac:(vm_compute; reflexivity)) as HS1 end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS1. clear HS.
lazymatch type of HS1 with st_ok_pi _ _ _ ?ss1 ?ms1 =>
  pose proof (st_ok_pi_add_region E ss1 ms1 ge_sig HS1 eq_refl) as HS2 end.
clear HS1.
lazymatch type of HS2 with _ -> _ -> st_ok_pi _ _ _ _ (restrict _ ?mc) =>
  assert (HSm : garr8 SEGS (mrestrict (w_H W) (ms_mem mc)) s (map (fun b : byte => bv_unsigned b) Sg))
    by (apply (ga_kept memc (ms_mem mc) s); [intros a Ha; rewrite length_map, HSl in Ha; apply MK; lia | exact HSa]) end.
match type of HS2 with ?A1 -> _ => assert (HRO : A1); [|specialize (HS2 HRO); clear HRO] end.
{ unfold ge_sig, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
  rewrite E11, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  pose proof (GateModel.fb_rng Sg 12). pose proof (GateModel.fb_rng Sg 13). pose proof (GateModel.fb_rng Sg 14).
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ s 12 1 (SOff 34 0) (CtrlParsed.fb Sg 12)); [rewrite den_atom0; exact E34 | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 12) by lia. exact (gsp_val_mem _ s Sg 12 1 HSm ltac:(lia)).
  - apply (chunk_ok_val SEGS E _ s 13 1 (SOff 35 0) (CtrlParsed.fb Sg 13)); [rewrite den_atom0; exact E35 | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 13) by lia. exact (gsp_val_mem _ s Sg 13 1 HSm ltac:(lia)).
  - apply (chunk_ok_val SEGS E _ s 14 1 (SOff 36 0) (CtrlParsed.fb Sg 14)); [rewrite den_atom0; exact E36 | cbn; lia | cbn; lia |].
    rewrite <- (gsp_fu1 Sg 14) by lia. exact (gsp_val_mem _ s Sg 14 1 HSm ltac:(lia)). }
match type of HS2 with ?A1 -> _ => assert (HRD : A1); [|specialize (HS2 HRD); clear HRD] end.
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  unfold ge_sig. cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E11, E10, Usp, !unsigned_lit_small by lia.
  unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. repeat split; lia. }
cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS2. clear HSm.
rename HS2 into HS.
paj_run_tok RUN HS HJ SHOK GBspan; [awr_pro Usp|].
pro_step Usp MK PG.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by (pose proof (GateModel.fb_rng Sg 12); lia).
  apply Z.eqb_eq in Hc. rename Hc into Hz.
  paj_run_tok RUN HS HJ SHOK GBspan; [awr_pro Usp|].
  pro_step Usp MK PG.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (br_ge0 E 33 _ E33) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4bd8; [awr_pro Usp|].
    pro_step Usp MK PG.
    pro_after AS E HS MK PG EE Hz Hc E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn.
  + rewrite (br_ge0 E 33 _ E33) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4bb0; [awr_pro Usp|].
    pro_step Usp MK PG.
    pro_loop FS AS E HS MK PG EE Hz Hc E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn.
- rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by (pose proof (GateModel.fb_rng Sg 12); lia).
  apply Z.eqb_neq in Hc. rename Hc into Hz.
  paj_run_tok RUN HS HJ SHOK GBspan; [awr_pro Usp|].
  pro_step Usp MK PG.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (br_ge0 E 33 _ E33) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4bd8; [awr_pro Usp|].
    pro_step Usp MK PG.
    pro_after AS E HS MK PG EE Hz Hc E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn.
  + rewrite (br_ge0 E 33 _ E33) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4bb0; [awr_pro Usp|].
    pro_step Usp MK PG.
    pro_loop FS AS E HS MK PG EE Hz Hc E2 E3 E4 E10 E11 E32 E33 E35 E36 Egn.
Qed.
Ltac zrng := match goal with |- 0 <= _ < 2 ^ (8 * Z.of_N ?w) => let v := eval vm_compute in (2 ^ (8 * Z.of_N w)) in change (2 ^ (8 * Z.of_N w)) with v end; lia.

Definition AF32 : afact := mkAF 0 (2 ^ 32 - 1) 0.
Definition AF8 : afact := mkAF 0 255 0.
Definition rF_a : YP09.region := YP09.mkRegion (Some 18%nat) 8 17 8 17 [ckv 8 4 46; ckv 12 4 47; ckv 16 1 48].
Definition rF_b : YP09.region := YP09.mkRegion (Some 18%nat) 24 32 24 32 [ckv 24 8 49].
Definition rF_sig : YP09.region := YP09.mkRegion (Some 9%nat) 8 17 0 0 [ckv 8 4 50; ckv 16 1 51].
Definition fa_F : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4 (2 ^ 47 - 25) 2); (18%nat, mkAF 8 (2 ^ 47 - 41) 3);
   (21%nat, mkAF GSB GSB 0); (46%nat, AF32); (47%nat, AF32); (48%nat, AF8); (50%nat, AF32); (51%nat, AF8)] [] [].
Definition ss_G (pc : Z) (upd : list (bv 5 * sv)) : sstate := mkSS pc (sr_sets sr_atoms upd) [rK_stk; rF_a; rF_b; rF_sig] None fa_F.
Definition SH_F : list shent := [mkSHE 18 8 32; mkSHE 9 8 17].
Ltac ekv rg X i n H :=
  let v := eval cbv [EK Eimg Ereg xK ew A_TEXT A_LIM Nat.leb Nat.ltb andb Nat.sub nth map] in (ew (EK rg X i) n) in
  assert (H : ew (EK rg X i) n = v) by reflexivity.
Lemma kst_G : forall pc upd regs' m X i,
  NoDup (map fst upd) ->
  Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot (EK regs' X i) (snd p)) upd ->
  tSV m -> tOW m -> tKP m -> tPR m -> tTB m X -> (i < 8)%nat -> spZ regs' = spZ regs - 112 ->
  getr regs' 9 = w64 s -> getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB ->
  st_ok_pi SEGS VAL (EK regs' X i) (ss_G pc upd) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 21 0) SH_F (EK regs' X i) (mrestrict (w_H W) m).
Proof.
intros pc upd regs' m X i HND HUPD HSV HOW HK HP [HX HXl] Hi Hsp R9 R18 R21.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
assert (Hg8b : 8 <= g) by (pose proof (Z.div_mod g 8 ltac:(lia)) as Dg; rewrite Hg8 in Dg; lia).
assert (Hs4b : 4 <= s) by (pose proof (Z.div_mod s 4 ltac:(lia)) as Ds; rewrite Hs4 in Ds; lia).
pose proof (kp_garr8_S m HK) as HSm.
ekv regs' X i 46%nat E46. ekv regs' X i 47%nat E47. ekv regs' X i 48%nat E48. ekv regs' X i 49%nat E49.
ekv regs' X i 50%nat E50. ekv regs' X i 51%nat E51.
assert (E2 : ew (EK regs' X i) 2 = getr regs' 2) by (apply ek_reg; reflexivity).
assert (E9 : ew (EK regs' X i) 9 = Z_to_bv 64 s) by (rewrite (ek_reg regs' X i 9%bv 9 eq_refl); exact R9).
assert (E18 : ew (EK regs' X i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i)) by (rewrite (ek_reg regs' X i 18%bv 18 eq_refl); exact R18).
assert (E21 : ew (EK regs' X i) 21 = Z_to_bv 64 GSB) by (rewrite (ek_reg regs' X i 21%bv 21 eq_refl); exact R21).
set (E := EK regs' X i) in *.
pose proof (GateModel.fu_rng4 X (32 * i + 8) ltac:(lia)) as R46. pose proof (GateModel.fu_rng4 X (32 * i + 12) ltac:(lia)) as R47.
pose proof (GateModel.fb_rng X (32 * i + 16)) as R48. pose proof (GateModel.fu_rng8 X (32 * i + 24) ltac:(lia)) as R49.
pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R50. pose proof (GateModel.fb_rng Sg 16) as R51.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
assert (Hwr : forall a, g <= a < g + 264 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Hgw a Ha)). }
assert (VG : forall (k n : nat), (k + n <= 264)%nat -> val_mem SEGS (mrestrict (w_H W) m) (g + Z.of_nat k) n (CtrlParsed.fu X k n))
  by (intros k0 n0 Hk; apply gsp_val_mem; [exact HX | lia]).
assert (VS : forall (k n : nat), (k + n <= 24)%nat -> val_mem SEGS (mrestrict (w_H W) m) (s + Z.of_nat k) n (CtrlParsed.fu Sg k n))
  by (intros k0 n0 Hk; apply gsp_val_mem; [exact HSm | lia]).
rewrite restrict_mkst_fx. split.
- unfold ss_G. apply pa_entry_st_ok_full.
  + apply (regs_ok_sets _ sr_atoms regs' regs' upd); [unfold E, EK; apply regs_ok_Eimg_Ereg | exact HND | intros r _; reflexivity | exact HUPD].
  + vm_compute. reflexivity.
  + apply Forall_cons; [exact (stk_region_ok regs' m X i HSV HOW Hsp)|].
    unfold rF_a, rF_b, rF_sig, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 18%nat _ E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ _ 8 4 (SOff 46 0) (CtrlParsed.fu X (32 * i + 8) 4)); [rewrite den_atom0; exact E46 | zrng | cbn; lia |].
         replace (g + 32 * Z.of_nat i + 8) with (g + Z.of_nat (32 * i + 8)) by lia. apply VG. lia.
      -- apply (chunk_ok_val SEGS E _ _ 12 4 (SOff 47 0) (CtrlParsed.fu X (32 * i + 12) 4)); [rewrite den_atom0; exact E47 | zrng | cbn; lia |].
         replace (g + 32 * Z.of_nat i + 12) with (g + Z.of_nat (32 * i + 12)) by lia. apply VG. lia.
      -- apply (chunk_ok_val SEGS E _ _ 16 1 (SOff 48 0) (CtrlParsed.fb X (32 * i + 16))); [rewrite den_atom0; exact E48 | zrng | cbn; lia |].
         replace (g + 32 * Z.of_nat i + 16) with (g + Z.of_nat (32 * i + 16)) by lia. rewrite <- gsp_fu1 by lia. apply VG. lia.
    * rewrite (VB 18%nat _ E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 49 0) (CtrlParsed.fu X (32 * i + 24) 8)); [rewrite den_atom0; exact E49 | zrng | cbn; lia |].
      replace (g + 32 * Z.of_nat i + 24) with (g + Z.of_nat (32 * i + 24)) by lia. apply VG. lia.
    * rewrite (VB 9%nat _ E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ _ 8 4 (SOff 50 0) (CtrlParsed.fu Sg 8 4)); [rewrite den_atom0; exact E50 | zrng | cbn; lia |].
         apply (VS 8%nat 4%nat). lia.
      -- apply (chunk_ok_val SEGS E _ _ 16 1 (SOff 51 0) (CtrlParsed.fb Sg 16)); [rewrite den_atom0; exact E51 | zrng | cbn; lia |].
         rewrite <- gsp_fu1 by lia. apply (VS 16%nat 1%nat). lia.
  + apply pairwise_disjoint_of_extents. unfold rK_stk, rF_a, rF_b, rF_sig, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 18%nat _ E18), (VB 9%nat _ E9) by lia.
    cbn [base_val]. rewrite E2. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold fa_F, AF32, AF8. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E18, E21, E46, E47, E48, E50, E51. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold GSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    assert (Hm2 : (g + 32 * Z.of_nat i) mod 8 = 0) by (rewrite Zplus_mod, Hg8, Zmult_mod; reflexivity).
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo.
    unfold GSB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, SH_F. repeat apply Forall_cons; try apply Forall_nil.
  + apply (shent_ok_of_range SEGS (w_H W) m E (SOff 21 0) 18 g 264 (g + 32 * Z.of_nat i) 8 32).
    * exact (kp_ra m g 264 HK ltac:(lia) Hgam ltac:(lia) Hgra).
    * apply (U_atom E 21 GSB E21). unfold GSB; lia.
    * apply (U_atom E 18 _ E18). lia.
    * lia. * lia.
    * intros x Hx. unfold SHADOW_OFF. cbn [Z.min Z.max] in Hx. lia.
  + apply (shent_ok_of_range SEGS (w_H W) m E (SOff 21 0) 9 s 24 s 8 17).
    * exact (kp_ra m s 24 HK ltac:(lia) Hsam ltac:(lia) Hsra).
    * apply (U_atom E 21 GSB E21). unfold GSB; lia.
    * apply (U_atom E 9 _ E9). lia.
    * lia. * lia.
    * intros x Hx. unfold SHADOW_OFF. cbn [Z.min Z.max] in Hx. lia.
Qed.

Definition gbn (M : word -> option byte) (X : list byte) : Prop :=
  length X = 264%nat /\ forall j b, nth_error X j = Some b -> mbyte SEGS M (g + Z.of_nat j) = Some b.
Definition wcov (ws : list (nat * nat * Z)) (j : nat) : Prop :=
  Exists (fun x : nat * nat * Z => let '(o, w, _) := x in (o <= j < o + w)%nat) ws.
Lemma gbn_cover : forall ws M M' X X', gbn M X -> length X' = 264%nat ->
  Forall (fun x : nat * nat * Z => let '(o, w, v) := x in
    0 <= v /\ val_mem SEGS M' (g + Z.of_nat o) w v /\ CtrlParsed.fld X' o w = Z_to_le_bytes w v /\ (o + w <= 264)%nat) ws ->
  (forall j, (j < 264)%nat -> ~ wcov ws j -> mbyte SEGS M' (g + Z.of_nat j) = mbyte SEGS M (g + Z.of_nat j) /\ nth_error X' j = nth_error X j) ->
  gbn M' X'.
Proof.
intros ws M M' X X' [HL HN] HL' HV HF. split; [exact HL'|]. intros j b Hj.
assert (Hjl : (j < 264)%nat) by (rewrite <- HL'; apply nth_error_Some; rewrite Hj; discriminate).
destruct (Exists_dec (fun x : nat * nat * Z => let '(o, w, _) := x in (o <= j < o + w)%nat) ws) as [Hc | Hc].
- intros [[o w] v]. destruct (le_lt_dec o j); destruct (lt_dec j (o + w)); [left; lia | right; lia | right; lia | right; lia].
- apply Exists_exists in Hc as ([[o w] v] & Hin & Hov).
  rewrite Forall_forall in HV. destruct (HV _ Hin) as (Hv0 & Hvm & Hs & Hw).
  assert (Hn : nth_error (CtrlParsed.fld X' o w) (j - o) = nth_error X' j).
  { rewrite GateModel.nth_error_fld. destruct (Nat.ltb_spec (j - o) w); [f_equal; lia | lia]. }
  rewrite Hs, Hj in Hn. rewrite le_bytes_nth in Hn by lia. injection Hn as <-.
  pose proof (Hvm (j - o)%nat ltac:(lia)) as Hb.
  replace (g + Z.of_nat o + Z.of_nat (j - o)) with (g + Z.of_nat j) in Hb by lia. rewrite Hb.
  f_equal. cbv delta [YG0f.le_byte YO0f.le_byte] beta. rewrite z8_mod. apply YC4b.low_byte_mod; lia.
- destruct (HF j Hjl Hc) as [Hm Hx]. rewrite Hm. rewrite Hx in Hj. exact (HN j b Hj).
Qed.

Lemma tTB_gbn : forall m X, tTB m X -> gbn (mrestrict (w_H W) m) X.
Proof. intros m X [HG HL]. split; [exact HL|]. intros j b Hj. exact (garr8_byte _ _ _ _ _ HG Hj). Qed.
Lemma gbn_tTB : forall m X, gbn (mrestrict (w_H W) m) X -> tTB m X.
Proof.
intros m X [HL HN]. split; [|exact HL]. intros j Hj. rewrite length_map in Hj.
destruct (nth_error X j) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) X) 0 = bv_unsigned b)
  by (apply nth_error_nth; rewrite nth_error_map, Hb; reflexivity).
rewrite Hn. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr.
split; [|lia]. intros kk Hk. destruct kk as [|kk]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, (HN j b Hb).
rewrite gle_byte_1_0 by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ent_tb : forall m m' X X' (i : nat) (v8 v12 v16 v24 : Z),
  (i < 8)%nat -> tTB m X -> length X' = 264%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 17) ->
     ~ (g + 32 * Z.of_nat i + 24 <= a < g + 32 * Z.of_nat i + 32) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall j, (j < 264)%nat -> ~ (32 * i + 8 <= j < 32 * i + 17)%nat -> ~ (32 * i + 24 <= j < 32 * i + 32)%nat ->
     nth_error X' j = nth_error X j) ->
  0 <= v8 -> val_mem SEGS (mrestrict (w_H W) m') (g + 32 * Z.of_nat i + 8) 4 v8 -> CtrlParsed.fld X' (32 * i + 8) 4 = Z_to_le_bytes 4 v8 ->
  0 <= v12 -> val_mem SEGS (mrestrict (w_H W) m') (g + 32 * Z.of_nat i + 12) 4 v12 -> CtrlParsed.fld X' (32 * i + 12) 4 = Z_to_le_bytes 4 v12 ->
  0 <= v16 -> val_mem SEGS (mrestrict (w_H W) m') (g + 32 * Z.of_nat i + 16) 1 v16 -> CtrlParsed.fld X' (32 * i + 16) 1 = Z_to_le_bytes 1 v16 ->
  0 <= v24 -> val_mem SEGS (mrestrict (w_H W) m') (g + 32 * Z.of_nat i + 24) 8 v24 -> CtrlParsed.fld X' (32 * i + 24) 8 = Z_to_le_bytes 8 v24 ->
  tTB m' X'.
Proof.
intros m m' X X' i v8 v12 v16 v24 Hi HT HL' HM HX P8 V8 F8 P12 V12 F12 P16 V16 F16 P24 V24 F24.
pose proof Hgam as Hg'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg'.
apply gbn_tTB. apply (gbn_cover [(32 * i + 8, 4, v8); (32 * i + 12, 4, v12); (32 * i + 16, 1, v16); (32 * i + 24, 8, v24)]%nat
  (mrestrict (w_H W) m) _ X X' (tTB_gbn m X HT) HL').
- repeat apply Forall_cons; try apply Forall_nil; cbv beta iota; (split; [assumption|]); (split; [|split; [assumption | lia]]);
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z.add_assoc; assumption.
- intros j Hj Hc. split.
  + apply (mbyte_of_aview SEGS). apply HM; [lia | |].
    * intros Hr. apply Hc. unfold wcov. destruct (Nat.lt_ge_cases j (32 * i + 12)); [apply Exists_cons_hd; lia|].
      apply Exists_cons_tl. destruct (Nat.lt_ge_cases j (32 * i + 16)); [apply Exists_cons_hd; lia|].
      apply Exists_cons_tl. apply Exists_cons_hd. lia.
    * intros Hr. apply Hc. unfold wcov. do 3 apply Exists_cons_tl. apply Exists_cons_hd. lia.
  + apply HX; [exact Hj | |].
    * intros Hr. apply Hc. unfold wcov. destruct (Nat.lt_ge_cases j (32 * i + 12)); [apply Exists_cons_hd; lia|].
      apply Exists_cons_tl. destruct (Nat.lt_ge_cases j (32 * i + 16)); [apply Exists_cons_hd; lia|].
      apply Exists_cons_tl. apply Exists_cons_hd. lia.
    * intros Hr. apply Hc. unfold wcov. do 3 apply Exists_cons_tl. apply Exists_cons_hd. lia.
Qed.
Lemma apres_of : forall regs2,
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 19 = getr regs 19 -> getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 ->
  getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 ->
  getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
  aregs_preserved regs regs2.
Proof.
intros regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 q Hq. unfold acallee_saved in Hq.
destruct Hq as [-> | [-> | [-> | [-> | [-> | Hq]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 |].
assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
destruct Hq' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; assumption.
Qed.

Lemma bltu_atoms : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff a 0)) (sv_denot E (SOff b 0)) = (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. rewrite branch_ltu_U, (U_atom E a x Ha Hx), (U_atom E b y Hb Hy). reflexivity. Qed.
Lemma bltu_diff_rf : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= y <= x -> x < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1))))) (sv_denot E (SLit 1000000000)) =
  (x - y <? GateModel.RF).
Proof.
intros E a b x y Ha Hb Hxy Hx. rewrite branch_ltu_U, U_lit by lia. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb), U_SLit by lia.
replace (zcanon (y * zcanon (-1))) with (zcanon (- y)) by (unfold zcanon, M64; rewrite Z.mul_mod_idemp_r by lia; f_equal; lia).
unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small by lia. unfold GateModel.RF. reflexivity.
Qed.
Definition fT_stmt : Prop := forall (i : nat) regs' m md,
  (i < Z.to_nat (disco_classify_c.gn G))%nat ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = false ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 16 = w64 now -> getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4d4c)) m (seg_rom SEGS)) md) tQ.
Ltac awrF e E18 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18 e);
      [reflexivity | rewrite E18; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; let a_ := fresh "a" in let Ha_ := fresh "Ha" in intros a_ Ha_; apply (proj1 (Hgw a_ ltac:(lia))) | ] ].
Ltac kwE e E18 HFr K :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (e + 8 <= a < e + 17) -> ~ (e + 24 <= a < e + 32) -> aview SEGS H m' a = aview SEGS H m a);
  [ let a_ := fresh "a" in let Ha_ := fresh "Ha" in let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in intros a_ Ha_ Hn1 Hn2;
    apply (kept_of_frame (segs := SEGS) Ex rs H m m' (fun a => e + 8 <= a < e + 17 \/ e + 24 <= a < e + 32) HFr); [ | exact Ha_ | tauto];
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b_ := fresh "b" in let wlo_ := fresh "wlo" in let whi_ := fresh "whi" in let x_ := fresh "x" in
    let Hin_ := fresh "Hin" in let Hx_ := fresh "Hx" in
    intros b_ wlo_ whi_ x_ Hin_ Hx_; cbn [In] in Hin_;
    repeat (destruct Hin_ as [Hin_|Hin_]; [injection Hin_ as <- <- <-; cbn [base_val] in Hx_; first [lia | rewrite E18, unsigned_lit_small in Hx_ by lia; lia] |]);
    try destruct Hin_
  | ] end.
Lemma ent_keep : forall m m' i, (i < 8)%nat -> tKP m -> tPR m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 17) ->
     ~ (g + 32 * Z.of_nat i + 24 <= a < g + 32 * Z.of_nat i + 32) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  tKP m' /\ tPR m'.
Proof.
intros m m' i Hi HK HP HM HG. split.
- intros a Ha Hs Hg2. rewrite HM by lia. apply HK; assumption.
- intros a Ha. apply (apresent_grows _ _ _ a HG). apply HP. exact Ha.
Qed.
Lemma ent_sv : forall m m', tSV m -> tOW m -> (forall a, 0 <= a < 2 ^ 64 -> spZ regs - 112 <= a < spZ regs -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  tSV m' /\ tOW m'.
Proof.
intros m m' HSV HOW HM. pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo. split.
- intros o q Hin. apply (vm_kept m m'); [|exact (HSV o q Hin)]. intros x Hx.
  assert (Ho : 8 <= o <= 104) by (cbv [SAVSL In] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]); destruct Hin).
  apply HM; lia.
- apply (vm_kept m m'); [|exact HOW]. intros x Hx. apply HM; lia.
Qed.

Lemma ent_leaf : forall E m m' X X' (i : nat) cs1 cs2 lo1 hi1 lo2 hi2 e8 e12 e16 e24 v8 v12 v16 v24,
  (i < 8)%nat -> tTB m X -> length X' = 264%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 17) ->
     ~ (g + 32 * Z.of_nat i + 24 <= a < g + 32 * Z.of_nat i + 32) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall j, (j < 264)%nat -> ~ (32 * i + 8 <= j < 32 * i + 17)%nat -> ~ (32 * i + 24 <= j < 32 * i + 32)%nat ->
     nth_error X' j = nth_error X j) ->
  region_ok SEGS E (mrestrict (w_H W) m') (YP09.mkRegion (Some 18%nat) lo1 hi1 lo1 hi1 cs1) ->
  region_ok SEGS E (mrestrict (w_H W) m') (YP09.mkRegion (Some 18%nat) lo2 hi2 lo2 hi2 cs2) ->
  bv_unsigned (ew E 18) = g + 32 * Z.of_nat i ->
  In (YP09.mkChunk 8 (CVal 4 e8)) cs1 -> In (YP09.mkChunk 12 (CVal 4 e12)) cs1 -> In (YP09.mkChunk 16 (CVal 1 e16)) cs1 ->
  In (YP09.mkChunk 24 (CVal 8 e24)) cs2 ->
  bv_unsigned (sv_denot E e8) mod 2 ^ 32 = v8 -> bv_unsigned (sv_denot E e12) mod 2 ^ 32 = v12 ->
  bv_unsigned (sv_denot E e16) mod 2 ^ 8 = v16 -> bv_unsigned (sv_denot E e24) mod 2 ^ 64 = v24 ->
  CtrlParsed.fld X' (32 * i + 8) 4 = Z_to_le_bytes 4 v8 -> CtrlParsed.fld X' (32 * i + 12) 4 = Z_to_le_bytes 4 v12 ->
  CtrlParsed.fld X' (32 * i + 16) 1 = Z_to_le_bytes 1 v16 -> CtrlParsed.fld X' (32 * i + 24) 8 = Z_to_le_bytes 8 v24 ->
  tTB m' X'.
Proof.
intros E m m' X X' i cs1 cs2 lo1 hi1 lo2 hi2 e8 e12 e16 e24 v8 v12 v16 v24 Hi HT HL HM HX R1 R2 Hb I8 I12 I16 I24 V8 V12 V16 V24 F8 F12 F16 F24.
pose proof (field_of_region_any (segs := SEGS) E _ 18 _ cs1 lo1 hi1 lo1 hi1 8 4 e8 R1 Hb I8 ltac:(cbn; lia)) as W8.
pose proof (field_of_region_any (segs := SEGS) E _ 18 _ cs1 lo1 hi1 lo1 hi1 12 4 e12 R1 Hb I12 ltac:(cbn; lia)) as W12.
pose proof (field_of_region_any (segs := SEGS) E _ 18 _ cs1 lo1 hi1 lo1 hi1 16 1 e16 R1 Hb I16 ltac:(cbn; lia)) as W16.
pose proof (field_of_region_any (segs := SEGS) E _ 18 _ cs2 lo2 hi2 lo2 hi2 24 8 e24 R2 Hb I24 ltac:(cbn; lia)) as W24.
change (8 * Z.of_N 4) with 32 in W8, W12. change (8 * Z.of_N 1) with 8 in W16. change (8 * Z.of_N 8) with 64 in W24.
rewrite V8 in W8. rewrite V12 in W12. rewrite V16 in W16. rewrite V24 in W24.
apply (ent_tb m m' X X' i v8 v12 v16 v24 Hi HT HL HM HX);
  first [ assumption | rewrite <- V8; apply Z.mod_pos_bound; lia | rewrite <- V12; apply Z.mod_pos_bound; lia
        | rewrite <- V16; apply Z.mod_pos_bound; lia | rewrite <- V24; apply Z.mod_pos_bound; lia ].
Qed.
Lemma mod_atom : forall E n v w, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ w -> 0 <= w <= 64 -> bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ w = v.
Proof.
intros E n v w H Hv Hw. rewrite den_atom0, H, unsigned_lit_small.
- apply Z.mod_small. exact Hv.
- split; [lia|]. apply (Z.lt_le_trans _ (2 ^ w)); [lia | apply Z.pow_le_mono_r; lia].
Qed.
Lemma nth_upd_out : forall (X bs : list byte) kk j, (kk + length bs <= length X)%nat -> ~ (kk <= j < kk + length bs)%nat ->
  nth_error (Mem.upd_bytes X kk bs) j = nth_error X j.
Proof.
intros X bs kk j H Hj. rewrite GateModel.nth_error_upd by exact H.
destruct (Nat.leb_spec kk j), (Nat.ltb_spec j (kk + length bs)); cbn [andb]; first [reflexivity | lia].
Qed.
Ltac fregs HS :=
  let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in
  let Q8 := fresh "Q8" in let Q9 := fresh "Q9" in let Q10 := fresh "Q10" in
  let Q18 := fresh "Q18" in let Q19 := fresh "Q19" in let Q20 := fresh "Q20" in let Q21 := fresh "Q21" in
  let Q22 := fresh "Q22" in let Q23 := fresh "Q23" in let Q24 := fresh "Q24" in let Q25 := fresh "Q25" in
  let Q26 := fresh "Q26" in let Q27 := fresh "Q27" in
  preg HS (1%bv : bv 5) Q1; preg HS (2%bv : bv 5) Q2; preg HS (3%bv : bv 5) Q3; preg HS (4%bv : bv 5) Q4;
  preg HS (8%bv : bv 5) Q8; preg HS (9%bv : bv 5) Q9; preg HS (10%bv : bv 5) Q10;
  preg HS (18%bv : bv 5) Q18; preg HS (19%bv : bv 5) Q19; preg HS (20%bv : bv 5) Q20; preg HS (21%bv : bv 5) Q21;
  preg HS (22%bv : bv 5) Q22; preg HS (23%bv : bv 5) Q23; preg HS (24%bv : bv 5) Q24; preg HS (25%bv : bv 5) Q25;
  preg HS (26%bv : bv 5) Q26; preg HS (27%bv : bv 5) Q27;
  rewrite ?den_atom0 in Q1, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.

Lemma fld_upd_same' : forall (BB bs : list byte) p n, length bs = n -> (p + n <= length BB)%nat -> CtrlParsed.fld (Mem.upd_bytes BB p bs) p n = bs.
Proof. intros BB bs p n Hl Hn. subst n. apply GateModel.fld_upd_same. exact Hn. Qed.
Ltac inch := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac fleaf X' rv E2 E3 E4 HJ HKf HPf :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
  fregs HS;
  let mat' := fresh "mat" in
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
  match goal with Q : getr (ms_regs msx) 1 = ew Ex ?n, H : ew Ex ?n = getr regs 1 |- _ => rewrite Q, H end;
  rewrite (Hra : v_jalr (getr regs 1) 0 = getr regs 1);
  apply (fin_post (ms_regs msx) (ms_mem msx) _ X' rv);
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
  | exact HKf | exact HPf | idtac
  | apply apres_of;
    [ match goal with Q : getr (ms_regs msx) 2 = _ |- _ => rewrite Q end;
      rewrite (den_off Ex 2 112 (spZ regs - 112) E2) by lia;
      replace (spZ regs - 112 + 112) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
    | match goal with Q : getr (ms_regs msx) 3 = _ |- _ => rewrite Q end; exact E3
    | match goal with Q : getr (ms_regs msx) 4 = _ |- _ => rewrite Q end; exact E4
    | .. ];
    match goal with |- getr (ms_regs msx) ?r = getr regs ?r =>
      match goal with Q : getr (ms_regs msx) r = ew Ex ?n, H : ew Ex ?n = getr regs r |- _ => rewrite Q, H; reflexivity end end
  | match goal with Q : getr (ms_regs msx) 1 = ew Ex ?n, H : ew Ex ?n = getr regs 1 |- _ => rewrite Q, H; reflexivity end
  | match goal with Q : getr (ms_regs msx) 10 = _ |- _ => rewrite Q end; reflexivity
  | idtac ]
  end.

Lemma fT_ok : fT_stmt.
Proof.
intros i regs' m md Hi Hgf Hed HJ HK HP HT HSV HOW Hsp R3 R4 R9 R16 R18 R21.
pose proof (proj1 (proj2 HGok)) as Hn.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg'.
pose proof Hgside as Hgs'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs', Hlo.
assert (Hi8 : (i < 8)%nat) by lia.
destruct (kst_G 0x4d4c [] regs' m G i NoDup_nil_2 (Forall_nil _) HSV HOW HK HP HT Hi8 Hsp R9 R18 R21) as [HS SHOK].
ekv regs' G i 33%nat EQ33. ekv regs' G i 34%nat EQ34. ekv regs' G i 35%nat EQ35. ekv regs' G i 36%nat EQ36.
ekv regs' G i 37%nat EQ37. ekv regs' G i 38%nat EQ38. ekv regs' G i 39%nat EQ39. ekv regs' G i 40%nat EQ40.
ekv regs' G i 41%nat EQ41. ekv regs' G i 42%nat EQ42. ekv regs' G i 43%nat EQ43. ekv regs' G i 44%nat EQ44.
ekv regs' G i 45%nat EQ45. ekv regs' G i 46%nat EQ46. ekv regs' G i 47%nat EQ47. ekv regs' G i 48%nat EQ48. ekv regs' G i 49%nat EQ49.
assert (E2 : ew (EK regs' G i) 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite (ek_reg regs' G i 2%bv 2 eq_refl), <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew (EK regs' G i) 3 = getr regs 3) by (rewrite (ek_reg regs' G i 3%bv 3 eq_refl); exact R3).
assert (E4 : ew (EK regs' G i) 4 = getr regs 4) by (rewrite (ek_reg regs' G i 4%bv 4 eq_refl); exact R4).
assert (E16 : ew (EK regs' G i) 16 = Z_to_bv 64 now) by (rewrite (ek_reg regs' G i 16%bv 16 eq_refl); exact R16).
assert (E18 : ew (EK regs' G i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i)) by (rewrite (ek_reg regs' G i 18%bv 18 eq_refl); exact R18).
remember (EK regs' G i) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
clear HE.
pose proof (GateModel.fu_rng8 G (32 * i + 24) ltac:(lia)) as R49.
paj_run_tok RUN HS HJ SHOK GBspan; [awrF (g + 32 * Z.of_nat i) E18|].
kwE (g + 32 * Z.of_nat i) E18 HFr K1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms1 end.
destruct (ent_keep m (ms_mem ms1) i Hi8 HK HP K1 HG) as [HK1 HP1].
destruct (ent_sv m (ms_mem ms1) HSV HOW ltac:(intros a Ha Hs; apply K1; lia)) as [HSV1 HOW1].
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (bltu_atoms E 16 49 now _ E16 EQ49) in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK GBspan; [awrF (g + 32 * Z.of_nat i) E18|].
  kwE (g + 32 * Z.of_nat i) E18 HFr K2.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?mc) => rename mc into ms2 end.
  destruct (ent_keep (ms_mem ms1) (ms_mem ms2) i Hi8 HK1 HP1 K2 HG) as [HK2 HP2].
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ss) rK_stk) in
    let r2 := eval vm_compute in (nth 2 (ss_mem ss) rK_stk) in
    pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RA;
    pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as RB end.
  cbn [ms_mem restrict] in RA, RB.
  fleaf (Mem.upd_bytes G (32 * i + 24) (Mem.le8 (Z_to_bv 64 now))) 1 E2 E3 E4 HJ HK2 HP2.
  + eapply (ent_leaf E m (ms_mem ms2) G _ i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 48 0) (SOff 16 0)
            (CtrlParsed.fu G (32 * i + 8) 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16)) now Hi8 HT).
    * rewrite GateModel.length_upd by (rewrite Mem.length_le8, HGl; lia). exact HGl.
    * intros a Ha H1 H2. rewrite K2 by lia. apply K1; lia.
    * intros j Hj H1 H2. apply nth_upd_out; rewrite ?Mem.length_le8, ?HGl; lia.
    * exact RA.
    * exact RB.
    * rewrite E18. apply unsigned_lit_small. lia.
    * inch. * inch. * inch. * inch.
    * apply (mod_atom E 46 _ 32 EQ46); [apply GateModel.fu_rng4; lia | lia].
    * apply (mod_atom E 47 _ 32 EQ47); [apply GateModel.fu_rng4; lia | lia].
    * apply (mod_atom E 48 _ 8 EQ48); [apply GateModel.fb_rng | lia].
    * apply (mod_atom E 16 _ 64 E16); [exact Rnow | lia].
    * rewrite GateModel.fld_upd_other by (rewrite ?Mem.length_le8, ?HGl; lia). apply fld_le; lia.
    * rewrite GateModel.fld_upd_other by (rewrite ?Mem.length_le8, ?HGl; lia). apply fld_le; lia.
    * rewrite GateModel.fld_upd_other by (rewrite ?Mem.length_le8, ?HGl; lia). rewrite GateModel.fld1 by lia. apply le1_fb.
    * rewrite fld_upd_same' by (rewrite ?Mem.length_le8, ?HGl; lia). apply le8_Z. exact Rnow.
  + apply (GateModel.gm_refresh G Sg now i); [exact Hgf | exact Hed | apply orb_true_iff; left; apply Z.ltb_lt; exact Hc].
- rewrite (bltu_atoms E 16 49 now _ E16 EQ49) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hge.
  paj_run_tok RUN HS HJ SHOK GBspan; [awrF (g + 32 * Z.of_nat i) E18|].
  kwE (g + 32 * Z.of_nat i) E18 HFr K2.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?mc) => rename mc into ms2 end.
  destruct (ent_keep (ms_mem ms1) (ms_mem ms2) i Hi8 HK1 HP1 K2 HG) as [HK2 HP2].
  destruct (ent_sv (ms_mem ms1) (ms_mem ms2) HSV1 HOW1 ltac:(intros a Ha Hs; apply K2; lia)) as [HSV2 HOW2].
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (bltu_diff_rf E 16 49 now _ E16 EQ49) in Hc by lia. apply Z.ltb_lt in Hc.
    paj_run_tok RUN HS HJ SHOK GBspan; [awrF (g + 32 * Z.of_nat i) E18|].
    kwE (g + 32 * Z.of_nat i) E18 HFr K3.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?mc) => rename mc into ms3 end.
    destruct (ent_keep (ms_mem ms2) (ms_mem ms3) i Hi8 HK2 HP2 K3 HG) as [HK3 HP3].
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msx) =>
      let r1 := eval vm_compute in (nth 1 (ss_mem ss) rK_stk) in
      let r2 := eval vm_compute in (nth 2 (ss_mem ss) rK_stk) in
      pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RA;
      pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as RB end.
    cbn [ms_mem restrict] in RA, RB.
    fleaf G 0 E2 E3 E4 HJ HK3 HP3.
    * eapply (ent_leaf E m (ms_mem ms3) G _ i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 48 0) (SOff 49 0)
              (CtrlParsed.fu G (32 * i + 8) 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16))
              (CtrlParsed.fu G (32 * i + 24) 8) Hi8 HT).
      -- exact HGl.
      -- intros a Ha H1 H2. rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
      -- intros j Hj H1 H2. reflexivity.
      -- exact RA.
      -- exact RB.
      -- rewrite E18. apply unsigned_lit_small. lia.
      -- inch. -- inch. -- inch. -- inch.
      -- apply (mod_atom E 46 _ 32 EQ46); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom E 47 _ 32 EQ47); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom E 48 _ 8 EQ48); [apply GateModel.fb_rng | lia].
      -- apply (mod_atom E 49 _ 64 EQ49); [apply GateModel.fu_rng8; lia | lia].
      -- apply fld_le; lia.
      -- apply fld_le; lia.
      -- rewrite GateModel.fld1 by lia. apply le1_fb.
      -- apply fld_le; lia.
    * apply (GateModel.gm_keep G Sg now i); [exact Hgf | exact Hed |].
      apply orb_false_iff. split; [apply Z.ltb_ge; lia | apply Z.leb_gt; unfold GateModel.RF in Hc |- *; lia].
  + rewrite (bltu_diff_rf E 16 49 now _ E16 EQ49) in Hc by lia. apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK GBspan; [awrF (g + 32 * Z.of_nat i) E18|].
    kwE (g + 32 * Z.of_nat i) E18 HFr K3.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?mc) => rename mc into ms3 end.
    destruct (ent_keep (ms_mem ms2) (ms_mem ms3) i Hi8 HK2 HP2 K3 HG) as [HK3 HP3].
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msx) =>
      let r1 := eval vm_compute in (nth 1 (ss_mem ss) rK_stk) in
      let r2 := eval vm_compute in (nth 2 (ss_mem ss) rK_stk) in
      pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RA;
      pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as RB end.
    cbn [ms_mem restrict] in RA, RB.
    fleaf (Mem.upd_bytes G (32 * i + 24) (Mem.le8 (Z_to_bv 64 now))) 1 E2 E3 E4 HJ HK3 HP3.
    * eapply (ent_leaf E m (ms_mem ms3) G _ i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 48 0) (SOff 16 0)
              (CtrlParsed.fu G (32 * i + 8) 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16)) now Hi8 HT).
      -- rewrite GateModel.length_upd by (rewrite Mem.length_le8, HGl; lia). exact HGl.
      -- intros a Ha H1 H2. rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
      -- intros j Hj H1 H2. apply nth_upd_out; rewrite ?Mem.length_le8, ?HGl; lia.
      -- exact RA.
      -- exact RB.
      -- rewrite E18. apply unsigned_lit_small. lia.
      -- inch. -- inch. -- inch. -- inch.
      -- apply (mod_atom E 46 _ 32 EQ46); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom E 47 _ 32 EQ47); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom E 48 _ 8 EQ48); [apply GateModel.fb_rng | lia].
      -- apply (mod_atom E 16 _ 64 E16); [exact Rnow | lia].
      -- rewrite GateModel.fld_upd_other by (rewrite ?Mem.length_le8, ?HGl; lia). apply fld_le; lia.
      -- rewrite GateModel.fld_upd_other by (rewrite ?Mem.length_le8, ?HGl; lia). apply fld_le; lia.
      -- rewrite GateModel.fld_upd_other by (rewrite ?Mem.length_le8, ?HGl; lia). rewrite GateModel.fld1 by lia. apply le1_fb.
      -- rewrite fld_upd_same' by (rewrite ?Mem.length_le8, ?HGl; lia). apply le8_Z. exact Rnow.
    * apply (GateModel.gm_refresh G Sg now i); [exact Hgf | exact Hed |].
      apply orb_true_iff. right. apply Z.leb_le. unfold GateModel.RF in Hc |- *. lia.
Qed.
Definition rC_cnt : YP09.region := YP09.mkRegion (Some 19%nat) 256 260 256 260 [].
Definition shx_c : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 256) (SLit 3)) (SOff 21 0).
Definition fa_X : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4 (2 ^ 47 - 25) 2); (19%nat, mkAF 8 (2 ^ 47 - 265) 3);
   (21%nat, mkAF GSB GSB 0); (23%nat, AFNOTG); (24%nat, mkAF 0 8 0)] [] [].
Definition ss_X (pc : Z) : sstate := mkSS pc (sr_sets sr_atoms [(20%bv, SOff 19 256); (25%bv, shx_c)]) [rK_stk] None fa_X.
Definition SH_X : list shent := [mkSHE 19 0 264].
Lemma kst_X : forall pc regs' m X i n,
  tSV m -> tOW m -> tKP m -> spZ regs' = spZ regs - 112 ->
  getr regs' 9 = w64 s -> getr regs' 19 = w64 g -> getr regs' 20 = w64 (g + 256) -> getr regs' 21 = w64 GSB ->
  getr regs' 23 = w64 (2 ^ 64 - 1 - g) -> getr regs' 24 = w64 n -> 0 <= n <= 8 -> getr regs' 25 = w64 (GSB + (g + 256) / 8) ->
  st_ok_pi SEGS VAL (EK regs' X i) (ss_X pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 21 0) SH_X (EK regs' X i) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X i n HSV HOW HK Hsp R9 R19 R20 R21 R23 R24 Hn R25.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
assert (Hg8b : 8 <= g) by (pose proof (Z.div_mod g 8 ltac:(lia)) as Dg; rewrite Hg8 in Dg; lia).
assert (Hs4b : 4 <= s) by (pose proof (Z.div_mod s 4 ltac:(lia)) as Ds; rewrite Hs4 in Ds; lia).
assert (E19 : ew (EK regs' X i) 19 = Z_to_bv 64 g) by (rewrite (ek_reg regs' X i 19%bv 19 eq_refl); exact R19).
assert (E21 : ew (EK regs' X i) 21 = Z_to_bv 64 GSB) by (rewrite (ek_reg regs' X i 21%bv 21 eq_refl); exact R21).
rewrite restrict_mkst_fx. split.
- unfold ss_X. apply pa_entry_st_ok_full.
  + apply (regs_ok_sets _ sr_atoms regs' regs' [(20%bv, SOff 19 256); (25%bv, shx_c)]).
    * unfold EK. apply regs_ok_Eimg_Ereg.
    * cbn [map fst]. apply NoDup_ListNoDup. apply List.NoDup_cons; [|apply List.NoDup_cons; [intros [] | apply List.NoDup_nil]].
      intros [Hq|[]]. apply (f_equal bv_unsigned) in Hq. vm_compute in Hq. discriminate Hq.
    * intros r _. reflexivity.
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; (split; [reflexivity|]).
      -- rewrite R20. rewrite (den_off (EK regs' X i) 19 256 g E19) by lia. reflexivity.
      -- rewrite R25. unfold shx_c. rewrite (denot_shx (EK regs' X i) 19 21 256 g GSB E19 E21) by (unfold GSB; lia). reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. exact (stk_region_ok regs' m X i HSV HOW Hsp).
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  + split; [|split; [exact I | exact I]].
    unfold fa_X, AFNOTG. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    ekreg 2%nat (2%bv : bv 5). ekreg 9%nat (9%bv : bv 5). ekreg 19%nat (19%bv : bv 5). ekreg 21%nat (21%bv : bv 5).
    ekreg 23%nat (23%bv : bv 5). ekreg 24%nat (24%bv : bv 5).
    change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite R9, R19, R21, R23, R24.
    unfold w64. rewrite !unsigned_lit_small by (unfold GSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo.
    unfold GSB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, SH_X. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) m (EK regs' X i) (SOff 21 0) 19 g 264 g 0 264).
  + exact (kp_ra m g 264 HK ltac:(lia) Hgam ltac:(lia) Hgra).
  + apply (U_atom (EK regs' X i) 21 GSB E21). unfold GSB; lia.
  + apply (U_atom (EK regs' X i) 19 g E19). lia.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. cbn [Z.min Z.max] in Hx. lia.
Qed.
Lemma br_ge7 : forall E kk nn, ew E kk = Z_to_bv 64 nn -> 0 <= nn <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 7)) (sv_denot E (SOff kk 0)) = negb (7 <? nn).
Proof.
intros E kk nn H Hn. cbn [branch_taken]. rewrite den_atom0, H. cbn [sv_denot].
rewrite bv_lts_small by lia. reflexivity.
Qed.
Definition rA_a : YP09.region := YP09.mkRegion (Some 19%nat) 8 17 8 17 [ckv 8 4 46; ckv 12 4 47; ckv 16 1 48].
Definition rA_b : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 24 32 [ckv 24 8 49].
Definition fa_A : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4 (2 ^ 47 - 25) 2); (19%nat, mkAF 8 (2 ^ 47 - 41) 3);
   (21%nat, mkAF GSB GSB 0); (46%nat, AF32); (47%nat, AF32); (48%nat, AF8); (50%nat, AF32); (51%nat, AF8)] [] [].
Definition ss_A (pc : Z) : sstate := mkSS pc sr_atoms [rK_stk; rA_a; rA_b; rF_sig] None fa_A.
Definition SH_A : list shent := [mkSHE 19 8 32; mkSHE 9 8 24].
Lemma kst_A : forall pc regs' m X i,
  tSV m -> tOW m -> tKP m -> tPR m -> tTB m X -> (i < 8)%nat -> spZ regs' = spZ regs - 112 ->
  getr regs' 9 = w64 s -> getr regs' 19 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB ->
  st_ok_pi SEGS VAL (EK regs' X i) (ss_A pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 21 0) SH_A (EK regs' X i) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X i HSV HOW HK HP [HX HXl] Hi Hsp R9 R19 R21.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
assert (Hg8b : 8 <= g) by (pose proof (Z.div_mod g 8 ltac:(lia)) as Dg; rewrite Hg8 in Dg; lia).
assert (Hs4b : 4 <= s) by (pose proof (Z.div_mod s 4 ltac:(lia)) as Ds; rewrite Hs4 in Ds; lia).
pose proof (kp_garr8_S m HK) as HSm.
ekv regs' X i 46%nat E46. ekv regs' X i 47%nat E47. ekv regs' X i 48%nat E48. ekv regs' X i 49%nat E49.
ekv regs' X i 50%nat E50. ekv regs' X i 51%nat E51.
assert (E2 : ew (EK regs' X i) 2 = getr regs' 2) by (apply ek_reg; reflexivity).
assert (E9 : ew (EK regs' X i) 9 = Z_to_bv 64 s) by (rewrite (ek_reg regs' X i 9%bv 9 eq_refl); exact R9).
assert (E19 : ew (EK regs' X i) 19 = Z_to_bv 64 (g + 32 * Z.of_nat i)) by (rewrite (ek_reg regs' X i 19%bv 19 eq_refl); exact R19).
assert (E21 : ew (EK regs' X i) 21 = Z_to_bv 64 GSB) by (rewrite (ek_reg regs' X i 21%bv 21 eq_refl); exact R21).
set (E := EK regs' X i) in *.
pose proof (GateModel.fu_rng4 X (32 * i + 8) ltac:(lia)) as R46. pose proof (GateModel.fu_rng4 X (32 * i + 12) ltac:(lia)) as R47.
pose proof (GateModel.fb_rng X (32 * i + 16)) as R48. pose proof (GateModel.fu_rng8 X (32 * i + 24) ltac:(lia)) as R49.
pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R50. pose proof (GateModel.fb_rng Sg 16) as R51.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
assert (Hwr : forall a, g <= a < g + 264 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Hgw a Ha)). }
assert (VG : forall (k n : nat), (k + n <= 264)%nat -> val_mem SEGS (mrestrict (w_H W) m) (g + Z.of_nat k) n (CtrlParsed.fu X k n))
  by (intros k0 n0 Hk; apply gsp_val_mem; [exact HX | lia]).
assert (VS : forall (k n : nat), (k + n <= 24)%nat -> val_mem SEGS (mrestrict (w_H W) m) (s + Z.of_nat k) n (CtrlParsed.fu Sg k n))
  by (intros k0 n0 Hk; apply gsp_val_mem; [exact HSm | lia]).
rewrite restrict_mkst_fx. split.
- unfold ss_A. apply pa_entry_st_ok_full.
  + unfold E, EK. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [exact (stk_region_ok regs' m X i HSV HOW Hsp)|].
    unfold rA_a, rA_b, rF_sig, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 19%nat _ E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ _ 8 4 (SOff 46 0) (CtrlParsed.fu X (32 * i + 8) 4)); [rewrite den_atom0; exact E46 | zrng | cbn; lia |].
         replace (g + 32 * Z.of_nat i + 8) with (g + Z.of_nat (32 * i + 8)) by lia. apply VG. lia.
      -- apply (chunk_ok_val SEGS E _ _ 12 4 (SOff 47 0) (CtrlParsed.fu X (32 * i + 12) 4)); [rewrite den_atom0; exact E47 | zrng | cbn; lia |].
         replace (g + 32 * Z.of_nat i + 12) with (g + Z.of_nat (32 * i + 12)) by lia. apply VG. lia.
      -- apply (chunk_ok_val SEGS E _ _ 16 1 (SOff 48 0) (CtrlParsed.fb X (32 * i + 16))); [rewrite den_atom0; exact E48 | zrng | cbn; lia |].
         replace (g + 32 * Z.of_nat i + 16) with (g + Z.of_nat (32 * i + 16)) by lia. rewrite <- gsp_fu1 by lia. apply VG. lia.
    * rewrite (VB 19%nat _ E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 49 0) (CtrlParsed.fu X (32 * i + 24) 8)); [rewrite den_atom0; exact E49 | zrng | cbn; lia |].
      replace (g + 32 * Z.of_nat i + 24) with (g + Z.of_nat (32 * i + 24)) by lia. apply VG. lia.
    * rewrite (VB 9%nat _ E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ _ 8 4 (SOff 50 0) (CtrlParsed.fu Sg 8 4)); [rewrite den_atom0; exact E50 | zrng | cbn; lia |].
         apply (VS 8%nat 4%nat). lia.
      -- apply (chunk_ok_val SEGS E _ _ 16 1 (SOff 51 0) (CtrlParsed.fb Sg 16)); [rewrite den_atom0; exact E51 | zrng | cbn; lia |].
         rewrite <- gsp_fu1 by lia. apply (VS 16%nat 1%nat). lia.
  + apply pairwise_disjoint_of_extents. unfold rK_stk, rA_a, rA_b, rF_sig, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 19%nat _ E19), (VB 9%nat _ E9) by lia.
    cbn [base_val]. rewrite E2. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold fa_A, AF32, AF8. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E19, E21, E46, E47, E48, E50, E51. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold GSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    assert (Hm2 : (g + 32 * Z.of_nat i) mod 8 = 0) by (rewrite Zplus_mod, Hg8, Zmult_mod; reflexivity).
    unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo.
    unfold GSB. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, SH_A. repeat apply Forall_cons; try apply Forall_nil.
  + apply (shent_ok_of_range SEGS (w_H W) m E (SOff 21 0) 19 g 264 (g + 32 * Z.of_nat i) 8 32).
    * exact (kp_ra m g 264 HK ltac:(lia) Hgam ltac:(lia) Hgra).
    * apply (U_atom E 21 GSB E21). unfold GSB; lia.
    * apply (U_atom E 19 _ E19). lia.
    * lia. * lia.
    * intros x Hx. unfold SHADOW_OFF. cbn [Z.min Z.max] in Hx. lia.
  + apply (shent_ok_of_range SEGS (w_H W) m E (SOff 21 0) 9 s 24 s 8 24).
    * exact (kp_ra m s 24 HK ltac:(lia) Hsam ltac:(lia) Hsra).
    * apply (U_atom E 21 GSB E21). unfold GSB; lia.
    * apply (U_atom E 9 _ E9). lia.
    * lia. * lia.
    * intros x Hx. unfold SHADOW_OFF. cbn [Z.min Z.max] in Hx. lia.
Qed.
Lemma ent_leafB : forall (bn : nat) E m m' X X' (i : nat) cs1 cs2 lo1 hi1 lo2 hi2 e8 e12 e16 e24 v8 v12 v16 v24,
  (i < 8)%nat -> tTB m X -> length X' = 264%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 17) ->
     ~ (g + 32 * Z.of_nat i + 24 <= a < g + 32 * Z.of_nat i + 32) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall j, (j < 264)%nat -> ~ (32 * i + 8 <= j < 32 * i + 17)%nat -> ~ (32 * i + 24 <= j < 32 * i + 32)%nat ->
     nth_error X' j = nth_error X j) ->
  region_ok SEGS E (mrestrict (w_H W) m') (YP09.mkRegion (Some bn) lo1 hi1 lo1 hi1 cs1) ->
  region_ok SEGS E (mrestrict (w_H W) m') (YP09.mkRegion (Some bn) lo2 hi2 lo2 hi2 cs2) ->
  bv_unsigned (ew E bn) = g + 32 * Z.of_nat i ->
  In (YP09.mkChunk 8 (CVal 4 e8)) cs1 -> In (YP09.mkChunk 12 (CVal 4 e12)) cs1 -> In (YP09.mkChunk 16 (CVal 1 e16)) cs1 ->
  In (YP09.mkChunk 24 (CVal 8 e24)) cs2 ->
  bv_unsigned (sv_denot E e8) mod 2 ^ 32 = v8 -> bv_unsigned (sv_denot E e12) mod 2 ^ 32 = v12 ->
  bv_unsigned (sv_denot E e16) mod 2 ^ 8 = v16 -> bv_unsigned (sv_denot E e24) mod 2 ^ 64 = v24 ->
  CtrlParsed.fld X' (32 * i + 8) 4 = Z_to_le_bytes 4 v8 -> CtrlParsed.fld X' (32 * i + 12) 4 = Z_to_le_bytes 4 v12 ->
  CtrlParsed.fld X' (32 * i + 16) 1 = Z_to_le_bytes 1 v16 -> CtrlParsed.fld X' (32 * i + 24) 8 = Z_to_le_bytes 8 v24 ->
  tTB m' X'.
Proof.
intros bn E m m' X X' i cs1 cs2 lo1 hi1 lo2 hi2 e8 e12 e16 e24 v8 v12 v16 v24 Hi HT HL HM HX R1 R2 Hb I8 I12 I16 I24 V8 V12 V16 V24 F8 F12 F16 F24.
pose proof (field_of_region_any (segs := SEGS) E _ bn _ cs1 lo1 hi1 lo1 hi1 8 4 e8 R1 Hb I8 ltac:(cbn; lia)) as W8.
pose proof (field_of_region_any (segs := SEGS) E _ bn _ cs1 lo1 hi1 lo1 hi1 12 4 e12 R1 Hb I12 ltac:(cbn; lia)) as W12.
pose proof (field_of_region_any (segs := SEGS) E _ bn _ cs1 lo1 hi1 lo1 hi1 16 1 e16 R1 Hb I16 ltac:(cbn; lia)) as W16.
pose proof (field_of_region_any (segs := SEGS) E _ bn _ cs2 lo2 hi2 lo2 hi2 24 8 e24 R2 Hb I24 ltac:(cbn; lia)) as W24.
change (8 * Z.of_N 4) with 32 in W8, W12. change (8 * Z.of_N 1) with 8 in W16. change (8 * Z.of_N 8) with 64 in W24.
rewrite V8 in W8. rewrite V12 in W12. rewrite V16 in W16. rewrite V24 in W24.
apply (ent_tb m m' X X' i v8 v12 v16 v24 Hi HT HL HM HX);
  first [ assumption | rewrite <- V8; apply Z.mod_pos_bound; lia | rewrite <- V12; apply Z.mod_pos_bound; lia
        | rewrite <- V16; apply Z.mod_pos_bound; lia | rewrite <- V24; apply Z.mod_pos_bound; lia ].
Qed.
Lemma mod_sx32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ 32 = v.
Proof.
intros E n v H Hv.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt, (U_atom E n v H) by lia. change (Z.of_N 32) with 32. rewrite (Z.mod_small v) by lia.
rewrite GateModel.s32_swrap by lia. unfold CtrlParsed.s32, zcanon, M64.
destruct (Z.ltb_spec v (2 ^ 31)); lia.
Qed.

Lemma mod_w32 : forall E n z, ew E n = Z_to_bv 64 z ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros E n z H. rewrite den_atom0, H, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296. lia.
Qed.
Lemma den_addsll : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y <= 8 -> x + 32 * y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SAlu ALU_SLL (SOff b 0) (SLit 5))) = Z_to_bv 64 (x + 32 * y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff a 0) (SAlu ALU_SLL (SOff b 0) (SLit 5))))). f_equal.
change (U E (SAlu ALU_ADD (SOff a 0) (SAlu ALU_SLL (SOff b 0) (SLit 5))) = x + 32 * y).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (U_atom E a x Ha), (U_atom E b y Hb) by lia.
change (Z.land (zcanon 5) 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
rewrite (zcanon_id (y * 32)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma vm_move : forall (m m' : word -> option byte) a a' n v,
  (forall j, (j < n)%nat -> aview SEGS (w_H W) m' (a' + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a' n v.
Proof.
intros m m' a a' n v He Hv j Hj. pose proof (He j Hj) as Ea. unfold aview in Ea. rewrite (Hv j Hj) in Ea. cbn [option_map] in Ea.
destruct (mbyte SEGS (mrestrict (w_H W) m') (a' + Z.of_nat j)) as [b|] eqn:Hb; cbn [option_map] in Ea; [|discriminate Ea].
injection Ea as Ea. f_equal. apply bv_eq. exact Ea.
Qed.
Definition xA (N : nat) : list byte :=
  Mem.upd_bytes (Mem.upd_bytes G 256 (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1)))) (32 * N) (CtrlParsed.fld Sg 0 6).
Lemma xA_len : forall N, (N < 8)%nat -> length (xA N) = 264%nat.
Proof.
intros N HN.
assert (L1 : length (Mem.upd_bytes G 256 (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1)))) = 264%nat)
  by (rewrite GateModel.length_upd; [exact HGl | rewrite Mem.length_le4, HGl; lia]).
unfold xA. rewrite GateModel.length_upd; [exact L1 | rewrite (GateModel.length_fld Sg 0 6) by lia; lia].
Qed.
Lemma app_mem : forall m m1 m2 (N : nat),
  (N < 8)%nat -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 256 <= a < g + 260) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
  val_mem SEGS (mrestrict (w_H W) m1) (g + 256) 4 (Z.of_nat N + 1) ->
  (forall i, 0 <= i < 6 -> aview SEGS (w_H W) m2 (g + 32 * Z.of_nat N + i) = aview SEGS (w_H W) m1 (s + i)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat N <= a < g + 32 * Z.of_nat N + 6) ->
     ~ (spZ regs - 112 - ESTACK <= a < spZ regs - 112) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
  tKP m2 /\ tPR m2 /\ tTB m2 (xA N) /\ tSV m2 /\ tOW m2.
Proof.
intros m m1 m2 N HN HK HP HT HSV HOW K1 P1 VC Hcpy K2 P2.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof Hgside as Hgs'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs', Hlo.
assert (L4 : length (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1))) = 4%nat) by apply Mem.length_le4.
assert (L6 : length (CtrlParsed.fld Sg 0 6) = 6%nat) by (apply GateModel.length_fld; lia).
assert (L1 : length (Mem.upd_bytes G 256 (Mem.le4 (Z_to_bv 64 (Z.of_nat N + 1)))) = 264%nat)
  by (rewrite GateModel.length_upd; [exact HGl | rewrite L4, HGl; lia]).
assert (HL : length (xA N) = 264%nat) by (apply xA_len; exact HN).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 256 <= a < g + 260) -> ~ (g + 32 * Z.of_nat N <= a < g + 32 * Z.of_nat N + 6) ->
   ~ (spZ regs - 112 - ESTACK <= a < spZ regs - 112) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a)
  by (intros a Ha H1 H2 H3; rewrite K2 by assumption; apply K1; assumption).
split; [|split; [|split]].
- intros a Ha Hs Hg. assert (Hs2 := Hs). unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hs2.
  rewrite K by (unfold ESTACK; lia). apply HK; assumption.
- intros a Ha. apply P2, P1, HP. exact Ha.
- assert (HSm1 : garr8 SEGS (mrestrict (w_H W) m1) s (map (fun b : byte => bv_unsigned b) Sg)).
  { apply (ga_kept m m1 s); [|exact (kp_garr8_S m HK)]. intros a Ha. rewrite length_map, HSl in Ha. apply K1; lia. }
  assert (V6 : val_mem SEGS (mrestrict (w_H W) m2) (g + Z.of_nat (32 * N)) 6 (CtrlParsed.fu Sg 0 6)).
  { apply (vm_move m1 m2 s).
    - intros j Hj. replace (g + Z.of_nat (32 * N) + Z.of_nat j) with (g + 32 * Z.of_nat N + Z.of_nat j) by lia. apply Hcpy. lia.
    - pose proof (gsp_val_mem _ s Sg 0 6 HSm1 ltac:(lia)) as V. replace (s + Z.of_nat 0) with s in V by lia. exact V. }
  assert (V4 : val_mem SEGS (mrestrict (w_H W) m2) (g + Z.of_nat 256) 4 (Z.of_nat N + 1)).
  { change (Z.of_nat 256) with 256. apply (vm_kept m1 m2); [|exact VC]. intros x Hx. apply K2; unfold ESTACK; lia. }
  apply gbn_tTB. apply (gbn_cover [(256%nat, 4%nat, Z.of_nat N + 1); ((32 * N)%nat, 6%nat, CtrlParsed.fu Sg 0 6)]
    (mrestrict (w_H W) m) _ G (xA N) (tTB_gbn m G HT) HL).
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbv beta iota.
    * split; [lia|]. split; [exact V4|]. split; [|lia].
      unfold xA. rewrite GateModel.fld_upd_other by (rewrite ?L6, ?L1; lia).
      rewrite fld_upd_same' by (rewrite ?L4, ?HGl; lia). rewrite le4_Z, Z.mod_small by lia. reflexivity.
    * split; [pose proof (GateModel.ble_range (CtrlParsed.fld Sg 0 6)) as Rb; unfold CtrlParsed.fu; lia|].
      split; [exact V6|]. split; [|lia].
      unfold xA. rewrite fld_upd_same' by (rewrite ?L6, ?L1; lia). apply fld_le. lia.
  + intros j Hj Hc. split.
    * apply (mbyte_of_aview SEGS). apply K; [lia | | | unfold ESTACK; lia].
      -- intros Hr. apply Hc. unfold wcov. apply Exists_cons_hd. lia.
      -- intros Hr. apply Hc. unfold wcov. apply Exists_cons_tl. apply Exists_cons_hd. lia.
    * unfold xA. rewrite nth_upd_out.
      -- rewrite nth_upd_out; [reflexivity | rewrite L4, HGl; lia |].
         intros Hr. apply Hc. unfold wcov. apply Exists_cons_hd. rewrite L4 in Hr. lia.
      -- rewrite L6, L1. lia.
      -- intros Hr. apply Hc. unfold wcov. apply Exists_cons_tl. apply Exists_cons_hd. rewrite L6 in Hr. lia.
- apply (ent_sv m m2 HSV HOW). intros a Ha Hs. apply K; unfold ESTACK; lia.
Qed.
Ltac awrN nb e Eb :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nb e);
      [reflexivity | rewrite Eb; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; let a_ := fresh "a" in let Ha_ := fresh "Ha" in intros a_ Ha_; apply (proj1 (Hgw a_ ltac:(lia))) | ] ].
Lemma after_ok : after_stmt.
Proof.
intros regs' m md Hnone HJ HK HP HT HSV HOW Hsp R3 R4 R9 R19 R20 R21 R22 R23 R24 R25.
pose proof (proj1 (proj2 HGok)) as Hn.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hlo.
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof Hgside as Hgs'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs'.
pose proof Hwin as Hwin'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hwin'.
pose proof Hsside as Hss'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hss'.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & _).
assert (Hg8b : 8 <= g) by (pose proof (Z.div_mod g 8 ltac:(lia)) as Dg; rewrite Hg8 in Dg; lia).
assert (Hs4b : 4 <= s) by (pose proof (Z.div_mod s 4 ltac:(lia)) as Ds; rewrite Hs4 in Ds; lia).
destruct (kst_X 0x4bd8 regs' m G 0%nat (disco_classify_c.gn G) HSV HOW HK Hsp R9 R19 R20 R21 R23 R24 ltac:(lia) R25) as [HS SHOK].
ekv regs' G 0%nat 33%nat EQ33. ekv regs' G 0%nat 34%nat EQ34. ekv regs' G 0%nat 35%nat EQ35. ekv regs' G 0%nat 36%nat EQ36.
ekv regs' G 0%nat 37%nat EQ37. ekv regs' G 0%nat 38%nat EQ38. ekv regs' G 0%nat 39%nat EQ39. ekv regs' G 0%nat 40%nat EQ40.
ekv regs' G 0%nat 41%nat EQ41. ekv regs' G 0%nat 42%nat EQ42. ekv regs' G 0%nat 43%nat EQ43. ekv regs' G 0%nat 44%nat EQ44.
ekv regs' G 0%nat 45%nat EQ45.
assert (E2 : ew (EK regs' G 0%nat) 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite (ek_reg regs' G 0%nat 2%bv 2 eq_refl), <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew (EK regs' G 0%nat) 3 = getr regs 3) by (rewrite (ek_reg regs' G 0%nat 3%bv 3 eq_refl); exact R3).
assert (E4 : ew (EK regs' G 0%nat) 4 = getr regs 4) by (rewrite (ek_reg regs' G 0%nat 4%bv 4 eq_refl); exact R4).
assert (E9 : ew (EK regs' G 0%nat) 9 = Z_to_bv 64 s) by (rewrite (ek_reg regs' G 0%nat 9%bv 9 eq_refl); exact R9).
assert (E19 : ew (EK regs' G 0%nat) 19 = Z_to_bv 64 g) by (rewrite (ek_reg regs' G 0%nat 19%bv 19 eq_refl); exact R19).
assert (E21 : ew (EK regs' G 0%nat) 21 = Z_to_bv 64 GSB) by (rewrite (ek_reg regs' G 0%nat 21%bv 21 eq_refl); exact R21).
assert (E22 : ew (EK regs' G 0%nat) 22 = Z_to_bv 64 (gdk Sg)) by (rewrite (ek_reg regs' G 0%nat 22%bv 22 eq_refl); exact R22).
assert (E24 : ew (EK regs' G 0%nat) 24 = Z_to_bv 64 (disco_classify_c.gn G)) by (rewrite (ek_reg regs' G 0%nat 24%bv 24 eq_refl); exact R24).
remember (EK regs' G 0%nat) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
clear HE.
paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
kw0 HFr KM0.
destruct (call_keep m _ G HK HP HT HSV HOW (fun a Ha _ => KM0 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
  as (HK0 & HP0 & HT0 & HSV0 & HOW0).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (br_ge7 E 24 _ E24) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
  set (N := Z.to_nat (disco_classify_c.gn G)) in *.
  assert (HgN : disco_classify_c.gn G = Z.of_nat N) by (unfold N; lia).
  assert (HN8 : (N < 8)%nat) by lia.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss1 ?ms1 =>
    pose proof (st_ok_pi_add_region E ss1 ms1 rC_cnt HS eq_refl) as HS2 end.
  match type of HS2 with ?A1 -> _ => assert (HRO : A1); [|specialize (HS2 HRO); clear HRO] end.
  { unfold rC_cnt, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HP0. exact (proj2 (Hgw (g + o) ltac:(lia))). }
  match type of HS2 with ?A1 -> _ => assert (HRD : A1); [|specialize (HS2 HRD); clear HRD] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    unfold rC_cnt. cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E19, E2, !unsigned_lit_small by lia.
    repeat split; lia. }
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS2. clear HS. rename HS2 into HS.
  paj_run_tok RUN HS HJ SHOK GBspan; [awrN 19%nat g E19|].
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?mA) (mrestrict _ ?mB) |- _ =>
    assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 256 <= a < g + 260) -> aview SEGS (w_H W) mB a = aview SEGS (w_H W) mA a);
    [ intros a0 Ha0 Hn0; apply (kept_of_frame (segs := SEGS) Ex rs (w_H W) mA mB (fun a => g + 256 <= a < g + 260) HFr); [ | exact Ha0 | exact Hn0];
      let w := eval vm_compute in (windows rs) in change (windows rs) with w;
      intros b0 wlo0 whi0 x0 Hin0 Hx0; cbn [In] in Hin0;
      repeat (destruct Hin0 as [Hin0|Hin0]; [injection Hin0 as <- <- <-; cbn [base_val] in Hx0; first [lia | rewrite E19, unsigned_lit_small in Hx0 by lia; lia] |]);
      try destruct Hin0
    | ] end.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mc) => rename mc into ms1 end.
  assert (HK1 : tKP (ms_mem ms1)) by (intros a Ha H1 H2; rewrite KC by lia; apply HK0; assumption).
  lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ss) rK_stk) in
    pose proof (st_ok_region_nth (segs := SEGS) E ss (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as RC end.
  cbn [ms_mem restrict] in RC.
  pose proof (field_of_region_any (segs := SEGS) E _ 19 g _ 256 260 256 260 256 4 (SOff 24 1) RC
    ltac:(rewrite E19; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(cbn; lia)) as VC.
  rewrite (den_off E 24 1 _ E24), unsigned_lit_small in VC by lia.
  change (N.to_nat 4) with 4%nat in VC. change (8 * Z.of_N 4) with 32 in VC.
  rewrite Z.mod_small, HgN in VC by lia.
  preg HS (10%bv : bv 5) Ra0. preg HS (11%bv : bv 5) Ra1. preg HS (12%bv : bv 5) Ra2. preg HS (1%bv : bv 5) Rra.
  preg HS (2%bv : bv 5) Qsp. preg HS (3%bv : bv 5) Qgp. preg HS (4%bv : bv 5) Qtp.
  preg HS (9%bv : bv 5) Q9. preg HS (19%bv : bv 5) Q19. preg HS (21%bv : bv 5) Q21. preg HS (22%bv : bv 5) Q22.
  rewrite (den_addsll E 19 24 g (disco_classify_c.gn G) E19 E24), HgN in Ra0, Q19 by lia.
  rewrite den_atom0, E9 in Ra1.
  change (SOff 240 19484) with (SOff A_TEXT 19484) in Rra. rewrite (codeptr_val E 19484 HEI) in Rra.
  rewrite den_atom0, E3 in Qgp. rewrite den_atom0, E4 in Qtp.
  rewrite den_atom0, E9 in Q9. rewrite den_atom0, E21 in Q21. rewrite den_atom0, E22 in Q22.
  assert (HspU : spZ (ms_regs ms1) = spZ regs - 112) by (unfold spZ at 1; rewrite Qsp, den_atom0, E2; apply unsigned_lit_small; lia).
  assert (HSm1 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) s (map (fun b : byte => bv_unsigned b) Sg)) by exact (kp_garr8_S _ HK1).
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_intrin_at (fx := fx) SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fx) W (ms_regs ms1) (ms_mem ms1)
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (g + 32 * Z.of_nat N) s 6 (spZ regs - 112 - sp0) (Z_to_bv 64 (BASE + 19484)) HJ).
    - exact Ra0.
    - exact Ra1.
    - rewrite Ra2. reflexivity.
    - lia. - lia. - lia.
    - rewrite HspU. lia.
    - apply mod16_sub; assumption.
    - lia.
    - unfold ESTACK. lia.
    - rewrite Qgp. exact Hgp.
    - rewrite Qtp. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [exact (proj1 (Hgw a ltac:(lia))) | unfold ESTACK; lia].
    - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
    - apply (kp_ra (ms_mem ms1) _ 6 HK1); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
      apply (range_addressable_sub _ _ g 264); [exact Hgra | lia | lia].
    - intros _. apply (kp_shv (ms_mem ms1) _ 6 HK1); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
      apply (gsp_hull_sub _ g 264); [exact Hgsh | lia | lia | lia | lia].
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. rewrite HspU. split; [apply (ga_aview_some (ms_mem ms1) s Sg a HSm1); rewrite HSl; lia | unfold ESTACK; lia]. }
      split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|]. split.
      + apply (kp_ra (ms_mem ms1) _ 6 HK1); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
        apply (range_addressable_sub _ _ s 24); [exact Hsra | lia | lia].
      + intros _. apply (kp_shv (ms_mem ms1) _ 6 HK1); [lia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia | lia |].
        apply (gsp_hull_sub _ s 24); [exact Hssh | lia | lia | lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hv2 & Hcpy & Hfr2 & Hpres2).
  assert (P2 : getr regs2 2 = getr (ms_regs ms1) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs2 3 = getr (ms_regs ms1) 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs2 4 = getr (ms_regs ms1) 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs2 9 = getr (ms_regs ms1) 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs2 19 = getr (ms_regs ms1) 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  assert (P21 : getr regs2 21 = getr (ms_regs ms1) 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
  assert (P22 : getr regs2 22 = getr (ms_regs ms1) 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
  destruct (app_mem _ (ms_mem ms1) mem2 N HN8 HK0 HP0 HT0 HSV0 HOW0 KC (fun a Ha => apresent_grows _ _ _ a HG Ha) VC
     ltac:(intros i0 Hi0; apply Hcpy; lia) ltac:(intros a Ha H1 H2; apply Hfr2; [exact Ha | exact H1 | lia]) Hpres2)
    as (HK2 & HP2' & HT2 & HSV2 & HOW2).
  clear HF HFr HG.
  assert (Hsp2 : spZ regs2 = spZ regs - 112) by (unfold spZ at 1; rewrite P2; exact HspU).
  assert (R9b : getr regs2 9 = w64 s) by (rewrite P9; exact Q9).
  assert (R19b : getr regs2 19 = w64 (g + 32 * Z.of_nat N)) by (rewrite P19; exact Q19).
  assert (R21b : getr regs2 21 = w64 GSB) by (rewrite P21; exact Q21).
  assert (R22b : getr regs2 22 = w64 (gdk Sg)) by (rewrite P22; exact Q22).
  assert (R3b : getr regs2 3 = getr regs 3) by (rewrite P3; exact Qgp).
  assert (R4b : getr regs2 4 = getr regs 4) by (rewrite P4; exact Qtp).
  clear HS SHOK.
  destruct (kst_A 0x4c1c regs2 mem2 (xA N) N HSV2 HOW2 HK2 HP2' HT2 HN8 Hsp2 R9b R19b R21b) as [HSb SHOKb].
  ekv regs2 (xA N) N 32%nat FQ32.
  ekv regs2 (xA N) N 33%nat FQ33. ekv regs2 (xA N) N 34%nat FQ34. ekv regs2 (xA N) N 35%nat FQ35. ekv regs2 (xA N) N 36%nat FQ36.
  ekv regs2 (xA N) N 37%nat FQ37. ekv regs2 (xA N) N 38%nat FQ38. ekv regs2 (xA N) N 39%nat FQ39. ekv regs2 (xA N) N 40%nat FQ40.
  ekv regs2 (xA N) N 41%nat FQ41. ekv regs2 (xA N) N 42%nat FQ42. ekv regs2 (xA N) N 43%nat FQ43. ekv regs2 (xA N) N 44%nat FQ44.
  ekv regs2 (xA N) N 45%nat FQ45. ekv regs2 (xA N) N 50%nat FQ50. ekv regs2 (xA N) N 51%nat FQ51.
  assert (F2 : ew (EK regs2 (xA N) N) 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite (ek_reg regs2 (xA N) N 2%bv 2 eq_refl), <- Hsp2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (F3 : ew (EK regs2 (xA N) N) 3 = getr regs 3) by (rewrite (ek_reg regs2 (xA N) N 3%bv 3 eq_refl); exact R3b).
  assert (F4 : ew (EK regs2 (xA N) N) 4 = getr regs 4) by (rewrite (ek_reg regs2 (xA N) N 4%bv 4 eq_refl); exact R4b).
  assert (F19 : ew (EK regs2 (xA N) N) 19 = Z_to_bv 64 (g + 32 * Z.of_nat N)) by (rewrite (ek_reg regs2 (xA N) N 19%bv 19 eq_refl); exact R19b).
  assert (F22 : ew (EK regs2 (xA N) N) 22 = Z_to_bv 64 (gdk Sg)) by (rewrite (ek_reg regs2 (xA N) N 22%bv 22 eq_refl); exact R22b).
  remember (EK regs2 (xA N) N) as E' eqn:HE'.
  assert (HEI' : img_env VAL A_LIM E') by (subst E'; apply Eimg_env).
  clear HE'.
  paj_run_tok RUN HSb HJ2 SHOKb GBspan; [awrN 19%nat (g + 32 * Z.of_nat N) F19|].
  kwE (g + 32 * Z.of_nat N) F19 HFr K3.
  lazymatch type of HSb with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms3 end.
  destruct (ent_keep mem2 (ms_mem ms3) N HN8 HK2 HP2' K3 HG) as [HK3 HP3].
  clear HF HFr HG.
  lazymatch type of HSb with st_ok_pi _ _ _ ?ss (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ss) rK_stk) in
    let r2 := eval vm_compute in (nth 2 (ss_mem ss) rK_stk) in
    pose proof (st_ok_pi_region_nth E' ss (restrict (w_H W) msx) 1 r1 HSb ltac:(vm_compute; reflexivity)) as RA;
    pose proof (st_ok_pi_region_nth E' ss (restrict (w_H W) msx) 2 r2 HSb ltac:(vm_compute; reflexivity)) as RB end.
  cbn [ms_mem restrict] in RA, RB.
  set (X1 := CtrlParsed.fld Sg 8 4). set (X2 := Mem.le4 (Z_to_bv 64 (GateModel.gdk Sg))).
  set (X3 := [nth 16 Sg (CtrlParsed.zb 0)]). set (X4 := Mem.le8 (Z_to_bv 64 now)).
  set (B1 := Mem.upd_bytes (xA N) (32 * N + 8) X1). set (B2 := Mem.upd_bytes B1 (32 * N + 12) X2).
  set (B3 := Mem.upd_bytes B2 (32 * N + 16) X3). set (B4 := Mem.upd_bytes B3 (32 * N + 24) X4).
  assert (LxA : length (xA N) = 264%nat) by (apply xA_len; exact HN8).
  assert (LX1 : length X1 = 4%nat) by (unfold X1; apply GateModel.length_fld; lia).
  assert (LX2 : length X2 = 4%nat) by (unfold X2; apply Mem.length_le4).
  assert (LX3 : length X3 = 1%nat) by reflexivity.
  assert (LX4 : length X4 = 8%nat) by (unfold X4; apply Mem.length_le8).
  assert (LB1 : length B1 = 264%nat) by (unfold B1; rewrite GateModel.length_upd; [exact LxA | rewrite LX1, LxA; lia]).
  assert (LB2 : length B2 = 264%nat) by (unfold B2; rewrite GateModel.length_upd; [exact LB1 | rewrite LX2, LB1; lia]).
  assert (LB3 : length B3 = 264%nat) by (unfold B3; rewrite GateModel.length_upd; [exact LB2 | rewrite LX3, LB2; lia]).
  assert (LB4 : length B4 = 264%nat) by (unfold B4; rewrite GateModel.length_upd; [exact LB3 | rewrite LX4, LB3; lia]).
  fleaf B4 1 F2 F3 F4 HJ2 HK3 HP3.
  + eapply (ent_leafB 19 E' mem2 (ms_mem ms3) (xA N) B4 N _ _ 8 17 24 32 (SExt true 32 (SOff 50 0)) (SOff 22 0) (SOff 51 0) (SOff 32 0)
            (CtrlParsed.fu Sg 8 4) (gdk Sg mod 2 ^ 32) (CtrlParsed.fb Sg 16) now HN8 HT2).
    * exact LB4.
    * intros a Ha H1 H2. apply K3; assumption.
    * intros j Hj H1 H2.
      unfold B4. rewrite nth_upd_out by (rewrite ?LX4, ?LB3; lia).
      unfold B3. rewrite nth_upd_out by (rewrite ?LX3, ?LB2; lia).
      unfold B2. rewrite nth_upd_out by (rewrite ?LX2, ?LB1; lia).
      unfold B1. rewrite nth_upd_out by (rewrite ?LX1, ?LxA; lia).
      reflexivity.
    * exact RA.
    * exact RB.
    * rewrite F19. apply unsigned_lit_small. lia.
    * inch.
    * inch.
    * inch.
    * inch.
    * apply (mod_sx32 E' 50 _ FQ50). apply GateModel.fu_rng4. lia.
    * apply (mod_w32 E' 22 _ F22).
    * apply (mod_atom E' 51 _ 8 FQ51); [apply GateModel.fb_rng | lia].
    * apply (mod_atom E' 32 _ 64 FQ32); [exact Rnow | lia].
    * unfold B4. rewrite GateModel.fld_upd_other by (rewrite ?LX4, ?LB3; lia).
      unfold B3. rewrite GateModel.fld_upd_other by (rewrite ?LX3, ?LB2; lia).
      unfold B2. rewrite GateModel.fld_upd_other by (rewrite ?LX2, ?LB1; lia).
      unfold B1. rewrite fld_upd_same' by (rewrite ?LX1, ?LxA; lia). unfold X1. apply fld_le. lia.
    * unfold B4. rewrite GateModel.fld_upd_other by (rewrite ?LX4, ?LB3; lia).
      unfold B3. rewrite GateModel.fld_upd_other by (rewrite ?LX3, ?LB2; lia).
      unfold B2. rewrite fld_upd_same' by (rewrite ?LX2, ?LB1; lia). unfold X2. apply le4_Z.
    * unfold B4. rewrite GateModel.fld_upd_other by (rewrite ?LX4, ?LB3; lia).
      unfold B3. rewrite fld_upd_same' by (rewrite ?LX3, ?LB2; lia). unfold X3. apply le1_fb.
    * unfold B4. rewrite fld_upd_same' by (rewrite ?LX4, ?LB3; lia). unfold X4. apply le8_Z. exact Rnow.
  + rewrite (GateModel.gm_app G Sg now N Hnone HgN HN8). reflexivity.
- rewrite (br_ge7 E 24 _ E24) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|].
  kw0 HFr KM1.
  destruct (call_keep _ _ G HK0 HP0 HT0 HSV0 HOW0 (fun a Ha _ => KM1 a Ha) (fun a Ha => apresent_grows _ _ _ a HG Ha))
    as (HK1 & HP1 & HT1 & HSV1 & HOW1).
  clear HF HFr HG.
  fleaf G 0 E2 E3 E4 HJ HK1 HP1.
  + exact HT1.
  + apply (GateModel.gm_full G Sg now Hnone). lia.
Qed.

Lemma gsp_nodup2 : forall a b : bv 5, bv_unsigned a <> bv_unsigned b -> NoDup [a; b].
Proof.
intros a b Hab. apply NoDup_cons_2; [|apply NoDup_cons_2; [intros H; inversion H | apply NoDup_nil_2]].
intros H. inversion H as [|? ? ? H1]; subst; [congruence | inversion H1].
Qed.
Definition eG2 (X1 : list byte) (i : nat) : list byte :=
  if CtrlParsed.fb Sg 16 =? 0 then X1 else Mem.upd_bytes X1 (32 * i + 16) [nth 16 Sg (CtrlParsed.zb 0)].
Definition eG3 (X1 : list byte) (i : nat) : list byte :=
  if gdk Sg <? 0 then eG2 X1 i else Mem.upd_bytes (eG2 X1 i) (32 * i + 12) (Mem.le4 (Z_to_bv 64 (gdk Sg))).
Definition eG4 (X1 : list byte) (i : nat) : list byte :=
  Mem.upd_bytes (eG3 X1 i) (32 * i + 24) (Mem.le8 (Z_to_bv 64 now)).
Lemma len_eG2 : forall X1 i, length X1 = 264%nat -> (i < 8)%nat -> length (eG2 X1 i) = 264%nat.
Proof. intros X1 i HL Hi. unfold eG2. destruct (CtrlParsed.fb Sg 16 =? 0); [exact HL|]. rewrite GateModel.length_upd; cbn [length]; lia. Qed.
Lemma len_eG3 : forall X1 i, length X1 = 264%nat -> (i < 8)%nat -> length (eG3 X1 i) = 264%nat.
Proof.
intros X1 i HL Hi. pose proof (len_eG2 X1 i HL Hi) as H2. unfold eG3. destruct (gdk Sg <? 0); [exact H2|].
rewrite GateModel.length_upd; rewrite ?Mem.length_le4; lia.
Qed.
Lemma len_eG4 : forall X1 i, length X1 = 264%nat -> (i < 8)%nat -> length (eG4 X1 i) = 264%nat.
Proof.
intros X1 i HL Hi. pose proof (len_eG3 X1 i HL Hi) as H3. unfold eG4.
rewrite GateModel.length_upd; rewrite ?Mem.length_le8; lia.
Qed.
Lemma blt0_atom : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E n v H Hv. rewrite den_atom0, H. cbn [sv_denot]. change (Z_to_bv 64 (zcanon 0)) with (Z_to_bv 64 0).
cbn [branch_taken]. apply GateModel.lts_lit; lia.
Qed.
Definition fE2_stmt : Prop := forall (i : nat) regs' m md (X1 : list byte),
  (i < 8)%nat -> length X1 = 264%nat ->
  GateModel.gate_model G Sg now = (eG4 X1 i, 1) ->
  tJ m md -> tKP m -> tPR m -> tTB m X1 -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 10 = w64 (s + 16) -> getr regs' 16 = w64 now ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB -> getr regs' 22 = w64 (gdk Sg) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4da0)) m (seg_rom SEGS)) md) tQ.

Lemma mod_mod_pow : forall z a b, 0 <= a <= b -> (z mod 2 ^ b) mod 2 ^ a = z mod 2 ^ a.
Proof.
intros z a b Hab. apply Z.bits_inj'. intros j Hj.
destruct (Z.lt_ge_cases j a) as [Hja|Hja].
- rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma mod_atom_s : forall E n v w, ew E n = Z_to_bv 64 v -> 0 <= w <= 64 ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ w = v mod 2 ^ w.
Proof.
intros E n v w H Hw. rewrite den_atom0, H, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply mod_mod_pow. lia.
Qed.
Ltac u18 HS E18 U e :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (U : bv_unsigned (ew Ex 18) = e)
      by (rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite E18; apply unsigned_lit_small; lia) end.
Ltac awrU U18 e :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18 e);
      [reflexivity | exact U18
      | cbn [YP09.r_wlo YP09.r_whi]; let a_ := fresh "a" in let Ha_ := fresh "Ha" in intros a_ Ha_; apply (proj1 (Hgw a_ ltac:(lia))) | ] ].
Ltac runE HS HJ SHOK E18 e :=
  let U := fresh "U18" in u18 HS E18 U e;
  paj_run_tok RUN HS HJ SHOK GBspan; [solve [awrU U e] |]; clear U.

Ltac tatom HS H0 H :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    lazymatch type of H0 with ew _ ?n = ?v =>
      assert (H : ew Ex n = v) by (rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact H0) end end.
Lemma beq0_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_eq_U, (U_off E n 0 v H) by lia. rewrite U_lit by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Ltac runEU HS HJ SHOK E18 e U :=
  u18 HS E18 U e; paj_run_tok RUN HS HJ SHOK GBspan; [solve [awrU U e] |].
Ltac kwU e U18 HFr K :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (e + 8 <= a < e + 17) -> ~ (e + 24 <= a < e + 32) -> aview SEGS H m' a = aview SEGS H m a);
  [ let a_ := fresh "a" in let Ha_ := fresh "Ha" in let Hn1 := fresh "Hn" in let Hn2 := fresh "Hn" in
    intros a_ Ha_ Hn1 Hn2;
    apply (kept_of_frame (segs := SEGS) Ex rs H m m' (fun a => e + 8 <= a < e + 17 \/ e + 24 <= a < e + 32) HFr); [ | exact Ha_ | tauto];
    let w := eval vm_compute in (windows rs) in change (windows rs) with w;
    let b_ := fresh "b" in let wlo_ := fresh "wlo" in let whi_ := fresh "whi" in let x_ := fresh "x" in
    let Hin_ := fresh "Hin" in let Hx_ := fresh "Hx" in
    intros b_ wlo_ whi_ x_ Hin_ Hx_; cbn [In] in Hin_;
    repeat (destruct Hin_ as [Hin_|Hin_]; [injection Hin_ as <- <- <-; cbn [base_val] in Hx_; first [lia | rewrite U18 in Hx_; lia] |]);
    try destruct Hin_
  | ] end.

Lemma eG4_facts : forall X1 (i : nat), length X1 = 264%nat -> (i < 8)%nat ->
  length (eG4 X1 i) = 264%nat /\
  CtrlParsed.fld (eG4 X1 i) (32 * i + 8) 4 = CtrlParsed.fld X1 (32 * i + 8) 4 /\
  CtrlParsed.fld (eG4 X1 i) (32 * i + 12) 4 =
    (if gdk Sg <? 0 then CtrlParsed.fld X1 (32 * i + 12) 4 else Mem.le4 (Z_to_bv 64 (gdk Sg))) /\
  CtrlParsed.fld (eG4 X1 i) (32 * i + 16) 1 =
    (if CtrlParsed.fb Sg 16 =? 0 then CtrlParsed.fld X1 (32 * i + 16) 1 else [nth 16 Sg (CtrlParsed.zb 0)]) /\
  CtrlParsed.fld (eG4 X1 i) (32 * i + 24) 8 = Mem.le8 (Z_to_bv 64 now) /\
  (forall j, (j < 264)%nat -> ~ (32 * i + 8 <= j < 32 * i + 17)%nat -> ~ (32 * i + 24 <= j < 32 * i + 32)%nat ->
     nth_error (eG4 X1 i) j = nth_error X1 j).
Proof.
intros X1 i HL Hi.
assert (L8 : length (Mem.le8 (Z_to_bv 64 now)) = 8%nat) by apply Mem.length_le8.
assert (L4 : length (Mem.le4 (Z_to_bv 64 (gdk Sg))) = 4%nat) by apply Mem.length_le4.
assert (L1 : length [nth 16 Sg (CtrlParsed.zb 0)] = 1%nat) by reflexivity.
assert (LE2 : length (eG2 X1 i) = 264%nat) by (apply len_eG2; assumption).
assert (LE3 : length (eG3 X1 i) = 264%nat) by (apply len_eG3; assumption).
assert (LE4 : length (eG4 X1 i) = 264%nat) by (apply len_eG4; assumption).
assert (F3 : forall k n, (k + n <= 264)%nat -> (k + n <= 32 * i + 24 \/ 32 * i + 32 <= k)%nat ->
   CtrlParsed.fld (eG4 X1 i) k n = CtrlParsed.fld (eG3 X1 i) k n)
  by (intros kk nn Hk Hd; unfold eG4; apply GateModel.fld_upd_other; [rewrite L8, LE3; lia | rewrite L8; lia]).
assert (F2 : forall k n, (k + n <= 264)%nat -> (k + n <= 32 * i + 12 \/ 32 * i + 16 <= k)%nat ->
   CtrlParsed.fld (eG3 X1 i) k n = CtrlParsed.fld (eG2 X1 i) k n).
{ intros kk nn Hk Hd. unfold eG3. destruct (gdk Sg <? 0); [reflexivity|].
  apply GateModel.fld_upd_other; [rewrite L4, LE2; lia | rewrite L4; lia]. }
assert (F1 : forall k n, (k + n <= 264)%nat -> (k + n <= 32 * i + 16 \/ 32 * i + 17 <= k)%nat ->
   CtrlParsed.fld (eG2 X1 i) k n = CtrlParsed.fld X1 k n).
{ intros kk nn Hk Hd. unfold eG2. destruct (CtrlParsed.fb Sg 16 =? 0); [reflexivity|].
  apply GateModel.fld_upd_other; [rewrite L1, HL; lia | rewrite L1; lia]. }
split; [exact LE4|].
split; [rewrite F3 by lia; rewrite F2 by lia; apply F1; lia|].
split.
{ rewrite F3 by lia. unfold eG3. destruct (gdk Sg <? 0); [apply F1; lia|].
  apply fld_upd_same'; [exact L4 | rewrite LE2; lia]. }
split.
{ rewrite F3 by lia. rewrite F2 by lia. unfold eG2. destruct (CtrlParsed.fb Sg 16 =? 0); [reflexivity|].
  apply fld_upd_same'; [exact L1 | rewrite HL; lia]. }
split.
{ unfold eG4. apply fld_upd_same'; [exact L8 | rewrite LE3; lia]. }
intros j Hj H1 H2.
assert (N4 : nth_error (eG4 X1 i) j = nth_error (eG3 X1 i) j)
  by (unfold eG4; apply nth_upd_out; [rewrite L8, LE3; lia | rewrite L8; lia]).
assert (N3 : nth_error (eG3 X1 i) j = nth_error (eG2 X1 i) j).
{ unfold eG3. destruct (gdk Sg <? 0); [reflexivity|]. apply nth_upd_out; [rewrite L4, LE2; lia | rewrite L4; lia]. }
assert (N2 : nth_error (eG2 X1 i) j = nth_error X1 j).
{ unfold eG2. destruct (CtrlParsed.fb Sg 16 =? 0); [reflexivity|]. apply nth_upd_out; [rewrite L1, HL; lia | rewrite L1; lia]. }
rewrite N4, N3, N2. reflexivity.
Qed.

Ltac rgn2 RA RB :=
  lazymatch goal with HS : st_ok_pi _ _ ?E0 ?ss (restrict _ ?msx) |- _ =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ss) rK_stk) in
    let r2 := eval vm_compute in (nth 2 (ss_mem ss) rK_stk) in
    pose proof (st_ok_pi_region_nth E0 ss (restrict (w_H W) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RA;
    pose proof (st_ok_pi_region_nth E0 ss (restrict (w_H W) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as RB;
    cbn [ms_mem restrict] in RA, RB end.

Lemma fE2_ok : fE2_stmt.
Proof.
intros i regs' m md X1 Hi HXl HMOD HJ HK HP HT HSV HOW Hsp R3 R4 R9 R10 R16 R18 R21 R22.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof Hgside as Hgs'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs', Hlo.
assert (Rdk : -1 <= gdk Sg < 65536) by (unfold gdk; apply GateModel.gdk_rng). pose proof (GateModel.fb_rng Sg 16) as Rf16.
destruct (kst_G 0x4da0 [(10%bv, SOff 9 16); (16%bv, SOff 32 0)] regs' m X1 i
  ltac:(apply gsp_nodup2; vm_compute; discriminate)
  ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        [ split; [vm_compute; reflexivity |
            rewrite R10; symmetry; apply (den_off (EK regs' X1 i) 9 16 s);
            [rewrite (ek_reg regs' X1 i 9%bv 9 eq_refl); exact R9 | lia | lia] ]
        | split; [vm_compute; reflexivity |
            rewrite R16; symmetry; rewrite den_atom0; unfold EK;
            rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0) ] ])
  HSV HOW HK HP HT Hi Hsp R9 R18 R21) as [HS SHOK].
ekv regs' X1 i 33%nat EQ33. ekv regs' X1 i 34%nat EQ34. ekv regs' X1 i 35%nat EQ35. ekv regs' X1 i 36%nat EQ36.
ekv regs' X1 i 37%nat EQ37. ekv regs' X1 i 38%nat EQ38. ekv regs' X1 i 39%nat EQ39. ekv regs' X1 i 40%nat EQ40.
ekv regs' X1 i 41%nat EQ41. ekv regs' X1 i 42%nat EQ42. ekv regs' X1 i 43%nat EQ43. ekv regs' X1 i 44%nat EQ44.
ekv regs' X1 i 45%nat EQ45.
ekv regs' X1 i 46%nat EQ46. ekv regs' X1 i 47%nat EQ47. ekv regs' X1 i 48%nat EQ48. ekv regs' X1 i 49%nat EQ49.
ekv regs' X1 i 50%nat EQ50. ekv regs' X1 i 51%nat EQ51.
assert (E2 : ew (EK regs' X1 i) 2 = Z_to_bv 64 (spZ regs - 112))
  by (rewrite (ek_reg regs' X1 i 2%bv 2 eq_refl), <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew (EK regs' X1 i) 3 = getr regs 3) by (rewrite (ek_reg regs' X1 i 3%bv 3 eq_refl); exact R3).
assert (E4 : ew (EK regs' X1 i) 4 = getr regs 4) by (rewrite (ek_reg regs' X1 i 4%bv 4 eq_refl); exact R4).
assert (E18 : ew (EK regs' X1 i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i))
  by (rewrite (ek_reg regs' X1 i 18%bv 18 eq_refl); exact R18).
assert (E22 : ew (EK regs' X1 i) 22 = Z_to_bv 64 (gdk Sg)) by (rewrite (ek_reg regs' X1 i 22%bv 22 eq_refl); exact R22).
assert (E32 : ew (EK regs' X1 i) 32 = Z_to_bv 64 now)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
remember (EK regs' X1 i) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
clear HE.

runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA.
kwU (g + 32 * Z.of_nat i) UA HFr K1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms1 end.
destruct (ent_keep m (ms_mem ms1) i Hi HK HP K1 HG) as [HK1 HP1].
destruct (ent_sv m (ms_mem ms1) HSV HOW ltac:(intros a Ha Hs2; apply K1; lia)) as [HSV1 HOW1].
clear HF HFr HG.
tatom HS EQ51 C51.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (beq0_atom _ 51 _ C51) in Hc by (pose proof (GateModel.fb_rng Sg 16); lia).
  apply Z.eqb_eq in Hc. rename Hc into Hf.
  runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB.
  kwU (g + 32 * Z.of_nat i) UB HFr K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms2 end.
  destruct (ent_keep (ms_mem ms1) (ms_mem ms2) i Hi HK1 HP1 K2 HG) as [HK2 HP2].
  destruct (ent_sv (ms_mem ms1) (ms_mem ms2) HSV1 HOW1 ltac:(intros a Ha Hs2; apply K2; lia)) as [HSV2 HOW2].
  clear HF HFr HG.
  tatom HS E22 C22.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (blt0_atom _ 22 _ C22) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hdk.
    runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC.
    kwU (g + 32 * Z.of_nat i) UC HFr K3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms3 end.
    destruct (ent_keep (ms_mem ms2) (ms_mem ms3) i Hi HK2 HP2 K3 HG) as [HK3 HP3].
    clear HF HFr HG.
    u18 HS E18 UL (g + 32 * Z.of_nat i). tatom HS EQ33 B33; tatom HS EQ34 B34; tatom HS EQ35 B35; tatom HS EQ36 B36; tatom HS EQ37 B37;
    tatom HS EQ38 B38; tatom HS EQ39 B39; tatom HS EQ40 B40; tatom HS EQ41 B41; tatom HS EQ42 B42;
    tatom HS EQ43 B43; tatom HS EQ44 B44; tatom HS EQ45 B45;
    tatom HS EQ46 B46; tatom HS EQ47 B47; tatom HS EQ48 B48; tatom HS EQ51 B51;
    tatom HS E2 B2; tatom HS E3 B3; tatom HS E4 B4; tatom HS E22 B22; tatom HS E32 B32. rgn2 RA RB.
    pose proof (eG4_facts X1 i HXl Hi) as (FL & F8 & F12 & F16 & F24 & FN).
    fleaf (eG4 X1 i) 1 B2 B3 B4 HJ HK3 HP3.
    * eapply (ent_leaf _ m (ms_mem ms3) X1 (eG4 X1 i) i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 48 0) (SOff 32 0)
               (CtrlParsed.fu X1 (32 * i + 8) 4) (CtrlParsed.fu X1 (32 * i + 12) 4) (CtrlParsed.fb X1 (32 * i + 16)) now Hi HT).
      -- exact FL.
      -- intros a Ha Ha1 Ha2. rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
      -- intros j Hj Hj1 Hj2. apply FN; assumption.
      -- exact RA.
      -- exact RB.
      -- exact UL.
      -- inch. -- inch. -- inch. -- inch.
      -- apply (mod_atom _ 46 _ 32 B46); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom _ 47 _ 32 B47); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom _ 48 _ 8 B48); [apply GateModel.fb_rng | lia].
      -- apply (mod_atom _ 32 _ 64 B32); [exact Rnow | lia].
      -- rewrite F8. apply fld_le; lia.
      -- rewrite F12. replace (gdk Sg <? 0) with true by (symmetry; apply Z.ltb_lt; exact Hdk). apply fld_le; lia.
      -- rewrite F16. replace (CtrlParsed.fb Sg 16 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hf). rewrite GateModel.fld1 by lia. apply le1_fb.
      -- rewrite F24. apply le8_Z. exact Rnow.
    * exact HMOD.

  + rewrite (blt0_atom _ 22 _ C22) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hdk.
    runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC.
    kwU (g + 32 * Z.of_nat i) UC HFr K3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms3 end.
    destruct (ent_keep (ms_mem ms2) (ms_mem ms3) i Hi HK2 HP2 K3 HG) as [HK3 HP3].
    clear HF HFr HG.
    u18 HS E18 UL (g + 32 * Z.of_nat i). tatom HS EQ33 B33; tatom HS EQ34 B34; tatom HS EQ35 B35; tatom HS EQ36 B36; tatom HS EQ37 B37;
    tatom HS EQ38 B38; tatom HS EQ39 B39; tatom HS EQ40 B40; tatom HS EQ41 B41; tatom HS EQ42 B42;
    tatom HS EQ43 B43; tatom HS EQ44 B44; tatom HS EQ45 B45;
    tatom HS EQ46 B46; tatom HS EQ47 B47; tatom HS EQ48 B48; tatom HS EQ51 B51;
    tatom HS E2 B2; tatom HS E3 B3; tatom HS E4 B4; tatom HS E22 B22; tatom HS E32 B32. rgn2 RA RB.
    pose proof (eG4_facts X1 i HXl Hi) as (FL & F8 & F12 & F16 & F24 & FN).
    fleaf (eG4 X1 i) 1 B2 B3 B4 HJ HK3 HP3.
    * eapply (ent_leaf _ m (ms_mem ms3) X1 (eG4 X1 i) i _ _ 8 17 24 32 (SOff 46 0) (SOff 22 0) (SOff 48 0) (SOff 32 0)
               (CtrlParsed.fu X1 (32 * i + 8) 4) (gdk Sg mod 2 ^ 32) (CtrlParsed.fb X1 (32 * i + 16)) now Hi HT).
      -- exact FL.
      -- intros a Ha Ha1 Ha2. rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
      -- intros j Hj Hj1 Hj2. apply FN; assumption.
      -- exact RA.
      -- exact RB.
      -- exact UL.
      -- inch. -- inch. -- inch. -- inch.
      -- apply (mod_atom _ 46 _ 32 B46); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom_s _ 22 _ 32 B22); lia.
      -- apply (mod_atom _ 48 _ 8 B48); [apply GateModel.fb_rng | lia].
      -- apply (mod_atom _ 32 _ 64 B32); [exact Rnow | lia].
      -- rewrite F8. apply fld_le; lia.
      -- rewrite F12. replace (gdk Sg <? 0) with false by (symmetry; apply Z.ltb_ge; lia). apply le4_Z.
      -- rewrite F16. replace (CtrlParsed.fb Sg 16 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hf). rewrite GateModel.fld1 by lia. apply le1_fb.
      -- rewrite F24. apply le8_Z. exact Rnow.
    * exact HMOD.

- rewrite (beq0_atom _ 51 _ C51) in Hc by (pose proof (GateModel.fb_rng Sg 16); lia).
  apply Z.eqb_neq in Hc. rename Hc into Hf.
  runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB.
  kwU (g + 32 * Z.of_nat i) UB HFr K2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms2 end.
  destruct (ent_keep (ms_mem ms1) (ms_mem ms2) i Hi HK1 HP1 K2 HG) as [HK2 HP2].
  destruct (ent_sv (ms_mem ms1) (ms_mem ms2) HSV1 HOW1 ltac:(intros a Ha Hs2; apply K2; lia)) as [HSV2 HOW2].
  clear HF HFr HG.
  tatom HS E22 C22.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (blt0_atom _ 22 _ C22) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hdk.
    runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC.
    kwU (g + 32 * Z.of_nat i) UC HFr K3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms3 end.
    destruct (ent_keep (ms_mem ms2) (ms_mem ms3) i Hi HK2 HP2 K3 HG) as [HK3 HP3].
    clear HF HFr HG.
    u18 HS E18 UL (g + 32 * Z.of_nat i). tatom HS EQ33 B33; tatom HS EQ34 B34; tatom HS EQ35 B35; tatom HS EQ36 B36; tatom HS EQ37 B37;
    tatom HS EQ38 B38; tatom HS EQ39 B39; tatom HS EQ40 B40; tatom HS EQ41 B41; tatom HS EQ42 B42;
    tatom HS EQ43 B43; tatom HS EQ44 B44; tatom HS EQ45 B45;
    tatom HS EQ46 B46; tatom HS EQ47 B47; tatom HS EQ48 B48; tatom HS EQ51 B51;
    tatom HS E2 B2; tatom HS E3 B3; tatom HS E4 B4; tatom HS E22 B22; tatom HS E32 B32. rgn2 RA RB.
    pose proof (eG4_facts X1 i HXl Hi) as (FL & F8 & F12 & F16 & F24 & FN).
    fleaf (eG4 X1 i) 1 B2 B3 B4 HJ HK3 HP3.
    * eapply (ent_leaf _ m (ms_mem ms3) X1 (eG4 X1 i) i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 51 0) (SOff 32 0)
               (CtrlParsed.fu X1 (32 * i + 8) 4) (CtrlParsed.fu X1 (32 * i + 12) 4) (CtrlParsed.fb Sg 16) now Hi HT).
      -- exact FL.
      -- intros a Ha Ha1 Ha2. rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
      -- intros j Hj Hj1 Hj2. apply FN; assumption.
      -- exact RA.
      -- exact RB.
      -- exact UL.
      -- inch. -- inch. -- inch. -- inch.
      -- apply (mod_atom _ 46 _ 32 B46); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom _ 47 _ 32 B47); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom _ 51 _ 8 B51); [apply GateModel.fb_rng | lia].
      -- apply (mod_atom _ 32 _ 64 B32); [exact Rnow | lia].
      -- rewrite F8. apply fld_le; lia.
      -- rewrite F12. replace (gdk Sg <? 0) with true by (symmetry; apply Z.ltb_lt; exact Hdk). apply fld_le; lia.
      -- rewrite F16. replace (CtrlParsed.fb Sg 16 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf). apply le1_fb.
      -- rewrite F24. apply le8_Z. exact Rnow.
    * exact HMOD.

  + rewrite (blt0_atom _ 22 _ C22) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hdk.
    runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC.
    kwU (g + 32 * Z.of_nat i) UC HFr K3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms3 end.
    destruct (ent_keep (ms_mem ms2) (ms_mem ms3) i Hi HK2 HP2 K3 HG) as [HK3 HP3].
    clear HF HFr HG.
    u18 HS E18 UL (g + 32 * Z.of_nat i). tatom HS EQ33 B33; tatom HS EQ34 B34; tatom HS EQ35 B35; tatom HS EQ36 B36; tatom HS EQ37 B37;
    tatom HS EQ38 B38; tatom HS EQ39 B39; tatom HS EQ40 B40; tatom HS EQ41 B41; tatom HS EQ42 B42;
    tatom HS EQ43 B43; tatom HS EQ44 B44; tatom HS EQ45 B45;
    tatom HS EQ46 B46; tatom HS EQ47 B47; tatom HS EQ48 B48; tatom HS EQ51 B51;
    tatom HS E2 B2; tatom HS E3 B3; tatom HS E4 B4; tatom HS E22 B22; tatom HS E32 B32. rgn2 RA RB.
    pose proof (eG4_facts X1 i HXl Hi) as (FL & F8 & F12 & F16 & F24 & FN).
    fleaf (eG4 X1 i) 1 B2 B3 B4 HJ HK3 HP3.
    * eapply (ent_leaf _ m (ms_mem ms3) X1 (eG4 X1 i) i _ _ 8 17 24 32 (SOff 46 0) (SOff 22 0) (SOff 51 0) (SOff 32 0)
               (CtrlParsed.fu X1 (32 * i + 8) 4) (gdk Sg mod 2 ^ 32) (CtrlParsed.fb Sg 16) now Hi HT).
      -- exact FL.
      -- intros a Ha Ha1 Ha2. rewrite K3 by lia. rewrite K2 by lia. apply K1; lia.
      -- intros j Hj Hj1 Hj2. apply FN; assumption.
      -- exact RA.
      -- exact RB.
      -- exact UL.
      -- inch. -- inch. -- inch. -- inch.
      -- apply (mod_atom _ 46 _ 32 B46); [apply GateModel.fu_rng4; lia | lia].
      -- apply (mod_atom_s _ 22 _ 32 B22); lia.
      -- apply (mod_atom _ 51 _ 8 B51); [apply GateModel.fb_rng | lia].
      -- apply (mod_atom _ 32 _ 64 B32); [exact Rnow | lia].
      -- rewrite F8. apply fld_le; lia.
      -- rewrite F12. replace (gdk Sg <? 0) with false by (symmetry; apply Z.ltb_ge; lia). apply le4_Z.
      -- rewrite F16. replace (CtrlParsed.fb Sg 16 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf). apply le1_fb.
      -- rewrite F24. apply le8_Z. exact Rnow.
    * exact HMOD.

Qed.

Lemma gsp_nodup3 : forall a b c : bv 5,
  bv_unsigned a <> bv_unsigned b -> bv_unsigned a <> bv_unsigned c -> bv_unsigned b <> bv_unsigned c ->
  NoDup [a; b; c].
Proof.
intros a b c Hab Hac Hbc. apply NoDup_cons_2; [|apply gsp_nodup2; exact Hbc].
intros H. inversion H as [|? ? ? H1]; subst; [congruence|].
inversion H1 as [|? ? ? H2]; subst; [congruence | inversion H2].
Qed.
Lemma s32_mod32 : forall x, 0 <= x < 2 ^ 32 -> CtrlParsed.s32 x mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold CtrlParsed.s32. destruct (Z.ltb_spec x (2 ^ 31)).
- apply Z.mod_small. lia.
- replace (x - 2 ^ 32) with (x + (-1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma u_s32 : forall v, 0 <= v < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (CtrlParsed.s32 v)) = (if v <? 2 ^ 31 then v else v - 2 ^ 32 + 2 ^ 64).
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold CtrlParsed.s32.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota.
- apply Z.mod_small. lia.
- symmetry. apply (Z.mod_unique (v - 2 ^ 32) (2 ^ 64) (-1)); lia.
Qed.
Lemma beq_s32 : forall E n v, ew E n = Z_to_bv 64 (CtrlParsed.s32 v) -> 0 <= v < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_eq_U, U_SOff, H, Z.add_0_r, U_lit by lia. rewrite u_s32 by lia.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; rewrite zcanon_id by (unfold M64; lia);
apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; lia.
Qed.
Lemma s32_atom_mod : forall E n v, ew E n = Z_to_bv 64 (CtrlParsed.s32 v) -> 0 <= v < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ 32 = v.
Proof.
intros E n v H Hv. rewrite den_atom0, H, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite mod_mod_pow by lia. apply s32_mod32. exact Hv.
Qed.
Lemma den_sext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (CtrlParsed.s32 v).
Proof.
intros E n v H Hv. apply bv_eq. change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt, (U_atom E n v H) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v) by lia.
rewrite GateModel.s32_swrap by lia. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma sext_mod32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ 32 = v.
Proof.
intros E n v H Hv. rewrite (den_sext32 E n v H Hv), Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite mod_mod_pow by lia. apply s32_mod32. exact Hv.
Qed.
Lemma fE_model : forall (i : nat),
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = true ->
  GateModel.gate_model G Sg now =
    (eG4 (if CtrlParsed.fu Sg 8 4 =? 0 then G else Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) i, 1).
Proof. intros i H1 H2. rewrite (GateModel.gm_edge G Sg now i H1 H2). unfold eG4, eG3, eG2, gdk. reflexivity. Qed.
Ltac runEUto HS HJ SHOK E18 e U stop :=
  u18 HS E18 U e; paj_run_to_tok RUNTO HS HJ SHOK GBspan stop; [solve [awrU U e] |].
Definition fE1_stmt : Prop := forall (i : nat) regs' m md,
  (i < 8)%nat ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = true ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 10 = w64 (s + 16) ->
  getr regs' 12 = Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) -> getr regs' 16 = w64 now ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB -> getr regs' 22 = w64 (gdk Sg) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4d84)) m (seg_rom SEGS)) md) tQ.
Definition fE1b_stmt : Prop := forall (i : nat) regs' m md,
  (i < 8)%nat ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  GateModel.gedge G Sg i = true -> CtrlParsed.fu Sg 8 4 <> 0 ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 10 = w64 (s + 16) ->
  getr regs' 12 = Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) -> getr regs' 16 = w64 now ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB -> getr regs' 22 = w64 (gdk Sg) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4d88)) m (seg_rom SEGS)) md) tQ.
Ltac lfs := rewrite ?GateModel.length_fld by lia; rewrite ?HGl; lia.
Lemma fE1b_ok : fE1b_stmt.
Proof.
intros i regs' m md Hi Hgf Hed Hnz HJ HK HP HT HSV HOW Hsp R3 R4 R9 R10 R12 R16 R18 R21 R22.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof Hgside as Hgs'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs', Hlo.
pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8s.
pose proof (fE_model i Hgf Hed) as HMOD.
destruct (kst_G 0x4d88 [] regs' m G i NoDup_nil_2 (Forall_nil _) HSV HOW HK HP HT Hi Hsp R9 R18 R21) as [HS SHOK].
ekv regs' G i 46%nat EQ46. ekv regs' G i 47%nat EQ47. ekv regs' G i 48%nat EQ48. ekv regs' G i 49%nat EQ49.
assert (E2 : ew (EK regs' G i) 2 = Z_to_bv 64 (spZ regs - 112))
  by (rewrite (ek_reg regs' G i 2%bv 2 eq_refl), <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew (EK regs' G i) 3 = getr regs 3) by (rewrite (ek_reg regs' G i 3%bv 3 eq_refl); exact R3).
assert (E4 : ew (EK regs' G i) 4 = getr regs 4) by (rewrite (ek_reg regs' G i 4%bv 4 eq_refl); exact R4).
assert (E9 : ew (EK regs' G i) 9 = Z_to_bv 64 s) by (rewrite (ek_reg regs' G i 9%bv 9 eq_refl); exact R9).
assert (E10 : ew (EK regs' G i) 10 = Z_to_bv 64 (s + 16)) by (rewrite (ek_reg regs' G i 10%bv 10 eq_refl); exact R10).
assert (E12 : ew (EK regs' G i) 12 = Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4))) by (rewrite (ek_reg regs' G i 12%bv 12 eq_refl); exact R12).
assert (E16 : ew (EK regs' G i) 16 = Z_to_bv 64 now) by (rewrite (ek_reg regs' G i 16%bv 16 eq_refl); exact R16).
assert (E18 : ew (EK regs' G i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i)) by (rewrite (ek_reg regs' G i 18%bv 18 eq_refl); exact R18).
assert (E21 : ew (EK regs' G i) 21 = Z_to_bv 64 GSB) by (rewrite (ek_reg regs' G i 21%bv 21 eq_refl); exact R21).
assert (E22 : ew (EK regs' G i) 22 = Z_to_bv 64 (gdk Sg)) by (rewrite (ek_reg regs' G i 22%bv 22 eq_refl); exact R22).
remember (EK regs' G i) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
clear HE.
runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA 0x4da0.
kwU (g + 32 * Z.of_nat i) UA HFr K1.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms1 end.
destruct (ent_keep m (ms_mem ms1) i Hi HK HP K1 HG) as [HK1 HP1].
destruct (ent_sv m (ms_mem ms1) HSV HOW ltac:(intros a Ha Hs2; apply K1; lia)) as [HSV1 HOW1].
clear HF HFr HG.
u18 HS E18 UL (g + 32 * Z.of_nat i).
tatom HS EQ46 B46. tatom HS EQ47 B47. tatom HS EQ48 B48. tatom HS EQ49 B49. tatom HS E12 B12.
tatom HS E2 B2. tatom HS E3 B3. tatom HS E4 B4. tatom HS E9 B9. tatom HS E10 B10. tatom HS E16 B16.
tatom HS E18 B18. tatom HS E21 B21. tatom HS E22 B22.
rgn2 RA RB.
assert (HT1 : tTB (ms_mem ms1) (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4))).
{ eapply (ent_leaf _ m (ms_mem ms1) G (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) i _ _ 8 17 24 32 (SOff 12 0) (SOff 47 0) (SOff 48 0) (SOff 49 0)
     (CtrlParsed.fu Sg 8 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16)) (CtrlParsed.fu G (32 * i + 24) 8) Hi HT).
  * rewrite GateModel.length_upd by lfs. exact HGl.
  * intros a Ha Ha1 Ha2. exact (K1 a Ha Ha1 Ha2).
  * intros j Hj Hj1 Hj2. apply nth_upd_out; lfs.
  * exact RA.
  * exact RB.
  * exact UL.
  * inch. * inch. * inch. * inch.
  * apply (s32_atom_mod _ 12 _ B12); lia.
  * apply (mod_atom _ 47 _ 32 B47); [apply GateModel.fu_rng4; lia | lia].
  * apply (mod_atom _ 48 _ 8 B48); [apply GateModel.fb_rng | lia].
  * apply (mod_atom _ 49 _ 64 B49); [apply GateModel.fu_rng8; lia | lia].
  * rewrite fld_upd_same'; [apply fld_le; lia | apply GateModel.length_fld; lia | lfs].
  * rewrite GateModel.fld_upd_other by lfs; apply fld_le; lia.
  * rewrite GateModel.fld_upd_other by lfs; rewrite GateModel.fld1 by lia; apply le1_fb.
  * rewrite GateModel.fld_upd_other by lfs; apply fld_le; lia. }
preg HS (2%bv : bv 5) Q2. preg HS (3%bv : bv 5) Q3. preg HS (4%bv : bv 5) Q4. preg HS (9%bv : bv 5) Q9.
preg HS (10%bv : bv 5) Q10. preg HS (16%bv : bv 5) Q16. preg HS (18%bv : bv 5) Q18. preg HS (21%bv : bv 5) Q21.
preg HS (22%bv : bv 5) Q22.
pmkst HS.
apply (fE2_ok i _ _ _ (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) Hi (proj2 HT1)).
- rewrite (fE_model i Hgf Hed). replace (CtrlParsed.fu Sg 8 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). reflexivity.
- first [exact HJ | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ].
- exact HK1. - exact HP1. - exact HT1. - exact HSV1. - exact HOW1.
- unfold spZ at 1. rewrite Q2, den_atom0, B2. apply unsigned_lit_small. lia.
- rewrite Q3, den_atom0. exact B3.
- rewrite Q4, den_atom0. exact B4.
- rewrite Q9, den_atom0. exact B9.
- rewrite Q10, den_atom0. exact B10.
- rewrite Q16, den_atom0. exact B16.
- rewrite Q18, den_atom0. exact B18.
- rewrite Q21, den_atom0. exact B21.
- rewrite Q22, den_atom0. exact B22.
Qed.
Lemma fE1_ok : fE1_stmt.
Proof.
intros i regs' m md Hi Hgf Hed HJ HK HP HT HSV HOW Hsp R3 R4 R9 R10 R12 R16 R18 R21 R22.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hgam as Hg'. pose proof Hsam as Hs'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs'.
pose proof Hgside as Hgs'. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs', Hlo.
pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R8s.
pose proof (fE_model i Hgf Hed) as HMOD.
destruct (kst_G 0x4d84 [] regs' m G i NoDup_nil_2 (Forall_nil _) HSV HOW HK HP HT Hi Hsp R9 R18 R21) as [HS SHOK].
ekv regs' G i 46%nat EQ46. ekv regs' G i 47%nat EQ47. ekv regs' G i 48%nat EQ48. ekv regs' G i 49%nat EQ49.
assert (E2 : ew (EK regs' G i) 2 = Z_to_bv 64 (spZ regs - 112))
  by (rewrite (ek_reg regs' G i 2%bv 2 eq_refl), <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew (EK regs' G i) 3 = getr regs 3) by (rewrite (ek_reg regs' G i 3%bv 3 eq_refl); exact R3).
assert (E4 : ew (EK regs' G i) 4 = getr regs 4) by (rewrite (ek_reg regs' G i 4%bv 4 eq_refl); exact R4).
assert (E9 : ew (EK regs' G i) 9 = Z_to_bv 64 s) by (rewrite (ek_reg regs' G i 9%bv 9 eq_refl); exact R9).
assert (E10 : ew (EK regs' G i) 10 = Z_to_bv 64 (s + 16)) by (rewrite (ek_reg regs' G i 10%bv 10 eq_refl); exact R10).
assert (E12 : ew (EK regs' G i) 12 = Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4))) by (rewrite (ek_reg regs' G i 12%bv 12 eq_refl); exact R12).
assert (E16 : ew (EK regs' G i) 16 = Z_to_bv 64 now) by (rewrite (ek_reg regs' G i 16%bv 16 eq_refl); exact R16).
assert (E18 : ew (EK regs' G i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i)) by (rewrite (ek_reg regs' G i 18%bv 18 eq_refl); exact R18).
assert (E21 : ew (EK regs' G i) 21 = Z_to_bv 64 GSB) by (rewrite (ek_reg regs' G i 21%bv 21 eq_refl); exact R21).
assert (E22 : ew (EK regs' G i) 22 = Z_to_bv 64 (gdk Sg)) by (rewrite (ek_reg regs' G i 22%bv 22 eq_refl); exact R22).
remember (EK regs' G i) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
clear HE.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (beq_s32 E 12 _ E12) in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hnz.
  runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA 0x4da0.
  kwU (g + 32 * Z.of_nat i) UA HFr K1.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms1 end.
  destruct (ent_keep m (ms_mem ms1) i Hi HK HP K1 HG) as [HK1 HP1].
  destruct (ent_sv m (ms_mem ms1) HSV HOW ltac:(intros a Ha Hs2; apply K1; lia)) as [HSV1 HOW1].
  clear HF HFr HG.
  u18 HS E18 UL (g + 32 * Z.of_nat i).
  tatom HS EQ46 B46. tatom HS EQ47 B47. tatom HS EQ48 B48. tatom HS EQ49 B49. tatom HS E12 B12.
  tatom HS E2 B2. tatom HS E3 B3. tatom HS E4 B4. tatom HS E9 B9. tatom HS E10 B10. tatom HS E16 B16.
  tatom HS E18 B18. tatom HS E21 B21. tatom HS E22 B22.
  rgn2 RA RB.
  assert (HT1 : tTB (ms_mem ms1) (G)).
  { eapply (ent_leaf _ m (ms_mem ms1) G (G) i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 48 0) (SOff 49 0)
       (CtrlParsed.fu G (32 * i + 8) 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16)) (CtrlParsed.fu G (32 * i + 24) 8) Hi HT).
    * exact HGl.
    * intros a Ha Ha1 Ha2. exact (K1 a Ha Ha1 Ha2).
    * intros j Hj Hj1 Hj2. reflexivity.
    * exact RA.
    * exact RB.
    * exact UL.
    * inch. * inch. * inch. * inch.
    * apply (mod_atom _ 46 _ 32 B46); [apply GateModel.fu_rng4; lia | lia].
    * apply (mod_atom _ 47 _ 32 B47); [apply GateModel.fu_rng4; lia | lia].
    * apply (mod_atom _ 48 _ 8 B48); [apply GateModel.fb_rng | lia].
    * apply (mod_atom _ 49 _ 64 B49); [apply GateModel.fu_rng8; lia | lia].
    * apply fld_le; lia.
    *  apply fld_le; lia.
    *  rewrite GateModel.fld1 by lia; apply le1_fb.
    *  apply fld_le; lia. }
  preg HS (2%bv : bv 5) Q2. preg HS (3%bv : bv 5) Q3. preg HS (4%bv : bv 5) Q4. preg HS (9%bv : bv 5) Q9.
  preg HS (10%bv : bv 5) Q10. preg HS (16%bv : bv 5) Q16. preg HS (18%bv : bv 5) Q18. preg HS (21%bv : bv 5) Q21.
  preg HS (22%bv : bv 5) Q22.
  pmkst HS.
  apply (fE2_ok i _ _ _ (G) Hi (proj2 HT1)).
  + rewrite (fE_model i Hgf Hed). replace (CtrlParsed.fu Sg 8 4 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hnz). reflexivity.
  + first [exact HJ | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ].
  + exact HK1. + exact HP1. + exact HT1. + exact HSV1. + exact HOW1.
  + unfold spZ at 1. rewrite Q2, den_atom0, B2. apply unsigned_lit_small. lia.
  + rewrite Q3, den_atom0. exact B3.
  + rewrite Q4, den_atom0. exact B4.
  + rewrite Q9, den_atom0. exact B9.
  + rewrite Q10, den_atom0. exact B10.
  + rewrite Q16, den_atom0. exact B16.
  + rewrite Q18, den_atom0. exact B18.
  + rewrite Q21, den_atom0. exact B21.
  + rewrite Q22, den_atom0. exact B22.

- rewrite (beq_s32 E 12 _ E12) in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hnz.
  runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA 0x4da0.
  kwU (g + 32 * Z.of_nat i) UA HFr K1.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mc) => rename mc into ms1 end.
  destruct (ent_keep m (ms_mem ms1) i Hi HK HP K1 HG) as [HK1 HP1].
  destruct (ent_sv m (ms_mem ms1) HSV HOW ltac:(intros a Ha Hs2; apply K1; lia)) as [HSV1 HOW1].
  clear HF HFr HG.
  u18 HS E18 UL (g + 32 * Z.of_nat i).
  tatom HS EQ46 B46. tatom HS EQ47 B47. tatom HS EQ48 B48. tatom HS EQ49 B49. tatom HS E12 B12.
  tatom HS E2 B2. tatom HS E3 B3. tatom HS E4 B4. tatom HS E9 B9. tatom HS E10 B10. tatom HS E16 B16.
  tatom HS E18 B18. tatom HS E21 B21. tatom HS E22 B22.
  rgn2 RA RB.
  assert (HT1 : tTB (ms_mem ms1) (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4))).
  { eapply (ent_leaf _ m (ms_mem ms1) G (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) i _ _ 8 17 24 32 (SOff 12 0) (SOff 47 0) (SOff 48 0) (SOff 49 0)
       (CtrlParsed.fu Sg 8 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16)) (CtrlParsed.fu G (32 * i + 24) 8) Hi HT).
    * rewrite GateModel.length_upd by lfs. exact HGl.
    * intros a Ha Ha1 Ha2. exact (K1 a Ha Ha1 Ha2).
    * intros j Hj Hj1 Hj2. apply nth_upd_out; lfs.
    * exact RA.
    * exact RB.
    * exact UL.
    * inch. * inch. * inch. * inch.
    * apply (s32_atom_mod _ 12 _ B12); lia.
    * apply (mod_atom _ 47 _ 32 B47); [apply GateModel.fu_rng4; lia | lia].
    * apply (mod_atom _ 48 _ 8 B48); [apply GateModel.fb_rng | lia].
    * apply (mod_atom _ 49 _ 64 B49); [apply GateModel.fu_rng8; lia | lia].
    * rewrite fld_upd_same'; [apply fld_le; lia | apply GateModel.length_fld; lia | lfs].
    * rewrite GateModel.fld_upd_other by lfs; apply fld_le; lia.
    * rewrite GateModel.fld_upd_other by lfs; rewrite GateModel.fld1 by lia; apply le1_fb.
    * rewrite GateModel.fld_upd_other by lfs; apply fld_le; lia. }
  preg HS (2%bv : bv 5) Q2. preg HS (3%bv : bv 5) Q3. preg HS (4%bv : bv 5) Q4. preg HS (9%bv : bv 5) Q9.
  preg HS (10%bv : bv 5) Q10. preg HS (16%bv : bv 5) Q16. preg HS (18%bv : bv 5) Q18. preg HS (21%bv : bv 5) Q21.
  preg HS (22%bv : bv 5) Q22.
  pmkst HS.
  apply (fE2_ok i _ _ _ (Mem.upd_bytes G (32 * i + 8) (CtrlParsed.fld Sg 8 4)) Hi (proj2 HT1)).
  + rewrite (fE_model i Hgf Hed). replace (CtrlParsed.fu Sg 8 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). reflexivity.
  + first [exact HJ | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ].
  + exact HK1. + exact HP1. + exact HT1. + exact HSV1. + exact HOW1.
  + unfold spZ at 1. rewrite Q2, den_atom0, B2. apply unsigned_lit_small. lia.
  + rewrite Q3, den_atom0. exact B3.
  + rewrite Q4, den_atom0. exact B4.
  + rewrite Q9, den_atom0. exact B9.
  + rewrite Q10, den_atom0. exact B10.
  + rewrite Q16, den_atom0. exact B16.
  + rewrite Q18, den_atom0. exact B18.
  + rewrite Q21, den_atom0. exact B21.
  + rewrite Q22, den_atom0. exact B22.

Qed.
Lemma gsp_s32_rng : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= CtrlParsed.s32 v < 2 ^ 31.
Proof. intros v Hv. unfold CtrlParsed.s32. destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia. Qed.
Lemma gsp_beq_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. apply GateModel.eqb_lit; assumption. Qed.
Lemma gsp_bne_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite GateModel.eqb_lit by assumption. reflexivity. Qed.
Lemma beq_sx : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hv. rewrite (den_sext32 E n v H Hv). change (sv_denot E (SLit 0)) with (Z_to_bv 64 0).
pose proof (gsp_s32_rng v Hv) as Hr. rewrite gsp_beq_lit by lia. clear Hr.
unfold CtrlParsed.s32. destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota;
apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; lia.
Qed.
Lemma bne_sx : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> 0 <= v1 < 2 ^ 32 -> ew E n2 = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 32 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n1 0))) (sv_denot E (SExt true 32 (SOff n2 0))) = negb (v1 =? v2).
Proof.
intros E n1 n2 v1 v2 H1 Hv1 H2 Hv2. rewrite (den_sext32 E n1 v1 H1 Hv1), (den_sext32 E n2 v2 H2 Hv2).
pose proof (gsp_s32_rng v1 Hv1). pose proof (gsp_s32_rng v2 Hv2).
rewrite gsp_bne_lit by lia. rewrite (GateModel.s32_inj v1 v2 Hv1 Hv2). reflexivity.
Qed.
Lemma bne_dk : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> - 2 ^ 63 <= v1 < 2 ^ 63 -> ew E n2 = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 32 ->
  branch_taken BC_NE (sv_denot E (SOff n1 0)) (sv_denot E (SExt true 32 (SOff n2 0))) = negb (v1 =? CtrlParsed.s32 v2).
Proof.
intros E n1 n2 v1 v2 H1 Hv1 H2 Hv2. rewrite den_atom0, H1, (den_sext32 E n2 v2 H2 Hv2).
pose proof (gsp_s32_rng v2 Hv2). apply gsp_bne_lit; lia.
Qed.
Lemma ged_ss : forall i, CtrlParsed.fu Sg 8 4 <> 0 -> CtrlParsed.fu Sg 8 4 <> CtrlParsed.fu G (32 * i + 8) 4 ->
  GateModel.gedge G Sg i = true.
Proof.
intros i H1 H2. unfold GateModel.gedge. apply orb_true_iff. left. apply orb_true_iff. left.
apply andb_true_iff. split; apply negb_true_iff, Z.eqb_neq; assumption.
Qed.
Lemma ged_dk : forall i, 0 <= gdk Sg -> gdk Sg <> CtrlParsed.s32 (CtrlParsed.fu G (32 * i + 12) 4) ->
  GateModel.gedge G Sg i = true.
Proof.
intros i H1 H2. unfold gdk in H1, H2. unfold GateModel.gedge. apply orb_true_iff. left. apply orb_true_iff. right.
apply andb_true_iff. split; [apply Z.leb_le; exact H1 | apply negb_true_iff, Z.eqb_neq; exact H2].
Qed.
Lemma ged_fl : forall i, CtrlParsed.fb Sg 16 <> 0 -> CtrlParsed.fb Sg 16 <> CtrlParsed.fb G (32 * i + 16) ->
  GateModel.gedge G Sg i = true.
Proof.
intros i H1 H2. unfold GateModel.gedge. apply orb_true_iff. right.
apply andb_true_iff. split; apply negb_true_iff, Z.eqb_neq; assumption.
Qed.
Lemma ged_no : forall i,
  (CtrlParsed.fu Sg 8 4 = 0 \/ CtrlParsed.fu Sg 8 4 = CtrlParsed.fu G (32 * i + 8) 4) ->
  (gdk Sg < 0 \/ gdk Sg = CtrlParsed.s32 (CtrlParsed.fu G (32 * i + 12) 4)) ->
  (CtrlParsed.fb Sg 16 = 0 \/ CtrlParsed.fb Sg 16 = CtrlParsed.fb G (32 * i + 16)) ->
  GateModel.gedge G Sg i = false.
Proof.
intros i H1 H2 H3. unfold gdk in H2. unfold GateModel.gedge.
apply orb_false_iff. split; [apply orb_false_iff; split|]; apply andb_false_iff.
- destruct H1 as [H1|H1]; [left | right]; apply negb_false_iff, Z.eqb_eq; exact H1.
- destruct H2 as [H2|H2]; [left; apply Z.leb_gt; exact H2 | right; apply negb_false_iff, Z.eqb_eq; exact H2].
- destruct H3 as [H3|H3]; [left | right]; apply negb_false_iff, Z.eqb_eq; exact H3.
Qed.
Lemma ent_G : forall E m m' (i : nat), (i < 8)%nat -> tTB m G ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g + 32 * Z.of_nat i + 8 <= a < g + 32 * Z.of_nat i + 17) ->
     ~ (g + 32 * Z.of_nat i + 24 <= a < g + 32 * Z.of_nat i + 32) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  region_ok SEGS E (mrestrict (w_H W) m') rF_a -> region_ok SEGS E (mrestrict (w_H W) m') rF_b ->
  bv_unsigned (ew E 18) = g + 32 * Z.of_nat i ->
  ew E 46 = Z_to_bv 64 (CtrlParsed.fu G (32 * i + 8) 4) -> ew E 47 = Z_to_bv 64 (CtrlParsed.fu G (32 * i + 12) 4) ->
  ew E 48 = Z_to_bv 64 (CtrlParsed.fb G (32 * i + 16)) -> ew E 49 = Z_to_bv 64 (CtrlParsed.fu G (32 * i + 24) 8) ->
  tTB m' G.
Proof.
intros E m m' i Hi HT HM RA RB UL EQ46 EQ47 EQ48 EQ49.
eapply (ent_leaf E m m' G G i _ _ 8 17 24 32 (SOff 46 0) (SOff 47 0) (SOff 48 0) (SOff 49 0)
          (CtrlParsed.fu G (32 * i + 8) 4) (CtrlParsed.fu G (32 * i + 12) 4) (CtrlParsed.fb G (32 * i + 16))
          (CtrlParsed.fu G (32 * i + 24) 8) Hi HT).
- exact HGl.
- exact HM.
- intros j Hj H1 H2. reflexivity.
- exact RA.
- exact RB.
- exact UL.
- inch. - inch. - inch. - inch.
- apply (mod_atom E 46 _ 32 EQ46); [apply GateModel.fu_rng4; lia | lia].
- apply (mod_atom E 47 _ 32 EQ47); [apply GateModel.fu_rng4; lia | lia].
- apply (mod_atom E 48 _ 8 EQ48); [apply GateModel.fb_rng | lia].
- apply (mod_atom E 49 _ 64 EQ49); [apply GateModel.fu_rng8; lia | lia].
- apply fld_le; lia.
- apply fld_le; lia.
- rewrite GateModel.fld1 by lia. apply le1_fb.
- apply fld_le; lia.
Qed.
Ltac fpre :=
  pose proof (proj1 (proj2 HGok)) as Hn;
  pose proof stk_lo as [Hlo Hhi]; pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  pose proof Hgam as Hg'; pose proof Hsam as Hs'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hg', Hs';
  pose proof Hgside as Hgs'; unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK in Hgs', Hlo.
Ltac fenv regs' i Hsp R9 R18 R22 :=
  let Q46 := fresh "EQ46" in ekv regs' G i 46%nat Q46; let Q47 := fresh "EQ47" in ekv regs' G i 47%nat Q47;
  let Q48 := fresh "EQ48" in ekv regs' G i 48%nat Q48; let Q49 := fresh "EQ49" in ekv regs' G i 49%nat Q49;
  let Q50 := fresh "EQ50" in ekv regs' G i 50%nat Q50; let Q51 := fresh "EQ51" in ekv regs' G i 51%nat Q51;
  assert (E2 : ew (EK regs' G i) 2 = Z_to_bv 64 (spZ regs - 112))
    by (rewrite (ek_reg regs' G i 2%bv 2 eq_refl), <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned);
  assert (E9 : ew (EK regs' G i) 9 = Z_to_bv 64 s) by (rewrite (ek_reg regs' G i 9%bv 9 eq_refl); exact R9);
  assert (E18 : ew (EK regs' G i) 18 = Z_to_bv 64 (g + 32 * Z.of_nat i))
    by (rewrite (ek_reg regs' G i 18%bv 18 eq_refl); exact R18);
  assert (E22 : ew (EK regs' G i) 22 = Z_to_bv 64 (gdk Sg)) by (rewrite (ek_reg regs' G i 22%bv 22 eq_refl); exact R22);
  assert (E32 : ew (EK regs' G i) 32 = Z_to_bv 64 now)
    by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0));
  let HE := fresh "HE" in
  remember (EK regs' G i) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
  assert (HAE : env_agree 32 (Ereg regs' (xK G i)) E)
    by (subst E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  clear HE.
Ltac ftrall :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  repeat match goal with H : ew ?E0 ?n = ?v |- _ =>
    tryif first [constr_eq E0 Ex | constr_eq n 18%nat] then fail else
    (let H' := fresh in
     assert (H' : ew Ex n = v) by (rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact H);
     clear H; rename H' into H)
  end end.
Ltac fag HAE :=
  lazymatch goal with
  | |- env_agree 32 ?E1 (ewset ?Ey ?n ?v) =>
      apply (YP03.env_agree_trans 32 E1 Ey (ewset Ey n v));
      [fag HAE | apply (YP03.env_agree_le 32 n Ey (ewset Ey n v)); [lia | apply YP03.env_agree_ewset]]
  | |- env_agree 32 ?E1 (havoc ?Ey ?k ?ws) => apply (YI04.env_agree_havoc_ge 32 k E1 Ey ws); [lia | fag HAE]
  | |- _ => exact HAE
  end.
Ltac fstep i E18 U K msn HKo HPo HSVo HOWo HTo HKn HPn HSVn HOWn HTn :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HF : frame_of _ _ _ _, HG : mem_grows (mrestrict _ ?mo) _ |- _ =>
  kwU (g + 32 * Z.of_nat i) U HFr K;
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?mc) |- _ => rename mc into msn end;
  ftrall;
  destruct (ent_keep mo (ms_mem msn) i ltac:(lia) HKo HPo K HG) as [HKn HPn];
  destruct (ent_sv mo (ms_mem msn) HSVo HOWo ltac:(let a_ := fresh "a" in let Ha_ := fresh "Ha" in let Hs_ := fresh "Hs" in
    intros a_ Ha_ Hs_; apply K; lia)) as [HSVn HOWn];
  let UL := fresh "UL" in let RA := fresh "RA" in let RB := fresh "RB" in
  lazymatch goal with HS : st_ok_pi _ _ ?E0 _ _ |- _ =>
    u18 HS E18 UL (g + 32 * Z.of_nat i); rgn2 RA RB;
    pose proof (ent_G E0 mo (ms_mem msn) i ltac:(lia) HTo K RA RB UL
      ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as HTn;
    clear UL RA RB end;
  clear HF HFr HG end.
Ltac fexit regs' i HAE HKR rl :=
  lazymatch goal with HS : st_ok_pi _ _ ?E0 ?ssx (restrict _ ?mc) |- _ =>
    pose proof (regs_kept_of_st_ok_pi E0 ssx (restrict (w_H W) mc) regs' (xK G i) rl HS ltac:(fag HAE)
      ltac:(vm_compute; reflexivity)) as HKR;
    cbn [ms_regs restrict] in HKR end.
Ltac fkr HKR H := rewrite HKR by (cbv; tauto); exact H.

Definition fF_stmt : Prop := forall (i : nat) regs' m md,
  (i < Z.to_nat (disco_classify_c.gn G))%nat ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  (CtrlParsed.fu Sg 8 4 = 0 \/ CtrlParsed.fu Sg 8 4 = CtrlParsed.fu G (32 * i + 8) 4) ->
  (gdk Sg < 0 \/ gdk Sg = CtrlParsed.s32 (CtrlParsed.fu G (32 * i + 12) 4)) ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 10 = w64 (s + 16) ->
  getr regs' 12 = Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) -> getr regs' 16 = w64 now ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB -> getr regs' 22 = w64 (gdk Sg) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4d18)) m (seg_rom SEGS)) md) tQ.
Lemma fF_ok : fF_stmt.
Proof.
intros i regs' m md Hi Hgf HD1 HD2 HJ HK HP HT HSV HOW Hsp R3 R4 R9 R10 R12 R16 R18 R21 R22.
fpre. assert (Hi8 : (i < 8)%nat) by lia.
destruct (kst_G 0x4d18 [(10%bv, SOff 9 16)] regs' m G i
  ltac:(cbn [map fst]; apply NoDup_cons_2; [intros H; inversion H | apply NoDup_nil_2])
  ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split; [vm_compute; reflexivity |
          rewrite R10; symmetry; apply (den_off (EK regs' G i) 9 16 s);
          [rewrite (ek_reg regs' G i 9%bv 9 eq_refl); exact R9 | lia | lia] ])
  HSV HOW HK HP HT Hi8 Hsp R9 R18 R21) as [HS SHOK].
fenv regs' i Hsp R9 R18 R22.
pose proof (GateModel.fb_rng Sg 16) as R51. pose proof (GateModel.fb_rng G (32 * i + 16)) as R48.
runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA.
fstep i E18 UA K1 ms1 HK HP HSV HOW HT HK1 HP1 HSV1 HOW1 HT1.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (beq0_atom _ 51 _ EQ51) in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hf.
  runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB 0x4d4c.
  fstep i E18 UB K2 ms2 HK1 HP1 HSV1 HOW1 HT1 HK2 HP2 HSV2 HOW2 HT2.
  fexit regs' i HAE HKR ([2; 3; 4; 9; 16; 18; 21]%bv : list (bv 5)).
  pmkst HS.
  apply (fT_ok i _ _ _ Hi Hgf (ged_no i HD1 HD2 (or_introl Hf)) HJ HK2 HP2 HT2 HSV2 HOW2).
  + unfold spZ. fkr HKR Hsp.
  + fkr HKR R3. + fkr HKR R4. + fkr HKR R9. + fkr HKR R16.
  + fkr HKR R18. + fkr HKR R21.
- rewrite (beq0_atom _ 51 _ EQ51) in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hf.
  runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB.
  fstep i E18 UB K2 ms2 HK1 HP1 HSV1 HOW1 HT1 HK2 HP2 HSV2 HOW2 HT2.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (bne_off _ 51 48 _ _ 0 EQ51 EQ48) in Hc by lia. rewrite Z.add_0_r in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC 0x4d84.
    fstep i E18 UC K3 ms3 HK2 HP2 HSV2 HOW2 HT2 HK3 HP3 HSV3 HOW3 HT3.
    fexit regs' i HAE HKR ([2; 3; 4; 9; 12; 16; 18; 21; 22]%bv : list (bv 5)).
    preg HS (10%bv : bv 5) Q10.
    pmkst HS.
    apply (fE1_ok i _ _ _ Hi8 Hgf (ged_fl i Hf Hc) HJ HK3 HP3 HT3 HSV3 HOW3).
    * unfold spZ. fkr HKR Hsp.
    * fkr HKR R3. * fkr HKR R4. * fkr HKR R9.
    * rewrite Q10. apply (den_off _ 9 16 s E9); lia.
    * fkr HKR R12. * fkr HKR R16. * fkr HKR R18. * fkr HKR R21. * fkr HKR R22.
  + rewrite (bne_off _ 51 48 _ _ 0 EQ51 EQ48) in Hc by lia. rewrite Z.add_0_r in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC 0x4d4c.
    fstep i E18 UC K3 ms3 HK2 HP2 HSV2 HOW2 HT2 HK3 HP3 HSV3 HOW3 HT3.
    fexit regs' i HAE HKR ([2; 3; 4; 9; 16; 18; 21]%bv : list (bv 5)).
    pmkst HS.
    apply (fT_ok i _ _ _ Hi Hgf (ged_no i HD1 HD2 (or_intror Hc)) HJ HK3 HP3 HT3 HSV3 HOW3).
    * unfold spZ. fkr HKR Hsp.
    * fkr HKR R3. * fkr HKR R4. * fkr HKR R9. * fkr HKR R16.
    * fkr HKR R18. * fkr HKR R21.
Qed.

Definition fD_stmt : Prop := forall (i : nat) regs' m md,
  (i < Z.to_nat (disco_classify_c.gn G))%nat ->
  GateModel.gfind G (CtrlParsed.fld Sg 0 6) 0 (Z.to_nat (disco_classify_c.gn G)) = Some i ->
  (CtrlParsed.fu Sg 8 4 = 0 \/ CtrlParsed.fu Sg 8 4 = CtrlParsed.fu G (32 * i + 8) 4) ->
  tJ m md -> tKP m -> tPR m -> tTB m G -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 9 = w64 s -> getr regs' 10 = w64 (s + 16) ->
  getr regs' 12 = Z_to_bv 64 (CtrlParsed.s32 (CtrlParsed.fu Sg 8 4)) -> getr regs' 16 = w64 now ->
  getr regs' 18 = w64 (g + 32 * Z.of_nat i) -> getr regs' 21 = w64 GSB -> getr regs' 22 = w64 (gdk Sg) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x4cf8)) m (seg_rom SEGS)) md) tQ.
Lemma fD_ok : fD_stmt.
Proof.
intros i regs' m md Hi Hgf HD1 HJ HK HP HT HSV HOW Hsp R3 R4 R9 R10 R12 R16 R18 R21 R22.
fpre. assert (Hi8 : (i < 8)%nat) by lia.
destruct (kst_G 0x4cf8 [] regs' m G i NoDup_nil_2 (Forall_nil _) HSV HOW HK HP HT Hi8 Hsp R9 R18 R21) as [HS SHOK].
fenv regs' i Hsp R9 R18 R22.
assert (Rdk : -1 <= gdk Sg < 65536) by (unfold gdk; apply GateModel.gdk_rng).
pose proof (GateModel.fu_rng4 G (32 * i + 12) ltac:(lia)) as R47.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (blt0_atom _ 22 _ E22) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hdk.
  runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA 0x4d18.
  fstep i E18 UA K1 ms1 HK HP HSV HOW HT HK1 HP1 HSV1 HOW1 HT1.
  fexit regs' i HAE HKR ([2; 3; 4; 9; 10; 12; 16; 18; 21; 22]%bv : list (bv 5)).
  pmkst HS.
  apply (fF_ok i _ _ _ Hi Hgf HD1 (or_introl Hdk) HJ HK1 HP1 HT1 HSV1 HOW1).
  + unfold spZ. fkr HKR Hsp.
  + fkr HKR R3. + fkr HKR R4. + fkr HKR R9. + fkr HKR R10.
  + fkr HKR R12. + fkr HKR R16. + fkr HKR R18. + fkr HKR R21. + fkr HKR R22.
- rewrite (blt0_atom _ 22 _ E22) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hdk.
  runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA.
  fstep i E18 UA K1 ms1 HK HP HSV HOW HT HK1 HP1 HSV1 HOW1 HT1.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (bne_dk _ 22 47 _ _ E22 ltac:(lia) EQ47 R47) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB 0x4d84.
    fstep i E18 UB K2 ms2 HK1 HP1 HSV1 HOW1 HT1 HK2 HP2 HSV2 HOW2 HT2.
    fexit regs' i HAE HKR ([2; 3; 4; 9; 10; 12; 16; 18; 21; 22]%bv : list (bv 5)).
    pmkst HS.
    apply (fE1_ok i _ _ _ Hi8 Hgf (ged_dk i Hdk Hc) HJ HK2 HP2 HT2 HSV2 HOW2).
    * unfold spZ. fkr HKR Hsp.
    * fkr HKR R3. * fkr HKR R4. * fkr HKR R9. * fkr HKR R10.
    * fkr HKR R12. * fkr HKR R16. * fkr HKR R18. * fkr HKR R21. * fkr HKR R22.
  + rewrite (bne_dk _ 22 47 _ _ E22 ltac:(lia) EQ47 R47) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB 0x4d18.
    fstep i E18 UB K2 ms2 HK1 HP1 HSV1 HOW1 HT1 HK2 HP2 HSV2 HOW2 HT2.
    fexit regs' i HAE HKR ([2; 3; 4; 9; 10; 12; 16; 18; 21; 22]%bv : list (bv 5)).
    pmkst HS.
    apply (fF_ok i _ _ _ Hi Hgf HD1 (or_intror Hc) HJ HK2 HP2 HT2 HSV2 HOW2).
    * unfold spZ. fkr HKR Hsp.
    * fkr HKR R3. * fkr HKR R4. * fkr HKR R9. * fkr HKR R10.
    * fkr HKR R12. * fkr HKR R16. * fkr HKR R18. * fkr HKR R21. * fkr HKR R22.
Qed.

Lemma found_ok : found_stmt.
Proof.
intros i regs' m md Hi Hgf HJ HK HP HT HSV HOW Hsp R3 R4 R9 R18 R21 R22.
fpre. assert (Hi8 : (i < 8)%nat) by lia.
destruct (kst_G 0x4cb8 [] regs' m G i NoDup_nil_2 (Forall_nil _) HSV HOW HK HP HT Hi8 Hsp R9 R18 R21) as [HS SHOK].
fenv regs' i Hsp R9 R18 R22.
pose proof (GateModel.fu_rng4 Sg 8 ltac:(lia)) as R50. pose proof (GateModel.fu_rng4 G (32 * i + 8) ltac:(lia)) as R46.
runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UA.
fstep i E18 UA K1 ms1 HK HP HSV HOW HT HK1 HP1 HSV1 HOW1 HT1.
psrr_branch_tok RUN BR HS SHOK GBspan.
- rewrite (beq_sx _ 50 _ EQ50 R50) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hz.
  runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB 0x4cf8.
  fstep i E18 UB K2 ms2 HK1 HP1 HSV1 HOW1 HT1 HK2 HP2 HSV2 HOW2 HT2.
  fexit regs' i HAE HKR ([2; 3; 4; 9; 18; 21; 22]%bv : list (bv 5)).
  preg HS (10%bv : bv 5) Q10. preg HS (12%bv : bv 5) Q12. preg HS (16%bv : bv 5) Q16.
  pmkst HS.
  apply (fD_ok i _ _ _ Hi Hgf (or_introl Hz) HJ HK2 HP2 HT2 HSV2 HOW2).
  + unfold spZ. fkr HKR Hsp.
  + fkr HKR R3. + fkr HKR R4. + fkr HKR R9.
  + rewrite Q10. apply (den_off _ 9 16 s E9); lia.
  + rewrite Q12. exact (den_sext32 _ 50 _ EQ50 R50).
  + rewrite Q16, den_atom0. exact E32.
  + fkr HKR R18. + fkr HKR R21. + fkr HKR R22.
- rewrite (beq_sx _ 50 _ EQ50 R50) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hz.
  runEU HS HJ SHOK E18 (g + 32 * Z.of_nat i) UB.
  fstep i E18 UB K2 ms2 HK1 HP1 HSV1 HOW1 HT1 HK2 HP2 HSV2 HOW2 HT2.
  psrr_branch_tok RUN BR HS SHOK GBspan.
  + rewrite (bne_sx _ 50 46 _ _ EQ50 R50 EQ46 R46) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC 0x4d88.
    fstep i E18 UC K3 ms3 HK2 HP2 HSV2 HOW2 HT2 HK3 HP3 HSV3 HOW3 HT3.
    fexit regs' i HAE HKR ([2; 3; 4; 9; 18; 21; 22]%bv : list (bv 5)).
    preg HS (10%bv : bv 5) Q10. preg HS (12%bv : bv 5) Q12. preg HS (16%bv : bv 5) Q16.
    pmkst HS.
    apply (fE1b_ok i _ _ _ Hi8 Hgf (ged_ss i Hz Hc) Hz HJ HK3 HP3 HT3 HSV3 HOW3).
    * unfold spZ. fkr HKR Hsp.
    * fkr HKR R3. * fkr HKR R4. * fkr HKR R9.
    * rewrite Q10. apply (den_off _ 9 16 s E9); lia.
    * rewrite Q12. exact (den_sext32 _ 50 _ EQ50 R50).
    * rewrite Q16, den_atom0. exact E32.
    * fkr HKR R18. * fkr HKR R21. * fkr HKR R22.
  + rewrite (bne_sx _ 50 46 _ _ EQ50 R50 EQ46 R46) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    runEUto HS HJ SHOK E18 (g + 32 * Z.of_nat i) UC 0x4cf8.
    fstep i E18 UC K3 ms3 HK2 HP2 HSV2 HOW2 HT2 HK3 HP3 HSV3 HOW3 HT3.
    fexit regs' i HAE HKR ([2; 3; 4; 9; 18; 21; 22]%bv : list (bv 5)).
    preg HS (10%bv : bv 5) Q10. preg HS (12%bv : bv 5) Q12. preg HS (16%bv : bv 5) Q16.
    pmkst HS.
    apply (fD_ok i _ _ _ Hi Hgf (or_intror Hc) HJ HK3 HP3 HT3 HSV3 HOW3).
    * unfold spZ. fkr HKR Hsp.
    * fkr HKR R3. * fkr HKR R4. * fkr HKR R9.
    * rewrite Q10. apply (den_off _ 9 16 s E9); lia.
    * rewrite Q12. exact (den_sext32 _ 50 _ EQ50 R50).
    * rewrite Q16, den_atom0. exact E32.
    * fkr HKR R18. * fkr HKR R21. * fkr HKR R22.
Qed.
End w.

Theorem pb_reac_disco_gate_should_push : treac_disco_gate_should_push_spec.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg
  HJc Hra Hra4 Hgp Htp H10 H11 H12 Rnow Hal Hwin Hspl Hg0 Hg8 Hg63 Hgside Hgw Hgam Hgra Hgsh HGl HGa HGok
  Hs0 Hs4 Hs63 Hsside Hsam Hsra Hssh HSl HSa Hgs.
apply (main_ok (fx := fq) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs g s now G Sg
  HJc Hgp Htp H10 H11 H12 Rnow Hal Hwin Hspl Hg0 Hg8 Hg63 Hgside Hgw Hgam Hgra Hgsh HGl HGa HGok
  Hs0 Hs4 Hs63 Hsside Hsam Hsra Hssh HSl HSa Hgs).
- eapply found_ok; eassumption.
- eapply after_ok; eassumption.
Qed.

End h.
End f.
End d.
