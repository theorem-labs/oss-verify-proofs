(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC85 YC44 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import jtok_is_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section s. Context {fx : YK11.FPState}.
Lemma aj_strlen_at : forall B, AR_laws SEGS B -> (forall a, in_img SEGS a -> 0 <= a < kLowMemEnd) ->
forall lo hi pc, astrlen_realizesM SEGS B lo hi pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= kk -> kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte SEGS W memT x (kk + 1) 0 kk ->
src_ok SEGS W regsT memT x (kk + 1) -> amem_range x (kk + 1) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (kk + 1) ->
shadow_hull_vis (aview SEGS (w_H W) memT) x (kk + 1) ->
(forall a, x + kk < a < x + kk - (x + kk) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
consts_view SEGS lo hi W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 kk /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS Hsegs lo hi pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x kk o raw
HJ Ha0 Hx0 Hk0 Hk32 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hmx Hrx Hhx Hsl Hrom.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x kk HPRE Ha0 Hx0 Hk0 Hk32 Hxk Hfb Hsx Hmx Hrx Hhx Hsl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; lia.
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End s.
Lemma jt_regupd8 : forall (regs : bvmap 5 word) z,
getr (regupd regs 8 z) 1 = getr regs 1 /\ getr (regupd regs 8 z) 2 = getr regs 2 /\
getr (regupd regs 8 z) 3 = getr regs 3 /\ getr (regupd regs 8 z) 4 = getr regs 4.
Proof. intros regs z. repeat split; apply getr_other; reg_neq_tac. Qed.
Lemma jt_frame_kept : forall E rs H (m m' : word -> option byte) lo hi,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hw a Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hx. exact (Hn (Hw a Hx)).
Qed.
Lemma jt_garr8_aview : forall H m p L j, garr8 SEGS (mrestrict H m) p L -> (j < length L)%nat ->
aview SEGS H m (p + Z.of_nat j) = Some (nth j L 0).
Proof. intros H m p L j HG Hj. destruct (HG j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H m _ _ Hv Hr). Qed.
Lemma jt_nth_T : forall (T slack : list byte) j, (j < length T)%nat ->
nth j (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) 0 = bv_unsigned (nth j T (Z_to_bv 8 0)).
Proof.
intros T slack j Hj. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite map_nth, app_nth1 by exact Hj. reflexivity.
Qed.
Lemma jt_nth_nul : forall (T slack : list byte), nth (length T) (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) 0 = 0.
Proof.
intros T slack. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite map_nth, app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma jt_first_byte : forall (W : world SEGS) m x (T slack : list byte),
~ In (Z_to_bv 8 0) T ->
garr8 SEGS (mrestrict (w_H W) m) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
first_byte SEGS W m x (Z.of_nat (length T) + 1) 0 (Z.of_nat (length T)).
Proof.
intros W m x T slack HT HG. split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) T (Z_to_bv 8 0))). split.
+ replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
rewrite (jt_garr8_aview _ _ _ _ _ HG) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite jt_nth_T by lia. reflexivity.
+ intros H0. apply HT. replace (Z_to_bv 8 0) with (nth (Z.to_nat i) T (Z_to_bv 8 0)) by (apply bv_eq; rewrite H0; reflexivity).
apply nth_In. lia.
- intros _. rewrite (jt_garr8_aview _ _ _ _ _ HG) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite jt_nth_nul. reflexivity.
Qed.
Lemma jt_slack : forall (W : world SEGS) m x (T slack : list byte),
garr8 SEGS (mrestrict (w_H W) m) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
(- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
forall a, x + Z.of_nat (length T) < a < x + Z.of_nat (length T) - (x + Z.of_nat (length T)) mod 8 + 8 ->
aview SEGS (w_H W) m a <> None.
Proof.
intros W m x T slack HG Hsl a Ha.
pose proof (Z.div_mod (x + Z.of_nat (length T)) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + Z.of_nat (length T)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (- (x + Z.of_nat (length T) + 1)) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (- (x + Z.of_nat (length T) + 1)) 8 ltac:(lia)) as M2.
replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
rewrite (jt_garr8_aview _ _ _ _ _ HG); [discriminate|]. rewrite length_map, length_app. cbn [length]. lia.
Qed.
Lemma jt_garr8_present : forall (W : world SEGS) m p L a, garr8 SEGS (mrestrict (w_H W) m) p L ->
p <= a < p + Z.of_nat (length L) -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m p L a HG Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (jt_garr8_aview _ _ _ _ _ HG); [discriminate|]. lia.
Qed.
Lemma jt_hull_sub : forall rd a n m, shadow_hull_vis rd a n -> 0 < m <= n -> shadow_hull_vis rd a m.
Proof.
intros rd a n m H Hm s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono (a + m - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (a + m - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma jt_amem_sub : forall p n m, amem_range p n -> 0 <= m <= n -> amem_range p m.
Proof. intros p n m H Hm. unfold amem_range in *. lia. Qed.
Lemma jt_ext32_mod : forall z, bv_extract 0 32 (Z_to_bv 64 (z mod 2 ^ 32)) = bv_extract 0 32 (Z_to_bv 64 z).
Proof.
intros z. apply bv_eq. rewrite !bv_extract_unsigned, !Z_to_bv_unsigned. cbn [Z.of_N]. rewrite !Z.shiftr_0_r. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (z mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound z (2 ^ 32)); lia).
rewrite Z.mod_mod by lia. rewrite (Z.mod_mod_divide z (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity). reflexivity.
Qed.
Lemma jt_br1 : forall E vk kind b, ew E 34 = Z_to_bv 64 (vk mod 2 ^ 32) -> ew E 11 = Z_to_bv 64 kind ->
-2 ^ 31 <= vk < 2 ^ 31 -> -2 ^ 31 <= kind < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 34 0))) (sv_denot E (SOff 11 0)) = b -> b = negb (vk =? kind).
Proof.
intros E vk kind b H34 H11 Hvk Hk Hb. subst b. cbn [sv_denot]. rewrite H34, H11, !Z.add_0_r, !Z_to_bv_bv_unsigned.
rewrite jt_ext32_mod, sext32_small by lia. cbn [branch_taken]. rewrite bv_eqb_small by lia. reflexivity.
Qed.
Lemma jt_nth_map : forall (L : list byte) j, (j < length L)%nat -> nth j (map bv_unsigned L) 0 = bv_unsigned (nth j L (Z_to_bv 8 0)).
Proof. intros L j Hj. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth. reflexivity. Qed.
Lemma jt_eq_bytes : forall H m p q (P T slack : list byte), length P = length T ->
garr8 SEGS (mrestrict H m) p (map bv_unsigned P) ->
garr8 SEGS (mrestrict H m) q (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
(P = T <-> forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS H m (p + i) = aview SEGS H m (q + i)).
Proof.
intros H m p q P T slack HL GP GQ. split.
- intros -> i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (jt_garr8_aview _ _ _ _ _ GP) by (rewrite length_map; lia).
rewrite (jt_garr8_aview _ _ _ _ _ GQ) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite jt_nth_T, jt_nth_map by lia. reflexivity.
- intros Heq. apply (nth_ext P T (Z_to_bv 8 0) (Z_to_bv 8 0) HL). intros j Hj.
specialize (Heq (Z.of_nat j) ltac:(lia)).
rewrite (jt_garr8_aview _ _ _ _ _ GP) in Heq by (rewrite length_map; lia).
rewrite (jt_garr8_aview _ _ _ _ _ GQ) in Heq by (rewrite length_map, length_app; cbn [length]; lia).
rewrite jt_nth_T, jt_nth_map in Heq by lia. injection Heq as Heq. apply bv_eq. exact Heq.
Qed.
Lemma jt_seqz : forall w : word, alu64 ALU_SLTU w (Z_to_bv 64 1) = if bv_unsigned w =? 0 then Z_to_bv 64 1 else Z_to_bv 64 0.
Proof.
intros w. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite (unsigned_lit_small 1) by lia.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
destruct (Z.eqb_spec (bv_unsigned w) 0) as [E0|E0].
- rewrite E0. rewrite unsigned_lit_small by lia. reflexivity.
- replace (bv_unsigned w <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Definition JSB : Z := 0x7fff8000.
Definition JBx : sv := SOff 35 0.
Definition JBspan : Z * Z := (JSB, JSB + 2 ^ 44 - 1).
Definition jt_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 35 ].
Definition jt_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 24) 3); (34%nat, mkAF 0 4294967295 0); (35%nat, mkAF JSB JSB 0) ] [] [].
Definition ss_jt : sstate := mkSS AF_both3_jtok_is sr_atoms jt_regions None jt_facts.
Definition jt_extra (vp vn vk : Z) : list word := map (Z_to_bv 64) [vp; vn; vk mod 2 ^ 32; JSB].
Definition jt_vregion : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 20 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 4 (SOff 34 0))].
Definition jt_SH : list shent := [mkSHE 10 0 20].
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Variables MC_CONSTS_LO MC_CONSTS_HI : Z.
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis MCROM : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom SEGS a.
Definition TJTOK_IS_STK : Z := 48 + 2 * ESTACK.
Definition tjtok_is_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (kind vk vn : Z) (P T : list byte)
  : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TJTOK_IS_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
       ((jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs' 10 = w64 1) \/
       (~ jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs' 10 = w64 0))).
Definition tjtok_is_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (v x kind vk vp vn : Z) (T slack P : list byte),
  afn_pre SEGS B TJTOK_IS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem ->
  getr regs 10 = w64 v -> getr regs 11 = Z_to_bv 64 kind -> getr regs 12 = w64 x ->
  -2 ^ 31 <= kind < 2 ^ 31 -> -2 ^ 31 <= vk < 2 ^ 31 ->
  0 < v -> v mod 8 = 0 -> v + 20 <= 2 ^ 63 ->
  val_mem SEGS (mrestrict (w_H W) mem) v 8 vp -> val_mem SEGS (mrestrict (w_H W) mem) (v + 8) 8 vn ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 16) 4 (vk mod 2 ^ 32) ->
  0 <= vp < 2 ^ 64 -> 0 <= vn < 2 ^ 64 ->
  amem_range v 20 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 20 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) v 20 ->
  (v + 20 <= spZ regs - TJTOK_IS_STK \/ spZ regs <= v) ->
  ~ In (Z_to_bv 8 0) T ->
  garr8 SEGS (mrestrict (w_H W) mem) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
  (- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < x -> x + Z.of_nat (length T + 1 + length slack) <= 2 ^ 63 ->
  Z.of_nat (length T) + 1 < 2 ^ 32 ->
  amem_range x (Z.of_nat (length T + 1)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x (Z.of_nat (length T + 1)) ->
  shadow_hull_vis (aview SEGS (w_H W) mem) x (Z.of_nat (length T + 1)) ->
  (x + Z.of_nat (length T + 1 + length slack) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= x) ->
  (vk = kind -> vn = Z.of_nat (length T) ->
     length P = length T /\ garr8 SEGS (mrestrict (w_H W) mem) vp (map bv_unsigned P) /\
     0 <= vp /\ vp + Z.of_nat (length T) <= 2 ^ 63 /\
     amem_range vp (Z.of_nat (length T)) /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF vp (Z.of_nat (length T)) /\
     (0 < Z.of_nat (length T) -> shadow_hull_vis (aview SEGS (w_H W) mem) vp (Z.of_nat (length T))) /\
     (vp + Z.of_nat (length T) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= vp)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_jtok_is) regs mem md) (tjtok_is_post fq regs ly S W mem md kind vk vn P T).
Section w. Context {fx : YK11.FPState}.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Lemma jt_entry : forall ly S W (regs : bvmap 5 word) mem md v vp vn vk,
AR SEGS B ly S W mem md -> astk_ok TJTOK_IS_STK ly (spZ regs) ->
(forall a, spZ regs - TJTOK_IS_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 v -> 0 < v -> v mod 8 = 0 -> amem_range v 20 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (jt_extra vp vn vk))) ss_jt
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_jtok_is)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md v vp vn vk HAR Hstk Hpres H10 Hv0 Hv8 Hvm.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : TJTOK_IS_STK = 8240) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
pose proof (Z.mod_pos_bound vk (2 ^ 32) ltac:(lia)) as Hvk32.
assert (Rv : 0 < v <= 2 ^ 47 - 24) by (revert Hv0 Hv8 Hvm C4 C5; clear; unfold amem_range; intros; pose proof (Z.div_mod v 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (jt_extra vp vn vk))).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E34 : ew E 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 JSB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v', ew E k = Z_to_bv 64 v' -> 0 <= v' < 2 ^ 64 -> base_val E (Some k) = v').
{ intros k v' Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
unfold ss_jt. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold jt_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 35 0) JSB);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold JSB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold jt_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 HSTK Hstk0 HgotR HcellR HgcD. clear. unfold off_img. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok jt_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E34, E35, !unsigned_lit_small by (unfold JSB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 C4 C5 HSTK Hstk0 Hal16 Hv0 Hv8 Rv Hvk32. clear. unfold JSB. intros.
pose proof (Z.div_mod v 8 ltac:(lia)).
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End w.
Theorem pb_jtok_is : tjtok_is_spec.
Proof.
unfold tjtok_is_spec.
intros fq ly S W regs mem md ch v x kind vk vp vn T slack P
HPRE HROD HROM H10 H11 H12 Rkind Rvk Hv0 Hv8 Hv63 Mvp Mvn Mvk Rvp Rvn Hvm Hvra Hvhv Hvw
HTnz GT Hsl Hx0 Hx63 HT32 Hxm Hxra Hxhv Hxw HP.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (paj_ret_at (PL := PL_both3_0) (PI := PI)) as RET.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (pal_got_shadow B TL) as HBgot. pose proof (pal_cell B TL) as HBcell.
destruct (jt_regupd8 regs (Z_to_bv 64 0)) as (U1 & U2 & U3 & U4).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite U2; reflexivity).
assert (Era : raZ (regupd regs 8 (Z_to_bv 64 0)) = raZ regs) by (unfold raZ; rewrite U1; reflexivity).
rewrite U1 in Hra. rewrite Era in Hra4. rewrite U3 in Hgp. rewrite U4 in Htp. rewrite Esp in Hstk, Hpres.
pose proof (ajournal_init SEGS B TJTOK_IS_STK [] ly S W _ mem md ch HPRE) as HJ.
rewrite Esp in HJ.
pose proof (jt_entry ly S W regs mem md v vp vn vk HAR Hstk Hpres H10 Hv0 Hv8 Hvm) as HS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : TJTOK_IS_STK = 8240) by reflexivity.
remember (Eimg (Ereg regs (jt_extra vp vn vk))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (jt_extra vp vn vk)) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 kind) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 x) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 vp) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 JSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (jt_extra vp vn vk)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
assert (SHOK : sh_ok SEGS JBx [] E (mrestrict (w_H W) mem)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_both3_jtok_is)) with (Z_to_bv 64 (BASE + AF_both3_jtok_is)).
paj_run_tok RUN HS HJ SHOK JBspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
assert (FK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ apply (jt_frame_kept E (ss_mem ss_jt) (w_H W) mem (ms_mem ms) (spZ regs - 48) (spZ regs) HFr).
intros a (r & Hin & Hr). unfold ss_jt, jt_regions, stack_region, got_regionP, bcell_regionP in Hin. cbn [ss_mem In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
assert (Hxk : 0 <= x /\ x + Z.of_nat (length T) + 1 + Z.of_nat (length slack) <= 2 ^ 63) by lia.
assert (HxA : x + Z.of_nat (length T) + 1 <= 2 ^ 47) by (revert Hxm C4 C5; clear; unfold amem_range; intros; lia).
assert (HxW : forall a, x <= a < x + Z.of_nat (length T) + 1 + Z.of_nat (length slack) -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs)) by lia.
assert (Hspl : alloc_ceiling <= spZ regs - TJTOK_IS_STK) by lia.
eapply SRr_bind.
{ eapply (aj_strlen_at (fx := fq) B LAWS Hsegs MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen) (ASTRLEN fq) W (ms_regs ms) (ms_mem ms)
TJTOK_IS_STK (spZ regs) [] ly S W mem md [] ly S _ 0 x (Z.of_nat (length T)) (-48) (Z_to_bv 64 (BASE + 11604)) HJ).
- rewrite Ra0, E12. reflexivity.
- exact Hx0.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite Rsp, Usp, unsigned_lit_small by lia. lia.
- reflexivity.
- lia.
- rewrite HSTK. unfold ESTACK. lia.
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- apply (jt_first_byte W (ms_mem ms) x T slack HTnz).
apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem ms) x _); [|exact GT].
intros a Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. apply FK1; [lia|]. specialize (HxW a ltac:(lia)). unfold ESTACK in *. lia.
- intros a Ha. split.
+ rewrite FK1 by (specialize (HxW a ltac:(lia)); lia). apply (jt_garr8_present W mem x _ a GT). rewrite length_map, length_app. cbn [length]. lia.
+ unfold spZ at 1 2. rewrite Rsp, Usp, unsigned_lit_small by lia. specialize (HxW a ltac:(lia)). unfold ESTACK. lia.
- replace (Z.of_nat (length T) + 1) with (Z.of_nat (length T + 1)) by lia. exact Hxm.
- apply (range_addressable_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - 48) (spZ regs)); [exact FK1 | lia | lia | lia |].
replace (Z.of_nat (length T) + 1) with (Z.of_nat (length T + 1)) by lia. exact Hxra.
- apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - 48) (spZ regs)); [exact FK1 | lia | lia | lia | lia |].
replace (Z.of_nat (length T) + 1) with (Z.of_nat (length T + 1)) by lia. exact Hxhv.
- intros a Ha. rewrite FK1.
+ exact (jt_slack W mem x T slack GT Hsl a Ha).
+ pose proof (Z.mod_pos_bound (x + Z.of_nat (length T)) 8 ltac:(lia)). lia.
+ pose proof (Z.mod_pos_bound (x + Z.of_nat (length T)) 8 ltac:(lia)).
pose proof (Z.div_mod (x + Z.of_nat (length T)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- (x + Z.of_nat (length T) + 1)) 8 ltac:(lia)).
pose proof (Z.div_mod (- (x + Z.of_nat (length T) + 1)) 8 ltac:(lia)). specialize (HxW a ltac:(lia)). lia.
- apply (consts_view_keep SEGS _ _ W mem (ms_mem ms) HROM). intros a Ha.
destruct (MCROM a Ha) as (sg & Hsg & _ & Hb). pose proof (Hsegs a (ex_intro _ sg (conj Hsg Hb))) as Ha'. apply FK1; lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hk2 & Hfr2 & Hpres2).
assert (FK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite Hfr2 by (unfold ESTACK; lia). apply FK1; lia. }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2' & _).
repeat apply Forall_cons; [| apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
+ apply (mbyte_of_aview SEGS). apply Hfr2; [lia | unfold ESTACK; lia].
+ intros _. apply (apresent_writable SEGS). apply Hpres2'. rewrite HSTK; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 36)%nat -> ew E5 k = ew E k) by (intros k Hk; rewrite HE5; apply ew_havoc_old; exact Hk).
assert (HAE5 : env_agree 32 (Ereg regs (jt_extra vp vn vk)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (G40 : ew E5 40 = getr regs2 10) by (rewrite HE5; reflexivity).
assert (G1 : ew E5 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (G3 : ew E5 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
assert (G4 : ew E5 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
assert (G10 : ew E5 10 = Z_to_bv 64 v) by (rewrite OLD by lia; exact E10).
assert (G11 : ew E5 11 = Z_to_bv 64 kind) by (rewrite OLD by lia; exact E11).
assert (G12 : ew E5 12 = Z_to_bv 64 x) by (rewrite OLD by lia; exact E12).
assert (G32 : ew E5 32 = Z_to_bv 64 vp) by (rewrite OLD by lia; exact E32).
assert (G33 : ew E5 33 = Z_to_bv 64 vn) by (rewrite OLD by lia; exact E33).
assert (G34 : ew E5 34 = Z_to_bv 64 (vk mod 2 ^ 32)) by (rewrite OLD by lia; exact E34).
assert (G35 : ew E5 35 = Z_to_bv 64 JSB) by (rewrite OLD by lia; exact E35).
assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
clear HE5.
assert (Rv : 0 < v <= 2 ^ 47 - 24) by (revert Hv0 Hv8 Hvm C4 C5; clear; unfold amem_range; intros; pose proof (Z.div_mod v 8 ltac:(lia)); lia).
pose proof (Z.mod_pos_bound vk (2 ^ 32) ltac:(lia)) as Hvk32.
assert (HvW : forall a, v <= a < v + 20 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs)) by lia.
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msX) =>
pose proof (st_ok_pi_add_region E5 ss (restrict (w_H W) msX) jt_vregion HS eq_refl) as HS3 end.
match type of HS3 with ?P1 -> ?P2 -> _ => assert (HP1 : P1); [|assert (HP2' : P2); [|specialize (HS3 HP1 HP2'); clear HP1 HP2']] end.
{ unfold region_ok, jt_vregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
rewrite G10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
- apply (chunk_ok_val SEGS E5 _ v 0 8 (SOff 32 0) vp); [cbn [sv_denot]; rewrite G32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 v 8 vp); [|exact Mvp]. intros k Hk. apply FK2; [lia | apply HvW; lia].
- apply (chunk_ok_val SEGS E5 _ v 8 8 (SOff 33 0) vn); [cbn [sv_denot]; rewrite G33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 (v + 8) 8 vn); [|exact Mvn]. intros k Hk. apply FK2; [lia | apply HvW; lia].
- apply (chunk_ok_val SEGS E5 _ v 16 4 (SOff 34 0) (vk mod 2 ^ 32)); [cbn [sv_denot]; rewrite G34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2 (v + 16) 4 (vk mod 2 ^ 32)); [|exact Mvk]. intros k Hk. apply FK2; [lia | apply HvW; lia]. }
{ apply all_disjoint_of_extents. unfold extent_of_region, jt_vregion. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val ss_mem].
rewrite G10, Usp5, unsigned_lit_small by lia. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia. }
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (SHOK5 : sh_ok SEGS JBx jt_SH E5 (mrestrict (w_H W) mem2)).
{ constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem2 E5 JBx 10 v 20 v 0 20).
- apply (range_addressable_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - TJTOK_IS_STK) (spZ regs)); [exact FK2 | lia | lia | lia | exact Hvra].
- unfold JBx. rewrite (U_atom E5 35 JSB G35) by (unfold JSB; lia). reflexivity.
- rewrite (U_atom E5 10 v G10) by lia. reflexivity.
- lia.
- lia.
- intros y Hy. change (Z.min 0 20) with 0 in Hy. change (Z.max 0 20) with 20 in Hy. revert Hvm Rv Hy C3 C4 C5. clear. unfold amem_range, SHADOW_OFF. intros. lia. }
paj_run_tok RUN HS HJ2 SHOK5 JBspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp5. }
assert (FK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (FK2 a Ha Hn).
apply (jt_frame_kept E5 _ (w_H W) mem2 (ms_mem ms0) (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
intros b (r & Hin & Hr). cbn [ss_mem In] in Hin.
destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp5 in Hr; lia. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK5 JBspan.
- pose proof (jt_br1 E5 vk kind _ G34 G11 Rvk Rkind Hc) as Hk1. clear Hc.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E6 := Ex) in * end.
assert (OLD6 : forall k, (k < 512)%nat -> ew E6 k = ew E5 k) by (intros k Hk; unfold E6; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAE6 : env_agree 32 (Ereg regs (jt_extra vp vn vk)) E6) by (unfold E6; env_agree_chain HAE5).
assert (Usp6 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Usp5).
paj_run_tok RUN HS HJ2 SHOK5 JBspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact Usp6 | exact Usp5]. }
assert (FK4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (FK3 a Ha Hn).
apply (jt_frame_kept _ _ (w_H W) _ _ (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
intros b (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp6 in Hr; lia |]). destruct Hin. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tjtok_is_post. apply apost_base_same_fx.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [cbn [ms_regs]; rewrite R1, OLD6, G1, Hra by lia; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (jt_extra vp vn vk) HS); [exact HAE6 | vm_compute; reflexivity]|].
cbv beta. split; [apply Permutation_refl|]. split; [intros a Ha Hn; cbn [ms_mem]; apply FK4; assumption|].
right. split; [intros (Heq & _); rewrite Heq, Z.eqb_refl in Hk1; discriminate | cbn [ms_regs]; rewrite R10; reflexivity].
- lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E6 := Ex) in * end.
assert (OLD6 : forall k, (k < 512)%nat -> ew E6 k = ew E5 k) by (intros k Hk; unfold E6; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAE6 : env_agree 32 (Ereg regs (jt_extra vp vn vk)) E6) by (unfold E6; env_agree_chain HAE5).
assert (Usp6 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Usp5).
pose proof (jt_br1 E6 vk kind _ ltac:(rewrite OLD6 by lia; exact G34) ltac:(rewrite OLD6 by lia; exact G11) Rvk Rkind Hc) as Hk1. clear Hc.
assert (EK : vk = kind) by (destruct (Z.eqb_spec vk kind); [assumption | discriminate Hk1]).
paj_run_tok RUN HS HJ2 SHOK5 JBspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact Usp6 | exact Usp5]. }
assert (FK4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (FK3 a Ha Hn).
apply (jt_frame_kept _ _ (w_H W) _ _ (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
intros b (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp6 in Hr; lia |]). destruct Hin. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK5 JBspan.
+ rewrite branch_ne_U, (U_atom E6 33 vn ltac:(rewrite OLD6 by lia; exact G33)), (U_atom E6 40 (Z.of_nat (length T)) ltac:(rewrite OLD6 by lia; rewrite G40, Hk2; reflexivity)) in Hc by lia.
assert (NN : vn <> Z.of_nat (length T)) by (intros X; rewrite X, Z.eqb_refl in Hc; discriminate Hc). clear Hc.
paj_run_tok RUN HS HJ2 SHOK5 JBspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact Usp6 | exact Usp5]. }
assert (FK5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (FK4 a Ha Hn).
apply (jt_frame_kept _ _ (w_H W) _ _ (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
intros b (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp6 in Hr; lia |]). destruct Hin. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tjtok_is_post. apply apost_base_same_fx.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [cbn [ms_regs]; rewrite R1, OLD6, G1, Hra by lia; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (jt_extra vp vn vk) HS); [exact HAE6 | vm_compute; reflexivity]|].
cbv beta. split; [apply Permutation_refl|]. split; [intros a Ha Hn; cbn [ms_mem]; apply FK5; assumption|].
right. split; [intros (_ & Hn & _); rewrite unsigned_lit_small in Hn by lia; exact (NN Hn) | cbn [ms_regs]; rewrite R10; reflexivity].
+ rewrite branch_ne_U, (U_atom E6 33 vn ltac:(rewrite OLD6 by lia; exact G33)), (U_atom E6 40 (Z.of_nat (length T)) ltac:(rewrite OLD6 by lia; rewrite G40, Hk2; reflexivity)) in Hc by lia.
assert (EN : vn = Z.of_nat (length T)) by (destruct (Z.eqb_spec vn (Z.of_nat (length T))); [assumption | discriminate Hc]). clear Hc.
destruct (HP EK EN) as (HPl & GP & Hvp0 & Hvp63 & Hvpm & Hvpra & Hvphv & Hvpw).
assert (HvpA : vp + Z.of_nat (length T) <= 2 ^ 47) by (revert Hvpm C4 C5; clear; unfold amem_range; intros; lia).
paj_run_tok RUN HS HJ2 SHOK5 JBspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact Usp6 | exact Usp5]. }
assert (FK5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (FK4 a Ha Hn).
apply (jt_frame_kept _ _ (w_H W) _ _ (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
intros b (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp6 in Hr; lia |]). destruct Hin. }
clear HF HFr HG.
clear Ra0 Rra Rsp Rgp Rtp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs ms2) (ms_mem ms2)
TJTOK_IS_STK (spZ regs) [] ly S W mem md [] ly S _ 0 vp x (Z.of_nat (length T)) (-48) (Z_to_bv 64 (BASE + 11700)) HJ2).
- rewrite Ra0, OLD6, G32 by lia. reflexivity.
- rewrite Ra1, OLD6, G12 by lia. reflexivity.
- rewrite Ra2, OLD6, G40, Hk2 by lia. reflexivity.
- lia.
- exact Hvp0.
- exact Hvp63.
- lia.
- lia.
- unfold spZ at 1. rewrite Rsp, Usp6, unsigned_lit_small by lia. lia.
- reflexivity.
- lia.
- rewrite HSTK. unfold ESTACK. lia.
- rewrite Rgp, OLD6, G3 by lia. exact Hgp.
- rewrite Rtp, OLD6, G4 by lia. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
+ rewrite FK5 by lia. apply (jt_garr8_present W mem vp _ a GP). rewrite length_map. lia.
+ unfold spZ at 1 2. rewrite Rsp, Usp6, unsigned_lit_small by lia. unfold ESTACK. lia.
- intros a Ha. split.
+ rewrite FK5 by (specialize (HxW a ltac:(lia)); lia). apply (jt_garr8_present W mem x _ a GT). rewrite length_map, length_app. cbn [length]. lia.
+ unfold spZ at 1 2. rewrite Rsp, Usp6, unsigned_lit_small by lia. specialize (HxW a ltac:(lia)). unfold ESTACK. lia.
- intros a Ha. unfold ESTACK. lia.
- intros a Ha. specialize (HxW a ltac:(lia)). unfold ESTACK. lia.
- exact Hvpm.
- apply (jt_amem_sub _ _ _ Hxm). lia.
- apply (range_addressable_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - TJTOK_IS_STK) (spZ regs)); [exact FK5 | lia | lia | lia | exact Hvpra].
- intros Hn. apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - TJTOK_IS_STK) (spZ regs)); [exact FK5 | lia | lia | lia | lia | exact (Hvphv Hn)].
- apply (range_addressable_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - TJTOK_IS_STK) (spZ regs)); [exact FK5 | lia | lia | lia |].
apply (range_addressable_sub _ _ x (Z.of_nat (length T + 1))); [exact Hxra | lia | lia].
- intros Hn. apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) _ (spZ regs - TJTOK_IS_STK) (spZ regs)); [exact FK5 | lia | lia | lia | lia |].
apply (jt_hull_sub _ x (Z.of_nat (length T + 1))); [exact Hxhv | lia]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & vb & -> & HJ3 & HP3 & Hvb & Hcmp & Hfr3 & Hpres3).
assert (FK6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite Hfr3 by (unfold ESTACK; lia). apply FK5; lia. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W) mem3) HP3 [1]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3' & _).
repeat apply Forall_cons; [| apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp6; intros a Ha.
+ apply (mbyte_of_aview SEGS). apply Hfr3; [lia | unfold ESTACK; lia].
+ intros _. apply (apresent_writable SEGS). apply Hpres3'. rewrite HSTK; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E6 52 (map (getr regs3) CLOB)) as E7 eqn:HE7 in HS.
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD7 : forall k, (k < 52)%nat -> ew E7 k = ew E6 k) by (intros k Hk; rewrite HE7; apply ew_havoc_old; exact Hk).
assert (HAE7 : env_agree 32 (Ereg regs (jt_extra vp vn vk)) E7) by (rewrite HE7; apply env_agree_havoc_ge; [lia | exact HAE6]).
assert (G56 : ew E7 56 = getr regs3 10) by (rewrite HE7; reflexivity).
assert (Usp7 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Usp6).
clear HE7.
assert (SHOK7 : sh_ok SEGS JBx [] E7 (mrestrict (w_H W) mem3)) by constructor.
paj_run_tok RUN HS HJ3 SHOK7 JBspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact Usp7 | exact Usp6]. }
assert (FK7 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (FK6 a Ha Hn).
apply (jt_frame_kept _ _ (w_H W) _ _ (spZ regs - 48) (spZ regs) HFr); [|exact Ha|lia].
intros b (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp7 in Hr; lia |]). destruct Hin. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tjtok_is_post. apply apost_base_same_fx.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [cbn [ms_regs]; rewrite R1, OLD7, OLD6, G1, Hra by lia; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (jt_extra vp vn vk) HS); [exact HAE7 | vm_compute; reflexivity]|].
cbv beta. split; [apply Permutation_refl|]. split; [intros a Ha Hn; cbn [ms_mem]; apply FK7; assumption|].
cbn [ms_regs]. rewrite R10, G56, Hvb, jt_seqz.
assert (HEQ : P = T <-> vb = w64 0).
{ rewrite Hcmp, (jt_eq_bytes (w_H W) mem vp x P T slack HPl GP GT).
split; intros Hq i Hi; specialize (Hq i Hi).
- rewrite (FK5 (vp + i)) by lia. rewrite (FK5 (x + i)) by lia. exact Hq.
- rewrite (FK5 (vp + i)) in Hq by lia. rewrite (FK5 (x + i)) in Hq by lia. exact Hq. }
destruct (Z.eqb_spec (bv_unsigned vb) 0) as [V0|V0].
* left. assert (HV : vb = w64 0) by (apply bv_eq; rewrite V0; reflexivity).
split; [split; [exact EK | split; [rewrite unsigned_lit_small by lia; exact EN | apply HEQ; exact HV]] | reflexivity].
* right. split; [|reflexivity].
intros (_ & _ & HPT). apply HEQ in HPT. apply V0. rewrite HPT. reflexivity.
Qed.
End h.
End f.
End d.
