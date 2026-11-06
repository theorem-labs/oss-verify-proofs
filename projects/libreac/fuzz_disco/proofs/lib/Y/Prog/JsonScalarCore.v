(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 726 of its 801 lines of code are new or changed and 3265 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalar.v, with its module paths and module names changed; 382 of its 467 lines of code are new or changed and 716 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s YC85 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import JtokIs.
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
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
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Variables MC_CONSTS_LO MC_CONSTS_HI : Z.
Hypothesis ASTRLEN : forall fq : YK11.FPState, astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis AMEMCHR : forall fq : YK11.FPState, amemchr_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_memchr).
Hypothesis MCROM : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom SEGS a.
Hypothesis GLOBS : globs_marked SEGS B tfib_globs.
Hypothesis IMGV : img_shadow_vis SEGS B.
Hypothesis ROU : tfib_ro_unowned B.
Definition TJSON_SCALAR_STK : Z := 128 + 2 * ESTACK.
Definition tjson_scalar_str (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
  amem_range a (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem x <> None) /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x).
Definition tjson_scalar_img (W : world SEGS) (mem : word -> option byte) : Prop :=
  exists t1 t2 t3 : Z,
  VAL (A_OBJ 20) mod 8 = 0 /\ (forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> in_img SEGS x) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 24 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20)) 8 t1 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20) + 8) 8 t2 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20) + 16) 8 t3 /\
  tjson_scalar_str W mem t1 [116; 114; 117; 101] /\
  tjson_scalar_str W mem t2 [102; 97; 108; 115; 101] /\
  tjson_scalar_str W mem t3 [110; 117; 108; 108] /\
  tjson_scalar_str W mem (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].

Section w.
Context {fx : YK11.FPState}.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sa : astate) (W0 : world SEGS) (mem0 : word -> option byte)
  (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (kk : Z) (b i n v spe : Z) (BS : list byte).
Definition BZ : list Z := map bv_unsigned BS.
Hypothesis ZL : Z.of_nat (length BS) = n.
Hypothesis Zin : 0 <= i < n.
Hypothesis Zb0 : 0 < b.
Hypothesis Zbm : amem_range b n.
Hypothesis ZBg : garr8 SEGS (mrestrict (w_H W) memc) b BZ.
Hypothesis Zbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n.
Hypothesis Zbsh : shadow_hull_vis (aview SEGS (w_H W) memc) b n.
Hypothesis Zbw : b + n <= spe - TJSON_SCALAR_STK \/ spe <= b.
Hypothesis Zboi : off_img b n.
Hypothesis Zbv : b + n <= v \/ v + 20 <= b.
Hypothesis Zv0 : 0 < v.
Hypothesis Zv8 : v mod 8 = 0.
Hypothesis Zvm : amem_range v 20.
Hypothesis Zvw : spe <= v \/ v + 20 <= spe - TJSON_SCALAR_STK.
Hypothesis Zvoi : off_img v 20.
Hypothesis Zvwr : forall a, v <= a < v + 20 ->
  awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Hypothesis Zvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20.
Hypothesis Zvsh : shadow_hull_vis (aview SEGS (w_H W) memc) v 20.
Hypothesis Zspa : alloc_ceiling <= spe - TJSON_SCALAR_STK.
Hypothesis Zsp47 : spe <= 2 ^ 47.
Hypothesis Zsp16 : spe mod 16 = 0.
Hypothesis ZspS : sp0 - STK <= spe - TJSON_SCALAR_STK.
Hypothesis Zsp0 : spe <= sp0.
Hypothesis Zsp016 : sp0 mod 16 = 0.
Hypothesis ZIMG : tjson_scalar_img W memc.
Hypothesis ZCV : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc.
Definition JW (m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spe - TJSON_SCALAR_STK <= a < spe) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).
Definition MK (m m' : word -> option byte) (Ev : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spe - TJSON_SCALAR_STK <= a < spe - 128) -> ~ Ev a ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) /\
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a).
Definition A_RET : Z := AF_both3_json_scalar + 0x32c.
Definition SEGPOST (m : word -> option byte) (regs : bvmap 5 word) (res : option jtok) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_RET)) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem' md' kk /\
    getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
    match res with
    | Some (e, kd, s, l) =>
        getr regs' 10 = w64 e /\ val_mem SEGS (mrestrict (w_H W) mem') v 8 (b + s) /\
        val_mem SEGS (mrestrict (w_H W) mem') (v + 8) 8 l /\ val_mem SEGS (mrestrict (w_H W) mem') (v + 16) 4 kd /\
        MK m mem' (fun a => v <= a < v + 20)
    | None => getr regs' 10 = w64 0 /\ MK m mem' (fun _ => False)
    end.
Lemma js_nums : b + n <= 2 ^ 47 - 1 /\ v + 20 <= 2 ^ 47 - 1 /\ v <= 2 ^ 47 - 24 /\
  0x7fff7f800000 <= spe - TJSON_SCALAR_STK /\ TJSON_SCALAR_STK = 8320.
Proof.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range in Zbm, Zvm.
pose proof (Z.div_mod v 8 ltac:(lia)). assert (TJSON_SCALAR_STK = 8320) by reflexivity. lia.
Qed.
Lemma jw_low : forall m, JW m -> forall a, 0 <= a < spe - TJSON_SCALAR_STK -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Proof. intros m [H _] a Ha. assert (TJSON_SCALAR_STK = 8320) by reflexivity. apply H; [lia | lia]. Qed.
Lemma jw_of_mk : forall m m', JW m -> MK m m' (fun _ => False) -> JW m'.
Proof.
intros m m' [H1 H2] [K1 K2]. split.
- intros a Ha Hn. rewrite (K1 a Ha) by (try lia; tauto). apply H1; assumption.
- intros a Ha. apply K2, H2, Ha.
Qed.
Lemma mk_refl : forall m Ev, MK m m Ev.
Proof. intros m Ev. split; [reflexivity | auto]. Qed.
Lemma mk_trans : forall m1 m2 m3 Ev, MK m1 m2 (fun _ => False) -> MK m2 m3 Ev -> MK m1 m3 Ev.
Proof.
intros m1 m2 m3 Ev [A1 A2] [B1 B2]. split.
- intros a Ha Hw He. rewrite (B1 a Ha Hw He). apply A1; [exact Ha | exact Hw | tauto].
- intros a Ha. apply B2, A2, Ha.
Qed.
Lemma mk_frame : forall m m1 m2 E0 rs (Ev : Z -> Prop), MK m m1 Ev ->
  frame_of E0 rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange E0 rs a -> Ev a \/ (spe - TJSON_SCALAR_STK <= a < spe - 128)) -> MK m m2 Ev.
Proof.
intros m m1 m2 E0 rs Ev [A1 A2] HF HG Hw. split.
- intros a Ha Hn He. rewrite <- (A1 a Ha Hn He). apply (aview_eq_of SEGS). apply HF.
  rewrite unsigned_lit_small by lia. intros Hx. destruct (Hw a Hx); tauto.
- intros a Ha. apply (apresent_grows (w_H W) m1 m2); [exact HG | apply A2, Ha].
Qed.
Lemma mk_call : forall m m1 m2 lo hi (Ev : Z -> Prop), MK m m1 Ev ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
  spe - TJSON_SCALAR_STK <= lo -> hi <= spe - 128 -> MK m m2 Ev.
Proof.
intros m m1 m2 lo hi Ev [A1 A2] Hk Hp Hlo Hhi. split.
- intros a Ha Hn He. rewrite Hk by (try lia; intros X; apply Hn; lia). apply A1; assumption.
- intros a Ha. apply Hp, A2, Ha.
Qed.
Lemma seg_chain : forall m regs mcur regscur res, MK m mcur (fun _ => False) ->
  getr regscur 2 = getr regs 2 -> getr regscur 3 = getr regs 3 -> getr regscur 4 = getr regs 4 ->
  forall W' c', SEGPOST mcur regscur res W' c' -> SEGPOST m regs res W' c'.
Proof.
intros m regs mcur regscur res HM E2 E3 E4 W' c' (HW' & regs' & mem' & md' & Hc & HJ & R2 & R3 & R4 & Hres).
split; [exact HW'|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact HJ|].
rewrite <- E2, <- E3, <- E4. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
destruct res as [[[[e kd] s] l]|].
- destruct Hres as (H1 & H2 & H3 & H4 & H5). repeat (split; [assumption|]). eapply mk_trans; eassumption.
- destruct Hres as (H1 & H5). split; [exact H1|]. eapply mk_trans; eassumption.
Qed.
Lemma jw_B : forall m, JW m -> garr8 SEGS (mrestrict (w_H W) m) b BZ.
Proof.
intros m HW jj Hj. destruct (ZBg jj Hj) as [H1 H2]. split; [|exact H2].
apply (val_mem_kept SEGS (w_H W) (w_H W) memc m _ 1); [|exact H1].
intros q Hq. unfold BZ in Hj. rewrite length_map in Hj. pose proof js_nums as (N1 & _).
apply (proj1 HW); lia.
Qed.
Lemma jw_Bra : forall m, JW m -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF b n.
Proof.
intros m HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (range_addressable_kept_win (aview SEGS (w_H W) memc) _ (spe - TJSON_SCALAR_STK) spe); [exact (proj1 HW) | lia | lia | lia | exact Zbra].
Qed.
Lemma jw_vra : forall m, JW m -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF v 20.
Proof.
intros m HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (range_addressable_kept_win (aview SEGS (w_H W) memc) _ (spe - TJSON_SCALAR_STK) spe); [exact (proj1 HW) | lia | lia | lia | exact Zvra].
Qed.
Lemma jw_vpres : forall m, JW m -> forall a, v <= a < v + 20 -> apresent (w_H W) m a.
Proof. intros m HW a Ha. apply (proj2 HW). exact (proj2 (Zvwr a Ha)). Qed.
Lemma jw_cv : forall m, JW m -> consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W m.
Proof.
intros m HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (consts_view_keep SEGS _ _ W memc m ZCV). intros a Ha.
destruct (MCROM a Ha) as (sg & Hsg & _ & Hb). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hb))).
apply (proj1 HW); lia.
Qed.

Lemma jw_imgaddr : forall m, JW m -> forall a, in_img SEGS a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Proof.
intros m HW a Ha. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_segs_low a Ha). apply (proj1 HW); lia.
Qed.
Lemma jw_tstr : forall m a s, JW m -> tjson_scalar_str W memc a s -> tjson_scalar_str W m a s.
Proof.
intros m a s HW (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlo : forall x, a <= x < a + Z.of_nat (length s) + 1 -> 0 <= x < kLowMemEnd).
{ intros x Hx. exact (pa_segs_low x (H10 x Hx)). }
assert (Hlow : a + Z.of_nat (length s) + 1 <= kLowMemEnd) by (pose proof (Hlo (a + Z.of_nat (length s)) ltac:(lia)); lia).
assert (HK : forall x, 0 <= x < spe - TJSON_SCALAR_STK -> aview SEGS (w_H W) m x = aview SEGS (w_H W) memc x) by (apply jw_low; exact HW).
split; [exact H1|]. split.
{ intros q Hq. destruct (H2 q Hq) as [V R]. split; [|exact R].
  apply (val_mem_kept SEGS (w_H W) (w_H W) memc m _ 1); [|exact V].
  intros r Hr. rewrite length_app in Hq. cbn [length] in Hq. apply HK. lia. }
split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [apply (range_addressable_kept_win (aview SEGS (w_H W) memc) _ (spe - TJSON_SCALAR_STK) spe); [exact (proj1 HW) | lia | lia | lia | exact H7]|].
split; [apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) _ (spe - TJSON_SCALAR_STK) spe); [exact (proj1 HW) | lia | lia | lia | lia | exact H8]|].
split; [|exact H10].
intros x Hx. pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)). rewrite HK by lia. exact (H9 x Hx).
Qed.
Lemma jw_litab : forall m, JW m -> exists t1 t2 t3 : Z,
  VAL (A_OBJ 20) mod 8 = 0 /\ (forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> in_img SEGS x) /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (VAL (A_OBJ 20)) 24 /\
  val_mem SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 20)) 8 t1 /\
  val_mem SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 20) + 8) 8 t2 /\
  val_mem SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 20) + 16) 8 t3 /\
  tjson_scalar_str W m t1 [116; 114; 117; 101] /\
  tjson_scalar_str W m t2 [102; 97; 108; 115; 101] /\
  tjson_scalar_str W m t3 [110; 117; 108; 108].
Proof.
intros m HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct ZIMG as (t1 & t2 & t3 & L8 & Li & Lra & V1 & V2 & V3 & S1 & S2 & S3 & _).
assert (Llow : forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> 0 <= x < kLowMemEnd) by (intros x Hx; exact (pa_segs_low x (Li x Hx))).
pose proof (Llow (VAL (A_OBJ 20)) ltac:(lia)). pose proof (Llow (VAL (A_OBJ 20) + 23) ltac:(lia)).
exists t1, t2, t3. split; [exact L8|]. split; [exact Li|].
split; [apply (range_addressable_kept_win (aview SEGS (w_H W) memc) _ (spe - TJSON_SCALAR_STK) spe); [exact (proj1 HW) | lia | lia | lia | exact Lra]|].
split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memc m _ 8); [intros r Hr; apply (jw_low m HW); lia | exact V1]|].
split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memc m _ 8); [intros r Hr; apply (jw_low m HW); lia | exact V2]|].
split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memc m _ 8); [intros r Hr; apply (jw_low m HW); lia | exact V3]|].
split; [exact (jw_tstr m _ _ HW S1)|]. split; [exact (jw_tstr m _ _ HW S2) | exact (jw_tstr m _ _ HW S3)].
Qed.
Lemma jw_str14 : forall m, JW m -> tjson_scalar_str W m (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].
Proof.
intros m HW. destruct ZIMG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S4). exact (jw_tstr m _ _ HW S4).
Qed.

Lemma jstr_fuel : forall fu Bm im j, jlen Bm - j <= Z.of_nat fu -> jstr Bm im j fu = jstr Bm im j (S fu).
Proof.
induction fu as [|fu IH]; intros Bm im j Hf.
- cbn [jstr]. replace (jlen Bm <=? j) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- cbn [jstr].
  destruct (jlen Bm <=? j) eqn:E1; [reflexivity|].
  destruct (jbyte Bm j =? 34); [reflexivity|]. destruct (jbyte Bm j <? 32); [reflexivity|].
  destruct (jbyte Bm j =? 92).
  + destruct (jlen Bm <=? j + 1); [reflexivity|]. destruct (negb (jesc (jbyte Bm (j + 1)))); [reflexivity|].
    destruct (jbyte Bm (j + 1) =? 117).
    * destruct (_ || _); [reflexivity|]. apply IH. lia.
    * apply IH. lia.
  + apply IH. lia.
Qed.
Lemma jstr_fuel_eq : forall d fu Bm im j, jlen Bm - j <= Z.of_nat fu -> jstr Bm im j fu = jstr Bm im j (d + fu).
Proof.
induction d as [|d IH]; intros fu Bm im j Hf; [reflexivity|].
rewrite (IH fu Bm im j Hf). replace (S d + fu)%nat with (S (d + fu)) by lia. apply jstr_fuel. lia.
Qed.
Lemma jstr_fuel_any : forall f1 f2 Bm im j, jlen Bm - j <= Z.of_nat f1 -> jlen Bm - j <= Z.of_nat f2 -> jstr Bm im j f1 = jstr Bm im j f2.
Proof.
intros f1 f2 Bm im j H1 H2. destruct (Nat.le_ge_cases f1 f2) as [L|L].
- replace f2 with ((f2 - f1) + f1)%nat by lia. apply jstr_fuel_eq. exact H1.
- replace f1 with ((f1 - f2) + f2)%nat by lia. symmetry. apply jstr_fuel_eq. exact H2.
Qed.
Lemma jdigits_fuel : forall fu Bm j, jlen Bm - j <= Z.of_nat fu -> jdigits Bm j fu = jdigits Bm j (S fu).
Proof.
induction fu as [|fu IH]; intros Bm j Hf.
- cbn [jdigits]. replace (j <? jlen Bm) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- cbn [jdigits].
  destruct ((j <? jlen Bm) && jdigit (jbyte Bm j)) eqn:E1; [|reflexivity].
  apply IH. apply andb_prop in E1 as [E1 _]. apply Z.ltb_lt in E1. lia.
Qed.
Lemma jdigits_fuel_any : forall f1 f2 Bm j, jlen Bm - j <= Z.of_nat f1 -> jlen Bm - j <= Z.of_nat f2 -> jdigits Bm j f1 = jdigits Bm j f2.
Proof.
assert (G : forall d fu Bm j, jlen Bm - j <= Z.of_nat fu -> jdigits Bm j fu = jdigits Bm j (d + fu)).
{ induction d as [|d IH]; intros fu Bm j Hf; [reflexivity|].
  rewrite (IH fu Bm j Hf). replace (S d + fu)%nat with (S (d + fu)) by lia. apply jdigits_fuel. lia. }
intros f1 f2 Bm j H1 H2. destruct (Nat.le_ge_cases f1 f2) as [L|L].
- replace f2 with ((f2 - f1) + f1)%nat by lia. apply G. exact H1.
- replace f1 with ((f1 - f2) + f2)%nat by lia. symmetry. apply G. exact H2.
Qed.


Definition jsBx : sv := SOff 27 0.
Definition jsBsp : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition jPTR (al : Z) : afact := mkAF 1 (2 ^ 47 - 1) al.
Definition jNOTP : afact := mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 2) 0.
Definition jIDX : afact := mkAF 0 (2 ^ 47 - 2) 0.
Definition jBYTE : afact := mkAF 0 255 0.
Definition jSP : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition jVP : afact := mkAF 1 (2 ^ 47 - 24) 3.
Definition jSB : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition jR (r : bv 5) (e : sv) (l : list sv) : list sv := sr_set l r e.
Lemma ew_EiR : forall regs extra q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r ->
  ew (Eimg (Ereg regs extra)) q = getr regs r.
Proof. intros regs extra q r Hn Hr. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma ew_EiX : forall regs extra c, (32 + c < 240)%nat ->
  ew (Eimg (Ereg regs extra)) (32 + c) = nth c extra (Z_to_bv 64 0).
Proof. intros regs extra c Hc. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma js_awr_v : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a.
Proof. intros a Ha. exact (proj1 (Zvwr a Ha)). Qed.
Lemma js_v_app : forall x, v <= x < v + 20 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros x Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range in Zvm. unfold SHADOW_OFF. lia.
Qed.

Definition jrest_exp (j2 : Z) : option jtok := match jexp BZ j2 with None => None | Some j3 => Some (j3, 2, i, j3 - i) end.
Definition jrest_frac (j1 : Z) : option jtok := match jfrac BZ j1 with None => None | Some j2 => jrest_exp j2 end.
Definition A_FC : Z := AF_both3_json_scalar + 0x3e0.
Definition A_IL : Z := AF_both3_json_scalar + 0x4e0.
Definition breg (c : Z) : YP09.region :=
  YP09.mkRegion (Some 32%nat) c (c + 1) 0 0 [YP09.mkChunk c (CVal 1 (SOff (Z.to_nat (33 + c)) 0))].
Definition jx_extra (j : Z) : list word :=
  map (Z_to_bv 64) [b + j; jbyte BZ j; jbyte BZ (j + 1); jbyte BZ (j + 2); jbyte BZ (j + 3); jbyte BZ (j + 4); jbyte BZ (j + 5)].
Definition nfacts (J : nat) (jlo jhi : Z) : facts :=
  mkFacts [ (2%nat, jSP); (J, mkAF jlo jhi 0); (19%nat, mkAF 1 (2 ^ 47 - 1) 0); (20%nat, jPTR 0);
            (16%nat, jNOTP); (15%nat, jIDX); (9%nat, jVP); (27%nat, jSB); (18%nat, mkAF 1 (2 ^ 47 - 2) 0);
            (32%nat, mkAF 1 (2 ^ 47 - 1) 0);
            (33%nat, jBYTE); (34%nat, jBYTE); (35%nat, jBYTE); (36%nat, jBYTE); (37%nat, jBYTE); (38%nat, jBYTE) ]
    [] [ (SAlu ALU_ADD (SOff 20 0) (SOff J 0), SOff 32 0) ].

Lemma jbyte_range : forall x, 0 <= jbyte BZ x < 256.
Proof.
intros x. unfold jbyte, BZ. destruct (Nat.lt_ge_cases (Z.to_nat x) (length BS)) as [Hl|Hl].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hl).
  rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat x) BS (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. change (Z.of_N 8) with 8 in R. lia.
- rewrite nth_overflow by (rewrite length_map; exact Hl). lia.
Qed.
Lemma garr8_at : forall M (l : list Z) a jz, garr8 SEGS M a l -> 0 <= jz < Z.of_nat (length l) ->
  val_mem SEGS M (a + jz) 1 (jbyte l jz) /\ 0 <= jbyte l jz < 256.
Proof.
intros M l a jz H Hj. unfold jbyte. destruct (H (Z.to_nat jz) ltac:(lia)) as [H1 H2].
rewrite Z2Nat.id in H1 by lia. split; assumption.
Qed.

Lemma st_ok_pi_add_cond : forall E0 ss ms c a0 b0,
  st_ok_pi SEGS VAL E0 ss ms -> branch_taken c (sv_denot E0 a0) (sv_denot E0 b0) = true -> st_ok_pi SEGS VAL E0 (add_cond ss (mkAC c a0 b0)) ms.
Proof. intros E0 ss ms c a0 b0 HS Hb. exact (st_ok_add_cond SEGS E0 (abs_ss VAL ss) ms c a0 b0 HS Hb). Qed.

Lemma U_offm : forall E0 q k x, ew E0 q = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E0 (SOff q k) = (x + k) mod 2 ^ 64.
Proof. intros E0 q k x Hq Hx. rewrite U_SOff, Hq, unsigned_lit_small by lia. reflexivity. Qed.
Lemma U_litm : forall E0 z, U E0 (SLit z) = z mod 2 ^ 64.
Proof. intros E0 z. rewrite U_SLit. reflexivity. Qed.
Lemma z256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true -> forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma bf_digit_ltu : forall c, 0 <= c < 256 -> ((c + -58) mod 2 ^ 64 <? (-10) mod 2 ^ 64) = negb (jdigit c).
Proof.
intros c Hc. apply Bool.eqb_prop.
exact (z256 (fun c => Bool.eqb ((c + -58) mod 2 ^ 64 <? (-10) mod 2 ^ 64) (negb (jdigit c))) ltac:(vm_compute; reflexivity) c Hc).
Qed.
Lemma jlen_BZ : jlen BZ = n.
Proof. unfold jlen, BZ. rewrite length_map. exact ZL. Qed.
Lemma jdigits_nd : forall j, 0 <= j < n -> jdigit (jbyte BZ j) = false -> jdigits BZ j (length BS) = j.
Proof.
intros j Hj Hd. pose proof ZL as ZL'. assert (exists L, length BS = Datatypes.S L) as [L EL] by (destruct (length BS); [lia | eauto]).
rewrite EL. cbn [jdigits]. rewrite jlen_BZ, Hd. rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma jdigits_d : forall j, 0 <= j < n -> jdigit (jbyte BZ j) = true -> jdigits BZ j (length BS) = jdigits BZ (j + 1) (length BS).
Proof.
intros j Hj Hd. pose proof ZL as ZL'. assert (exists L, length BS = Datatypes.S L) as [L EL] by (destruct (length BS); [lia | eauto]).
rewrite EL. rewrite <- (jdigits_fuel L BZ (j + 1)) by (rewrite jlen_BZ; lia).
change (jdigits BZ j (Datatypes.S L)) with (if (j <? jlen BZ) && jdigit (jbyte BZ j) then jdigits BZ (j + 1) L else j).
rewrite jlen_BZ, Hd. replace (j <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma jdigits_n : forall f, jdigits BZ n f = n.
Proof. intros [|f]; [reflexivity|]. cbn [jdigits]. rewrite jlen_BZ, Z.ltb_irrefl. reflexivity. Qed.
Lemma jrest_exp_n : jrest_exp n = Some (n, 2, i, n - i).
Proof. unfold jrest_exp, jexp. rewrite jlen_BZ, Z.ltb_irrefl. reflexivity. Qed.
Definition A_WR : Z := AF_both3_json_scalar + 0x5f4.
Definition A_SL : Z := AF_both3_json_scalar + 0xa0.
Definition A_LIT : Z := AF_both3_json_scalar + 0x298.
Definition A_N0 : Z := AF_both3_json_scalar + 0x2fc.

Lemma add_breg : forall E0 ss ms0 c j, st_ok_pi SEGS VAL E0 ss (restrict (w_H W) ms0) -> JW (ms_mem ms0) ->
  ew E0 32 = Z_to_bv 64 (b + j) -> ew E0 (Z.to_nat (33 + c)) = Z_to_bv 64 (jbyte BZ (j + c)) ->
  0 <= j -> 0 <= c -> j + c < n -> all_disjoint E0 (breg c) (ss_mem ss) ->
  st_ok_pi SEGS VAL E0 (add_atom (mkSS (ss_pc ss) (ss_regs ss) (breg c :: ss_mem ss) (ss_resv ss) (ss_facts ss)) 32 (mkAF 1 (2 ^ 47 - 2 - c) 0))
    (restrict (w_H W) ms0).
Proof.
intros E0 ss ms0 c j HS HW E32 E3c Hj Hc Hjc Hd.
pose proof js_nums as (N1 & N2 & N3 & N4 & N5).
destruct (garr8_at _ _ _ (j + c) (jw_B _ HW) ltac:(unfold BZ; rewrite length_map; lia)) as [VB RB].
apply st_ok_pi_add_fact.
- apply (st_ok_pi_add_region E0 ss _ (breg c) HS).
  + unfold region_wf, chunk_inside, breg. cbn [r_lo r_hi r_wlo r_whi r_chunks forallb c_off c_len cv_len YP09.c_val].
    rewrite (proj2 (Z.leb_le c (c + 1))) by lia. rewrite !Z.leb_refl. reflexivity.
  + unfold region_ok, breg. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem restrict].
    rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E0 _ (b + j) c 1 (SOff (Z.to_nat (33 + c)) 0) (jbyte BZ (j + c)));
      [cbn [sv_denot]; rewrite E3c, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
    replace (b + j + c) with (b + (j + c)) by lia. exact VB.
  + exact Hd.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma obl_B : forall Ex M c j, JW M -> ew Ex 27 = Z_to_bv 64 SHADOW_OFF -> ew Ex 32 = Z_to_bv 64 (b + j) ->
  0 <= j -> 0 <= c -> j + c < n -> range_addressable (rd_of SEGS (mrestrict (w_H W) M)) (U Ex jsBx) (U Ex (SOff 32 c)) 1.
Proof.
intros Ex M c j HW H27 H32 Hj Hc Hjc. pose proof js_nums as (N1 & N2 & N3 & N4 & N5).
assert (UB : U Ex jsBx = SHADOW_OFF) by (unfold jsBx; rewrite (U_atom Ex 27 SHADOW_OFF H27) by (unfold SHADOW_OFF; lia); reflexivity).
rewrite (U_atom_off Ex 32 (b + j) c H32) by lia.
eapply (obl_of_range SEGS (w_H W) M Ex jsBx _ 1 b n (jw_Bra M HW) UB); lia.
Qed.
Definition A_EL : Z := AF_both3_json_scalar + 0x5b4.
Definition A_EC : Z := AF_both3_json_scalar + 0x524.
Definition A_FL : Z := AF_both3_json_scalar + 0x438.
Lemma jdig_at_ge : forall j, n <= j -> jdig_at BZ j = false.
Proof. intros j Hj. unfold jdig_at. rewrite jlen_BZ. replace (j <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma jdig_at_lt : forall j, j < n -> jdig_at BZ j = jdigit (jbyte BZ j).
Proof. intros j Hj. unfold jdig_at. rewrite jlen_BZ. replace (j <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma jstr_ge : forall j f, n <= j -> jstr BZ i j f = None.
Proof.
intros j [|f] Hj; [reflexivity|]. cbn [jstr]. rewrite jlen_BZ.
replace (n <=? j) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma bf_hex2 : forall c, 0 <= c < 256 -> jdigit c = false ->
  (zcanon (zcanon (Z.land ((c + 0) mod 2 ^ 64) (223 mod 2 ^ 64)) + -71 mod 2 ^ 64) <? 18446744073709551610 mod 2 ^ 64) = negb (jhexd c).
Proof.
intros c Hc Hd. apply Bool.eqb_prop.
pose proof (z256 (fun c => jdigit c || Bool.eqb (zcanon (zcanon (Z.land ((c + 0) mod 2 ^ 64) (223 mod 2 ^ 64)) + -71 mod 2 ^ 64) <? 18446744073709551610 mod 2 ^ 64) (negb (jhexd c))) ltac:(vm_compute; reflexivity) c Hc) as H.
cbv beta in H. rewrite Hd in H. exact H.
Qed.
Lemma bf_hex1 : forall c, 0 <= c < 256 -> (18446744073709551605 mod 2 ^ 64 <? (c + -58) mod 2 ^ 64) = jdigit c.
Proof.
intros c Hc. apply Bool.eqb_prop.
exact (z256 (fun c => Bool.eqb (18446744073709551605 mod 2 ^ 64 <? (c + -58) mod 2 ^ 64) (jdigit c)) ltac:(vm_compute; reflexivity) c Hc).
Qed.

Definition sl_facts : facts :=
  mkFacts [ (2%nat, jSP); (20%nat, jPTR 0); (25%nat, mkAF 1 (2 ^ 47 - 2) 0); (19%nat, mkAF 1 (2 ^ 47 - 1) 0);
            (24%nat, jNOTP); (9%nat, jIDX); (23%nat, jVP); (27%nat, jSB); (18%nat, mkAF 1 (2 ^ 47 - 2) 0);
            (32%nat, mkAF 1 (2 ^ 47 - 2) 0);
            (33%nat, jBYTE); (34%nat, jBYTE); (35%nat, jBYTE); (36%nat, jBYTE); (37%nat, jBYTE); (38%nat, jBYTE) ]
    [] [ (SAlu ALU_ADD (SOff 20 0) (SOff 25 0), SOff 32 0) ].
Definition A_HX2 : Z := AF_both3_json_scalar + 0x164.
Definition SLP (j : Z) : Prop := forall regs m md,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 20 = w64 b -> getr regs 25 = w64 j -> getr regs 8 = w64 (j - 1) ->
  getr regs 26 = w64 34 -> getr regs 13 = w64 32 -> getr regs 14 = w64 92 -> getr regs 21 = w64 (VAL (A_OBJ 19)) ->
  getr regs 19 = w64 n -> getr regs 24 = w64 (2 ^ 64 - 1 - b) -> getr regs 9 = w64 i -> getr regs 23 = w64 v ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 (b + i) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_SL)) m (seg_rom SEGS)) md) (SEGPOST m regs (jstr BZ i j (length BS))).


Definition HXP (pc : Z) (j : Z) (res : option jtok) : Prop := forall regs m md,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W m md kk -> JW m ->
  getr regs 2 = w64 (spe - 128) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 20 = w64 b -> getr regs 25 = w64 (j + 1) -> getr regs 8 = w64 (j - 1) ->
  getr regs 26 = w64 34 -> getr regs 13 = w64 32 -> getr regs 14 = w64 92 -> getr regs 21 = w64 (VAL (A_OBJ 19)) ->
  getr regs 19 = w64 n -> getr regs 24 = w64 (2 ^ 64 - 1 - b) -> getr regs 9 = w64 i -> getr regs 23 = w64 v ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 18 = w64 (b + i) -> getr regs 15 = w64 18446744073709551605 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)) md) (SEGPOST m regs res).

Definition jm_regions : smem := [ stack_region 128; got_regionP; bcell_regionP 35; breg 0 ].
Definition jm_facts : facts :=
  mkFacts [ (2%nat, jSP); (10%nat, jPTR 0); (11%nat, jIDX); (12%nat, mkAF 1 (2 ^ 47 - 1) 0); (13%nat, jVP);
            (32%nat, mkAF 1 (2 ^ 47 - 2) 0); (33%nat, jBYTE); (34%nat, jNOTP); (35%nat, jSB) ]
    [ mkAC BC_LTU (SOff 11 0) (SOff 12 0) ]
    [ (SAlu ALU_XOR (SOff 10 0) (SLit (-1)), SOff 34 0); (SAlu ALU_ADD (SOff 10 0) (SOff 11 0), SOff 32 0) ].
Definition ss_jm : sstate := mkSS AF_both3_json_scalar sr_atoms jm_regions None jm_facts.
Definition jm_extra : list word := map (Z_to_bv 64) [b + i; jbyte BZ i; 2 ^ 64 - 1 - b; SHADOW_OFF].
End w.
End h.
End f.
End d.
