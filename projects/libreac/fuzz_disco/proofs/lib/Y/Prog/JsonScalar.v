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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalar.v, with its module paths and module names changed; 680 of its 851 lines of code are new or changed and 630 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Export JsonScalarCore
  JsonScalarSeg_wr JsonScalarSeg_el JsonScalarSeg_ec JsonScalarSeg_fl JsonScalarSeg_fc JsonScalarSeg_il JsonScalarSeg_num0 JsonScalarSeg_lit JsonScalarSeg_hx JsonScalarSeg_sl JsonScalarSeg_jm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[local] Ltac LiaTwx2.zify_split_ranges ::= idtac.
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
#[local] Notation tjson_scalar_str := (@tjson_scalar_str rc PI).
#[local] Notation tjson_scalar_img := (@tjson_scalar_img rc PI).
Definition tjson_rom_bytes (a : Z) (l : list Z) : Prop :=
  forall k, (k < length l)%nat -> seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (nth k l 0)).
Definition tjson_rom_word (a w : Z) : Prop :=
  forall k, (k < 8)%nat -> seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 8 k)).
Definition tjson_scalar_rostr (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  In (a, Z.of_nat (length s) + 1) tfib_globs /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x /\ in_roP SEGS pa_relro_lo pa_relro_hi x) /\
  tjson_rom_bytes a (s ++ [0]) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     seg_rom SEGS (Z_to_bv 64 x) <> None).
Definition tjson_scalar_roimg : Prop :=
  exists t1 t2 t3 : Z,
  In (VAL (A_OBJ 20), 24) tfib_globs /\ VAL (A_OBJ 20) mod 8 = 0 /\
  (forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> in_img SEGS x /\ in_roP SEGS pa_relro_lo pa_relro_hi x) /\
  tjson_rom_word (VAL (A_OBJ 20)) t1 /\ tjson_rom_word (VAL (A_OBJ 20) + 8) t2 /\ tjson_rom_word (VAL (A_OBJ 20) + 16) t3 /\
  tjson_scalar_rostr t1 [116; 114; 117; 101] /\
  tjson_scalar_rostr t2 [102; 97; 108; 115; 101] /\
  tjson_scalar_rostr t3 [110; 117; 108; 108] /\
  tjson_scalar_rostr (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].
Definition tjson_scalar_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp v : Z) (E : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TJSON_SCALAR_STK <= a < sp) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - TJSON_SCALAR_STK <= a < sp) -> apresent (w_H W) memc a ->
     apresent (w_H W2) mem2 a) /\
  (forall a, sp - TJSON_SCALAR_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition tjson_scalar_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b i v : Z) (BS : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    match jscalar (map bv_unsigned BS) i with
    | Some (e, kd, s, l) =>
        getr regs2 10 = w64 e /\
        val_mem SEGS (mrestrict (w_H W2) mem2) v 8 (b + s) /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (v + 8) 8 l /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (v + 16) 4 kd /\
        tjson_scalar_kept lyc Sc W memc W2 mem2 (spZ regs) v (fun a => v <= a < v + 20)
    | None =>
        getr regs2 10 = w64 0 /\
        tjson_scalar_kept lyc Sc W memc W2 mem2 (spZ regs) v (fun _ => False)
    end.
Definition tjson_scalar_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b i n v : Z) (BS : list byte) ch,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc ->
  tjson_scalar_roimg ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 b -> getr regs 11 = w64 i -> getr regs 12 = w64 n -> getr regs 13 = w64 v ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z (regupd regs 8 (Z_to_bv 64 0))) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TJSON_SCALAR_STK -> spZ regs <= sp0 ->
  0 <= i < 2 ^ 64 -> Z.of_nat (length BS) = n -> b + n <= 2 ^ 64 ->
  (i < n ->
     garr8 SEGS (mrestrict (w_H W) memc) b (map bv_unsigned BS) /\
     0 < b /\ b + n <= 2 ^ 63 /\ amem_range b n /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n /\
     shadow_hull_vis (aview SEGS (w_H W) memc) b n /\
     (b + n <= spZ regs - TJSON_SCALAR_STK \/ spZ regs <= b) /\ off_img b n /\ (b + n <= v \/ v + 20 <= b)) ->
  0 < v -> v mod 8 = 0 -> v + 20 <= 2 ^ 63 -> amem_range v 20 ->
  (spZ regs <= v \/ v + 20 <= spZ regs - TJSON_SCALAR_STK) ->
  off_img v 20 ->
  (forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) v 20 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_json_scalar) regs memc mdc)
    (tjson_scalar_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b i v BS).
Lemma tfib_globs_bnd : forall q sz, In (q, sz) tfib_globs -> 0x20000 <= q /\ q + sz <= 0xa0700 /\ 1 <= sz.
Proof.
intros q sz H. unfold tfib_globs in H.
repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.
Lemma tjson_ro_mbyte : forall (W : world SEGS) mem lo sz x (bt : byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ro_unowned B lo sz ->
  in_roP SEGS pa_relro_lo pa_relro_hi x -> lo <= x < lo + sz -> seg_rom SEGS (Z_to_bv 64 x) = Some bt ->
  mbyte SEGS (mrestrict (w_H W) mem) x = Some bt.
Proof.
intros W mem lo sz x bt HR HU Hro Hx Hs.
pose proof (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ lo sz x HR Hro HU Hx) as Hv. rewrite Hs in Hv.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict (w_H W) mem) x) as [b0|] eqn:E0; cbn in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma tjson_le_byte1 : forall c, 0 <= c < 256 -> YO0f.le_byte c 1 0 = c.
Proof.
intros c Hc. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma tjson_ro_unowned_of : forall q sz, In (q, sz) tfib_globs -> ro_unowned B q sz.
Proof. intros q sz H. apply (tfib_ro_unowned_at B q sz ROU). unfold tfib_ro_ranges. apply in_or_app. left. exact H. Qed.
Section ro. Context {fx : YK11.FPState}.
Lemma tjson_str_of_ro : forall ly S (W : world SEGS) mem md a s,
  AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  tjson_scalar_rostr a s -> tjson_scalar_str W mem a s.
Proof.
intros ly S W mem md a s HAR HR (HF & HIn & HIR & HB & HT).
pose proof (tfib_globs_bnd _ _ HIn) as (Q1 & Q2 & Q3).
pose proof (tjson_ro_unowned_of _ _ HIn) as HU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hc : forall j, (j < length (s ++ [0%Z]))%nat -> 0 <= nth j (s ++ [0]) 0 < 256).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length s)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl. pose proof (proj1 (Forall_forall _ _) HF (nth j s 0) (nth_In s 0 Hl)) as Hq. cbv beta in Hq. lia.
  - rewrite app_nth2 by exact Hl. replace (j - length s)%nat with 0%nat by lia. cbn. lia. }
split; [exact HF|]. split.
{ intros j Hj. split; [|exact (Hc j Hj)]. intros k Hk. assert (k = 0%nat) as -> by lia.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite length_app in Hj. cbn [length] in Hj.
  apply (tjson_ro_mbyte W mem a (Z.of_nat (length s) + 1)); [exact HR | exact HU | apply HIR; lia | lia |].
  rewrite (HB j) by (rewrite length_app; cbn [length]; lia).
  rewrite (tjson_le_byte1 (nth j (s ++ [0]) 0)) by (apply Hc; rewrite length_app; cbn [length]; lia). reflexivity. }
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold amem_range; left; lia|].
split; [apply (ro_usable_glob SEGS B tfib_globs ly S W mem md a (Z.of_nat (length s) + 1) a (Z.of_nat (length s) + 1) GLOBS HIn HAR); lia|].
split; [apply (ro_hull SEGS B ly S W mem md a (Z.of_nat (length s) + 1) IMGV HAR); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
split.
- intros x Hx. unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)); [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 x)) eqn:E0; [discriminate|]. exfalso. exact (HT x Hx E0).
- intros x Hx. exact (proj1 (HIR x Hx)).
Qed.
Lemma tjson_img_of_ro : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  tjson_scalar_roimg -> tjson_scalar_img W mem.
Proof.
intros ly S W mem md HAR HR (t1 & t2 & t3 & HIn & H8 & HIR & W1 & W2 & W3 & S1 & S2 & S3 & S4).
pose proof (tfib_globs_bnd _ _ HIn) as (Q1 & Q2 & Q3).
pose proof (tjson_ro_unowned_of _ _ HIn) as HU.
assert (VW : forall o t, 0 <= o -> o + 8 <= 24 -> tjson_rom_word (VAL (A_OBJ 20) + o) t ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20) + o) 8 t).
{ intros o t Ho Ho8 Hw k Hk. apply (tjson_ro_mbyte W mem (VAL (A_OBJ 20)) 24); [exact HR | exact HU | apply HIR; lia | lia | exact (Hw k Hk)]. }
exists t1, t2, t3. split; [exact H8|]. split; [intros x Hx; exact (proj1 (HIR x Hx))|].
split; [apply (ro_usable_glob SEGS B tfib_globs ly S W mem md (VAL (A_OBJ 20)) 24 (VAL (A_OBJ 20)) 24 GLOBS HIn HAR); lia|].
split; [rewrite <- (Z.add_0_r (VAL (A_OBJ 20))) at 1; apply VW; [lia | lia | rewrite Z.add_0_r; exact W1]|].
split; [apply VW; [lia | lia | exact W2]|]. split; [apply VW; [lia | lia | exact W3]|].
split; [exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S1)|].
split; [exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S2)|].
split; [exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S3)|].
exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S4).
Qed.
End ro.

Section w.
Context {fx : YK11.FPState}.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sa : astate) (W0 : world SEGS) (mem0 : word -> option byte)
  (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (kk : Z) (b i n v spe : Z) (BS : list byte).
#[local] Notation BZ := (@BZ BS).
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
#[local] Notation JW := (@JW rc PI W memc spe).
#[local] Notation MK := (@MK rc PI W spe).
#[local] Notation SEGPOST := (@SEGPOST rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W kk b v spe).
#[local] Notation js_nums := (@js_nums rc sp0 b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_low := (@jw_low rc PI sp0 W memc i n v spe BS Zin Zv0 Zsp47).
#[local] Notation jw_of_mk := (@jw_of_mk rc PI sp0 W memc i n v spe BS Zin).
#[local] Notation mk_refl := (@mk_refl rc PI W spe).
#[local] Notation mk_trans := (@mk_trans rc PI W b i n v spe Zin Zbw Zbv Zvw).
#[local] Notation mk_frame := (@mk_frame rc PI sp0 W b i n v spe BS Zin Zbw Zbv Zvw).
#[local] Notation mk_call := (@mk_call rc PI sp0 W b i n v spe BS Zin Zb0 Zbw Zbv Zv0 Zvw Zsp16 Zsp0 Zsp016).
#[local] Notation seg_chain := (@seg_chain rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W kk b i n v spe Zin Zbw Zbv Zvw).
#[local] Notation jw_B := (@jw_B rc PI sp0 W memc b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_Bra := (@jw_Bra rc PI sp0 W memc b i n v spe BS Zin Zb0 Zbm Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_vra := (@jw_vra rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zvra Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_vpres := (@jw_vpres rc PI B STK sp0 FP ly Sa own lyc Sc W memc v spe Zvwr).
#[local] Notation jw_cv := (@jw_cv rc PI MC_CONSTS_LO MC_CONSTS_HI MCROM sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZCV).
#[local] Notation jw_imgaddr := (@jw_imgaddr rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_tstr := (@jw_tstr rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jw_litab := (@jw_litab rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZIMG).
#[local] Notation jw_str14 := (@jw_str14 rc PI sp0 W memc b i n v spe BS Zin Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 ZIMG).
#[local] Notation jstr_fuel := (@jstr_fuel sp0 i n v spe BS Zin).
#[local] Notation jstr_fuel_eq := (@jstr_fuel_eq sp0 i n v spe BS Zin Zv0).
#[local] Notation jstr_fuel_any := (@jstr_fuel_any sp0 i n v spe BS Zin Zv0).
#[local] Notation jdigits_fuel := (@jdigits_fuel sp0 i n v spe BS Zin).
#[local] Notation jdigits_fuel_any := (@jdigits_fuel_any sp0 i n v spe BS Zin Zv0).
#[local] Notation ew_EiR := (@ew_EiR rc PI sp0 i n v spe BS Zin).
#[local] Notation ew_EiX := (@ew_EiX rc PI sp0 i n v spe BS Zin).
#[local] Notation js_awr_v := (@js_awr_v rc PI B STK sp0 FP ly Sa own lyc Sc W memc v Zvwr).
#[local] Notation js_v_app := (@js_v_app rc sp0 i n v spe BS Zin Zv0 Zv8 Zvm).
#[local] Notation jrest_exp := (@jrest_exp i BS).
#[local] Notation jrest_frac := (@jrest_frac i BS).
#[local] Notation jx_extra := (@jx_extra b BS).
#[local] Notation jbyte_range := (@jbyte_range sp0 i n v spe BS Zin).
#[local] Notation garr8_at := (@garr8_at rc PI sp0 i n v spe BS Zin Zv0).
#[local] Notation st_ok_pi_add_cond := (@st_ok_pi_add_cond rc PI fx).
#[local] Notation U_offm := (@U_offm sp0 i n v spe BS Zin).
#[local] Notation z256 := (@z256 sp0 i n v spe BS Zin Zv0).
#[local] Notation bf_digit_ltu := (@bf_digit_ltu sp0 i n v spe BS Zin Zv0).
#[local] Notation jlen_BZ := (@jlen_BZ n BS ZL).
#[local] Notation jdigits_nd := (@jdigits_nd sp0 i n v spe BS ZL Zin Zv0).
#[local] Notation jdigits_d := (@jdigits_d sp0 i n v spe BS ZL Zin Zv0).
#[local] Notation jdigits_n := (@jdigits_n n BS ZL).
#[local] Notation jrest_exp_n := (@jrest_exp_n i n BS ZL).
#[local] Notation add_breg := (@add_breg rc PI fx sp0 W memc b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation obl_B := (@obl_B rc PI sp0 W memc b i n v spe BS Zin Zb0 Zbm Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation jdig_at_ge := (@jdig_at_ge sp0 i n v spe BS ZL Zin).
#[local] Notation jdig_at_lt := (@jdig_at_lt sp0 i n v spe BS ZL Zin).
#[local] Notation jstr_ge := (@jstr_ge sp0 i n v spe BS ZL Zin).
#[local] Notation bf_hex2 := (@bf_hex2 sp0 i n v spe BS Zin Zv0).
#[local] Notation bf_hex1 := (@bf_hex1 sp0 i n v spe BS Zin Zv0).
#[local] Notation SLP := (@SLP rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS).
#[local] Notation HXP := (@HXP rc SK PI B fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe).
#[local] Notation jm_extra := (@jm_extra b i BS).
#[local] Notation seg_wr := (@JsonScalarSeg_wr.seg_wr rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS Zin Zb0 Zbm Zbw Zbv Zv0 Zv8 Zvm Zvw Zvwr Zvra Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation seg_el := (@JsonScalarSeg_el.seg_el rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 seg_wr).
#[local] Notation seg_ec := (@JsonScalarSeg_ec.seg_ec rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 seg_wr seg_el).
#[local] Notation seg_fl := (@JsonScalarSeg_fl.seg_fl rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 seg_wr seg_ec).
#[local] Notation seg_fc := (@JsonScalarSeg_fc.seg_fc rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 seg_ec seg_fl).
#[local] Notation seg_il := (@JsonScalarSeg_il.seg_il rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 seg_wr seg_fc).
#[local] Notation seg_num0 := (@JsonScalarSeg_num0.seg_num0 rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016 seg_fc seg_il).
#[local] Notation seg_lit := (@JsonScalarSeg_lit.seg_lit rc SK PI B LAWS ABCMP MC_CONSTS_LO MC_CONSTS_HI ASTRLEN MCROM fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbsh Zbw Zbv Zv0 Zv8 Zvm Zvw Zvwr Zvra Zspa Zsp47 Zsp16 ZspS Zsp0 Zsp016 ZIMG ZCV seg_num0).
#[local] Notation seg_hx2 := (@JsonScalarSeg_hx.seg_hx2 rc SK PI B LAWS fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 Zsp0 Zsp016).
#[local] Notation seg_sl := (@JsonScalarSeg_sl.seg_sl rc SK PI B LAWS MC_CONSTS_LO MC_CONSTS_HI AMEMCHR MCROM fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbra Zbw Zbv Zv0 Zv8 Zvm Zvw Zvwr Zvra Zspa Zsp47 Zsp16 ZspS Zsp0 Zsp016 ZIMG ZCV seg_hx2).
#[local] Notation jm_entry := (@JsonScalarSeg_jm.jm_entry rc SK PI B LAWS TL fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS ZL Zin Zb0 Zbm ZBg Zbw Zboi Zbv Zv0 Zv8 Zvm Zvw Zspa Zsp47 Zsp16 ZspS Zsp0 Zsp016).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac ereg q r H := rewrite (ew_EiR _ _ q r) by (cbv; first [lia | reflexivity]); exact H.
Definition jmBx : sv := SOff 35 0.
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).

Ltac jm_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?ly ?own => let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc ly own) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; repeat match goal with H : _ \/ _ |- _ => clear H | H : _ mod _ = _ |- _ => clear H end; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spe - sp0));
      [ reflexivity
      | rewrite ?ew_ewset_other by lia; lazymatch goal with |- context [ew ?Ex 2] => lazymatch goal with H : ew Ex 2 = Z_to_bv 64 spe |- _ => rewrite H end end;
        rewrite unsigned_lit_small by lia; lia
      | cbn; lia | cbn; lia | ] ].

Definition MWm (m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).
Lemma mw_memc : MWm memc.
Proof. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.
Lemma mw_jw : forall m, MWm m -> JW m.
Proof.
intros m [H1 H2]. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). split; [|exact H2].
intros a Ha Hn. apply H1; [exact Ha | lia].
Qed.
Lemma mw_frame : forall m1 m2 E0 rs, MWm m1 ->
  frame_of E0 rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange E0 rs a -> spe - 128 <= a < spe) -> MWm m2.
Proof.
intros m1 m2 E0 rs [A1 A2] HF HG Hw. split.
- intros a Ha Hn. rewrite <- (A1 a Ha Hn). apply (aview_eq_of SEGS). apply HF.
  rewrite unsigned_lit_small by lia. intros Hx. exact (Hn (Hw a Hx)).
- intros a Ha. apply (apresent_grows (w_H W) m1 m2); [exact HG | apply A2, Ha].
Qed.
Ltac mw_tac HM HFr HG :=
  eapply (mw_frame _ _ _ _ HM HFr HG);
  let a := fresh "a" in let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in
  intros a (r & Hr0 & Hr);
  lazymatch type of Hr0 with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr0 end;
  cbn [In] in Hr0;
  repeat (destruct Hr0 as [<- | Hr0]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?ew_ewset_other in Hr by lia;
    first [ lia | lazymatch type of Hr with context [ew ?Ex 2] => lazymatch goal with H : ew Ex 2 = Z_to_bv 64 spe |- _ => rewrite H, unsigned_lit_small in Hr by lia; lia end end ] |]);
  try (destruct Hr0).

Definition JM_CLOB : list (bv 5) := [1; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma jm_clob_kept : forall r : bv 5, reg_in r JM_CLOB = false -> r = 0%bv \/ r = 2%bv \/ r = 3%bv \/ r = 4%bv.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; first [left; reflexivity | right; first [left; reflexivity | right; reflexivity]]] |]).
destruct Hin.
Qed.
Lemma U_subf2 : forall E0 a c x y, ew E0 a = Z_to_bv 64 x -> ew E0 c = Z_to_bv 64 y -> 0 <= y <= x -> x < 2 ^ 64 ->
  U E0 (SAlu ALU_ADD (SMd M_MUL (SOff c 0) (SLit (-1))) (SOff a 0)) = x - y.
Proof.
intros E0 a c x y Ha Hc Hy Hx. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E0 a x Ha), (U_atom E0 c y Hc), U_SLit by lia.
unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (y * (2 ^ 64 - 1) + x) with ((x - y) + y * 2 ^ 64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma U_shadd : forall E0 sb q x, ew E0 sb = Z_to_bv 64 SHADOW_OFF -> ew E0 q = Z_to_bv 64 x -> 0 <= x < 2 ^ 47 ->
  U E0 (SAlu ALU_ADD (SOff sb 0) (SAlu ALU_SRL (SOff q 0) (SLit 3))) = SHADOW_OFF + x / 8 /\
  U E0 (SAlu ALU_ADD (SAlu ALU_SRL (SOff q 0) (SLit 3)) (SOff sb 0)) = SHADOW_OFF + x / 8.
Proof.
intros E0 sb q x Hsb Hq Hx. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E0 sb SHADOW_OFF Hsb), (U_atom E0 q x Hq), U_SLit by (unfold SHADOW_OFF; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
unfold zcanon, M64. rewrite (Z.mod_small (x / 8)) by lia. rewrite !Z.mod_small by (unfold SHADOW_OFF; lia). split; lia.
Qed.
Ltac jm_reg HS r :=
  lazymatch type of HS with st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
  rewrite (st_ok_pi_restrict_reg Hh Ex ss ms r HS);
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
  rewrite denot_lit_U; unfold w64 end.

Lemma mk_weaken : forall m m' (Ev : Z -> Prop), MK m m' (fun _ => False) -> MK m m' Ev.
Proof. intros m m' Ev [H1 H2]. split; [intros a Ha Hn _; apply H1; auto | exact H2]. Qed.
Lemma jm_lit_eq : jbyte BZ i <> 34 -> jscalar BZ i = match jlit BZ i jlit_words with Some t => Some t | None => jnum BZ i end.
Proof.
intros NQ. unfold jscalar. rewrite jlen_BZ. replace (n <=? i) with false by (symmetry; apply Z.leb_gt; lia).
replace (jbyte BZ i =? 34) with false by (symmetry; apply Z.eqb_neq; exact NQ). reflexivity.
Qed.
Lemma jm_str_eq : jbyte BZ i = 34 -> jscalar BZ i = jstr BZ i (i + 1) (length BS).
Proof.
intros Q. unfold jscalar. rewrite jlen_BZ. replace (n <=? i) with false by (symmetry; apply Z.leb_gt; lia).
rewrite Q, Z.eqb_refl. f_equal. unfold BZ. apply length_map.
Qed.
Lemma jm_kept : forall md0' mF (Ev : Z -> Prop), AR SEGS B lyc Sc W memc md0' ->
  (forall a, Ev a -> v <= a < v + 20) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spe - TJSON_SCALAR_STK <= a < spe) -> ~ Ev a -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  (forall a, spe - TJSON_SCALAR_STK <= a < spe -> apresent (w_H W) mF a) ->
  tjson_scalar_kept lyc Sc W memc W mF spe v Ev.
Proof.
intros md0' mF Ev HAR HEv HK HP HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Zspa as Zspa'. pose proof Zvoi as Zvoi'. unfold off_img in Zvoi'.
split; [exact HK|]. split.
{ intros b0 m0 i0 Hin Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc md0' b0 m0 HAR Hin) as (_ & Hb4 & Hbc & _). apply HK; [lia | lia | exact Hn]. }
split.
{ intros a Ha _ _. pose proof (pa_img_range a Ha). pose proof (pa_segs_low a Ha). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
  apply HK; [lia | lia |]. intros He. pose proof (HEv a He). lia. }
split.
{ intros cid pos a Hin Hr Hn. destruct (al_sep _ _ LAWS lyc Sc W memc md0' HAR) as (_ & HF).
  pose proof (proj1 (Forall_forall _ _) HF (cid, pos) Hin) as Hf. cbn [fst snd] in Hf.
  apply HK; [| | exact Hn]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr;
  pose proof (fs_frame_bytes_nonneg cid);
  pose proof (Z.div_le_mono (frame_addr lyc cid pos) alloc_ceiling 8 ltac:(lia) ltac:(lia));
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia));
  pose proof (Z.div_le_mono (fs_frame_bytes cid) alloc_ceiling 8 ltac:(lia) ltac:(lia)); lia. }
split.
{ intros a Ha Hn Hp. apply HP. exact Hp. }
exact HW.
Qed.

Lemma jm_frame_kept : forall E0 rs (m m' : word -> option byte),
  frame_of E0 rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E0 rs a -> spe - 128 <= a < spe) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E0 rs m m' HF Hw a Ha Hn. apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by lia. intros Hx. exact (Hn (Hw a Hx)).
Qed.
Ltac jm_wr :=
  let a := fresh "a" in let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in
  intros a (r & Hr0 & Hr);
  lazymatch type of Hr0 with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr0 end;
  cbn [In] in Hr0;
  repeat (destruct Hr0 as [<- | Hr0]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?ew_ewset_other in Hr by lia;
    first [ lia | lazymatch type of Hr with context [ew ?Ex 2] => lazymatch goal with H : ew Ex 2 = Z_to_bv 64 spe |- _ => rewrite H, unsigned_lit_small in Hr by lia; lia end end ] |]);
  try (destruct Hr0).
Lemma jm_kept_chain : forall mdc' m0 mE mF (Ev : Z -> Prop), AR SEGS B lyc Sc W memc mdc' ->
  (forall a, Ev a -> v <= a < v + 20) ->
  MWm m0 -> MK m0 mE Ev ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) mE a) ->
  (forall a, apresent (w_H W) mE a -> apresent (w_H W) mF a) ->
  (forall a, spe - TJSON_SCALAR_STK <= a < spe -> apresent (w_H W) mF a) ->
  tjson_scalar_kept lyc Sc W memc W mF spe v Ev.
Proof.
intros mdc' m0 mE mF Ev HAR HEv [M1 M2] [K1 K2] HF HG HW. pose proof js_nums as (N1 & N2 & N3 & N4 & N5).
apply (jm_kept mdc' mF Ev HAR HEv); [| | exact HW].
- intros a Ha Hn He. rewrite HF by lia. rewrite K1 by (try exact He; lia). apply M1; lia.
- intros a Ha. apply HG, K2, M2, Ha.
Qed.
Lemma jw_memc : JW memc.
Proof. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.
Lemma js_main : forall (regs : bvmap 5 word) mdc,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc kk ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 b -> getr regs 11 = w64 i -> getr regs 12 = w64 n -> getr regs 13 = w64 v -> spZ regs = spe ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_json_scalar) regs memc mdc)
    (tjson_scalar_post fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk regs b i v BS).
Proof.
intros regs mdc HJ Hra Hra4 Hgp Htp H10 H11 H12 H13 Hsp.
pose proof HJ as (HARc & _).
pose proof js_nums as (N1 & N2 & N3 & N4 & N5). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (jm_entry regs mdc HJ H10 H11 H12 H13 Hsp) as HS.
remember (Eimg (Ereg regs jm_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 spe) by (subst E; rewrite (ew_EiR _ _ 2 (2%bv : bv 5)) by (cbv; first [lia | reflexivity]); unfold spZ in Hsp; rewrite <- Hsp; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew E 3 = getr regs 3) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (subst E; apply ew_EiR; [cbv; lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (subst E; ereg 10%nat (10%bv : bv 5) H10).
assert (E11 : ew E 11 = Z_to_bv 64 i) by (subst E; ereg 11%nat (11%bv : bv 5) H11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (subst E; ereg 12%nat (12%bv : bv 5) H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (subst E; ereg 13%nat (13%bv : bv 5) H13).
assert (E32 : ew E 32 = Z_to_bv 64 (b + i)) by (subst E; exact (ew_EiX regs jm_extra 0 ltac:(cbv; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (jbyte BZ i)) by (subst E; exact (ew_EiX regs jm_extra 1 ltac:(cbv; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (subst E; exact (ew_EiX regs jm_extra 2 ltac:(cbv; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_EiX regs jm_extra 3 ltac:(cbv; lia))).
assert (HAE : env_agree 32 (Ereg regs jm_extra) E) by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (UBx : U E jmBx = SHADOW_OFF) by (unfold jmBx; rewrite (U_atom E 35 SHADOW_OFF E35) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS jmBx [] E (mrestrict (w_H W) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_both3_json_scalar)) with (Z_to_bv 64 (BASE + AF_both3_json_scalar)).
paj_run_tok RUN HS HJ SHOK jsBsp.
{ cbn [ms_mem]. rewrite (U_atom E 32 (b + i) E32) by lia. eapply (obl_of_range SEGS (w_H W) memc E jmBx _ 1 b n (jw_Bra memc jw_memc) UBx); lia. }
{ jm_awr. }

lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Ea := Ex) in * end.
assert (OLDa : forall q, (q < 512)%nat -> ew Ea q = ew E q) by (intros q Hq; unfold Ea; rewrite ?ew_ewset_other by lia; reflexivity).
assert (Ea2 : ew Ea 2 = Z_to_bv 64 spe) by (rewrite OLDa by lia; exact E2).
assert (HM1 : MWm (ms_mem ms)) by (mw_tac mw_memc HFr HG). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK jsBsp.
- rewrite branch_ne_U, (U_atom Ea 33 (jbyte BZ i)), U_SLit in Hc by (try (rewrite OLDa by lia; exact E33); pose proof (jbyte_range i); lia).
  assert (NQ : jbyte BZ i <> 34) by (intros X; rewrite X in Hc; vm_compute in Hc; discriminate Hc). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_LIT. { jm_awr. }
  assert (HM2 : MWm (ms_mem ms0)) by (mw_tac HM1 HFr HG). clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Eb := Ex) in * end.
  assert (OLDb : forall q, (q < 512)%nat -> ew Eb q = ew E q) by (intros q Hq; unfold Eb, Ea; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (Eb2 : ew Eb 2 = Z_to_bv 64 spe) by (rewrite OLDb by lia; exact E2).
  destruct (jw_litab memc jw_memc) as (t1 & t2 & t3 & L8 & Li & _).
  assert (HL0 : 0 <= VAL (A_OBJ 20) < kLowMemEnd) by exact (pa_segs_low _ (Li (VAL (A_OBJ 20)) ltac:(lia))).
  assert (Eb261 : ew Eb (A_OBJ 20) = Z_to_bv 64 (VAL (A_OBJ 20))) by (rewrite OLDb by (unfold A_OBJ, A_TEXT; lia); rewrite <- (HEI (A_OBJ 20) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as RV. cbn [ms_mem restrict] in RV.
  pose proof (field_of_region_any (segs := SEGS) Eb _ 2 spe _ _ _ _ _ (-128) 8 (SOff 34 0) RV ltac:(rewrite Eb2; apply unsigned_lit_small; lia) ltac:(cbn; tauto) ltac:(lia)) as F0.
  pose proof (field_of_region_any (segs := SEGS) Eb _ 2 spe _ _ _ _ _ (-120) 8 (SOff 13 0) RV ltac:(rewrite Eb2; apply unsigned_lit_small; lia) ltac:(cbn; tauto) ltac:(lia)) as F8.
  pose proof (field_of_region_any (segs := SEGS) Eb _ 2 spe _ _ _ _ _ (-112) 8 (SOff 11 0) RV ltac:(rewrite Eb2; apply unsigned_lit_small; lia) ltac:(cbn; tauto) ltac:(lia)) as F16.
  pmkst HS.
  eapply SRr_bind.
  { apply (seg_lit 0 (ms_regs ms0) (ms_mem ms0) _ ltac:(lia) HJ (mw_jw _ HM2)).
    - jm_reg HS (2%bv : bv 5). f_equal. rewrite (U_atom_off Eb 2 spe (-128) Eb2) by lia. lia.
    - prreg HS (3%bv : bv 5) R3. rewrite R3, OLDb, E3 by lia. exact Hgp.
    - prreg HS (4%bv : bv 5) R4. rewrite R4, OLDb, E4 by lia. exact Htp.
    - jm_reg HS (25%bv : bv 5). rewrite U_SLit. reflexivity.
    - jm_reg HS (24%bv : bv 5). rewrite U_SLit. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    - jm_reg HS (23%bv : bv 5). f_equal. change 261%nat with (A_OBJ 20).
      rewrite (proj1 (U_shadd Eb 35 (A_OBJ 20) (VAL (A_OBJ 20)) ltac:(rewrite OLDb by lia; exact E35) Eb261 ltac:(lia))). lia.
    - jm_reg HS (9%bv : bv 5). f_equal. change 261%nat with (A_OBJ 20). rewrite (U_atom Eb (A_OBJ 20) (VAL (A_OBJ 20)) Eb261) by lia. lia.
    - jm_reg HS (26%bv : bv 5). f_equal. apply (U_subf2 Eb 12 11 n i); [rewrite OLDb by lia; exact E12 | rewrite OLDb by lia; exact E11 | lia | lia].
    - jm_reg HS (18%bv : bv 5). f_equal. apply (U_atom Eb 32 (b + i)); [rewrite OLDb by lia; exact E32 | lia].
    - jm_reg HS (8%bv : bv 5). f_equal.
      exact (proj2 (U_shadd Eb 35 32 (b + i) ltac:(rewrite OLDb by lia; exact E35) ltac:(rewrite OLDb by lia; exact E32) ltac:(lia))).
    - jm_reg HS (27%bv : bv 5). f_equal. apply (U_atom Eb 35 SHADOW_OFF); [rewrite OLDb by lia; exact E35 | unfold SHADOW_OFF; lia].
    - jm_reg HS (19%bv : bv 5). f_equal. apply (U_atom Eb 12 n); [rewrite OLDb by lia; exact E12 | lia].
    - jm_reg HS (20%bv : bv 5). f_equal. apply (U_atom Eb 10 b); [rewrite OLDb by lia; exact E10 | lia].
    - replace (spe - 128) with (spe + -128) by lia.
      replace (2 ^ 64 - 1 - b) with (bv_unsigned (sv_denot Eb (SOff 34 0)) mod 2 ^ (8 * Z.of_N 8)); [exact F0|].
      change (bv_unsigned (sv_denot Eb (SOff 34 0))) with (U Eb (SOff 34 0)).
      rewrite (U_atom Eb 34 (2 ^ 64 - 1 - b)) by (try (rewrite OLDb by lia; exact E34); lia). apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia.
    - replace (spe - 120) with (spe + -120) by lia.
      replace v with (bv_unsigned (sv_denot Eb (SOff 13 0)) mod 2 ^ (8 * Z.of_N 8)); [exact F8|].
      change (bv_unsigned (sv_denot Eb (SOff 13 0))) with (U Eb (SOff 13 0)).
      rewrite (U_atom Eb 13 v) by (try (rewrite OLDb by lia; exact E13); lia). apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia.
    - replace (spe - 112) with (spe + -112) by lia.
      replace i with (bv_unsigned (sv_denot Eb (SOff 11 0)) mod 2 ^ (8 * Z.of_N 8)); [exact F16|].
      change (bv_unsigned (sv_denot Eb (SOff 11 0))) with (U Eb (SOff 11 0)).
      rewrite (U_atom Eb 11 i) by (try (rewrite OLDb by lia; exact E11); lia). apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia.
    - exact NQ.
    - reflexivity. }
  intros W' c' _ (HW' & regsE & memE & mdE & Hc' & HJE & R2E & R3E & R4E & Hres). subst W' c'.
  change (skipn 0 jlit_words) with jlit_words in Hres. unfold tjson_scalar_post. change (map bv_unsigned BS) with BZ. rewrite (jm_lit_eq NQ).
  remember (match jlit BZ i jlit_words with Some t => Some t | None => jnum BZ i end) as res eqn:Hres_eq.
  clear Hres_eq.
  assert (MKv : MK (ms_mem ms0) memE (fun a => v <= a < v + 20)).
  { destruct res as [[[[e kd] s] l]|]; [exact (proj2 (proj2 (proj2 (proj2 Hres)))) | apply mk_weaken; exact (proj2 Hres)]. }
  pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
  pose proof Zvoi as Zvoi'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Zvoi'.
  pose proof Zboi as Zboi'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Zboi'.
  pose proof Zbw as Zbw'. pose proof Zvw as Zvw'. pose proof Zbv as Zbv'.
  assert (Eb241 : ew Eb (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (rewrite OLDb by (unfold A_OBJ, A_TEXT; lia); rewrite <- (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
  assert (Eb253 : ew Eb (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (rewrite OLDb by (unfold A_OBJ, A_TEXT; lia); rewrite <- (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
  jafter_stretch_pi HS 40%nat regsE (mrestrict (w_H W) memE) JM_CLOB A_RET HS2.
  match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
  { intros r0 Hr0. cbn [ms_regs restrict]. destruct (jm_clob_kept r0 Hr0) as [-> | [-> | [-> | ->]]]; [rewrite !getr_zero; reflexivity | exact R2E | exact R3E | exact R4E]. }
  { cbn [ms_mem restrict]. destruct MKv as [MK1 MK2].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) memE 2 spe); [rewrite Eb2; apply unsigned_lit_small; lia | | exact MK2].
      intros a Ha. apply MK1; lia.
    - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) memE (A_OBJ 0) (VAL (A_OBJ 0))); [rewrite Eb241; apply unsigned_lit_small; lia | | exact MK2].
      intros a Ha. apply MK1; lia.
    - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) memE (A_OBJ 12) (VAL (A_OBJ 12))); [rewrite Eb253; apply unsigned_lit_small; lia | | exact MK2].
      intros a Ha. apply MK1; lia.
    - apply (region_kept_aview Eb (w_H W) (ms_mem ms0) memE 32 (b + i)); [rewrite OLDb, E32 by lia; apply unsigned_lit_small; lia | | exact MK2].
      intros a Ha. apply MK1; clear - Ha Zbw Zbv Zin Zb0 N1 N2 N3 N4 N5; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?E0 ?k0 ?l0) _ _ => remember (havoc E0 k0 l0) as Ec eqn:HEc in HS end.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [assumption | cbv; lia]).
  assert (OLDc : forall q, (q < 40)%nat -> ew Ec q = ew Eb q) by (intros q Hq; rewrite HEc; apply ew_havoc_old; exact Hq).
  assert (HAEb : env_agree 32 (Ereg regs jm_extra) Eb) by (unfold Eb, Ea; env_agree_chain HAE).
  assert (HAEc : env_agree 32 (Ereg regs jm_extra) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [lia | exact HAEb]).
  assert (G46 : ew Ec 46 = getr regsE 10) by (rewrite HEc; reflexivity).
  assert (Ec2 : ew Ec 2 = Z_to_bv 64 spe) by (rewrite OLDc by lia; exact Eb2).
  clear HEc.
  assert (SHOKc : sh_ok SEGS jmBx [] Ec (mrestrict (w_H W) memE)) by constructor.
  paj_run_tok RUN HS HJE SHOKc jsBsp.
  { jm_awr. }
  lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?M)) => rename M into msF end.
  assert (FKf : forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memE a)
    by (apply (jm_frame_kept _ _ _ _ HFr); clear Zbw' Zvw' Zbv' Zvoi' Zboi' Zbw Zvw Zbv Zv8 Zsp16 Zsp016 L8 NQ HcellR HgotR; jm_wr).
  assert (HGf : forall a, apresent (w_H W) memE a -> apresent (w_H W) (ms_mem msF) a) by (intros a Ha; apply (apresent_grows (w_H W) memE (ms_mem msF)); [exact HG | exact Ha]).
  pose proof HJE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
  assert (HWf : forall a, spe - TJSON_SCALAR_STK <= a < spe -> apresent (w_H W) (ms_mem msF) a) by (intros a Ha; apply HpF; lia).
  clear HF HFr HG.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists lyc, Sc, rg, m, d end.
  split; [rewrite R1, OLDc, OLDb, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJE|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs jm_extra HS); [exact HAEc | vm_compute; reflexivity]|].
  split; [reflexivity|]. split; [reflexivity|].
  rewrite Hsp. rewrite R10, G46.
  destruct res as [[[[e kd] s] l]|].
  + destruct Hres as (He & Hv1 & Hv2 & Hv3 & MKs).
    split; [exact He|].
    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem msF) v 8 (b + s)); [intros k Hk; apply FKf; lia | exact Hv1]|].
    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem msF) (v + 8) 8 l); [intros k Hk; apply FKf; lia | exact Hv2]|].
    split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem msF) (v + 16) 4 kd); [intros k Hk; apply FKf; lia | exact Hv3]|].
    exact (jm_kept_chain mdc _ _ _ _ HARc (fun a H => H) HM2 MKs FKf HGf HWf).
  + destruct Hres as (He & MKs). split; [exact He|].
    exact (jm_kept_chain mdc _ _ _ _ HARc (fun a H => False_ind _ H) HM2 MKs FKf HGf HWf).
- rewrite branch_ne_U, (U_atom Ea 33 (jbyte BZ i)), U_SLit in Hc by (try (rewrite OLDa by lia; exact E33); pose proof (jbyte_range i); lia).
  apply negb_false_iff, Z.eqb_eq in Hc. change (34 mod 2 ^ 64) with 34 in Hc. rename Hc into Q.
  assert (Ea11 : ew Ea 11 = Z_to_bv 64 i) by (rewrite OLDa by lia; exact E11).
  assert (Ea12 : ew Ea 12 = Z_to_bv 64 n) by (rewrite OLDa by lia; exact E12).
  paj_run_tok RUN HS HJ SHOK jsBsp. { jm_awr. }
  assert (HMa : MWm (ms_mem ms0)) by (mw_tac HM1 HFr HG). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK jsBsp.
  + rewrite branch_geu_U, (U_atom_off Ea 11 i 1 Ea11), (U_atom Ea 12 n Ea12) in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc.
    assert (JN : jstr BZ i (i + 1) (length BS) = None).
    { pose proof jlen_BZ as JL0. remember (length BS) as L eqn:HLn. destruct L; cbn [jstr]; [reflexivity|]. rewrite JL0. replace (n <=? i + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    unfold tjson_scalar_post. change (map bv_unsigned BS) with BZ. rewrite (jm_str_eq Q), JN.
    paj_run_tok RUN HS HJ SHOK jsBsp. { jm_awr. }
    assert (FKf : forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a)
      by (apply (jm_frame_kept _ _ _ _ HFr); jm_wr).
    assert (HGf : forall a, apresent (w_H W) (ms_mem ms0) a -> apresent (w_H W) (ms_mem ms1) a) by (intros a Ha; apply (apresent_grows (w_H W) (ms_mem ms0) (ms_mem ms1)); [exact HG | exact Ha]).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
    assert (HWf : forall a, spe - TJSON_SCALAR_STK <= a < spe -> apresent (w_H W) (ms_mem ms1) a) by (intros a Ha; apply HpF; lia).
    clear HF HFr HG.
    assert (HAEa : env_agree 32 (Ereg regs jm_extra) Ea) by (unfold Ea; env_agree_chain HAE).
    prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. cbv beta.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists lyc, Sc, rg, m, d end.
    split; [rewrite R1, OLDa, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs jm_extra HS); [exact HAEa | vm_compute; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|].
    rewrite Hsp. split; [rewrite R10; reflexivity|].
    exact (jm_kept_chain mdc _ _ _ _ HARc (fun a H => False_ind _ H) HMa (mk_refl _ _) FKf HGf HWf).
  + rewrite branch_geu_U, (U_atom_off Ea 11 i 1 Ea11), (U_atom Ea 12 n Ea12) in Hc by lia.
    apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hj1.
    paj_run_to_tok RUNTO HS HJ SHOK jsBsp A_SL. { jm_awr. }
    assert (HM2 : MWm (ms_mem ms1)) by (mw_tac HMa HFr HG). clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Eb := Ex) in * end.
    assert (OLDb : forall q, (q < 512)%nat -> ew Eb q = ew E q) by (intros q Hq; unfold Eb, Ea; rewrite ?ew_ewset_other by lia; reflexivity).
    assert (Eb2 : ew Eb 2 = Z_to_bv 64 spe) by (rewrite OLDb by lia; exact E2).
    assert (Eb10 : ew Eb 10 = Z_to_bv 64 b) by (rewrite OLDb by lia; exact E10).
    assert (Eb11 : ew Eb 11 = Z_to_bv 64 i) by (rewrite OLDb by lia; exact E11).
    assert (Eb12 : ew Eb 12 = Z_to_bv 64 n) by (rewrite OLDb by lia; exact E12).
    assert (Eb13 : ew Eb 13 = Z_to_bv 64 v) by (rewrite OLDb by lia; exact E13).
    assert (Eb32 : ew Eb 32 = Z_to_bv 64 (b + i)) by (rewrite OLDb by lia; exact E32).
    assert (Eb34 : ew Eb 34 = Z_to_bv 64 (2 ^ 64 - 1 - b)) by (rewrite OLDb by lia; exact E34).
    assert (Eb35 : ew Eb 35 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDb by lia; exact E35).
    pose proof (jw_str14 memc jw_memc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S14i).
    pose proof (pa_segs_low _ (S14i (VAL (A_OBJ 19)) ltac:(cbn [length]; lia))) as H19R.
    assert (Eb260 : ew Eb (A_OBJ 19) = Z_to_bv 64 (VAL (A_OBJ 19))) by (rewrite OLDb by (unfold A_OBJ, A_TEXT; lia); rewrite <- (HEI (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
    pmkst HS.
    eapply SRr_bind.
    { apply (seg_sl (length BS) (ms_regs ms1) (ms_mem ms1) _ (i + 1) HJ (mw_jw _ HM2)).
      - jm_reg HS (2%bv : bv 5). f_equal. rewrite (U_atom_off Eb 2 spe (-128) Eb2) by lia. lia.
      - jm_reg HS (3%bv : bv 5). rewrite U_SOff, Z.add_0_r. unfold zcanon, M64.
        rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (ew Eb 3)) as RR; unfold bv_modulus in RR; change (Z.of_N 64) with 64 in RR; lia).
        rewrite Z_to_bv_bv_unsigned, OLDb, E3 by lia. exact Hgp.
      - jm_reg HS (4%bv : bv 5). rewrite U_SOff, Z.add_0_r. unfold zcanon, M64.
        rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (ew Eb 4)) as RR; unfold bv_modulus in RR; change (Z.of_N 64) with 64 in RR; lia).
        rewrite Z_to_bv_bv_unsigned, OLDb, E4 by lia. exact Htp.
      - jm_reg HS (20%bv : bv 5). f_equal. apply (U_atom Eb 10 b Eb10). lia.
      - jm_reg HS (25%bv : bv 5). f_equal. rewrite (U_atom_off Eb 11 i 1 Eb11) by lia. reflexivity.
      - jm_reg HS (8%bv : bv 5). f_equal. rewrite (U_atom Eb 11 i Eb11) by lia. lia.
      - jm_reg HS (26%bv : bv 5). rewrite U_SLit. reflexivity.
      - jm_reg HS (13%bv : bv 5). rewrite U_SLit. reflexivity.
      - jm_reg HS (14%bv : bv 5). rewrite U_SLit. reflexivity.
      - jm_reg HS (21%bv : bv 5). f_equal. change 260%nat with (A_OBJ 19). apply (U_atom Eb (A_OBJ 19) (VAL (A_OBJ 19)) Eb260). lia.
      - jm_reg HS (19%bv : bv 5). f_equal. apply (U_atom Eb 12 n Eb12). lia.
      - jm_reg HS (24%bv : bv 5). f_equal. apply (U_atom Eb 34 (2 ^ 64 - 1 - b) Eb34). lia.
      - jm_reg HS (9%bv : bv 5). f_equal. apply (U_atom Eb 11 i Eb11). lia.
      - jm_reg HS (23%bv : bv 5). f_equal. apply (U_atom Eb 13 v Eb13). lia.
      - jm_reg HS (27%bv : bv 5). f_equal. apply (U_atom Eb 35 SHADOW_OFF Eb35). unfold SHADOW_OFF; lia.
      - jm_reg HS (18%bv : bv 5). f_equal. apply (U_atom Eb 32 (b + i) Eb32). lia.
      - lia.
      - rewrite ZL. lia. }
  intros W' c' _ (HW' & regsE & memE & mdE & Hc' & HJE & R2E & R3E & R4E & Hres). subst W' c'.
    unfold tjson_scalar_post. change (map bv_unsigned BS) with BZ. rewrite (jm_str_eq Q).
    remember (jstr BZ i (i + 1) (length BS)) as res eqn:Hres_eq.
    clear Hres_eq.
    assert (MKv : MK (ms_mem ms1) memE (fun a => v <= a < v + 20)).
    { destruct res as [[[[e kd] s] l]|]; [exact (proj2 (proj2 (proj2 (proj2 Hres)))) | apply mk_weaken; exact (proj2 Hres)]. }
    pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
    pose proof Zvoi as Zvoi'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Zvoi'.
    pose proof Zboi as Zboi'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Zboi'.
    pose proof Zbw as Zbw'. pose proof Zvw as Zvw'. pose proof Zbv as Zbv'.
    assert (Eb241 : ew Eb (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (rewrite OLDb by (unfold A_OBJ, A_TEXT; lia); rewrite <- (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
    assert (Eb253 : ew Eb (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (rewrite OLDb by (unfold A_OBJ, A_TEXT; lia); rewrite <- (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
    jafter_stretch_pi HS 40%nat regsE (mrestrict (w_H W) memE) JM_CLOB A_RET HS2.
    match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
    { intros r0 Hr0. cbn [ms_regs restrict]. destruct (jm_clob_kept r0 Hr0) as [-> | [-> | [-> | ->]]]; [rewrite !getr_zero; reflexivity | exact R2E | exact R3E | exact R4E]. }
    { cbn [ms_mem restrict]. destruct MKv as [MK1 MK2].
      repeat apply Forall_cons; try apply Forall_nil.
      - apply (region_kept_aview Eb (w_H W) (ms_mem ms1) memE 2 spe); [rewrite Eb2; apply unsigned_lit_small; lia | | exact MK2].
        intros a Ha. apply MK1; lia.
      - apply (region_kept_aview Eb (w_H W) (ms_mem ms1) memE (A_OBJ 0) (VAL (A_OBJ 0))); [rewrite Eb241; apply unsigned_lit_small; lia | | exact MK2].
        intros a Ha. apply MK1; lia.
      - apply (region_kept_aview Eb (w_H W) (ms_mem ms1) memE (A_OBJ 12) (VAL (A_OBJ 12))); [rewrite Eb253; apply unsigned_lit_small; lia | | exact MK2].
        intros a Ha. apply MK1; lia.
      - apply (region_kept_aview Eb (w_H W) (ms_mem ms1) memE 32 (b + i)); [rewrite OLDb, E32 by lia; apply unsigned_lit_small; lia | | exact MK2].
        intros a Ha. apply MK1; clear - Ha Zbw Zbv Zin Zb0 N1 N2 N3 N4 N5; lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ (havoc ?E0 ?k0 ?l0) _ _ => remember (havoc E0 k0 l0) as Ec eqn:HEc in HS end.
    assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [assumption | cbv; lia]).
    assert (OLDc : forall q, (q < 40)%nat -> ew Ec q = ew Eb q) by (intros q Hq; rewrite HEc; apply ew_havoc_old; exact Hq).
    assert (HAEb : env_agree 32 (Ereg regs jm_extra) Eb) by (unfold Eb, Ea; env_agree_chain HAE).
    assert (HAEc : env_agree 32 (Ereg regs jm_extra) Ec) by (rewrite HEc; apply env_agree_havoc_ge; [lia | exact HAEb]).
    assert (G46 : ew Ec 46 = getr regsE 10) by (rewrite HEc; reflexivity).
    assert (Ec2 : ew Ec 2 = Z_to_bv 64 spe) by (rewrite OLDc by lia; exact Eb2).
    clear HEc.
    assert (SHOKc : sh_ok SEGS jmBx [] Ec (mrestrict (w_H W) memE)) by constructor.
    paj_run_tok RUN HS HJE SHOKc jsBsp.
    { jm_awr. }
    lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?M)) => rename M into msF end.
    assert (FKf : forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memE a)
      by (apply (jm_frame_kept _ _ _ _ HFr); try clear Zbw'; try clear Zvw'; try clear Zbv'; try clear Zvoi'; try clear Zboi'; try clear Zbw; try clear Zbv; try clear Zvw; try clear Zv8; try clear Zsp16; try clear Zsp016; try clear L8; try clear NQ; try clear HcellR; try clear HgotR; jm_wr).
    assert (HGf : forall a, apresent (w_H W) memE a -> apresent (w_H W) (ms_mem msF) a) by (intros a Ha; apply (apresent_grows (w_H W) memE (ms_mem msF)); [exact HG | exact Ha]).
    pose proof HJE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
    assert (HWf : forall a, spe - TJSON_SCALAR_STK <= a < spe -> apresent (w_H W) (ms_mem msF) a) by (intros a Ha; apply HpF; lia).
    clear HF HFr HG.
    prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. cbv beta.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists lyc, Sc, rg, m, d end.
    split; [rewrite R1, OLDc, OLDb, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJE|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs jm_extra HS); [exact HAEc | vm_compute; reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|].
    rewrite Hsp. rewrite R10, G46.
    destruct res as [[[[e kd] s] l]|].
    * destruct Hres as (He & Hv1 & Hv2 & Hv3 & MKs).
      split; [exact He|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem msF) v 8 (b + s)); [intros k Hk; apply FKf; lia | exact Hv1]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem msF) (v + 8) 8 l); [intros k Hk; apply FKf; lia | exact Hv2]|].
      split; [apply (val_mem_kept SEGS (w_H W) (w_H W) memE (ms_mem msF) (v + 16) 4 kd); [intros k Hk; apply FKf; lia | exact Hv3]|].
      exact (jm_kept_chain mdc _ _ _ _ HARc (fun a H => H) HM2 MKs FKf HGf HWf).
    * destruct Hres as (He & MKs). split; [exact He|].
      exact (jm_kept_chain mdc _ _ _ _ HARc (fun a H => False_ind _ H) HM2 MKs FKf HGf HWf).

Qed.
End w.

Section ge.
Context {fx : YK11.FPState}.
Let RUNg := paj_run B LAWS.
Let RETg := paj_ret_at (PL := PL_both3_0) (PI := PI).
Definition jgBsp : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition gSP : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition ge_regions : smem := [ stack_region 128 ].
Definition ge_facts : facts :=
  mkFacts [ (2%nat, gSP); (11%nat, mkAF 0 (2 ^ 64 - 1) 0); (12%nat, mkAF 0 (2 ^ 64 - 1) 0) ]
    [ mkAC BC_GEU (SOff 11 0) (SOff 12 0) ] [].
Definition ss_ge : sstate := mkSS AF_both3_json_scalar sr_atoms ge_regions None ge_facts.
Lemma js_ge : forall (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sa : astate) (W0 : world SEGS) (mem0 : word -> option byte)
  (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (kk b i n v spe : Z) (BS : list byte) (regs : bvmap 5 word) mdc,
  ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc kk ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 11 = w64 i -> getr regs 12 = w64 n ->
  0 <= i < 2 ^ 64 -> 0 <= n -> n <= i ->
  Z.of_nat (length BS) = n ->
  spZ regs = spe -> 2 ^ 46 + 128 <= spe <= 2 ^ 47 -> spe mod 16 = 0 ->
  alloc_ceiling <= spe - TJSON_SCALAR_STK -> sp0 - STK <= spe - TJSON_SCALAR_STK -> spe <= sp0 ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_json_scalar) regs memc mdc)
    (tjson_scalar_post fx STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk regs b i v BS).
Proof.
intros STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v spe BS regs mdc HJ Hra H11 H12 Hi Hn Hni HL Hsp Hspr Hsp16 Hspa HspS Hsp0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : TJSON_SCALAR_STK = 8320) by reflexivity.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; cbv; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; cbv; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 i) by (subst E; rewrite Eimg_low by (unfold A_TEXT; cbv; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (n mod 2 ^ 64)).
{ subst E; rewrite Eimg_low by (unfold A_TEXT; cbv; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
pose proof (Z.mod_pos_bound n (2 ^ 64) ltac:(lia)) as Hnm. pose proof (Z.mod_le n (2 ^ 64) ltac:(lia) ltac:(lia)) as Hnle.
assert (Usp : bv_unsigned (ew E 2) = spe) by (rewrite E2; exact Hsp).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_ge (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_json_scalar)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ge. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, stack_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn. exact (conj I I).
  - split; [|split; [|exact I]].
    + cbn [ge_facts f_atoms atoms_ok]. unfold afact_ok, gSP. cbn [af_lo af_hi af_al2].
      rewrite Usp, E11, E12, !unsigned_lit_small by lia.
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
    + cbn [ge_facts f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_atom E 11 i E11), (U_atom E 12 (n mod 2 ^ 64) E12) by lia. apply negb_true_iff. apply Z.ltb_ge. lia. }
assert (SHOK : sh_ok SEGS (SOff 35 0) [] E (mrestrict (w_H W) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_both3_json_scalar)) with (Z_to_bv 64 (BASE + AF_both3_json_scalar)).
paj_run_tok RUNg HS HJ SHOK jgBsp.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?lyq ?ownq => let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (spe - sp0)); [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_nil. }

assert (FK : forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 128 <= a < spe) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ apply (jt_frame_kept E (ss_mem ss_ge) (w_H W) memc (ms_mem ms) (spe - 128) spe HFr).
  intros a (r & Hr0 & Hr). unfold ss_ge, ge_regions, stack_region in Hr0. cbn [ss_mem In] in Hr0. destruct Hr0 as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp in Hr. lia. }
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs ([] : list word) HS HAE ltac:(vm_compute; reflexivity)) as HPT.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
eapply (RETg W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tjson_scalar_post.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?d = _ /\ _ => exists lyc, Sc, rg, mm, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split; [exact HPT|]. split; [reflexivity|]. split; [reflexivity|].
assert (HN : jscalar (map bv_unsigned BS) i = None).
{ unfold jscalar. replace (jlen (map bv_unsigned BS) <=? i) with true; [reflexivity|].
  symmetry. apply Z.leb_le. unfold jlen. rewrite length_map, HL. lia. }
rewrite HN. split; [cbn [ms_regs]; rewrite R10; reflexivity|].
assert (HKall : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJSON_SCALAR_STK <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a) by (intros a Ha Hx; apply FK; [lia | rewrite Hsp in Hx; lia]).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
split; [cbn [ms_mem]; intros a Ha Hx _; apply HKall; assumption|].
split.
{ cbn [ms_mem]. intros p m2 q Hp Hq _.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc p m2 HAR Hp) as (_ & M4096 & Hc2 & _).
  apply HKall; [lia | rewrite Hsp; lia]. }
split.
{ cbn [ms_mem]. intros a Hai _ _. pose proof (pa_segs_low a Hai). apply HKall; [lia | rewrite Hsp; lia]. }
split.
{ cbn [ms_mem]. intros cid pos a Hf Hr _.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf0 & Hfc & Hfa).
  pose proof (fs_frame_bytes_nonneg cid). pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(lia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)).
  apply HKall; [unfold kHighShadowEnd in *; lia | rewrite Hsp; unfold kLowMemEnd, kHighShadowEnd in *; lia]. }
split.
{ cbn [ms_mem]. intros a Ha Hx Hp. apply (apresent_grows (w_H W) memc (ms_mem ms)); [exact HG | exact Hp]. }
cbn [ms_mem]. intros a Ha. apply (apresent_grows (w_H W) memc (ms_mem ms)); [exact HG|]. apply Hpres. rewrite Hsp in Ha. lia.
Qed.
End ge.
Theorem pb_json_scalar : tjson_scalar_spec.
Proof.
unfold tjson_scalar_spec.
intros fq STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc kk regs b i n v BS ch
HJc HROD HCV HROI Hra Hra4 Hgp Htp H10 H11 H12 H13 Hch Hal16 HspS Hsp0 Hi HL Hbn HB Hv0 Hv8 Hv63 Hvm Hvw Hvoi Hvwr Hvra Hvsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hs16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HSTK : TJSON_SCALAR_STK = 8320) by reflexivity.
assert (Zspa : alloc_ceiling <= spZ regs - TJSON_SCALAR_STK) by lia.
assert (Zsp47 : spZ regs <= 2 ^ 47) by lia.
assert (Zspr : 2 ^ 46 + 128 <= spZ regs) by lia.
destruct (Z_lt_le_dec i n) as [Hlt | Hge].
- destruct (HB Hlt) as (HBg & Hb0 & Hbn63 & Hbm & Hbra & Hbsh & Hbw & Hboi & Hbv).
  pose proof (tjson_img_of_ro lyc Sc W memc mdc HAR HROD HROI) as HIMG.
  eapply (js_main (fx := fq) STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v (spZ regs) BS);
    try eassumption; try lia; try reflexivity.
- eapply (js_ge (fx := fq) STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc kk b i n v (spZ regs) BS);
    try eassumption; try lia.
Qed.

End h.
End f.
End d.
