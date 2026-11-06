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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalar.v, with its module paths and module names changed; 62 of its 157 lines of code are new or changed and 706 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryShapes DiscoArm3JsonJs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model jtok_is_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition TJTOK_IS_STK : Z := 48 + 2 * ESTACK.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.

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
Definition tjson_scalar_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
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
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (b i n v : Z) (BS : list byte) ch,
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

Definition tjtok_is_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (kind vk vn : Z)
  (P T : list byte) : world SEGS -> config -> Prop :=
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
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_jtok_is) regs mem md)
    (tjtok_is_post fq regs ly S W mem md kind vk vn P T).

End h.
End f.
End d.
