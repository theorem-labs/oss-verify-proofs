(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 2047 of its 2116 lines of code are new or changed and 300 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacDiscoTableAge.v; 45 of its 98 lines of code are new or changed and 2063 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK06.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YI0m YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c disco_table_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Definition REAC_DISCO_TABLE_OBSERVE_STK : Z := 96 + 2 * ESTACK.
Definition treac_disco_table_observe_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp t : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp) -> ~ (t <= a < t + 400) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (t <= b + i < t + 400) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (t <= a < t + 400) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition treac_disco_table_observe_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (t s ow now : Z) (T G : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (T' : list byte) (ret : Z),
    c2 = mkCfg (YK11.mkst (fx := fq) regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ YK11.getr regs2 10 = w64 ret /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    treac_disco_table_observe_kept lyc Sc W memc W2 mem2 (spZ regs) t /\
    garr8 SEGS (mrestrict (w_H W2) mem2) t (map (fun b : byte => bv_unsigned b) T') /\ length T' = 400%nat /\
    garr8 SEGS (mrestrict (w_H W2) mem2) s (map (fun b : byte => bv_unsigned b) G) /\
    reac_disco_table_observe_c.observe_model T G ow now T' ret /\
    disco_table_c.tbl_T1 T' /\ disco_table_c.tbl_T2 T' /\ disco_table_c.tbl_T3 T' /\
    (disco_table_c.tbl_T4 T -> disco_table_c.tbl_T4 T').
Definition treac_disco_table_observe_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (t s ow now : Z) (T G : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
  YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 10 = w64 t -> YK11.getr regs 11 = w64 s -> YK11.getr regs 12 = w64 ow -> YK11.getr regs 13 = w64 now ->
  -2 ^ 31 <= ow < 2 ^ 31 -> 0 <= now < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK -> spZ regs <= sp0 ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> amem_range t 400 ->
  (spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK) ->
  (forall a, t <= a < t + 400 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
  garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T) -> length T = 400%nat ->
  0 < s -> s + 24 <= 2 ^ 63 -> amem_range s 24 ->
  s mod 8 = 0 -> (forall a, s <= a < s + 24 -> apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 ->
  (spZ regs <= s \/ s + 24 <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK) ->
  shadow_hull_vis (aview SEGS (w_H W) memc) s 24 ->
  garr8 SEGS (mrestrict (w_H W) memc) s (map (fun b : byte => bv_unsigned b) G) -> length G = 24%nat ->
  ((exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= s /\ s + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 24 <= b + req_size m)) ->
  s + 24 <= t \/ t + 400 <= s ->
  disco_table_c.tbl_T1 T -> disco_table_c.tbl_T2 T -> disco_table_c.tbl_T3 T ->
  disco_table_c.sighting_S1 G -> disco_table_c.sighting_S2 G ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_disco_table_observe) regs memc mdc)
    (treac_disco_table_observe_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t s ow now T G).
End h.
End f.
End d.
