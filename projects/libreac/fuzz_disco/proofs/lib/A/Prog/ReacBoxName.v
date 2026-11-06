(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 227 of its 280 lines of code are new or changed and 3287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/SbDec.v, with its module names and numbers changed; 121 of its 181 lines of code are new or changed and 220 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec DiscoRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition MC_CONSTS_LO : Z := 0x10368.
Definition MC_CONSTS_HI : Z := 0x10388.
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
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ASSF5 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f5) 0xf5.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis HSBDEC : tsb_dec_spec B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Definition REAC_BOX_NAME_STK : Z := 592 + 2 * ESTACK.
Definition rbn_str (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
  amem_range a (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem x <> None).
Definition rbn_stem (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  rbn_str W mem a s /\ (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x).
Definition rbn_lit (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x).
Definition rbn_ro (q sz : Z) : Prop :=
  In (q, sz) disco_globs /\ (sz mod 8 = 0 \/ In (q + sz, 8 - sz mod 8) disco_glob_tails).
Definition rbn_img (W : world SEGS) (mem : word -> option byte) : Prop :=
  exists t1 t2 t3 : Z,
  VAL (A_OBJ 26) mod 8 = 0 /\ (forall x, VAL (A_OBJ 26) <= x < VAL (A_OBJ 26) + 24 -> in_img SEGS x) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 26)) 24 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 26)) 8 t1 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 26) + 8) 8 t2 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 26) + 16) 8 t3 /\
  rbn_stem W mem t1 (bn_STEM 1) /\ rbn_stem W mem t2 (bn_STEM 2) /\ rbn_stem W mem t3 (bn_STEM 3) /\
  rbn_stem W mem (VAL (A_OBJ 27)) (bn_STEM 0) /\
  rbn_lit W mem (VAL (A_OBJ 28)) [32; 40] /\
  rbn_lit W mem (VAL (A_OBJ 29)) [32; 105; 110; 32; 47; 32] /\
  rbn_lit W mem (VAL (A_OBJ 30)) [32; 111; 117; 116; 41] /\
  rbn_ro (VAL (A_OBJ 26)) 24 /\ rbn_ro t1 7 /\ rbn_ro t2 7 /\ rbn_ro t3 8 /\ rbn_ro (VAL (A_OBJ 27)) 5 /\
  rbn_ro (VAL (A_OBJ 28)) 3 /\ rbn_ro (VAL (A_OBJ 29)) 7 /\ rbn_ro (VAL (A_OBJ 30)) 6.
Definition rbn_said (lyc : alayout) (Sc : astate) (W : world SEGS) (mem : word -> option byte)
  (sp sp0 said : Z) (sd : list Z) : Prop :=
  (said = 0 /\ sd = []) \/
  (said <> 0 /\ rbn_str W mem said sd /\
   ((exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= said /\
       said + Z.of_nat (length sd) - (said + Z.of_nat (length sd)) mod 8 + 8 <= b + req_size m) \/
    (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= said /\
       said + Z.of_nat (length sd) + 1 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
    (sp + 16 <= said /\ said + Z.of_nat (length sd) + 1 <= sp0) \/
    (exists q sz, rbn_ro q sz /\ q <= said /\ said + Z.of_nat (length sd) + 1 <= q + sz))).
Definition rbn_buf (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (mem : word -> option byte) (sp b n : Z) : Prop :=
  0 <= b /\ b + n <= 2 ^ 63 /\ amem_range b n /\ (sp <= b \/ b + n <= sp - REAC_BOX_NAME_STK) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF b n /\ shadow_hull_vis (aview SEGS (w_H W) mem) b n /\
  (forall a, b <= a < b + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) mem a).
Definition rbn_bufs (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (mem : word -> option byte)
  (sp name name_len token token_len display display_len : Z) : Prop :=
  rbn_buf STK sp0 FP ly S own lyc Sc W mem sp name (Z.min name_len 24) /\
  rbn_buf STK sp0 FP ly S own lyc Sc W mem sp token (Z.min token_len 24) /\
  rbn_buf STK sp0 FP ly S own lyc Sc W mem sp display (Z.min display_len 48) /\
  (name + Z.min name_len 24 <= token \/ token + Z.min token_len 24 <= name) /\
  (name + Z.min name_len 24 <= display \/ display + Z.min display_len 48 <= name) /\
  (token + Z.min token_len 24 <= display \/ display + Z.min display_len 48 <= token).
Definition rbn_wr (f : Z) (sd : list Z) (i o name name_len token token_len display display_len a : Z) : Prop :=
  reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len = true /\
  (name <= a < name + Z.of_nat (length (bn_NM f sd i o)) + 1 \/
   token <= a < token + Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1 \/
   display <= a < display + Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1).
Definition treac_box_name_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (f i o name name_len token token_len display display_len : Z) (sd : list Z)
  : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    getr regs2 10 =
      w64 (if reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len then 0 else -1) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_BOX_NAME_STK <= a < spZ regs) ->
       ~ rbn_wr f sd i o name name_len token token_len display display_len a ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall b m j, In (b, m) (ablocks B lyc Sc) -> 0 <= j < req_size m ->
       ~ rbn_wr f sd i o name name_len token token_len display display_len (b + j) ->
       aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W) memc (b + j)) /\
    (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall cid pos a, In (cid, pos) (frames Sc) ->
       (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
       ~ rbn_wr f sd i o name name_len token token_len display display_len a ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_BOX_NAME_STK <= a < spZ regs) ->
       apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
    (forall a, spZ regs - REAC_BOX_NAME_STK <= a < spZ regs -> apresent (w_H W2) mem2 a) /\
    (reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len = true ->
       garr8 SEGS (mrestrict (w_H W2) mem2) name (bn_NM f sd i o ++ [0]) /\
       garr8 SEGS (mrestrict (w_H W2) mem2) token (bn_TK (bn_NM f sd i o) ++ [0]) /\
       garr8 SEGS (mrestrict (w_H W2) mem2) display (bn_DP (bn_NM f sd i o) i o ++ [0])).
Definition treac_box_name_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (f said i o name name_len token token_len display display_len : Z) (sd : list Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_BOX_NAME_STK -> spZ regs + 16 <= sp0 ->
  Z.of_nat (length (frames Sc)) <= 8 ->
  getr regs 10 = w64 f -> -2 ^ 31 <= f < 2 ^ 31 ->
  getr regs 11 = w64 said -> 0 <= said < 2 ^ 64 ->
  getr regs 12 = w64 i -> -2 ^ 31 <= i < 2 ^ 31 ->
  getr regs 13 = w64 o -> -2 ^ 31 <= o < 2 ^ 31 ->
  getr regs 14 = w64 name -> 0 <= name < 2 ^ 64 ->
  getr regs 15 = w64 name_len -> 0 <= name_len < 2 ^ 64 ->
  getr regs 16 = w64 token -> 0 <= token < 2 ^ 64 ->
  getr regs 17 = w64 token_len -> 0 <= token_len < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs) 8 display -> 0 <= display < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 8) 8 display_len -> 0 <= display_len < 2 ^ 64 ->
  rbn_img W memc ->
  (reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true ->
     rbn_said lyc Sc W memc (spZ regs) sp0 said sd /\
     rbn_bufs STK sp0 FP ly S own lyc Sc W memc (spZ regs) name name_len token token_len display display_len) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name) regs memc mdc)
    (treac_box_name_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
       f i o name name_len token token_len display display_len sd).
End h.
End f.
End d.
