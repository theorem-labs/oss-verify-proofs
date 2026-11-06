(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_identity_ingest.v; 124 of its 160 lines of code are new or changed and 458 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import WrapRo StrlenDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition REAC_BOX_NAME_STK : Z := 304 + 2 * ESTACK.
Definition EV_REAC_BOX_NAME : Z := 0.
Definition LIVE_REAC_BOX_NAME : Z := 0.
Definition rbn_fp (name name_len token token_len display display_len : Z) : list (Z * Z) :=
  [(name, if name =? 0 then name else name + Z.min name_len 24);
   (token, if token =? 0 then token else token + Z.min token_len 24);
   (display, if display =? 0 then display else display + Z.min display_len 48)].
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Definition rbn_cstr (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) < 2 ^ 31 /\
  0 < a /\ amem_range a (Z.of_nat (length s) + 8) /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem x <> None).
Definition rbn_glob (a n : Z) : Prop :=
  exists q z, In (q, z) G /\ q <= a /\ a + n <= q + z.
Definition rbn_fixed (a n : Z) : Prop :=
  forall x, a <= x < a + n ->
    in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Definition rbn_imgstr (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  IMG_LO + 64 <= a /\ a + Z.of_nat (length s) + 1 + 64 <= IMG_TOP /\
  Forall (fun c => 0 < c < 256) s /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  rbn_glob a (Z.of_nat (length s) + 1) /\ rbn_fixed a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     seg_rom SEGS (Z_to_bv 64 x) <> None).
Definition rbn_img (W : world SEGS) (mem : word -> option byte) : Prop :=
  VAL (A_OBJ 21) mod 8 = 0 /\
  IMG_LO + 64 <= VAL (A_OBJ 21) /\ VAL (A_OBJ 21) + 24 + 64 <= IMG_TOP /\
  in_zs B (VAL (A_OBJ 21)) 24 /\ rbn_fixed (VAL (A_OBJ 21)) 24 /\
  (exists s1 s2 s3,
     val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 21)) 8 s1 /\
     val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 21) + 8) 8 s2 /\
     val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 21) + 16) 8 s3 /\
     rbn_imgstr W mem s1 (bn_STEM 1) /\ rbn_imgstr W mem s2 (bn_STEM 2) /\ rbn_imgstr W mem s3 (bn_STEM 3)) /\
  rbn_imgstr W mem (VAL (A_OBJ 18)) (bn_STEM 0) /\
  VAL (A_OBJ 22) mod 8 = 0 /\ rbn_imgstr W mem (VAL (A_OBJ 22)) [32; 40] /\
  VAL (A_OBJ 23) mod 8 = 0 /\ rbn_imgstr W mem (VAL (A_OBJ 23)) [32; 105; 110; 32; 47; 32] /\
  VAL (A_OBJ 24) mod 8 = 0 /\ rbn_imgstr W mem (VAL (A_OBJ 24)) [32; 111; 117; 116; 41].
Definition rbn_said (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (said : Z) (sd : list Z)
  : Prop :=
  (said = 0 /\ sd = []) \/
  (said <> 0 /\ rbn_cstr W mem said sd /\
   exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= said /\ said + Z.of_nat (length sd) + 8 <= frame_addr ly cid pos + fs_frame_bytes cid).
Definition rbn_bufs (ly : alayout) (S : astate) (name name_len token token_len display display_len : Z) : Prop :=
  (exists q N, In (q, N) (ablocks B ly S) /\ q <= name /\ name + Z.min name_len 24 <= q + N) /\
  (exists q N, In (q, N) (ablocks B ly S) /\ q <= token /\ token + Z.min token_len 24 <= q + N) /\
  (exists q N, In (q, N) (ablocks B ly S) /\ q <= display /\ display + Z.min display_len 48 <= q + N) /\
  (name + Z.min name_len 24 <= token \/ token + Z.min token_len 24 <= name) /\
  (name + Z.min name_len 24 <= display \/ display + Z.min display_len 48 <= name) /\
  (token + Z.min token_len 24 <= display \/ display + Z.min display_len 48 <= token).
Definition treac_box_name_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (f : Z) (sd : list Z) (i o name name_len token token_len display display_len : Z)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B REAC_BOX_NAME_STK (rbn_fp name name_len token token_len display display_len)
    regs ly S W mem md EV_REAC_BOX_NAME
    (fun ly' S' W' regs' mem' md' =>
       W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (if reac_box_name_c.bn_accept f sd i o name name_len token token_len display display_len
        then getr regs' 10 = w64 0 /\
             garr8 SEGS (mrestrict (w_H W') mem') name (bn_NM f sd i o ++ [0]) /\
             garr8 SEGS (mrestrict (w_H W') mem') token (bn_TK (bn_NM f sd i o) ++ [0]) /\
             garr8 SEGS (mrestrict (w_H W') mem') display (bn_DP (bn_NM f sd i o) i o ++ [0]) /\
             (forall a, inFP (rbn_fp name name_len token token_len display display_len) a ->
                ~ (name <= a < name + Z.of_nat (length (bn_NM f sd i o)) + 1) ->
                ~ (token <= a < token + Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1) ->
                ~ (display <= a < display + Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1) ->
                aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
        else getr regs' 10 = w64 (-1) /\
             (forall a, inFP (rbn_fp name name_len token token_len display display_len) a ->
                (exists q N, In (q, N) (ablocks B ly S) /\ q <= a < q + N) ->
                aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a))).
Definition treac_box_name_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch
         (f said i o name name_len token token_len display display_len : Z) (sd : list Z),
  afn_pre SEGS B REAC_BOX_NAME_STK ly S W regs mem md ch ->
  arodata_okP SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI) B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 f -> - 2 ^ 31 <= f < 2 ^ 31 ->
  getr regs 11 = w64 said -> 0 <= said < 2 ^ 64 ->
  getr regs 12 = w64 i -> - 2 ^ 31 <= i < 2 ^ 31 ->
  getr regs 13 = w64 o -> - 2 ^ 31 <= o < 2 ^ 31 ->
  getr regs 14 = w64 name -> 0 <= name < 2 ^ 64 ->
  getr regs 15 = w64 name_len -> 0 <= name_len < 2 ^ 64 ->
  getr regs 16 = w64 token -> 0 <= token < 2 ^ 64 ->
  getr regs 17 = w64 token_len -> 0 <= token_len < 2 ^ 64 ->
  (forall a, spZ regs <= a < spZ regs + 16 -> apresent (w_H W) mem a) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs) 8 display -> 0 <= display < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 8) 8 display_len -> 0 <= display_len < 2 ^ 64 ->
  rbn_img W mem ->
  (reac_box_name_c.bn_args_ok name name_len token token_len display display_len i o = true ->
     rbn_said ly S W mem said sd /\ rbn_bufs ly S name name_len token token_len display display_len) ->
  Z.of_nat (length (frames S)) <= 7 ->
  st_nev S + EV_REAC_BOX_NAME <= EV_MAX -> blocks_bytes S + LIVE_REAC_BOX_NAME <= LIVE_MAX ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name) regs mem md)
    (treac_box_name_post regs ly S W mem md f sd i o name name_len token token_len display display_len).
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ ident_listing PI) (@pa_relro_hi _ ident_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IS___asan_set_shadow_f5) 245.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis PSIG : ident_prog_sig_ok.
Hypothesis HSB : tsb_dec_spec B.
End walk.
End h.
End f.
End d.
