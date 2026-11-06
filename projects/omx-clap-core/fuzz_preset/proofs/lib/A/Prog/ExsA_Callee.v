(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image A' (#102 pin asan 1be0f53d96cb, facts 8f3e7e1a07f1): the ACHAIN-FREE RUN
   FORMS of ex_string's two program callees, ex_hex4 (fuzz_preset.c :136-155, A_prog_sigma AS_ex_hex4 = 0x84688) and
   ex_utf8 (fuzz_preset.c :157-183, A_prog_sigma AS_ex_utf8 = 0x84764). STATEMENTS ONLY; the proofs are
   lib/A/Prog/ExHex4RunA.v and lib/A/Prog/ExUtf8RunA.v.
   PORTED from lib/B/Prog/ExsB_Callee.v (image B', a Theorem Labs lane, on the cut 7cdbb61b5fa0): the same texts, verbatim, over
   image A's loaded segments (lib/A/Img0.v rsegs) in place of image B's. The form is image-free; only the segments
   constant changed.
   WHY a run form: ex_string keeps q in s0 (A 0x84078 `mv s0,a0`), so at its calls A 0x84180 / 0x841f4 (ex_hex4) and
   A 0x84230 (ex_utf8) the fpre of the kit's tex_hex4_specX / tex_utf8_specX asks a frame chain from s0 = q that no
   premise of tex_string_specX gives. The kit owner's ruling (via a Theorem Labs lane, 2026-10-29): prove the callees in an achain-free form.
   FORM: the callee runs under its CALLER's journal ajournal_x STK sp0 FP .. (any one), whose window holds the callee's
   16-byte frame; the post keeps that journal, the callee-saved registers, the memnorm keep (PRH_Base.v fQmn's), every
   byte outside the callee's frame and its written bytes, and states the result. No afn_pre_x, so no frame chain. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YN3v YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

(* the callees' frames (PRH_Img.v pi_frame: F_ex_hex4 => 16, F_ex_utf8 => 16) *)
Definition EXH_STK : Z := 16.
Definition EXU_STK : Z := 16.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- ex_hex4 (p, out): the four bytes BS at p as a hex number; on success *out = it (one 4-byte store), else nothing
   written (fuzz_preset.c :136-155). out lies in the caller's journal window above the callee's sp. ---- *)
Definition texhex4_postA (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z)
  (W0 : world rsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (W : world rsegs) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (o : Z) (BS : list Z) : world rsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
    ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
    aregs_preserved regs regs' /\ (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs mem') /\
    (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - EXH_STK <= x < spZ regs) -> ~ (o <= x < o + 4) ->
       aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
    match PjGrammar.hex4 BS with
    | Some h => getr regs' 10 = w64 0 /\ val_mem rsegs (rdW W mem') o 4 h
    | None => getr regs' 10 = w64 (-1) /\
        (forall x, o <= x < o + 4 -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)
    end.
Definition texhex4_runA (a : Z) : Prop :=
  forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (p o : Z) (BS : list Z),
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 10 = w64 p -> getr regs 11 = w64 o ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - EXH_STK -> spZ regs <= sp0 ->
  (forall x, spZ regs - EXH_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
  4096 <= p -> amem_range p 4 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
  garr8 rsegs (rdW W memc) p BS -> Z.of_nat (length BS) = 4 ->
  spZ regs <= o -> o + 4 <= sp0 -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
  (forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
  (o + 4 <= p \/ p + 4 <= o) ->
  (spZ regs <= p \/ p + 4 <= spZ regs - EXH_STK) ->
  SRr rsegs W (cfg_at rsegs a regs memc mdc)
    (texhex4_postA STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs o BS).

(* ---- ex_utf8 (o, cp): cp as UTF-8 (RFC 3629) at o, returning the byte count (fuzz_preset.c :157-183); for
   cp < 2 ^ 21 the bytes are PjGrammar.utf8 cp. The written bytes are writable under the caller's journal
   (awr_byte: in its stack window, or in FP inside a live block, as ex_string's scratch). ---- *)
Definition texutf8_postA (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z)
  (W0 : world rsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (W : world rsegs) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (o cp : Z) : world rsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
    ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
    aregs_preserved regs regs' /\ (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs mem') /\
    (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - EXU_STK <= x < spZ regs) ->
       ~ (o <= x < o + Z.of_nat (length (PjGrammar.utf8 cp))) ->
       aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
    getr regs' 10 = w64 (Z.of_nat (length (PjGrammar.utf8 cp))) /\
    garr8 rsegs (rdW W mem') o (PjGrammar.utf8 cp).
Definition texutf8_runA (a : Z) : Prop :=
  forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (o cp : Z),
  let n := Z.of_nat (length (PjGrammar.utf8 cp)) in
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 0 <= cp < 2 ^ 21 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - EXU_STK -> spZ regs <= sp0 ->
  (forall x, spZ regs - EXU_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
  4096 <= o -> o + n <= 2 ^ 47 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o n ->
  (forall x, o <= x < o + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
  (spZ regs <= o \/ o + n <= spZ regs - EXU_STK) ->
  SRr rsegs W (cfg_at rsegs a regs memc mdc)
    (texutf8_postA STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs o cp).
End c.
