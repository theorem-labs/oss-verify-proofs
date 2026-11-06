(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* The segments of the walk of reac_identity_ingest (fuzz_identity.asan 0x838fc..0x83e34), one lane each:
   - IngestWalk.v     0x838fc .. the arm entries, the refusals, the return-0 exits (the main path);
   - IngestSegVer.v   the version arm,   0x83994 .. 0x83b3c, then 0x83ca0 .. ret (ting_seg_ver);
   - IngestSegFw.v    the firmware arm,  0x83944 .. 0x83988, 0x83c08 .. 0x83c9c, then 0x83ca0 .. ret (ting_seg_fw);
   - IngestSegName.v  the model-name arm, 0x83b50 .. 0x83c04, then 0x83ca0 .. ret (ting_seg_name).
   An arm starts where the main path hands over: the call is accepted, the prologue has saved ra, s0, s1 in the
   frame, a6 holds the shadow base, and the arm's own address and length tests have passed. Its statement ends in
   the post of the whole call, treac_identity_ingest_post. lib/A/Prog/reac_identity_ingest.v has the lemmas the
   segments share (ing_tail for the tail at 0x83cbc, rec_region / pay_region, ing_shent, ing_zones, ...). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel reac_identity_ingest_c.
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
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
(* The arm entries, as listing offsets. *)
Definition AF_ing_fw : Z := AF_reac_identity_ingest + 0x48.     (* 0x83944, after 0x83940 bltu a3,a4 (a4 = 4) *)
Definition AF_ing_ver : Z := AF_reac_identity_ingest + 0x98.    (* 0x83994, after 0x83990 bltu a3,a1 (a1 = 8) *)
Definition AF_ing_name : Z := AF_reac_identity_ingest + 0x254.  (* 0x83b50, after 0x83b44 bgeu a3,a1 (a1 = 2) *)
Section h.
Variable B : asyms.
(* The state where the main path hands an arm over.
   - The call's premises, as treac_identity_ingest_spec states them, for an accepted call (the journal is the
     caller's journal at the call: memc, mdc).
   - The machine at the hand-over: regsT, memT, mdT; the caller's journal extended to memT, mdT; a0, a2, a3
     still id, p, len; a6 the shadow base; sp lowered by the 32-byte frame; ra and every callee-saved register
     but sp still the caller's; the frame holds the caller's ra, s0, s1 at sp-8, sp-16, sp-24 (what ing_tail
     reloads); memory is the call-time memory outside the frame; nothing present at the call went away. *)
Definition ing_arm_at (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (id ad p len : Z) (idb pb : list byte)
  (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  0 <= id < 2 ^ 64 /\ 0 <= ad < 65536 /\ 0 <= p < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - INGEST_STK /\ spZ regs <= sp0 /\
  length pb = Z.to_nat len /\
  reac_identity_ingest_c.ingest_refused id p len = false /\
  ting_rec_ok B STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\
  ting_pay_ok B lyc Sc W memc p len pb /\
  st_nev Sc + EV_INGEST <= EV_MAX /\ blocks_bytes Sc + LIVE_INGEST <= LIVE_MAX /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\
  getr regsT 10 = w64 id /\ getr regsT 12 = w64 p /\ getr regsT 13 = w64 len /\
  getr regsT 16 = w64 SB_ING /\ getr regsT 2 = w64 (spZ regs - 32) /\ getr regsT 1 = getr regs 1 /\
  (forall q, acallee_saved q -> q <> 2 -> getr regsT (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) /\
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
     aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memT a).
(* The version arm (ad = 1536, 8 <= len): the raw bytes p[0..8) to id+28, major/minor/patch from p[2..8) to
   id+22, id+24, id+26 (big-endian pairs), 1 to id+36; result 1. *)
Definition ting_seg_ver : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (id ad p len : Z)
         (idb pb : list byte) (regsT : bvmap 5 word) memT mdT,
  ing_arm_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb regsT memT mdT ->
  ad = 1536 -> 8 <= len ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_ing_ver)) memT (seg_rom SEGS)) mdT)
    (treac_identity_ingest_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
(* The firmware arm (ad = 0, 4 <= len, a4 = 4, the digit counter): the four digits p[0..4); a byte above 9
   returns 0; else the value to id (2 bytes) and 1 to id+2; result 1. *)
Definition ting_seg_fw : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (id ad p len : Z)
         (idb pb : list byte) (regsT : bvmap 5 word) memT mdT,
  ing_arm_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb regsT memT mdT ->
  ad = 0 -> 4 <= len -> getr regsT 14 = w64 4 ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_ing_fw)) memT (seg_rom SEGS)) mdT)
    (treac_identity_ingest_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
(* The model-name arm (ad = 4096, 2 <= len): up to min(len-1, 16) name bytes p[1..] to id+3.. until a 0
   byte, a NUL after them, 1 to id+20; result 1, or 0 when p[1] = 0. *)
Definition ting_seg_name : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (id ad p len : Z)
         (idb pb : list byte) (regsT : bvmap 5 word) memT mdT,
  ing_arm_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb regsT memT mdT ->
  ad = 4096 -> 2 <= len ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_ing_name)) memT (seg_rom SEGS)) mdT)
    (treac_identity_ingest_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
End h.
End f.
End d.
