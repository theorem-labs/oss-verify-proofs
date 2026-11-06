(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 361 of its 413 lines of code are new or changed and 1226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg1.v, with its module paths changed; 159 of its 186 lines of code are new or changed and 386 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition d_kept (P : Z -> Prop) (W : world SEGS) (m : word -> option byte) (W' : world SEGS)
  (m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a.
Definition d_fsh (cx : dcx) (a : Z) : Prop :=
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8.
Definition d_objr (cx : dcx) (o : dobj) (a : Z) : Prop := d_obj cx o <= a < d_obj cx o + dobj_size o.
Definition d_untr (o : dobj) : bool := match o with OT | OG | OLOCK | OOUR => false | _ => true end.
Definition d_inxb (xb : list (Z * Z)) (a : Z) : Prop := exists b n, In (b, n) xb /\ b <= a < b + req_size n.
Definition d_rdset (cx : dcx) (h : Z) (a : Z) : Prop :=
  d_objr cx OT a \/ d_objr cx OG a \/ d_objr cx OLOCK a \/ d_objr cx OOUR a \/ (h <= a < h + HUNT_SIZE) \/
  (0 < c_n cx /\ c_p cx <= a < c_p cx + c_n cx) \/
  (in_roP SEGS pa_relro_lo pa_relro_hi a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
  (AE2k.FF_canary <= a < AE2k.FF_canary + 8).
Definition d_obj_new (cx : dcx) (o : dobj) (W : world SEGS) (m : word -> option byte) : Prop :=
  match o with
  | OT => exists T : list byte, length T = 400%nat /\
      garr8 SEGS (rd W m) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) /\ disco_table_c.table_ok T
  | OG => exists G : list byte, length G = 264%nat /\
      garr8 SEGS (rd W m) (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G) /\ disco_classify_c.gate_ok G
  | OLOCK => exists Lk : list byte, length Lk = 12%nat /\
      garr8 SEGS (rd W m) (d_obj cx OLOCK) (map (fun b : byte => bv_unsigned b) Lk) /\ disco_classify_c.lock_ok Lk
  | OOUR => garr8 SEGS (rd W m) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))
  | _ => True
  end.
Definition d_h_new (cx : dcx) (h : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  exists H : list byte, length H = 480%nat /\ garr8 SEGS (rd W m) h (map (fun b : byte => bv_unsigned b) H) /\
    hunt_c.hunt_ok H /\ firstn 6 (skipn 412 H) = our_of (c_pl cx).
Definition d_jr (cx : dcx) (ly : alayout) (S : astate) (W : world SEGS) (m : word -> option byte) (md : Model)
  (k : Z) : Prop :=
  d_base B MT XM_LIB RLO RHI tfib_K cx /\
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly S W m md k.
Definition d_ro_hyps : Prop :=
  disco_ro_unowned B /\ globs_marked SEGS B disco_globs /\ img_shadow_vis SEGS B.
Definition d_can_hyps : Prop :=
  asink_img_laws SEGS B tfib_K /\ ak_canary tfib_K = AE2k.FF_canary.

Definition d_body_keep_stmt : Prop :=
  forall cx h n n' shf ly3 S3 W3 mem mem' lo hi,
  d_body B cx h n [] shf ly3 S3 W3 mem -> d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem a) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W3) mem a -> apresent (w_H W3) mem' a) ->
  d_frame cx h shf W3 mem' -> d_shadow cx shf W3 mem' -> 0 <= n' <= n ->
  d_body B cx h n' [] shf ly3 S3 W3 mem'.
Definition d_body_rt_stmt : Prop :=
  forall cx h n n' xb shf shf' ly3 S3 W3 mem mem' lo hi (R : Z -> Prop),
  d_body B cx h n xb shf ly3 S3 W3 mem -> d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  (forall a, R a -> (lo <= a < hi) \/ ~ d_rdset cx h a) ->
  d_kept R W3 mem W3 mem' ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W3) mem a -> apresent (w_H W3) mem' a) ->
  d_frame cx h shf' W3 mem' -> d_shadow cx shf' W3 mem' -> 0 <= n' <= n ->
  d_body B cx h n' xb shf' ly3 S3 W3 mem'.
Definition d_body_call_keep_stmt : Prop :=
  AR_laws SEGS B ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi,
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  d_kept (fun a => lo <= a < hi) W3 m3 W4 m4 ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb shf' ly4 S4 W4 m4.
Definition d_body_tobs_stmt : Prop :=
  AR_laws SEGS B ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi (os : list dobj) (R : Z -> Prop),
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  (forall a, R a -> (lo <= a < hi) \/ Exists (fun o => d_objr cx o a) os \/ ~ d_rdset cx h a) ->
  d_kept R W3 m3 W4 m4 ->
  Forall (fun o => d_obj_new cx o W4 m4) os ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb shf' ly4 S4 W4 m4.
Definition d_body_hwr_stmt : Prop :=
  AR_laws SEGS B ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi,
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  d_kept (fun a => (lo <= a < hi) \/ (h <= a < h + HUNT_SIZE)) W3 m3 W4 m4 ->
  d_h_new cx h W4 m4 ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb shf' ly4 S4 W4 m4.
Definition d_body_hcall_stmt : Prop :=
  AR_laws SEGS B ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi,
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  d_kept (fun a => (lo <= a < hi) \/ d_inxb xb a) W3 m3 W4 m4 ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb shf' ly4 S4 W4 m4.
Definition d_body_pcall_stmt : Prop :=
  AR_laws SEGS B -> d_ro_hyps -> d_can_hyps ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 md3 ly4 S4 W4 m4 md4 k4 STK sp FP kc,
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  ajournal SEGS B STK sp FP ly3 S3 W3 m3 md3 [] ly4 S4 W4 m4 md4 kc ->
  d_S cx - LLVMF_STK <= sp - STK -> sp <= d_S cx ->
  (forall a, inFP FP a -> d_inxb xb a \/ (h <= a < h + HUNT_SIZE) \/ inFP [] a) ->
  ((exists a, inFP FP a /\ h <= a < h + HUNT_SIZE) -> d_h_new cx h W4 m4) ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb shf' ly4 S4 W4 m4.
Definition d_body_malloc_stmt : Prop :=
  AR_laws SEGS B -> d_ro_hyps -> d_can_hyps ->
  forall cx h n xb shf shf' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi (xr : list (Z * Z)),
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly3 S3 W3 m3 md3 k3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  (length xr <= 1)%nat -> d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  ablocks B ly4 S4 = ablocks B ly3 S3 ++ xr ->
  Forall (fun b => off_img (fst b) (req_size (snd b))) xr ->
  acall_kept SEGS B ly3 S3 W3 m3 W4 m4 lo hi (d_inxb xr) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n (xr ++ xb) shf' ly4 S4 W4 m4.
Definition d_body_free_stmt : Prop :=
  AR_laws SEGS B -> d_ro_hyps -> d_can_hyps ->
  forall cx h n xb1 xb2 pz shf shf' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi l1 l2,
  d_body B cx h n (xb1 ++ pz ++ xb2) shf ly3 S3 W3 m3 -> d_jr cx ly3 S3 W3 m3 md3 k3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  (length pz <= 1)%nat -> d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  ablocks B ly3 S3 = l1 ++ pz ++ l2 -> ablocks B ly4 S4 = l1 ++ l2 ->
  acall_kept SEGS B ly3 S3 W3 m3 W4 m4 lo hi (d_inxb pz) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n (xb1 ++ xb2) shf' ly4 S4 W4 m4.
Definition d_body_read_stmt : Prop :=
  forall cx h n xb shf ly S W m,
  d_body B cx h n xb shf ly S W m ->
  (forall T : list byte, length T = 400%nat ->
     garr8 SEGS (rd W m) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) -> disco_table_c.table_ok T) /\
  (forall G : list byte, length G = 264%nat ->
     garr8 SEGS (rd W m) (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G) -> disco_classify_c.gate_ok G) /\
  (forall Lk : list byte, length Lk = 12%nat ->
     garr8 SEGS (rd W m) (d_obj cx OLOCK) (map (fun b : byte => bv_unsigned b) Lk) -> disco_classify_c.lock_ok Lk) /\
  (forall H : list byte, length H = 480%nat ->
     garr8 SEGS (rd W m) h (map (fun b : byte => bv_unsigned b) H) ->
     hunt_c.hunt_ok H /\ firstn 6 (skipn 412 H) = our_of (c_pl cx)).
Definition d_body_step_stmt : Prop :=
  AR_laws SEGS B -> d_ro_hyps -> d_can_hyps ->
  forall cx h n xb xb' shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T' G' Lk' H',
  d_body B cx h n xb shf ly3 S3 W3 m3 -> d_jr cx ly4 S4 W4 m4 md4 k4 ->
  d_blocks B cx h xb' ly4 S4 -> d_objs cx h T' G' Lk' H' W4 m4 ->
  (forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) ->
  d_frame cx h shf' W4 m4 -> d_shadow cx shf' W4 m4 ->
  d_body B cx h n xb' shf' ly4 S4 W4 m4.
Definition dimg_consts_of_ro_stmt : Prop :=
  AR_laws SEGS B -> d_ro_hyps ->
  forall ly S W m md, AR SEGS B ly S W m md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) -> dimg_consts W m.
End h.
End f.
End d.
