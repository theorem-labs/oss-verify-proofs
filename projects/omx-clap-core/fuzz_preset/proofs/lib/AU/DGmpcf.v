(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/cgif/cgif_file_fuzzer/lib/DGmpcf.v (commit 3cae605a900a, file sha256 b6b90b3a83a0) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; cgif's image-instance names kept where preset's B' instance carries them (AGif2cgif, AImg_cgif), CfImg_cgif -> CfImg_B, cgif's image rows mapped to preset's (YGcfImgcgif.* -> CfImgB / PresetImgRefillB / PresetImgRowsB, *cgif -> *preset); its 1 image numerals moved by symbol from cgif_file_fuzzer.asan-ubsan (pin 1c29845fe605, unstripped twin of the same build) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets, derived counts and list indices by the same stage map), 0 list indices re-picked, and 3 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, cf layer, field round 3 part 3; integrator ReallocPrimary).
   rule 24: no function proved (kind: frame corollaries over the Deallocate walks' dmem_m frame).

   The cf discharge of the Deallocate walks' keep law [MP_keep] (DGfz.v / DGg2.v) at
   MP := fun m => arodata_ok_cf tfibsegs B m (part 3c: memnorm is no longer part of MP):
   YG0dcf.arodata_frame_cf with X := dwin_m u dg_dzone u dg_izone u dshadow, whose second premise is the unit image
   row [zones_miss_relro] below: no non-owned covered byte (YG0dcf.aro_addr_cf: the RELRO range and the report reads
   cf_ro_reads) lies in those four zones.
   [zones_miss_relro_cgif] proves that row for cgif_file from NAMED bounds only: CfImg_cgif's cf_relro_lo /
   cf_relro_hi and cf_ro_reads (YGcfImgcgif.v:146-151), the zones' own Definitions (DGgi.DZONE / DGgi.IZONE over TFIB_IAL_LO /
   TFIB_IAL_HI / TFIB_IAL_FLAG, YG0f.SHADOW_OFF, YG0f.kHighMemBeg), the image window TFIB_IMG_LO / TFIB_IMG_END
   (YF0x.v:36 / :24) and the seed's own facts (DGgm.LYB's zone3 rows and kHighMemBeg <= ly_stk_lo, and
   DGgm.derived_ranges / DGgm.fh_Hsp / DGgm.fh_Hp).  No numeral is introduced here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG03 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGbase DGgi DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImgRefillB PresetImgRowsB. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.

(* The cf instance of DGif0.DIface's memory predicate MP: the read-only bytes (RELRO and the report reads), the fact
   acall_pre_cf carries at the call (YG0dcf.arodata_ok_cf). *)
Definition MPcf (B : asyms) (m : word -> option byte) : Prop :=
arodata_ok_cf tfibsegs B m.

(* The unit image row MP_keep_cf needs: at the seed's geometry, no non-owned covered byte (RELRO or a report read)
   lies in the walk's window, the depot zone, the internal allocator's zone or the freed block's shadow.  It is exactly
   arodata_frame_cf's second premise at X := those four zones. *)
Definition zones_miss_relro (B : asyms) : Prop :=
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU,
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
0 <= a < 2 ^ 64 /\ ~ dwin_m ly (bv_unsigned (getr regs0 2)) p a /\ ~ dg_dzone ly a /\ ~ dg_izone a /\
~ dshadow p nn a.

(* The keep law of MP at the cf instance (DGfz.MP_keep / DGg2.MP_keep). *)
Theorem MP_keep_cf : forall B, zones_miss_relro B ->
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
(forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
  ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
MPcf B mem0 -> MPcf B mem'.
Proof.
intros B HZ W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU mem' FH FR HRO.
apply (arodata_frame_cf tfibsegs B
  (fun a => dwin_m ly (bv_unsigned (getr regs0 2)) p a \/ dg_dzone ly a \/ dg_izone a \/ dshadow p nn a)
  mem0 mem').
- intros x NX. apply FR; intros Y; apply NX; tauto.
- intros a Ha NO.
  destruct (HZ W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha NO) as (R & N1 & N2 & N3 & N4).
  split; [exact R|]. intros [X|[X|[X|X]]]; [exact (N1 X) | exact (N2 X) | exact (N3 X) | exact (N4 X)].
- exact HRO.
Qed.
End a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* cgif_file: the row from named bounds.                                                                            *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem zones_miss_relro_B : forall B, zones_miss_relro (ci := CfImg_B) B.
Proof.
intros B W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha0 _.
(* every covered address (RELRO [0xa2240, 0xa4000) and the five report reads, all in [0x1ea32, 0x20b58)) lies in
   [TFIB_IMG_LO, cf_relro_hi), below every zone *)
assert (Ha : 0x10000 <= a < 0xa4000).
{ unfold aro_addr_cf in Ha0. cbn [cf_relro_lo cf_relro_hi cf_ro_reads CfImg_B] in Ha0.
  destruct Ha0 as [Ha0|Ha0]; [lia|].
  apply Exists_exists in Ha0 as (r & Hr & Hin). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hin; cbn [fst snd] in Hin; lia. }
clear Ha0.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (ZT & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _ & _ & _ & _ & _ & HSTKLO).
pose proof (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (DP & _).
pose proof (DGgm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & _ & _).
pose proof (DGgm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (DGgm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as [N8a N8b].
assert (HIMG : TFIB_IMG_LO <= a < TFIB_IMG_END) by (unfold TFIB_IMG_LO, TFIB_IMG_END; lia).
assert (Hp8 : 0 <= p / 8) by (apply Z.div_pos; lia).
(* the four zone facts, each from the seed's own rows; dg_dzone / dg_izone are DGgi.DZONE / DGgi.IZONE at
   DImg_cgif (DGif0cgif.v:32), so the asserts below are the same statement up to conversion *)
assert (NDZ : ~ DGgi.DZONE ly a).
{ unfold DGgi.DZONE. intros [Hd|[Hd|Hd]].
  - lia.
  - exact (YF0x.zone3_apart_img (ly_NB ly) kNodesBlockSize a ZNB HIMG Hd).
  - exact (YF0x.zone3_apart_img (ly_SB ly) kStoreBlockSize a ZSB HIMG Hd). }
assert (NIZ : ~ DGgi.IZONE a)
  by (unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG; lia).
assert (NWIN : ~ dwin_m ly (bv_unsigned (getr regs0 2)) p a).
{ unfold dwin_m, DGgmC.WINT, DGgmC.WINB, DGbaseC.DFSTACK. cbv beta zeta.
  unfold DGbase.DFSTACK in S1. unfold kHighMemBeg in HSTKLO.
  intros [Hw|[[Hw|Hw]|[Hw|Hw]]].
  - lia.
  - exact (YF0x.zone3_apart_img (ly_T ly) kThreadObjSize a ZT HIMG
      ltac:(unfold t_unwinding, kThreadObjSize in *; lia)).
  - exact (YF0x.zone3_apart_img (ly_T ly) kThreadObjSize a ZT HIMG
      ltac:(unfold t_stats, kThreadObjSize in *; lia)).
  - exact (YF0x.zone3_apart_img (p - 16) (DGgm.N8v nn + 16) a HP HIMG ltac:(lia)).
  - exact (YF0x.zone3_apart_img (p - 16) (DGgm.N8v nn + 16) a HP HIMG ltac:(lia)). }
assert (NSH : ~ dshadow p nn a)
  by (unfold dshadow, DGgiC.SPv, SHADOW_OFF; lia).
split; [lia|]. split; [exact NWIN|]. split; [exact NDZ|]. split; [exact NIZ | exact NSH].
Qed.

(* MP_keep_cf at cgif's row: the law the cgif-image cf instance hands to DGfz / DGg2. *)
Theorem MP_keep_cf_preset_B : forall B,
forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
(forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
  ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
MPcf (ci := CfImg_B) B mem0 -> MPcf (ci := CfImg_B) B mem'.
Proof. intros B. exact (MP_keep_cf (ci := CfImg_B) B (zones_miss_relro_B B)). Qed.
End b.

Check MP_keep_cf.
Check zones_miss_relro_B.
Print Assumptions zones_miss_relro_B.
