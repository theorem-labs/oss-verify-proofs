(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyRelroGeoB.v (commit 8f6c4bb5cbbf, file sha256 fceaf8ad8dfd) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 7 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (Geo, a subagent of a prior worker, for a Theorem Labs lane's cf layer round 3 at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: measurement; per-unit image facts about the layout of reply's image B,
   fuzz_reply.asan-ubsan, pin sha256 10ffb5f9202a, unstripped twin 3389287e1d61; no function walk).

   The RELRO range is CfImg_B's [cf_relro_lo, cf_relro_hi) (B/CfImgB.v:81-83, generated from the ELF's PT_GNU_RELRO).
   Read again from both ELFs for this file: PT_GNU_RELRO p_vaddr 0xa2240, p_memsz 0x1648, so [0xa2240, 0xa4000), in the
   pin and in its unstripped twin; it is the whole range of the third PT_LOAD; e_type 2 (ET_EXEC).
   Every bound below is a NAME: the CfImg_B fields, the TfibSyms constants of B/YF0m.v (TFIB_ERRNO, TFIB_IAL_LO,
   TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_STORE, TFIB_OOM), DRVW_lo of B/YD1y.v, and YD20.RS_LO (see 5). No numeral is
   typed in a term except those of the owners' texts (65536, 8, the 0 of `ew E 0`, and the 0, 2 and 2 ^ 64 of 8's text).

   Eight facts (the eighth, zones_miss_relro_preset_B, is described at the end of the file):
   1. relro_geo_preset_B: no write window of the driver (drv_win_ok, B/YD1y.v:51) covers a RELRO byte, when the stack
      pointer is at least 65536 above cf_relro_hi (a Theorem Labs lane's ruling, 14:00Z: the stack premise is REQUIRED; without it
      the stack window [sp - 65536, sp) can reach the range). From in_wrange_drv (B/YD1y.v:58) and DRVW_lo
      (B/YD1y.v:41, the driver's image windows start at 0xa24f8, above cf_relro_hi = 0xa4000).
   2. relro_seg_preset_B: round 3's relro_seg_t (Reusable/YG0ncf.v:646-647) at tfibsegs: one segment holds the range.
   3. errno_relro_preset_B: round 3's errno_relro_t (Reusable/YG0ncf.v:648) at TfibSyms: errno (TFIB_ERRNO) is above.
   4. pf_ial_apart_preset_B: the layer's pf_ial_apart_t (Reusable/YG0ncf.v:189 on this base, 
      b38406ef4b14) at TfibSyms: Printf's two cells lie outside the internal allocator's arena and its flag.
   5. dzone_static_text_B: the FIRST disjunct of YFgi.DZONE (B/YFgi.v:484-485) is [dzone_static_lo, dzone_static_hi),
      by reflexivity. DZONE writes the two bounds as inline numerals; the names here are other files' names for the
      same addresses: dzone_static_lo := TFIB_STORE (B/YF0m.v:17, __sanitizer::stackStore), dzone_static_hi :=
      YD20.RS_LO (B/YD20.v:45, the start of the driver's global read_stage). Both read from the unstripped twin's
      .symtab for this file: stackStore 0x17d5c8 (size 0x10010); read_stage 0x5cdd50 (size 0x10000), right after
      __ubsan::ubsan_flags, which ends at 0x5cdd50.
   6. pf_cells_apart_preset_B: the layer's pf_cells_apart_t (Reusable/YG0ncf.v:203 on this base) at TfibSyms: Printf's
      two cells lie below the stack store, off the out-of-memory byte and outside the error-message-buffer object.
   7. pf_dzone_static_preset_B: the static half of PF_APART (a Theorem Labs lane 15:53Z): Printf's two cells lie outside DZONE's
      first disjunct, from 6 at the image's TfibB (B/YD2l.v:15, TfibB_syms :73). The ly-dependent NB / SB half is not
      here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFgi YD20 YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0x. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DGbase. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DGgm DGgi. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset.
Open Scope Z_scope.

(* Image B's CfImg for the texts below, as B/CfRBridgeRulesB.v:476 takes it. *)
#[local] Existing Instance CfImg_B.

(* 1. RELRO geometry. *)
Lemma relro_geo_preset_B : forall E rs a, forallb drv_win_ok rs = true -> cf_relro_hi + 65536 <= bv_unsigned (ew E 0) ->
cf_relro_lo <= a < cf_relro_hi -> ~ in_wrange E rs a.
Proof.
intros E rs a Hok Hsp Ha Hw. destruct (YD1y.in_wrange_drv E rs a Hok Hw) as [Hs|Hd].
- lia.
- apply YD1y.DRVW_lo in Hd. cbn [cf_relro_lo cf_relro_hi CfImg_B] in Ha. lia.
Qed.

(* 2. relro_seg_t at tfibsegs: the segment is found by a closed computation over the image's segment list. *)
(* relro_seg_preset_B: preset states this fact as CfAroPresetB.relro_seg_preset_AU. *)

(* 3. errno_relro_t at TfibSyms. *)
(* errno_relro_preset_B: preset states this fact as CfAroPresetB.errno_relro_preset_AU. *)

(* 4. pf_ial_apart_t at TfibSyms. *)
(* pf_ial_apart_preset_B: preset states this fact as CfIalApartPreset.pf_ial_apart_B. *)

(* 5. DZONE's first disjunct by name (B/YFgi.v:484-485). *)
Definition dzone_static_lo : Z := TFIB_STORE.
Definition dzone_static_hi : Z := YD20.RS_LO.
Lemma dzone_static_text_B : forall ly a, YFgi.DZONE ly a =
((dzone_static_lo <= a < dzone_static_hi) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
 (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)).
Proof. intros ly a. reflexivity. Qed.

(* 6. pf_cells_apart_t at TfibSyms. *)
(* pf_cells_apart_preset_B: preset states this fact as CfIalApartPreset.pf_cells_apart_B. *)

(* 7. The static half of PF_APART, from 6 at TfibB. *)
Lemma pf_dzone_static_preset_B : forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
~ (dzone_static_lo <= a < dzone_static_hi).
Proof.
intros a Ha [Hlo _]. destruct (CfIalApartPreset.pf_cells_apart_B _ YD2l.TfibB_syms a Ha) as [H _]. rewrite (ts_store _ YD2l.TfibB_syms) in H. unfold dzone_static_lo in Hlo. lia.
Qed.

(* 8. zones_miss_relro_preset_B (field round 3 part 3; the statement is a Theorem Labs lane's, 18:21Z, agreed with DeallocNmaxA, whose
   lib/B/DGmpcf.v is to Require this file and close its zones_miss_relro by exact): the unit image row behind the
   Deallocate walks' keep law of arodata_ok_cf (cgif: DGmpcf.zones_miss_relro_cgif, proofs/cgif/
   cgif_file_fuzzer/lib/DGmpcf.v:82-117 at e8a7dd66acf; its proof with CfImg_cgif -> CfImg_B and YF0x -> YF0x). At the
   seed's geometry (DGgm.free_hyps), no non-owned byte of the RELRO range lies in the walk's window (DGif0.dwin_m), the
   depot zone (DGgi.DZONE), the internal allocator's zone (DGgi.IZONE) or the freed block's shadow (DGif0.dshadow).
   Part 3c: the covered set is YG0dcf.aro_addr_cf (the RELRO range and the report reads cf_ro_reads).
   Named bounds only: CfImg_B's cf_relro_lo / cf_relro_hi / cf_ro_reads, the zones' own Definitions, the image window
   YF0x.TFIB_IMG_LO / TFIB_IMG_END, and the seed's facts DGgm.LYB / derived_ranges / fh_Hsp / fh_Hp / N8_ge. *)
Section Z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem zones_miss_relro_preset_B : forall (B : asyms) W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU, DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU -> forall a, YG0dcf.aro_addr_cf (ci := CfImg_B) a -> ~ Exists (in_zr a) (as_owned_static B) -> 0 <= a < 2 ^ 64 /\ ~ DGif0.dwin_m ly (bv_unsigned (getr regs0 2)) p a /\ ~ DGgi.DZONE ly a /\ ~ DGgi.IZONE a /\ ~ DGif0.dshadow p nn a.
Proof.
intros B W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha0 _.
(* part 3c: a covered address is in the RELRO range or in one of the report's read-only reads (cf_ro_reads), all of
   them in [YF0x.TFIB_IMG_LO, cf_relro_hi) *)
assert (Ha : YF0x.TFIB_IMG_LO <= a < @cf_relro_hi CfImg_B).
{ unfold YG0dcf.aro_addr_cf in Ha0. unfold YF0x.TFIB_IMG_LO. cbn [cf_relro_lo cf_relro_hi cf_ro_reads CfImg_B] in Ha0 |- *.
  destruct Ha0 as [Ha0|Ha0]; [lia|].
  apply Exists_exists in Ha0 as (r & Hr & Hin). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hin; cbn [fst snd] in Hin; lia. }
clear Ha0. unfold YF0x.TFIB_IMG_LO in Ha. cbn [cf_relro_hi CfImg_B] in Ha.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (ZT & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _ & _ & _ & _ & _ & HSTKLO).
pose proof (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (DP & _ & DSP & _).
pose proof (DGgm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & _ & _).
pose proof (DGgm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (DGgm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as [N8a N8b].
assert (HIMG : YF0x.TFIB_IMG_LO <= a < YF0x.TFIB_IMG_END) by (unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END; lia).
assert (NDZ : ~ DGgi.DZONE ly a).
{ unfold DGgi.DZONE. intros [Hd|[Hd|Hd]].
  - lia.
  - exact (YF0x.zone3_apart_img _ _ a ZNB HIMG Hd).
  - exact (YF0x.zone3_apart_img _ _ a ZSB HIMG Hd). }
assert (NIZ : ~ DGgi.IZONE a) by (unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG; lia).
assert (NWIN : ~ DGif0.dwin_m ly (bv_unsigned (getr regs0 2)) p a).
{ unfold DGif0.dwin_m, ImgBaseDG.DGgmC.WINT, ImgBaseDG.DGgmC.WINB, ImgBaseDG.DGbaseC.DFSTACK. cbv beta zeta.
  unfold DGbase.DFSTACK in S1. unfold kHighMemBeg in HSTKLO.
  intros [Hw|[[Hw|Hw]|[Hw|Hw]]].
  - lia.
  - exact (YF0x.zone3_apart_img _ _ a ZT HIMG ltac:(unfold t_unwinding, kThreadObjSize in *; lia)).
  - exact (YF0x.zone3_apart_img _ _ a ZT HIMG ltac:(unfold t_stats, kThreadObjSize in *; lia)).
  - exact (YF0x.zone3_apart_img _ _ a HP HIMG ltac:(lia)).
  - exact (YF0x.zone3_apart_img _ _ a HP HIMG ltac:(lia)). }
assert (NSH : ~ DGif0.dshadow p nn a)
  by (unfold DGgm.SPv in DSP; unfold DGif0.dshadow, ImgBaseDG.DGgiC.SPv, SHADOW_OFF in *; lia).
split; [lia|]. split; [exact NWIN|]. split; [exact NDZ|]. split; [exact NIZ | exact NSH].
Qed.
End Z.
