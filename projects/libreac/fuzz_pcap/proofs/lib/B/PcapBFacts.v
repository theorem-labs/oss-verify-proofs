From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the lib/B (asan-ubsan) twin of lib/A/PcapBFacts.v, for libreac/fuzz_pcap v1.9.0's
   asan-ubsan build (pin fuzz_pcap.asan-ubsan sha256 9e66f771f22a..., the image the build loads as AsanUbsan;
   symbols from its unstripped twin fuzz_pcap sha256 c969d83cdd59...). rule 24: no function proved; these
   are image facts and law instances of B := lib/Reusable/YD2l.v PcapB, each closing one Section hypothesis of
   lib/B/PcapCloseB.v (a working branch) at the type it states there.
   - The A file's names (PcapB_segs_low, PcapB_lib, PcapB_env, PcapB_ML, PcapB_LAWS, PcapB_AMALLOC4, PcapB_AFREE4,
     PcapB_AFREEN4), from cgif c8557374ad2e lib/YCed.v:33-97 (the asan-ubsan twin of lib/A/ACed.v:40-104), at PcapB
     and tfibsegs (lib/Reusable/YB1v.v, = AsanUbsan.M.loaded_segments); TfibLib / tl_env are lib/Reusable/YCeh.v's.
     The allocator closures are lib/Reusable/YF0w.v tfib_amalloc_realizes / YF0q.v afree_realizes_closed at
     TfibB_syms, as PcapCloseB.v rows 8 / 9 use them.
   - PcapB_TL / PcapB_TLF / PcapB_FFL: cgif lib/YCed.v:70 tfibX_PALib0, :98 tfibX_PALibF0, :126 tfibX_FFL, at the listing
     image lib/B/Prog/PcapEntryTop.v PI_pcap. fuzz_pcap's PALib has the donor's fields plus pal_uar_cell /
     pal_got_cell, and PALibF the separation palf_sep; each is a closed computation on PcapAddr.v / YF0l.v.
   - PcapB_HGOS / PcapB_HGERR: the range checks of lib/A/PcapGHarness.v (a working branch 042287afd92: rng_disj_b,
     rng_out_sound, rng_out1_sound, pcap_G_harness_gx_ok / pcap_G_harness_pe_bytes) at PcapEntry.G_HARNESS_U.
   - PcapB_HTRM / PcapB_HTRF: lib/A/Prog/PcapEntryDefs.v pe_traces_of_sites, at this image's trace starts, through
     lib/Reusable/YCejSites.v:25 llvmf_site_in.
   - PcapB_AFM: cgif lib/YCke.v:26 afile_meter_trivB, renamed to the read stream's record (PSourceMeter.v).
   - PcapB_HROI: lib/Reusable/YD1o.v:53 ro_img_of_arodata (cgif lib/YD1o.v:40); arodata_okP at PI_pcap's window
     (PcapRelro.v PCAP_RLO / PCAP_RHI) is YCeg.arodata_ok (in_ro_tfa, the same window) by unfolding.
   - PcapB_HPATH: lib/A/PcapHPath.v pcap_path_addressable (a working branch a0f806fabca, from cgif lib/A/AE2m.v
     tfib_trailer_shadow), over lib/Reusable/YF0m.v's shadow tables.
   Measured on the pin 9e66f771 (pyelftools, capstone 5.0.7 RV64C):
   - LLVMFuzzerTestOneInput 0x80818 (nm T, size 0x848); target_run 0x805b8 calls it with `jal 0x80818` at 0x80680, so
     the return into target_run is 0x80684 (the chain's spine below). Its wrapper calls: `jal 0x52c28`
     __interceptor_trampoline_malloc at 0x809b4 / 0x80ac8 (ra 0x809b8 / 0x80acc = BASE 0x80788 + 0x230 / 0x344) and
     `jal 0x52c24` __interceptor_trampoline_free at 0x80a90 / 0x80e94 / 0x80e9c (ra 0x80a94 / 0x80e98 / 0x80ea0 =
     BASE + 0x30c / 0x710 / 0x718): PcapEntryDefs.v PE_MALLOC_SITES / PE_FREE_SITES.
   - The allocator trace starts: __interceptor_malloc 0x52dfc calls StackTrace::GetCurrentPc (0x7312c) at 0x52ec0, so
     pc_malloc_ra0 = 0x52ec4; __interceptor_free 0x52c2c calls it at 0x52d60, so pc_free_ra0 = 0x52d64 (YF0l.v).
   - The path literal: symbol `.str` 0x20d00 (STT_OBJECT, local, st_size 0x20) in .rodata [0x102e0, 0x2266c), bytes
     "<fuzz-input>" and NUL = 13 bytes; PcapAddr.v pcap_obj 3 = 0x20d00. Its ASan descriptor: asan_globals
     [0x9dfd0, +0x100) descriptor 0 (0x9dfd0): beg 0x20d00, size 0xd, size_with_redzone 0x20 (right redzone
     [0x20d0d, 0x20d20)); descriptor 1 (0x9e010) is the next global, `.str` "rb" at 0x20d40. Shadow (0x7fff8000 + a / 8):
     0x7fffc1a0 (granule 0x20d00) is in YF0m Tfib_zero_shadow's first range (0x10000, 0x20d08 - 0x10000); 0x7fffc1a1
     (granule 0x20d08, 5 addressable bytes) = 5 and 0x7fffc1a2 / 0x7fffc1a3 (the redzone) = 0xf9 are YF0m const-shadow
     cells; the hull's last four bytes 0x7fffc1a4..0x7fffc1a7 (granules 0x20d20..0x20d38, no ASan global) are in
     Tfib_zero_shadow's second range (0x20d20, 0x20d40 - 0x20d20).
   - The harness globals: g_file_len 0x5d3e40 and g_file 0x5d3e60 (STT_OBJECT, local, st_size 0x20; ASan descriptors 2
     (0x9e050) and 3 (0x9e090): size 8, size_with_redzone 0x20), PcapEntry.v G_HARNESS_U.
   - The PALib cells: __asan_shadow_memory_dynamic_address 0xa17b8 (size 8), __asan_option_detect_stack_use_after_return
     0xa17c0 (size 4), __interceptor_trampoline_free / _malloc 0x52c24 / 0x52c28, __asan_stack_malloc_0 / _1 0x3c588 /
     0x3c6fc: the values of PcapAddr.v pcap_obj 15 / 16 / pcap_sigma and YF0l.v Tfib_code. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG05 YG0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YF0l YF0m YF0x YE2y YCej YCeh YD2l YF0w YF0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PcapImgEnd YImgTop YCejSites YCeg YD1o YE3i PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PSourceMeter.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require
  PcapEntry PcapEntryDefs PcapEntryTop PcapPa PcapPaLib PcapFrame PcapList PcapAddr PcapSyms.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Local Open Scope Z_scope.

(* lib/B's modules by their full paths: lib/A loads modules of the same short names. *)
Module PEB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntry.
Module PED := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryDefs.
Module PET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module PPA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPa.
Module PPL := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPaLib.
Module PFR := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapFrame.
Module PLS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapList.
Module PAD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapAddr.
Module PSY := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSyms.
Module PAT := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PaTable.
Module PBA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapBase.
Module WJG := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.W_journalG.
Module PSR := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PSourceMeter.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCbq.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0n.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YA0n.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YK04.
Module RG0v := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0v.
Module RE3i := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE3i.
Module RD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module RPSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.
Module RCejS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCejSites.
Module RD1o := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD1o.

(* PcapCloseB.v's abbreviations for PcapEntryTop.v's listing image at a given rc. *)
#[local] Abbreviation PIp rc := (@PET.PI_pcap rc).
#[local] Abbreviation PSEGS rc := (@PPA.pa_segs rc PLS.pcap_listing (PIp rc)).
#[local] Abbreviation VALp rc a := (@PPA.pa_val rc PLS.pcap_listing (PIp rc) a).
#[local] Abbreviation RLOp rc := (@PPA.pa_relro_lo rc PLS.pcap_listing (PIp rc)).
#[local] Abbreviation RHIp rc := (@PPA.pa_relro_hi rc PLS.pcap_listing (PIp rc)).

(* ====================================================================================================== *)
(* lib/A/PcapBFacts.v's names, at the asan-ubsan PcapB (cgif lib/YCed.v:33-97)                            *)
(* ====================================================================================================== *)

(* donor YCed.v:95-97 segs_low argument: YCeh.v tfib_segs_low. *)
Definition PcapB_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := tfib_segs_low.
(* donor YCed.v:33 tfibX_lib, at PcapB. tl_errno_img: TFIB_ERRNO (YF0m.v, 0x5d46ec) lies in the image's fourth loaded
   segment AsanUbsan_segment_003 ([0x9b000, +0x55c000)); the donor takes cgif's segment 3 through its (base, size)
   literals (YCed.v:38). tl_lib_consts: YCeh.v lib_const_addr is False for fuzz_pcap (YCeh.v header), so the donor's
   tfibX_lib_consts_chk (YCed.v:29-32) has no counterpart. *)
Theorem PcapB_lib : TfibLib PcapB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn [as_errno PcapB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno PcapB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  exists AsanUbsan.AsanUbsan_segment_003. split; [do 3 right; left; reflexivity|]. cbn. lia.
- reflexivity.
- intros a Ha. unfold lib_const_addr in Ha. destruct Ha.
- cbn [as_gp PcapB]. unfold TFIB_GP. lia.
Qed.
(* donor YCed.v:69 tfibX_env. *)
Definition PcapB_env : api_env tfibsegs PcapB := tl_env PcapB PcapB_lib.
(* donor YCed.v:67-68 tfibX_ML. *)
Lemma PcapB_ML : model_laws (as_universe PcapB).
Proof. exact (model_laws_ok (as_universe PcapB) (ts_universe PcapB TfibB_syms)). Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* donor YCed.v:66 tfibX_LAWS. *)
Definition PcapB_LAWS : AR_laws tfibsegs PcapB := AR_laws_ok tfibsegs PcapB.
(* donor YCed.v:95-97 tfibX_AMALLOC4 / tfibX_AFREE4 / tfibX_AFREEN4. SK is passed by name: lib/Reusable/YI5b.v's
   global instance src0_sink_head must not stand in for it. *)
Definition PcapB_AMALLOC4 : amalloc04_rule (SK := SK) tfibsegs PcapB ameter_triv :=
  @amalloc04_rule_triv fx rc SK tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML
    (@tfib_amalloc_realizes fx rc PcapB TfibB_syms (fun _ => eq_refl)).
Definition PcapB_AFREE4 : afree04_rule (SK := SK) tfibsegs PcapB ameter_triv :=
  @afree04_rule_triv fx rc SK tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML
    (@afree_realizes_closed fx rc PcapB TfibB_syms (fun _ => eq_refl)).
Definition PcapB_AFREEN4 : afree_null04_rule (SK := SK) tfibsegs PcapB ameter_triv :=
  @afree_null04_rule_triv fx rc SK tfibsegs PcapB PcapB_segs_low PcapB_env PcapB_LAWS PcapB_ML
    (@afree_realizes_closed fx rc PcapB TfibB_syms (fun _ => eq_refl)).
End b.

(* ====================================================================================================== *)
(* The Section hypotheses of lib/B/PcapCloseB.v, each at the type stated there                           *)
(* ====================================================================================================== *)

(* errno_low (PcapCloseB.v Section asan_ubsan, segs := AsanUbsan.M.loaded_segments). *)
Definition PcapB_errno_low : RCbq.api_env AsanUbsan.M.loaded_segments RD2l.PcapB := PcapB_env.

(* ---- TL / TLF: donor YCed.v:70 tfibX_PALib0, :98 tfibX_PALibF0 at PI_pcap ---- *)
(* The listing's values the two records name, by computation on the closed value table PcapEntryTop.pcap_val
   (PcapAddr.v pcap_obj 0 / 1 / 15 / 16, pcap_text). *)
Lemma pcap_val_cells :
  PET.pcap_val (PAT.A_OBJ 1) = (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x60)%Z) /\ PET.pcap_val (PAT.A_OBJ 15) = (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address) /\
  PET.pcap_val (PAT.A_OBJ 0) = (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xb8)%Z) /\ PET.pcap_val (PAT.A_OBJ 16) = (symaddr Symbols.AsanUbsan.s___asan_option_detect_stack_use_after_return) /\ PET.pcap_val PAT.A_TEXT = (symaddr Symbols.AsanUbsan.s_libreac_fuzz_fopen).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pi_pcap_val : forall (rc : YM05.RunCeil) a, VALp rc a = PET.pcap_val a.
Proof. reflexivity. Qed.

Lemma PcapB_TL : forall rc : YM05.RunCeil, @PPL.PALib rc PLS.pcap_listing (PIp rc) RD2l.PcapB.
Proof.
intros rc. destruct pcap_val_cells as (V1 & V15 & V0 & V16 & VT).
constructor; rewrite ?pi_pcap_val.
- rewrite V1. reflexivity.
- rewrite V15. reflexivity.
- rewrite V0. reflexivity.
- rewrite V16. reflexivity.
- rewrite V1, V15. left. lia.
- exact PcapB_env.
- reflexivity.
- reflexivity.
- rewrite VT. cbn [as_code RD2l.PcapB pc_free_ra0 pc_malloc_ra0 Tfib_code]. lia.
Qed.

Lemma PcapB_TLF : forall rc : YM05.RunCeil, @PFR.PALibF rc PLS.pcap_listing (PIp rc) RD2l.PcapB.
Proof.
intros rc. destruct pcap_val_cells as (V1 & V15 & V0 & V16 & VT).
constructor; rewrite ?pi_pcap_val.
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite V1, V0, V15. cbn [as_uar_cell RD2l.PcapB PFR.zseps PFR.zseps_from fst snd]. repeat split; lia.
Qed.

(* ---- FFL: donor YCed.v:126 tfibX_FFL ---- *)
Lemma PcapB_FFL0 : forall rc : YM05.RunCeil, @frame_flag_lawP rc tfibsegs PcapB.
Proof.
intros rc ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ PcapB_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ PcapB_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil].
  unfold RCbq.zone2, RCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma PcapB_FFL : forall rc : YM05.RunCeil, @RCbq.frame_flag_lawP rc (PSEGS rc) RD2l.PcapB.
Proof. intros rc. exact (PcapB_FFL0 rc). Qed.

(* ---- HGOS / HGERR: lib/A/PcapGHarness.v's range checks at G_HARNESS_U ---- *)
(* Two ranges are disjoint (PcapGHarness.v rng_disj_b), and what that gives for one byte (rng_out_sound,
   rng_out1_sound): the A text, image-free. *)
Definition rng_disj_b (r r' : Z * Z) : bool := (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r).
Lemma rng_out_sound : forall L r a, forallb (rng_disj_b r) L = true -> in_zr a r -> ~ Exists (in_zr a) L.
Proof.
intros L r a H Ha HE. apply Exists_exists in HE as (r' & Hin & Ha').
pose proof (proj1 (forallb_forall _ _) H r' Hin) as Hd. unfold rng_disj_b, in_zr in *.
apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
Lemma rng_out1_sound : forall r e n a, rng_disj_b r (e, n) = true -> in_zr a r -> ~ (e <= a < e + n).
Proof.
intros r e n a H Ha He. unfold rng_disj_b, in_zr in *. cbn [fst snd] in *.
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* No byte of G_HARNESS_U (.bss g_file_len [0x5d3e40, +8), g_file [0x5d3e60, +8)) is in a row of YF0m.v
   Tfib_owned_static (their 24-byte redzones are rows, the objects are not). *)
Lemma PcapB_HGOS : forall a, WJG.inG PEB.G_HARNESS_U a -> ~ Exists (RG0n.in_zr a) (as_owned_static RD2l.PcapB).
Proof.
intros a Ha. cbn [as_owned_static RD2l.PcapB].
assert (C : forallb (fun r => forallb (rng_disj_b r) Tfib_owned_static) PEB.G_HARNESS_U = true)
  by (vm_compute; reflexivity).
unfold WJG.inG in Ha. apply Exists_exists in Ha as (r & Hr & Ha).
exact (rng_out_sound _ r a (proj1 (forallb_forall _ _) C r Hr) Ha).
Qed.
(* No byte of G_HARNESS_U is one of errno's 4 bytes (YF0m.v TFIB_ERRNO, B's TLS cell). *)
Lemma PcapB_HGERR : forall a, WJG.inG PEB.G_HARNESS_U a -> ~ (as_errno RD2l.PcapB <= a < as_errno RD2l.PcapB + 4).
Proof.
intros a Ha. cbn [as_errno RD2l.PcapB].
assert (C : forallb (fun r => rng_disj_b r (TFIB_ERRNO, 4)) PEB.G_HARNESS_U = true) by (vm_compute; reflexivity).
unfold WJG.inG in Ha. apply Exists_exists in Ha as (r & Hr & Ha).
exact (rng_out1_sound r _ _ a (proj1 (forallb_forall _ _) C r Hr) Ha).
Qed.

(* ---- HTRM / HTRF: lib/A/Prog/PcapEntryDefs.v pe_traces_of_sites, at this image ---- *)
(* The call trace of a wrapper call made by LLVMFuzzerTestOneInput: its chain holds the caller's record, whose return
   address is the return into target_run (0x80684), when the frame lies below the stack top. *)
Lemma pcap_llvmf_trace : forall (rc : YM05.RunCeil) (cx : @PED.ecx rc (PIp rc)), raZ (PED.c_regs cx) = PEB.RA_LLVMF ->
  forall pc0 (regsT : bvmap 5 word), RCbq.call_trace0 pc0 regsT (PED.pch cx) =
    firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r])
      (raZ regsT :: (if spZ (PED.c_regs cx) + 16 <? ly_top (PED.c_ly cx) then [(symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)] else []))).
Proof.
intros rc cx Hra pc0 regsT. unfold RCbq.call_trace0, PED.pch. rewrite RCejS.unwind_of_chain_spine.
destruct (spZ (PED.c_regs cx) + 16 <? ly_top (PED.c_ly cx)); cbn [map fst snd]; [rewrite Hra|]; reflexivity.
Qed.
Lemma PcapB_HTRM : forall (rc : YM05.RunCeil) (cx : @PED.ecx rc (PIp rc)), raZ (PED.c_regs cx) = PEB.RA_LLVMF ->
  forall regsT : bvmap 5 word, In (raZ regsT - VALp rc PAT.A_TEXT) PED.PE_MALLOC_SITES ->
  In (RCbq.call_trace0 (pc_malloc_ra0 (as_code RD2l.PcapB)) regsT (PED.pch cx)) (as_universe RD2l.PcapB).
Proof.
intros rc cx Hra regsT Hs. rewrite (pcap_llvmf_trace rc cx Hra).
rewrite pi_pcap_val in Hs. destruct pcap_val_cells as (_ & _ & _ & _ & VT). rewrite VT in Hs.
change (pc_malloc_ra0 (as_code RD2l.PcapB)) with (symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z). change (as_universe RD2l.PcapB) with Tfib_universe.
apply RCejS.llvmf_site_in. unfold PED.PE_MALLOC_SITES in Hs. cbn [In] in Hs.
destruct Hs as [Hs | [Hs | []]]; [do 3 right; left | do 4 right]; (split; [reflexivity | lia]).
Qed.
Lemma PcapB_HTRF : forall (rc : YM05.RunCeil) (cx : @PED.ecx rc (PIp rc)), raZ (PED.c_regs cx) = PEB.RA_LLVMF ->
  forall regsT : bvmap 5 word, In (raZ regsT - VALp rc PAT.A_TEXT) PED.PE_FREE_SITES ->
  In (RCbq.call_trace0 (pc_free_ra0 (as_code RD2l.PcapB)) regsT (PED.pch cx)) (as_universe RD2l.PcapB).
Proof.
intros rc cx Hra regsT Hs. rewrite (pcap_llvmf_trace rc cx Hra).
rewrite pi_pcap_val in Hs. destruct pcap_val_cells as (_ & _ & _ & _ & VT). rewrite VT in Hs.
change (pc_free_ra0 (as_code RD2l.PcapB)) with (symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z). change (as_universe RD2l.PcapB) with Tfib_universe.
apply RCejS.llvmf_site_in. unfold PED.PE_FREE_SITES in Hs. cbn [In] in Hs.
destruct Hs as [Hs | [Hs | [Hs | []]]]; [left | right; left | do 2 right; left]; (split; [reflexivity | lia]).
Qed.

(* ---- AFM: donor YCke.v:26 afile_meter_trivB, for the read stream's record ---- *)
Lemma asrc_file_meter_trivB : forall (rc : YM05.RunCeil) (SK : YI16.sink_head) segs B,
  @PSR.asrc_file_meter rc SK segs B ameter_triv.
Proof. intros rc SK segs B. constructor; intros; exact I. Qed.
(* At SK_U = PcapSinkHeads.asan_ubsan_sink_head, passed by name. *)
Lemma PcapB_AFM : forall rc : YM05.RunCeil,
  @PSR.asrc_file_meter rc RPSH.asan_ubsan_sink_head (PSEGS rc) RD2l.PcapB ameter_triv.
Proof. intros rc. exact (asrc_file_meter_trivB rc RPSH.asan_ubsan_sink_head _ _). Qed.

(* ---- HROI: Reusable/YD1o.v:53 ro_img_of_arodata ---- *)
(* arodata_okP at PI_pcap (segments tfibsegs, window PCAP_RLO / PCAP_RHI = 0x99198 / 0x9a3f0) is YCeg.arodata_ok, whose
   in_ro_tfa is the same disjunction at the same window. *)
Lemma PcapB_HROI : forall (rc : YM05.RunCeil) (W : RA0n.world (PSEGS rc)) mem,
  PBA.arodata_okP (PSEGS rc) (RLOp rc) (RHIp rc) RD2l.PcapB (RG0n.aview (PSEGS rc) (RA0n.w_H W) mem) ->
  RE3i.ro_img (RK04.mrestrict (RA0n.w_H W) mem).
Proof.
intros rc W mem H. exact (RD1o.ro_img_of_arodata RD2l.PcapB (RA0n.w_H W) mem TfibB_syms H).
Qed.

(* ---- HPATH: lib/A/PcapHPath.v pcap_path_addressable, over YF0m's shadow tables ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* 0x20d00 = PcapAddr.pcap_obj 3, the listing's object 3 (the path literal "<fuzz-input>"); 13 = its ASan descriptor's
   size. The proof is the A text (a working branch a0f806fabca), with PcapSyms B the asan-ubsan record (YF0m.v). *)
Lemma pcap_path_addressable : forall B, PcapSyms B -> forall segs ly S (W : world segs) mem md,
AR segs B ly S W mem md ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) 13 /\
shadow_hull_vis (aview segs (w_H W) mem) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) 13.
Proof.
intros B TB segs ly S W mem md HAR. set (rd := aview segs (w_H W) mem).
pose proof (proj1 HAR) as HM.
assert (C1 : forall a v, const_chk ly a 1%N v = true -> rd a = Some (le_byte v 1 0)).
{ intros a v Hc. pose proof (const_chk_sound _ _ _ _ Hc) as E.
assert (X : cell_holds B ly rd (ACell (ANum a) (N.to_nat 1) (AV (ANum v)))).
{ apply (proj1 (Forall_forall (cell_holds B ly rd) (as_const B ly)) (am_const B ly S _ HM)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E). }
unfold cell_holds in X. cbn [c_at c_val c_w aeval N.to_nat] in X.
specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X. }
assert (ZS : forall lo len i, In (lo, len) Tfib_zero_shadow -> 0 <= i < len / 8 -> rd (SHADOW_OFF + lo / 8 + i) = Some 0).
{ intros lo len i Hin Hi.
exact (AR_zshadow_law_ok segs B ly S W mem md (lo, len) HAR ltac:(right; rewrite (ts_zsh B TB); exact Hin) i Hi). }
(* The granule 0x20d00 (shadow 0x7fffc1a0) and the four shadow bytes 0x7fffc1a4..0x7fffc1a7 are zero shadow. *)
assert (Z0 : rd (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z) = Some 0).
{ pose proof (ZS 0x10000 ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z) - 0x10000) 0x21a0 ltac:(unfold Tfib_zero_shadow; left; reflexivity)
    ltac:(change (((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z) - 0x10000) / 8) with 0x21a1; lia)) as H.
change (SHADOW_OFF + 0x10000 / 8 + 0x21a0) with (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z) in H. exact H. }
assert (Z4 : forall s, (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z) <= s < (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68192) / 8 + 0x7fff8000)%Z) -> rd s = Some 0).
{ intros s Hs.
pose proof (ZS (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68192)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z)) (s - (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z)) ltac:(unfold Tfib_zero_shadow; right; left; reflexivity)
    ltac:(change (((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68192)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z)) / 8) with 4; lia)) as H.
assert (E : SHADOW_OFF + (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z) / 8 = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z)) by reflexivity.
rewrite E in H. replace ((symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z) + (s - (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z))) with s in H by lia. exact H. }
split.
- intros x Hx. unfold shadow_of_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
destruct (Z_lt_le_dec x (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68136)%Z)) as [L|G].
+ assert (Q : x / 8 = 0x41a0) by lia. rewrite Q.
exists 0. split; [| left; reflexivity].
change (SHADOW_OFF + 0x41a0) with 0x7fffc1a0. exact Z0.
+ assert (Q : x / 8 = 0x41a1) by lia. rewrite Q.
exists (le_byte 0x5 1 0). split.
* change (SHADOW_OFF + 0x41a1) with 0x7fffc1a1. apply C1. vm_compute. reflexivity.
* right. change (le_byte 0x5 1 0) with 5. lia.
- intros s Hs.
assert (E1 : shadow_addr (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) / 8 * 8 = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z)) by reflexivity.
assert (E2 : shadow_addr ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) + 13 - 1) / 8 * 8 + 8 = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68192) / 8 + 0x7fff8000)%Z)) by reflexivity.
rewrite E1, E2 in Hs.
destruct (Z_lt_le_dec s (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68160) / 8 + 0x7fff8000)%Z)) as [L|G].
+ assert (C : s = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68128) / 8 + 0x7fff8000)%Z) \/ s = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68136) / 8 + 0x7fff8000)%Z) \/ s = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68144) / 8 + 0x7fff8000)%Z) \/ s = (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68152) / 8 + 0x7fff8000)%Z)) by lia.
destruct C as [-> | [-> | [-> | ->]]].
* rewrite Z0. discriminate.
* rewrite (C1 (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68136) / 8 + 0x7fff8000)%Z) 0x5); [discriminate | vm_compute; reflexivity].
* rewrite (C1 (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68144) / 8 + 0x7fff8000)%Z) 0xf9); [discriminate | vm_compute; reflexivity].
* rewrite (C1 (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68152) / 8 + 0x7fff8000)%Z) 0xf9); [discriminate | vm_compute; reflexivity].
+ rewrite (Z4 s ltac:(lia)). discriminate.
Qed.
End p.
Lemma pcap_val_obj3 : PET.pcap_val (PAT.A_OBJ 3) = (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z).
Proof. vm_compute. reflexivity. Qed.
Lemma PcapB_HPATH : forall (rc : YM05.RunCeil) ly S0 (W : RA0n.world (PSEGS rc)) mem md,
  RG0n.AR (PSEGS rc) RD2l.PcapB ly S0 W mem md ->
  RG0v.range_addressable (RG0n.aview (PSEGS rc) (RA0n.w_H W) mem) SHADOW_OFF (VALp rc (PAT.A_OBJ 3)) 13 /\
  shadow_hull_vis (RG0n.aview (PSEGS rc) (RA0n.w_H W) mem) (VALp rc (PAT.A_OBJ 3)) 13.
Proof.
intros rc ly S0 W mem md HAR. rewrite pi_pcap_val, pcap_val_obj3.
exact (pcap_path_addressable RD2l.PcapB TfibB_syms _ ly S0 W mem md HAR).
Qed.
