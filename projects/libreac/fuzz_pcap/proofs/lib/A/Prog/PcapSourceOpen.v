(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module paths, module names and numbers changed; 1709 of its 1849 lines of code are new or changed and 490 lines of the source are left out. *)
(* pcap_source_open (fuzz_pcap.asan 0x8145c, listing offset AF_pcap_source_open = 0xd24, 240 instructions) on
   libreac v1.9.0's ASan build: the walk of the code against its contract PcapSourceOpenDefs.tpcap_source_open_specX,
   in cgif_file's walk style (proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v for the side-stack frame, and this unit's
   PcapSourceClose.v for the caller-journal form and the fclose call).

   The callees are Section hypotheses of their exact statement types: libreac_fuzz_fopen
   (PcapFuzzFopenDefs.v tlibreac_fuzz_fopen_specX), the fread wrapper (PFreadISpec.v afread_spec), the
   fclose wrapper (PFclose.v afclose_source_spec), __asan_stack_malloc_1 (YG0d.v astack_malloc_realizes 1), and the
   laws of the stack frames, of the meter and of the file meter (PSourceMeter.v asrc_file_meter). The shadow checks of
   the four stores into the caller's struct (0x81580, 0x8159c, 0x815b4, 0x815cc) are decided by the shadow entry of ps
   (0..24 usable), so their report blocks (0x817a4..0x817d0, 0x817fc) are never reached.
   getr / mkst / seg_rom come from YK11 (imported after LinuxProcessSem); nothing from lib/Lib is imported.
   The machine-stack frame arm of the prologue (0x814dc..0x814f4) is closed, not walked: the use-after-return flag
   reads 1 by YG0d.v AR_const_law, and __asan_stack_malloc_1's rule returns frame_addr >= 4096, so the side-stack
   frame is the one taken (a Theorem Labs lane 22:4xZ; if the core rules the flag cell 0, that arm is walked with a kit change).
   The walk stops at the test of f (0x815d4) and hands each arm on through PcapSourceOpenPh.v: f = NULL at 0x81660 to
   PcapSourceOpenB.op_from_null (op_gi_null), f <> NULL at 0x815d8 to PcapSourceOpenR.op_read_arm
   (op_read_arm_obl, with op_arm_read). Both arms build the same op_mid off the engine's five regions
   (op_saves, op_hdr, op_shadow, op_psfields). The read-only image predicate, the bytes it reads and the harness's
   image facts are Section hypotheses (ROIMG_KEPT, HGRO, HGX), so the file needs no core file. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame YC45.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import
PSource PSourceMeta PSourceMeter PFmemopenISpec PFreadISpec PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournalFs PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs PcapSourceOpenPh PcapSourceOpenB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceOpenR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* No global sink_head instance is in scope (a Theorem Labs lane ruling 21:57Z): every journal below uses the Section's SK. *)
Fail Definition sink_head_probe_walk : YI16.sink_head := _.

(* ---- the symbolic state at the entry -------------------------------------- *)
Definition SB_OP : Z := 0x7fff8000.
Definition OBx : sv := SOff 32 0.
Definition OPspan : Z * Z := (SB_OP, SB_OP + 2 ^ 44 - 1).
(* The machine frame below sp: 96 bytes and up to 16 more by the realignment (0x8145c, 0x81494). *)
Definition op_stack : YP09.region := stack_region OPEN_SPAN.
(* The caller's struct, 24 bytes at a0, written only. *)
(* The struct in two regions: the bytes the body writes (0..8 = ps->f, 12..22 = the three zeroed fields; the gap
   8..12 = ps->swapped is not written on the paths before the cuts) and 8..24 read-only, so that the engine's
   frame_of keeps ps->swapped and ps + 22..24 for the post. *)
Definition op_ps_lo : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 8 [].
Definition op_ps_hi : YP09.region := YP09.mkRegion (Some 10%nat) 8 24 12 22 [].
Definition op_regions : smem :=
  [op_stack; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 16); uar_cell_regionP (A_OBJ 16); op_ps_lo; op_ps_hi].
Definition op_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB_OP SB_OP 0)] [] [].
Definition ss_op : sstate := mkSS AF_pcap_source_open sr_atoms op_regions None op_facts.
Definition op_SH : list shent := [mkSHE 10 0 24].
Definition op_extra : list word := map (Z_to_bv 64) [SB_OP].

(* Copies of PcapSourceClose.v:73-83, 263-267 (a Theorem Labs lane, on this base). *)
Lemma div8_in : forall p x, p mod 8 = 0 -> p <= x < p + 8 -> x / 8 = p / 8.
Proof.
intros p x H Hx. pose proof (Z_div_mod_eq_full p 8) as E. rewrite H, Z.add_0_r in E.
symmetry. apply (Z.div_unique x 8 (p / 8) (x - p)); [left; lia | lia].
Qed.
Lemma div8_of_mul64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.
Lemma ra_frame : forall (rd rd' : Z -> option Z) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite Hk by exact Hx. split; [exact Hs | exact Ho]. Qed.
(* x / 8 for x in a frame [f, f + nb) with f and nb multiples of 64 lies in the frame's shadow [f / 8, f / 8 + nb / 8). *)
Lemma div8_frame : forall f nb x, f mod 64 = 0 -> nb mod 64 = 0 -> f <= x < f + nb ->
  f / 8 <= x / 8 < f / 8 + nb / 8.
Proof.
intros f nb x Hf Hn Hx. destruct (div8_of_mul64 f Hf) as [Ef8 Ef]. destruct (div8_of_mul64 nb Hn) as [En8 En].
rewrite Ef8, En8. split.
- apply Z.div_le_lower_bound; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* The read-only image fact and the bytes it reads are Section data here (this file is lib/A/Prog, which does not
   see the core): a Theorem Labs lane's lib/A/AE3i.v ro_img / img_ro_chunks and lib/A/PcapGHarness.v discharge ROIMG_KEPT,
   HGRO and HGX at SEGS = tfibsegs (lib/A/AB1v.v). *)
Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
(* The statement's read-only-image parameter, and the bytes it reads (a Theorem Labs lane's AE3i.v ro_img and the addresses of
   img_ro_chunks; AB1v.v gives SEGS = tfibsegs). *)
Variable ro_img : (word -> option byte) -> Prop.
Variable ro_chunk_addr : Z -> Prop.
(* ro_img reads only those bytes (AE3i's ro_img is a region_ok over img_ro_region, whose chunks are exactly
   ro_chunk_addr; YI04.region_ok_transport). *)
Hypothesis ROIMG_KEPT : forall m m' : word -> option byte,
  (forall a, ro_chunk_addr a -> mbyte SEGS m' a = mbyte SEGS m a) -> ro_img m -> ro_img m'.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
Hypothesis FOPEN : tlibreac_fuzz_fopen_specX SK SEGS (BASE + AF_libreac_fuzz_fopen)
  (VAL (A_OBJ 3)) (VAL (A_OBJ 4)) (VAL (A_OBJ 2)) ro_img B K MT FM_RA CTX.
Hypothesis AFREAD : afread_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fread).
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Hypothesis ASIL : asource_img_laws SK SEGS B K.
(* The listing's object 12 is the "rb" mode literal (0x81564 auipc, 0x81568 addi; 0x20d40 on the pin). *)
Hypothesis HMODE : VAL (A_OBJ 12) = as_mode K.
(* The image facts after __asan_stack_malloc_1 (core lib/A/PcapGHarness.v hg_img_laws, proved there as
   pcap_hg_img_laws: HGRO is its field hg_ro and HGX its field hg_glob, at SEGS = tfibsegs), and the path
   literal's shadow, which AR's constant-shadow cells fix at every allocator state (a Theorem Labs lane 23:3xZ; all three
   discharged by a Theorem Labs lane from AF0m). *)
Hypothesis HGRO : forall a, ro_chunk_addr a ->
  in_roP SEGS pa_relro_lo pa_relro_hi a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4).
(* a Theorem Labs lane's name and text for the two harness globals across __asan_stack_malloc_1 (the per-byte form of
   pe_base's gx_ok SEGS B pe_G); it is hg_img_laws' field hg_glob at g_file_len and g_file. *)
Hypothesis HGX : forall a, (VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 8) \/ (VAL (A_OBJ 2) <= a < VAL (A_OBJ 2) + 8) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPATH : forall ly S W mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 3)) 13.
(* PcapBase.v's class: the read-only bytes lie below the open-file list head (core, as PcapHarnessTail.v's HRO),
   for PcapBase.arodata_ok_journalP across the two calls. *)
Context {ROB : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* Lane PcapSourceOpenB's lemma (lib/A/Prog/PcapSourceOpenB.v op_from_null): the walk from the NULL cut
   (PcapSourceOpenPh.v) to the post. *)
Lemma OPB_NULL : op_from SK B K MT FM_RA CTX ro_img (op_gi_null SK B K MT).
Proof. eapply PcapSourceOpenB.op_from_null; eassumption. Qed.
(* The READ arm from 0x815d8 (H5, fread, the READ cut): PcapSourceOpenPh.v op_read_arm_obl, proved by a Theorem Labs lane's
   lib/A/Prog/PcapSourceOpenR.v op_read_arm; this walk supplies its op_pre and op_arm_read. *)
Lemma OPR : op_read_arm_obl SK B K MT FM_RA CTX ro_img.
Proof. eapply PcapSourceOpenR.op_read_arm; eassumption. Qed.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HBguar := pal_got_uar B TL. Let HBuar := pal_uar_cell B TL.
Let RUN := paj_run (SK := SK) B LAWS.
Let RUNTO := paj_run_to (SK := SK) B LAWS.
Let RUNP := SRr_run_pi_AJ (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PI := PI) B LAWS.
Let errno_low := pal_env B TL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).

Lemma shent_op_ok : forall Ex (m : word -> option byte) ps,
  U Ex OBx = SHADOW_OFF -> U Ex (SOff 10 0) = ps ->
  (4096 <= ps /\ (ps + 24 <= kLowShadowBeg \/ kHighMemBeg <= ps)) ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF ps 24 ->
  sh_ok SEGS OBx op_SH Ex m.
Proof.
intros Ex m ps HB Hq Hz HR. unfold sh_ok, op_SH. apply Forall_cons; [|apply Forall_nil].
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq. split.
- rewrite Z.add_0_r. exact HR.
- intros a Ha. cbn in Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma op_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ps cid pos,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 ps ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TPCAP_SOURCE_OPEN_STK -> spZ regs <= sp0 ->
  In (cid, pos) own -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= ps -> ps + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid -> ps mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 24 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs op_extra)) ss_op
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pcap_source_open)) memc (seg_rom SEGS))) /\
  sh_ok SEGS OBx op_SH (Eimg (Ereg regs op_extra)) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps cid pos
  HJ H10 Hal16 Hwlo Hwhi Hown Hin Hfa1 Hfa2 Hps8 Hsh.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (pa_obj_img 15 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 0 ltac:(lia)) as HguarR. pose proof (pa_obj_img 16 ltac:(lia)) as HuarR.
unfold pcap_img_end, YImgTop.IMG_TOP in HcellR, HgotR, HguarR, HuarR.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
pose proof (palf_sep B TLF) as Hsep. rewrite HBuar in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
set (E := Eimg (Ereg regs op_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs op_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB_OP) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EIMG : forall i, (i < 17)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = ps) by (rewrite E10; apply unsigned_lit_small; unfold in_app in Hfapp; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (VBI : forall i, (i < 17)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EIMG i Hi) | pose proof (pa_val_range (A_OBJ i)); lia]. }
assert (HPS : forall a, ps <= a < ps + 24 -> apresent (w_H W) memc a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right. right. right. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_op. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold op_regions, op_stack, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
      op_ps_lo, op_ps_hi, OPEN_SPAN.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * fold E. rewrite (VBI 1%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15)));
      [cbn [sv_denot]; rewrite (EIMG 15%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 15)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * fold E. rewrite (VBI 15%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 OBx SB_OP);
      [cbn [sv_denot OBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_OP; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * fold E. rewrite (VBI 0%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
      [cbn [sv_denot]; rewrite (EIMG 16%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    * fold E. rewrite (VBI 16%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
    * fold E. rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
      split; [lia|]. split; [unfold in_app in Hfapp; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
    * fold E. rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
      split; [lia|]. split; [unfold in_app in Hfapp; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
  + apply pairwise_disjoint_of_extents.
    unfold op_regions, op_stack, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP,
      op_ps_lo, op_ps_hi, OPEN_SPAN, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite !VBI by lia. rewrite (VB 10%nat ps E10) by (unfold in_app in Hfapp; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, in_app, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    revert Hslo Hshi H47 Hceil C1 C3 HTS Hstk0 HcellR HgotR HguarR HuarR Hsep Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hfimg
      Hwlo Hwhi.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [op_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, U10, E32, !unsigned_lit_small by (unfold SB_OP; lia).
    try change (2 ^ 4) with 16. try change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold in_app in Hfapp.
    revert Hslo Hshi H47 Hceil C1 C3 HTS Hstk0 Hal16 Hps8 Hfa1 Hfa2 Hf4096 Hfceil Hfapp Hwlo Hwhi.
    clear. unfold SB_OP. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- apply (shent_op_ok _ _ ps).
  + unfold OBx. rewrite (U_atom _ 32 SB_OP E32) by (unfold SB_OP; lia). reflexivity.
  + rewrite (U_atom _ 10 ps E10) by (unfold in_app in Hfapp; lia). reflexivity.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + rewrite <- (aview_rd_of SEGS). exact Hsh.
Qed.

(* The write rights of a run: the machine-frame window (the caller's journal window covers it) and the regions
   based at a register atom whose bytes lie in a frame of `own` (ps, then this call's own frame). *)
Ltac op_awr spv sp0v Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spv - sp0v);
    [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; unfold OPEN_SPAN, TPCAP_SOURCE_OPEN_STK in *; lia
    | cbn [YP09.r_whi]; lia |]
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | eassumption | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha |] ].

Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

(* cgif_file_fuzzer lib/A/ACer.v:156-164 (origin/ossv/recipes c8557374ad2e). *)
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)) as Hle. pose proof (Z.div_pos (v + c) 32 ltac:(lia) ltac:(lia)) as Hp.
assert (HU : U E (SAlu ALU_AND (SOff n c) (SLit (-32))) = 32 * ((v + c) / 32)).
{ unfold U. rewrite (denot_and_m32 E n v c Hn H0 H1 Hv). apply unsigned_lit_small. lia. }
rewrite HU. apply zcanon_id. rewrite M64_val. lia.
Qed.

(* A register's symbolic value, not normalized (prreg normalizes it). *)
Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* Region trimming (cgif_file_fuzzer lib/A/ACer.v:24-25, 86-91, 131-139). *)
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
  Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
    (filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
  match rs with
  | [] => []
  | r :: t => match YP09.r_base r with
              | Some 2%nat => trim_region r lo hi :: t
              | _ => r :: trim_stack t lo hi end end.
(* The first n regions made read-only (their chunks kept). *)
Fixpoint ro_upto (n : nat) (rs : smem) : smem :=
  match n, rs with
  | S n', r :: t => YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r) :: ro_upto n' t
  | _, _ => rs
  end.
Ltac subregion_tac :=
  unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
  let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
  first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac norm_pi HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let v := eval vm_compute in ss in change ss with v in HS end.
Ltac add_fact HS n f prf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_fact Ev ssx msx n f HS ltac:(prf)) as HS3; clear HS; rename HS3 into HS; norm_pi HS end.
(* Disjointness of a new region from the state's regions, the atoms' values substituted. *)
Ltac op_disj U60 U44 U62 U3_10 U3_2 :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U60, ?U44, ?U62, ?U3_10, ?U3_2;
  try change (fs_frame_bytes 1) with 128; try change (128 / 8) with 16.
(* The write right of one byte of a region: the journal's window, this call's frame or its shadow, or the caller's
   frame holding ps. *)
Ltac op_awr_close Hown F fpos cid pos :=
  first
  [ left; lia
  | right; right; right; exists 1, fpos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    try change (fs_frame_bytes 1) with 128; fold F; lia
  | right; right; right; exists 1, fpos; split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
    try change (fs_frame_bytes 1 / 8) with 16; fold F; change SHADOW_OFF with SB_OP; lia
  | right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd]; lia ].
(* The same, at a later layout ly3 whose frame addresses are lyc's (Efa : forall c q, frame_addr ly3 c q = ...). *)
Ltac op_awr_close3 Hown F fpos cid pos Efa :=
  first
  [ left; lia
  | right; right; right; exists 1, fpos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    rewrite ?Efa; try change (fs_frame_bytes 1) with 128; fold F; lia
  | right; right; right; exists 1, fpos; split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
    rewrite ?Efa; try change (fs_frame_bytes 1 / 8) with 16; fold F; change SHADOW_OFF with SB_OP; lia
  | right; right; right; exists cid, pos; split; [right; exact Hown|]; left; unfold in_zr; cbn [fst snd]; rewrite ?Efa; lia ].
(* A region of an st_ok_pi state, by index. *)
Ltac spregion HS i HR :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      pose proof (st_ok_pi_region_nth E ss ms i r HS ltac:(vm_compute; reflexivity)) as HR;
      cbn [ms_mem restrict mkst] in HR end end.
(* The shadow cell of an atom: (x >> 3) + B. *)
Lemma denot_shadow_cell : forall E n m v base,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> ew E m = Z_to_bv 64 base -> 0 <= base -> base + v / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (base + v / 8).
Proof.
intros E n m v base Hn Hv Hm Hb Hs. rewrite denot_lit_U. f_equal.
assert (Hd : 0 <= v / 8) by (apply Z.div_pos; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite (U_atom_off E n v 0 Hn ltac:(lia) ltac:(lia)), (U_atom_off E m base 0 Hm ltac:(lia) ltac:(lia)).
rewrite !Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v / 8)) by (rewrite M64_val; lia). rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.
(* A chunk of a region, as val_mem. *)
Ltac fldv HR nn base off w e v :=
  lazymatch type of HR with region_ok _ ?Ex _ _ =>
    pose proof (field_of_region Ex _ nn base _ _ _ _ _ off w e v HR ltac:(eassumption)
      ltac:(cbn; repeat (first [left; reflexivity | right]))
      ltac:(apply sv_off0; eassumption) ltac:(cbn; lia) ltac:(cbn; lia)) end.
(* ---- composing what a call keeps (topen_kept) ------------------------------ *)
Lemma tk_weaken : forall lyc Sc Sc' W m W' m' slo shi E,
  (forall bb mm, In (bb, mm) (ablocks B lyc Sc) -> In (bb, mm) (ablocks B lyc Sc')) ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames Sc')) ->
  topen_kept SK SEGS B lyc Sc' W m W' m' slo shi E -> topen_kept SK SEGS B lyc Sc W m W' m' slo shi E.
Proof.
intros lyc Sc Sc' W m W' m' slo shi E Hb Hf (A1 & A2 & A3 & A4 & A5 & A6).
split; [exact A1|]. split; [intros bb mm i Hi Hr He; exact (A2 bb mm i (Hb _ _ Hi) Hr He)|].
split; [exact A3|]. split; [intros c q a Hin Hr He; exact (A4 c q a (Hf _ _ Hin) Hr He)|].
split; [exact A5 | exact A6].
Qed.
Section tk.
Variable lyc : alayout.
Variable Sc : astate.
Variable W0' : world SEGS.
Variable memc0 : word -> option byte.
Variable mdc0 : Model.
Hypothesis HAR0 : AR SEGS B lyc Sc W0' memc0 mdc0.
Variables slo shi : Z.
Variable E : Z -> Prop.
Lemma tk_trans : forall W m W' m' W'' m'',
  topen_kept SK SEGS B lyc Sc W m W' m' slo shi E -> topen_kept SK SEGS B lyc Sc W' m' W'' m'' slo shi E ->
  topen_kept SK SEGS B lyc Sc W m W'' m'' slo shi E.
Proof.
intros W m W' m' W'' m'' (A1 & A2 & A3 & A4 & A5 & A6) (C1 & C2 & C3 & C4 & C5 & C6).
split; [intros a H1 H2; rewrite (C1 a H1 H2); exact (A1 a H1 H2)|].
split; [intros bb mm i Hb Hi He; rewrite (C2 bb mm i Hb Hi He); exact (A2 bb mm i Hb Hi He)|].
split; [intros a H1 H2 H3 H4; rewrite (C3 a H1 H2 H3 H4); exact (A3 a H1 H2 H3 H4)|].
split; [intros c q a Hf Hr He; rewrite (C4 c q a Hf Hr He); exact (A4 c q a Hf Hr He)|].
split; [intros a H1 H2 Hp; exact (C5 a H1 H2 (A5 a H1 H2 Hp)) | exact C6].
Qed.
(* A run that writes only inside Zs keeps everything topen_kept names, when Zs meets no class but E. *)
Lemma tk_of_un : forall W m m' (Zs : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall a bb mm i, Zs a -> In (bb, mm) (ablocks B lyc Sc) -> a = bb + i -> 0 <= i < req_size mm -> E a) ->
  (forall a, Zs a -> ~ in_img SEGS a) ->
  (forall a c q, Zs a -> In (c, q) (frames Sc) ->
     (in_zr a (frame_rng lyc (c, q)) \/ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8)) -> E a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  (forall a, slo <= a < shi -> apresent (w_H W) m' a) ->
  topen_kept SK SEGS B lyc Sc W m W m' slo shi E.
Proof.
intros W m m' Zs HU Hc1 Hc2 Hc3 Hc4 Hgr Hpr.
pose proof asan_consts as (CC0 & CC1 & CC2 & CC3 & CC4).
assert (HA : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) by exact HU.
split; [intros a H1 H2; apply HA; [lia | intros HZ; exact (H2 (Hc1 a HZ H1))]|].
split.
{ intros bb mm i Hb Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb mm HAR0 Hb) as (_ & Hb4 & Hbc & _).
  pose proof asan_consts as (CC & _).
  apply HA; [lia | intros HZ; exact (He (Hc2 (bb + i) bb mm i HZ Hb eq_refl Hi))]. }
split.
{ intros a H1 H2 H3 H4. apply HA; [pose proof (pa_segs_low a H1); unfold kLowMemEnd in *; lia
  | intros HZ; exact (Hc3 a HZ H1)]. }
split.
{ intros c q a Hf Hr He.
  destruct (frames_bounds SEGS B LAWS lyc Sc W0' memc0 mdc0 c q HAR0 Hf) as (Hf4 & Hfc & _).
  pose proof asan_consts as (CC & C2' & C3' & C4' & C5').
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  assert (Ha64 : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr;
    [lia | pose proof (Z.div_pos (frame_addr lyc c q) 8 ltac:(lia) ltac:(lia));
           pose proof (Z.div_le_upper_bound (frame_addr lyc c q) 8 alloc_ceiling ltac:(lia) ltac:(lia));
           pose proof (Z.div_pos (fs_frame_bytes c) 8 ltac:(lia) ltac:(lia));
           pose proof (Z.div_le_upper_bound (fs_frame_bytes c) 8 alloc_ceiling ltac:(lia) ltac:(lia)); lia]. }
  apply HA; [exact Ha64 | intros HZ; exact (He (Hc4 a c q HZ Hf Hr))]. }
split; [intros a H1 H2 Hp; exact (Hgr a Hp) | exact Hpr].
Qed.
(* A call's journal keeps what topen_kept names (the kit's acall_kept_of_journal, YCbq.v:971, for a SINK-OPEN
   footprint: the image clause then holds only off the open-file head, which is what topen_kept states). *)
Lemma tk_of_journal : forall stk sp1' FP1 nf ly2 S2 W m md W2 m2 md2 k1,
  ajournal SEGS B stk sp1' FP1 lyc Sc W m md nf ly2 S2 W2 m2 md2 k1 ->
  AR SEGS B lyc Sc W m md ->
  (forall a, inFP FP1 a -> a < 4096) ->
  (forall bb mm i, In (bb, mm) (ablocks B lyc Sc) -> 0 <= i < req_size mm -> ~ E (bb + i) ->
     In (bb, mm) (ablocks B ly2 S2)) ->
  slo <= sp1' - stk -> sp1' <= shi ->
  (forall a, slo <= a < shi -> apresent (w_H W2) m2 a) ->
  topen_kept SK SEGS B lyc Sc W m W2 m2 slo shi E.
Proof.
intros stk sp1' FP1 nf ly2 S2 W m md W2 m2 md2 k1
  (HAR2 & Hly2 & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT)
  HAR HFE Hlive Hlo Hhi Hpr.
split; [intros a Ha Hs; apply G1; [exact Ha | intros Hw; apply Hs; lia]|].
split.
{ intros bb mm i Hb Hi HnE. apply (G2 bb mm i Hb (Hlive bb mm i Hb Hi HnE) Hi). intros Hf.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb mm HAR0 Hb) as (_ & Hb4 & _). pose proof (HFE _ Hf). lia. }
split; [intros a Hi Hns He Hofl; exact (G3 a Hi Hns He (fp_spares_off FP1 a Hofl))|].
split.
{ intros c q a Hin Hr HnE. apply (G4 c q a); [exact Hin | exact Hr | intros Hf].
  pose proof (HFE _ Hf) as Hlt.
  destruct (frames_bounds SEGS B LAWS lyc Sc W0' memc0 mdc0 c q HAR0 Hin) as (Hf4 & _ & _).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr;
  [lia | pose proof (Z.div_pos (frame_addr lyc c q) 8 ltac:(lia) ltac:(lia)); lia]. }
split; [|exact Hpr].
intros a Ha Hs Hp. pose proof asan_consts as (D0 & D1 & D2 & D3 & D4). eapply apresent_transfer;
  [lia | intros Him; pose proof (pa_segs_low a Him); unfold kLowMemEnd in *; lia
   | apply G1; [exact Ha | intros Hw; apply Hs; lia] | exact Hp].
Qed.
End tk.

(* The registers op_mid names, at a cut. *)
Ltac op_cut_regs HS pfx :=
  let n2 := fresh pfx "2" in let n8 := fresh pfx "8" in let n9 := fresh pfx "9" in
  let n18 := fresh pfx "18" in let n19 := fresh pfx "19" in let n20 := fresh pfx "20" in
  let n21 := fresh pfx "21" in let n22 := fresh pfx "22" in let n23 := fresh pfx "23" in
  let n24 := fresh pfx "24" in let n25 := fresh pfx "25" in let n26 := fresh pfx "26" in
  let n27 := fresh pfx "27" in let n3 := fresh pfx "3" in let n4 := fresh pfx "4" in
  prreg_raw HS (2%bv : bv 5) n2; prreg_raw HS (8%bv : bv 5) n8; prreg_raw HS (9%bv : bv 5) n9;
  prreg_raw HS (18%bv : bv 5) n18; prreg_raw HS (19%bv : bv 5) n19; prreg_raw HS (20%bv : bv 5) n20;
  prreg_raw HS (21%bv : bv 5) n21; prreg_raw HS (22%bv : bv 5) n22; prreg_raw HS (23%bv : bv 5) n23;
  prreg_raw HS (24%bv : bv 5) n24; prreg_raw HS (25%bv : bv 5) n25; prreg_raw HS (26%bv : bv 5) n26;
  prreg_raw HS (27%bv : bv 5) n27; prreg_raw HS (3%bv : bv 5) n3; prreg_raw HS (4%bv : bv 5) n4.
(* A register of an st_ok state, its symbolic value computed. *)
Ltac sreg HS r Hr :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr end.
(* A region of an st_ok state, by index. *)
Ltac sregion HS i HR :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      pose proof (st_ok_region_nth (segs:=segs) E ss (restrict H ms) i r HS ltac:(vm_compute; reflexivity)) as HR;
      cbn [ms_mem restrict mkst] in HR end end.

(* Copy of PcapSourceClose.v:175-198 (a Theorem Labs lane, on this base): the closed-stream predicate reads only
   the stream's environment. *)
Lemma vm_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.
Ltac vmf Hfr H := eapply vm_frame; [| exact H]; intros ?x ?Hx; apply Hfr.
Lemma asource_none_frame : forall (m m' : word -> option byte),
  (forall a, asrc_env_addr K a -> mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_none SEGS K m -> asource_none SEGS K m'.
Proof.
intros m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- vmf Hfr Hth. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hnl. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hlk. unfold asrc_env_addr. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. lia.
- exists cv. split; [exact Hcv|]. vmf Hfr Hc. unfold asrc_env_addr. cbn in Hx. lia.
- vmf Hfr Hhead. unfold asrc_env_addr. cbn in Hx. lia.
Qed.

(* ---- reading the cut's state off the engine's regions ---------------------- *)
(* The shape the engine pins for every state it certifies (PcapHarnessTail.v:83-86 ms_eta, in the
   form op_mid asks for). *)
Lemma op_ms_shape : forall (msx : machine_state) r pcv m,
  msx = mkst r pcv m (seg_rom SEGS) ->
  ms_resv msx = None /\ ms_svc_pending msx = None /\ ms_rom msx = seg_rom SEGS /\
  ms_fregs msx = fp_regs /\ ms_fcsr msx = fp_csr /\ ms_pc_val msx = pcv.
Proof. intros msx r pcv m H. repeat split; rewrite H; reflexivity. Qed.
Lemma op_reg_rng : forall (rg : bvmap 5 word) (r : bv 5), 0 <= bv_unsigned (getr rg r) < 2 ^ 64.
Proof. intros rg r. exact (bv_unsigned_in_range _ (getr rg r)). Qed.
(* One byte of memory, from a one-byte val_mem. *)
Lemma aview_byte_of_val : forall (H : word -> bool) m a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite (le_byte_small v 1%nat 0%nat ltac:(cbn; lia) ltac:(lia)) in Hv.
rewrite Z.mul_0_r, Z.shiftr_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* One byte of a zeroed chunk of a region (the name chunk_ok is shadowed here by the allocator's). *)
Lemma op_zero_byte : forall (Ex : env) (H : word -> bool) m (r : YP09.region) base off len j,
  region_ok SEGS Ex (mrestrict H m) r -> base_val Ex (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CZero len)) (YP09.r_chunks r) -> 0 <= j < len ->
  aview SEGS H m (base + off + j) = Some 0.
Proof.
intros Ex H m r base off len j HR Hb Hin Hj.
destruct HR as (_ & _ & _ & HCh). rewrite Forall_forall in HCh.
pose proof (HCh _ Hin) as Hc. rewrite Hb in Hc.
destruct (Hc j ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val] in Hb1, Hb2. cbn in Hb1. injection Hb1 as <-.
unfold aview. rewrite Hb2. reflexivity.
Qed.
Lemma op_set_fs_eta : forall s : astate, exists f, s = set_fs f s.
Proof. intros []. eexists. reflexivity. Qed.
(* The read-only image fact reads only the bytes HGRO names. *)
Lemma op_rod_frame : forall (rd rd' : reader),
  (forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B rd -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rd'.
Proof. intros rd rd' Hk HR a Hro Ho He. rewrite (Hk a Hro Ho He). exact (HR a Hro Ho He). Qed.
(* The empty read window reads only f + 8 .. f + 24. *)
Lemma op_window_nil_frame : forall (m m' : word -> option byte) f,
  (forall a, f <= a < f + 24 -> mbyte SEGS m' a = mbyte SEGS m a) ->
  source_window SEGS m f [] -> source_window SEGS m' f [].
Proof.
intros m m' f Hk [(_ & H8 & H16) | (i & Hi0 & Hi1 & H8 & H16 & Hg)].
- left. split; [reflexivity|].
  split; (eapply vm_frame; [intros x Hx; apply Hk; cbn in Hx; lia | assumption]).
- right. exists i. split; [exact Hi0|]. split; [exact Hi1|].
  split; [eapply vm_frame; [intros x Hx; apply Hk; cbn in Hx; lia | exact H8]|].
  split; [eapply vm_frame; [intros x Hx; apply Hk; cbn in Hx; lia | exact H16]|].
  apply (garr8_frame SEGS m m' _ _ Hg). intros x Hx. cbn [length] in Hx. exfalso. cbn in Hx. lia.
Qed.
(* The open stream reads only its block, the input buffer and the stdio environment. *)
Lemma op_unbuf_frame : forall (m m' : word -> option byte) f bb C p,
  (forall a, (f <= a < f + SRC_FILE_BLOCK) \/ (bb <= a < bb + Z.of_nat (length C)) \/ asrc_env_addr K a ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_unbuffered SEGS K m f bb C p -> asource_unbuffered SEGS K m' f bb C p.
Proof.
intros m m' f bb C p Hk (Hat & Hw). split.
- exact (asource_at_frame_segs SEGS K m m' f bb C p Hk Hat).
- apply (op_window_nil_frame m m' f); [|exact Hw]. intros a Ha. apply Hk. left. unfold SRC_FILE_BLOCK. lia.
Qed.

(* The eleven words the prologue saved (0x81464..0x8148c), as the cut states them. *)
Definition op_stk_cut : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-88) 0 (-88) 0
    [YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition op_F_cut : YP09.region :=
  YP09.mkRegion (Some 44%nat) 0 128 0 0
    [YP09.mkChunk 16 (CVal 8 (SOff 252 0)); YP09.mkChunk 8 (CVal 8 (SOff 251 0));
     YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 120 (CVal 8 (SOff 61 0))].
Definition op_sh_cut : YP09.region :=
  YP09.mkRegion (Some 62%nat) 0 16 0 0
    [YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551603));
     YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551603));
     YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
     YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601));
     YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608));
     YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608));
     YP09.mkChunk 12 (CZero 4)].
Definition op_pslo_cut : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 68 0))].
Definition op_pshi_cut : YP09.region :=
  YP09.mkRegion (Some 10%nat) 8 24 12 22
    [YP09.mkChunk 20 (CVal 2 (SLit 0)); YP09.mkChunk 16 (CVal 4 (SLit 0)); YP09.mkChunk 12 (CVal 4 (SLit 0))].

Ltac op_in_chunk := cbn [YP09.r_chunks op_stk_cut op_F_cut op_sh_cut op_pslo_cut op_pshi_cut In];
  repeat (first [left; reflexivity | right]).

(* The saved ra and the ten callee-saved words, as op_mid states them. *)
Lemma op_saves : forall (Ex : env) (H : word -> bool) m (rg : bvmap 5 word) spv,
  bv_unsigned (ew Ex 2) = spv ->
  (forall r : nat, (r < 32)%nat -> ew Ex r = getr rg (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok SEGS Ex (mrestrict H m) op_stk_cut ->
  rdword (aview SEGS H m) (spv - 8) = Some (bv_unsigned (getr rg 1)) /\
  (forall j, 0 <= j < 10 -> rdword (aview SEGS H m) (spv - 16 - 8 * j) =
     Some (bv_unsigned (getr rg (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
Proof.
intros Ex H m rg spv Hb HE HR.
assert (FLD : forall (o : Z) (r : nat), (r < 32)%nat -> In (YP09.mkChunk o (CVal 8 (SOff r 0))) (YP09.r_chunks op_stk_cut) ->
  rdword (aview SEGS H m) (spv + o) = Some (bv_unsigned (getr rg (Z_to_bv 5 (Z.of_nat r))))).
{ intros o r Hr Hin.
  pose proof (field_of_region Ex (mrestrict H m) 2%nat spv _ _ _ _ _ o 8%N (SOff r 0)
    (bv_unsigned (getr rg (Z_to_bv 5 (Z.of_nat r)))) HR Hb Hin
    ltac:(apply sv_off0; rewrite (HE r Hr); symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(cbn; exact (op_reg_rng rg (Z_to_bv 5 (Z.of_nat r)))) ltac:(cbn; lia)) as V.
  change (N.to_nat 8) with 8%nat in V.
  exact (rdword_of_val_mem SEGS H m _ _ V (op_reg_rng rg (Z_to_bv 5 (Z.of_nat r)))). }
split.
- replace (spv - 8) with (spv + -8) by ring.
  exact (FLD (-8) 1%nat ltac:(lia) ltac:(op_in_chunk)).
- intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
  [ replace (spv - 16 - 8 * 0) with (spv + -16) by ring; exact (FLD (-16) 8%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 1) with (spv + -24) by ring; exact (FLD (-24) 9%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 2) with (spv + -32) by ring; exact (FLD (-32) 18%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 3) with (spv + -40) by ring; exact (FLD (-40) 19%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 4) with (spv + -48) by ring; exact (FLD (-48) 20%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 5) with (spv + -56) by ring; exact (FLD (-56) 21%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 6) with (spv + -64) by ring; exact (FLD (-64) 22%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 7) with (spv + -72) by ring; exact (FLD (-72) 23%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 8) with (spv + -80) by ring; exact (FLD (-80) 24%nat ltac:(lia) ltac:(op_in_chunk))
  | replace (spv - 16 - 8 * 9) with (spv + -88) by ring; exact (FLD (-88) 25%nat ltac:(lia) ltac:(op_in_chunk))
  ].
Qed.

(* The frame's header (0x814f8..0x81530) and its flag pointer (__asan_stack_malloc_1's slot word). *)
Lemma op_hdr : forall (Ex : env) (H : word -> bool) m Fv FLv,
  bv_unsigned (ew Ex 44) = Fv -> ew Ex 61 = Z_to_bv 64 FLv -> 0 <= FLv < 2 ^ 64 ->
  ew Ex 251 = Z_to_bv 64 (VAL (A_OBJ 10)) -> ew Ex 252 = Z_to_bv 64 (VAL (A_OBJ 11)) ->
  region_ok SEGS Ex (mrestrict H m) op_F_cut ->
  rdword (aview SEGS H m) Fv = Some OP_MAGIC /\
  rdword (aview SEGS H m) (Fv + 8) = Some (VAL (A_OBJ 10)) /\
  rdword (aview SEGS H m) (Fv + 16) = Some (VAL (A_OBJ 11)) /\
  rdword (aview SEGS H m) (Fv + OP_FLAGPTR) = Some FLv.
Proof.
intros Ex H m Fv FLv Hb H61 HFL H251 H252 HR.
pose proof (pa_val_range (A_OBJ 10)) as R10. pose proof (pa_val_range (A_OBJ 11)) as R11.
assert (W8 : forall o (e : sv) v, In (YP09.mkChunk o (CVal 8 e)) (YP09.r_chunks op_F_cut) ->
  sv_denot Ex e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H m) (Fv + o) = Some v).
{ intros o e v Hin He Hv.
  pose proof (field_of_region Ex (mrestrict H m) 44%nat Fv _ _ _ _ _ o 8%N e v HR Hb Hin He
    ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  change (N.to_nat 8) with 8%nat in V. exact (rdword_of_val_mem SEGS H m _ _ V Hv). }
split; [|split; [|split]].
- rewrite <- (Z.add_0_r Fv) at 1. apply (W8 0 (SLit 1102416563) OP_MAGIC ltac:(op_in_chunk)); [reflexivity | unfold OP_MAGIC; lia].
- apply (W8 8 (SOff 251 0) (VAL (A_OBJ 10)) ltac:(op_in_chunk)); [apply sv_off0; exact H251 | lia].
- apply (W8 16 (SOff 252 0) (VAL (A_OBJ 11)) ltac:(op_in_chunk)); [apply sv_off0; exact H252 | lia].
- apply (W8 120 (SOff 61 0) FLv ltac:(op_in_chunk)); [apply sv_off0; exact H61 | lia].
Qed.

(* The frame's sixteen shadow bytes, out of scope (0x81534..0x81560 and __asan_stack_malloc_1's zeroes). *)
Lemma op_shadow : forall (Ex : env) (H : word -> bool) m Sv,
  bv_unsigned (ew Ex 62) = Sv -> region_ok SEGS Ex (mrestrict H m) op_sh_cut ->
  forall i, (i < 16)%nat -> aview SEGS H m (Sv + Z.of_nat i) = Some (nth i OSH_out 0).
Proof.
intros Ex H m Sv Hb HR i Hi.
assert (LIT : forall o c v, In (YP09.mkChunk o (CVal 1 (SLit c))) (YP09.r_chunks op_sh_cut) ->
  v = bv_unsigned (sv_denot Ex (SLit c)) mod 2 ^ (8 * Z.of_N 1) -> 0 <= v < 256 ->
  aview SEGS H m (Sv + o) = Some v).
{ intros o c v Hin -> Hv.
  pose proof (field_of_region_any Ex (mrestrict H m) 62%nat Sv _ _ _ _ _ o 1%N (SLit c) HR Hb Hin ltac:(cbn; lia)) as V.
  change (N.to_nat 1) with 1%nat in V. exact (aview_byte_of_val H m _ _ V Hv). }
assert (ZB : forall j, 0 <= j < 4 -> aview SEGS H m (Sv + 12 + j) = Some 0).
{ intros j Hj.
  exact (op_zero_byte Ex H m op_sh_cut Sv 12 4 j HR
           ltac:(cbn [YP09.r_base op_sh_cut base_val]; exact Hb) ltac:(op_in_chunk) Hj). }
do 16 (destruct i as [|i]; [unfold OSH_out; cbn [nth];
  lazymatch goal with |- aview _ _ _ (_ + ?o) = _ => let o' := eval vm_compute in o in change o with o' end;
  first [ apply (LIT 0 18446744073709551601) | apply (LIT 1 18446744073709551601)
        | apply (LIT 2 18446744073709551601) | apply (LIT 3 18446744073709551601)
        | apply (LIT 4 18446744073709551608) | apply (LIT 5 18446744073709551608)
        | apply (LIT 6 18446744073709551608) | apply (LIT 7 18446744073709551603)
        | apply (LIT 8 18446744073709551603) | apply (LIT 9 18446744073709551603)
        | apply (LIT 10 18446744073709551603) | apply (LIT 11 18446744073709551603)
        | replace (Sv + 12) with (Sv + 12 + 0) by ring; apply ZB
        | replace (Sv + 13) with (Sv + 12 + 1) by ring; apply ZB
        | replace (Sv + 14) with (Sv + 12 + 2) by ring; apply ZB
        | replace (Sv + 15) with (Sv + 12 + 3) by ring; apply ZB ];
  solve [ op_in_chunk | vm_compute; reflexivity | lia ] |]).
exfalso. lia.
Qed.

(* The four fields the body wrote into the caller's struct (0x81588..0x815d0). *)
Lemma op_psfields : forall (Ex : env) (H : word -> bool) m psv hv,
  bv_unsigned (ew Ex 10) = psv -> ew Ex 68 = Z_to_bv 64 hv -> 0 <= hv < 2 ^ 64 ->
  region_ok SEGS Ex (mrestrict H m) op_pslo_cut -> region_ok SEGS Ex (mrestrict H m) op_pshi_cut ->
  val_mem SEGS (mrestrict H m) psv 8 hv /\ val_mem SEGS (mrestrict H m) (psv + 12) 4 0 /\
  val_mem SEGS (mrestrict H m) (psv + 16) 4 0 /\ val_mem SEGS (mrestrict H m) (psv + 20) 2 0.
Proof.
intros Ex H m psv hv Hb H68 Hh HRlo HRhi.
split; [|split; [|split]].
- rewrite <- (Z.add_0_r psv).
  pose proof (field_of_region Ex (mrestrict H m) 10%nat psv _ _ _ _ _ 0 8%N (SOff 68 0) hv HRlo Hb
    ltac:(op_in_chunk) ltac:(apply sv_off0; exact H68) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  change (N.to_nat 8) with 8%nat in V. exact V.
- pose proof (field_of_region Ex (mrestrict H m) 10%nat psv _ _ _ _ _ 12 4%N (SLit 0) 0 HRhi Hb
    ltac:(op_in_chunk) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  change (N.to_nat 4) with 4%nat in V. exact V.
- pose proof (field_of_region Ex (mrestrict H m) 10%nat psv _ _ _ _ _ 16 4%N (SLit 0) 0 HRhi Hb
    ltac:(op_in_chunk) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  change (N.to_nat 4) with 4%nat in V. exact V.
- pose proof (field_of_region Ex (mrestrict H m) 10%nat psv _ _ _ _ _ 20 2%N (SLit 0) 0 HRhi Hb
    ltac:(op_in_chunk) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  change (N.to_nat 2) with 2%nat in V. exact V.
Qed.

Theorem pb_pcap_source_openX : tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi
  (VAL (A_OBJ 3)) (VAL (A_OBJ 4)) (VAL (A_OBJ 2)) ro_img B K MT FM_RA CTX (BASE + AF_pcap_source_open).
Proof.
unfold tpcap_source_open_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos
  HJ HROD Hraw Hra4 Hgp Htp H10 H11 Hch Hctx Hal16 Hwlo Hwhi Htop32 Hnfr Hown Hfa1 Hfa2 Hps0 Hps8 Hsh HFP0
  HRO HPra HPhull HVn HVb Hb64 HNONE Hn HnC Hinput HMETA Hev Hlive MOK HU0 HUC.
(* The entry journal, kept for op_pre at the two cuts (the runs below rebind HJ to the current state). *)
pose proof HJ as HJ0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
assert (Hspc : alloc_ceiling + 18736 <= spZ regs) by (rewrite HTS in Hwlo; clear - Hwlo Hslo Hceil; lia).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Hfimg. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
pose proof (frame_al64 SEGS B lyc Sc W memc mdc cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
destruct (op_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps cid pos
  HJ H10 Hal16 Hwlo Hwhi Hown Hin Hfa1 Hfa2 Hps8 Hsh) as [HS SHOK].
remember (Eimg (Ereg regs op_extra)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs op_extra) n)
  by (intros nn Hn'; subst E; apply Eimg_low; exact Hn').
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 ps) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E25 : ew E 25 = getr regs 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB_OP) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
(* Every register atom below 32 is the entry value of that register (op_saves reads the eleven saves). *)
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (HAE : env_agree 32 (Ereg regs op_extra) E) by (split; [intros nn Hn'; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hps64 : 0 <= ps < 2 ^ 64) by lia.
assert (U10 : bv_unsigned (ew E 10) = ps) by (rewrite E10; apply unsigned_lit_small; exact Hps64).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_pcap_source_open)) with (Z_to_bv 64 (BASE + AF_pcap_source_open)).
(* The prologue, the frame request, up to the call of __asan_stack_malloc_1 (0x814c4). *)
paj_run_tok RUN HS HJ SHOK OPspan;
  [ op_awr (spZ regs) sp0 Usp;
    repeat (right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia]) |].
pmkst HS.
prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* s1 = sp = (sp0' - 96) & -32 (0x81494). *)
set (sp1 := 32 * ((spZ regs - OPEN_FRAME) / 32)).
destruct (sp1_facts (spZ regs - OPEN_FRAME) ltac:(unfold OPEN_FRAME; lia)
  ltac:(unfold OPEN_FRAME; rewrite Zminus_mod, Hal16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16. unfold OPEN_FRAME in Hsp1r.
assert (Rsp1 : getr (ms_regs ms) 2 = Z_to_bv 64 sp1).
{ rewrite R2.
  change (alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (ew E 2) + -96)) (Z_to_bv 64 (-32)))
    with (sv_denot E (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32)))).
  rewrite (denot_and_m32 E 2 (spZ regs) (-96)); [unfold sp1, OPEN_FRAME; f_equal; lia | | lia | lia | lia].
  rewrite <- Usp. symmetry. apply Z_to_bv_bv_unsigned. }
(* The trimmed machine frame (the saves, sp0' - 88 .. sp0'; the callee's window starts at s1 <= sp0' - 96) and ps;
   the GOT words and the two runtime cells are not read again. *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick (trim_stack rs (-88) 0) [0; 5; 6]%nat) in
  pose proof (st_ok_submem SEGS Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; submem_to) ltac:(vm_compute; reflexivity))
    as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
(* __asan_stack_malloc_1(0x60): the class-1 slot (fpos) on top of own. Its window is ESTACK below s1:
   ESTACK - (s1 - sp0) <= STK because s1 >= sp0' - 112 and sp0' - TPCAP_SOURCE_OPEN_STK >= sp0 - STK. *)
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
assert (HFF : 8 <= fs_frames 1) by (vm_compute; congruence).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ).
  - unfold spZ at 1. rewrite Rsp1, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - lia.
  - change ESTACK with 4096. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. clear R2 R3 R4 R1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HK & HJe & (fS2 & ES2)).
replace (sp0 + (sp1 - sp0)) with sp1 in HK, HJe by lia. change ESTACK with 4096 in HK.
pose proof HJ2 as (HAR2 & Hly2 & _).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). pose proof HK as (K1 & _). apply K1; lia.
    + intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
  - eapply (region_kept_ownframe_aj SEGS B); [exact HK | exact U10 | exact Hin | left; lia | intros ?a ?Ha [] |].
    intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 _)).
    right. right. right. exists cid, pos. split; [right; exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia.
  - eapply (region_kept_ownframe_aj SEGS B); [exact HK | exact U10 | exact Hin | left; lia | intros ?a ?Ha [] |].
    intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 _)).
    right. right. right. exists cid, pos. split; [right; exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn) by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE1 : env_agree 32 (Ereg regs op_extra) Ev1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE1.
(* The frame F (a0 after the call, atom 44), its flag FL and its shadow. *)
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10, Ha0; reflexivity). clear R10.
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. fold F in HF4096, HFceil, HFapp.
pose proof (frame_al64 SEGS B lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFa64 & _ & _). fold F in HFa64.
change (fs_frame_bytes 1) with 128 in *.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFpres & HFSpres).
fold F in HFpres, HFSpres. change (fs_frame_bytes 1) with 128 in HFpres, HFSpres.
destruct (FFL lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
(* F and the caller's frame holding ps are two frames of S2: disjoint. *)
assert (HdFps : F + 128 <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= F).
{ destruct (in_split _ _ Hin) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (cid, pos) [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia. }
(* F is disjoint from every frame of the caller, and so are their shadows. *)
assert (HdF : forall c q, In (c, q) (frames Sc) ->
  frame_addr lyc c q + fs_frame_bytes c <= F \/ F + 128 <= frame_addr lyc c q).
{ intros c q Hcq. destruct (in_split _ _ Hcq) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (c, q) [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia. }
assert (HdFs : forall c q, In (c, q) (frames Sc) ->
  shadow_addr (frame_addr lyc c q) + fs_frame_bytes c / 8 <= SB_OP + F / 8
  \/ SB_OP + F / 8 + 16 <= shadow_addr (frame_addr lyc c q)).
{ intros c q Hcq.
  destruct (frame_al64 SEGS B lyc S2 W mem2 md2 c q HAR2 ltac:(rewrite Hfrs2; right; exact Hcq)) as (Ha64 & Hb64' & _).
  destruct (div8_of_mul64 _ Ha64) as [E1' E2']. destruct (div8_of_mul64 _ Hb64') as [E3' E4'].
  destruct (div8_of_mul64 F HFa64) as [E5' E6'].
  pose proof (HdF c q Hcq) as Hd. unfold shadow_addr. change SHADOW_OFF with SB_OP. lia. }
pose proof (frm_off_imgP B lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as HFimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg. fold F in HFimg. change (fs_frame_bytes 1) with 128 in HFimg.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (HF8u : F < 8 * (F / 8) + 8) by (pose proof (Z.mod_pos_bound F 8 ltac:(lia)); pose proof (Z_div_mod_eq_full F 8); lia).
assert (HFb : 4096 <= F /\ F + 128 <= 140737479966720) by (clear - HF4096 HFceil C1; lia).
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8c : F / 8 <= 17592184995824) by (apply Z.div_le_upper_bound; lia).
(* The bytes this call writes (Zop) and the bytes the post lets it write in the caller's struct (Eop), with the
   four class facts topen_kept needs: outside the call's stack window Zop is below the allocator's ceiling, it meets
   no block and no image byte, and what it meets of the caller's frames is Eop. *)
set (Zop := fun a : Z => (spZ regs - TPCAP_SOURCE_OPEN_STK <= a < spZ regs)
     \/ (SB_OP + F / 8 <= a < SB_OP + F / 8 + 16) \/ (F <= a < F + 128)
     \/ (ps <= a < ps + 8) \/ (ps + 12 <= a < ps + 22)).
set (Eop := fun a : Z => ps <= a < ps + 22).
assert (Zop_ceil : forall a, Zop a -> alloc_ceiling <= a < 2 ^ 64 ->
  spZ regs - TPCAP_SOURCE_OPEN_STK <= a < spZ regs).
{ intros a HZ Ha. unfold Zop in HZ; cbv beta in HZ. clear - HZ Ha HF8b HF8c HFceil Hfa1 Hfa2 Hfceil C1 HTS Hspc. unfold SB_OP in HZ. lia. }
assert (Zop_img : forall a, Zop a -> ~ in_img SEGS a).
{ intros a HZ Hi. pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  unfold Zop in HZ; cbv beta in HZ. clear - HZ Hr HFimg Hfimg Hfa1 Hfa2 Hspc C1 HF8b HTS. unfold SB_OP in HZ. lia. }
assert (Zop_blk : forall a bb mm i, Zop a -> In (bb, mm) (ablocks B lyc Sc) -> a = bb + i ->
  0 <= i < req_size mm -> Eop a).
{ intros a bb mm i HZ Hb -> Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb mm HAR Hb) as (_ & Hb4 & Hbc & Hbia & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hbia.
  pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 bb mm 1 fpos HAR2 ltac:(rewrite Eab; exact Hb) Hfin2) as D2.
  unfold zdisjoint in D2. cbn [fst snd] in D2. fold F in D2. change (fs_frame_bytes 1) with 128 in D2.
  unfold Zop, Eop in *; cbv beta in HZ |- *. clear - HZ Hb4 Hbc Hbia Hi D2 Hspc C1 HF8b HF8c HTS. unfold SB_OP in HZ. lia. }
assert (Zop_frm : forall a c q, Zop a -> In (c, q) (frames Sc) ->
  (in_zr a (frame_rng lyc (c, q)) \/ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8)) -> Eop a).
{ intros a c q HZ Hcq Hr.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR Hcq) as (Hc4 & Hcc & Hcia).
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hcia.
  pose proof (HdF c q Hcq) as Hd1. pose proof (HdFs c q Hcq) as Hd2.
  destruct (frame_al64 SEGS B lyc Sc W memc mdc c q HAR Hcq) as (Hca & Hcb & Hcb64).
  destruct (div8_of_mul64 _ Hca) as [Ea8 Ea64']. destruct (div8_of_mul64 _ Hcb) as [Eb8 Eb64'].
  unfold shadow_addr in Hd2. change SHADOW_OFF with SB_OP in Hd2.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr;
  unfold Zop, Eop in *; cbv beta in HZ |- *; unfold SB_OP in *;
  [ clear - HZ Hr Hd1 Hc4 Hcc Hcia Hspc C1 HF8b HF8c HFceil HF4096 Hfa1 Hfa2 HTS HFapp Hfapp
  | clear - HZ Hr Hd2 Hc4 Hcc Hcia Ea8 Ea64' Eb8 Eb64' Hspc C1 HF8b HF8c HF8m HF8u HFceil HF4096 Hfa1 Hfa2 HTS HFapp Hfapp ]; lia. }
(* s1 and sp: rebind them to the atom 60 = sp1 (the engine cannot place a store through a masked address). *)
assert (E12 : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ regs) (-96) E12) in Rsp2 by lia.
rewrite (denot_and_m32_add0 Ev1 2 (spZ regs) (-96) E12) in Rs12 by lia.
replace (32 * ((spZ regs + -96) / 32)) with sp1 in Rsp2, Rs12 by (unfold sp1, OPEN_FRAME; f_equal; f_equal; lia).
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1]) as E2v eqn:HE2 in HS.
assert (OLD2 : forall nn, (nn < 60)%nat -> ew E2v nn = ew Ev1 nn) by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E2v 60 = Z_to_bv 64 sp1) by (rewrite HE2; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env VAL A_LIM E2v) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
clear HE2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
(* The flag FL (atom 61) and the shadow SH = SB + F / 8 (atom 62). *)
pose proof (st_ok_pi_havoc_hi 61 E2v _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 61)%nat -> ew E3v nn = ew E2v nn) by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E61 : ew E3v 61 = Z_to_bv 64 FL)
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 (SB_OP + F / 8))
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SB_OP + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI3 : img_env VAL A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
clear HE3.
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD3, OLD2 by lia; exact E12).
assert (E3_10 : ew E3v 10 = Z_to_bv 64 ps) by (rewrite OLD3, OLD2, OLD1 by lia; exact E10).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 SB_OP) by (rewrite OLD3, OLD2, OLD1 by lia; exact E32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3, OLD2 by lia; exact E44).
assert (E3_60 : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite OLD3 by lia; exact E60).
assert (Hsp1_hi : sp1 + 96 <= spZ regs) by lia.
assert (Hsp1_lo : alloc_ceiling <= sp1) by lia.
assert (HF8 : (SB_OP + F / 8) mod 8 = 0).
{ unfold SB_OP. pose proof (Z_div_mod_eq_full F 64) as D. rewrite HFa64, Z.add_0_r in D.
  assert (F / 8 = 8 * (F / 64)) as ->.
  { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_60, unsigned_lit_small by lia; change (2 ^ 5) with 32; repeat split; lia).
add_fact HS 44%nat (HPTR 6)
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E3_44, unsigned_lit_small by lia; change (2 ^ 6) with 64; repeat split; lia).
add_fact HS 61%nat (HPTR 0)
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E61, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia).
assert (HA62 : afact_ok E3v 62 (mkAF SB_OP (SB_OP + 2 ^ 44) 3)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E62.
  rewrite unsigned_lit_small by (unfold SB_OP; clear - HF8b; lia).
  change (2 ^ 3) with 8. split; [|split; [exact HF8 | lia]]. unfold SB_OP. clear - HF8b. lia. }
add_fact HS 62%nat (mkAF SB_OP (SB_OP + 2 ^ 44) 3) ltac:(exact HA62).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 44 32 62 F SB_OP E3_44 ltac:(lia) E3_32 E62)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* The frame's three regions: s1's word (0x814f8 `sd s6,0(s1)`), F (the header at 0..24, the flag pointer at 120),
   F's 16 shadow bytes (zero, __asan_stack_malloc_1's zero_shadow; one CZero chunk, which the engine splits around
   the bytes the prologue writes, so bytes 12..15 stay known). *)
assert (ZB : forall i, 0 <= i < 16 -> mbyte SEGS (mrestrict (w_H W) mem2) (SB_OP + F / 8 + 0 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold zero_shadow in Hz. pose proof (Hz i ltac:(change (128 / 8) with 16; lia)) as Hzi.
  unfold shadow_of_addr in Hzi. destruct (aview_byte SEGS _ _ _ _ Hzi) as (bb & Hbb & Hv & _).
  replace (SB_OP + F / 8 + 0 + i) with (SHADOW_OFF + F / 8 + i) by (unfold SB_OP, SHADOW_OFF; lia).
  rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity. }
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E3_60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = SB_OP + F / 8) by (rewrite E62; apply unsigned_lit_small; unfold SB_OP; lia).
assert (U3_10 : bv_unsigned (ew E3v 10) = ps) by (rewrite E3_10; apply unsigned_lit_small; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ regs) by (rewrite E3_2; apply unsigned_lit_small; lia).
assert (HFLb : 4096 <= FL < alloc_ceiling) by (destruct HFLrng as (_ & ? & _ & ?); lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 8 0 8 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply Hpres2; lia)
  ltac:(op_disj U60 U44 U62 U3_10 U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS _ _ F 120 8 _ FL);
          [cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
          | replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
  ltac:(op_disj U60 U44 U62 U3_10 U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
  (fshadow_region 62 1 0 16 [YP09.mkChunk 0 (CZero 16)]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold SB_OP; lia|]; split; [unfold SB_OP; lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS);
          replace (SB_OP + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SB_OP, SHADOW_OFF; lia);
          apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
        | apply Forall_cons; [apply chunk_ok_zero; exact ZB | apply Forall_nil] ])
  ltac:(op_disj U60 U44 U62 U3_10 U3_2; unfold SB_OP; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* ps's 24 bytes are still usable: their shadow lies in the caller's frame's shadow, which the call kept. *)
assert (HRms : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF ps 24).
{ pose proof SHOK as SH1. unfold sh_ok, op_SH in SH1. apply Forall_inv in SH1. destruct SH1 as (HR & _).
  cbn [she_m she_lo she_hi ms_mem restrict] in HR. unfold OBx in HR.
  rewrite (U_atom _ 32 SB_OP E32) in HR by (unfold SB_OP; lia). rewrite (U_atom _ 10 ps E10) in HR by lia.
  rewrite Z.add_0_r, Z.sub_0_r in HR. rewrite (aview_rd_of SEGS). exact HR. }
assert (HRm2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF ps 24).
{ apply (ra_frame (aview SEGS (w_H W) (ms_mem ms))); [exact HRms|].
  intros x Hx. unfold shadow_of_addr.
  pose proof HK as (_ & _ & _ & G4 & _).
  assert (Hx' : frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid) by lia.
  pose proof (div8_frame _ _ x Hfa64 Hfb64 Hx') as Hd.
  apply (G4 cid pos (SHADOW_OFF + x / 8) Hin); [right; unfold in_zr, shadow_addr; cbn [fst snd]; lia | intros []]. }
clear SHOK.
(* H3: the frame's header and shadow (no shadow check on this segment: the plain engine), up to the call of
   libreac_fuzz_fopen (0x81570). *)
paj_run_shc RUNP RUNC HS HJ2.
{ op_awr (spZ regs) sp0 U3_2; op_awr_close Hown F fpos cid pos. }
(* ---- libreac_fuzz_fopen (0x81570), under the caller's journal (YC85.v cl_callS) ---- *)
(* What the two runs and __asan_stack_malloc_1 kept. *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zop HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?Usp, ?U10 in HrrW; unfold Zop; cbv beta; clear - HrrW HTS; lia|]); destruct HinW)) as UN1.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zop HFr0
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U62, ?U44, ?U60, ?U3_2, ?U3_10 in HrrW; unfold Zop; cbv beta;
                clear - HrrW Hsp1r HTS; lia|]); destruct HinW)) as UN3.
pose proof HK as (K1 & K2 & K3 & K4 & _).
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Hia Ho He. pose proof (pa_img_range a Hia) as Ha. unfold pcap_img_end, YImgTop.IMG_TOP in Ha.
  rewrite (UN3 a) by (unfold Zop; cbv beta; clear - Ha HF8b HFimg Hsp1_lo Hsp1_hi C1 Hfimg Hfa1 Hfa2 HTS Hspc; unfold SB_OP; lia).
  rewrite (K3 a Hia Ho He). apply UN1; unfold Zop; cbv beta; clear - Ha Hsp1_lo Hsp1_hi C1 Hfimg HFimg Hfa1 Hfa2 HTS Hspc HF8b HF8c; unfold SB_OP; lia. }
assert (KTOP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha.
  rewrite (UN3 a) by (unfold Zop; cbv beta; clear - Ha HF8b HFceil Hsp1_lo Hsp1_hi C1 Hfa2 Hfceil HTS Hspc; unfold SB_OP; lia).
  rewrite (K1 a) by (clear - Ha Hsp1_lo Hsp1_hi; lia).
  apply UN1; unfold Zop; cbv beta; clear - Ha Hsp1_lo Hsp1_hi Hfa2 Hfceil C1 HTS Hspc HF8b HF8c HFceil; unfold SB_OP; lia. }
assert (KBLK : forall a, In (b, n) (ablocks B lyc Sc) -> b <= a < b + n ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Hb Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & Hb4096 & Hbceil & Hbia & _).
  pose proof (req_size_pos n ltac:(clear - Hn; lia)) as [_ Hrs].
  pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b n cid pos HAR Hb Hin) as D1.
  pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b n 1 fpos HAR2 ltac:(rewrite Eab; exact Hb) Hfin2) as D2.
  unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2. fold F in D2. change (fs_frame_bytes 1) with 128 in D2.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hbia.
  rewrite (UN3 a) by (unfold Zop; cbv beta; clear - Ha Hrs Hb4096 Hbceil Hbia D1 D2 HF8b HF8c HF8m HFceil C1 Hsp1_lo Hsp1_hi Hfa1 Hfa2 HTS Hspc; unfold SB_OP; lia).
  replace a with (b + (a - b)) by ring. rewrite (K2 b n (a - b) Hb ltac:(clear - Ha Hrs; lia) (fun H => H)).
  apply UN1; unfold Zop; cbv beta; clear - Ha Hrs Hb4096 Hbceil C1 Hspc D1 D2 Hfa1 Hfa2 HTS HF8b HF8c Hbia; unfold SB_OP; lia. }
assert (KENV : forall a, asrc_env_addr K a -> mbyte SEGS (rdW W (ms_mem ms0)) a = mbyte SEGS (rdW W memc) a).
{ intros a Ha. destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). apply (mbyte_of_aview SEGS). exact (KIMG a Hi Ho He). }
(* The call state's registers and the saved ra / s0 (the stack region's chunks -8 and -16). *)
pmkst HS. rewrite pa_sigma_libreac_fuzz_fopen.
sreg HS (1%bv : bv 5) R1c. sreg HS (2%bv : bv 5) R2c. sreg HS (3%bv : bv 5) R3c. sreg HS (4%bv : bv 5) R4c.
sreg HS (8%bv : bv 5) R8c. sreg HS (10%bv : bv 5) R10c. sreg HS (11%bv : bv 5) R11c.
assert (EA3 : forall a, (A_TEXT <= a < A_LIM)%nat -> ew E3v a = Z_to_bv 64 (VAL a))
  by (intros a Ha; rewrite <- (HEI3 a Ha); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (pa_val_range A_TEXT) as HVT.
assert (RA : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (symaddr ((Symbols.Asan.s_pcap_source_open + 0x118) - Symbols.Asan.s_libreac_fuzz_fopen)%Z))).
{ rewrite R1c. cbn [sv_denot]. change 240%nat with A_TEXT. rewrite (EA3 A_TEXT) by (unfold A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by exact HVT. reflexivity. }
assert (RSP : getr (ms_regs ms0) 2 = Z_to_bv 64 sp1) by (rewrite R2c; exact (sv_off0 _ _ _ E3_60)).
assert (RGP : getr (ms_regs ms0) 3 = getr regs 3) by (rewrite R3c; apply sv_off0; rewrite OLD3, OLD2, OLD1 by lia; exact E3).
assert (RTP : getr (ms_regs ms0) 4 = getr regs 4) by (rewrite R4c; apply sv_off0; rewrite OLD3, OLD2, OLD1 by lia; exact E4).
assert (RS0 : getr (ms_regs ms0) 8 = Z_to_bv 64 (spZ regs)) by (rewrite R8c; exact (sv_off0 _ _ _ E3_2)).
assert (RA0 : getr (ms_regs ms0) 10 = getr regs 11) by (rewrite R10c; apply sv_off0; rewrite OLD3, OLD2, OLD1 by lia; exact E11).
assert (RA1 : getr (ms_regs ms0) 11 = Z_to_bv 64 (VAL (A_OBJ 12))).
{ rewrite R11c. apply sv_off0. change 253%nat with (A_OBJ 12). apply EA3. unfold A_OBJ, A_TEXT, A_LIM. lia. }
clear R1c R2c R3c R4c R8c R10c R11c.
sregion HS 3%nat HRst.
assert (Hrr : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; exact (bv_unsigned_in_range _ (getr regs 1))).
assert (Hs0r : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; exact (bv_unsigned_in_range _ (getr regs 8))).
pose proof (field_of_region E3v _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HRst U3_2
  ltac:(cbn; repeat (first [left; reflexivity | right]))
  ltac:(apply sv_off0; rewrite OLD3, OLD2, OLD1 by lia; rewrite E1; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn; exact Hrr) ltac:(cbn; lia)) as VRA.
pose proof (field_of_region E3v _ 2%nat (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HRst U3_2
  ltac:(cbn; repeat (first [left; reflexivity | right]))
  ltac:(apply sv_off0; rewrite OLD3, OLD2, OLD1 by lia; rewrite E8; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(cbn; exact Hs0r) ltac:(cbn; lia)) as VS0.
change (N.to_nat 8) with 8%nat in VRA, VS0.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem ms0) _ _ VRA Hrr) as RDra.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem ms0) _ _ VS0 Hs0r) as RDs0.
assert (HCH1 : achain lyc (aview SEGS (w_H W) (ms_mem ms0)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  assert (Hsp8 : spZ regs mod 8 = 0).
  { pose proof (Z_div_mod_eq_full (spZ regs) 16) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by ring. apply Z_mod_mult. }
  apply (achain_push lyc (aview SEGS (w_H W) memc)).
  - exact Hch.
  - rewrite Etop. clear - Htop H47. lia.
  - exact KTOP.
  - replace (spZ regs - 8) with (spZ regs + -8) by ring. exact RDra.
  - replace (spZ regs - 16) with (spZ regs + -16) by ring. exact RDs0.
  - exact Hra4.
  - clear - Hsp1_lo Hsp1_hi. lia.
  - exact Hsp8.
  - clear - Htop32. lia.
  - clear - Hsp1_hi. lia. }
set (mdC := with_vm_backing (m_vm_lazy md2) mat0 md2) in *.
eapply SRr_bind.
{ eapply (cl_callS (PI := PI) B LAWS W (ms_regs ms0) (ms_mem ms0) _ STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 mdC k
    LIBREAC_FUZZ_FOPEN_STK afmemopen_fp EV_FUZZ_FOPEN (sp1 - sp0) (Z_to_bv 64 (BASE + (symaddr ((Symbols.Asan.s_pcap_source_open + 0x118) - Symbols.Asan.s_libreac_fuzz_fopen)%Z)))
    ((spZ regs, raZ regs, s0Z regs) :: ch)
    (fun ly3 S3 W3 regs3 mem3 md3 => exists h : Z, getr regs3 10 = w64 h /\ frames S3 = frames S2 /\
       m_fds md3 = m_fds mdC /\ m_fs md3 = m_fs mdC /\
       (n = 0 -> h = 0 /\ ablocks B ly3 S3 = ablocks B lyc S2 /\ asource_none SEGS K (rdW W3 mem3) /\ mo_le MT S2 S3 0) /\
       (1 <= n -> 4096 <= h /\ h mod 16 = 0 /\ ablocks B ly3 S3 = ablocks B lyc S2 ++ [(h, SRC_FILE_BLOCK)] /\
          asource_unbuffered SEGS K (rdW W3 mem3) h b C 0 /\ mo_le MT S2 S3 (mo_malloc MT SRC_FILE_BLOCK)))
    HJ2).
  - unfold spZ at 1. rewrite RSP, unsigned_lit_small by (clear - Hsp1_lo C1 Hsp1_hi Hwhi H47 Hshi; lia). ring.
  - rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
  - clear - Hsp1_hi Hwhi. lia.
  - unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK. lia.
  - unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK. rewrite HTS in Hwlo. clear - Hwlo Hsp1r. lia.
  - rewrite RGP. exact Hgp.
  - rewrite RTP. exact Htp.
  - exact RA.
  - apply ret_ok_codeptr_v; [clear - HBASE HBLO; lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE HBLO; lia). clear - HBASE HBLO. lia.
  - replace (sp0 + (sp1 - sp0)) with sp1 by ring. unfold s0Z. rewrite RS0, unsigned_lit_small by (clear - Hsp1_lo Hsp1_hi C1 Hwhi Hshi H47; lia).
    exact HCH1.
  - intros HPRE. eapply SRr_mono.
    { eapply (FOPEN lyc S2 W (ms_regs ms0) (ms_mem ms0) mdC _ n b C HPRE).
      + cbn [spine map fst snd]. exact Hctx.
      + rewrite RA0. exact H11.
      + rewrite RA1, HMODE. reflexivity.
      + apply (ROIMG_KEPT (rdW W memc)); [|exact HRO].
        intros a Ha. destruct (HGRO a Ha) as (Hro & Ho & He).
        apply (mbyte_of_aview SEGS). apply KIMG; [|exact Ho | exact He].
        destruct Hro as [(sg & Hs & _ & Hr) | Hrel]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
      + exact (proj1 (HPATH _ _ _ _ _ (proj1 HJ2))).
      + exact (proj2 (HPATH _ _ _ _ _ (proj1 HJ2))).
      + apply (vm_frame (rdW W memc)); [|exact HVn]. intros x Hx. apply (mbyte_of_aview SEGS).
        destruct (HGX x ltac:(left; clear - Hx; change (Z.of_nat 8) with 8 in Hx; lia)) as (Hi & Ho & He). exact (KIMG x Hi Ho He).
      + apply (vm_frame (rdW W memc)); [|exact HVb]. intros x Hx. apply (mbyte_of_aview SEGS).
        destruct (HGX x ltac:(right; clear - Hx; change (Z.of_nat 8) with 8 in Hx; lia)) as (Hi & Ho & He). exact (KIMG x Hi Ho He).
      + exact Hb64.
      + apply (asource_none_frame (rdW W memc)); [exact KENV | exact HNONE].
      + exact Hn.
      + exact HnC.
      + intros Hn1. destruct (Hinput Hn1) as (Hbin & Hg & Hbo). split; [rewrite Eab; exact Hbin|]. split; [|exact Hbo].
        apply (garr8_frame SEGS (rdW W memc) _ _ _ Hg). intros x Hx. apply (mbyte_of_aview SEGS).
        apply KBLK; [exact Hbin | rewrite Hn; exact Hx].
      + rewrite Hnev2. unfold EV_OPEN in Hev. clear - Hev. lia.
      + rewrite Hbb2. exact Hlive.
      + rewrite ES2. apply (mo_ok_set_fs MT MLAWF). exact MOK.
      + exact HU0.
      + exact HUC. }
    cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJf & HPf & HQf).
    exists ly3, S3, regs3, mem3, md3. rewrite RA. split; [reflexivity|]. split; [exact HJf|]. split; [exact HPf | exact HQf].
  - intros a Ha. left. unfold afmemopen_fp, inFP in Ha. destruct Ha as (r & [<- | []] & Hr).
    unfold YI16.sink_token in Hr. cbn [fst snd] in Hr. replace a with 0 by (clear - Hr; lia). exact HFP0. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (h & Ha03 & Hfrs3 & Hfds3 & Hfs3 & Hn0 & Hn1)).
(* ---- after libreac_fuzz_fopen: the five regions are kept (the callee's journal: its window lies below s1, and the
   frames of S2 with their shadows are kept off its footprint, the sink token) ---- *)
replace (sp0 + (sp1 - sp0)) with sp1 in HJc3 by ring.
pose proof HJc3 as (_ & Hly3 & _ & _ & _ & _ & _ & _ & F31 & _ & _ & F34 & _).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
assert (Efa3 : forall c q, frame_addr ly3 c q = frame_addr lyc c q).
{ intros c q. unfold frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact Hin2).
assert (NFP : forall a, a <> 0 -> ~ inFP afmemopen_fp a).
{ intros a Ha (r & [<- | []] & Hr). unfold YI16.sink_token in Hr. cbn [fst snd] in Hr. lia. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (_ & _ & HFpres3 & HFSpres3).
rewrite Efa3 in HFpres3, HFSpres3. fold F in HFpres3, HFSpres3. change (fs_frame_bytes 1) with 128 in HFpres3, HFSpres3.
change (128 / 8) with 16 in HFSpres3.
assert (HPS3 : forall a, ps <= a < ps + 24 -> apresent (w_H W3) mem3 a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ3 _)).
  right. right. right. exists cid, pos. split; [right; exact Hown|]. left. unfold in_zr. cbn [fst snd]. rewrite Efa3.
  clear - Ha Hfa1 Hfa2. lia. }
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3; 4; 5]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val fframe_region fshadow_region];
    rewrite ?U62, ?U44, ?U60, ?U3_2, ?U3_10; intros a Ha; try change (fs_frame_bytes 1) with 128 in Ha;
    try change (128 / 8) with 16 in Ha.
  - apply (mbyte_of_aview SEGS). apply (F34 1 fpos a Hfin2).
    + right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F. change (fs_frame_bytes 1 / 8) with 16.
      change SHADOW_OFF with SB_OP. clear - Ha. lia.
    + apply NFP. clear - Ha HF8b. unfold SB_OP in Ha. lia.
  - intros _. apply (apresent_writable SEGS).
    replace a with (shadow_addr F + (a - (SB_OP + F / 8))) by (unfold shadow_addr; change SHADOW_OFF with SB_OP; ring).
    apply (proj1 (HFSpres3 (a - (SB_OP + F / 8)) ltac:(clear - Ha; lia))).
  - apply (mbyte_of_aview SEGS). apply (F34 1 fpos a Hfin2).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 1) with 128. clear - Ha. lia.
    + apply NFP. clear - Ha HFb. lia.
  - intros _. apply (apresent_writable SEGS). apply (proj1 (HFpres3 a ltac:(clear - Ha; lia))).
  - apply (mbyte_of_aview SEGS). apply F31; clear - Ha Hsp1_lo Hsp1_hi C1 Hwhi Hshi H47; unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK; lia.
  - intros _. apply (apresent_writable SEGS). apply Hpres3. clear - Ha Hsp1_hi Hwhi Hwlo HTS Hsp1r. rewrite HTS in Hwlo. lia.
  - apply (mbyte_of_aview SEGS). apply F31; clear - Ha Hsp1_lo Hsp1_hi C1 Hwhi Hshi H47; unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK; lia.
  - intros _. apply (apresent_writable SEGS). apply Hpres3. clear - Ha Hwhi Hwlo HTS. rewrite HTS in Hwlo. lia.
  - apply (mbyte_of_aview SEGS). apply (F34 cid pos a Hin2).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. clear - Ha Hfa1 Hfa2. lia.
    + apply NFP. clear - Ha Hf4096 Hfa1. lia.
  - intros _. apply (apresent_writable SEGS). apply HPS3. clear - Ha. lia.
  - apply (mbyte_of_aview SEGS). apply (F34 cid pos a Hin2).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. clear - Ha Hfa1 Hfa2. lia.
    + apply NFP. clear - Ha Hf4096 Hfa1. lia.
  - intros _. apply (apresent_writable SEGS). apply HPS3. clear - Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3v 64 (map (getr regs3) CLOB)) as E4v eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4v) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall nn, (nn < 64)%nat -> ew E4v nn = ew E3v nn) by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
clear HE4.
prreg HS (10%bv : bv 5) R10h.
assert (E68 : ew E4v 68 = Z_to_bv 64 h) by (rewrite <- R10h, Ha03; reflexivity). clear R10h.
assert (U4_60 : bv_unsigned (ew E4v 60) = sp1) by (rewrite OLD4 by lia; exact U60).
assert (U4_44 : bv_unsigned (ew E4v 44) = F) by (rewrite OLD4 by lia; exact U44).
assert (U4_62 : bv_unsigned (ew E4v 62) = SB_OP + F / 8) by (rewrite OLD4 by lia; exact U62).
assert (U4_10 : bv_unsigned (ew E4v 10) = ps) by (rewrite OLD4 by lia; exact U3_10).
assert (U4_2 : bv_unsigned (ew E4v 2) = spZ regs) by (rewrite OLD4 by lia; exact U3_2).
assert (E4_32 : ew E4v 32 = Z_to_bv 64 SB_OP) by (rewrite OLD4 by lia; exact E3_32).
assert (E4_10 : ew E4v 10 = Z_to_bv 64 ps) by (rewrite OLD4 by lia; exact E3_10).
assert (E4_60 : ew E4v 60 = Z_to_bv 64 sp1) by (rewrite OLD4 by lia; exact E3_60).
assert (E4_44 : ew E4v 44 = Z_to_bv 64 F) by (rewrite OLD4 by lia; exact E3_44).
assert (E4_62 : ew E4v 62 = Z_to_bv 64 (SB_OP + F / 8)) by (rewrite OLD4 by lia; exact E62).
assert (E4_2 : ew E4v 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD4 by lia; exact E3_2).
assert (E4_11 : ew E4v 11 = getr regs 11) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E11).
assert (E4_3 : ew E4v 3 = getr regs 3) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E3).
assert (E4_4 : ew E4v 4 = getr regs 4) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E4).
assert (E4_25 : ew E4v 25 = getr regs 25) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E25).
assert (E4_26 : ew E4v 26 = getr regs 26) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E26).
assert (E4_27 : ew E4v 27 = getr regs 27) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E27).
assert (E4_1 : ew E4v 1 = getr regs 1) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E1).
assert (E4_8 : ew E4v 8 = getr regs 8) by (rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact E8).
(* ps's shadow is still usable: kept by H3 (off its windows) and by libreac_fuzz_fopen (a frame of S2's shadow). *)
assert (HRm3 : range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF ps 24).
{ apply (ra_frame (aview SEGS (w_H W) mem2)); [exact HRm2|].
  intros x Hx. unfold shadow_of_addr.
  assert (Hx' : frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid) by (clear - Hx Hfa1 Hfa2; lia).
  pose proof (div8_frame _ _ x Hfa64 Hfb64 Hx') as Hd.
  destruct (div8_of_mul64 F HFa64) as [EF8 EF]. destruct (div8_of_mul64 _ Hfa64) as [Efr8 Efr].
  destruct (div8_of_mul64 _ Hfb64) as [Efb8 Efb].
  assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; clear - Hx' Hf4096 Hfceil C1; lia).
  rewrite (F34 cid pos (SHADOW_OFF + x / 8) Hin2).
  - pose proof (HdFs cid pos Hin) as Hds. unfold shadow_addr in Hds. change SHADOW_OFF with SB_OP in Hds.
    apply UN3; unfold Zop; cbv beta; unfold SHADOW_OFF, SB_OP in *;
      clear - Hx8 Hd Hds EF8 EF Efr8 Efr Efb8 Efb Hfb HdFps HFapp Hfapp Hfa1 Hfa2 Hspc HTS C1 Hx HF8b HF8c; lia.
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. clear - Hd. lia.
  - apply NFP. unfold SHADOW_OFF. clear - Hx8. lia. }
assert (SHOK4 : sh_ok SEGS OBx op_SH E4v (mrestrict (w_H W3) mem3)).
{ apply (shent_op_ok _ _ ps).
  + unfold OBx. rewrite (U_atom _ 32 SB_OP E4_32) by (unfold SB_OP; lia). reflexivity.
  + rewrite (U_atom _ 10 ps E4_10) by lia. reflexivity.
  + unfold in_app, kLowShadowBeg, kHighMemBeg in Hfapp. clear - Hfapp Hfa1 Hfa2. unfold kLowShadowBeg, kHighMemBeg. lia.
  + rewrite <- (aview_rd_of SEGS). exact HRm3. }
(* F's shadow region and F are read-only on H4: the token engine needs every writable window off the shadow span
   (cells_safe_b), and F's interval fact [4096, 2^47) does not exclude it. H4 writes neither. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (ro_upto 2 rs) in
  pose proof (st_ok_pi_submem Ex ssx msx rs' HS ltac:(submem_to) ltac:(vm_compute; reflexivity)) as HS2;
  clear HS; rename HS2 into HS end.
norm_pi HS.
(* The test of f (0x815d4 beqz a3): f = NULL exactly for the empty input. *)
paj_run_to_tok RUNTO HS HJ3 SHOK4 OPspan (symaddr ((Symbols.Asan.s_pcap_source_open + 0x178) - Symbols.Asan.s_libreac_fuzz_fopen)%Z);
  [ op_awr (spZ regs) sp0 U4_2; op_awr_close3 Hown F fpos cid pos Efa3 |].
psrr_branch_tok RUN BR HS SHOK4 OPspan.
- (* taken: libreac_fuzz_fopen returned NULL, so the input was empty (0x81660) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (ESET : forall nn, (nn < 512)%nat -> ew Ex nn = ew E4v nn)
      by (intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity) end.
  assert (Hn00 : n = 0).
  { destruct (Z.eq_dec n 0) as [Hz0 | Hne]; [exact Hz0|]. exfalso.
    destruct (Hn1 ltac:(clear - Hne Hn HnC; lia)) as (H4096 & Hm16 & Eab3' & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ h SRC_FILE_BLOCK HAR3
      ltac:(rewrite Eab3'; apply in_or_app; right; left; reflexivity)) as (_ & _ & Hhc & _).
    change (req_size SRC_FILE_BLOCK) with 1304 in Hhc.
    revert Hc. rewrite branch_eq_U, U_SLit. change (zcanon 0) with 0.
    rewrite (U_atom _ 68%nat h ltac:(rewrite ESET by lia; exact E68)) by (clear - H4096 Hhc C1; lia).
    intros Hq. apply Z.eqb_eq in Hq. clear - Hq H4096. lia. }
  destruct (Hn0 Hn00) as (Hh0 & Eab3 & HNONE3 & MLE3). subst h.
  paj_run_to_tok RUNTO HS HJ3 SHOK4 OPspan (symaddr ((Symbols.Asan.s_pcap_source_open + 0x204) - Symbols.Asan.s_libreac_fuzz_fopen)%Z);
    [ op_awr (spZ regs) sp0 U4_2; op_awr_close3 Hown F fpos cid pos Efa3 |].
  (* what the whole call kept of the caller's memory, composed over the five steps *)
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zop HFr1
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                  rewrite ?U4_62, ?U4_44, ?U4_60, ?U4_2, ?U4_10 in HrrW; unfold Zop; cbv beta;
                  clear - HrrW Hsp1r HTS; lia|]);
          destruct HinW)) as UN4.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zop HFr2
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                  rewrite !ESET in HrrW by lia;
                  rewrite ?U4_62, ?U4_44, ?U4_60, ?U4_2, ?U4_10 in HrrW; unfold Zop; cbv beta;
                  clear - HrrW Hsp1r HTS; lia|]);
          destruct HinW)) as UN5.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP2' & _).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP5' & _).
  assert (HP4' : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows (w_H W3) mem3 (ms_mem ms1) a HG1 (Hpres3 a Ha))).
  assert (TKALL : topen_kept SK SEGS B lyc Sc W memc W3 (ms_mem ms2)
                    (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) Eop).
  { eapply tk_trans; [eapply tk_trans; [eapply tk_trans; [eapply tk_trans; [eapply tk_trans|]|]|]|].
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W memc (ms_mem ms) Zop UN1 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W) memc (ms_mem ms) a HG Hp)
               (fun a Ha => HP1 a ltac:(clear - Ha Hwlo Hwhi HTS; lia))).
    - pose proof HK as (M1 & M2 & M3 & M4 & M5 & _).
      split; [intros a Ha Hs; apply M1; [exact Ha | clear - Hs Hsp1r HTS; lia]|].
      split; [intros bb mm i Hb Hi He; apply (M2 bb mm i Hb Hi); intros []|].
      split; [intros a Hi Hns He _; exact (M3 a Hi Hns He)|].
      split; [intros c q a Hf Hr He; apply (M4 c q a Hf Hr); intros []|].
      split; [intros a Ha Hs Hp; apply M5; [exact Ha | clear - Hs Hsp1r HTS; lia | exact Hp]|].
      intros a Ha. apply Hpres2. clear - Ha Hwlo Hwhi HTS. lia.
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W mem2 (ms_mem ms0) Zop UN3 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W) mem2 (ms_mem ms0) a HG0 Hp)
               (fun a Ha => HP2' a ltac:(clear - Ha Hwlo Hwhi HTS; lia))).
    - eapply tk_weaken; [rewrite Eab; exact (fun bb mm H => H) | rewrite Hfrs2; intros c q Hcq; right; exact Hcq |].
      eapply (tk_of_journal lyc S2 W mem2 md2 HAR2 _ _ Eop); [exact HJc3 | exact (proj1 HJ2) | | | | |].
      + intros a Haf. unfold afmemopen_fp, inFP in Haf. destruct Haf as (r & [<- | []] & Hr).
        unfold YI16.sink_token in Hr. cbn [fst snd] in Hr. clear - Hr. lia.
      + intros bb mm i Hb Hi He. rewrite Eab3. exact Hb.
      + clear - Hsp1r HTS Hwlo Hwhi. unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK. lia.
      + clear - Hsp1r HTS. lia.
      + intros a Ha. apply Hpres3. clear - Ha Hwlo Hwhi HTS. lia.
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W3 mem3 (ms_mem ms1) Zop UN4 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W3) mem3 (ms_mem ms1) a HG1 Hp)
               (fun a Ha => HP4' a ltac:(clear - Ha Hwlo Hwhi HTS; lia))).
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W3 (ms_mem ms1) (ms_mem ms2) Zop UN5 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W3) (ms_mem ms1) (ms_mem ms2) a HG2 Hp)
               (fun a Ha => HP5' a ltac:(clear - Ha Hwlo Hwhi HTS; lia))). }
  (* ---- the NULL cut (0x81660): the state op_gi_null names, then PcapSourceOpenB's op_from_null ---- *)
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HMS. cbn [ss_pc] in HMS.
  destruct (op_ms_shape _ _ _ _ HMS) as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & Zpc).
  rewrite wvb_collapse in HJ3.
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & F33 & _ & _ & _ & _ & F35 & _).
  pose proof HJe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _ & _ & _ & _ & Eextra3 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & Eslo & Eshi & _).
  assert (Hps8d : 0 <= ps / 8 <= ps) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (bv_unsigned_in_range _ (getr regs 2))).
  assert (Hsp8 : spZ regs mod 8 = 0).
  { pose proof (Z_div_mod_eq_full (spZ regs) 16) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by ring. apply Z_mod_mult. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (U5_2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ESET by lia; exact U4_2);
    assert (U5_44 : bv_unsigned (ew Ex 44) = F) by (rewrite ESET by lia; exact U4_44);
    assert (U5_62 : bv_unsigned (ew Ex 62) = SB_OP + F / 8) by (rewrite ESET by lia; exact U4_62);
    assert (U5_10 : bv_unsigned (ew Ex 10) = ps) by (rewrite ESET by lia; exact U4_10);
    assert (E5_61 : ew Ex 61 = Z_to_bv 64 FL) by (rewrite ESET by lia; rewrite OLD4 by lia; exact E61);
    assert (E5_68 : ew Ex 68 = Z_to_bv 64 0) by (rewrite ESET by lia; exact E68);
    assert (EA5 : forall a : nat, (A_TEXT <= a < A_LIM)%nat -> ew Ex a = Z_to_bv 64 (VAL a))
      by (intros a Ha; rewrite ESET by (unfold A_TEXT, A_LIM in Ha; lia);
          rewrite <- (HEI4 a Ha); symmetry; apply Z_to_bv_bv_unsigned);
    assert (EREG5 : forall r : nat, (r < 32)%nat -> ew Ex r = getr regs (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr; rewrite ESET by lia; rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact (EREG r Hr))
  end.
  (* the registers the cut names (0x81494, 0x814f8..0x81570, 0x81578..0x815d0) *)
  op_cut_regs HS Q.
  assert (R2v : getr (ms_regs ms2) 2 = w64 sp1) by (rewrite Q2; apply sv_off0; rewrite ESET by lia; exact E4_60).
  assert (R8v : getr (ms_regs ms2) 8 = w64 (spZ regs)) by (rewrite Q8; apply sv_off0; rewrite ESET by lia; exact E4_2).
  assert (R9v : getr (ms_regs ms2) 9 = w64 sp1) by (rewrite Q9; apply sv_off0; rewrite ESET by lia; exact E4_60).
  assert (R18v : getr (ms_regs ms2) 18 = w64 F) by (rewrite Q18; apply sv_off0; rewrite ESET by lia; exact E4_44).
  assert (R19v : getr (ms_regs ms2) 19 = w64 ps) by (rewrite Q19; apply sv_off0; rewrite ESET by lia; exact E4_10).
  assert (R20v : getr (ms_regs ms2) 20 = w64 (VAL (A_OBJ 3)))
    by (rewrite Q20; apply sv_off0; rewrite ESET by lia; rewrite E4_11; exact H11).
  assert (R21v : getr (ms_regs ms2) 21 = w64 (SB_OP + F / 8))
    by (rewrite Q21; apply sv_off0; rewrite ESET by lia; exact E4_62).
  assert (R22v : getr (ms_regs ms2) 22 = w64 F) by (rewrite Q22; apply sv_off0; rewrite ESET by lia; exact E4_44).
  assert (R23v : getr (ms_regs ms2) 23 = w64 SB_OP) by (rewrite Q23; apply sv_off0; rewrite ESET by lia; exact E4_32).
  assert (R24v : getr (ms_regs ms2) 24 = w64 (SB_OP + ps / 8)).
  { rewrite Q24. apply (denot_shadow_cell _ 10 32 ps SB_OP);
      [rewrite ESET by lia; exact E4_10 | lia | rewrite ESET by lia; exact E4_32
      | unfold SB_OP; lia | unfold SB_OP; lia]. }
  assert (R25v : getr (ms_regs ms2) 25 = w64 (bv_unsigned (getr regs 25))).
  { rewrite Q25. apply sv_off0. rewrite ESET by lia. rewrite E4_25. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R3v : getr (ms_regs ms2) 3 = getr regs 3) by (rewrite Q3; apply sv_off0; rewrite ESET by lia; exact E4_3).
  assert (R4v : getr (ms_regs ms2) 4 = getr regs 4) by (rewrite Q4; apply sv_off0; rewrite ESET by lia; exact E4_4).
  assert (R26v : getr (ms_regs ms2) 26 = getr regs 26) by (rewrite Q26; apply sv_off0; rewrite ESET by lia; exact E4_26).
  assert (R27v : getr (ms_regs ms2) 27 = getr regs 27) by (rewrite Q27; apply sv_off0; rewrite ESET by lia; exact E4_27).
  (* the memory the cut names, off the engine's five regions *)
  spregion HS 0%nat HRsh. spregion HS 1%nat HRfr. spregion HS 3%nat HRstk.
  spregion HS 4%nat HRlo. spregion HS 5%nat HRhi.
  destruct (op_saves _ _ _ regs (spZ regs) U5_2 EREG5 HRstk) as (RDra8 & RDsav).
  destruct (op_hdr _ _ _ F FL U5_44 E5_61 ltac:(clear - HFLb C1; lia)
    (EA5 (A_OBJ 10) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    (EA5 (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) HRfr) as (RDmag & RDh8 & RDh16 & RDflag).
  pose proof (op_shadow _ _ _ (SB_OP + F / 8) U5_62 HRsh) as RDsh.
  destruct (op_psfields _ _ _ ps 0 U5_10 E5_68 ltac:(lia) HRlo HRhi) as (Vpsf & Vps12 & Vps16 & Vps20).
  (* what the two runs after libreac_fuzz_fopen kept, and what the whole call kept *)
  assert (UNrun : forall a, 0 <= a < 2 ^ 64 -> ~ Zop a ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) mem3 a)
    by (intros a Ha HnZ; rewrite (UN5 a Ha HnZ); exact (UN4 a Ha HnZ)).
  assert (KIMG2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> a < AOFL_HEAD ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
  { intros a Hi Ho He Hlt.
    pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    rewrite (UNrun a ltac:(clear - Hr; lia) ltac:(intros HZ; exact (Zop_img a HZ Hi))).
    rewrite (F33 a Hi Ho He (fp_spares_below afmemopen_fp a Hlt)). exact (KIMG a Hi Ho He). }
  assert (KGAP : forall i, 8 <= i < 12 ->
    aview SEGS (w_H W3) (ms_mem ms2) (ps + i) = aview SEGS (w_H W) memc (ps + i)).
  { intros i Hi.
    assert (Ha64 : 0 <= ps + i < 2 ^ 64) by (clear - Hi Hps64 Hfa2 Hfapp Hfceil C1; lia).
    assert (HnZ : ~ Zop (ps + i)).
    { unfold Zop; cbv beta.
      clear - Hi Hfa1 Hfa2 Hfceil Hfapp Hf4096 HF8b HF8c HdFps HFb Hspc HTS C1. unfold SB_OP. lia. }
    rewrite (UNrun (ps + i) Ha64 HnZ).
    rewrite (F34 cid pos (ps + i) Hin2
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Hi Hfa1 Hfa2; lia)
      ltac:(apply NFP; clear - Hi Hfa1 Hf4096; lia)).
    rewrite (UN3 (ps + i) Ha64 HnZ).
    rewrite (K4 cid pos (ps + i) Hin
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Hi Hfa1 Hfa2; lia) ltac:(intros [])).
    exact (UN1 (ps + i) Ha64 HnZ). }
  assert (HNONE5 : asource_none SEGS K (rdW W3 (ms_mem ms2))).
  { apply (asource_none_frame (rdW W3 mem3)); [|exact HNONE3].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _ & _).
    pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    exact (UNrun a ltac:(clear - Hr; lia) ltac:(intros HZ; exact (Zop_img a HZ Hi))). }
  assert (IMGZ : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a ->
    in_img SEGS a /\ 0 <= a < 2 ^ 64 /\ ~ Zop a).
  { intros a Hro.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hs & _ & Hr) | Hrel];
          [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)]).
    pose proof (pa_img_range a Hi) as Hr2. unfold pcap_img_end, YImgTop.IMG_TOP in Hr2.
    split; [exact Hi|]. split; [clear - Hr2; lia|]. intros HZ. exact (Zop_img a HZ Hi). }
  assert (HROD3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms2))).
  { apply (op_rod_frame (aview SEGS (w_H W3) mem3));
      [intros a Hro _ _; destruct (IMGZ a Hro) as (_ & Ha & HnZ); exact (UNrun a Ha HnZ)|].
    eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJc3|].
    apply (op_rod_frame (aview SEGS (w_H W) mem2));
      [intros a Hro _ _; destruct (IMGZ a Hro) as (_ & Ha & HnZ); exact (UN3 a Ha HnZ)|].
    eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJe|].
    apply (op_rod_frame (aview SEGS (w_H W) memc));
      [intros a Hro _ _; destruct (IMGZ a Hro) as (_ & Ha & HnZ); exact (UN1 a Ha HnZ)|].
    exact HROD. }
  (* the interceptor's meta region: off this call's write set, and kept by both callees *)
  assert (KEXTRA : forall a, M <= a < M + AMETA_SIZE ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
  { intros a Ha.
    pose proof HMETA as (HXm & _ & _ & _ & _ & _ & _ & _).
    assert (HXa : Exists (in_zr a) (ly_extra lyc))
      by (apply Exists_exists; exists (M, AMETA_SIZE); split;
          [exact HXm | unfold in_zr; cbn [fst snd]; clear - Ha; lia]).
    destruct (AR_extra_law_ok SEGS B lyc S2 W mem2 md2 a HAR2 HXa) as (_ & _ & Xf & Xs & Xi & Xsh & Xapp).
    assert (Hne : ~ (as_errno B <= a < as_errno B + 4))
      by (intros He; exact (Xi (asil_errno_img _ _ _ _ ASIL a He))).
    assert (Ha64 : 0 <= a < 2 ^ 64)
      by (pose proof HMETA as (_ & _ & _ & _ & H0m' & H47m' & _); clear - Ha H0m' H47m'; lia).
    assert (HnZ : ~ Zop a).
    { destruct (Xf 1 fpos ltac:(rewrite Hfrs2; left; reflexivity)) as (XfF & XfS).
      destruct (Xf cid pos Hin2) as (Xfp & _).
      change (fs_frame_bytes 1) with 128 in XfF, XfS. fold F in XfF, XfS.
      unfold shadow_addr, SHADOW_OFF in XfS. rewrite Eslo, Eshi in Xs.
      unfold Zop; cbv beta. unfold SB_OP. try change (128 / 8) with 16 in XfS.
      intros [Z1 | [Z2 | [Z3 | [Z4 | Z5]]]].
      + apply Xs. clear - Z1 Hslo Hshi Hwlo Hwhi. lia.
      + apply XfS. clear - Z2. lia.
      + apply XfF. exact Z3.
      + apply Xfp. clear - Z4 Hfa1 Hfa2. lia.
      + apply Xfp. clear - Z5 Hfa1 Hfa2. lia. }
    rewrite (UNrun a Ha64 HnZ). rewrite (F35 a HXa Hne). rewrite (UN3 a Ha64 HnZ).
    rewrite (K35 a HXa Hne). exact (UN1 a Ha64 HnZ). }
  assert (HMETA3 : asrc_meta_inv SEGS K ly3 (rdW W3 (ms_mem ms2)) M).
  { pose proof HMETA as (HXm & Himgm & _ & Hmm & H0m & H47m & Halm & HZm).
    split; [rewrite Eextra3; exact HXm|]. split; [exact Himgm|].
    split; [exact (asrc_meta_ptr_of_AR SK SEGS B K ASIL _ _ _ _ _ (proj1 HJ3))|].
    split.
    { eapply vm_frame; [|exact Hmm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
      destruct (asil_meta _ _ _ _ ASIL x ltac:(clear - Hx; lia)) as (Hi & Hns & He & Hlt).
      exact (KIMG2 x Hi Hns He Hlt). }
    split; [exact H0m|]. split; [exact H47m|]. split; [exact Halm|].
    intros a Ha. rewrite <- (HZm a Ha). apply (mbyte_of_aview SEGS). exact (KEXTRA a Ha). }
  (* the call chain: the caller's, with this call's frame record on top *)
  assert (KTOP2 : forall a, spZ regs <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
  { intros a Ha.
    assert (HnZ : ~ Zop a)
      by (intros HZ; destruct (Zop_ceil a HZ ltac:(clear - Ha Hspc C1; lia)) as (_ & Hlt);
          clear - Ha Hlt; lia).
    rewrite (UNrun a ltac:(clear - Ha Hsp64; lia) HnZ).
    rewrite (F31 a ltac:(clear - Ha Hspc C1; lia)
      ltac:(clear - Ha Hsp1_hi; unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK; lia)).
    exact (KTOP a Ha). }
  assert (HCH3 : achain ly3 (aview SEGS (w_H W3) (ms_mem ms2)) sp1 (spZ regs)
                   ((spZ regs, raZ regs, s0Z regs) :: ch)).
  { apply (achain_ly_top lyc ly3 _ _ _ _ Etop3).
    pose proof (RDsav 0 ltac:(lia)) as RD16.
    replace (spZ regs - 16 - 8 * 0) with (spZ regs - 16) in RD16 by ring.
    apply (achain_push lyc (aview SEGS (w_H W) memc)).
    - exact Hch.
    - rewrite Etopc. clear - Htop H47. lia.
    - exact KTOP2.
    - exact RDra8.
    - exact RD16.
    - exact Hra4.
    - clear - Hsp1_lo Hsp1_hi. lia.
    - exact Hsp8.
    - clear - Htop32. lia.
    - clear - Hsp1_hi. lia. }
  (* the descriptors and the file system: the frame call's journal is sink-closed, the fopen call states them *)
  assert (HNSO : ~ YI16.sink_open_fp (@nil (Z * Z))) by (intros (r & [] & _)).
  assert (HFDS : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc)
    by (eapply (ajournal_closed_fs SK SEGS B); [exact HNSO | exact HJe]).
  assert (Efds : m_fds (with_vm_backing (m_vm_lazy md3) mat2 md3) = m_fds mdc).
  { rewrite md_fds_wvb, Hfds3. unfold mdC. rewrite md_fds_wvb. exact (proj1 HFDS). }
  assert (Efss : m_fs (with_vm_backing (m_vm_lazy md3) mat2 md3) = m_fs mdc).
  { rewrite md_fs_wvb, Hfs3. unfold mdC. rewrite md_fs_wvb. exact (proj2 HFDS). }
  (* ---- the two sides of op_from_null ---- *)
  assert (HPRE : op_pre SK B K MT FM_RA CTX ro_img
    (mkOCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)).
  { unfold op_pre. cbv zeta.
    cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs
         o_ch o_ps o_n o_b o_M o_C o_cid o_pos].
    split; [exact HJ0|]. split; [exact HROD|]. split; [exact Hraw|]. split; [exact Hra4|].
    split; [exact Hgp|]. split; [exact Htp|]. split; [exact H10|]. split; [exact H11|].
    split; [exact Hch|]. split; [exact Hctx|]. split; [exact Hal16|]. split; [exact Hwlo|].
    split; [exact Hwhi|]. split; [exact Htop32|]. split; [exact Hnfr|]. split; [exact Hown|].
    split; [exact Hfa1|]. split; [exact Hfa2|]. split; [exact Hps0|]. split; [exact Hps8|].
    split; [exact Hsh|]. split; [exact HFP0|]. split; [exact HRO|]. split; [exact HPra|].
    split; [exact HPhull|]. split; [exact HVn|]. split; [exact HVb|]. split; [exact Hb64|].
    split; [exact HNONE|]. split; [exact Hn|]. split; [exact HnC|]. split; [exact Hinput|].
    split; [exact HMETA|]. split; [exact Hev|]. split; [exact Hlive|]. split; [exact MOK|].
    split; [exact HU0 | exact HUC]. }
  apply (OPB_NULL (mkOCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)
           fpos ly3 S3 W3 ms2 (with_vm_backing (m_vm_lazy md3) mat2 md3) HPRE).
  unfold op_gi_null, op_mid. cbv zeta.
  cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs
       o_ch o_ps o_n o_b o_M o_C o_cid o_pos].
  unfold oSH, oFL, osp1, oF.
  cbn [o_lyc o_regs o_ps o_C o_n o_b o_k o_own o_Sc o_W o_memc o_mdc o_STK o_sp0 o_FP o_ly o_S
       o_W0 o_mem0 o_md0 o_ch o_M o_cid o_pos].
  split; [exact Zpc|].
  split.
  { split; [exact Zrsv|]. split; [exact Zsvc|]. split; [exact Zrom|]. split; [exact Zfrg|].
    split; [exact Zfcsr|].
    split; [exact HJ3|]. split; [clear; lia|].
    split; [clear - Hnev3 Hnev2; unfold EV_FUZZ_FOPEN in Hnev3; lia|].
    split; [rewrite Hfrs3; exact Hfrs2|]. split; [exact Hnin|].
    split; [exact (op_set_fs_eta S3)|].
    split; [exact R2v|]. split; [exact R8v|]. split; [exact R9v|]. split; [exact R18v|].
    split; [exact R19v|]. split; [exact R20v|]. split; [exact R21v|]. split; [exact R22v|].
    split; [exact R23v|]. split; [exact R24v|]. split; [exact R25v|].
    split; [exact R3v|]. split; [exact R4v|]. split; [exact R26v|]. split; [exact R27v|].
    split; [exact RDra8|]. split; [exact RDsav|].
    split; [exact RDmag|]. split; [exact RDh8|]. split; [exact RDh16|]. split; [exact RDflag|].
    split; [reflexivity|]. split; [exact RDsh|].
    split; [exact Vpsf|]. split; [exact Vps12|]. split; [exact Vps16|]. split; [exact Vps20|].
    split; [exact KGAP|].
    split; [exact TKALL|].
    split; [exact Efds|]. split; [exact Efss|].
    split; [exact HMETA3|]. split; [exact HROD3|]. exact HCH3. }
  split; [exact Hn00|].
  split; [rewrite Eab3; exact Eab|].
  split; [exact HNONE5|].
  exact (mo_le_set_fs_l MT MLAWF Sc S3 fS2 0 ltac:(rewrite <- ES2; exact MLE3)).
- (* not taken: the stream is open; hand the arm at 0x815d8 to op_read_arm_obl (OPR) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (ESET : forall nn, (nn < 512)%nat -> ew Ex nn = ew E4v nn)
      by (intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity) end.
  (* f <> NULL, so the input is not empty *)
  assert (Hn1' : 1 <= n).
  { destruct (Z.eq_dec n 0) as [Hz0 | Hne]; [|clear - Hne Hn; lia].
    exfalso. destruct (Hn0 Hz0) as (Hh0 & _).
    revert Hc. rewrite branch_eq_U, U_SLit. change (zcanon 0) with 0.
    rewrite (U_atom _ 68%nat h ltac:(rewrite ESET by lia; exact E68)) by (rewrite Hh0; lia).
    rewrite Hh0. intros Hq. cbn in Hq. discriminate Hq. }
  destruct (Hn1 Hn1') as (Hh4096 & Hh16 & Eab3 & HUNB & MLE3).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ h SRC_FILE_BLOCK HAR3
    ltac:(rewrite Eab3; apply in_or_app; right; left; reflexivity)) as (_ & _ & Hhc & Hhapp & _).
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhc, Hhapp.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hhapp.
  paj_run_to_tok RUNTO HS HJ3 SHOK4 OPspan (symaddr ((Symbols.Asan.s_pcap_source_open + 0x17c) - Symbols.Asan.s_libreac_fuzz_fopen)%Z);
    [ op_awr (spZ regs) sp0 U4_2; op_awr_close3 Hown F fpos cid pos Efa3 |].
  (* what the whole call kept of the caller's memory, composed over the five steps *)
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zop HFr1
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                  rewrite ?U4_62, ?U4_44, ?U4_60, ?U4_2, ?U4_10 in HrrW; unfold Zop; cbv beta;
                  clear - HrrW Hsp1r HTS; lia|]);
          destruct HinW)) as UN4.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zop HFr2
    ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
          repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                  rewrite !ESET in HrrW by lia;
                  rewrite ?U4_62, ?U4_44, ?U4_60, ?U4_2, ?U4_10 in HrrW; unfold Zop; cbv beta;
                  clear - HrrW Hsp1r HTS; lia|]);
          destruct HinW)) as UN5.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP1 & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP2' & _).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP5' & _).
  assert (HP4' : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows (w_H W3) mem3 (ms_mem ms1) a HG1 (Hpres3 a Ha))).
  assert (TKALL : topen_kept SK SEGS B lyc Sc W memc W3 (ms_mem ms2)
                    (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) Eop).
  { eapply tk_trans; [eapply tk_trans; [eapply tk_trans; [eapply tk_trans; [eapply tk_trans|]|]|]|].
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W memc (ms_mem ms) Zop UN1 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W) memc (ms_mem ms) a HG Hp)
               (fun a Ha => HP1 a ltac:(clear - Ha Hwlo Hwhi HTS; lia))).
    - pose proof HK as (M1 & M2 & M3 & M4 & M5 & _).
      split; [intros a Ha Hs; apply M1; [exact Ha | clear - Hs Hsp1r HTS; lia]|].
      split; [intros bb mm i Hb Hi He; apply (M2 bb mm i Hb Hi); intros []|].
      split; [intros a Hi Hns He _; exact (M3 a Hi Hns He)|].
      split; [intros c q a Hf Hr He; apply (M4 c q a Hf Hr); intros []|].
      split; [intros a Ha Hs Hp; apply M5; [exact Ha | clear - Hs Hsp1r HTS; lia | exact Hp]|].
      intros a Ha. apply Hpres2. clear - Ha Hwlo Hwhi HTS. lia.
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W mem2 (ms_mem ms0) Zop UN3 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W) mem2 (ms_mem ms0) a HG0 Hp)
               (fun a Ha => HP2' a ltac:(clear - Ha Hwlo Hwhi HTS; lia))).
    - eapply tk_weaken; [rewrite Eab; exact (fun bb mm H => H) | rewrite Hfrs2; intros c q Hcq; right; exact Hcq |].
      eapply (tk_of_journal lyc S2 W mem2 md2 HAR2 _ _ Eop); [exact HJc3 | exact (proj1 HJ2) | | | | |].
      + intros a Haf. unfold afmemopen_fp, inFP in Haf. destruct Haf as (r & [<- | []] & Hr).
        unfold YI16.sink_token in Hr. cbn [fst snd] in Hr. clear - Hr. lia.
      + intros bb mm i Hb Hi He. rewrite Eab3. apply in_or_app. left. exact Hb.
      + clear - Hsp1r HTS Hwlo Hwhi. unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK. lia.
      + clear - Hsp1r HTS. lia.
      + intros a Ha. apply Hpres3. clear - Ha Hwlo Hwhi HTS. lia.
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W3 mem3 (ms_mem ms1) Zop UN4 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W3) mem3 (ms_mem ms1) a HG1 Hp)
               (fun a Ha => HP4' a ltac:(clear - Ha Hwlo Hwhi HTS; lia))).
    - exact (tk_of_un lyc Sc W memc mdc HAR _ _ Eop W3 (ms_mem ms1) (ms_mem ms2) Zop UN5 Zop_ceil Zop_blk Zop_img Zop_frm
               (fun a Hp => apresent_grows (w_H W3) (ms_mem ms1) (ms_mem ms2) a HG2 Hp)
               (fun a Ha => HP5' a ltac:(clear - Ha Hwlo Hwhi HTS; lia))). }
  (* ---- the arm's state (0x815d8): the same op_mid as the NULL cut, with f in ps->f and a3 ---- *)
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as HMS. cbn [ss_pc] in HMS.
  destruct (op_ms_shape _ _ _ _ HMS) as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & Zpc).
  rewrite wvb_collapse in HJ3.
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & F33 & _ & _ & _ & _ & F35 & _).
  pose proof HJe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _ & _ & _ & _ & Eextra3 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & Eslo & Eshi & _).
  assert (Hps8d : 0 <= ps / 8 <= ps) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (bv_unsigned_in_range _ (getr regs 2))).
  assert (Hh64 : 0 <= h < 2 ^ 64) by (clear - Hh4096 Hhc C1; lia).
  assert (Hsp8 : spZ regs mod 8 = 0).
  { pose proof (Z_div_mod_eq_full (spZ regs) 16) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by ring. apply Z_mod_mult. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (U5_2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite ESET by lia; exact U4_2);
    assert (U5_44 : bv_unsigned (ew Ex 44) = F) by (rewrite ESET by lia; exact U4_44);
    assert (U5_62 : bv_unsigned (ew Ex 62) = SB_OP + F / 8) by (rewrite ESET by lia; exact U4_62);
    assert (U5_10 : bv_unsigned (ew Ex 10) = ps) by (rewrite ESET by lia; exact U4_10);
    assert (E5_61 : ew Ex 61 = Z_to_bv 64 FL) by (rewrite ESET by lia; rewrite OLD4 by lia; exact E61);
    assert (E5_68 : ew Ex 68 = Z_to_bv 64 h) by (rewrite ESET by lia; exact E68);
    assert (EA5 : forall a : nat, (A_TEXT <= a < A_LIM)%nat -> ew Ex a = Z_to_bv 64 (VAL a))
      by (intros a Ha; rewrite ESET by (unfold A_TEXT, A_LIM in Ha; lia);
          rewrite <- (HEI4 a Ha); symmetry; apply Z_to_bv_bv_unsigned);
    assert (EREG5 : forall r : nat, (r < 32)%nat -> ew Ex r = getr regs (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr; rewrite ESET by lia; rewrite OLD4, OLD3, OLD2, OLD1 by lia; exact (EREG r Hr))
  end.
  op_cut_regs HS Q. prreg_raw HS (13%bv : bv 5) Q13.
  assert (R13v : getr (ms_regs ms2) 13 = w64 h) by (rewrite Q13; apply sv_off0; exact E5_68).
  assert (R2v : getr (ms_regs ms2) 2 = w64 sp1) by (rewrite Q2; apply sv_off0; rewrite ESET by lia; exact E4_60).
  assert (R8v : getr (ms_regs ms2) 8 = w64 (spZ regs)) by (rewrite Q8; apply sv_off0; rewrite ESET by lia; exact E4_2).
  assert (R9v : getr (ms_regs ms2) 9 = w64 sp1) by (rewrite Q9; apply sv_off0; rewrite ESET by lia; exact E4_60).
  assert (R18v : getr (ms_regs ms2) 18 = w64 F) by (rewrite Q18; apply sv_off0; rewrite ESET by lia; exact E4_44).
  assert (R19v : getr (ms_regs ms2) 19 = w64 ps) by (rewrite Q19; apply sv_off0; rewrite ESET by lia; exact E4_10).
  assert (R20v : getr (ms_regs ms2) 20 = w64 (VAL (A_OBJ 3)))
    by (rewrite Q20; apply sv_off0; rewrite ESET by lia; rewrite E4_11; exact H11).
  assert (R21v : getr (ms_regs ms2) 21 = w64 (SB_OP + F / 8))
    by (rewrite Q21; apply sv_off0; rewrite ESET by lia; exact E4_62).
  assert (R22v : getr (ms_regs ms2) 22 = w64 F) by (rewrite Q22; apply sv_off0; rewrite ESET by lia; exact E4_44).
  assert (R23v : getr (ms_regs ms2) 23 = w64 SB_OP) by (rewrite Q23; apply sv_off0; rewrite ESET by lia; exact E4_32).
  assert (R24v : getr (ms_regs ms2) 24 = w64 (SB_OP + ps / 8)).
  { rewrite Q24. apply (denot_shadow_cell _ 10 32 ps SB_OP);
      [rewrite ESET by lia; exact E4_10 | lia | rewrite ESET by lia; exact E4_32
      | unfold SB_OP; lia | unfold SB_OP; lia]. }
  assert (R25v : getr (ms_regs ms2) 25 = w64 (bv_unsigned (getr regs 25))).
  { rewrite Q25. apply sv_off0. rewrite ESET by lia. rewrite E4_25. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R3v : getr (ms_regs ms2) 3 = getr regs 3) by (rewrite Q3; apply sv_off0; rewrite ESET by lia; exact E4_3).
  assert (R4v : getr (ms_regs ms2) 4 = getr regs 4) by (rewrite Q4; apply sv_off0; rewrite ESET by lia; exact E4_4).
  assert (R26v : getr (ms_regs ms2) 26 = getr regs 26) by (rewrite Q26; apply sv_off0; rewrite ESET by lia; exact E4_26).
  assert (R27v : getr (ms_regs ms2) 27 = getr regs 27) by (rewrite Q27; apply sv_off0; rewrite ESET by lia; exact E4_27).
  spregion HS 0%nat HRsh. spregion HS 1%nat HRfr. spregion HS 3%nat HRstk.
  spregion HS 4%nat HRlo. spregion HS 5%nat HRhi.
  destruct (op_saves _ _ _ regs (spZ regs) U5_2 EREG5 HRstk) as (RDra8 & RDsav).
  destruct (op_hdr _ _ _ F FL U5_44 E5_61 ltac:(clear - HFLb C1; lia)
    (EA5 (A_OBJ 10) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    (EA5 (A_OBJ 11) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) HRfr) as (RDmag & RDh8 & RDh16 & RDflag).
  pose proof (op_shadow _ _ _ (SB_OP + F / 8) U5_62 HRsh) as RDsh.
  destruct (op_psfields _ _ _ ps h U5_10 E5_68 Hh64 HRlo HRhi) as (Vpsf & Vps12 & Vps16 & Vps20).
  assert (UNrun : forall a, 0 <= a < 2 ^ 64 -> ~ Zop a ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) mem3 a)
    by (intros a Ha HnZ; rewrite (UN5 a Ha HnZ); exact (UN4 a Ha HnZ)).
  assert (KIMG2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> a < AOFL_HEAD ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
  { intros a Hi Ho He Hlt.
    pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    rewrite (UNrun a ltac:(clear - Hr; lia) ltac:(intros HZ; exact (Zop_img a HZ Hi))).
    rewrite (F33 a Hi Ho He (fp_spares_below afmemopen_fp a Hlt)). exact (KIMG a Hi Ho He). }
  assert (KGAP : forall i, 8 <= i < 12 ->
    aview SEGS (w_H W3) (ms_mem ms2) (ps + i) = aview SEGS (w_H W) memc (ps + i)).
  { intros i Hi.
    assert (Ha64 : 0 <= ps + i < 2 ^ 64) by (clear - Hi Hps64 Hfa2 Hfapp Hfceil C1; lia).
    assert (HnZ : ~ Zop (ps + i)).
    { unfold Zop; cbv beta.
      clear - Hi Hfa1 Hfa2 Hfceil Hfapp Hf4096 HF8b HF8c HdFps HFb Hspc HTS C1. unfold SB_OP. lia. }
    rewrite (UNrun (ps + i) Ha64 HnZ).
    rewrite (F34 cid pos (ps + i) Hin2
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Hi Hfa1 Hfa2; lia)
      ltac:(apply NFP; clear - Hi Hfa1 Hf4096; lia)).
    rewrite (UN3 (ps + i) Ha64 HnZ).
    rewrite (K4 cid pos (ps + i) Hin
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Hi Hfa1 Hfa2; lia) ltac:(intros [])).
    exact (UN1 (ps + i) Ha64 HnZ). }
  (* the open stream: its FILE block, the input buffer and the stdio environment are off Zop *)
  assert (HUNB5 : asource_unbuffered SEGS K (rdW W3 (ms_mem ms2)) h b C 0).
  { apply (op_unbuf_frame (rdW W3 mem3)); [|exact HUNB].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (Hinput Hn1') as (Hbin & _ & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hbin) as (_ & Hb4 & Hbc & Hbia & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hbia.
    pose proof (req_size_pos n ltac:(clear - Hn; lia)) as [_ Hrs].
    assert (HX : 0 <= a < 2 ^ 64 /\ ~ Zop a).
    { destruct Ha as [Ha | [Ha | Ha]].
      - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 h SRC_FILE_BLOCK 1 fpos HAR3
          ltac:(rewrite Eab3; apply in_or_app; right; left; reflexivity) Hfin3) as D1.
        pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 h SRC_FILE_BLOCK cid pos HAR3
          ltac:(rewrite Eab3; apply in_or_app; right; left; reflexivity) Hin3) as D2.
        unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2. rewrite !Efa3 in D1, D2. fold F in D1.
        change (req_size SRC_FILE_BLOCK) with 1304 in D1, D2. change (fs_frame_bytes 1) with 128 in D1.
        unfold SRC_FILE_BLOCK in Ha.
        split; [clear - Ha Hhc Hh4096 C1; lia|].
        unfold Zop; cbv beta. unfold SB_OP.
        intros [Z1 | [Z2 | [Z3 | [Z4 | Z5]]]].
        + clear - Z1 Ha Hhc Hspc HTS. lia.
        + clear - Z2 Ha Hhapp HF8b HF8c. lia.
        + clear - Z3 Ha D1. lia.
        + clear - Z4 Ha D2 Hfa1 Hfa2. lia.
        + clear - Z5 Ha D2 Hfa1 Hfa2. lia.
      - pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc b n cid pos HAR Hbin Hin) as D3.
        unfold zdisjoint in D3. cbn [fst snd] in D3.
        split; [clear - Ha Hbc Hb4 Hrs Hn C1; lia|].
        intros HZ. pose proof (Zop_blk a b n (a - b) HZ Hbin ltac:(ring) ltac:(clear - Ha Hn Hrs; lia)) as He.
        unfold Eop in He; cbv beta in He. clear - He D3 Hfa1 Hfa2 Ha Hn Hrs. lia.
      - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _ & _).
        pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
        split; [clear - Hr; lia | intros HZ; exact (Zop_img a HZ Hi)]. }
    destruct HX as (Ha64 & HnZ). exact (UNrun a Ha64 HnZ). }
  (* fclose's footprint: the FILE block is this call's (or, had the caller freed the same block earlier, the
     caller's journal footprint holds it), and the sink token is the caller's to spare *)
  assert (HFPinc : forall x, inFP (asource_fp h) x ->
    inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B ly3 S3) x).
  { intros x (r & Hr & Hx). destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hx.
    - destruct (in_dec (fun p q : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (h, SRC_FILE_BLOCK)
        (ablocks B ly S)) as [Hold | Hnew].
      + left.
        assert (Hnot : ~ In (h, SRC_FILE_BLOCK) (ablocks B lyc Sc)).
        { intros Hin'. destruct (in_split _ _ Hin') as (l1 & l2 & El).
          pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (h, SRC_FILE_BLOCK) (h, SRC_FILE_BLOCK)
            l1 l2 [] HAR3 ltac:(rewrite Eab3, Eab, El, <- app_assoc; reflexivity)) as Hd.
          unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size SRC_FILE_BLOCK) with 1304 in Hd.
          clear - Hd. lia. }
        pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
        replace x with (h + (x - h)) by ring.
        apply (Hgone h SRC_FILE_BLOCK (x - h) Hold Hnot).
        change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. clear - Hx. lia.
      + right. exists h, SRC_FILE_BLOCK. split; [rewrite Eab3; apply in_or_app; right; left; reflexivity|].
        split; [exact Hnew|]. change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. clear - Hx. lia.
    - left. unfold YI16.sink_token in Hx. cbn [fst snd] in Hx. replace x with 0 by (clear - Hx; lia). exact HFP0. }
  assert (IMGZ : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a ->
    in_img SEGS a /\ 0 <= a < 2 ^ 64 /\ ~ Zop a).
  { intros a Hro.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hs & _ & Hr) | Hrel];
          [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)]).
    pose proof (pa_img_range a Hi) as Hr2. unfold pcap_img_end, YImgTop.IMG_TOP in Hr2.
    split; [exact Hi|]. split; [clear - Hr2; lia|]. intros HZ. exact (Zop_img a HZ Hi). }
  assert (HROD3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms2))).
  { apply (op_rod_frame (aview SEGS (w_H W3) mem3));
      [intros a Hro _ _; destruct (IMGZ a Hro) as (_ & Ha & HnZ); exact (UNrun a Ha HnZ)|].
    eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJc3|].
    apply (op_rod_frame (aview SEGS (w_H W) mem2));
      [intros a Hro _ _; destruct (IMGZ a Hro) as (_ & Ha & HnZ); exact (UN3 a Ha HnZ)|].
    eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJe|].
    apply (op_rod_frame (aview SEGS (w_H W) memc));
      [intros a Hro _ _; destruct (IMGZ a Hro) as (_ & Ha & HnZ); exact (UN1 a Ha HnZ)|].
    exact HROD. }
  assert (KEXTRA : forall a, M <= a < M + AMETA_SIZE ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
  { intros a Ha.
    pose proof HMETA as (HXm & _ & _ & _ & _ & _ & _ & _).
    assert (HXa : Exists (in_zr a) (ly_extra lyc))
      by (apply Exists_exists; exists (M, AMETA_SIZE); split;
          [exact HXm | unfold in_zr; cbn [fst snd]; clear - Ha; lia]).
    destruct (AR_extra_law_ok SEGS B lyc S2 W mem2 md2 a HAR2 HXa) as (_ & _ & Xf & Xs & Xi & Xsh & Xapp).
    assert (Hne : ~ (as_errno B <= a < as_errno B + 4))
      by (intros He; exact (Xi (asil_errno_img _ _ _ _ ASIL a He))).
    assert (Ha64 : 0 <= a < 2 ^ 64)
      by (pose proof HMETA as (_ & _ & _ & _ & H0m' & H47m' & _); clear - Ha H0m' H47m'; lia).
    assert (HnZ : ~ Zop a).
    { destruct (Xf 1 fpos ltac:(rewrite Hfrs2; left; reflexivity)) as (XfF & XfS).
      destruct (Xf cid pos Hin2) as (Xfp & _).
      change (fs_frame_bytes 1) with 128 in XfF, XfS. fold F in XfF, XfS.
      unfold shadow_addr, SHADOW_OFF in XfS. rewrite Eslo, Eshi in Xs.
      unfold Zop; cbv beta. unfold SB_OP. try change (128 / 8) with 16 in XfS.
      intros [Z1 | [Z2 | [Z3 | [Z4 | Z5]]]].
      + apply Xs. clear - Z1 Hslo Hshi Hwlo Hwhi. lia.
      + apply XfS. clear - Z2. lia.
      + apply XfF. exact Z3.
      + apply Xfp. clear - Z4 Hfa1 Hfa2. lia.
      + apply Xfp. clear - Z5 Hfa1 Hfa2. lia. }
    rewrite (UNrun a Ha64 HnZ). rewrite (F35 a HXa Hne). rewrite (UN3 a Ha64 HnZ).
    rewrite (K35 a HXa Hne). exact (UN1 a Ha64 HnZ). }
  assert (HMETA3 : asrc_meta_inv SEGS K ly3 (rdW W3 (ms_mem ms2)) M).
  { pose proof HMETA as (HXm & Himgm & _ & Hmm & H0m & H47m & Halm & HZm).
    split; [rewrite Eextra3; exact HXm|]. split; [exact Himgm|].
    split; [exact (asrc_meta_ptr_of_AR SK SEGS B K ASIL _ _ _ _ _ (proj1 HJ3))|].
    split.
    { eapply vm_frame; [|exact Hmm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
      destruct (asil_meta _ _ _ _ ASIL x ltac:(clear - Hx; lia)) as (Hi & Hns & He & Hlt).
      exact (KIMG2 x Hi Hns He Hlt). }
    split; [exact H0m|]. split; [exact H47m|]. split; [exact Halm|].
    intros a Ha. rewrite <- (HZm a Ha). apply (mbyte_of_aview SEGS). exact (KEXTRA a Ha). }
  assert (KTOP2 : forall a, spZ regs <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
  { intros a Ha.
    assert (HnZ : ~ Zop a)
      by (intros HZ; destruct (Zop_ceil a HZ ltac:(clear - Ha Hspc C1; lia)) as (_ & Hlt);
          clear - Ha Hlt; lia).
    rewrite (UNrun a ltac:(clear - Ha Hsp64; lia) HnZ).
    rewrite (F31 a ltac:(clear - Ha Hspc C1; lia)
      ltac:(clear - Ha Hsp1_hi; unfold LIBREAC_FUZZ_FOPEN_STK, AFMEMOPEN_STK; lia)).
    exact (KTOP a Ha). }
  assert (HCH3 : achain ly3 (aview SEGS (w_H W3) (ms_mem ms2)) sp1 (spZ regs)
                   ((spZ regs, raZ regs, s0Z regs) :: ch)).
  { apply (achain_ly_top lyc ly3 _ _ _ _ Etop3).
    pose proof (RDsav 0 ltac:(lia)) as RD16.
    replace (spZ regs - 16 - 8 * 0) with (spZ regs - 16) in RD16 by ring.
    apply (achain_push lyc (aview SEGS (w_H W) memc)).
    - exact Hch.
    - rewrite Etopc. clear - Htop H47. lia.
    - exact KTOP2.
    - exact RDra8.
    - exact RD16.
    - exact Hra4.
    - clear - Hsp1_lo Hsp1_hi. lia.
    - exact Hsp8.
    - clear - Htop32. lia.
    - clear - Hsp1_hi. lia. }
  assert (HNSO : ~ YI16.sink_open_fp (@nil (Z * Z))) by (intros (r & [] & _)).
  assert (HFDS : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc)
    by (eapply (ajournal_closed_fs SK SEGS B); [exact HNSO | exact HJe]).
  assert (Efds : m_fds (with_vm_backing (m_vm_lazy md3) mat2 md3) = m_fds mdc).
  { rewrite md_fds_wvb, Hfds3. unfold mdC. rewrite md_fds_wvb. exact (proj1 HFDS). }
  assert (Efss : m_fs (with_vm_backing (m_vm_lazy md3) mat2 md3) = m_fs mdc).
  { rewrite md_fs_wvb, Hfs3. unfold mdC. rewrite md_fs_wvb. exact (proj2 HFDS). }
  assert (HPRE : op_pre SK B K MT FM_RA CTX ro_img
    (mkOCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)).
  { unfold op_pre. cbv zeta.
    cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs
         o_ch o_ps o_n o_b o_M o_C o_cid o_pos].
    split; [exact HJ0|]. split; [exact HROD|]. split; [exact Hraw|]. split; [exact Hra4|].
    split; [exact Hgp|]. split; [exact Htp|]. split; [exact H10|]. split; [exact H11|].
    split; [exact Hch|]. split; [exact Hctx|]. split; [exact Hal16|]. split; [exact Hwlo|].
    split; [exact Hwhi|]. split; [exact Htop32|]. split; [exact Hnfr|]. split; [exact Hown|].
    split; [exact Hfa1|]. split; [exact Hfa2|]. split; [exact Hps0|]. split; [exact Hps8|].
    split; [exact Hsh|]. split; [exact HFP0|]. split; [exact HRO|]. split; [exact HPra|].
    split; [exact HPhull|]. split; [exact HVn|]. split; [exact HVb|]. split; [exact Hb64|].
    split; [exact HNONE|]. split; [exact Hn|]. split; [exact HnC|]. split; [exact Hinput|].
    split; [exact HMETA|]. split; [exact Hev|]. split; [exact Hlive|]. split; [exact MOK|].
    split; [exact HU0 | exact HUC]. }
  apply (OPR (mkOCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos)
           fpos ly3 S3 W3 ms2 (with_vm_backing (m_vm_lazy md3) mat2 md3) HPRE).
  exists h. unfold op_arm_read, op_mid. cbv zeta.
  cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs
       o_ch o_ps o_n o_b o_M o_C o_cid o_pos].
  unfold oSH, oFL, osp1, oF.
  cbn [o_lyc o_regs o_ps o_C o_n o_b o_k o_own o_Sc o_W o_memc o_mdc o_STK o_sp0 o_FP o_ly o_S
       o_W0 o_mem0 o_md0 o_ch o_M o_cid o_pos].
  split; [exact Zpc|]. split; [exact R13v|].
  split.
  { split; [exact Zrsv|]. split; [exact Zsvc|]. split; [exact Zrom|]. split; [exact Zfrg|].
    split; [exact Zfcsr|].
    split; [exact HJ3|]. split; [clear; lia|].
    split; [clear - Hnev3 Hnev2; unfold EV_FUZZ_FOPEN in Hnev3; lia|].
    split; [rewrite Hfrs3; exact Hfrs2|]. split; [exact Hnin|].
    split; [exact (op_set_fs_eta S3)|].
    split; [exact R2v|]. split; [exact R8v|]. split; [exact R9v|]. split; [exact R18v|].
    split; [exact R19v|]. split; [exact R20v|]. split; [exact R21v|]. split; [exact R22v|].
    split; [exact R23v|]. split; [exact R24v|]. split; [exact R25v|].
    split; [exact R3v|]. split; [exact R4v|]. split; [exact R26v|]. split; [exact R27v|].
    split; [exact RDra8|]. split; [exact RDsav|].
    split; [exact RDmag|]. split; [exact RDh8|]. split; [exact RDh16|]. split; [exact RDflag|].
    split; [reflexivity|]. split; [exact RDsh|].
    split; [exact Vpsf|]. split; [exact Vps12|]. split; [exact Vps16|]. split; [exact Vps20|].
    split; [exact KGAP|].
    split; [exact TKALL|].
    split; [exact Efds|]. split; [exact Efss|].
    split; [exact HMETA3|]. split; [exact HROD3|]. exact HCH3. }
  split; [exact Hn1'|]. split; [exact Hh4096|]. split; [exact Hh16|].
  split; [rewrite Eab3, Eab; reflexivity|].
  split; [exact HUNB5|].
  split; [exact HFPinc|].
  exact (mo_le_set_fs_l MT MLAWF Sc S3 fS2 (mo_malloc MT SRC_FILE_BLOCK) ltac:(rewrite <- ES2; exact MLE3)).
Qed.

End e.
End d.
End b.

(* The audit: the walk's Section hypotheses are its premises; no axiom beyond the base's. *)
Print Assumptions pb_pcap_source_openX.
