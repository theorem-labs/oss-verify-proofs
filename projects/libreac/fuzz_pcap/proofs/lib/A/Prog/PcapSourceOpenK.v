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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names and numbers changed; 388 of its 508 lines of code are new or changed and 510 lines of the source are left out. *)
(* pcap_source_open (fuzz_pcap.asan 0x8145c) on libreac v1.9.0's ASan build: the shared, closed lemmas of its walk.
   PcapSourceOpen.v (the walk of the code, work in progress) uses them; PcapSourceOpenB.v walks from the two cuts
   of PcapSourceOpenPh.v. Everything here is Qed: the symbolic entry state and its st_ok (op_entry), the shadow
   entry of the caller's struct (shent_op_ok), the arithmetic of the realigned stack pointer and of the shadow
   cells (sp1_facts, land_m32, denot_and_m32, denot_and_m32_add0, denot_shadow_cell), the region trimming the
   engine needs (trim_stack, ro_upto), the frame-shadow arithmetic (div8_in, div8_of_mul64, div8_frame, ra_frame),
   and the composition of what the call keeps (topen_kept: tk_weaken, tk_trans, tk_of_un, tk_of_journal), with
   ro_img_chunks_kept and asource_none_frame for the image and the stream's environment. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs PcapSourceOpenDefs PcapSourceOpenPh.
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
Hypothesis HGX : forall a, (VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 8) \/ (VAL (A_OBJ 2) <= a < VAL (A_OBJ 2) + 8) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPATH : forall ly S W mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (VAL (A_OBJ 3)) 13.
(* Lane PcapSourceOpenB's two lemmas (lib/A/Prog/PcapSourceOpenB.v): the walk from each cut (PcapSourceOpenPh.v)
   to the post. *)
Hypothesis OPB_NULL : op_from SK B K MT FM_RA CTX ro_img (op_gi_null SK B K MT).
Hypothesis OPB_READ : op_from SK B K MT FM_RA CTX ro_img (op_gi_read SK B K MT).
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


End e.
End d.
End b.
