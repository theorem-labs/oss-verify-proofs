(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module names changed; 525 of its 590 lines of code are new or changed and 1486 lines of the source are left out. *)
(* pcap_source_open (fuzz_pcap.asan 0x8145c) on libreac v1.9.0's ASan build: the READ arm of its walk,
   PcapSourceOpenPh.v op_read_arm_obl, from the not-taken arm of the test of f (0x815d4 `beqz a3`) to the post.

   What it walks (listing offsets = address - 0x80738), from the arm state op_arm_read at 0x815d8 (OP_ARM_READ):
   - 0x815d8 `addi s4,s6,0x20`: s4 = F + 32, the 24-byte header buffer (OP_HDR);
   - 0x815dc..0x815e4 `sb zero,4..6(s5)`: the buffer's three shadow bytes go in scope (0xf8 -> 0), so the frame's
     shadow becomes OSH_in;
   - 0x815e8..0x815f4: a1 = 1, a2 = 24, s9 = 24, a0 = s4;
   - 0x815f8 `jal __interceptor_trampoline_fread`: fread(F + 32, 1, 24, f) through the wrapper, by its contract
     lib/A/Stdio/PFreadISpec.v afread_spec in the caller-journal form (the caller's journal extended, no event);
   - the return address 0x815fc (OP_CUT_READ): the READ cut op_gi_read, closed by lane B's
     PcapSourceOpenB.op_from_read.
   The walk 0x815d8..0x815f8 is one run of the plain engine (it has no shadow check: the three stores are the
   instrumentation's own shadow writes) over a seated state with one chunk-free region, F's shadow with the write
   window 4..7 (a Theorem Labs lane's SHADOW-SPEEDUP.md (sha256 8a139366a4e4; internal record) items 1-3: fresh seat, atoms for addresses, no chunks the stores do
   not read).

   ASan report edges: the range 0x815d8..0x815f8 has no branch, so no __asan_report entry edge. pcap_source_open's
   report calls 0x817b0..0x81818 are entered from 0x81580, 0x8159c, 0x815b4, 0x815cc (the head walk, before the arm)
   and 0x81650, 0x8166c, 0x81698, 0x816b0, 0x816c0 (PcapSourceOpenB.op_from_read, after the cut); a Theorem Labs lane's
   classify.out (sha256 88dae4bd2adf; internal record) lists the same pcap_source_open entry edges. The fread wrapper's own check
   of the destination's shadow (0x43568..0x435bc, region_is_poisoned 0x436a8) is decided inside afread_spec's proof
   from its premises range_addressable and shadow_hull_vis of (F + 32, 24), which this walk proves
   (or_dest_addressable, or_dest_hull below: the three shadow bytes are 0 after 0x815dc..0x815e4).

   Stack depth: the callee's window [s1 - AFREAD_STK, s1) lies in the caller's journal window, since
   sp0 - STK <= sp0' - TPCAP_SOURCE_OPEN_STK (op_pre) and s1 >= sp0' - 112, so s1 - 8192 >= sp0' - 8304 >= sp0' - 18736.
   No astk_ok conjunct is discharged here (afread_pre's rread_call states none).

   Callees and laws are Section hypotheses of their exact statement types: afread_spec (PFreadISpec.v), and, for
   op_from_read, the hypotheses of PcapSourceOpenB.v's Section (AR_laws, model_laws, astack_free_law,
   frame_flag_lawP, ameter_laws, ameter_fs_laws, asrc_file_meter, asource_img_laws, afclose_source_spec with its two
   universe facts). Every number is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...; image
   root: the ORIGINAL v1.9.0 pins, capstone disassembly of the unstripped twin fuzz_pcap.asan (sha256 36da3052c383)).

   TAKEN FROM (same branch): the cut's destructuring, the frame / block facts and the environment of
   PcapSourceOpenB.v:1778-1850 and 1870-1926 (op_from_read); the clause structure of the kept set across a write,
   PcapSourceOpenB.v:422-499 (opb_kept_step); the call's register facts, PcapSourceOpenB.v:2107-2140; the meta region
   across a journal, lib/A/Stdio/PSourceMeta.v:146-164 (asrc_meta_inv_kept), here between two journals with one
   start; the region lookup of PcapSourceOpenK.v:536-541 (sregion), inlined because a Section-local Ltac is not
   exported (nothing else of the kit is used, so the kit is not Required). *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YImgTop PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame YC45.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import
PSource PSourceMeta PSourceMeter PFreadM PFreadISpec PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import
PcapFuzzFopenDefs PcapSourceOpenDefs PcapSourceOpenPh PcapSourceOpenB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below uses the Section's SK. *)
Fail Definition or_sink_head_probe : YI16.sink_head := _.

(* ---- the seated state at the arm (0x815d8) ---------------------------------------------------------------- *)
(* F's 16 shadow bytes, based at s5 (atom 21), writable at 4..7 only (the stores 0x815dc..0x815e4); no chunk. *)
Definition or_FS : YP09.region := YP09.mkRegion (Some 21%nat) 0 16 4 7 [].
Definition or_ss : sstate := mkSS OP_ARM_READ sr_atoms [or_FS] None (mkFacts [] [] []).

(* The frame's shadow after the stores: OSH_out with bytes 4..6 in scope. *)
Lemma or_osh_out : forall i, (i < 16)%nat -> ~ (4 <= i < 7)%nat -> nth i OSH_in 0 = nth i OSH_out 0.
Proof. intros i Hi Hn. do 16 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). lia. Qed.
Lemma or_osh_mid : forall i, (4 <= i < 7)%nat -> nth i OSH_in 0 = 0.
Proof. intros i Hi. do 7 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable roimg : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
Hypothesis ASIL : asource_img_laws SK SEGS B K.
(* The fread wrapper's 4-byte jump (0x41580 on the pin), lib/A/Stdio/PFreadISpec.v. *)
Hypothesis AFREAD : afread_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fread).
(* The fclose wrapper, for PcapSourceOpenB.op_from_read (its two closing calls 0x81674 / 0x816b8). *)
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B K (SIGMA PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Let RUNP := SRr_run_pi_AJ (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PI := PI) B LAWS.

(* The meta region between two journals with one start (PSourceMeta.v:146-164 asrc_meta_inv_kept, rebased): both
   end states hold the start's bytes on the meta region and the meta cell. *)
Lemma or_meta_rebase : forall STK sp0 FP ly S W mem md own ly3 S3 W3 m3 md3 k3 ly5 S5 W5 m5 md5 k5 M,
  ajournal SEGS B STK sp0 FP ly S W mem md own ly3 S3 W3 m3 md3 k3 ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly5 S5 W5 m5 md5 k5 ->
  asrc_meta_inv SEGS K ly3 (rdW W3 m3) M -> asrc_meta_inv SEGS K ly5 (rdW W5 m5) M.
Proof.
intros STK sp0 FP ly S W mem md own ly3 S3 W3 m3 md3 k3 ly5 S5 W5 m5 md5 k5 M HJa HJb
  (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ).
pose proof HJa as (_ & Hlya & _ & _ & _ & _ & _ & _ & _ & _ & Fa3 & _ & _ & _ & _ & Fa5 & _).
pose proof HJb as (HARb & Hlyb & _ & _ & _ & _ & _ & _ & _ & _ & Fb3 & _ & _ & _ & _ & Fb5 & _).
pose proof Hlya as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Exa & _).
pose proof Hlyb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Exb & _).
assert (HX5 : In (M, AMETA_SIZE) (ly_extra ly5)) by (rewrite Exb, <- Exa; exact HX).
assert (HXl : forall a, M <= a < M + AMETA_SIZE -> Exists (in_zr a) (ly_extra ly)).
{ intros a Ha. apply Exists_exists. exists (M, AMETA_SIZE).
  split; [rewrite <- Exa; exact HX | unfold in_zr; cbn [fst snd]; lia]. }
split; [exact HX5|]. split; [exact Himg|].
split; [exact (asrc_meta_ptr_of_AR SK SEGS B K ASIL _ _ _ _ _ HARb)|].
split.
- eapply opb_vm_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
  rewrite (Fb3 x Hi Hns He (fp_spares_below FP x Hlt)), (Fa3 x Hi Hns He (fp_spares_below FP x Hlt)).
  reflexivity.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  assert (Hne : ~ (as_errno B <= a < as_errno B + 4)).
  { intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi.
    destruct (AR_extra_law_ok SEGS B ly5 S5 W5 m5 md5 a HARb
      ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX5 | unfold in_zr; cbn [fst snd]; lia]))
      as (_ & _ & _ & _ & Hni & _).
    exact (Hni Hi). }
  rewrite (Fb5 a (HXl a Ha) Hne), (Fa5 a (HXl a Ha) Hne). reflexivity.
Qed.

Theorem op_read_arm : op_read_arm_obl SK B K MT FM_RA CTX roimg.
Proof.
assert (OPB_READ : op_from SK B K MT FM_RA CTX roimg (op_gi_read SK B K MT))
  by (eapply op_from_read; eassumption).
unfold op_read_arm_obl, op_from.
intros cx fpos ly3 S3 W3 ms3 md3 HPRE (f & HG).
unfold op_arm_read in HG. cbv zeta in HG.
destruct HG as (Hpc & Ha3 & HM & Hn1 & Hf4096 & Hf16 & Hab & HUNB & HFPinc & Hmo).
unfold op_mid in HM. cbv zeta in HM.
destruct HM as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ3 & Hkk & Hnev3 & Hfrs3 & Hnin & Hfs3 & M2 & M8 & M9 &
  M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M3 & M4 & M26 & M27 & Hra8 & Hsav & Hhdr0 & Hhdr8 & Hhdr16 &
  Hflagp & Hshlen & Hshb & Hvf & Hv12 & Hv16 & Hv20 & Hkeep8 & HKEPT & Hfds & Hfsm & HMETA3 & HROD3 & Hchain3).
pose proof HPRE as HPRE'. unfold op_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HJ & HROD & Hraw & Hra4 & Hgp & Htp & _ & _ & Hch & Hctx & Hal16 & Hwlo & Hwhi & Htop32 &
  Hnfr & Hown & Hfa1 & Hfa2 & Hps0 & Hps8 & Hshp & HFP0 & HRO & _ & _ & HVn & HVb & Hb64 & HNONE & Hnn & HnC &
  Hinput & HMETA & Hev & Hlive & MOK & HU0 & HUC).
(* ---- the facts of the cut (PcapSourceOpenB.v:1789-1850) ---- *)
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TPCAP_SOURCE_OPEN_STK = 18736) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
assert (Elay : forall c p, frame_addr (o_lyc cx) c p = frame_addr ly3 c p)
  by (intros c p; unfold frame_addr; rewrite (opb_lay_F _ _ _ Hly3), (opb_lay_F _ _ _ Hly); reflexivity).
assert (Hin : In (o_cid cx, o_pos cx) (frames (o_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hin3 : In (o_cid cx, o_pos cx) (frames S3)) by (rewrite Hfrs3; right; exact Hin).
assert (HinF : In (OP_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hincl : forall b m, In (b, m) (ablocks B (o_lyc cx) (o_Sc cx)) -> In (b, m) (ablocks B ly3 S3))
  by (intros b m Hb; rewrite Hab; apply in_or_app; left; exact Hb).
assert (Hfin : In (f, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (Hfresh : ~ In (f, SRC_FILE_BLOCK) (ablocks B (o_lyc cx) (o_Sc cx))).
{ intros Hc. apply in_split in Hc as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (f, SRC_FILE_BLOCK) (f, SRC_FILE_BLOCK)
    l1 l2 [] HAR3 ltac:(rewrite Hab, El, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  change (req_size SRC_FILE_BLOCK) with 1304 in Hd. clear - Hd. lia. }
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF)
  as (HF4096 & HFceil & HFapp).
assert (EF : frame_addr ly3 OP_CID fpos = oF cx fpos) by (unfold oF; symmetry; apply (Elay OP_CID fpos)).
rewrite EF in HF4096, HFceil, HFapp.
change (fs_frame_bytes OP_CID) with 128 in HF4096, HFceil, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (o_cid cx) (o_pos cx) HAR3 Hin3)
  as (Hg4096 & Hgceil & Hgapp).
rewrite <- (Elay (o_cid cx) (o_pos cx)) in Hg4096, Hgceil, Hgapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp.
pose proof (fs_frame_bytes_nonneg (o_cid cx)) as Hgnn.
assert (Hpsb : 4096 <= o_ps cx /\ o_ps cx + 24 <= 140737479966720)
  by (clear - Hfa1 Hfa2 Hg4096 Hgceil C1; lia).
assert (Hsplo : alloc_ceiling + TPCAP_SOURCE_OPEN_STK <= spZ (o_regs cx))
  by (clear - Hceil Hslo Hwlo Hwhi; lia).
assert (Hspr : 0 <= spZ (o_regs cx) < 2 ^ 64) by (unfold spZ; clear; apply u64_range).
pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (HFal & _ & _).
rewrite EF in HFal.
assert (HSHeq : oSH cx fpos = shadow_addr (oF cx fpos)) by (unfold oSH, shadow_addr; reflexivity).
destruct (opb_div8_mul64 _ HFal) as (HF8 & HF64).
assert (HSHm8 : oSH cx fpos mod 8 = 0).
{ unfold oSH, SHADOW_OFF. rewrite HF8.
  clear. replace (2147450880 + 8 * (oF cx fpos / 64)) with ((268431360 + oF cx fpos / 64) * 8) by lia.
  apply Z_mod_mult. }
destruct (opb_sp1_facts (spZ (o_regs cx)) ltac:(clear - Hspr; lia) Hal16) as (Hsp1r & Hsp1m32 & Hsp1m16).
assert (Hosp1 : osp1 cx = 32 * ((spZ (o_regs cx) - 96) / 32)) by (unfold osp1, OPEN_FRAME; reflexivity).
rewrite <- Hosp1 in Hsp1r, Hsp1m32, Hsp1m16.
assert (HSHb : SHADOW_OFF <= oSH cx fpos /\ oSH cx fpos + 16 <= SHADOW_OFF + 2 ^ 44).
{ assert (Hd0 : 0 <= oF cx fpos / 8) by (apply Z.div_pos; clear - HF4096; lia).
  assert (Hd1 : oF cx fpos / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
  unfold oSH. clear - Hd0 Hd1. lia. }
unfold SHADOW_OFF in HSHb.
assert (HFlt : 0 <= oF cx fpos < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
assert (HSHlt : 0 <= oSH cx fpos < 2 ^ 64) by (clear - HSHb; lia).
(* the FILE block, the input buffer, and their places against F and the caller's frame *)
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK HAR3 Hfin) as (_ & Hfb1 & Hfb2 & Hfb3 & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hfb2, Hfb3.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfb3.
destruct (Hinput Hn1) as (Hbin & _ & _).
assert (Hbin3 : In (o_b cx, o_n cx) (ablocks B ly3 S3)) by (apply Hincl; exact Hbin).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hbin3) as (_ & Hbb1 & Hbb2 & Hbb3 & _).
pose proof (req_size_pos (o_n cx) ltac:(clear - Hn1; lia)) as (_ & Hrq).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbb3.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK OP_CID fpos HAR3 Hfin HinF)
  as Dff.
unfold zdisjoint in Dff. cbn [fst snd] in Dff. rewrite EF in Dff.
change (req_size SRC_FILE_BLOCK) with 1304 in Dff. change (fs_frame_bytes OP_CID) with 128 in Dff.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (o_b cx) (o_n cx) OP_CID fpos HAR3 Hbin3 HinF)
  as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite EF in Dbf.
change (fs_frame_bytes OP_CID) with 128 in Dbf.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK (o_cid cx) (o_pos cx)
  HAR3 Hfin Hin3) as Dfg.
unfold zdisjoint in Dfg. cbn [fst snd] in Dfg. rewrite <- (Elay (o_cid cx) (o_pos cx)) in Dfg.
change (req_size SRC_FILE_BLOCK) with 1304 in Dfg.
assert (DFg : oF cx fpos + 128 <= frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) \/
              frame_addr (o_lyc cx) (o_cid cx) (o_pos cx) + fs_frame_bytes (o_cid cx) <= oF cx fpos).
{ destruct (in_split _ _ Hin) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (OP_CID, fpos) (o_cid cx, o_pos cx) [] l2 l3
    HAR3 ltac:(rewrite Hfrs3, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF, <- (Elay (o_cid cx) (o_pos cx)) in Hd.
  change (fs_frame_bytes OP_CID) with 128 in Hd. exact Hd. }
(* F's shadow bytes are present *)
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 OP_CID fpos HAR3 HinF) as (_ & _ & HFpres & HFSpres).
rewrite EF in HFpres, HFSpres. change (fs_frame_bytes OP_CID) with 128 in HFpres, HFSpres.
assert (HSs : forall o, 0 <= o < 16 -> apresent (w_H W3) (ms_mem ms3) (oSH cx fpos + o)).
{ intros o Ho. rewrite HSHeq. apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; clear - Ho; lia))). }
(* ---- the seated state (PcapSourceOpenB.v:1870-1926, without extra atoms) ---- *)
set (E := Eimg (Ereg (ms_regs ms3) [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. clear - Hr Hu. lia. }
assert (E21 : ew E 21 = w64 (oSH cx fpos)) by (rewrite (EREG 21%nat 21%bv eq_refl); exact M21).
assert (U21 : bv_unsigned (ew E 21) = oSH cx fpos) by (rewrite E21; apply unsigned_lit_small; exact HSHlt).
assert (HS : st_ok_pi SEGS VAL E or_ss (restrict (w_H W3) ms3)).
{ rewrite (opb_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr), Hpc, Hrom, restrict_mkst_fx.
  unfold or_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, or_FS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U21. split; [clear - HSHb; lia|]. split; [clear - HSHb; lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply (HSs o ltac:(clear - Ho; lia))|].
    apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  - split; [exact I | split; [exact I | exact I]]. }
clearbody E.
assert (E2 : ew E 2 = w64 (osp1 cx)) by (rewrite (EREG 2%nat 2%bv eq_refl); exact M2).
assert (E3 : ew E 3 = getr (o_regs cx) 3) by (rewrite (EREG 3%nat 3%bv eq_refl); exact M3).
assert (E4 : ew E 4 = getr (o_regs cx) 4) by (rewrite (EREG 4%nat 4%bv eq_refl); exact M4).
assert (E8 : ew E 8 = w64 (spZ (o_regs cx))) by (rewrite (EREG 8%nat 8%bv eq_refl); exact M8).
assert (E9 : ew E 9 = w64 (osp1 cx)) by (rewrite (EREG 9%nat 9%bv eq_refl); exact M9).
assert (E13 : ew E 13 = w64 f) by (rewrite (EREG 13%nat 13%bv eq_refl); exact Ha3).
assert (E18 : ew E 18 = w64 (oF cx fpos)) by (rewrite (EREG 18%nat 18%bv eq_refl); exact M18).
assert (E19 : ew E 19 = w64 (o_ps cx)) by (rewrite (EREG 19%nat 19%bv eq_refl); exact M19).
assert (E22 : ew E 22 = w64 (oF cx fpos)) by (rewrite (EREG 22%nat 22%bv eq_refl); exact M22).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EREG 23%nat 23%bv eq_refl); exact M23).
assert (E24 : ew E 24 = w64 (SHADOW_OFF + o_ps cx / 8)) by (rewrite (EREG 24%nat 24%bv eq_refl); exact M24).
assert (E26 : ew E 26 = getr (o_regs cx) 26) by (rewrite (EREG 26%nat 26%bv eq_refl); exact M26).
assert (E27 : ew E 27 = getr (o_regs cx) 27) by (rewrite (EREG 27%nat 27%bv eq_refl); exact M27).
assert (U22 : bv_unsigned (ew E 22) = oF cx fpos) by (rewrite E22; apply unsigned_lit_small; exact HFlt).
(* ---- 0x815d8..0x815f8: the buffer in scope, the arguments, the call of the fread wrapper ---- *)
pose proof HJ3 as HJ3c.
paj_run_shc RUNP RUNC HS HJ3.
{ intros a (r & Hr & Ha). cbn [or_ss ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [or_FS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U21 in Ha.
  right. right. right. exists OP_CID, fpos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EF, <- HSHeq. change (fs_frame_bytes OP_CID / 8) with 16.
  clear - Ha. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Rg1. prreg HS (2%bv : bv 5) Rg2. prreg HS (3%bv : bv 5) Rg3. prreg HS (4%bv : bv 5) Rg4.
prreg HS (8%bv : bv 5) Rg8. prreg HS (9%bv : bv 5) Rg9. prreg HS (10%bv : bv 5) Rg10.
prreg HS (11%bv : bv 5) Rg11. prreg HS (12%bv : bv 5) Rg12. prreg HS (13%bv : bv 5) Rg13.
prreg HS (18%bv : bv 5) Rg18. prreg HS (19%bv : bv 5) Rg19. prreg HS (20%bv : bv 5) Rg20.
prreg HS (21%bv : bv 5) Rg21. prreg HS (22%bv : bv 5) Rg22. prreg HS (23%bv : bv 5) Rg23.
prreg HS (24%bv : bv 5) Rg24. prreg HS (25%bv : bv 5) Rg25. prreg HS (26%bv : bv 5) Rg26.
prreg HS (27%bv : bv 5) Rg27.
(* what the run kept: everything but F's shadow bytes 4..6 *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (oSH cx fpos + 4 <= a < oSH cx fpos + 7) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E _ (w_H W3) (ms_mem ms3) (ms_mem ms)
    (fun x => oSH cx fpos + 4 <= x < oSH cx fpos + 7) HFr); [|exact Ha | exact Hn].
  intros bW wloW whiW aW HinW HrrW. vm_compute in HinW.
  destruct HinW as [HqW | []]. injection HqW as <- <- <-. cbn [base_val] in HrrW. rewrite U21 in HrrW.
  cbv beta. clear - HrrW. lia. }
(* what the run wrote: the three bytes are in scope *)
lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let o := eval vm_compute in (nth_error (ss_mem ssx) 0%nat) in
  lazymatch o with Some ?r =>
    pose proof (st_ok_region_nth (segs := SEGS) E ssx (restrict (w_H W3) ms) 0%nat r HS
      ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end end.
assert (SH0 : forall j, 4 <= j < 7 -> aview SEGS (w_H W3) (ms_mem ms) (oSH cx fpos + j) = Some 0).
{ intros j Hj. assert (Hjc : j = 4 \/ j = 5 \/ j = 6) by (clear - Hj; lia).
  destruct Hjc as [-> | [-> | ->]]; apply (aview_of_val_mem1 SEGS); try (clear; lia);
  match goal with |- val_mem _ _ (_ + ?o) 1 0 =>
    pose proof (field_of_region E _ 21%nat (oSH cx fpos) _ _ _ _ _ o 1%N (SLit 0) 0 HR0 U21
      ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv;
    change (N.to_nat 1) with 1%nat in Hv; exact Hv end. }
assert (SHW : forall i, (i < 16)%nat ->
  aview SEGS (w_H W3) (ms_mem ms) (oSH cx fpos + Z.of_nat i) = Some (nth i OSH_in 0)).
{ intros i Hi. destruct (Nat.lt_ge_cases i 4) as [Hl | Hl];
  [| destruct (Nat.lt_ge_cases i 7) as [Hl2 | Hl2]].
  - rewrite (KW (oSH cx fpos + Z.of_nat i) ltac:(clear - Hi HSHlt HSHb; lia) ltac:(clear - Hl; lia)), (Hshb i Hi).
    f_equal. symmetry. apply or_osh_out; [exact Hi | clear - Hl; lia].
  - rewrite (SH0 (Z.of_nat i) ltac:(clear - Hl Hl2; lia)). f_equal. symmetry. apply or_osh_mid. clear - Hl Hl2; lia.
  - rewrite (KW (oSH cx fpos + Z.of_nat i) ltac:(clear - Hi HSHlt HSHb; lia) ltac:(clear - Hl2; lia)), (Hshb i Hi).
    f_equal. symmetry. apply or_osh_out; [exact Hi | clear - Hl2; lia]. }
assert (Hspc : spZ (ms_regs ms) = osp1 cx).
{ unfold spZ. rewrite Rg2, E2. unfold w64. apply unsigned_lit_small. clear - Hsp1r Hsplo C1 HTS Hspr. lia. }
assert (Hs0c : s0Z (ms_regs ms) = spZ (o_regs cx)).
{ unfold s0Z. rewrite Rg8, E8. unfold w64. apply unsigned_lit_small. exact Hspr. }
assert (HBLO : 4096 <= BASE + (symaddr ((Symbols.Asan.s_pcap_source_open + 0x1a0) - Symbols.Asan.s_libreac_fuzz_fopen)%Z) < 2 ^ 64).
{ pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)). pose proof pa_B_ok as (HB0 & HB1 & _).
  clear - H HB0 HB1. lia. }
(* the destination's shadow after the stores: usable, and the hull visible *)
assert (or_dest_addressable : range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF
          (oF cx fpos + OP_HDR) 24).
{ intros x Hx. unfold OP_HDR in Hx.
  assert (Hj1 : oF cx fpos / 8 + 4 <= x / 8) by (apply Z.div_le_lower_bound; [clear; lia | clear - Hx HF8 HF64; lia]).
  assert (Hj2 : x / 8 < oF cx fpos / 8 + 7) by (apply Z.div_lt_upper_bound; [clear; lia | clear - Hx HF8 HF64; lia]).
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (oSH cx fpos + (x / 8 - oF cx fpos / 8))
    by (unfold oSH; clear; lia).
  apply SH0. clear - Hj1 Hj2. lia. }
assert (or_dest_hull : shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms)) (oF cx fpos + OP_HDR) 24).
{ intros s Hs. unfold shadow_addr, OP_HDR in Hs.
  assert (HA1 : (oF cx fpos + 32) / 8 = oF cx fpos / 8 + 4).
  { symmetry. apply (Z.div_unique _ 8 _ 0); [left; clear; lia | clear - HF8 HF64; lia]. }
  assert (HA2 : (oF cx fpos + 32 + 24 - 1) / 8 = oF cx fpos / 8 + 6).
  { symmetry. apply (Z.div_unique _ 8 _ 7); [left; clear; lia | clear - HF8 HF64; lia]. }
  rewrite HA1, HA2 in Hs.
  assert (HQ : oSH cx fpos = 8 * (oSH cx fpos / 8))
    by (pose proof (Z_div_mod_eq_full (oSH cx fpos) 8) as Hq; rewrite HSHm8, Z.add_0_r in Hq; exact Hq).
  assert (HB1 : (SHADOW_OFF + (oF cx fpos / 8 + 4)) / 8 = oSH cx fpos / 8).
  { symmetry. apply (Z.div_unique _ 8 _ 4); [left; clear; lia | unfold oSH in HQ |- *; clear - HQ; lia]. }
  assert (HB2 : (SHADOW_OFF + (oF cx fpos / 8 + 6)) / 8 = oSH cx fpos / 8).
  { symmetry. apply (Z.div_unique _ 8 _ 6); [left; clear; lia | unfold oSH in HQ |- *; clear - HQ; lia]. }
  rewrite HB1, HB2 in Hs.
  replace s with (oSH cx fpos + Z.of_nat (Z.to_nat (s - oSH cx fpos))) by (clear - Hs HQ; lia).
  rewrite (SHW (Z.to_nat (s - oSH cx fpos)) ltac:(clear - Hs HQ; lia)). discriminate. }
(* the chain at the call (the run wrote nothing at or above s1) *)
assert (HCHc : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (osp1 cx) (spZ (o_regs cx))
          ((spZ (o_regs cx), raZ (o_regs cx), s0Z (o_regs cx)) :: o_ch cx)).
{ eapply achain_kept with (lo := osp1 cx); [exact Hchain3 | clear; lia | rewrite Etop3; clear - Htop H47; lia |].
  intros a Ha. apply KW; [clear - Ha Hsp1r Hsplo HTS C1; lia | clear - Ha Hsp1r Hsplo HTS C1 HSHb; lia]. }
(* the stream, unchanged by the run *)
assert (HSRC : asource_at SEGS K (rdW W3 (ms_mem ms)) f (o_b cx) (o_C cx) 0).
{ apply (PcapSourceCloseSpec.asource_at_frame_segs SEGS K (rdW W3 (ms_mem ms3))); [|exact (proj1 HUNB)].
  intros a Ha. apply (mbyte_of_aview SEGS).
  destruct Ha as [Ha | [Ha | Ha]].
  - unfold SRC_FILE_BLOCK in Ha. apply KW; [clear - Ha Hfb1 Hfb2 C1; lia | clear - Ha Hfb3 HSHb; lia].
  - rewrite <- Hnn in Ha. apply KW; [clear - Ha Hbb1 Hbb2 Hrq C1; lia | clear - Ha Hbb3 Hrq HSHb; lia].
  - pose proof (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))) as Hr.
    unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    apply KW; [clear - Hr; lia | clear - Hr HSHb; lia]. }
(* ---- fread(F + 32, 1, 24, f) through the wrapper (0x815f8), PFreadISpec.v afread_spec ---- *)
assert (HFPRE : afread_pre SK SEGS B K (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx)
  (o_md0 cx) ((OP_CID, fpos) :: o_own cx) ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)
  (o_k cx + 1) (ms_regs ms) ((spZ (o_regs cx), raZ (o_regs cx), s0Z (o_regs cx)) :: o_ch cx)
  (oF cx fpos + OP_HDR) 24 f (o_b cx) 0 (o_C cx)).
{ unfold afread_pre, rread_call.
  split.
  { split; [exact HJ3|].
    split; [rewrite Rg1; apply ret_ok_codeptr_v; [clear; lia | reflexivity]|].
    split; [unfold raZ; rewrite Rg1, unsigned_lit_small by (clear - HBLO; lia); clear - HBLO; lia|].
    split; [rewrite Rg3, E3; exact Hgp|].
    split; [rewrite Rg4, E4; exact Htp|].
    split; [rewrite Hspc; exact Hsp1m16|].
    split; [rewrite Hspc; unfold AFREAD_STK; clear - Hsp1r Hwlo HTS; lia|].
    split; [rewrite Hspc; clear - Hsp1r Hwhi; lia|].
    rewrite Hspc, Hs0c. exact HCHc. }
  split; [rewrite Rg10, U22; reflexivity|].
  split; [rewrite Rg11; reflexivity|].
  split; [rewrite Rg12; reflexivity|].
  split; [rewrite Rg13, E13; reflexivity|].
  split; [exact Hfin|].
  split; [rewrite <- Hnn; exact Hbin3|].
  split; [left; rewrite Hspc, <- Hnn; unfold AFREAD_STK; clear - Hbb2 Hrq Hsp1r Hsplo HTS C1; lia|].
  split; [exact HSRC|].
  split.
  { intros a Ha. split.
    - destruct (HFPinc a ltac:(exists (f, f + SRC_FILE_BLOCK); split; [left; reflexivity | cbn [fst snd]; exact Ha]))
        as [Hq | Hq].
      + right. left. split; [exact Hq|]. exists f, SRC_FILE_BLOCK. split; [exact Hfin|].
        change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Ha. clear - Ha. lia.
      + right. right. left. exact Hq.
    - rewrite Hspc. unfold AFREAD_STK, SRC_FILE_BLOCK in *. clear - Ha Hfb2 Hsp1r Hsplo HTS C1. lia. }
  split; [clear; lia|].
  unfold rread_dest.
  split; [unfold OP_HDR, SRC_FILE_BLOCK; clear - Dff; lia|].
  split; [rewrite <- Hnn; unfold OP_HDR; clear - Dbf Hrq; lia|].
  split; [unfold OP_HDR; clear - HF4096; lia|].
  split; [unfold amem_range, OP_HDR, kLowMemEnd, kHighMemBeg, kHighMemEnd; clear - HFapp HFceil C1; lia|].
  split.
  { left. exists OP_CID, fpos. split; [exact HinF|]. intros a Ha.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes OP_CID) with 128.
    unfold OP_HDR in Ha. clear - Ha. lia. }
  split.
  { intros a Ha. split.
    - right. right. right. exists OP_CID, fpos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes OP_CID) with 128.
      unfold OP_HDR in Ha. clear - Ha. lia.
    - rewrite Hspc. unfold AFREAD_STK, OP_HDR in *. clear - Ha HFceil Hsp1r Hsplo HTS C1. lia. }
  split; [exact or_dest_addressable|].
  intros _. exact or_dest_hull. }
eapply SRr_bind.
{ exact (AFREAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HFPRE). }
cbv beta. intros W5 c5 _ HPOST.
destruct HPOST as (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HK5 & HQ5).
destruct HQ5 as (-> & -> & Ha05 & Hgarr5 & Hsrc5 & _ & _ & Hfds5 & Hfs5 & Hsb5).
destruct HK5 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HR5 : forall (r : Prelude.reg), acallee_saved (bv_unsigned r) -> getr regs5 r = getr (ms_regs ms) r)
  by (intros r Hr; pose proof (HP5 (bv_unsigned r) Hr) as Hq; rewrite !Z_to_bv_bv_unsigned in Hq; exact Hq).
assert (NWhi : forall a, alloc_ceiling <= a -> ~ rread_wrset f (oF cx fpos + OP_HDR) 24 a)
  by (intros a Ha [Hq | Hq]; unfold SRC_FILE_BLOCK, OP_HDR in Hq; clear - Ha Hq Hfb2 HFceil; lia).
(* what the call and the run kept of the arm's memory *)
assert (KST : forall a, spZ (o_regs cx) - 96 <= a < spZ (o_regs cx) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  rewrite (K1 a ltac:(clear - Ha Hsplo HTS C1 Hspr; lia)
    ltac:(rewrite Hspc; unfold AFREAD_STK; clear - Ha Hsp1r; lia)
    (NWhi a ltac:(clear - Ha Hsplo HTS C1; lia))).
  apply KW; [clear - Ha Hspr Hsplo HTS C1; lia | clear - Ha HSHb Hsplo HTS C1; lia]. }
assert (KF : forall a, oF cx fpos <= a < oF cx fpos + 128 -> ~ (oF cx fpos + 32 <= a < oF cx fpos + 56) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn.
  rewrite (K4 OP_CID fpos a HinF
    ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF; change (fs_frame_bytes OP_CID) with 128;
          exact Ha)
    ltac:(intros [Hq | Hq]; unfold SRC_FILE_BLOCK, OP_HDR in Hq; [clear - Hq Ha Dff | clear - Hq Hn]; lia)).
  apply KW; [clear - Ha HFlt HFceil C1; lia | clear - Ha HFapp HSHb; lia]. }
assert (KPS : forall a, o_ps cx <= a < o_ps cx + 24 ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha.
  rewrite (K4 (o_cid cx) (o_pos cx) a Hin3
    ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- (Elay (o_cid cx) (o_pos cx));
          clear - Ha Hfa1 Hfa2; lia)
    ltac:(intros [Hq | Hq]; unfold SRC_FILE_BLOCK, OP_HDR in Hq;
          [clear - Hq Ha Dfg Hfa1 Hfa2 | clear - Hq Ha DFg Hfa1 Hfa2]; lia)).
  apply KW; [clear - Ha Hpsb; lia | clear - Ha Hgapp Hfa1 Hfa2 Hgnn HSHb; lia]. }
(* the post's kept set, from the arm's (the clause structure of PcapSourceOpenB.v:422-499) *)
assert (TK : topen_kept SK SEGS B (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W5 mem5
   (spZ (o_regs cx) - TPCAP_SOURCE_OPEN_STK) (spZ (o_regs cx)) (fun a => o_ps cx <= a < o_ps cx + 22)).
{ destruct HKEPT as (T1 & T2 & T3 & T4 & T5 & T6).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn.
    rewrite (K1 a Ha ltac:(rewrite Hspc; unfold AFREAD_STK; clear - Hn Hsp1r HTS; lia) (NWhi a (proj1 Ha))).
    rewrite (KW a ltac:(clear - Ha C1; lia) ltac:(clear - Ha HSHb C1; lia)).
    exact (T1 a Ha Hn).
  - intros bb mm i Hb Hi HnE.
    assert (Hb3 : In (bb, mm) (ablocks B ly3 S3)) by (apply Hincl; exact Hb).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 bb mm HAR3 Hb3) as (_ & Hc4096 & Hcceil & Hcapp & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp.
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 bb mm OP_CID fpos HAR3 Hb3 HinF) as Dbb.
    unfold zdisjoint in Dbb. cbn [fst snd] in Dbb. rewrite EF in Dbb.
    change (fs_frame_bytes OP_CID) with 128 in Dbb.
    assert (Hne : (bb, mm) <> (f, SRC_FILE_BLOCK)) by (intros Hq; rewrite Hq in Hb; exact (Hfresh Hb)).
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 bb mm f SRC_FILE_BLOCK HAR3 Hb3 Hfin Hne) as Dbf'.
    unfold zdisjoint in Dbf'. cbn [fst snd] in Dbf'. change (req_size SRC_FILE_BLOCK) with 1304 in Dbf'.
    rewrite (K2 bb mm i Hb3 Hi
      ltac:(intros [Hq | Hq]; unfold SRC_FILE_BLOCK, OP_HDR in Hq; [clear - Hq Hi Dbf' | clear - Hq Hi Dbb]; lia)).
    rewrite (KW (bb + i) ltac:(clear - Hc4096 Hcceil Hi C1; lia) ltac:(clear - Hcapp Hi HSHb; lia)).
    exact (T2 bb mm i Hb Hi HnE).
  - intros a Hi Ho He Hof.
    pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    rewrite (K3 a Hi Ho He).
    rewrite (KW a ltac:(clear - Hr; lia) ltac:(clear - Hr HSHb; lia)).
    exact (T3 a Hi Ho He Hof).
  - intros c q a Hcq Hrng HnE.
    assert (Hcq3 : In (c, q) (frames S3)) by (rewrite Hfrs3; right; exact Hcq).
    destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 c q HAR3 Hcq3) as (Hc4096 & Hcceil & Hcapp).
    pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 c q HAR3 Hcq3) as (Hcal & Hcbal & _).
    pose proof (fs_frame_bytes_nonneg c) as Hcnn.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hcapp.
    pose proof Hcq as Hcq'.
    apply in_split in Hcq' as (l1 & l2 & El).
    pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (OP_CID, fpos) (c, q) [] l1 l2 HAR3
      ltac:(rewrite Hfrs3, El; reflexivity)) as Dcq.
    unfold zdisjoint, frame_rng in Dcq. cbn [fst snd] in Dcq. rewrite EF in Dcq.
    change (fs_frame_bytes OP_CID) with 128 in Dcq.
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 f SRC_FILE_BLOCK c q HAR3 Hfin Hcq3) as Dfc.
    unfold zdisjoint in Dfc. cbn [fst snd] in Dfc. change (req_size SRC_FILE_BLOCK) with 1304 in Dfc.
    pose proof (opb_shadow_disj (oF cx fpos) 128 (frame_addr ly3 c q) (fs_frame_bytes c)
      HFal ltac:(reflexivity) Hcal Hcbal ltac:(clear - HF4096; lia) ltac:(clear - Hc4096; lia)
      ltac:(clear; lia) Hcnn ltac:(clear - Dcq; lia)) as Dsh.
    rewrite <- HSHeq in Dsh. change (128 / 8) with 16 in Dsh.
    assert (Hs1 : kLowMemEnd <= shadow_addr (frame_addr ly3 c q) < kHighShadowEnd)
      by (apply shadow_addr_bounds; clear - Hc4096 Hcceil Hcnn C1 C4; lia).
    assert (Hs2 : shadow_addr (frame_addr ly3 c q) + fs_frame_bytes c / 8
                  <= shadow_addr (frame_addr ly3 c q + fs_frame_bytes c))
      by (apply shadow_range_end; exact Hcnn).
    assert (Hs3 : kLowMemEnd <= shadow_addr (frame_addr ly3 c q + fs_frame_bytes c) < kHighShadowEnd)
      by (apply shadow_addr_bounds; clear - Hc4096 Hcceil Hcnn C1 C4; lia).
    assert (Hrng3 : in_zr a (frame_rng ly3 (c, q)) \/
                    in_zr a (shadow_addr (frame_addr ly3 c q), fs_frame_bytes c / 8)).
    { unfold frame_rng. cbn [fst snd]. rewrite <- (Elay c q). exact Hrng. }
    assert (Habnd : 0 <= a < 2 ^ 64).
    { unfold in_zr, frame_rng in Hrng3. cbn [fst snd] in Hrng3.
      destruct Hrng3 as [Hq | Hq]; [clear - Hq Hc4096 Hcceil C1; lia | clear - Hq Hs1 Hs2 Hs3 C2 C5; lia]. }
    assert (HnW : ~ rread_wrset f (oF cx fpos + OP_HDR) 24 a).
    { unfold in_zr, frame_rng in Hrng3. cbn [fst snd] in Hrng3.
      intros [Hq | Hq]; unfold SRC_FILE_BLOCK, OP_HDR in Hq;
      (destruct Hrng3 as [Hr' | Hr'];
       [ clear - Hq Hr' Dfc Dcq; lia
       | clear - Hq Hr' Hs1 Hs2 Hs3 C2 C5 Hfb3 HFapp HFceil C1; lia ]). }
    assert (HnS : ~ (oSH cx fpos + 4 <= a < oSH cx fpos + 7)).
    { unfold in_zr, frame_rng in Hrng3. cbn [fst snd] in Hrng3.
      destruct Hrng3 as [Hr' | Hr']; [clear - Hr' Hcapp HSHb; lia | clear - Hr' Dsh Hcnn; lia]. }
    rewrite (K4 c q a Hcq3 Hrng3 HnW), (KW a Habnd HnS).
    exact (T4 c q a Hcq Hrng HnE).
  - intros a Ha Hn Hp.
    apply (K5 a Ha ltac:(rewrite Hspc; unfold AFREAD_STK; clear - Hn Hsp1r HTS; lia)).
    exact (apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms) a HG (T5 a Ha Hn Hp)).
  - intros a Ha.
    pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP5w & _).
    apply HP5w. clear - Ha Hwlo Hwhi HTS. lia. }
(* ---- the READ cut (0x815fc), closed by PcapSourceOpenB.op_from_read ---- *)
rewrite Rg1.
apply (OPB_READ cx fpos ly3 S3 W5 _ md5 HPRE).
unfold op_gi_read. cbv zeta.
exists f, (Z.min 24 (o_n cx)).
split; [reflexivity|].
split.
{ unfold op_mid. cbv zeta. cbn [ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact HJ5|].
  split; [clear; lia|].
  split; [exact Hnev3|].
  split; [exact Hfrs3|].
  split; [exact Hnin|].
  split; [exact Hfs3|].
  split; [rewrite (HR5 2%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 2%bv) with 2; lia)), Rg2, E2;
          reflexivity|].
  split; [rewrite (HR5 8%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 8%bv) with 8; lia)), Rg8, E8;
          reflexivity|].
  split; [rewrite (HR5 9%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 9%bv) with 9; lia)), Rg9, E9;
          reflexivity|].
  split; [rewrite (HR5 18%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 18%bv) with 18; lia)), Rg18,
          E18; reflexivity|].
  split; [rewrite (HR5 19%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 19%bv) with 19; lia)), Rg19,
          E19; reflexivity|].
  split; [rewrite (HR5 20%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 20%bv) with 20; lia)), Rg20,
          U22; reflexivity|].
  split; [rewrite (HR5 21%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 21%bv) with 21; lia)), Rg21,
          E21; reflexivity|].
  split; [rewrite (HR5 22%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 22%bv) with 22; lia)), Rg22,
          E22; reflexivity|].
  split; [rewrite (HR5 23%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 23%bv) with 23; lia)), Rg23,
          E23; reflexivity|].
  split; [rewrite (HR5 24%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 24%bv) with 24; lia)), Rg24,
          E24; reflexivity|].
  split; [rewrite (HR5 25%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 25%bv) with 25; lia)), Rg25;
          reflexivity|].
  split; [rewrite (HR5 3%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 3%bv) with 3; lia)), Rg3, E3;
          reflexivity|].
  split; [rewrite (HR5 4%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 4%bv) with 4; lia)), Rg4, E4;
          reflexivity|].
  split; [rewrite (HR5 26%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 26%bv) with 26; lia)), Rg26,
          E26; reflexivity|].
  split; [rewrite (HR5 27%bv ltac:(clear; unfold acallee_saved; change (bv_unsigned 27%bv) with 27; lia)), Rg27,
          E27; reflexivity|].
  split; [rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W5) mem5)
            (spZ (o_regs cx) - 8) ltac:(intros i Hi; apply KST; clear - Hi; lia)); exact Hra8|].
  split; [intros j Hj; rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W5) mem5)
            (spZ (o_regs cx) - 16 - 8 * j) ltac:(intros i Hi; apply KST; clear - Hi Hj; lia));
          exact (Hsav j Hj)|].
  split; [rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W5) mem5)
            (oF cx fpos) ltac:(intros i Hi; apply KF; clear - Hi; lia)); exact Hhdr0|].
  split; [rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W5) mem5)
            (oF cx fpos + 8) ltac:(intros i Hi; apply KF; clear - Hi; lia)); exact Hhdr8|].
  split; [rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W5) mem5)
            (oF cx fpos + 16) ltac:(intros i Hi; apply KF; clear - Hi; lia)); exact Hhdr16|].
  split; [rewrite (opb_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W5) mem5)
            (oF cx fpos + OP_FLAGPTR) ltac:(intros i Hi; unfold OP_FLAGPTR; apply KF; clear - Hi; lia));
          exact Hflagp|].
  split; [reflexivity|].
  split; [intros i Hi; rewrite (Hsb5 (oSH cx fpos + Z.of_nat i)
            ltac:(unfold kLowMemEnd, kHighShadowEnd; clear - Hi HSHb; lia)); exact (SHW i Hi)|].
  split; [eapply opb_vm_frame; [|exact Hvf]; intros x Hx; apply (mbyte_of_aview SEGS); apply KPS;
          clear - Hx; cbn in Hx; lia|].
  split; [eapply opb_vm_frame; [|exact Hv12]; intros x Hx; apply (mbyte_of_aview SEGS); apply KPS;
          clear - Hx; cbn in Hx; lia|].
  split; [eapply opb_vm_frame; [|exact Hv16]; intros x Hx; apply (mbyte_of_aview SEGS); apply KPS;
          clear - Hx; cbn in Hx; lia|].
  split; [eapply opb_vm_frame; [|exact Hv20]; intros x Hx; apply (mbyte_of_aview SEGS); apply KPS;
          clear - Hx; cbn in Hx; lia|].
  split; [intros i Hi; rewrite (KPS (o_ps cx + i) ltac:(clear - Hi; lia)); exact (Hkeep8 i Hi)|].
  split; [exact TK|].
  split; [rewrite Hfds5, (proj1 (opb_wvb_fds_fs _ _ _)); exact Hfds|].
  split; [rewrite Hfs5, (proj2 (opb_wvb_fds_fs _ _ _)); exact Hfsm|].
  split; [eapply or_meta_rebase; [exact HJ3c | exact HJ5 | exact HMETA3]|].
  split.
  { intros a Ha Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Ha as [(sg & Hs & _ & Hr) | Hrel]; [exists sg; split; [exact Hs | exact Hr]
                                                      | exact (pa_relro_img a Hrel)]).
    pose proof (pa_img_range a Hia) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    rewrite (K3 a Hia Ho He), (KW a ltac:(clear - Hr; lia) ltac:(clear - Hr HSHb; lia)).
    exact (HROD3 a Ha Ho He). }
  eapply achain_kept with (lo := osp1 cx); [exact Hchain3 | clear; lia | rewrite Etop3; clear - Htop H47; lia |].
  intros a Ha.
  rewrite (K1 a ltac:(clear - Ha Hsp1r Hsplo HTS C1; lia) ltac:(rewrite Hspc; unfold AFREAD_STK; clear - Ha; lia)
    (NWhi a ltac:(clear - Ha Hsp1r Hsplo HTS C1; lia))).
  apply KW; [clear - Ha Hsp1r Hsplo HTS C1; lia | clear - Ha Hsp1r Hsplo HTS C1 HSHb; lia]. }
split; [exact Hn1|]. split; [exact Hf4096|]. split; [exact Hf16|]. split; [exact Hab|].
split; [cbn [ms_regs mkst]; rewrite Ha05; unfold rread_k; rewrite Z.sub_0_r, <- Hnn; reflexivity|].
split; [reflexivity|].
split; [cbn [ms_mem mkst]; unfold rread_k in Hgarr5; rewrite Z.sub_0_r, <- Hnn in Hgarr5; exact Hgarr5|].
split; [cbn [ms_mem mkst]; unfold rread_k in Hsrc5; rewrite Z.add_0_l, Z.sub_0_r, <- Hnn in Hsrc5; exact Hsrc5|].
split; [exact HFPinc|].
exact Hmo.
Qed.

End e.
End d.
End b.

(* SK explicit (a Theorem Labs lane ruling 21:57Z), with a guard: it fails if SK becomes implicit. *)
Arguments op_read_arm {fx rc} SK {PI} B K MT FM_RA CTX roimg.
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) B K MT FM_RA
          CTX roimg => op_read_arm (fx := fx) (rc := rc) SK (PI := PI) B K MT FM_RA CTX roimg).
Print Assumptions op_read_arm.
