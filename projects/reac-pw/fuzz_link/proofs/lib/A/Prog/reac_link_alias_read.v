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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 501 of its 581 lines of code are new or changed and 1471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeHead.v, with its module paths and module names changed; 24 of its 67 lines of code are new or changed and 538 lines of the source are left out. *)
(* reac_link_alias_read (fuzz_link.asan 0x8867c, AF_reac_link_alias_read = 0x64b0, 760 bytes) on image A:
   the four files of its walk composed into the contract.

     reac_link_alias_readHead.v  ar_head  : the entry to the MID cut (+0x118), and the composition
     reac_link_alias_readArms.v  ar_arms  : +0x118 .. +0x180, the two guarded NUL stores, the name tests,
                                            fuzz_if_nametoindex and the three refusal exits
     reac_link_alias_readSend.v  ar_send  : +0x180 .. +0x1f4, the request, checked_memset and nl_talk
     reac_link_alias_readExit.v  ar_exit  : +0x1fc .. +0x2c4, the retired magic, the frame's shadow, the
                                            inline release, the restores and the `ret`
   The cuts they meet at are lib/A/Prog/reac_link_alias_readDefs.v.

   Proves function reac_link_alias_read (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide PcapRelro PcapRelroA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_link_alias_read_c nl_talk_c fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_link_alias_readDefs reac_link_alias_readPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_link_alias_readHead reac_link_alias_readArms reac_link_alias_readSend reac_link_alias_readExit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
(* link's image certificate, lib/A/AF0m.v PcapSyms; discharged at link's B by AD2l.PcapB_syms *)
Hypothesis TB : AF0m.PcapSyms B.
(* the segments the listing is certified against (lib/A/AB1v.v tfibsegs); the link PAImg instance has it by
   reflexivity *)
Hypothesis HSEGS : pa_segs = tfibsegs.
(* frame_alloc_1 (0x3da88): lib/A/AF0s.v stack_malloc1_contract, at tfibsegs *)
Hypothesis ASM1 : astack_malloc_realizes pa_segs B 1.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes, at tfibsegs; its premise order differs from
   aintrin_realizes only by moving `amem_range d n` after the two shadow premises *)
Hypothesis AMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
(* the two own callees, at the relro constants (the library walks' rule) *)
Hypothesis FIFN : fuzz_if_nametoindex_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis NLT : nl_talk_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* the read-only window is image bytes: the window lies inside one loaded segment of image A
   (PcapRelroA.v pcap_relro_in_image, a computation over the image module the build loads) *)
Lemma ar_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
Proof.
  intros a Ha. rewrite HSEGS.
  destruct pcap_relro_in_image as (s & Hin & H1 & H2 & H3).
  exists s. split; [exact Hin | lia].
Qed.

(* frame_alloc_1's entry in the code record is the 4-byte jump the listing calls: AF0l.v Tfib_code's
   pc_stack_malloc 1 = 0x3da88 = LinkAddr.v link_sigma LS___asan_stack_malloc_1 *)
Lemma ar_hsm1 : pc_stack_malloc (as_code B) 1 = pa_sigma LS___asan_stack_malloc_1.
Proof. rewrite (AF0m.ts_code B TB), (lv_sigma HV). reflexivity. Qed.

Theorem reac_link_alias_read_aproof :
  reac_link_alias_read_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
  pose proof (ar_exit SK B LAWS TB HSEGS) as EXIT.
  pose proof (ar_send SK B LAWS HV TB HSEGS AMSET NLT EXIT) as SEND.
  pose proof (ar_arms SK B LAWS HV TL TB HSEGS FIFN SEND EXIT) as MID.
  exact (ar_head SK B LAWS HV TL ASM1 ar_hsm1 HSEGS TB ar_relro_img MID SEND EXIT).
Qed.

About reac_link_alias_read_aproof.
Print Assumptions reac_link_alias_read_aproof.

End b.
End a.
