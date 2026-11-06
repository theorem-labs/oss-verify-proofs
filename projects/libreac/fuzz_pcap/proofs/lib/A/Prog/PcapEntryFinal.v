(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_pcap (v1.9.0, ASan build) from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, A/AI12.v and A/ACbj.v (the listing's image instance, in the form libreac/fuzz_grant's lib/A/Prog/GrantImg.v gives it, a working branch) and A/ACfh.v, A/ACfj.v and A/ACfi.v (the bridge from the entry walk to the contract, in the form libreac/fuzz_grant's lib/A/Prog/GrantLibX.v gives it): the code table of fuzz_pcap.asan's program code (0x80738, 1521 words, the span of PcapList.pcap_listing), the value table over PcapAddr.v, the instance PI_pcap of PcapPa.PAImg with its named equalities, pe_base from the contract's pre, the composition of the harness walks into pe_start, and pe_post to the contract's post. The meta region at the end is a Theorem Labs lane's h_meta_gx (a working branch 4259db10ddc), restated over explicit premises. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapEntryTop.v; 280 of its 336 lines of code are new or changed and 273 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* fuzz_pcap's entry contract (row 11, the ASan build of libreac v1.9.0, image fuzz_pcap.asan sha256
   b7a91d9b1fb0017d...), composed: PcapEntryTop.pcap_entry_top with every walk hypothesis that is proved instantiated
   by its lemma, so that a type mismatch between a proved walk and the top shows here, at once.

   Instantiated walks (each by `fit`, which demands that the lemma's conclusion at PI_pcap, KS := pcap_KS and
   POST := pe_post is SYNTACTICALLY the top's hypothesis, with no conversion, and logs as `ARGS_FIT CONVERSION` each
   argument whose type is the lemma's premise only up to conversion):
     pe_E                             PcapHarnessPE.v
     pe_A                             PcapHarnessPA.v:158 (a Theorem Labs lane, a working branch; on a working branch
                                      29385b28245)
     pe_B, pe_C                       PcapHarnessA.v    (a Theorem Labs lane, a working branch)
     tail_W, tail_R1 .. tail_R7,      PcapHarnessTail.v (a Theorem Labs lane, a working branch)
     tail_K12r, tail_leave, tail_ret
     pe_Walk                          PcapHarnessWalk.v, with its Section hypothesis
                                      WALKR := fun POST => PcapHarnessWalkR.pe_WalkR .. POST (a Theorem Labs lane,
                                      a working branch), itself checked by `fit` against pe_Walk's WALKR
     pe_KR, pe_WalkR's KR             PcapHarnessWalkKR.v:3083 (a Theorem Labs lane, on a working branch 5f9b0299dc5)
   and the callee statements the walks take:
     OPEN (fin_OPEN)                  PcapSourceOpen.v:811 pb_pcap_source_openX (a Theorem Labs lane, on a working branch c253ca9c73a)
     NEXT (fin_NEXT)                  PcapSourceNext.v:146 pb_pcap_source_nextX (a Theorem Labs lane, on a working branch 29b85aab8d0)
     FOPEN (fin_FOPEN), which OPEN takes   PcapFuzzFopen.v:217 pb_libreac_fuzz_fopenX (a Theorem Labs lane, on a working branch 29b85aab8d0)
     CLOSE (fin_CLOSE)                PcapSourceClose.v:378 pb_pcap_source_closeX (a Theorem Labs lane, on a working branch
                                      dcd4e33b7bd), general in B, K and MT like OPEN and NEXT
   and the frame give-back law ASF (fin_ASF): YG0t.v:474 astack_free_law_ok, general in the segments and B, no premise.
   HGLEN of pe_E, pe_B, tail_W and pe_WalkR is PcapEntryTop.pi_pcap_glen; pe_WalkR's HGX is fin_HGX, from
   pcap_G_harness_gx_ok and PcapEntryTop.pi_pcap_pe_G. The SMP of pb_pcap_source_openX and pb_pcap_source_nextX is
   fin_SMP (from ML); pb_pcap_source_openX's HMODE is pi_pcap_obj12_mode (computed on the instance) and its HGX
   fin_HGX_open (from pcap_G_harness_gx_ok and pcap_G_harness_pe_bytes).
   ASIL is passed BY CONVERSION (kernel-checked) to every lemma that takes it (a Theorem Labs lane ruling, 08:16Z): the file's
   ASIL is the top's, at Asan.M.loaded_segments; each lemma states it at pa_segs PI_pcap, which reduces to
   Asan.M.loaded_segments by delta + iota (PcapEntryTop.v:140-141). Each such site carries a `conversion:` comment,
   and the build log shows each one as an ARGS_FIT CONVERSION line.
   FOPEN is passed BY CONVERSION (kernel-checked) to pb_pcap_source_openX, at that one site (a Theorem Labs lane via a Theorem Labs lane,
   08:4xZ: the same class as ASIL): fin_FOPEN is pb_libreac_fuzz_fopenX's own conclusion, which names the Definitions
   A_libreac_fuzz_fopenP (= BASE + AF_libreac_fuzz_fopen, PcapFuzzFopen.v:69) and FO_PATH / FO_LEN / FO_FILE (= 3 / 4
   / 2, PcapFuzzFopen.v:44-46); pb_pcap_source_openX's premise states the unfolded terms. Delta only; the site carries a
   `conversion:` comment and the build log shows it as one ARGS_FIT CONVERSION line. No other argument differs from
   its premise.

   Section hypotheses: the types of (1)-(4) are copied from PcapEntryTop.v's Section top, unchanged (the meter, core
   and image facts); (4b) was the walk pe_KR, pe_WalkR's hypothesis KR; fin_KR now holds it, so no walk is open.
   (5) was the callee statement CLOSE; fin_CLOSE now holds it.
   (6) are the other premises of the proved walks, in each lane's own form at PI_pcap; (7) the premises of
   pb_pcap_source_openX that (1)-(6) do not hold; (8) those of pb_pcap_source_nextX that (1)-(7) do not hold; (9)
   those of pb_libreac_fuzz_fopenX that (1)-(8) do not hold; (10) those of pe_A that (1)-(9) do not hold; (11) that of
   pe_KR that (1)-(10) do not hold. Every
   implicit argument of class type (sink head, FPState, RunCeil, PAImg, ro_below_ofl) is given explicitly: no
   instance search picks one. The end of the file prints each walk application under Set Printing All (every
   sink-head argument is the Section variable SK) and shows that the plain build's src0_sink_head is not loaded at
   all. *)
(* The premises of (6), (4b) and pcap_source_open's parameters: premise, type, DISCHARGER (a Theorem Labs lane, 06:16Z), source
   file. Source files found by name on 2026-10-29 at the base branch c253ca9c73a (the core union 40f7f2e1839: the base branch + a working branch
   429b6cb9055 + a working branch 727a1c84c2a + a working branch 2ce3f2d7b1c, plus a working branch f2f68949c4c), and where a file is not on the base branch,
   at other working branches: 6c461415f47, 9700d736a50. NOT FOUND: no lemma with that
   conclusion on any of these refs. UNION: what the core union proves of it (06:43Z check); "none" = no lemma.
     LAWS   AR_laws SEGS B                  core: YG0d.AsanAPI's aa_laws     lib/Reusable/YG0d.v:531-532; the AsanAPI
                                                                             value at pcap's B NOT FOUND. UNION: none
     TL     PALib B                         core: AF0m's PcapSyms            lib/A/AF0m.v:437 PcapSyms; PcapSyms B ->
                                                                             PALib B NOT FOUND. UNION: none
     TLF    PALibF B                        core: AF0m's PcapSyms            lib/A/AF0m.v:437; PALibF in
                                                                             lib/A/Prog/PcapFrame.v:96; lemma NOT FOUND.
                                                                             UNION: none
     ASM1   astack_malloc_realizes SEGS B 1 AF0s.stack_malloc1_contract via PcapSyms at the instance (a Theorem Labs lane)
                                                                             lib/A/AF0s.v:520 stack_malloc1_contract.
                                                                             UNION: proves it at AB1v.tfibsegs, not at
                                                                             pa_segs PI_pcap (convertible, not
                                                                             syntactic), and from AF0m.PcapSyms B, which
                                                                             this file does not have: NOT wired (reported)
     AM     amalloc04_rule SEGS B MT        core: YC5d / YCbp, AF0w          lib/Reusable/YCbp.v:29 amalloc04_rule_triv
                                                                             (only at MT := ameter_triv) from
                                                                             lib/A/AF0w.v:31 / :39 (a working branch). UNION:
                                                                             none at a general MT; AF0w is not in it
     AF     afree04_rule SEGS B MT          core: YC5d / YCbp, AF0q          lib/Reusable/YCbp.v:38 afree04_rule_triv
                                                                             (only at MT := ameter_triv) from
                                                                             lib/A/AF0q.v:15 (a working branch). UNION: none at
                                                                             a general MT; AF0q is not in it
     ML     model_laws (as_universe B)      core: YG0d.AsanAPI's aa_model    lib/Reusable/YG0d.v:533; the value NOT
                                                                             FOUND. UNION: none
     ASF    astack_free_law SEGS B          core: YG0t                       lib/Reusable/YG0t.v:474 astack_free_law_ok,
                                                                             general: WIRED (fin_ASF), constr_eq
     FFL    frame_flag_lawP SEGS B          core (AsanAPI side)              defined lib/Reusable/YCbq.v:797; lemma
                                                                             NOT FOUND. UNION: none
     MFSL   ameter_fs_laws MT               core: YCbp                       lib/Reusable/YCbp.v:23 ameter_triv_fs_laws
                                                                             (only at MT := ameter_triv). UNION: none
                                                                             at a general MT
     RO     PcapBase.ro_below_ofl SEGS LO HI SK   the PcapRelro instance     lib/A/Prog/PcapRelro.v:23-24 (PCAP_RLO,
                                                                             PCAP_RHI); the instance NOT FOUND. Its law
                                                                             needs SK := asan_sink_head
                                                                             (lib/Reusable/PcapSinkHeads.v:30). UNION:
                                                                             none
     KR     pe_KR at every FPState          a Theorem Labs lane              lib/A/Prog/PcapHarnessWalkKR.v:3084 pe_KR:
                                                                             WIRED (fin_KR); its new premise ABCMP:
     ABCMP  abcmp_realizes SEGS B (SIGMA bcmp trampoline 0x41570), at every FPState
                                            a Theorem Labs lane's core: YG0d.AsanAPI's aa_bcmp   lib/Reusable/YG0d.v:543 (at
                                                                             pc_wrap_bcmp (as_code B) = 0x41570); the
                                                                             value at pcap's B NOT FOUND
     ROI    (word -> option byte) -> Prop   open side: AE3i                  lib/A/AE3i.v:62 ro_img
     HROI   arodata_okP .. -> ROI ..        open side: AE3i, a working branch AD1o   lib/A/AD1o.v:49 ro_img_of_arodata
                                                                             (a working branch) states it over arodata_ok B
                                                                             (ACeg / ACeh), not PcapBase.arodata_okP:
                                                                             the exact form NOT FOUND. UNION: none
     HPATH  AR .. -> range_addressable / shadow_hull_vis of object 3, 13 bytes   open side: AF0m   NOT FOUND (the open
                                                                             lane, lib/A/Prog/PcapSourceOpen.v:158,
                                                                             takes it as a hypothesis too). UNION: none
     FM_RA  Z                               open side                        lib/A/Stdio/PStdioImgA.v:46 FM_MALLOC_RA
                                                                             (0x8e90c), as the candidate value
     CTX    list (list Z)                   open side's instance facts       NOT FOUND
     HCTX   In [BASE + PP_K7; RA_LLVMF] CTX /\ In [BASE + PP_K7] CTX   open side's instance facts   NOT FOUND
     HFMU   the malloc-trace universe facts over FM_RA and CTX   open side: AF0m   NOT FOUND. UNION: none
   (7) pb_pcap_source_openX's premises (PcapSourceOpen.v:111-163), new here; source files found by name at the base branch
   c253ca9c73a, the tree's base:
     ro_chunk_addr  Z -> Prop (the bytes ROI reads)   a Theorem Labs lane's core: AE3i   lib/A/AE3i.v:26 img_ro_chunks (their
                                                                             addresses)
     ROIMG_KEPT  ROI kept when the ro_chunk_addr bytes are   a Theorem Labs lane's core: AE3i   lib/A/AE3i.v:93 ro_img_kept states
                                                                             it over the window [IMG_RO_LO, IMG_RO_HI)
                                                                             and mrestrict, not over ro_chunk_addr and
                                                                             mbyte: the exact form NOT FOUND
     HGRO   ro_chunk_addr a -> in_roP .. /\ not static /\ not errno   a Theorem Labs lane's core: PcapGHarness hg_img_laws' hg_ro
                                                                             lib/A/PcapGHarness.v
                                                                             (a working branch), not on
                                                                             the base branch: NOT FOUND on the base branch
     FM     PSourceMeter.asrc_file_meter SK SEGS B MT   the meter's owner   lib/A/Stdio/PSourceMeter.v:47 (the
                                                                             record); the lemma NOT FOUND
     FOPEN  tlibreac_fuzz_fopen_specX SK SEGS (BASE + AF_libreac_fuzz_fopen) obj3 obj4 obj2 ROI B pcap_KS MT FM_RA
            CTX, at every FPState     a Theorem Labs lane                    lib/A/Prog/PcapFuzzFopen.v:217
                                                                             pb_libreac_fuzz_fopenX: WIRED (fin_FOPEN),
                                                                             its premises are (9); passed by conversion
                                                                             (kernel-checked), delta: PcapFuzzFopen.v:43-45,
                                                                             :68
     AFREAD PFreadISpec.afread_spec SK SEGS B pcap_KS (SIGMA fread trampoline), at every FPState
                                            a Theorem Labs lane's rfread_contract   lib/A/Stdio/PFreadISpec.v:137-138 (the
                                                                             statement); the lemma NOT FOUND
     ra_fc1, ra_fc2  Z (fclose's two return addresses)   a Theorem Labs lane            NOT FOUND
     AFCLOSE PFclose.afclose_source_spec SK SEGS B pcap_KS (SIGMA fclose trampoline) ra_fc1 ra_fc2 LO HI, at every
            FPState                         a Theorem Labs lane's PFclose               lib/A/Stdio/PFclose.v:209 (the statement,
                                                                             still a stand-in); the lemma NOT FOUND
     HUfc1, HUfc2  In [pc_free_ra0 (as_code B); ra_fc1 / ra_fc2] (as_universe B)   a Theorem Labs lane / the trace universe
                                                                             (a Theorem Labs lane's ACej.Tfib_universe):
                                                                             NOT FOUND
   (8) pb_pcap_source_nextX's premises (PcapSourceNext.v:73-89), new here; source files found by name at the base branch
   29b85aab8d0, the tree's base after the merge:
     ASM0   astack_malloc_realizes SEGS B NX_CID (class 0), at every FPState
                                            StackMalloc0.stack_malloc0_contract via PcapSyms at the instance (a Theorem Labs lane)
                                                                             lib/A/StackMalloc0.v:520: proved at
                                                                             tfibsegs, class 0, from PcapSyms B, which
                                                                             this file does not have: NOT wired
     AMM    MemmoveDef.amemmove_realizes SEGS B (SIGMA __asan_memmove), at every FPState
                                            a Theorem Labs lane: Memmove.asan_memmove_contract via PcapSyms at the instance
                                                                             lib/A/Rt/Memmove.v:147: proved at
                                                                             tfibsegs and 0x51bf0, from PcapSyms B: NOT
                                                                             wired
   (9) pb_libreac_fuzz_fopenX's premises (PcapFuzzFopen.v:70-98), new here; source files found by name on 2026-10-29
   at a working branch 29b85aab8d0 (the tree's base) and, where not on the base branch, at another working branch
   c5180b0bcf1:
     ROIMG_LOW  PcapFuzzFopenG.roimg_low SEGS ROI   a Theorem Labs lane's core: AE3i      lib/A/AE3i.v:61-62 ro_img over
                                                                             img_ro_region [IMG_RO_LO, IMG_RO_HI), below
                                                                             alloc_ceiling; the lemma NOT FOUND
     mc_lo, mc_hi  Z (the fmemopen wrapper's word-constant window)   a Theorem Labs lane's core: AE3i   0x10350 / 0x10370, inside
                                                                             AE3i's chunk 0x10330 .. 0x10398
                                                                             (lib/A/AE3i.v:26); as values
     MCONSTS  ROI (mrestrict ..) -> mc_lo <= a < mc_hi -> aview SEGS .. a = option_map .. (seg_rom SEGS ..)
                                            a Theorem Labs lane's core: AE3i               the lemma NOT FOUND
     FI     PcapFuzzFopenG.FopenImg SK (VAL obj FO_LEN) (VAL obj FO_FILE) pcap_KS
                                            the image instance               PcapFuzzFopen.v:496 fopen_img_tables
                                                                             (fi_sep's tables, by computation); fi_head
                                                                             needs SK := asan_sink_head
                                                                             (lib/Reusable/PcapSinkHeads.v:30); the
                                                                             record NOT FOUND
     STRCMP PcapFuzzFopenG.astrcmp_path_at SEGS B ROI (SIGMA strcmp trampoline) (VAL obj FO_PATH), at every FPState
                                            a Theorem Labs lane: StrcmpIcpt.strcmp_lit_contract via PcapSyms at the instance
                                                                             lib/A/Rt/StrcmpIcpt.v:458 (astrcmp_lit_realizes
                                                                             B, lib/A/Rt/StrcmpDef.v:53): at tfibsegs and
                                                                             SM_INST, from PcapSyms B: NOT wired
     AFMEMOPEN PFmemopenISpec.afmemopen_spec SK SEGS B pcap_KS MT CTX (SIGMA fmemopen trampoline) FM_RA mc_lo mc_hi,
            at every FPState                a Theorem Labs lane: PFmemopenC.pcap_afmemopen_closed
                                                                             lib/A/Stdio/PFmemopenC.v:23 (a working branch; not
                                                                             on the base branch): at tfibsegs, FM_ENTRY,
                                                                             FM_MALLOC_RA, 0x10350 / 0x10370, from
                                                                             PcapSyms B and amalloc04_rule: NOT wired
   (10) PcapHarnessPA.pe_A's premises (PcapHarnessPA.v:91-114), new here; source files found by name on 2026-10-29 at
   a working branch 29385b28245 (the tree's base after the merge):
     HCPY   aintrin_realizes SEGS B OCpy (SIGMA __asan_memcpy), at every FPState
                                            a Theorem Labs lane's core: AD1o.ocpy_of_icpt via PcapSyms at the instance
                                                                             lib/A/AD1o.v:82: at tfibsegs and
                                                                             pc_wrap_memcpy (as_code B), from PcapSyms B:
                                                                             NOT wired
     HSET   aintrin_realizes SEGS B OSet (SIGMA __asan_memset), at every FPState
                                            a Theorem Labs lane's core: AD1o.oset_of_icpt via PcapSyms at the instance
                                                                             lib/A/AD1o.v:84: at tfibsegs and
                                                                             pc_wrap_memset (as_code B), from PcapSyms B:
                                                                             NOT wired
     HCTX_A In [BASE + PP_K2; RA_LLVMF] CTX /\ In [BASE + PP_K2] CTX (the lane's HCTX, at pe_A's landing PP_K2)
                                            the open side's instance facts   NOT FOUND
   (3) ASIL, the top's asource_img_laws SK SEGS B pcap_KS: by conversion (kernel-checked) at every walk, open and
   next (pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntryTop PcapHarnessPE PcapHarnessA PcapHarnessPA
  PcapHarnessTail PcapHarnessWalk PcapHarnessWalkR PcapHarnessWalkKR PcapSourceOpen PcapFuzzFopenDefs PcapFuzzFopenG
  PcapFuzzFopen PcapSourceNext PcapSourceNextSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PSourceMeter PFreadISpec PFclose PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 YO09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop YG0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YG0t.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase PcapRelro PcapRelroA PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceClose
  PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
Import ListNotations.
Open Scope Z_scope.

(* `args_fit t` compares each argument a of the application t with the premise type the head expects at a's position.
   When a's type is not SYNTACTICALLY that premise (constr_eq) it prints an `ARGS_FIT CONVERSION` line with both types
   (under Set Printing All, below): the kernel accepts such an argument only by conversion, and the log names each
   one. *)
Ltac args_fit t :=
  lazymatch t with
  | ?f ?a =>
      args_fit f;
      lazymatch type of f with
      | forall _ : ?T, _ =>
          let T' := type of a in
          tryif constr_eq T T' then idtac
          else idtac "ARGS_FIT CONVERSION: the argument" a "has the type" T' "where the premise is" T
      end
  | _ => idtac
  end.

(* `fit L` logs L's arguments by args_fit, then closes the goal with the term L only when L's type is syntactically
   the goal. *)
Ltac fit L := args_fit L; lazymatch goal with |- ?G => let T := type of L in constr_eq T G; exact L end.

(* The listing's object 12 is pcap_KS's mode literal "rb" (0x20d40: PcapAddr.v pcap_obj 12, PSourceK.v:66
   PCAP_MODE): pb_pcap_source_openX's HMODE at PI_pcap, by computation on the instance, as PcapEntryTop.pi_pcap_obj2. *)
Lemma pi_pcap_obj12_mode : forall rc : YM05.RunCeil,
  @pa_val rc pcap_listing (@PcapEntryTop.PI_pcap rc) (A_OBJ 12) = as_mode pcap_KS.
Proof. intros rc. vm_compute. reflexivity. Qed.

Section final.
Context {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Local Notation SEGS := Asan.M.loaded_segments.
Local Notation PIp := (@PcapEntryTop.PI_pcap rc).
Local Notation POSTP fx := (@pe_post fx rc SK PIp B MT pcap_KS).
Local Notation PFROM fx GI := (@pe_from rc SK PIp B MT pcap_KS (POSTP fx) GI).
Local Notation GIx X fx := (X fx rc PIp B MT pcap_KS).
(* The lanes' image terms at PI_pcap. *)
Local Notation SEGSp := (@pa_segs rc pcap_listing PIp).
Local Notation VALp a := (@pa_val rc pcap_listing PIp a).
Local Notation LOp := (@pa_relro_lo rc pcap_listing PIp).
Local Notation HIp := (@pa_relro_hi rc pcap_listing PIp).

(* ---- (1)-(4): PcapEntryTop.v Section top, unchanged ---- *)
Hypothesis MTL : ameter_laws MT.
Hypothesis HXM : forall n, pe_need MT n <= XM_LIB n.
Hypothesis HXMN : forall n, XM_LIB n <= XN_LIB n.
Hypothesis pcap_G_harness_gx_ok : gx_ok SEGS B G_HARNESS.
Hypothesis pcap_G_harness_pe_bytes : forall a, inG G_HARNESS a ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ (as_meta_mem pcap_KS <= a < as_meta_mem pcap_KS + 8) /\
  ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HMRA : pc_malloc_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z).
Hypothesis HFRA : pc_free_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z).
Hypothesis HUNIV : as_universe B = ACej.Tfib_universe.
Hypothesis ASIL : asource_img_laws SK SEGS B pcap_KS.
(* pe_A: no longer a hypothesis: fin_pe_A below is PcapHarnessPA.pe_A, at the premises of (10). *)

(* ---- (4b): the walk pe_KR (PP_KL2 -> PP_KR, the skip loop's body), pe_WalkR's Section hypothesis KR, is no longer a
   hypothesis: fin_KR below is PcapHarnessWalkKR.pe_KR, at the premise of (11). ---- *)

(* ---- (5): the callee statements the proved walks take, at every FPState ---- *)
(* pcap_source_next (a Theorem Labs lane, PcapSourceNextDefs.v): pe_C, tail_R2, tail_R4. Its statement is no longer a
   hypothesis: fin_NEXT below is PcapSourceNext.pb_pcap_source_nextX. *)
(* pcap_source_close (a Theorem Labs lane, PcapSourceCloseSpec.v): tail_W, tail_R3. Its statement is no longer a
   hypothesis: fin_CLOSE below is PcapSourceClose.pb_pcap_source_closeX. *)
(* pcap_source_open (a Theorem Labs lane, PcapSourceOpenDefs.v), at its parameters FM_RA, CTX, ROI: tail_R1. Its
   statement is no longer a hypothesis: fin_OPEN below is PcapSourceOpen.pb_pcap_source_openX.
   FM_RA, CTX, ROI: DISCHARGER the open side (its instance facts; candidates in the header table). *)
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.

(* ---- (6): the other premises of the proved walks, NOT in PcapEntryTop's Section top (a Theorem Labs lane, 06:16Z: they stay
   here). Each carries its DISCHARGER; the header table gives the source files. ---- *)
(* The allocator laws: all walks. DISCHARGER a Theorem Labs lane's core (YG0d.AsanAPI's aa_laws), via the base branch's merges of 429b6cb9055 and 727a1c84c2a. *)
Hypothesis LAWS : @AR_laws rc SEGSp B.
(* The listing's runtime symbols: pe_E, pe_B, tail_R5, tail_R6. DISCHARGER a Theorem Labs lane's core (AF0m's PcapSyms). *)
Hypothesis TL : @PALib rc pcap_listing PIp B.
(* The frame symbols: pe_E. DISCHARGER a Theorem Labs lane's core (AF0m's PcapSyms). *)
Hypothesis TLF : @PALibF rc pcap_listing PIp B.
(* __asan_stack_malloc_1's rule: pe_E, pb_pcap_source_openX.
   DISCHARGER AF0s.stack_malloc1_contract via PcapSyms at the instance (a Theorem Labs lane) *)
Hypothesis ASM1 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc SEGSp B 1.
(* The runtime rules malloc / free (Reusable/YC5d.v): AM pe_E, pe_B; AF pe_B, tail_R5, tail_R6. DISCHARGER a Theorem Labs lane's
   core: YCbp.amalloc04_rule_triv / afree04_rule_triv (MT := ameter_triv) from AF0w / AF0q's realizes theorems. *)
Hypothesis AM : forall fx : YK11.FPState, @amalloc04_rule fx rc SK SEGSp B MT.
Hypothesis AF : forall fx : YK11.FPState, @afree04_rule fx rc SK SEGSp B MT.
(* PcapBase.ro_below_ofl: pe_C, tail_W, tail_R1 .. tail_R4. DISCHARGER the PcapRelro instance (at the ASan sink
   head: its law is a < sk_ofl_head SK). *)
Hypothesis RO : @ro_below_ofl SEGSp LOp HIp SK.
(* pcap_source_open's side conditions: tail_R1. DISCHARGER the open side (a Theorem Labs lane's AE3i / AF0m and its
   instance facts). *)
Hypothesis HROI : forall (W : world SEGSp) mem,
  arodata_okP SEGSp LOp HIp B (aview SEGSp (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S (W : world SEGSp) mem md, @AR rc SEGSp B ly S W mem md ->
  range_addressable (aview SEGSp (w_H W) mem) SHADOW_OFF (VALp (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGSp (w_H W) mem) (VALp (A_OBJ 3)) 13.
Hypothesis HCTX : In [VALp A_TEXT + PP_K7; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K7] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).
(* The model laws (pe_E, tail_leave) and the meter's frame-state law (pe_E, tail_leave). DISCHARGER a Theorem Labs lane's core: ML
   YG0d.AsanAPI's aa_model, FFL the core's frame flag law, MFSL YCbp.ameter_triv_fs_laws (MT := ameter_triv). The
   frame give-back ASF (tail_leave, open, next) is no longer a hypothesis: fin_ASF below is YG0t.astack_free_law_ok. *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : @frame_flag_lawP rc SEGSp B.
Hypothesis MFSL : ameter_fs_laws MT.

(* ---- (7): the premises of PcapSourceOpen.pb_pcap_source_openX (PcapSourceOpen.v:111-163) that (1)-(6) do not
   hold, in the lane's form at PI := PI_pcap, K := pcap_KS, ro_img := ROI. Each carries its DISCHARGER; the header
   table gives the source files. The lane's LAWS TL TLF ML ASM1 ASF FFL MLAW (MTL) MLAWF (MFSL) ASIL HPATH ROB (RO)
   are (1)-(6)'s; SMP, HMODE and HGX are derived below (fin_SMP, pi_pcap_obj12_mode, fin_HGX_open). ---- *)
(* The bytes ROI reads, and ROI's frame law over them. DISCHARGER a Theorem Labs lane's core: AE3i's ro_img over img_ro_region,
   whose chunks are img_ro_chunks (lib/A/AE3i.v:26, :61-62; YI04.region_ok_transport), at SEGS = tfibsegs. *)
Variable ro_chunk_addr : Z -> Prop.
Hypothesis ROIMG_KEPT : forall m m' : word -> option byte,
  (forall a, ro_chunk_addr a -> mbyte SEGSp m' a = mbyte SEGSp m a) -> ROI m -> ROI m'.
(* The image facts of the read-only bytes. DISCHARGER a Theorem Labs lane's core: lib/A/PcapGHarness.v hg_img_laws' field hg_ro
   (a working branch); not on the base branch. *)
Hypothesis HGRO : forall a, ro_chunk_addr a ->
  in_roP SEGSp LOp HIp a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* The file meter. DISCHARGER the meter's owner (PSourceMeter.v:47 asrc_file_meter; MT := ameter_triv); the lemma
   NOT FOUND on the base branch. *)
Hypothesis FM : @PSourceMeter.asrc_file_meter rc SK SEGSp B MT.
(* libreac_fuzz_fopen: its statement is no longer a hypothesis: fin_FOPEN below is
   PcapFuzzFopen.pb_libreac_fuzz_fopenX, at the premises of (9). *)
(* The fread wrapper. DISCHARGER a Theorem Labs lane's rfread_contract (lib/A/Stdio/PFreadISpec.v:137-138); the lemma NOT
   FOUND on the base branch. *)
Hypothesis AFREAD : forall fx : YK11.FPState,
  @PFreadISpec.afread_spec fx rc SK SEGSp B pcap_KS (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fread).
(* The fclose wrapper, at its two return addresses ra_fc1 / ra_fc2 and their trace-universe facts. DISCHARGER a Theorem Labs lane
   (lib/A/Stdio/PFclose.v:209 afclose_source_spec, still a stand-in); the lemma and the two addresses NOT FOUND on
   the base branch. *)
Variables ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : forall fx : YK11.FPState,
  @PFclose.afclose_source_spec fx rc SK SEGSp B pcap_KS
    (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2 LOp HIp.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).

(* ---- (8): the premises of PcapSourceNext.pb_pcap_source_nextX (PcapSourceNext.v:62-89) that (1)-(7) do not hold,
   in the lane's form at PI := PI_pcap, KS := pcap_KS. Its LAWS TL TLF ML MTL MTF (MFSL) ASF FFL ASIL AFREAD are
   (1)-(7)'s and its SMP is fin_SMP. ---- *)
(* __asan_stack_malloc_0's rule (class 0, PcapSourceNextSpec.NX_CID).
   DISCHARGER StackMalloc0.stack_malloc0_contract via PcapSyms at the instance (a Theorem Labs lane) *)
Hypothesis ASM0 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc SEGSp B PcapSourceNextSpec.NX_CID.
(* __asan_memmove's contract at its entry. DISCHARGER a Theorem Labs lane's Memmove.asan_memmove_contract
   (lib/A/Rt/Memmove.v:147, at tfibsegs and 0x51bf0, from PcapSyms B) via PcapSyms at the instance. *)
Hypothesis AMM : forall fx : YK11.FPState,
  @MemmoveDef.amemmove_realizes fx rc SEGSp B (@pa_sigma rc pcap_listing PIp PS___asan_memmove).

(* ---- (9): the premises of PcapFuzzFopen.pb_libreac_fuzz_fopenX (PcapFuzzFopen.v:70-98) that (1)-(8) do not hold,
   in the lane's form at PI := PI_pcap, K := pcap_KS, roimg := ROI. Its FM_RA CTX MT ROI LAWS MLAWS (MTL) are
   (1)-(7)'s. Each carries its DISCHARGER; the header table gives the source files. ---- *)
(* ROI depends only on the bytes below alloc_ceiling. DISCHARGER a Theorem Labs lane's core: AE3i's ro_img over img_ro_region,
   which lies below alloc_ceiling and has no writable part (lib/A/AE3i.v:61-62; YI04.region_ok_transport). *)
Hypothesis ROIMG_LOW : PcapFuzzFopenG.roimg_low SEGSp ROI.
(* The word-constant window the fmemopen wrapper asks for, and ROI pinning it. DISCHARGER a Theorem Labs lane's core: mc_lo :=
   0x10350, mc_hi := 0x10370 from AE3i's chunk 0x10330 .. 0x10398 (lib/A/AE3i.v) at SEGS = tfibsegs (AB1v). *)
Variables mc_lo mc_hi : Z.
Hypothesis MCONSTS : forall (W : world SEGSp) (mem : word -> option byte), ROI (mrestrict (w_H W) mem) ->
  forall a, mc_lo <= a < mc_hi ->
  aview SEGSp (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGSp (Z_to_bv 64 a)).
(* The image facts of the two globals and of pcap_KS's stdio cells. DISCHARGER the image instance: fi_sep and
   fi_kimg by computation on PI_pcap (PcapFuzzFopen.v:496 fopen_img_tables computes fi_sep's tables), fi_head at the
   ASan sink head (as RO's law, lib/Reusable/PcapSinkHeads.v:30). *)
Hypothesis FI : PcapFuzzFopenG.FopenImg SK (VALp (A_OBJ PcapFuzzFopen.FO_LEN)) (VALp (A_OBJ PcapFuzzFopen.FO_FILE))
  pcap_KS.
(* The strcmp wrapper at the listing's strcmp trampoline and object FO_PATH. DISCHARGER a Theorem Labs lane's
   StrcmpIcpt.strcmp_lit_contract (lib/A/Rt/StrcmpIcpt.v:458, astrcmp_lit_realizes B of lib/A/Rt/StrcmpDef.v:53, at
   tfibsegs, from PcapSyms B) via PcapSyms at the instance (a Theorem Labs lane). *)
Hypothesis STRCMP : forall fx : YK11.FPState,
  @PcapFuzzFopenG.astrcmp_path_at fx rc SEGSp B ROI (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_strcmp)
    (VALp (A_OBJ PcapFuzzFopen.FO_PATH)).
(* The fmemopen wrapper. DISCHARGER a Theorem Labs lane's PFmemopenC.pcap_afmemopen_closed (lib/A/Stdio/PFmemopenC.v:23 on
   a working branch c5180b0bcf1, at tfibsegs, from PcapSyms B and amalloc04_rule); not on the base branch. *)
Hypothesis AFMEMOPEN : forall fx : YK11.FPState,
  @PFmemopenISpec.afmemopen_spec fx rc SK SEGSp B pcap_KS MT CTX
    (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fmemopen) FM_RA mc_lo mc_hi.

(* ---- (10): the premises of PcapHarnessPA.pe_A (PcapHarnessPA.v:91-114) that (1)-(9) do not hold, in the lane's form
   at PI := PI_pcap, KS := pcap_KS. Its LAWS MLAWS (MTL) ASIL HRO (RO) FM_RA CTX ROI HROI HPATH HFMU are (1)-(7)'s and
   its OPENS is fin_OPEN. Each carries its DISCHARGER; the header table gives the source files. ---- *)
(* __asan_memcpy / __asan_memset at the listing's trampolines. DISCHARGER a Theorem Labs lane's core: AD1o.ocpy_of_icpt /
   oset_of_icpt (lib/A/AD1o.v:82, :84, at tfibsegs and pc_wrap_memcpy / pc_wrap_memset (as_code B), from PcapSyms B)
   via PcapSyms at the instance. *)
Hypothesis HCPY : forall fx : YK11.FPState,
  @aintrin_realizes fx rc SEGSp B OCpy (@pa_sigma rc pcap_listing PIp PS___asan_memcpy).
Hypothesis HSET : forall fx : YK11.FPState,
  @aintrin_realizes fx rc SEGSp B OSet (@pa_sigma rc pcap_listing PIp PS___asan_memset).
(* The call spines of pe_A's pcap_source_open call (its landing PP_K2), the lane's HCTX; (6)'s HCTX is tail_R1's,
   at PP_K7. DISCHARGER the open side's instance facts (as HCTX). *)
Hypothesis HCTX_A : In [VALp A_TEXT + PP_K2; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K2] CTX.

(* ---- (11): the premise of PcapHarnessWalkKR.pe_KR (PcapHarnessWalkKR.v:981-988) that (1)-(10) do not hold, in the
   lane's form at PI := PI_pcap, KS := pcap_KS. Its LAWS MTL RO ASIL are (1)-(6)'s, its HGX is fin_HGX and its NEXT
   is fin_NEXT (its TL is unused). ---- *)
(* The bcmp wrapper at the listing's bcmp trampoline (0x41570, PcapAddr.v:24). DISCHARGER a Theorem Labs lane's core:
   YG0d.AsanAPI's aa_bcmp (lib/Reusable/YG0d.v:543), at pc_wrap_bcmp (as_code B) = 0x41570 (AF0l.v:14); the value at
   pcap's B NOT FOUND. *)
Hypothesis ABCMP : forall fx : YK11.FPState,
  @abcmp_realizes fx rc SEGSp B (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_bcmp).

(* pb_pcap_source_openX's SMP, from ML (YG0d.v:520 ml_stack_malloc_progress), as PcapHarnessPE.v:369 does. *)
Lemma fin_SMP : stack_malloc_progressP B.
Proof. exact (fun s cid HW Hc Hn => ml_stack_malloc_progress _ ML s cid HW Hc Hn). Qed.

(* ASF, the frame give-back law tail_leave, pb_pcap_source_openX and pb_pcap_source_nextX take: YG0t.v:474
   astack_free_law_ok, general in the segments and B, with no premise (fit). *)
Lemma fin_ASF : @astack_free_law rc SEGSp B.
Proof. fit (YG0t.astack_free_law_ok (rc := rc) SEGSp B). Qed.

(* pb_pcap_source_openX's HGX at PI_pcap: objects 4 and 2 are G_HARNESS's two globals (PcapEntryTop.pi_pcap_obj4 /
   pi_pcap_obj2), so it is (2)'s pcap_G_harness_gx_ok and the errno conjunct of pcap_G_harness_pe_bytes. *)
Lemma fin_HGX_open : forall a,
  (VALp (A_OBJ 4) <= a < VALp (A_OBJ 4) + 8) \/ (VALp (A_OBJ 2) <= a < VALp (A_OBJ 2) + 8) ->
  in_img SEGSp a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite (@PcapEntryTop.pi_pcap_obj4 rc), (@PcapEntryTop.pi_pcap_obj2 rc) in Ha.
  assert (HG : inG G_HARNESS a).
  { unfold inG, G_HARNESS. destruct Ha as [Ha | Ha];
      [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd]; unfold in_zr; cbn [fst snd]; lia. }
  destruct (pcap_G_harness_gx_ok a HG) as [G1 G2]. destruct (pcap_G_harness_pe_bytes a HG) as (_ & _ & G3).
  split; [exact G1|]. split; [exact G2 | exact G3].
Qed.

(* FOPEN, the statement pb_pcap_source_openX takes, from a Theorem Labs lane's walk (PcapFuzzFopen.v:218): the conclusion
   syntactically the lane's own statement (fit), at the premises of (9). *)
Set Printing All.
Lemma fin_FOPEN : forall fx : YK11.FPState,
  @PcapFuzzFopenDefs.tlibreac_fuzz_fopen_specX fx rc SK SEGSp (@PcapFuzzFopen.A_libreac_fuzz_fopenP rc PIp)
    (VALp (A_OBJ PcapFuzzFopen.FO_PATH)) (VALp (A_OBJ PcapFuzzFopen.FO_LEN)) (VALp (A_OBJ PcapFuzzFopen.FO_FILE)) ROI B
    pcap_KS MT FM_RA CTX.
Proof.
  intros fx.
  fit (@PcapFuzzFopen.pb_libreac_fuzz_fopenX fx rc SK PIp B pcap_KS FM_RA CTX MT ROI ROIMG_LOW mc_lo mc_hi MCONSTS
    LAWS MTL FI (STRCMP fx) (AFMEMOPEN fx)).
Qed.

(* OPEN, the statement tail_R1 takes, from the pcap_source_open walk (PcapSourceOpen.v:812): the conclusion syntactically
   OPEN's type (fit). *)
Lemma fin_OPEN : forall fx : YK11.FPState,
  @tpcap_source_open_specX fx rc SK SEGSp LOp HIp (VALp (A_OBJ 3)) (VALp (A_OBJ 4)) (VALp (A_OBJ 2)) ROI B pcap_KS MT
    FM_RA CTX (VALp A_TEXT + AF_pcap_source_open).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  (* conversion: FOPEN at A_libreac_fuzz_fopenP = BASE + AF_libreac_fuzz_fopen, FO_PATH/LEN/FILE = 3/4/2
     (PcapFuzzFopen.v:43-45, :68) *)
  fit (@PcapSourceOpen.pb_pcap_source_openX fx rc SK PIp B pcap_KS MT FM_RA CTX ROI ro_chunk_addr ROIMG_KEPT LAWS
    TL TLF ML (ASM1 fx) fin_SMP fin_ASF FFL MTL MFSL FM (fin_FOPEN fx) (AFREAD fx) ra_fc1 ra_fc2 (AFCLOSE fx) HUfc1 HUfc2
    ASIL (pi_pcap_obj12_mode rc) HGRO fin_HGX_open HPATH RO).
Qed.

(* NEXT, the statement pe_C, tail_R2 and tail_R4 take, from a Theorem Labs lane's walk (PcapSourceNext.v:147): the conclusion
   syntactically NEXT's type (fit). *)
Lemma fin_NEXT : forall fx : YK11.FPState,
  @tpcap_source_next_specX fx rc SK SEGSp LOp HIp NX_STK B MT pcap_KS (VALp A_TEXT + AF_pcap_source_next).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapSourceNext.pb_pcap_source_nextX fx rc SK PIp B MT pcap_KS LAWS TL TLF ML MTL MFSL (ASM0 fx) fin_SMP fin_ASF
    FFL ASIL (AFREAD fx) (AMM fx)).
Qed.

(* CLOSE, the statement tail_W and tail_R3 take, from a Theorem Labs lane's walk (PcapSourceClose.v:379), general in
   B, K and MT like OPEN and NEXT: the conclusion syntactically CLOSE's type (fit). Its LAWS TL ra_fc1 ra_fc2 AFCLOSE
   HUfc1 HUfc2 ASIL FM are (6)-(7)'s. *)
Lemma fin_CLOSE : forall fx : YK11.FPState,
  @tpcap_source_close_specX fx rc SK SEGSp LOp HIp B pcap_KS MT (VALp A_TEXT + AF_pcap_source_close).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapSourceClose.pb_pcap_source_closeX fx rc SK PIp B pcap_KS MT LAWS TL ra_fc1 ra_fc2 (AFCLOSE fx) HUfc1 HUfc2
    ASIL FM).
Qed.

(* ===================== the proved walks, at the top's hypothesis types ===================== *)

Lemma fin_pe_E : forall fx : YK11.FPState,
  PFROM fx (GIx (@GI_K1) fx) -> PFROM fx (GIx (@GI_leave) fx) -> @pe_start fx rc SK PIp B MT pcap_KS (POSTP fx).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessPE.pe_E fx rc SK PIp B MT pcap_KS LAWS TL TLF MTL MFSL ML (ASM1 fx) (AM fx) ASIL
         (@PcapEntryTop.pi_pcap_glen rc) (POSTP fx)).
Qed.

Lemma fin_pe_A : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K2) fx) -> PFROM fx (GIx (@GI_K1) fx).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessPA.pe_A fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL RO (HCPY fx) (HSET fx) FM_RA CTX ROI
         (fin_OPEN fx) HROI HPATH HCTX_A HFMU).
Qed.

Lemma fin_pe_B : forall fx : YK11.FPState,
  PFROM fx (GIx (@GI_K3) fx) -> PFROM fx (GIx (@GI_K12r) fx) -> PFROM fx (GIx (@GI_K2) fx).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessA.pe_B fx rc SK PIp B MT pcap_KS LAWS TL MTL ASIL (AM fx) (AF fx) (@PcapEntryTop.pi_pcap_glen rc)
         (POSTP fx)).
Qed.

(* pe_C's RO is an explicit Section hypothesis at the source since a working branch 621e74e7e94: it is passed in its place. *)
Lemma fin_pe_C : forall fx : YK11.FPState, PFROM fx (GIx (@GI_KD) fx) -> PFROM fx (GIx (@GI_K3) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessA.pe_C fx rc SK PIp B MT pcap_KS LAWS MTL (fin_NEXT fx) RO ASIL (POSTP fx)).
Qed.

(* pe_WalkR's HGX: gx_ok of pe_G, which is G_HARNESS at PI_pcap (PcapEntryTop.pi_pcap_pe_G). *)
Lemma fin_HGX : gx_ok SEGSp B (@pe_G rc PIp).
Proof. rewrite (@PcapEntryTop.pi_pcap_pe_G rc). exact pcap_G_harness_gx_ok. Qed.

(* KR, pe_WalkR's Section hypothesis, from a Theorem Labs lane's walk (PcapHarnessWalkKR.v:3084): the conclusion syntactically
   KR's type (fit). *)
Lemma fin_KR : forall fx : YK11.FPState, forall (POST : @ecx rc PIp -> world SEGSp -> config -> Prop) (n : nat),
  @PcapHarnessWalk.at_cut rc SK PIp B MT pcap_KS (GIx (@GI_KL2) fx) POST n ->
  @PcapHarnessWalk.at_cut rc SK PIp B MT pcap_KS (GIx (@GI_KR) fx) POST (S n).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessWalkKR.pe_KR fx rc SK PIp B MT pcap_KS LAWS MTL RO fin_HGX (fin_NEXT fx) (ABCMP fx) ASIL).
Qed.

(* WALKR, pe_Walk's Section hypothesis, from pe_WalkR (a Theorem Labs lane's closed term), by `fit` at its exact type. *)
Lemma fin_WALKR : forall fx : YK11.FPState, forall POST : @ecx rc PIp -> world SEGSp -> config -> Prop,
  @pe_from rc SK PIp B MT pcap_KS POST (GIx (@GI_K5) fx) -> @pe_from rc SK PIp B MT pcap_KS POST (GIx (@GI_K4) fx).
Proof.
  intros fx POST.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessWalkR.pe_WalkR fx rc SK PIp B MT pcap_KS LAWS fin_HGX (@PcapEntryTop.pi_pcap_glen rc) ASIL (fin_KR fx)
         POST).
Qed.

Lemma fin_pe_Walk : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K5) fx) -> PFROM fx (GIx (@GI_KD) fx).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  (* fin_WALKR's type is syntactically pe_Walk's WALKR premise. *)
  lazymatch type of (@PcapHarnessWalk.pe_Walk fx rc SK PIp B MT pcap_KS LAWS ASIL) with
  | ?E -> _ => let T := type of (fin_WALKR fx) in constr_eq T E
  end.
  fit (@PcapHarnessWalk.pe_Walk fx rc SK PIp B MT pcap_KS LAWS ASIL (fin_WALKR fx) (POSTP fx)).
Qed.

Lemma fin_tail_W : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K6) fx) -> PFROM fx (GIx (@GI_K5) fx).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessTail.tail_W fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL (fin_CLOSE fx)
         (@PcapEntryTop.pi_pcap_glen rc) RO).
Qed.

Lemma fin_tail_R1 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K7) fx) -> PFROM fx (GIx (@GI_K6) fx).
Proof.
  intros fx.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  fit (@PcapHarnessTail.tail_R1 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL FM_RA CTX ROI (fin_OPEN fx) HROI
         HPATH HCTX HFMU RO).
Qed.

Lemma fin_tail_R2 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K8) fx) -> PFROM fx (GIx (@GI_K7) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_R2 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL (fin_NEXT fx) RO).
Qed.

Lemma fin_tail_R3 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K9) fx) -> PFROM fx (GIx (@GI_K8) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_R3 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL (fin_CLOSE fx) RO).
Qed.

Lemma fin_tail_R4 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K10) fx) -> PFROM fx (GIx (@GI_K9) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_R4 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL (fin_NEXT fx) RO).
Qed.

Lemma fin_tail_R5 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K11) fx) -> PFROM fx (GIx (@GI_K10) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_R5 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS TL MTL ASIL (AF fx)).
Qed.

Lemma fin_tail_R6 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K12) fx) -> PFROM fx (GIx (@GI_K11) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_R6 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS TL MTL ASIL (AF fx)).
Qed.

Lemma fin_tail_R7 : forall fx : YK11.FPState, PFROM fx (GIx (@GI_K12r) fx) -> PFROM fx (GIx (@GI_K12) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_R7 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS ASIL).
Qed.

Lemma fin_tail_K12r : forall fx : YK11.FPState, PFROM fx (GIx (@GI_leave) fx) -> PFROM fx (GIx (@GI_K12r) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_K12r fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS ASIL).
Qed.

Lemma fin_tail_leave : forall fx : YK11.FPState,
  @pe_from_ret rc SK PIp B MT pcap_KS (POSTP fx) (GIx (@GI_ret) fx) -> PFROM fx (GIx (@GI_leave) fx).
Proof.
  (* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 *)
  intros fx. fit (@PcapHarnessTail.tail_leave fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS ASIL ML fin_ASF FFL MFSL).
Qed.

Lemma fin_tail_ret : forall fx : YK11.FPState,
  @pe_from_ret rc SK PIp B MT pcap_KS (POSTP fx) (GIx (@GI_ret) fx).
Proof.
  intros fx. fit (@PcapHarnessTail.tail_ret fx rc SK PIp B MT pcap_KS LAWS MTL).
Qed.

(* ===================== the composition ===================== *)

Theorem pcap_entry_final : @tfib_lib_contract_x_all_A rc SK B MT XM_LIB XN_LIB pcap_KS.
Proof.
  fit (@PcapEntryTop.pcap_entry_top rc SK B MT XM_LIB XN_LIB MTL HXM HXMN pcap_G_harness_gx_ok pcap_G_harness_pe_bytes
         HMRA HFRA HUNIV ASIL fin_pe_E fin_pe_A fin_pe_B fin_pe_C fin_pe_Walk fin_tail_W fin_tail_R1 fin_tail_R2 fin_tail_R3
         fin_tail_R4 fin_tail_R5 fin_tail_R6 fin_tail_R7 fin_tail_K12r fin_tail_leave fin_tail_ret).
Qed.
Unset Printing All.

Print Assumptions pcap_entry_final.

(* Sink-head audit (a Theorem Labs lane, 06:03Z): each walk application above, printed in full, so that every sink-head
   argument in it can be read; each is the Section variable SK. *)
(* conversion: ASIL at pa_segs PI_pcap = Asan.M.loaded_segments, PcapEntryTop.v:140-141 (each Check passing ASIL) *)
(* conversion: FOPEN at A_libreac_fuzz_fopenP = BASE + AF_libreac_fuzz_fopen, FO_PATH/LEN/FILE = 3/4/2
   (PcapFuzzFopen.v:43-45, :68) (the Check of pb_pcap_source_openX) *)
Set Printing All.
Check (fun fx : YK11.FPState => @PcapHarnessPE.pe_E fx rc SK PIp B MT pcap_KS LAWS TL TLF MTL MFSL ML (ASM1 fx) (AM fx)
  ASIL (@PcapEntryTop.pi_pcap_glen rc) (POSTP fx)).
Check (fun fx : YK11.FPState => @PcapHarnessPA.pe_A fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL RO (HCPY fx)
  (HSET fx) FM_RA CTX ROI (fin_OPEN fx) HROI HPATH HCTX_A HFMU).
Check (fun fx : YK11.FPState => @PcapHarnessA.pe_B fx rc SK PIp B MT pcap_KS LAWS TL MTL ASIL (AM fx) (AF fx)
  (@PcapEntryTop.pi_pcap_glen rc) (POSTP fx)).
Check (fun fx : YK11.FPState => @PcapHarnessA.pe_C fx rc SK PIp B MT pcap_KS LAWS MTL (fin_NEXT fx) RO ASIL
  (POSTP fx)).
Check (fun fx : YK11.FPState => @PcapHarnessWalk.pe_Walk fx rc SK PIp B MT pcap_KS LAWS ASIL
  (fun POST => @PcapHarnessWalkR.pe_WalkR fx rc SK PIp B MT pcap_KS LAWS fin_HGX (@PcapEntryTop.pi_pcap_glen rc) ASIL
     (fin_KR fx) POST) (POSTP fx)).
Check (fun fx : YK11.FPState => @PcapHarnessWalkKR.pe_KR fx rc SK PIp B MT pcap_KS LAWS MTL RO fin_HGX (fin_NEXT fx)
  (ABCMP fx) ASIL).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_W fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL (fin_CLOSE fx)
  (@PcapEntryTop.pi_pcap_glen rc) RO).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R1 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL FM_RA CTX ROI
  (fin_OPEN fx) HROI HPATH HCTX HFMU RO).
Check (fun fx : YK11.FPState => @PcapFuzzFopen.pb_libreac_fuzz_fopenX fx rc SK PIp B pcap_KS FM_RA CTX MT ROI ROIMG_LOW
  mc_lo mc_hi MCONSTS LAWS MTL FI (STRCMP fx) (AFMEMOPEN fx)).
Check (fun fx : YK11.FPState => @PcapSourceOpen.pb_pcap_source_openX fx rc SK PIp B pcap_KS MT FM_RA CTX ROI
  ro_chunk_addr ROIMG_KEPT LAWS TL TLF ML (ASM1 fx) fin_SMP fin_ASF FFL MTL MFSL FM (fin_FOPEN fx) (AFREAD fx) ra_fc1
  ra_fc2 (AFCLOSE fx) HUfc1 HUfc2 ASIL (pi_pcap_obj12_mode rc) HGRO fin_HGX_open HPATH RO).
Check (fun fx : YK11.FPState => @PcapSourceNext.pb_pcap_source_nextX fx rc SK PIp B MT pcap_KS LAWS TL TLF ML MTL MFSL
  (ASM0 fx) fin_SMP fin_ASF FFL ASIL (AFREAD fx) (AMM fx)).
Check (fun fx : YK11.FPState => @PcapSourceClose.pb_pcap_source_closeX fx rc SK PIp B pcap_KS MT LAWS TL ra_fc1 ra_fc2
  (AFCLOSE fx) HUfc1 HUfc2 ASIL FM).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R2 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL
  (fin_NEXT fx) RO).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R3 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL (fin_CLOSE fx)
  RO).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R4 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS MTL ASIL
  (fin_NEXT fx) RO).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R5 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS TL MTL ASIL (AF fx)).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R6 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS TL MTL ASIL (AF fx)).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_R7 fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS ASIL).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_K12r fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS ASIL).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_leave fx rc SK PIp B MT pcap_KS (POSTP fx) LAWS ASIL ML fin_ASF FFL
  MFSL).
Check (fun fx : YK11.FPState => @PcapHarnessTail.tail_ret fx rc SK PIp B MT pcap_KS LAWS MTL).
Unset Printing All.

End final.

Print Assumptions pcap_entry_final.
Set Printing All.
Check @pcap_entry_final.
Unset Printing All.

(* The plain build's sink head (Reusable/YI5b.v src0_sink_head, 0x4f3b0) is not loaded by this file's closure, so it
   occurs in no statement used or proved here (a statement carrying it is vacuous; a Theorem Labs lane, 06:03Z). The log shows
   it: every object named src0_sink_head, every class named sink_head, and the global instances of the class SK has. *)
Locate src0_sink_head.
Locate sink_head.
Print Instances OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head.
