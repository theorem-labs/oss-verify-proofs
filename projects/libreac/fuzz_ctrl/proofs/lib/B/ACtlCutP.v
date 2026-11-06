(* lib/B/ACtlCutP.v -- the 91 cut bodies of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput,
   transcribed from ctrl's own cut text against the fixed interface of lib/B/ACtlCut.v.  Written by a Theorem Labs lane's
   transcription lane (a Theorem Labs lane) with an image-B copy of a Theorem Labs lane's generator
   (gen_b.py, from gen.py,
   which wrote lib/A/ACtlCutP.v at a working branch 6446767144e); single writer.  DEFINITIONS ONLY:
   no Lemma, no Axiom, no Parameter, no Admitted, no tactic.

   WHAT THIS FILE IS
   ctrl's cut text of record is lib/B/Prog/SlotInv.v at 23a791566db (3406 lines).  Its shells (FRA :330,
   FRAH :447, ENT :371, CUTST :433, CUTST0 :489, CUTSTR :495, PREF :1391) speak the Theorem Labs lane frame vocabulary this
   walk replaces, so they are NOT transcribed: ACtlCut.v's ctl_base (the core's own lib pre), ctl_from and
   ctl_rt state them in the donor's form (the translation section of
   llvmf-B-walk-plan.md section 2.1 (a working note, not in this delivery)).  What IS transcribed is every cut's own
   register / memory predicate and the body bundles those predicates call, verbatim.  Each record is named
   C_<cut> after the cut column of cut-table-B.tsv (a working note, not in this delivery) with the index
   letters dropped from the name (they are the record's idx argument): row "B816ec_at b" is C_B816ec_at.

   RULE 24 (released proofs first).  proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28
   20:16:23Z from main@e966c513ee6, ossv/recipes@a8831f7c5c): 30 files named for it, 1290 uses of its address,
   105 related; released proofs for seven other units, as ASan for bluez/fuzz_hci and for the donor
   cgif/cgif_file_fuzzer.  Second-agent check a Theorem Labs lane, 21:10Z: CONFIRM -- cgif is the only released ASan
   donor matching this unit on branch (ossv/recipes), LPS (2afba80c) and framework (afn_pre / ajournal); the
   donor's constants are A/ACfn.v:20-25 (image B: the root YCfn.v:18-23).  This file restates ctrl's cut text
   against that donor's form.

   FIELD MAP (brief cutp-transcribe.md), applied to every body:
     g_p g -> c_p cx    g_n g -> c_n cx    g_in g -> c_in cx    g_regs g -> c_regs cx
     g_mem g -> c_mem cx    g_md g -> c_md cx    g_S g -> c_sp cx    rg -> ACtlCut.rgv
     AC.aspZ -> Reusable.YG0d.spZ    ASAN_K -> B.ACtlK.ASAN_K
   g_H and g_T have no counterpart.  A conjunct naming the live-heap ghost g_H becomes the body's own
   Permutation of bl (the live list ACtlCut.v hands the body) against the entry blocks; a conjunct naming the
   kept-block ghost g_T is dropped (plan 2.1, rows "ENT T subset H" and "DROP").  asan_cells / shadow_rw /
   mem_inv / ro_agree are dropped wherever a body names them: ctl_rt carries asan_cells, shadow_rw and ro_agree
   (ACtlCut.v section 4; mem_inv is no longer carried, a Theorem Labs lane 00:35Z, and no image-B body names it -- plan (a working note, not in this delivery):
   no image-B bundle names any of the four; LOOPB, f1_IN and FSREC are the restated ones).  The CUTST / CUTST0 /
   CUTSTR / FCUTP / FCUT wrapper is dropped with its configuration equation; CUTST0's and CUTSTR's selector
   becomes the body's sel argument.  A conjunct naming the Theorem Labs lane vocabulary is dropped at the smallest
   conjunct that names it: image B nests some inside a larger group (an `exists A kp, ...` group, the conclusion
   of an implication), where the rest of the group is kept.  Every dropped conjunct is listed, record by record,
   in the transcription report.

   ctrl's OWN READERS, TRANSCRIBED HERE (ACtlCut.v keeps only rgv and a0v): q64 / u32 / u16 / b8 (SlotInv.v
   :268-271), Sfr (:282) and spill (:834-835), over lib/Lib's memory predicates, qualified, and AsanRT's
   shadow_addr.  ctrl writes them against the image's segment list rsegs; this file writes them against the
   walk's segs (the same image's list under the core's name), so lib/B/Img0.v is NOT in the closure.  If the
   core's segs is not definitionally ctrl's rsegs, that is one bridge lemma in lib/B/ProgBridge.v, not an edit
   here -- it is the only place the two lists meet.

   SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): getr, mkst, seg_rom exist in BOTH lib/Lib and the core's
   YK11 and DIFFER (lib/Lib's mkst empties the FP registers), so a file can build green and be wrong.  Every
   one of them here is lib.Reusable.YK11.* (cfg_at: Reusable.YG0d.cfg_at), lib/Lib is never Imported, and lib/Lib
   is used only for the memory predicates (bytes_at, rw_cells / CB, addressable, stk, mbyte).  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/B/ACtlCutP.v
   Output: (empty -- no hit outside this comment).

   THE FAKE-STACK ARM (two Theorem Labs lanes, 21:29Z-21:30Z, ACtlCut.v section 3): the class-full arm,
   where __asan_stack_malloc_6 would return 0, is not a live case in the model -- at the entry frames S = [],
   so the room premise holds, astack_malloc_realizes has only the frame_addr outcome (YG0d.v:284-299) and
   stack_malloc_progress rules the null result out (YG05.v:69-84).  The stage at the fake-stack call discharges
   the machine's s8 = 0 branch from that law.  So every cut from the frame's allocation to its release owns the
   class-6 frame (own6), ENTRY and the post-release cuts own nothing (own0), and the shell passes sel = fr.

   MODULES THIS FILE REQUIRES (complete; nothing project-side is Imported or Exported, every name is fully
   qualified through the Module aliases below, so the auditor's check is
     grep -nE 'Require (Import|Export)' lib/B/ACtlCutP.v
   whose only code hits are the Coq stdlib line `From Coq Require Import ZArith List Permutation.` and LPS's
   machine-vocabulary line `From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics
   MemImageType State Run.`; no project module is Imported or Exported).

     lib/Reusable/YK11.v                        the core's machine vocabulary (getr; word, byte and Z_to_bv are LPS's)
     lib/Reusable/YA0n.v YG00.v YG01.v YG0f.v   the core's world / layout / state vocabulary (YG0f: asyms, as_tp)
     lib/Reusable/YG0d.v YC5d.v YCbq.v YM05.v   the core's blocks, meter, journal, run ceiling
     lib/Reusable/YK18.v                        the core's leaf type (ACtlCut's post)
     lib/Reusable/YO09.v YI16.v                 lib_shape, sink_head (ACtlCut.v's Section contexts)
     lib/Reusable/YB1v.v                        the core's segment list tfibsegs (the segs notation)
     lib/Reusable/YCfn.v                        the core's lib contract (ACtlCut's ctl_base / ctl_post)
     lib/B/ACtlK.v                              this walk's internal names (a Theorem Labs lane)
     lib/B/ACtlCut.v                            this walk's cut interface (a Theorem Labs lane)
     lib/B/Prog/SlotModel.v                     pure model (no frame vocabulary)
     lib/Prog/RcModel.v                         pure model (no frame vocabulary)
     lib/Prog/RcIdentModel.v                    pure model (no frame vocabulary)
     lib/Prog/RcFrag.v                          pure model (no frame vocabulary)
     lib/Prog/RcReply.v                         pure model (no frame vocabulary)
     lib/Prog/RcLeaf.v                          pure model (no frame vocabulary)
     lib/Prog/RcDecl.v                          pure model (no frame vocabulary)
     lib/Prog/RcParse.v                         pure model (no frame vocabulary)
     lib/Prog/RcPorts.v                         pure model (no frame vocabulary)
     lib/Prog/RcKind.v                          pure model (no frame vocabulary)
     lib/Prog/RcClassify.v                      pure model (no frame vocabulary)
     lib/Prog/RcRec.v                           pure model (no frame vocabulary; image B only, one body: C_B823d8_at)
     lib/Prog/RcSynth.v RcBox.v                 pure model (no frame vocabulary; image B only: RBE, R6X,
                                                C_B8169c, C_B816ec_at)
     lib/Lib/Mem.v Cells.v Step.v Frame.v       memory predicates only (porter 21:33Z), never Imported
     lib/B/AsanRT.v                             addressable, app_mem, end_in_app, APPMEM_END, shadow_addr,
                                                RT_LO / RT_HI (one body: C_B81d18)
     lib/B/AsanRTFacts.v                        all_app (one body: C_B81d18)
     lib/B/Prog/reac_ctrl_kind_name_c.v         QMARK, kind_name_addr, kind_name_bytes, KIND_NAME
     lib/B/Prog/bcmp_wrap_c.v                   BCMP_WRAP_K
     lib/B/Prog/reac_ctrl_identity_fragment_c.v fg_mem, REAC_CTRL_IDENTITY_FRAGMENT_K
     lib/B/Prog/asan_memset_c.v                 ASAN_MEMSET_K (one body: C_B81d18)
     lib/B/Prog/reac_ctrl_identity_reply_c.v    REAC_CTRL_IDENTITY_REPLY_K (one body: C_B81d68)
     lib/B/Prog/reac_ctrl_parse_c.v             REAC_CTRL_PARSE_BC (one body: C_B81d68)
     lib/Prog/reac_ctrl_build_as_c.v            ba_tbl (image B only: RBE, R6X)
     lib/B/Prog/reac_ctrl_build_as_c.v          BA_FR (image B only: RBE, R6X)
     lib/B/Spec/StrFun.v                        memcmp_model, find_byte

   NOT required, and never to be: lib/B/Prog/SlotInv.v, lib/AZ/**, lib/AZ/AS/SpinAlg.v (not in this delivery), lib/B/Contract.v,
   lib/B/FrameAPI.v, lib/A/W6.  (a Theorem Labs lane's ruling, 21:29Z / 21:33Z: the landing list targets the FRAME
   route, not ctrl's pure input model or lib/Lib's memory predicates; Require without Import, fully qualified,
   is allowed.)

   CLOSURE, MEASURED FROM THIS FILE'S OWN REQUIRES (not assumed; image A's first scan started at SlotModel.v
   only and so missed the file's other roots -- the composition lane found an AsanRTInv.v Require that way,
   22:01Z).  Command, run in proofs/libreac/fuzz_ctrl; it reads EVERY `From <prefix> Require [Import|Export]
   <names>.` of lib/B/ACtlCutP.v, follows only prefixes under OSSVerify.Proofs.libreac.fuzz_ctrl, and
   handles dotted module names (Reusable.YK11) (image A's command, with image B's forbidden set):

     python3 - <<'EOF'
     import re,os,collections
     ROOT='OSSVerify.Proofs.libreac.fuzz_ctrl.'
     RE=re.compile(r'From\s+([\w.]+)\s+Require\s+((?:Import|Export)\s+)?([\w.\s]+?)\.(?=\s)',re.S)
     def path_of(m):
       p=m.replace('.','/')+'.v'
       return p if os.path.exists(p) else None
     def reqs(p): return [(m.group(1),n) for m in RE.finditer(open(p).read()) for n in m.group(3).split()]
     def resolve(pref,n): return path_of((pref[len(ROOT):]+'.'+n) if pref.startswith(ROOT) else n)
     q=[resolve(a,b) for a,b in reqs('lib/B/ACtlCutP.v') if a.startswith('OssFuzz')]
     q=[f for f in q if f]; seen=set(); files=[]; ext=collections.Counter(); miss=set()
     while q:
       f=q.pop(0)
       if f in seen: continue
       seen.add(f); files.append(f)
       for pref,n in reqs(f):
         if pref.startswith('OssFuzz'):
           p=resolve(pref,n)
           if p: q.append(p)
           else: miss.add(n)
         else: ext[pref]+=1
     FORB=['Prog/SlotInv.v','/AZ/','AsanRTInv.v','/B/Contract.v','FrameAPI.v','SpinAlg','/W6/','MemNorm.v','/B/Reusable/']
     print(len(files)); [print(' ',f) for f in sorted(files)]
     print('FORBIDDEN:',[f for f in sorted(files) if any(k in '/'+f for k in FORB)])
     print('NOT YET ON DISK (the core):',sorted(miss)); print('EXT:',sorted(ext))
     EOF

   Output (on the commit that adds this file, with lib/B/Prog/SlotModel.v = 23a791566db's blob de18d111c37):
   144 files, and the line that matters --
     FORBIDDEN: []
   i.e. nothing under the porter's forbidden set (lib/B/Prog/SlotInv.v, lib/AZ/**, lib/B/AsanRTInv.v,
   lib/B/Contract.v, lib/B/FrameAPI.v, AZ/AS/SpinAlg, W6, lib/B/MemNorm.v, anything under lib/B/Reusable) is
   reachable, and no lib/AZ/AsanW, W6 or cut-free (SegCF, *_cfw) file either (lib/Reusable/R/Cfg.v, also in image
   A's measured set, is the core's configuration-record file, not a cut-free one).  NOT YET ON DISK, so not in the
   count, and all of them the relocated core's own files, which the porter owns: lib.Reusable.YA0n / YB1v / YC5d / YCbq / YCfn / YG00 / YG01 / YG0d / YG0f / YG0n.
   External prefixes: Stdlib, Coq, Ltac2, stdpp(.bitvector), LinuxProcessSemantics.Riscv,
   LinuxProcessSemantics.EquivalenceDefinition, LinuxProcessSemantics.LinuxProcessSem(.Sys/.Sys.Mm/.Checks/
   .Checks.Sys).  The 144 files, every one allowed:

     lib/AllocBound.v                                lib/AllocCount.v
     lib/AllocDepth.v                                lib/AllocFree.v
     lib/AllocFreeMB.v                               lib/AllocFreePath.v
     lib/AllocGS.v                                   lib/AllocMB.v
     lib/AllocMalloc.v                               lib/AllocMallocMB.v
     lib/AllocMallocPath.v                           lib/AllocRealloc.v
     lib/AllocReallocMB.v                            lib/AllocSI.v
     lib/AllocSlots.v                                lib/B/ACtlCut.v
     lib/B/ACtlK.v                                   lib/B/AsanRT.v
     lib/B/AsanRTFacts.v                             lib/B/Img0.v
     lib/B/Prog/RcAsanFP.v                           lib/B/Prog/SlotModel.v
     lib/B/Prog/asan_memset_c.v                      lib/B/Prog/asan_stack_malloc_c.v
     lib/B/Prog/bcmp_wrap_c.v                        lib/B/Prog/memcmp_c.v
     lib/B/Prog/reac_box_model_block_c.v             lib/B/Prog/reac_ctrl_build_as_c.v
     lib/B/Prog/reac_ctrl_identity_fragment_c.v      lib/B/Prog/reac_ctrl_identity_reply_c.v
     lib/B/Prog/reac_ctrl_kind_name_c.v              lib/B/Prog/reac_ctrl_parse_c.v
     lib/B/Spec/StrFun.v                             lib/BWorld.v
     lib/Img0.v                                      lib/Lib/Acfg.v
     lib/Lib/AndN.v                                  lib/Lib/Arr.v
     lib/Lib/Bytes.v                                 lib/Lib/Ceiling.v
     lib/Lib/Cells.v                                 lib/Lib/ExN.v
     lib/Lib/Exec.v                                  lib/Lib/FP.v
     lib/Lib/Frame.v                                 lib/Lib/Image.v
     lib/Lib/LiaTwx2.v                               lib/Lib/MState.v
     lib/Lib/Mem.v                                   lib/Lib/PropExec.v
     lib/Lib/Step.v                                  lib/Lib/Tac.v
     lib/Lib/ZBridge.v                               lib/Lib/Zifyk6b.v
     lib/Prog/RcBox.v                                lib/Prog/RcClassify.v
     lib/Prog/RcDecl.v                               lib/Prog/RcEmit.v
     lib/Prog/RcFin.v                                lib/Prog/RcFrag.v
     lib/Prog/RcIdentModel.v                         lib/Prog/RcKind.v
     lib/Prog/RcLay.v                                lib/Prog/RcLeaf.v
     lib/Prog/RcMatch.v                              lib/Prog/RcModel.v
     lib/Prog/RcParse.v                              lib/Prog/RcPorts.v
     lib/Prog/RcRec.v                                lib/Prog/RcReply.v
     lib/Prog/RcSynth.v                              lib/Prog/reac_ctrl_build_as_c.v
     lib/Reusable/PlaceCap.v                         lib/Reusable/R/Cfg.v
     lib/Reusable/R/Place.v                          lib/Reusable/YI16.v
     lib/Reusable/YK02.v                             lib/Reusable/YK0h.v
     lib/Reusable/YK0i.v                             lib/Reusable/YK0j.v
     lib/Reusable/YK0l.v                             lib/Reusable/YK0n.v
     lib/Reusable/YK0q.v                             lib/Reusable/YK0s.v
     lib/Reusable/YK0t.v                             lib/Reusable/YK0v.v
     lib/Reusable/YK10.v                             lib/Reusable/YK11.v
     lib/Reusable/YK14.v                             lib/Reusable/YK15.v
     lib/Reusable/YK16.v                             lib/Reusable/YK18.v
     lib/Reusable/YK1a.v                             lib/Reusable/YK1b.v
     lib/Reusable/YK1c.v                             lib/Reusable/YK1d.v
     lib/Reusable/YK1e.v                             lib/Reusable/YK1g.v
     lib/Reusable/YK1i.v                             lib/Reusable/YM02.v
     lib/Reusable/YM03.v                             lib/Reusable/YM05.v
     lib/Reusable/YM06.v                             lib/Reusable/YM0b.v
     lib/Reusable/YO02.v                             lib/Reusable/YO03.v
     lib/Reusable/YO04.v                             lib/Reusable/YO05.v
     lib/Reusable/YO09.v                             lib/Reusable/YO0d.v
     lib/Reusable/YO0e.v                             lib/Reusable/YO0f.v
     lib/Reusable/YO0g.v                             lib/Reusable/YO0h.v
     lib/Reusable/YO0i.v                             lib/Reusable/YO0j.v
     lib/Reusable/YO0k.v                             lib/Reusable/YO0l.v
     lib/Reusable/YO0m.v                             lib/Reusable/YO0n.v
     lib/Reusable/YO0o.v                             lib/Reusable/YO0p.v
     lib/Reusable/YO0q.v                             lib/Reusable/YO0s.v
     lib/Reusable/YO0t.v                             lib/Reusable/YO0u.v
     lib/Reusable/YO0v.v                             lib/Reusable/YO0w.v
     lib/Reusable/YO0x.v                             lib/Reusable/YO0y.v
     lib/Reusable/YO0z.v                             lib/Reusable/YO10.v
     lib/Reusable/YO11.v                             lib/Reusable/YO12.v
     lib/Reusable/YO13.v                             lib/Reusable/YO14.v
     lib/Reusable/YO15.v                             lib/Reusable/YO16.v
     lib/Reusable/YP09.v                             lib/Reusable/YP0e.v
     lib/Reusable/YP0m.v                             lib/Reusable/YZ00.v
     lib/Reusable/Z/MmapComplete.v                   lib/Reusable/Z/Placement.v

   ONE ROOT WAS REMOVED to make that true (a Theorem Labs lane 22:01Z, as for image A):
     lib/B/AsanRTInv.v      FORBIDDEN itself.  Its only use here was rt_disjoint, in C_B81d18's memset window;
                            restated below from AsanRTInv.v:12-20 over AsanRT.v's constants and lib/Lib's
                            disjoint_from.  No other conjunct of AsanRTInv is named by any body; the four
                            ctl_rt facts come from ACtlCut.ctl_rt, not from here.
   Image A's two other removals do not apply to image B: lib/B/Reusable/YP09.v was never Required by this file
   (its two names occur only in shell conjuncts section 2.1 drops), and image B's
   lib/B/Prog/reac_ctrl_identity_reply_c.v and reac_ctrl_parse_c.v are measured clean (34 / 32 files, no
   lib/AZ; image A's reach lib/AZ/LibA/AcctCore.v), so they stay Required under RCIR / RCP.  The other callee
   contract files, measured the same way: reac_ctrl_kind_name_c 18 files, bcmp_wrap_c 21, asan_memset_c 19,
   reac_ctrl_identity_fragment_c 25, lib/B/Prog/reac_ctrl_build_as_c 32, lib/Prog/reac_ctrl_build_as_c 24,
   lib/B/Spec/StrFun.v 17, lib/B/AsanRT.v 10, lib/B/AsanRTFacts.v 22 -- none reaches a forbidden file.

   ONE-LINE SWAP.  Every model name here is reached through the Module alias SM (and the Rc* aliases).  If the
   porter rules the closure must be literally SlotModel-free, lib/B/ACtlM.v restates SlotModel.v's pure
   functions and ONE Require line plus ONE alias line change here; no record is touched.

   NAMES THIS FILE TAKES FROM B.ACtlK (all four defined there, with their sources, at the commit that adds this
   file):
     B.ACtlK.ASAN_K     the shadow offset, re-exported from AsanRT.v, for ctrl's inline shadow-byte conjuncts
     B.ACtlK.a_size     ctrl's AC.a_size (lib/B/Contract.v:129): the allocator's block size for a request
                        (a_size 0 = 1), named only where a conjunct is about addressable bytes, i.e. in HB --
                        the live-block lists carry the REQUEST size, as the core's ablocks does
     B.ACtlK.ANMAX      ctrl's AC.ANMAX (lib/B/Contract.v:50), the harness's maximum input length
     B.ACtlK.EV_LLVMF   the walk's measured event need, 526, which the W5 rows use as their k bound
   The thread-pointer word and the frame header's entry word are NOT new names: they are Reusable.YG0f.as_tp B
   (the core's own symbol-bundle field, which its pre states) and Reusable.YCfn.A_LLVMF.

   MODEL VERSION (image B only, measured by check_cutp_b.py): the
   bodies name image B's v1.9.0 model, lib/B/Prog/SlotModel.v at 23a791566db (blob de18d111c37), which SlotInv.v
   at that commit is written over; every name qualified through a Module alias here is defined by its module at
   23a791566db.  The commit that re-twins this file brings that model by path (the branch had the older
   patched-image blob 5e641ff, which lacks SM.fs_n, SM.fs_body, SM.joined_byte and SM.joined_addr).

   BUILD STATE (honest): the relocated core is in this tree (lib/Reusable), and ACtlCut.v and this file are built with it (lib/dune takes every .v file; lib/B/ACtlW0.v and lib/B/ACtlAll.v Require this file);
   before it landed both were labelled stand-ins, to be typechecked the hour the core landed (zfactsbuild on FACTS ed6b6b7b0ab +
   PAU pau-libreac-v190; there was no cb base, a Theorem Labs lane 21:22Z).  Nothing here was built, committed or pushed then. *)

From Coq Require Import ZArith List Permutation.
(* LPS's machine vocabulary (word, byte, bvmap, Model, Z_to_bv, ...) comes from LPS directly, as ACtlCut.v and
   the donor's root YCfn.v do: YK11.v only Imports it, so `lib.Reusable.YK11.word` does not resolve (composition lane,
   22:37Z).  Only the shadowed names getr / mkst / seg_rom / cfg_at stay YK11 / YG0d-qualified, and lib/Lib is
   never Imported. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YCfn B.ACtlK B.ACtlCut.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Cells Step Frame.
(* the model, pure, Require only -- the ONE line lib/B/ACtlM.v would replace *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcModel Prog.RcIdentModel Prog.RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcReply Prog.RcLeaf Prog.RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcParse Prog.RcPorts Prog.RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcRec Prog.RcSynth Prog.RcBox.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_kind_name_c B.Prog.bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_memset_c B.Prog.reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.reac_ctrl_identity_reply_c B.Spec.StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.reac_ctrl_build_as_c B.Prog.reac_ctrl_build_as_c.
Import ListNotations.
Local Open Scope Z_scope.

(* The model aliases (the swap point).  SM is ctrl's pure input model; the Rc* aliases are the target's own
   record / parse / reply / fragment models, which SlotModel is written over. *)
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotModel.
Module RMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RRP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcReply.
Module RLF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLeaf.
Module RDC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcDecl.
Module RPA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RPO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.
Module RKN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcKind.
Module RCL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcClassify.
(* Image B only: three more of the target's pure models, which image B's bundles name (RcRec in C_B823d8_at; RcSynth
   and RcBox, under image B's SlotInv.v aliases RS6 / RBx, in RBE, R6X, C_B8169c and C_B816ec_at). *)
Module RRC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcRec.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module RBx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcBox.
(* The memory vocabulary ctrl's bodies name and ACtlCut.v has no counterpart for.  Qualified use only. *)
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module CEL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module STP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRTFacts.
(* Program constants, under the aliases image A's SlotInv.v uses (image B's SlotInv.v :36-52 calls the same
   image-B modules KNC / BW / SF / RIFC); BAP / BAC are image B's own aliases, for its build_as package.  Image B
   keeps the two callee contract files image A turned into Section Variables (RCIR, RCP): at 23a791566db their
   closures are clean (34 and 32 files, no lib/AZ), see CLOSURE above. *)
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Module BWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module FGA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.
Module AMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.
Module RCIR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_reply_c.
Module RCP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module SFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.

(* The core's segment list, as ACtlCut.v takes it: a notation, not a Variable, so that `world segs` is the
   pre's type and not a new one (ACtlCut.v, 22:37Z; the donor's root YB1v.v:11, the porter's name 22:45Z). *)
Local Notation segs := Reusable.YB1v.tfibsegs.

Section CtlCutP.

(* The same Section shape as ACtlCut.v (its contexts and variables, in its order). *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.   (* Record asyms is donor YG0f.v:154, not YG00 (a Theorem Labs lane, measured) *)
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

(* ACtlCut.v's vocabulary, with that file's Section arguments absorbed once.  This is the only place where
   ACtlCut's discharged arguments appear, so one edit here follows any change to its Section. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation ctlcut := ACtlCut.ctlcut.
Local Notation mkCtlCut := ACtlCut.mkCtlCut.
Local Notation own6 := ACtlCut.own6.
Local Notation own0 := ACtlCut.own0.
Local Notation c_ly := ACtlCut.c_ly.
Local Notation c_S := ACtlCut.c_S.
Local Notation c_W := ACtlCut.c_W.
Local Notation c_regs := ACtlCut.c_regs.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_p := ACtlCut.c_p.
Local Notation c_n := ACtlCut.c_n.
Local Notation c_in := ACtlCut.c_in.
Local Notation c_fpos := ACtlCut.c_fpos.
Local Notation c_sp := ACtlCut.c_sp.
Local Notation rgv := ACtlCut.rgv.
Local Notation a0v := ACtlCut.a0v.

(* rt_disjoint, RESTATED here from lib/B/AsanRTInv.v:12-20 (a Theorem Labs lane 22:01Z: AsanRTInv.v is forbidden in a port
   file, and this is its only use -- C_B81d18's memset window).  Verbatim text, over AsanRT.v's runtime-cell
   constants and lib/Lib/Frame.v's disjoint_from, both allowed; no other conjunct of AsanRTInv is named. *)
Definition rt_disjoint (W : list FRM.ivl) : Prop :=
  FRM.disjoint_from W ART.RT_LO (ART.RT_HI - ART.RT_LO) /\ FRM.disjoint_from W ART.RT_GOT_AF 8 /\
  FRM.disjoint_from W (ART.RT_AF + 60) 1 /\
  FRM.disjoint_from W ART.RT_GOT_VERB 8 /\ FRM.disjoint_from W ART.RT_VERB 4 /\
  FRM.disjoint_from W ART.RT_GOT_CF 8 /\ FRM.disjoint_from W ART.RT_CF 288 /\
  FRM.disjoint_from W (ART.RT_AF + 29) 1 /\
  FRM.disjoint_from W ART.RT_TSDI 1 /\ FRM.disjoint_from W ART.RT_TSDK 4 /\
  FRM.disjoint_from W ART.RT_PGSZ 8 /\
  FRM.disjoint_from W (ART.RT_TP - 88) 8 /\ FRM.disjoint_from W ART.RT_TSDMAIN 8 /\
  FRM.disjoint_from W ART.RT_REAL_LO (ART.RT_REAL_HI - ART.RT_REAL_LO) /\
  FRM.disjoint_from W ART.RT_IMAP 8 /\ FRM.disjoint_from W ART.RT_IMEM 8 /\
  FRM.disjoint_from W (ART.RT_AF + 24) 4 /\ FRM.disjoint_from W ART.RT_MUG 8 /\
  FRM.disjoint_from W ART.RT_AGLOB ART.RT_AGLOB_LEN /\
  FRM.disjoint_from W (ART.RT_TP - 8) 24 /\ FRM.disjoint_from W (ART.RT_TP + 40) 8.

(* The loop index.  ACtlCut.v's idx is a list Z: [] for a straight cut, [b] for the round trip, [j] for the
   frame loop, [j; i] for the three row cuts.  ctrl's bodies take b / j / i as nat and t as Z. *)
Definition ixn (k : nat) (idx : list Z) : nat := Z.to_nat (nth k idx 0).
Definition ixz (k : nat) (idx : list Z) : Z := nth k idx 0.

(* ---------------------------------------------------------------------------------------------------------
   1. The body predicates ctrl's cuts share, transcribed from SlotInv.v at 23a791566db with their names kept, in
   SlotInv.v's own order (its line order, which is its dependency order).  Among them are ctrl's own readers
   (q64 / u32 / u16 / b8 :268-271, Sfr :282, spill :834-835).  Each carries its source line; the conjuncts dropped
   from each are listed in the transcription report, bundle by bundle. *)

(* FRAME_BYTES, SlotInv.v:59 *)
Definition FRAME_BYTES : Z :=
  3136.

(* FRAME_SHADOW, SlotInv.v:60 *)
Definition FRAME_SHADOW : Z :=
  FRAME_BYTES / 8.

(* q64, SlotInv.v:268 *)
Definition q64 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a (MEM.le8 (Z_to_bv 64 v)).

(* u32, SlotInv.v:269 *)
Definition u32 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a (MEM.le4 (Z_to_bv 64 v)).

(* u16, SlotInv.v:270 *)
Definition u16 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a (MEM.le2 (Z_to_bv 64 v)).

(* b8, SlotInv.v:271 *)
Definition b8 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a [Z_to_bv 8 v].

(* saved_bytes, SlotInv.v:275 *)
Definition saved_bytes (cx : ctlcx) : list byte :=
  MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 27) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 26) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 25) ++
  MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 24) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 23) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 22) ++
  MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 21) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 20) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 19) ++
  MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 18) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 9) ++ MEM.le8 (lib.Reusable.YK11.getr (c_regs cx) 8) ++ MEM.le8 (Z_to_bv 64 Reusable.YCfn.RA_LLVMF).

(* Sfr, SlotInv.v:282 *)
Definition Sfr (fr : Z) : Z :=
  ART.shadow_addr fr.

(* HB, SlotInv.v:811 *)
Definition HB (mem : word -> option byte) (phi len : Z) : Prop :=
  phi <> 0 /\ ART.addressable mem phi (B.ACtlK.a_size len).

(* rnb, SlotInv.v:812 *)
Definition rnb (cx : ctlcx) (b : nat) : Z :=
  SM.rt_n (c_in cx) (Z.of_nat b).

(* decl_slot, SlotInv.v:815 *)
Definition decl_slot (fr : Z) : Z :=
  fr + 2560.

(* spill, SlotInv.v:834 *)
Definition spill (regs : bvmap 5 word) (m : word -> option byte) (off v : Z) : Prop :=
  exists A, rgv regs 9 A /\ q64 m (A + off) v.

(* CUR, SlotInv.v:838 *)
Definition CUR (cx : ctlcx) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= c_n cx /\ rgv regs 23 (c_p cx + c) /\ rgv regs 25 (c_n cx - c).

(* OURb, SlotInv.v:840 *)
Definition OURb (cx : ctlcx) (fr : Z) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2624) (SM.OUR (c_in cx)).

(* IDBr, SlotInv.v:842 *)
Definition IDBr (cx : ctlcx) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2176) idb.

(* FGBr, SlotInv.v:844 *)
Definition FGBr (cx : ctlcx) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2256) st.

(* IDBe, SlotInv.v:846 *)
Definition IDBe (cx : ctlcx) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2688) idb.

(* FGBe, SlotInv.v:848 *)
Definition FGBe (cx : ctlcx) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2768) st.

(* RB, SlotInv.v:853 *)
Definition RB (cx : ctlcx) (fr : Z) (b : nat) (idb fgb : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b <= 6)%nat /\ CUR cx 7 regs /\ OURb cx fr m /\ rgv regs 22 (Z.of_nat b) /\ IDBr cx fr idb m /\ FGBr cx fr fgb m.

(* RS, SlotInv.v:855 *)
Definition RS (cx : ctlcx) (fr : Z) (b : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) regs m.

(* RFb, SlotInv.v:858 *)
Definition RFb (cx : ctlcx) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB cx fr b idb fgb regs m /\ rnb cx b <> 0 /\ rgv regs 20 phi /\ MEM.bytes_at segs m phi (SM.rt_F (c_in cx) (Z.of_nat b)).

(* RFx, SlotInv.v:861 *)
Definition RFx (cx : ctlcx) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFb cx fr b idb fgb phi regs m /\ rgv regs 18 (rnb cx b).

(* RF, SlotInv.v:863 *)
Definition RF (cx : ctlcx) (fr : Z) (b : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFx cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m.

(* IDb, SlotInv.v:869 *)
Definition IDb (cx : ctlcx) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  IDBe cx fr idb m /\ RIM.id_ok idb.

(* FGb, SlotInv.v:871 *)
Definition FGb (cx : ctlcx) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  FGBe cx fr st m /\ SM.frag_ok st.

(* FSb, SlotInv.v:882 *)
Definition FSb (cx : ctlcx) (fr : Z) (s : SM.fstate) (st : list byte) (regs : bvmap 5 word) (m : word -> option byte)
    : Prop :=
  u32 m (fr + 2880) (SM.fs_have s) /\ b8 m (fr + 2884) (SM.fs_n s) /\
  MEM.bytes_at segs m (fr + 2885) (SM.fs_body s) /\ ART.addressable m (fr + 2880) 40 /\ SM.FI st s.

(* IDj, SlotInv.v:886 *)
Definition IDj (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  IDb cx fr (SM.t_ID (c_in cx) j) m.

(* FGj, SlotInv.v:887 *)
Definition FGj (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FGb cx fr (SM.t_FG (c_in cx) j) m.

(* FSj, SlotInv.v:888 *)
Definition FSj (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FSb cx fr (SM.fst_at (c_in cx) j) (SM.t_FG (c_in cx) j) regs m.

(* IFS, SlotInv.v:890 *)
Definition IFS (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj cx fr j m /\ FGj cx fr j m /\ FSj cx fr j regs m.

(* FREC, SlotInv.v:906 *)
Definition FREC (cx : ctlcx) (fr : Z) (idb st : list byte) (m : word -> option byte) : Prop :=
  IDb cx fr idb m /\ FGb cx fr st m.

(* REC0, SlotInv.v:908 *)
Definition REC0 (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC cx fr (SM.t_ID (c_in cx) j) (SM.t_FG (c_in cx) j) m.

(* RECR, SlotInv.v:910 *)
Definition RECR (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC cx fr (SM.t_IDr (c_in cx) j) (SM.t_FG (c_in cx) j) m.

(* RECF, SlotInv.v:912 *)
Definition RECF (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC cx fr (SM.t_IDr (c_in cx) j) (SM.t_FG (c_in cx) (S j)) m.

(* RECS, SlotInv.v:914 *)
Definition RECS (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FREC cx fr (SM.t_ID (c_in cx) (S j)) (SM.t_FG (c_in cx) (S j)) m.

(* fragb, SlotInv.v:918 *)
Definition fragb (fr : Z) : Z :=
  fr + 2768.

(* RAD, SlotInv.v:928 *)
Definition RAD (fr : Z) (m : word -> option byte) : Prop :=
  ART.addressable m (fr + 2688) 38 /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2880) 40.

(* KNT, SlotInv.v:940 *)
Definition KNT (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m KNA.KIND_NAME KNA.kind_name_bytes /\ ART.addressable m KNA.KIND_NAME 112.

(* FLI, SlotInv.v:970 *)
Definition FLI (cx : ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 27 (-8) /\ spill regs m 168 (fr + 2880) /\
  spill regs m 96 (fr + 180) /\ spill regs m 112 (fr + 186) /\
  spill regs m 120 (fragb fr + 15) /\ spill regs m 128 (fragb fr + 19) /\
  spill regs m 136 (fr + 160) /\ spill regs m 144 (fr + 452) /\ spill regs m 152 (fr + 64) /\
  spill regs m 280 (fr + 176) /\ spill regs m 160 (fr + 32) /\ spill regs m 176 (fr + 2688) /\
  spill regs m 192 (fr + 528) /\ spill regs m 200 (fr + 336) /\ spill regs m 216 (fr + 448) /\
  spill regs m 208 (fragb fr) /\ spill regs m 104 (fr + 128) /\ spill regs m 256 (fragb fr + 8) /\
  spill regs m 264 (fr + 2624) /\ spill regs m 288 (fr + 256) /\ spill regs m 296 (fr + 304) /\
  spill regs m 304 (fr + 272) /\
  ART.addressable m (fr + 2624) 6 /\ FRM.stk segs m fr (fr + FRAME_BYTES) /\ RAD fr m /\ KNT m /\
  spill regs m 168 (fr + 2880) /\ spill regs m 88 (fr + 2885).

(* PRA, SlotInv.v:1008 *)
Definition PRA (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 136 (fr + 160) /\ spill regs m 280 (fr + 176) /\ spill regs m 168 (fr + 2880) /\
  spill regs m 192 (fr + 528) /\ spill regs m 200 (fr + 336) /\ spill regs m 216 (fr + 448) /\
  spill regs m 104 (fr + 128) /\ spill regs m 288 (fr + 256) /\ spill regs m 296 (fr + 304) /\
  spill regs m 304 (fr + 272) /\ spill regs m 168 (fr + 2880).

(* PRO, SlotInv.v:1013 *)
Definition PRO (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 264 (fr + 2624) /\
  ART.addressable m (fr + 2624) 6 /\ spill regs m 160 (fr + 32).

(* LK, SlotInv.v:1018 *)
Definition LK (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ spill regs m 240 (Z.of_nat j) /\ OURb cx fr m /\ FLI cx fr regs m.

(* LI, SlotInv.v:1022 *)
Definition LI (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rgv regs 13 (Z.of_nat j) /\ OURb cx fr m /\
  CUR cx (SM.t_c (c_in cx) j) regs /\ 1 <= SM.t_left (c_in cx) j /\ IFS cx fr j regs m /\ FLI cx fr regs m.

(* FC, SlotInv.v:1027 *)
Definition FC (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 232 (SM.t_left (c_in cx) j - SM.t_h (c_in cx) j) /\ rgv regs 21 (c_p cx + SM.t_body (c_in cx) j) /\
  rgv regs 20 (SM.t_len (c_in cx) j).

(* FTURN, SlotInv.v:1039 *)
Definition FTURN (cx : ctlcx) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 224 (c_p cx + SM.t_body (c_in cx) j) /\ spill regs m 232 (SM.t_left (c_in cx) j - SM.t_h (c_in cx) j) /\
  MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\ Z.of_nat (length (SM.t_phi (c_in cx) j)) <= SM.t_len (c_in cx) j.

(* pBb, SlotInv.v:1098 *)
Definition pBb (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 176) (SM.t_B (c_in cx) j).

(* PORTS, SlotInv.v:1104 *)
Definition PORTS (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  (SM.t_rp (c_in cx) j = 0 ->
     u32 m (fr + 128) (4 * RLF.n_in (SM.t_pbs (c_in cx) j)) /\
     u32 m (fr + 132) (4 * RLF.n_out (SM.t_pbs (c_in cx) j)) /\
     u32 m (fr + 136) (16 * RLF.bt (SM.t_pbs (c_in cx) j) 7)) /\
  (SM.t_rp (c_in cx) j <> 0 -> u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7)).

(* FIRSTb, SlotInv.v:1110 *)
Definition FIRSTb (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  b8 m (fr + 160) (SM.t_first (c_in cx) j).

(* FLV, SlotInv.v:1123 *)
Definition FLV (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 120 (fragb fr + 15) /\ spill regs m 128 (fragb fr + 19) /\ spill regs m 256 (fragb fr + 8) /\
  spill regs m 304 (fr + 272) /\ spill regs m 296 (fr + 304) /\
  (SM.t_rf (c_in cx) j = 1 ->
     q64 m (fr + 272) (fragb fr + 19) /\
     q64 m (fr + 304) (SM.f_pll (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j))).

(* FLVsp, SlotInv.v:1133 *)
Definition FLVsp (A fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 9 A /\ q64 m (A + 120) (fragb fr + 15) /\ q64 m (A + 128) (fragb fr + 19) /\
  q64 m (A + 256) (fragb fr + 8) /\ q64 m (A + 304) (fr + 272) /\ q64 m (A + 296) (fr + 304).

(* flen, SlotInv.v:1138 *)
Definition flen (cx : ctlcx) (j : nat) : Z :=
  SM.t_len (c_in cx) j.

(* frcl, SlotInv.v:1143 *)
Definition frcl (cx : ctlcx) (j : nat) (fr phi : Z) : RFR.fg_case :=
  RFR.fg_class (fragb fr) phi (fr + 256) (fr + 272) (fr + 304) (flen cx j) (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j).

(* frrec, SlotInv.v:1145 *)
Definition frrec (cx : ctlcx) (j : nat) (fr phi : Z) : list byte :=
  SM.fg_next (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j) (frcl cx j fr phi).

(* FM, SlotInv.v:1158 *)
Definition FM (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 22 1 /\
  rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  spill regs m 312 (if SM.t_big (c_in cx) j then phi + 18 else 0).

(* FTL, SlotInv.v:1169 *)
Definition FTL (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 21 (fr + 128) /\ spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  spill regs m 272 (SM.t_k (c_in cx) j) /\ rgv regs 24 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  spill regs m 312 (if SM.t_big (c_in cx) j then phi + 18 else 0).

(* FTK, SlotInv.v:1179 *)
Definition FTK (cx : ctlcx) (j : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ rgv regs 22 1 /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
  spill regs m 272 (SM.t_k (c_in cx) j) /\ rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)).

(* rec_inv, SlotInv.v:1190 *)
Definition rec_inv (cx : ctlcx) (j : nat) (phi A kp : Z) (m : word -> option byte) : Prop :=
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ (50 <= flen cx j)%Z /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
  (forall a, phi <= a < phi + 50 -> ART.app_mem a) /\
  q64 m (A + 312) (phi + 18) /\
  MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
  MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
  (exists (field16 v14 v15 v16 v17 : Z),
     q64 m (A + 248) (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\ u16 m (kp + 20) field16 /\ (kp + 22 <= 2 ^ 64) /\ 0 <= kp /\
     b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
     0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
     b8 m (Z.shiftr (phi + 14) 3 + B.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + B.ACtlK.ASAN_K) 0 /\
     b8 m (Z.shiftr (phi + 16) 3 + B.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + B.ACtlK.ASAN_K) 0 /\
     field16 = v14 + 256 * v15 /\
     (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if SM.t_k (c_in cx) j =? 1 then 1 else 0)).

(* FRB, SlotInv.v:1223 *)
Definition FRB (cx : ctlcx) (j : nat) (fr phi A kp : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall a, fr + 2880 <= a < fr + 2920 -> ART.app_mem a) /\
  (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
     (SM.t_8819 (c_in cx) j = true -> w272 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w272 = 0)) /\
  (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
  (kp + 22 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= kp) /\
  (kp + 22 <= fr + 2688 \/ fr + 2688 + 38 <= kp + 20) /\
  (50 <= flen cx j ->
     (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
     (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi)) /\
  (SM.t_8819 (c_in cx) j = true ->
     rec_inv cx j phi A kp m /\
     (exists (L : Z) (ls rs : list byte),
        q64 m (A + 112) L /\ MEM.bytes_at segs m L ls /\ length ls = 6%nat /\
        MEM.bytes_at segs m phi rs /\ length rs = 6%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
        ART.addressable m L 6 /\ ART.app_mem (L + 6) /\ ART.app_mem (L + 7) /\
        (L + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L) /\
        (L + 6 <= fr + 2880 \/ fr + 2920 <= L) /\
        (L + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L)) /\
     (exists (L2 : Z) (ls2 rs2 : list byte),
        q64 m (A + 96) L2 /\ MEM.bytes_at segs m L2 ls2 /\ length ls2 = 6%nat /\
        MEM.bytes_at segs m (phi + 6) rs2 /\ length rs2 = 6%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
        ART.addressable m L2 6 /\ ART.app_mem (L2 + 6) /\ ART.app_mem (L2 + 7) /\
        (L2 + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L2) /\
        (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2) /\
        (L2 + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L2))).

(* FRBA, SlotInv.v:1251 *)
Definition FRBA (cx : ctlcx) (j : nat) (fr phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ FRB cx j fr phi A (fr + 176) regs m.

(* FRX, SlotInv.v:1264 *)
Definition FRX (cx : ctlcx) (j : nat) (fr phi : Z) (m : word -> option byte) : Prop :=
  (50 <= flen cx j ->
     MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ ART.addressable m phi 50 /\ (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi)) /\
  MEM.bytes_at segs m (fragb fr) (frrec cx j fr phi) /\ ART.addressable m (fragb fr) 72 /\
  (exists idb, length idb = 38%nat /\ STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\
  ART.addressable m (fr + 2688) 38 /\
  (SM.t_rf (c_in cx) j = 1 ->
     0 <= SM.fs_have (SM.fst_at (c_in cx) j) < 2 ^ 64 /\ SM.fs_have (SM.fst_at (c_in cx) j) <> 0 /\
     0 <= SM.fs_n (SM.fst_at (c_in cx) j) < 256 /\
     0 <= SM.joined_byte (SM.fst_at (c_in cx) j) (SM.t_g (c_in cx) j) 9 < 256 /\
     0 <= SM.joined_byte (SM.fst_at (c_in cx) j) (SM.t_g (c_in cx) j) 10 < 256 /\
     (exists AD, u16 m (fr + 256) AD /\ 0 <= AD < 65536 /\
        AD = SM.joined_addr (SM.fst_at (c_in cx) j) (SM.t_g (c_in cx) j))).

(* FPS, SlotInv.v:1292 *)
Definition FPS (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  pBb cx fr j m /\ ART.addressable m (fr + 176) 36.

(* F272, SlotInv.v:1298 *)
Definition F272 (cx : ctlcx) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 272 (SM.b2z (SM.t_8819 (c_in cx) j)).

(* RCA, SlotInv.v:1303 *)
Definition RCA (fr : Z) (m : word -> option byte) : Prop :=
  ART.addressable m (fr + 256) 2 /\ ART.addressable m (fr + 272) 8 /\ ART.addressable m (fr + 304) 8.

(* FS9, SlotInv.v:1309 *)
Definition FS9 (cx : ctlcx) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 248 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)).

(* f10_K, SlotInv.v:1320 *)
Definition f10_K (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
  (exists A, FLVsp A fr regs m /\ 0 <= A < 2 ^ 64 /\
     q64 m (A + 288) (fr + 256) /\ q64 m (A + 176) (fr + 2688) /\
     q64 m (A + 200) (fr + 336) /\ q64 m (A + 208) (fr + 2768) /\
     q64 m (A + 248) (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
     q64 m (A + 312) (if SM.t_big (c_in cx) j then phi + 18 else 0)) /\
  rgv regs 18 phi /\ rgv regs 20 (flen cx j) /\ rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  rgv regs 24 (SM.t_k (c_in cx) j) /\ spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ rgv regs 22 1 /\
  RRP.reply_args phi (fr + 256) (fr + 272) (fr + 304) = true.

(* f10_RPost, SlotInv.v:1333 *)
Definition f10_RPost (phi fr : Z) (G : list byte) (m : word -> option byte) : Prop :=
  STP.rw_cells segs m (fr + 256) [CEL.CB 2 (RRP.reply_addr G)] /\
  STP.rw_cells segs m (fr + 272) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (phi + 38)))] /\
  STP.rw_cells segs m (fr + 304) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (RRP.ir_s G - 13)))].

(* PT32, SlotInv.v:1340 *)
Definition PT32 (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 18 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 20 (SM.t_len (c_in cx) j) /\
  spill regs m 152 (fr + 64) /\ spill regs m 312 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\
  MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\ (Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
  spill regs m 160 (fr + 32) /\
  FRM.stk segs m fr (fr + FRAME_BYTES).

(* PTL, SlotInv.v:1350 *)
Definition PTL (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  SM.t_rowsel (c_in cx) j = true /\
  rgv regs 18 phi /\ rgv regs 20 (SM.t_len (c_in cx) j) /\ spill regs m 152 (fr + 64) /\ spill regs m 312 (phi + 18) /\
  MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\ (Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
  spill regs m 160 (fr + 32) /\ q64 m (fr + 32) 11 /\
  FRM.stk segs m fr (fr + FRAME_BYTES).

(* RL, SlotInv.v:1356 *)
Definition RL (cx : ctlcx) (j i : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (i <= 10)%nat /\ rgv regs 23 (SM.CAT + SM.CAT_ROW * Z.of_nat i) /\ rgv regs 25 (Z.of_nat i) /\ rgv regs 21 SM.CAT /\
  rgv regs 10 (SM.CAT_ROW * Z.of_nat i) /\ rgv regs 11 0 /\ rgv regs 12 0 /\
  (forall i', (i' < i)%nat -> SM.t_blk (c_in cx) j <> SM.decl_i (Z.of_nat i')) /\ PTL cx j phi fr regs m.

(* RLc, SlotInv.v:1365 *)
Definition RLc (cx : ctlcx) (j i : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (i <= 10)%nat /\ rgv regs 23 (SM.CAT + SM.CAT_ROW * Z.of_nat i) /\ rgv regs 24 (SM.CAT + SM.CAT_ROW * Z.of_nat i) /\
  rgv regs 25 (Z.of_nat i) /\ rgv regs 21 SM.CAT /\ rgv regs 22 (fr + 64) /\
  (forall i', (i' < i)%nat -> SM.t_blk (c_in cx) j <> SM.decl_i (Z.of_nat i')) /\ PTL cx j phi fr regs m.

(* F27K, SlotInv.v:1373 *)
Definition F27K (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK cx fr j regs m /\ rgv regs 18 phi /\ rgv regs 27 (-8) /\
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\
  MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
  spill regs m 312 (phi + 18) /\ spill regs m 272 (SM.t_k (c_in cx) j) /\
  rgv regs 24 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  spill regs m 104 (fr + 128) /\ spill regs m 136 (fr + 160).

(* LOOPB, SlotInv.v:1492 *)
Definition LOOPB (cx : ctlcx) (t fr sel : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  c_n cx < 2 ^ 26 /\ 0 <= t <= 5 /\ rgv regs 24 sel /\ rgv regs 25 fr /\
    spill regs m 144 (fr + 2176) /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ rgv regs 20 (fr + 2656) /\
    rgv regs 10 (6 - t) /\ rgv regs 11 1 /\ rgv regs 12 (fr + 2624 + t) /\ rgv regs 17 (fr + 64) /\
    rgv regs 18 (c_n cx - Z.min t (c_n cx)) /\ rgv regs 22 (c_p cx + Z.min t (c_n cx)) /\ rgv regs 27 (Sfr fr + 68) /\
    spill regs m 56 (fr + 3040) /\ spill regs m 184 (fr + 2368) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ ART.addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 64 (fr + 3056) /\
    MEM.bytes_at segs m (c_p cx) (c_in cx) /\
    (0 < c_n cx -> ART.addressable m (c_p cx) (c_n cx)) /\
    (exists junk, length junk = Z.to_nat (6 - t) /\
       MEM.bytes_at segs m (fr + 2624) (firstn (Z.to_nat t) (SM.OUR (c_in cx)) ++ junk)) /\
    rgv regs 16 (fr + 32).

(* OUTA, SlotInv.v:1574 *)
Definition OUTA (fr : Z) (m : word -> option byte) : Prop :=
  ART.addressable m (fr + 544) 1492.

(* RBE, SlotInv.v:1616 *)
Definition RBE (cx : ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 128 0xe38f0000 /\ spill regs m 312 (fr + 544) /\ spill regs m 272 (SM.mrow (c_in cx)) /\
  spill regs m 264 (fr + 2624) /\ spill regs m 256 0x21140 /\ spill regs m 248 0x1234 /\
  spill regs m 56 (fr + 3040) /\ spill regs m 184 (fr + 2368) /\
  spill regs m 144 (fr + 2176) /\ spill regs m 8 (Sfr fr + 68) /\
  spill regs m 32 0 /\ spill regs m 24 (SM.mrow (c_in cx) + 16) /\ spill regs m 16 (SM.mrow (c_in cx) + 20) /\
  spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
  spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
  spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
  OUTA fr m /\ ART.addressable m (fr + 2176) 38 /\
  (RS6.has (SM.rt_mb (c_in cx)) <> 0 /\ RS6.rname (SM.rt_mb (c_in cx)) <> 0 ->
     RBx.name_ok (SM.rt_nb (c_in cx)) /\ MEM.bytes_at segs m (RS6.rname (SM.rt_mb (c_in cx))) (SM.rt_nb (c_in cx)) /\
     ART.addressable m (RS6.rname (SM.rt_mb (c_in cx))) (Z.of_nat (length (SM.rt_nb (c_in cx)))) /\
     0 < RS6.rname (SM.rt_mb (c_in cx))) /\
  ART.addressable m (fr + 2624) 6 /\ MEM.bytes_at segs m (BAC.BA_FR + 72) BAP.ba_tbl /\ MEM.bytes_at segs m SM.BOXA SM.box6 /\
  MEM.bytes_at segs m (SM.mrow (c_in cx)) (SM.rt_mb (c_in cx)) /\
  PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 112 (fr + 2256) /\ ART.addressable m (fr + 2256) 72 /\
  spill regs m 160 (fr + 32).

(* R6X, SlotInv.v:1651 *)
Definition R6X (cx : ctlcx) (b : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  ART.addressable m (fr + 544) 1492 /\
  ART.addressable m (fr + 2624) 6 /\
  MEM.bytes_at segs m (BAC.BA_FR + 72) BAP.ba_tbl /\
  MEM.bytes_at segs m SM.BOXA SM.box6 /\
  MEM.bytes_at segs m (SM.mrow (c_in cx)) (SM.rt_mb (c_in cx)) /\
  ((Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ RS6.has (SM.rt_mb (c_in cx)) <> 0 /\ RS6.rname (SM.rt_mb (c_in cx)) <> 0 ->
     RBx.name_ok (SM.rt_nb (c_in cx)) /\ MEM.bytes_at segs m (RS6.rname (SM.rt_mb (c_in cx))) (SM.rt_nb (c_in cx)) /\
     ART.addressable m (RS6.rname (SM.rt_mb (c_in cx))) (Z.of_nat (length (SM.rt_nb (c_in cx)))) /\
     0 < RS6.rname (SM.rt_mb (c_in cx))).

(* rsum, SlotInv.v:1872 *)
Definition rsum (cx : ctlcx) (b i : nat) : Z :=
  RMO.psum (skipn 18 (SM.rt_g (c_in cx) (Z.of_nat b))) i.

(* PL0, SlotInv.v:1990 *)
Definition PL0 (cx : ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  CUR cx (SM.c0 (c_in cx)) regs /\ IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ RAD fr m /\
  spill regs m 176 (fr + 2688) /\ spill regs m 208 (fragb fr) /\ FSj cx fr 0 regs m.

(* XC, SlotInv.v:2030 *)
Definition XC (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 24 (fr + 3040) /\ ART.addressable m (fr + 3040) 1.

(* f1_IN, SlotInv.v:2208 *)
Definition f1_IN (cx : ctlcx) (m : word -> option byte) : Prop :=
  ART.addressable m (c_p cx) (c_n cx) /\
  MEM.bytes_at segs m (c_p cx) (c_in cx).

(* F23GAP, SlotInv.v:2880 *)
Definition F23GAP (cx : ctlcx) (j : nat) (phi : Z) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
  (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)).

(* F28GAP, SlotInv.v:2951 *)
Definition F28GAP (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  F27K cx j phi fr regs m /\
  SM.t_rp (c_in cx) j = 0 /\ rgv regs 23 (SM.t_unk (c_in cx) j) /\
  PORTS cx fr j m /\ FIRSTb cx fr j m /\
  rgv regs 10 (phi + 26) /\ rgv regs 14 (phi + 26) /\ rgv regs 16 (-8 - (phi + 18)) /\ rgv regs 17 12 /\
  rgv regs 11 0 /\ rgv regs 12 0 /\ rgv regs 13 0 /\ rgv regs 15 0 /\ rgv regs 28 12.

(* ---------------------------------------------------------------------------------------------------------
   1b. THE CARRIED PART OF ctrl's SHELLS.  ACtlCut.v's shell states the journal, the owned frames, the pc, the
   event bound and ctl_rt; the translation's section 2.1 marks three rows of ctrl's FRA / FRAH / PREF CARRY,
   i.e. they cross into the body unchanged, and every other row RESTATE or DROP.  The CARRY rows, transcribed
   here once and conjoined to every cut body (which shell per the row's shell column):
     FRA :337, :339-344  the sp / gp / tp / s0 / s1 / s3 / s10 pins, fr mod 32, the spill
                         base A with A mod 32, A <= S, sp <= A, fr + FRAME_BYTES <= A, A + 448 <= S,
                         S - 4096 < sp, S < APPMEM_END, and the spills [A+336] / [A+48] / [A+40]
     FRA :350-351        the frame header words and the 392 frame shadow bytes
     FRA :353            the saved caller registers at [S - 104, S)
   The last two are what a cgif-form callee's achain obligation reads (a Theorem Labs lane's reply spec, via a Theorem Labs lane
   21:44Z).  TWO conjuncts of that CARRY range are NOT here (a Theorem Labs lane 23:05Z): ctrl's `(s5 = 0 \/ s5 = fr)` :342 /
   `(sel = 0 \/ sel = fr)` :459, because the shell passes sel = fr and the class-full arm is discharged at the
   fake-stack call; and `fr = frame_addr ly 6 fpos` in any FSREC-derived form, because ACtlCut.v's ctl_from now states the frame law
   itself (`forall cid pos, In (cid, pos) (cut_own X cx) -> fr = Reusable.YG0f.frame_addr (c_ly cx) cid pos`).  NOT transcribed, because section 2.1 marks them RESTATE or DROP and ACtlCut.v's shell or the
   core's pre states them: AsanRTInv.RT :333, aa_AH :334, ro_agree / sink_none / m_halted :335, G_img_c :336,
   aa_stklo :338, the real / side frame-location disjunction :345-349, stk :352, errno writable :354,
   frame_AG :355, the slot window minus the frame :356, aa_stkhi and the entry bytes above S :357-360, the hb
   length and live-bytes bounds :361, the input facts :362 (image B only: image A carries them in PRO per
   cut), and the whole of ENT :371-424 (its only CARRY-looking row, :375-378, is RESTATE: the core's pre gives
   aspZ (c_regs cx) = c_sp cx and the tp word).

   ctrl's g_S is the ENTRY sp, so the field map's g_S -> c_sp cx is right here: c_sp cx is
   Reusable.YG0d.spZ (c_regs cx), the entry registers' sp, never the cut's own sp (which stays the
   existential sp below, pinned to register 2).

   ONE NAME THIS NEEDS FROM ACtlK: the thread-pointer word that ctrl writes AC.as_tp AC.ASYMS (:339 / :456 /
   PREF :1397).  Contract.v is outside the port's closure, so it is Reusable.YG0f.as_tp B here; the frame-header entry
   word AF.ENTRY (:350 / :467) is the core's own Reusable.YCfn.A_LLVMF, the function's entry address. *)
Definition FRAC (cx : ctlcx) (fr sel : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists A sp,
    lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\
    Reusable.YG0d.spZ regs = sp /\
    lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) /\
    rgv regs 8 (c_sp cx) /\ rgv regs 9 A /\
    lib.Reusable.YK11.getr regs 3 = lib.Reusable.YK11.getr (c_regs cx) 3 /\
    rgv regs 19 (Sfr fr) /\ rgv regs 26 B.ACtlK.ASAN_K /\
    fr mod 32 = 0 /\ A mod 32 = 0 /\ A <= c_sp cx /\ sp <= A /\
    fr + FRAME_BYTES <= A /\ A + 448 <= c_sp cx /\ c_sp cx - 4096 < sp /\ c_sp cx <= ART.APPMEM_END /\
    q64 m (A + 336) fr /\ q64 m (A + 48) sel /\ q64 m (A + 40) fr /\
    q64 m fr 0x41b58ab3 /\ q64 m (fr + 16) Reusable.YCfn.A_LLVMF /\
    (exists sh, MEM.bytes_at segs m (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx) /\
    q64 m (fr + 4088) (Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx)).

(* FRAH's CARRY part (SlotInv.v:454-470): FRA's, with the header word a parameter (FRAS 0x41b58ab3 :482,
   FRAR 0x45e0360e :485) and without the two spills [A+48] / [A+40], which the early edge 0x81450 never
   writes (:439-446). *)
Definition FRAHC (cx : ctlcx) (fr sel hdr : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists A sp,
    lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\
    Reusable.YG0d.spZ regs = sp /\
    lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) /\
    rgv regs 8 (c_sp cx) /\ rgv regs 9 A /\
    lib.Reusable.YK11.getr regs 3 = lib.Reusable.YK11.getr (c_regs cx) 3 /\
    rgv regs 19 (Sfr fr) /\ rgv regs 26 B.ACtlK.ASAN_K /\
    fr mod 32 = 0 /\ A mod 32 = 0 /\ A <= c_sp cx /\ sp <= A /\
    fr + FRAME_BYTES <= A /\ A + 448 <= c_sp cx /\ c_sp cx - 4096 < sp /\ c_sp cx <= ART.APPMEM_END /\
    q64 m (A + 336) fr /\
    q64 m fr hdr /\ q64 m (fr + 16) Reusable.YCfn.A_LLVMF /\
    (exists sh, MEM.bytes_at segs m (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx) /\
    q64 m (fr + 4088) (Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx)).

(* FAKE-FRAME TRAILER WORD (added 04:58Z by a Theorem Labs lane, the shell's one writer; found by a Theorem Labs lane): the last
   conjunct of FRAC and FRAHC.  The class-6 frame's last word, at fr + fs_frame_bytes 6 - 8 = fr + 4088, holds the
   frame's flag address.  The core's frame allocator post gives it (YG0d.v:296; aj_stack_malloc_at, YCbq.v:1764) at
   0x8108c, and the release at 0x82f48 needs it (Reusable.StackFreeDef.astack_free_realizes, StackFreeDef.v:25;
   aj_stack_free_at).  Neither AR nor ajournal carries it for the walk's OWN frame, so every own6 body carries it,
   in raw form like the other frame words; the program writes only [fr, fr + FRAME_BYTES) of the frame. *)

(* PREF's CARRY part (SlotInv.v:1392-1412), for the two pre-frame cuts B81090 and B810c4: the same pins without
   the frame (no fr, no s3, no header, no frame shadow), with PREF's own spill-base window S - 464 <= A and
   its input bound.  PREF's A and sp are ctrl's parameters; they are existential here, pinned by register 2
   and register 9 exactly as the FRA form pins them. *)
Definition PREFC (cx : ctlcx) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists A sp,
    lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\
    Reusable.YG0d.spZ regs = sp /\
    lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) /\
    rgv regs 8 (c_sp cx) /\ rgv regs 9 A /\
    lib.Reusable.YK11.getr regs 3 = lib.Reusable.YK11.getr (c_regs cx) 3 /\ rgv regs 26 B.ACtlK.ASAN_K /\
    A mod 32 = 0 /\ A <= c_sp cx /\ c_sp cx - 464 <= A /\ sp <= A /\ A + 448 <= c_sp cx /\
    c_sp cx - 4096 < sp /\ c_sp cx <= ART.APPMEM_END /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx) /\
    c_n cx <= B.ACtlK.ANMAX.

(* ---------------------------------------------------------------------------------------------------------
   2. The span shell of the frame loop, FCUTP (SlotInv.v:2263), with its CUTST wrapper dropped and its live list
   stated as the body's own Permutation of bl.  FCUT (:2268) is FCUTP with a body that ignores phi, so its cuts
   pass (fun _ fr regs m => ...).  Fifteen FCUTP cuts and three FCUT cuts are written through it, exactly as
   ctrl writes them.

   THE LIVE-LIST ENTRY IS THE REQUEST SIZE (a Theorem Labs lane 21:52Z, settling the disagreement this lane reported): the
   core's ablocks records (res, n) with n the REQUEST (amalloc04_rule's post appends it, donor YC5d.v:67-74),
   while ctrl's `hb1 phi (AC.a_size (flen g j))` is a Theorem Labs lane's aa_AH convention, which the translation section of llvmf-B-walk-plan.md section 2.1 (a working note, not in this delivery) RESTATES.  So
   every live entry here is `(phi, flen cx j)` for the frame loop and `(phi, rnb cx b)` for the round trip.
   ctrl's a_size survives only where a body conjunct is about addressable BYTES, i.e. inside HB, verbatim. *)
Definition fcutp_body (cx : ctlcx) (j : nat) (bl : list (Z * Z)) (fr : Z)
    (regs : bvmap 5 word)
    (m : word -> option byte)
    (P : Z -> Z -> bvmap 5 word ->
         (word -> option byte) -> Prop) : Prop :=
  exists phi,
    Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
    c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\
    rgv regs 18 phi /\ rgv regs 20 (flen cx j) /\ FTURN cx j phi regs m /\ P phi fr regs m.

(* ---------------------------------------------------------------------------------------------------------
   3. The 91 cuts, in the address order of the cut map, one record per row of
   cut-table-B.tsv (a working note, not in this delivery).  Each record's comment gives the row's cut
   name, its SlotInv.v definition and line at 23a791566db, ctrl's shell, the pc, the index shape, the event
   bound, the frame list and the W piece, plus the table's superseded note where it has one.

   EVERY CUT FROM A4's FRAME ALLOCATION TO ITS RELEASE OWNS THE CLASS-6 FAKE FRAME (own6).  The class-full
   arm, where __asan_stack_malloc_6 returns 0 and the frame would be the real stack, is DISCHARGED by the
   model law at the fake-stack call, not walked: astack_malloc_realizes has only the frame_addr outcome
   (YG0d.v:284-299) and stack_malloc_progress rules the null result out (YG05.v:69-84), since frames S = [] at
   the entry (two Theorem Labs lanes, 21:29Z-21:30Z).  ENTRY (before the frame) and the post-release cuts
   own nothing (own0).  The shell passes sel = fr. *)
(* ENTRY: Inv_ENTRY, SlotInv.v:789 (shell alib_pre (Inv_ENTRY :789, `AF.alib_pre` :791-792)); pc 0x81018, index [], k <= 0, own0, piece W0
   live list (table): entry blocks *)
Definition C_ENTRY : ctlcut := mkCtlCut
  0x81018
  own0
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     Reusable.YG0d.spZ (c_regs cx) = c_sp cx /\
     (* the entry cut's registers ARE the contract's entry registers (added 06:00Z, found by a Theorem Labs lane:
        without it seg_A1 cannot pin regs 3 / 8 / 18 / 22 or the saved bytes at B81090) *)
     regs = c_regs cx).

(* B81090: Inv_B81090, SlotInv.v:1420 (shell PREF :1391 (A = sp) + ENT :371 (:1423)); pc 0x81090, index [], k <= 0, own6, piece W0
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): the r = 0 (class 6 full) outcome of __asan_stack_malloc_6 @0x8108c is discharged by the model law, not walked; own resolves to own6 = [(6,fpos)], r = frame_addr ly 6 fpos
   live list (table): entry blocks *)
Definition C_B81090 : ctlcut := mkCtlCut
  0x81090
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     PREFC cx regs m /\
     (* the frame request's result in a0 IS the selector: the shell passes sel = fr and the
        class-full (a0 = 0) arm is discharged at the fake-stack call, a Theorem Labs lane 23:05Z *)
     a0v regs sel /\ 0 <= sel < 2 ^ 64 /\
    rgv regs 22 (c_p cx) /\ rgv regs 18 (c_n cx) /\
    (* the fake-frame trailer word, born by the frame allocation's post at 0x8108c (see FRAC); added 06:00Z *)
    q64 m (fr + 4088) (Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))).

(* B810c4: Inv_B810c4, SlotInv.v:1435 (shell PREF :1391 + ENT :371 (:1438)); pc 0x810c4, index [], k <= 0, own6, piece W0
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s8 = fr); plan (a working note, not in this delivery) 21:48Z, BM4 CLOSED (UAR word 0xa96c0 = 1 measured): S_A1's direct zero-UAR edge into this cut is dead
   live list (table): entry blocks *)
Definition C_B810c4 : ctlcut := mkCtlCut
  0x810c4
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     PREFC cx regs m /\
     exists A,
     rgv regs 25 fr /\ fr mod 32 = 0 /\ (* s8, ctrl's selector register (SlotInv.v:266), is sel: see B81090 *)
    rgv regs 24 sel /\ 0 <= fr < 2 ^ 64 /\ fr + FRAME_BYTES <= A /\
    rgv regs 22 (c_p cx) /\ rgv regs 18 (c_n cx) /\
    q64 m (fr + 4088) (Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))).

(* B81220: Inv_B81220, SlotInv.v:1454 (shell CUTST0 :489 (FRAS :482 = FRAH :447 + ENT :371)); pc 0x81220, index [], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (sel = fr)
   live list (table): entry blocks *)
Definition C_B81220 : ctlcut := mkCtlCut
  0x81220
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x41b58ab3 regs m /\
     c_n cx <= B.ACtlK.ANMAX /\
    rgv regs 20 (-8) /\ rgv regs 21 (-14) /\ rgv regs 24 sel /\ rgv regs 25 fr /\
    rgv regs 22 (c_p cx) /\ rgv regs 18 (c_n cx) /\ rgv regs 27 (Sfr fr + 68)).

(* B81548_at t: Inv_B81548_at, SlotInv.v:1510 (shell CUTST0 :489 (FRAS :482 = FRAH :447 + ENT :371)); pc 0x81548, index [t], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (sel = fr)
   live list (table): entry blocks *)
Definition C_B81548_at : ctlcut := mkCtlCut
  0x81548
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     let t := ixz 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x41b58ab3 regs m /\
     LOOPB cx t fr sel regs m /\ PRA fr regs m).

(* B81550: Inv_B81550, SlotInv.v:1530 (shell CUTST0 :489 (FRAS :482 = FRAH :447 + ENT :371) (∃ t of `Inv_B81550_at` :1526)); pc 0x81550, index [], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (sel = fr)
   live list (table): entry blocks *)
Definition C_B81550 : ctlcut := mkCtlCut
  0x81550
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     exists t,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x41b58ab3 regs m /\
     LOOPB cx t fr sel regs m /\ PRA fr regs m /\ t < c_n cx /\ rgv regs 13 (c_p cx + t + 1)).

(* B815fc: Inv_B815fc, SlotInv.v:1543 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x815fc, index [], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B815fc : ctlcut := mkCtlCut
  0x815fc
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ a0v regs SM.CAT /\ OURb cx fr m /\
    rgv regs 27 (Sfr fr + 68) /\ CUR cx 7 regs /\ spill regs m 144 (fr + 2176) /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\
    rgv regs 20 (fr + 2656) /\ q64 m (fr + 2656) SM.CAT_N /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ ART.addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\
    rgv regs 22 (SM.mode (c_in cx)) /\
    spill regs m 160 (fr + 32)).

(* B81640: Inv_B81640, SlotInv.v:1559 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81640, index [], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81640 : ctlcut := mkCtlCut
  0x81640
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ CUR cx 7 regs /\ OURb cx fr m /\
    spill regs m 144 (fr + 2176) /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ ART.addressable m (fr + 544) 1488 /\ spill regs m 8 (Sfr fr + 68) /\
    rgv regs 18 (SM.mrow (c_in cx)) /\ ART.addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 160 (fr + 32)).

(* B8168c: Inv_B8168c, SlotInv.v:1681 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8168c, index [], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B8168c : ctlcut := mkCtlCut
  0x8168c
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ CUR cx 7 regs /\ OURb cx fr m /\
    IDBr cx fr (SM.RID (c_in cx) 0) m /\ ART.addressable m (fr + 2256) 72 /\ spill regs m 112 (fr + 2256) /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ ART.addressable m (fr + 544) 1492 /\ ART.addressable m (fr + 2176) 38 /\
    spill regs m 144 (fr + 2176) /\ spill regs m 8 (Sfr fr + 68) /\
    rgv regs 18 (SM.mrow (c_in cx)) /\ ART.addressable m (fr + 2624) 6 /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 160 (fr + 32)).

(* B8169c: Inv_B8169c, SlotInv.v:1703 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8169c, index [], k <= 0, own6, piece W1
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B8169c : ctlcut := mkCtlCut
  0x8169c
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ CUR cx 7 regs /\ OURb cx fr m /\
    IDBr cx fr (SM.RID (c_in cx) 0) m /\ FGBr cx fr (SM.RFG (c_in cx) 0) m /\
    spill regs m 312 (fr + 544) /\ spill regs m 264 (fr + 2624) /\ spill regs m 56 (fr + 3040) /\
    spill regs m 184 (fr + 2368) /\ spill regs m 144 (fr + 2176) /\ spill regs m 8 (Sfr fr + 68) /\
    rgv regs 18 (SM.mrow (c_in cx)) /\ ART.addressable m (fr + 2624) 6 /\ OUTA fr m /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    spill regs m 240 (fr + 2448) /\ spill regs m 232 (fr + 2464) /\ spill regs m 224 (fr + 2496) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    PRA fr regs m /\ spill regs m 152 (fr + 64) /\ spill regs m 112 (fr + 2256) /\
    ART.addressable m (fr + 2176) 38 /\ ART.addressable m (fr + 2256) 72 /\
    (RS6.has (SM.rt_mb (c_in cx)) <> 0 /\ RS6.rname (SM.rt_mb (c_in cx)) <> 0 ->
       RBx.name_ok (SM.rt_nb (c_in cx)) /\ MEM.bytes_at segs m (RS6.rname (SM.rt_mb (c_in cx))) (SM.rt_nb (c_in cx)) /\
       ART.addressable m (RS6.rname (SM.rt_mb (c_in cx))) (Z.of_nat (length (SM.rt_nb (c_in cx)))) /\
       0 < RS6.rname (SM.rt_mb (c_in cx))) /\
    spill regs m 160 (fr + 32)).

(* B816ec_at b: Inv_B816ec_at, SlotInv.v:1732 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x816ec, index [b], k <= 2b, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B816ec_at : ctlcut := mkCtlCut
  0x816ec
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ RS cx fr b regs m /\
    RBE cx fr regs m /\ rgv regs 21 36 /\ R6X cx b fr regs m /\
    (RS6.has (SM.rt_mb (c_in cx)) <> 0 /\ RS6.rname (SM.rt_mb (c_in cx)) <> 0 ->
       RBx.name_ok (SM.rt_nb (c_in cx)) /\ MEM.bytes_at segs m (RS6.rname (SM.rt_mb (c_in cx))) (SM.rt_nb (c_in cx)) /\
       ART.addressable m (RS6.rname (SM.rt_mb (c_in cx))) (Z.of_nat (length (SM.rt_nb (c_in cx)))) /\
       0 < RS6.rname (SM.rt_mb (c_in cx))) /\ rgv regs 27 32).

(* B81710_at b: Inv_B81710_at, SlotInv.v:1755 (shell raw FRA :330 + ENT :371 (:1758; "Not a CUTST", :1742)); pc 0x81710, index [b], k <= 2b, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81710_at : ctlcut := mkCtlCut
  0x81710
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     exists A,
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ 0 <= rnb cx b <= B.ACtlK.ANMAX /\
    0 <= B.ACtlK.a_size (rnb cx b) <= 616472576 /\
    0 <= A < 2 ^ 64 /\ rgv regs 9 A /\ rgv regs 21 36 /\ a0v regs (rnb cx b) /\ q64 m (A + 128) 0xe38f0000 /\
    RBE cx fr regs m /\
    IDBr cx fr (SM.RID (c_in cx) b) m /\ FGBr cx fr (SM.RFG (c_in cx) b) m /\
    (rnb cx b <> 0 -> MEM.bytes_at segs m (fr + 544) (SM.rt_F (c_in cx) (Z.of_nat b))) /\
    rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\
    
    OUTA fr m /\
    (rnb cx b = 0 -> R6X cx (S b) fr regs m) /\ rgv regs 27 32).

(* B81764_at b: Inv_B81764_at, SlotInv.v:1779 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81764, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B81764_at : ctlcut := mkCtlCut
  0x81764
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ rnb cx b <> 0 /\
    a0v regs phi /\ HB m phi (rnb cx b) /\ rgv regs 18 (rnb cx b) /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    IDBr cx fr (SM.RID (c_in cx) b) m /\ FGBr cx fr (SM.RFG (c_in cx) b) m /\ MEM.bytes_at segs m (fr + 544) (SM.rt_F (c_in cx) (Z.of_nat b)) /\
    rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\
    ART.addressable m (fr + 544) (rnb cx b) /\ rgv regs 27 32).

(* B8177c_at b: Inv_B8177c_at, SlotInv.v:1796 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8177c, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B8177c_at : ctlcut := mkCtlCut
  0x8177c
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    rnb cx b <> 0 /\ rgv regs 20 phi /\ rgv regs 18 (rnb cx b) /\ spill regs m 184 (fr + 2368) /\
    IDBr cx fr (SM.RID (c_in cx) b) m /\ FGBr cx fr (SM.RFG (c_in cx) b) m /\
    MEM.bytes_at segs m phi (SM.rt_F (c_in cx) (Z.of_nat b)) /\ ART.addressable m (fr + 2256) 72 /\ rgv regs 27 32).

(* B817a4_at b: Inv_B817a4_at, SlotInv.v:1811 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x817a4, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B817a4_at : ctlcut := mkCtlCut
  0x817a4
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 4 /\
    a0v regs (SM.rt_k (c_in cx) (Z.of_nat b)) /\ RF cx fr b phi regs m /\
    spill regs m 24 (SM.mrow (c_in cx) + 16) /\ spill regs m 16 (SM.mrow (c_in cx) + 20) /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    ART.addressable m (fr + 2256) 72 /\
    (b = 5%nat -> SM.fg_rf (rnb cx 5) (SM.RFG (c_in cx) 5) (SM.rt_g (c_in cx) 5) = 0) /\ rgv regs 27 32).

(* B817ec_at b: Inv_B817ec_at, SlotInv.v:1825 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x817ec, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B817ec_at : ctlcut := mkCtlCut
  0x817ec
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    (b = 3 \/ b = 4)%nat /\ RF cx fr b phi regs m /\
    a0v regs (RRP.reply_ret phi (rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496) (SM.rt_g (c_in cx) (Z.of_nat b))) /\
    (RRP.reply_ok phi (rnb cx b) (fr + 2448) (fr + 2464) (fr + 2496) (SM.rt_g (c_in cx) (Z.of_nat b)) = true ->
       STP.rw_cells segs m (fr + 2448) [CEL.CB 2 (RRP.reply_addr (SM.rt_g (c_in cx) (Z.of_nat b)))] /\
       STP.rw_cells segs m (fr + 2464) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (phi + 38)))] /\
       STP.rw_cells segs m (fr + 2496) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (RRP.ir_s (SM.rt_g (c_in cx) (Z.of_nat b)) - 13)))]) /\
    rgv regs 27 32).

(* B81834_at b: Inv_B81834_at, SlotInv.v:1845 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81834, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B81834_at : ctlcut := mkCtlCut
  0x81834
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    b = 6%nat /\ rnb cx b <> 0 /\ rgv regs 20 phi /\
    IDBr cx fr (SM.RID (c_in cx) b) m /\ FGBr cx fr (SM.RFG (c_in cx) (S b)) m /\ ART.addressable m (fr + 2256) 72 /\
    a0v regs (SM.fg_rf (rnb cx b) (SM.RFG (c_in cx) b) (SM.rt_g (c_in cx) (Z.of_nat b))) /\
    (SM.fg_rf (rnb cx b) (SM.RFG (c_in cx) b) (SM.rt_g (c_in cx) (Z.of_nat b)) = 1 ->
       u16 m (fr + 2448) (RFR.fg_addr (SM.RFG (c_in cx) b) (SM.rt_g (c_in cx) (Z.of_nat b))) /\
       q64 m (fr + 2464) (fr + 2256 + 19) /\
       q64 m (fr + 2496) (RFR.fg_T (SM.RFG (c_in cx) b) (SM.rt_g (c_in cx) (Z.of_nat b)) - 13)) /\
    rgv regs 27 32).

(* B81860_at b: Inv_B81860_at, SlotInv.v:1865 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81860, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B81860_at : ctlcut := mkCtlCut
  0x81860
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    IDBr cx fr (SM.RID (c_in cx) (S b)) m /\ FGBr cx fr (SM.RFG (c_in cx) (S b)) m /\ rgv regs 20 phi /\ a0v regs 1 /\ rgv regs 27 32).

(* B818a8_at b: Inv_B818a8_at, SlotInv.v:1886 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x818a8, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B818a8_at : ctlcut := mkCtlCut
  0x818a8
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi (i : nat),
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\ (i <= 32)%nat /\ rgv regs 10 (phi + 18 + Z.of_nat i) /\ rgv regs 12 (phi + 18 + Z.of_nat i) /\ rgv regs 14 (32 - Z.of_nat i) /\
    b = 0%nat /\ (i < 32)%nat /\ rgv regs 11 (rsum cx b i) /\ RF cx fr b phi regs m /\
    spill regs m 24 (SM.mrow (c_in cx) + 16) /\ spill regs m 16 (SM.mrow (c_in cx) + 20) /\
    spill regs m 96 (decl_slot fr) /\ spill regs m 120 (fr + 2528) /\
    ART.addressable m (fr + 2528) 12 /\ rgv regs 13 (- (phi + 18)) /\ rgv regs 27 32).

(* B81914_at b: Inv_B81914_at, SlotInv.v:1896 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81914, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B81914_at : ctlcut := mkCtlCut
  0x81914
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    RB cx fr b (SM.RID (c_in cx) (S b)) (SM.RFG (c_in cx) (S b)) regs m /\ rgv regs 20 phi /\ a0v regs 0 /\ rgv regs 27 32).

(* B8194c_at b: Inv_B8194c_at, SlotInv.v:1907 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8194c, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B8194c_at : ctlcut := mkCtlCut
  0x8194c
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi (i : nat),
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\ (i <= 32)%nat /\ rgv regs 10 (phi + 18 + Z.of_nat i) /\ rgv regs 12 (phi + 18 + Z.of_nat i) /\ rgv regs 14 (32 - Z.of_nat i) /\
    (b = 1 \/ b = 2)%nat /\ (i < 32)%nat /\ rgv regs 11 (rsum cx b i) /\
    RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ rgv regs 13 (- (phi + 18)) /\ rgv regs 27 32).

(* B819a8_at b: Inv_B819a8_at, SlotInv.v:1916 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x819a8, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B819a8_at : ctlcut := mkCtlCut
  0x819a8
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ spill regs m 120 (fr + 2528) /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    b = 0%nat /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ a0v regs (SM.mrow (c_in cx)) /\
    spill regs m 24 (SM.mrow (c_in cx) + 16) /\ spill regs m 16 (SM.mrow (c_in cx) + 20) /\
    spill regs m 96 (decl_slot fr) /\ ART.addressable m (fr + 2528) 12 /\ rgv regs 27 32).

(* B819d0_at b: Inv_B819d0_at, SlotInv.v:1927 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x819d0, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B819d0_at : ctlcut := mkCtlCut
  0x819d0
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ spill regs m 96 (decl_slot fr) /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    b = 0%nat /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ rgv regs 18 (phi + 18) /\
    a0v regs 0 /\
    u32 m (fr + 2528) (4 * RLF.n_in (SM.rt_pbs (c_in cx))) /\
    u32 m (fr + 2532) (4 * RLF.n_out (SM.rt_pbs (c_in cx))) /\
    spill regs m 120 (fr + 2528) /\ spill regs m 24 (SM.mrow (c_in cx) + 16) /\
    spill regs m 16 (SM.mrow (c_in cx) + 20) /\ rgv regs 27 32).

(* B81a50_at b: Inv_B81a50_at, SlotInv.v:1941 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81a50, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B81a50_at : ctlcut := mkCtlCut
  0x81a50
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi vd,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ rgv regs 10 vd /\ vd <> 0 /\ rgv regs 18 (phi + 18) /\ spill regs m 96 (decl_slot fr) /\ MEM.bytes_at segs m (decl_slot fr) (RDC.decl (SM.rt_mb (c_in cx))) /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    b = 0%nat /\ HB m phi (rnb cx b) /\ 0 <= vd < 2 ^ 64 /\
    length (RDC.decl (SM.rt_mb (c_in cx))) = 32%nat /\ ART.addressable m (decl_slot fr) 32 /\ rgv regs 27 32).

(* B81a68_at b: Inv_B81a68_at, SlotInv.v:1949 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81a68, index [b], k <= 2b+1, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, rnb g b)] (Perm; ctrl hb = `hb1 phi (rnb g b)`) *)
Definition C_B81a68_at : ctlcut := mkCtlCut
  0x81a68
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ CUR cx 7 regs /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    b = 0%nat /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ a0v regs 0 /\ rgv regs 27 32).

(* B81aa0_at b: Inv_B81aa0_at, SlotInv.v:1956 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81aa0, index [b], k <= 2b+2, own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81aa0_at : ctlcut := mkCtlCut
  0x81aa0
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 2)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ rgv regs 22 (Z.of_nat b) /\ OURb cx fr m /\ RBE cx fr regs m /\ rgv regs 21 36 /\
    RB cx fr b (SM.RID (c_in cx) (S b)) (SM.RFG (c_in cx) (S b)) regs m /\ rgv regs 27 32).

(* B81ac0_at b: Inv_B81ac0_at, SlotInv.v:1969 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81ac0, index [b], k <= 2b (only producer: S_R7's n_b = 0 skip, no malloc; S_R21 runs through 0x81ac0 in its owner form, UB `Seg/Slot.v` (not in this delivery)), own6, piece W2
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81ac0_at : ctlcut := mkCtlCut
  0x81ac0
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\
    rgv regs 22 (Z.of_nat b) /\ CUR cx 7 regs /\ OURb cx fr m /\
    IDBr cx fr (SM.RID (c_in cx) (S b)) m /\ FGBr cx fr (SM.RFG (c_in cx) (S b)) m /\
    RBE cx fr regs m /\ rgv regs 21 36 /\ R6X cx (S b) fr regs m /\ rgv regs 27 32).

(* B81c58: Inv_B81c58, SlotInv.v:2017 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81c58, index [], k <= 14 (max: S_R21 at b = 6 gives 2·6+2 = 14; S_R21_a5c at b = 6 gives 12), own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81c58 : ctlcut := mkCtlCut
  0x81c58
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs 0 /\
    PRO fr regs m /\
    (exists Q, spill regs m 8 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    spill regs m 56 (fr + 3040) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    CUR cx (SM.c0 (c_in cx)) regs /\ ART.addressable m KNA.KIND_NAME 112).

(* B81c60: Inv_B81c60, SlotInv.v:2037 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81c60, index [], k <= 12 (only producer S_R21_a5c at b = 6, from `Inv_B81ac0_at` 6; 14 also holds), own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81c60 : ctlcut := mkCtlCut
  0x81c60
  own6
  (fun _ _ => 12)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs 0 /\
    PRO fr regs m /\
    (exists Q, spill regs m 8 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    spill regs m 56 (fr + 3040) /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\ spill regs m 64 (fr + 3056) /\
    CUR cx (SM.c0 (c_in cx)) regs /\ ART.addressable m KNA.KIND_NAME 112).

(* B81ca8: Inv_B81ca8, SlotInv.v:2045 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81ca8, index [], k <= 14 (max over S_R21 b = 6: 14, S_P1: 14, S_P1_bfc: 12), own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81ca8 : ctlcut := mkCtlCut
  0x81ca8
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ spill regs m 56 (fr + 3040) /\
    PRO fr regs m /\
    spill regs m 176 (fr + 2688) /\ spill regs m 208 (fr + 2768) /\
    spill regs m 64 (fr + 3056) /\ CUR cx (SM.c0 (c_in cx)) regs /\ ART.addressable m KNA.KIND_NAME 112).

(* B81cb0: Inv_B81cb0, SlotInv.v:2059 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81cb0, index [], k <= 14 (max: 0 on the S_A5 / S_R1 mode-test edge that skips the round trip; 14 via S_P2), own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81cb0 : ctlcut := mkCtlCut
  0x81cb0
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ rgv regs 24 (fr + 3040) /\
    PRO fr regs m /\
    spill regs m 64 (fr + 3056) /\ CUR cx (SM.c0 (c_in cx)) regs /\ ART.addressable m KNA.KIND_NAME 112 /\
    exists (spv A : Z) (idb junk : list byte),
      lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 spv /\ lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\
      0 <= A < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      q64 m (A + 176) (fr + 2688) /\
      STP.rw_cells segs m (A + 208) [CEL.C8 (Z_to_bv 64 (fr + 2768))] /\
      STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb] /\
      STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk] /\
      (exists junkf : list byte, STP.rw_cells segs m (fr + 2880) [CEL.CB 40 junkf])).

(* B81d18: Inv_B81d18, SlotInv.v:2077 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81d18, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81d18 : ctlcut := mkCtlCut
  0x81d18
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ rgv regs 24 (fr + 3040) /\
    PRO fr regs m /\
    CUR cx (SM.c0 (c_in cx)) regs /\ ART.addressable m KNA.KIND_NAME 112 /\ IDBe cx fr RIM.ID0 m /\
    ART.addressable m (fr + 2688) 38 /\ spill regs m 176 (fr + 2688) /\
    exists (D spv A : Z) (junk : list byte),
      let W : list FRM.ivl := [(D, D + 72); (spv - AMC.ASAN_MEMSET_K, spv)] in
      lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 spv /\ lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\
      0 <= A < 2 ^ 64 /\ 0 <= D < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      STP.rw_cells segs m (A + 208) [CEL.C8 (Z_to_bv 64 D)] /\
      STP.rw_cells segs m D [CEL.CB 72 junk] /\ ART.addressable m D 72 /\ ART.end_in_app D 72 /\ ART.app_mem (D + 7) /\
      (D + 72 <= ART.RT_LO \/ ART.RT_HI <= D) /\
      (D + 72 <= spv - AMC.ASAN_MEMSET_K \/ spv <= D) /\
      (forall x, 0 <= x < 6283264 -> FRM.outside W x) /\
      (forall x, fr <= x < fr + 24 -> FRM.outside W x) /\
      (forall A0, lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 336 <= x < A0 + 344 -> FRM.outside W x) /\
      (forall A0, lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 40 <= x < A0 + 56 -> FRM.outside W x) /\
      (forall x, c_sp cx - 104 <= x < c_sp cx -> FRM.outside W x) /\
      (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> FRM.outside W x) /\
      (forall x, fr + 2624 <= x < fr + 2624 + Z.of_nat (length (SM.OUR (c_in cx))) -> FRM.outside W x) /\
      ARF.all_app W /\ rt_disjoint W /\
      D = fr + 2768 /\ q64 m (A + 64) (fr + 3056) /\
      FSj cx fr 0 regs m /\ ART.addressable m (fr + 2880) 40).

(* B81d28: Inv_B81d28, SlotInv.v:2107 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81d28, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81d28 : ctlcut := mkCtlCut
  0x81d28
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\
    PRO fr regs m /\
    CUR cx (SM.c0 (c_in cx)) regs /\ ART.addressable m KNA.KIND_NAME 112 /\ IDBe cx fr RIM.ID0 m /\
    FGBe cx fr SM.z72 m /\ RAD fr m /\ spill regs m 176 (fr + 2688) /\ spill regs m 208 (fragb fr) /\
    exists (A : Z) (jy junk : list byte),
      rgv regs 9 A /\ 0 <= A /\ rgv regs 24 (fr + 3040) /\ q64 m (A + 64) (fr + 3056) /\
      STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\
      STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk] /\
      FSj cx fr 0 regs m).

(* B81d68: Inv_B81d68, SlotInv.v:2124 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81d68, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81d68 : ctlcut := mkCtlCut
  0x81d68
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ XC fr regs m /\
    PRO fr regs m /\
    spill regs m 64 (fr + 3056) /\ PL0 cx fr regs m /\ ART.addressable m KNA.KIND_NAME 112 /\
    exists (A pa pp pn f : Z),
      rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ 0 <= pa < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\ 0 <= pn < 2 ^ 64 /\
      q64 m (A + 88) pa /\ q64 m (A + 80) pp /\ q64 m (A + 72) pn /\ q64 m (A + 208) f /\
      ART.addressable m (Reusable.YG0d.spZ regs - RCIR.REAC_CTRL_IDENTITY_REPLY_K)
        RCIR.REAC_CTRL_IDENTITY_REPLY_K /\
      ART.addressable m RCP.REAC_CTRL_PARSE_BC 6).

(* B81d80: Inv_B81d80, SlotInv.v:2146 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81d80, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81d80 : ctlcut := mkCtlCut
  0x81d80
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    (exists v, spill regs m 208 v) /\ (exists v, spill regs m 88 v) /\ (exists v, spill regs m 80 v) /\
    (exists v, spill regs m 72 v) /\ spill regs m 64 (fr + 3056) /\
    rgv regs 24 (fr + 3040) /\ ART.addressable m (fr + 3040) 1 /\
    ART.addressable m KNA.KIND_NAME 112 /\ PL0 cx fr regs m).

(* B81da8: Inv_B81da8, SlotInv.v:2154 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81da8, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81da8 : ctlcut := mkCtlCut
  0x81da8
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    rgv regs 18 (-1) /\ spill regs m 64 (fr + 3056) /\
    rgv regs 24 (fr + 3040) /\ ART.addressable m (fr + 3040) 1 /\
    ART.addressable m KNA.KIND_NAME 112 /\ PL0 cx fr regs m).

(* B81dbc: Inv_B81dbc, SlotInv.v:2166 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81dbc, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81dbc : ctlcut := mkCtlCut
  0x81dbc
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    rgv regs 24 (fr + 3040) /\ ART.addressable m (fr + 3040) 1 /\
    ART.addressable m KNA.KIND_NAME 112 /\ PL0 cx fr regs m).

(* B81dd4: Inv_B81dd4, SlotInv.v:2172 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81dd4, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81dd4 : ctlcut := mkCtlCut
  0x81dd4
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs (-1) /\ rgv regs 18 (-1) /\
    PRO fr regs m /\
    rgv regs 24 (fr + 3040) /\ ART.addressable m (fr + 3040) 1 /\
    ART.addressable m KNA.KIND_NAME 112 /\ PL0 cx fr regs m).

(* B81de8: Inv_B81de8, SlotInv.v:2183 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81de8, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81de8 : ctlcut := mkCtlCut
  0x81de8
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs (-1) /\
    PRO fr regs m /\
    b8 m (fr + 3040) 0 /\ XC fr regs m /\
    ART.addressable m KNA.KIND_NAME 112 /\ PL0 cx fr regs m).

(* B81e08: Inv_B81e08, SlotInv.v:2195 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81e08, index [], k <= 14, own6, piece W3
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81e08 : ctlcut := mkCtlCut
  0x81e08
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ PRO fr regs m /\ PL0 cx fr regs m /\
    a0v regs KNA.QMARK /\ KNT m).

(* B81ec4_at j: Inv_B81ec4_at, SlotInv.v:2243 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81ec4, index [j], k <= 14+2j, own6, piece W4a
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B81ec4_at : ctlcut := mkCtlCut
  0x81ec4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ LI cx fr j regs m /\ f1_IN cx m /\
    spill regs m 280 (fr + 176) /\ rgv regs 22 1).

(* B81f50_at j: Inv_B81f50_at, SlotInv.v:2253 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x81f50, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B81f50_at : ctlcut := mkCtlCut
  0x81f50
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ a0v regs phi /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\ FC cx fr j regs m /\ f1_IN cx m /\
    FSj cx fr j regs m /\ REC0 cx fr j m /\ rgv regs 22 1).

(* B81f78_at j: Inv_B81f78_at, SlotInv.v:2271 (shell FCUT :2268 → FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x81f78, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B81f78_at : ctlcut := mkCtlCut
  0x81f78
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun _ fr regs m =>
       LK cx fr j regs m /\ FC cx fr j regs m /\ rgv regs 22 1 /\ FSj cx fr j regs m /\ REC0 cx fr j m)).

(* B81fbc_at j: Inv_B81fbc_at, SlotInv.v:2282 (shell FCUT :2268 → FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x81fbc, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B81fbc_at : ctlcut := mkCtlCut
  0x81fbc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun _ fr regs m =>
       LK cx fr j regs m /\ FC cx fr j regs m /\ rgv regs 22 1 /\ FSj cx fr j regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ a0v regs (SM.t_k (c_in cx) j) /\ 50 <= flen cx j)).

(* B82048_at j: Inv_B82048_at, SlotInv.v:2286 (shell FCUT :2268 → FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82048, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82048_at : ctlcut := mkCtlCut
  0x82048
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun _ fr regs m =>
       LK cx fr j regs m /\ rgv regs 22 1 /\ FSj cx fr j regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ a0v regs (SM.t_k (c_in cx) j) /\ flen cx j < 50)).

(* B82098_at j: Inv_B82098_at, SlotInv.v:2299 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82098, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82098_at : ctlcut := mkCtlCut
  0x82098
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ rgv regs 22 1 /\ FSj cx fr j regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\
  50 <= flen cx j /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ a0v regs (phi + 18) /\ rgv regs 11 0 /\ rgv regs 12 (phi + 18) /\
  rgv regs 13 (- (phi + 18)) /\ rgv regs 14 32 /\ rgv regs 17 32 /\ rgv regs 5 (phi + 18))).

(* B8215c_at j: Inv_B8215c_at, SlotInv.v:2319 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8215c, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8215c_at : ctlcut := mkCtlCut
  0x8215c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 18 phi /\ rgv regs 20 (SM.t_len (c_in cx) j) /\ FM cx j phi fr regs m /\ FSj cx fr j regs m /\
       MEM.bytes_at segs m KNA.KIND_NAME KNA.kind_name_bytes /\ ART.addressable m KNA.KIND_NAME 112 /\
       spill regs m 248 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\ (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
       FTURN cx j phi regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\
       exists A v, FLVsp A fr regs m /\
         rgv regs 10 v /\ rgv regs 24 v /\ 0 <= v < 2 ^ 31 /\ q64 m (A + 280) (fr + 176) /\
         u32 m (fr + 176) v).

(* B82174_at j: Inv_B82174_at, SlotInv.v:2334 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82174, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82174_at : ctlcut := mkCtlCut
  0x82174
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 18 phi /\ rgv regs 20 (SM.t_len (c_in cx) j) /\ FM cx j phi fr regs m /\ FSj cx fr j regs m /\
       MEM.bytes_at segs m KNA.KIND_NAME KNA.kind_name_bytes /\ ART.addressable m KNA.KIND_NAME 112 /\
       spill regs m 248 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\ (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
       FTURN cx j phi regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\
       exists A v, FLVsp A fr regs m /\
         rgv regs 10 (KNA.kind_name_addr v) /\ rgv regs 24 v /\ 0 <= v < 2 ^ 31 /\ q64 m (A + 280) (fr + 176) /\
         u32 m (fr + 176) v).

(* B82180_at j: Inv_B82180_at, SlotInv.v:2349 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82180, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82180_at : ctlcut := mkCtlCut
  0x82180
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 18 phi /\ rgv regs 20 (SM.t_len (c_in cx) j) /\ FM cx j phi fr regs m /\ FSj cx fr j regs m /\
       MEM.bytes_at segs m KNA.KIND_NAME KNA.kind_name_bytes /\ ART.addressable m KNA.KIND_NAME 112 /\
       spill regs m 248 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\ (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
       FTURN cx j phi regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\
       exists A v, FLVsp A fr regs m /\
         rgv regs 10 (KNA.kind_name_addr v) /\ rgv regs 24 v /\ 0 <= v < 2 ^ 31 /\ q64 m (A + 280) (fr + 176) /\
         u32 m (fr + 176) v /\
         MEM.bytes_at segs m (KNA.kind_name_addr v) (RKN.cstr_bytes (RKN.kind_name v))).

(* B821ec_at j: Inv_B821ec_at, SlotInv.v:2372 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x821ec, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B821ec_at : ctlcut := mkCtlCut
  0x821ec
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     f10_K cx j phi fr regs m /\ FSj cx fr j regs m /\
       (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
       rgv regs 10 (RRP.reply_ret phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j)) /\
       (RRP.reply_ok phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j) = true ->
          f10_RPost phi fr (SM.t_g (c_in cx) j) m) /\
       FTURN cx j phi regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\ RCA fr m).

(* B8226c_at j: Inv_B8226c_at, SlotInv.v:2385 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8226c, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8226c_at : ctlcut := mkCtlCut
  0x8226c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     f10_K cx j phi fr regs m /\ FSj cx fr j regs m /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ SM.t_sum_ok (c_in cx) j = true /\
       MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\
       RRP.reply_ok phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j) = true /\
       f10_RPost phi fr (SM.t_g (c_in cx) j) m /\
       rgv regs 11 (RRP.ir_s (SM.t_g (c_in cx) j) - 13) /\
       FTURN cx j phi regs m /\ REC0 cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\ RCA fr m).

(* B82304_at j: Inv_B82304_at, SlotInv.v:2402 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82304, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82304_at : ctlcut := mkCtlCut
  0x82304
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FM cx j phi fr regs m /\ FSj cx fr j regs m /\ RECR cx fr j m /\
    (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
    FPS cx fr j m /\ F272 cx j regs m /\ RCA fr m /\
    (exists r, rgv regs 10 r /\ 0 <= r < 2 ^ 63) /\ FS9 cx j regs m)).

(* B82308_at j: Inv_B82308_at, SlotInv.v:2411 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82308, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82308_at : ctlcut := mkCtlCut
  0x82308
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     f10_K cx j phi fr regs m /\ FSj cx fr j regs m /\
       (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
       RRP.ir (flen cx j) (SM.t_g (c_in cx) j) = false /\
       FTURN cx j phi regs m /\ RECR cx fr j m /\ FPS cx fr j m /\ F272 cx j regs m /\ RCA fr m).

(* B82340_at j: Inv_B82340_at, SlotInv.v:2433 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82340, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82340_at : ctlcut := mkCtlCut
  0x82340
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       (LK cx fr j regs m /\ MEM.bytes_at segs m (fr + 336) (SM.t_FG (c_in cx) j) /\
        FM cx j phi fr regs m /\ FSj cx fr j regs m) /\
       rgv regs 21 (fragb fr) /\
       (50 <= flen cx j ->
          (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
          (phi + 50 <= Reusable.YG0d.spZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ Reusable.YG0d.spZ regs <= phi) /\
          MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ ART.addressable m phi 50) /\
       MEM.bytes_at segs m (fragb fr) (SM.t_FG (c_in cx) j) /\
       ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 336) 72 /\
       ART.addressable m (fr + 256) 2 /\ ART.addressable m (fr + 272) 8 /\ ART.addressable m (fr + 304) 8 /\
       RECR cx fr j m /\ FRBA cx j fr phi regs m /\ FS9 cx j regs m)).

(* B8235c_at j: Inv_B8235c_at, SlotInv.v:2457 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x8235c, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8235c_at : ctlcut := mkCtlCut
  0x8235c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       (LK cx fr j regs m /\ FM cx j phi fr regs m /\ FSj cx fr j regs m) /\
       rgv regs 10 (RFR.fg_ret (frcl cx j fr phi)) /\
       (50 <= flen cx j ->
          (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
          (phi + 50 <= Reusable.YG0d.spZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ Reusable.YG0d.spZ regs <= phi) /\
          MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ ART.addressable m phi 50) /\
       MEM.bytes_at segs m (fr + 336) (SM.t_FG (c_in cx) j) /\ ART.addressable m (fr + 336) 72 /\
       MEM.bytes_at segs m (fragb fr) (frrec cx j fr phi) /\ ART.addressable m (fragb fr) 72 /\
       FGA.fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j)
         (frcl cx j fr phi) m /\
       RECF cx fr j m /\ FRBA cx j fr phi regs m /\ FRX cx j fr phi m /\ FS9 cx j regs m)).

(* B82378_at j: Inv_B82378_at, SlotInv.v:2479 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82378, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82378_at : ctlcut := mkCtlCut
  0x82378
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FLV cx fr j regs m /\ FM cx j phi fr regs m /\
    FSj cx fr j regs m /\ rgv regs 23 (RFR.fg_ret (frcl cx j fr phi)) /\
    SM.t_sum_ok (c_in cx) j = false /\
    (exists vcmp : Z,
       SFA.memcmp_model (SM.t_FG (c_in cx) j) (frrec cx j fr phi) 72 = Some vcmp /\ rgv regs 10 vcmp) /\
    RECF cx fr j m /\ FRBA cx j fr phi regs m /\ FRX cx j fr phi m /\ FS9 cx j regs m)).

(* B8237c_at j: Inv_B8237c_at, SlotInv.v:2496 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x8237c, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8237c_at : ctlcut := mkCtlCut
  0x8237c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FLV cx fr j regs m /\ FM cx j phi fr regs m /\
    FSj cx fr j regs m /\ rgv regs 23 (RFR.fg_ret (frcl cx j fr phi)) /\ RECF cx fr j m /\
    FRBA cx j fr phi regs m /\ FRX cx j fr phi m /\ FS9 cx j regs m)).

(* B823d8_at j: Inv_B823d8_at, SlotInv.v:2525 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x823d8, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B823d8_at : ctlcut := mkCtlCut
  0x823d8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 20 (flen cx j) /\ spill regs m 224 (c_p cx + SM.t_body (c_in cx) j) /\
       FM cx j phi fr regs m /\ FSj cx fr j regs m /\
       rgv regs 18 phi /\ rgv regs 27 (-8) /\ ART.addressable m phi 50 /\
       (exists rb, MEM.bytes_at segs m phi rb /\ length rb = 38%nat) /\
       (exists A kp,
          rgv regs 9 A /\ q64 m (A + 280) kp /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
          0 <= A < 2 ^ 64 /\ Reusable.YG0d.spZ regs <= A /\ fr + FRAME_BYTES <= A /\
          (forall a, fr + 2880 <= a < fr + 2920 -> ART.app_mem a) /\
          (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
             (SM.t_8819 (c_in cx) j = true -> w272 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w272 = 0)) /\
          (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
          (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
          (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
          (kp + 22 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= kp) /\
          (phi + 50 <= fr + 2688 \/ fr + 2688 + 38 <= phi) /\
          (kp + 22 <= fr + 2688 \/ fr + 2688 + 38 <= kp + 20) /\
          (SM.t_8819 (c_in cx) j = true ->
             rec_inv cx j phi A kp m /\
             (exists (L : Z) (ls rs : list byte),
                q64 m (A + 112) L /\ MEM.bytes_at segs m L ls /\ length ls = 6%nat /\
                MEM.bytes_at segs m phi rs /\ length rs = 6%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                ART.addressable m L 6 /\ ART.app_mem (L + 6) /\ ART.app_mem (L + 7) /\
                (L + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L) /\
                (L + 6 <= fr + 2880 \/ fr + 2920 <= L) /\
                (L + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L)) /\
             (exists (L2 : Z) (ls2 rs2 : list byte),
                q64 m (A + 96) L2 /\ MEM.bytes_at segs m L2 ls2 /\ length ls2 = 6%nat /\
                MEM.bytes_at segs m (phi + 6) rs2 /\ length rs2 = 6%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                ART.addressable m L2 6 /\ ART.app_mem (L2 + 6) /\ ART.app_mem (L2 + 7) /\
                (L2 + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L2) /\
                (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2) /\
                (L2 + 6 <= fr + 2688 \/ fr + 2688 + 38 <= L2))) /\
          (exists (N : Z) (bs : list byte),
             rgv regs 11 N /\ q64 m (A + 120) (fragb fr + 15) /\
             1 <= N /\ fragb fr + 15 + N <= fr + FRAME_BYTES /\
             MEM.bytes_at segs m (fragb fr + 15) bs /\ length bs = Z.to_nat N /\
             RRC.recsum bs = 0 /\ ART.addressable m (fragb fr + 15) N) /\
          (exists (HAVE NB AD A0V A1V : Z),
             u32 m (fr + 2880) HAVE /\ HAVE <> 0 /\ 0 <= HAVE < 2 ^ 64 /\
             b8 m (fr + 2884) NB /\ 0 <= NB < 2 ^ 64 /\
             q64 m (A + 168) A0V /\ A0V = fr + 2880 /\
             q64 m (A + 312) A1V /\ A1V = phi + 18 /\
             q64 m (A + 288) (fr + 256) /\ u16 m (fr + 256) AD /\ 0 <= AD < 65536 /\
             AD = SM.joined_addr (SM.fst_at (c_in cx) j) (SM.t_g (c_in cx) j)) /\
          (exists (PLL : Z) (idb pb : list byte),
             q64 m (A + 304) (fr + 272) /\ q64 m (fr + 272) (fragb fr + 19) /\
             q64 m (A + 296) (fr + 304) /\ q64 m (fr + 304) PLL /\
             q64 m (A + 176) (fr + 2688) /\
             0 <= PLL /\ fragb fr + 19 + PLL <= fr + FRAME_BYTES /\
             length pb = Z.to_nat PLL /\ MEM.bytes_at segs m (fragb fr + 19) pb /\
             ART.addressable m (fragb fr + 19) PLL /\
             length idb = 38%nat /\ STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb] /\
             ART.addressable m (fr + 2688) 38)) /\
       FLV cx fr j regs m /\ SM.t_rf (c_in cx) j = 1 /\
       rgv regs 11 (SM.f_pll (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j) + 5) /\
       MEM.bytes_at segs m (fragb fr) (SM.t_FGf (c_in cx) j) /\ ART.addressable m (fragb fr) 72 /\
       SM.frag_ok (SM.t_FG (c_in cx) j) /\
       u16 m (fr + 256) (RFR.fg_addr (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j)) /\
       (exists idb, MEM.bytes_at segs m (fr + 2688) idb /\ length idb = 38%nat) /\
       FTURN cx j phi regs m /\ RECF cx fr j m /\ FS9 cx j regs m).

(* B82464_at j: Inv_B82464_at, SlotInv.v:2602 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82464, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82464_at : ctlcut := mkCtlCut
  0x82464
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi : Z,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
         rgv regs 20 (flen cx j) /\ spill regs m 224 (c_p cx + SM.t_body (c_in cx) j) /\
         FM cx j phi fr regs m /\ FSj cx fr j regs m /\
         rgv regs 18 phi /\ ART.addressable m phi 50 /\
         (exists rb, MEM.bytes_at segs m phi rb /\ (38 <= length rb)%nat) /\
         (exists v0, rgv regs 10 v0 /\ 0 <= v0 < 2 ^ 63) /\
         rgv regs 27 (-8) /\
         (exists A kp, rgv regs 9 A /\ q64 m (A + 280) kp /\
            (forall a, fr + 2880 <= a < fr + 2920 -> ART.app_mem a) /\
            (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
               (SM.t_8819 (c_in cx) j = true -> w272 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w272 = 0)) /\
            rgv regs 24 (SM.t_k (c_in cx) j) /\
            (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
            (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
            (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
            (kp + 22 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= kp) /\
            (SM.t_8819 (c_in cx) j = true ->
               rec_inv cx j phi A kp m /\
               (exists (L : Z) (ls rs : list byte),
                  q64 m (A + 112) L /\ MEM.bytes_at segs m L ls /\ (6 <= length ls)%nat /\
                  MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                  ART.addressable m L 6 /\ ART.app_mem (L + 6) /\ ART.app_mem (L + 7) /\
                  (L + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L) /\
                  (L + 6 <= fr + 2880 \/ fr + 2920 <= L)) /\
               (exists (L2 : Z) (ls2 rs2 : list byte),
                  q64 m (A + 96) L2 /\ MEM.bytes_at segs m L2 ls2 /\ (6 <= length ls2)%nat /\
                  MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                  ART.addressable m L2 6 /\ ART.app_mem (L2 + 6) /\ ART.app_mem (L2 + 7) /\
                  (L2 + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L2) /\
                  (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2)))) /\
         FTURN cx j phi regs m /\ RECS cx fr j m /\ FS9 cx j regs m).

(* B82468_at j: Inv_B82468_at, SlotInv.v:2649 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82468, index [j], k <= 14+2j+1, own6, piece W4d
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr); plan (a working note, not in this delivery) 21:48Z walk rule (a Theorem Labs lane 21:01Z): no segment _F twin, so the F17b stretch (seg_F17b proved at UB, M12 (plan (a working note, not in this delivery))) is re-proved inside the walk (W4d) unless the lead allows mechanical _F re-runs (pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82468_at : ctlcut := mkCtlCut
  0x82468
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FM cx j phi fr regs m /\ FSj cx fr j regs m /\
       (50 <= flen cx j -> ART.addressable m phi 50 /\ (exists rb, MEM.bytes_at segs m phi rb /\ (38 <= length rb)%nat)) /\
       rgv regs 27 (-8) /\
       (exists A kp, rgv regs 9 A /\ q64 m (A + 280) kp /\
          (forall a, fr + 2880 <= a < fr + 2920 -> ART.app_mem a) /\
          (exists w272, q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
             (SM.t_8819 (c_in cx) j = true -> w272 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w272 = 0)) /\
          rgv regs 24 (SM.t_k (c_in cx) j) /\
          (kp + 22 <= fr + 2880 \/ fr + 2920 <= kp + 20) /\
          (kp + 22 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= kp) /\
          (50 <= flen cx j ->
             (phi + 50 <= fr + 2880 \/ fr + 2920 <= phi) /\
             (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi)) /\
          (SM.t_8819 (c_in cx) j = true ->
             rec_inv cx j phi A kp m /\
             (exists (L : Z) (ls rs : list byte),
                q64 m (A + 112) L /\ MEM.bytes_at segs m L ls /\ (6 <= length ls)%nat /\
                MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                ART.addressable m L 6 /\ ART.app_mem (L + 6) /\ ART.app_mem (L + 7) /\
                (L + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L) /\
                (L + 6 <= fr + 2880 \/ fr + 2920 <= L)) /\
             (exists (L2 : Z) (ls2 rs2 : list byte),
                q64 m (A + 96) L2 /\ MEM.bytes_at segs m L2 ls2 /\ (6 <= length ls2)%nat /\
                MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                ART.addressable m L2 6 /\ ART.app_mem (L2 + 6) /\ ART.app_mem (L2 + 7) /\
                (L2 + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L2) /\
                (L2 + 6 <= fr + 2880 \/ fr + 2920 <= L2)))) /\
       RECS cx fr j m /\ FS9 cx j regs m)).

(* B82634_at j: Inv_B82634_at, SlotInv.v:2697 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82634, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82634_at : ctlcut := mkCtlCut
  0x82634
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi : Z,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
         rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
         (exists (A kp w272 : Z),
            rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ Reusable.YG0d.spZ regs <= A /\
            rgv regs 18 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ q64 m (A + 280) kp /\
            q64 m (A + 272) w272 /\ 0 <= w272 < 2 ^ 64 /\
            (SM.t_8819 (c_in cx) j = false -> w272 = 0) /\
            (SM.t_8819 (c_in cx) j = true ->
               w272 <> 0 /\ rec_inv cx j phi A kp m /\
               exists (L L2 : Z) (ls rs ls2 rs2 : list byte),
                 q64 m (A + 112) L /\ 0 <= L < 2 ^ 64 /\
                 MEM.bytes_at segs m L ls /\ (6 <= length ls)%nat /\ MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\
                 SFA.memcmp_model ls rs 6 = Some 0 /\
                 ART.addressable m L 6 /\ ART.addressable m phi 6 /\
                 ART.app_mem (L + 6) /\ ART.app_mem (L + 7) /\ ART.app_mem (phi + 6) /\ ART.app_mem (phi + 7) /\
                 (L + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L) /\
                 (phi + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
                 (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
                 (kp + 22 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= kp) /\
                 q64 m (A + 96) L2 /\ 0 <= L2 < 2 ^ 64 /\
                 MEM.bytes_at segs m L2 ls2 /\ (6 <= length ls2)%nat /\ MEM.bytes_at segs m (phi + 6) rs2 /\
                 (6 <= length rs2)%nat /\
                 SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                 ART.addressable m L2 6 /\ ART.addressable m (phi + 6) 6 /\
                 ART.app_mem (L2 + 6) /\ ART.app_mem (L2 + 7) /\ ART.app_mem (phi + 12) /\ ART.app_mem (phi + 13) /\
                 (L2 + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L2) /\
                 (phi + 12 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi + 6))) /\
         FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B8264c_at j: Inv_B8264c_at, SlotInv.v:2733 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8264c, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8264c_at : ctlcut := mkCtlCut
  0x8264c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi : Z,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
         rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
         (exists (A kp L2 : Z) (ls2 rs2 : list byte),
            rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ Reusable.YG0d.spZ regs <= A /\
            rgv regs 18 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ q64 m (A + 280) kp /\ rgv regs 10 0 /\
            rec_inv cx j phi A kp m /\
            q64 m (A + 96) L2 /\ 0 <= L2 < 2 ^ 64 /\
            MEM.bytes_at segs m L2 ls2 /\ (6 <= length ls2)%nat /\ MEM.bytes_at segs m (phi + 6) rs2 /\
            (6 <= length rs2)%nat /\
            SFA.memcmp_model ls2 rs2 6 = Some 0 /\
            ART.addressable m L2 6 /\ ART.addressable m (phi + 6) 6 /\
            ART.app_mem (L2 + 6) /\ ART.app_mem (L2 + 7) /\ ART.app_mem (phi + 12) /\ ART.app_mem (phi + 13) /\
            (L2 + 6 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= L2) /\
            (phi + 12 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi + 6) /\
            (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
            (kp + 22 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= kp)) /\
         FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82668_at j: Inv_B82668_at, SlotInv.v:2763 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82668, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82668_at : ctlcut := mkCtlCut
  0x82668
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
       rgv regs 18 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 10 0 /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m /\
       
       exists v14 v15 v16 v17 field16,
          u16 m (fr + 196) field16 /\
          b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\
          b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
          0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
          b8 m (Z.shiftr (phi + 14) 3 + B.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 15) 3 + B.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 16) 3 + B.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 17) 3 + B.ACtlK.ASAN_K) 0 /\
          field16 = v14 + 256 * v15 /\
          (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if SM.t_k (c_in cx) j =? 1 then 1 else 0)).

(* B82728_at j: Inv_B82728_at, SlotInv.v:2792 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82728, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82728_at : ctlcut := mkCtlCut
  0x82728
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
       rgv regs 10 (if RMO.blocksum (SM.t_blk (c_in cx) j) =? 0 then 0 else -1) /\
       rgv regs 18 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B827f8_at j: Inv_B827f8_at, SlotInv.v:2815 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x827f8, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B827f8_at : ctlcut := mkCtlCut
  0x827f8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
       rgv regs 10 0 /\ rgv regs 11 0 /\ rgv regs 12 (phi + 34) /\ rgv regs 13 (2 ^ 64 - (phi + 35)) /\
       rgv regs 17 6 /\ rgv regs 18 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       RPA.cp_v (SM.t_g (c_in cx) j) 18 = 4 /\ RPA.cp_v (SM.t_g (c_in cx) j) 19 = 3 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       (forall i, 0 <= i < 6 -> b8 m (Z.shiftr (phi + 34 + i) 3 + B.ACtlK.ASAN_K) 0) /\
       rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       (forall a, fr <= a < fr + FRAME_BYTES -> ART.app_mem a) /\
       (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B8283c_at j: Inv_B8283c_at, SlotInv.v:2834 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x8283c, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8283c_at : ctlcut := mkCtlCut
  0x8283c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
       rgv regs 18 phi /\ rgv regs 23 (SM.t_want_v (c_in cx) j) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       (forall a, fr <= a < fr + FRAME_BYTES -> ART.app_mem a) /\
       (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82844_at j: Inv_B82844_at, SlotInv.v:2850 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82844, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82844_at : ctlcut := mkCtlCut
  0x82844
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 20 (flen cx j) /\ FM cx j phi fr regs m /\
       rgv regs 10 (SM.t_want_v (c_in cx) j) /\
       rgv regs 18 phi /\ rgv regs 23 (SM.t_want_v (c_in cx) j) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       (forall a, fr <= a < fr + FRAME_BYTES -> ART.app_mem a) /\
       (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82878_at j: Inv_B82878_at, SlotInv.v:2884 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82878, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82878_at : ctlcut := mkCtlCut
  0x82878
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FTL cx j phi fr regs m /\ rgv regs 22 1 /\
    IFS cx fr (S j) regs m /\
    F27K cx j phi fr regs m /\
    rgv regs 20 (flen cx j) /\ rgv regs 23 1 /\ spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
    rgv regs 21 (fr + 128) /\
    u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7) /\
    ART.addressable m (fr + 128) 12 /\
    F23GAP cx j phi m /\
    (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18))).

(* B82888_at j: Inv_B82888_at, SlotInv.v:2897 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82888, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82888_at : ctlcut := mkCtlCut
  0x82888
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FTL cx j phi fr regs m /\ IFS cx fr (S j) regs m /\
    F27K cx j phi fr regs m /\
    rgv regs 10 (SM.t_rp (c_in cx) j) /\ rgv regs 20 (flen cx j) /\ rgv regs 23 1 /\
    spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ rgv regs 22 (phi + 18) /\
    PORTS cx fr j m /\
    F23GAP cx j phi m /\
    (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
    rgv regs 21 (fr + 128))).

(* B828a4_at j: Inv_B828a4_at, SlotInv.v:2921 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x828a4, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B828a4_at : ctlcut := mkCtlCut
  0x828a4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ F27K cx j phi fr regs m /\
       rgv regs 20 (flen cx j) /\ FTL cx j phi fr regs m /\
       rgv regs 25 (SM.t_rp (c_in cx) j) /\ rgv regs 10 (SM.t_unk (c_in cx) j) /\ rgv regs 22 (phi + 18) /\
       PORTS cx fr j m /\ FIRSTb cx fr j m /\
       (phi + 50 <= Reusable.YG0d.spZ regs - 16 \/ Reusable.YG0d.spZ regs <= phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m /\
       rgv regs 21 (fr + 128)).

(* B828b4_at j: Inv_B828b4_at, SlotInv.v:2932 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x828b4, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B828b4_at : ctlcut := mkCtlCut
  0x828b4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ F27K cx j phi fr regs m /\
       rgv regs 20 (flen cx j) /\ FTL cx j phi fr regs m /\
       rgv regs 25 (SM.t_rp (c_in cx) j) /\ rgv regs 23 (SM.t_unk (c_in cx) j) /\ rgv regs 10 (SM.t_unk (c_in cx) j) /\
       PORTS cx fr j m /\ FIRSTb cx fr j m /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m /\
       rgv regs 21 (fr + 128)).

(* B8292c_at j: Inv_B8292c_at, SlotInv.v:2958 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x8292c, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B8292c_at : ctlcut := mkCtlCut
  0x8292c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FTL cx j phi fr regs m /\ IFS cx fr (S j) regs m /\
    F28GAP cx j phi fr regs m)).

(* B82aa4_at j: Inv_B82aa4_at, SlotInv.v:2964 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82aa4, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82aa4_at : ctlcut := mkCtlCut
  0x82aa4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FTL cx j phi fr regs m /\ IFS cx fr (S j) regs m)).

(* B82abc_at j: Inv_B82abc_at, SlotInv.v:2973 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82abc, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82abc_at : ctlcut := mkCtlCut
  0x82abc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ FTK cx j fr regs m /\ IFS cx fr (S j) regs m /\
    spill regs m 312 (if SM.t_big (c_in cx) j then phi + 18 else 0))).

(* B82af8_at j: Inv_B82af8_at, SlotInv.v:2983 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82af8, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82af8_at : ctlcut := mkCtlCut
  0x82af8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       FTK cx j fr regs m /\
       rgv regs 10 (RCL.cl_r (SM.t_cls (c_in cx) j)) /\
       spill regs m 144 (fr + 452) /\ spill regs m 264 (fr + 2624) /\ spill regs m 216 (fr + 448) /\
       MEM.bytes_at segs m (fr + 448) (SM.t_B (c_in cx) j) /\
       ART.addressable m (fr + 452) 6 /\ ART.addressable m (fr + 2624) 6 /\
       spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       spill regs m 192 (fr + 528) /\ (forall e, SM.t_cls (c_in cx) j = Some e -> u32 m (fr + 528) e) /\
       PT32 cx j phi fr regs m /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82b38_at j: Inv_B82b38_at, SlotInv.v:2998 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82b38, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82b38_at : ctlcut := mkCtlCut
  0x82b38
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       FTK cx j fr regs m /\
       SM.t_cls (c_in cx) j <> None /\
       (lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (SM.t_B (c_in cx) j)) = SM.OUR (c_in cx)) /\
       spill regs m 184 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ rgv regs 25 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       spill regs m 192 (fr + 528) /\ (forall e, SM.t_cls (c_in cx) j = Some e -> u32 m (fr + 528) e) /\
       PT32 cx j phi fr regs m /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82b5c_at j: Inv_B82b5c_at, SlotInv.v:3011 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82b5c, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82b5c_at : ctlcut := mkCtlCut
  0x82b5c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       FTK cx j fr regs m /\
       PT32 cx j phi fr regs m /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82bcc_at j: Inv_B82bcc_at, SlotInv.v:3023 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82bcc, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82bcc_at : ctlcut := mkCtlCut
  0x82bcc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       FTK cx j fr regs m /\
       SM.t_rowsel (c_in cx) j = true /\
       rgv regs 10 SM.CAT /\ rgv regs 23 (fr + 32) /\ q64 m (fr + 32) 11 /\
       rgv regs 18 phi /\ rgv regs 20 (SM.t_len (c_in cx) j) /\ spill regs m 152 (fr + 64) /\
       MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
       (Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\ spill regs m 160 (fr + 32) /\
       FRM.stk segs m fr (fr + FRAME_BYTES) /\
       spill regs m 312 (phi + 18) /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82bf4_at j i: Inv_B82bf4_at, SlotInv.v:3044 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82bf4, index [j; i], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82bf4_at : ctlcut := mkCtlCut
  0x82bf4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       rgv regs 22 1 /\ (i = 0%nat -> rgv regs 24 (SM.t_k (c_in cx) j)) /\
       spill regs m 272 (SM.t_k (c_in cx) j) /\ True  /\
       RL cx j i phi fr regs m /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82c24_at j i: Inv_B82c24_at, SlotInv.v:3086 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82c24, index [j; i], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82c24_at : ctlcut := mkCtlCut
  0x82c24
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ (i <= 10)%nat /\
    spill regs m 272 (SM.t_k (c_in cx) j) /\ True  /\
    RLc cx j i phi fr regs m /\ rgv regs 10 1 /\
    MEM.bytes_at segs m (fr + 64) (SM.decl_i (Z.of_nat i)) /\ ART.addressable m (fr + 64) 32 /\
    IFS cx fr (S j) regs m)).

(* B82c38_at j i: Inv_B82c38_at, SlotInv.v:3100 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82c38, index [j; i], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82c38_at : ctlcut := mkCtlCut
  0x82c38
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\ (i <= 10)%nat /\
    spill regs m 272 (SM.t_k (c_in cx) j) /\ True  /\
    RLc cx j i phi fr regs m /\
    (lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 0 <-> SM.t_blk (c_in cx) j = SM.decl_i (Z.of_nat i)) /\
    MEM.bytes_at segs m (fr + 64) (SM.decl_i (Z.of_nat i)) /\ ART.addressable m (fr + 64) 32 /\
    IFS cx fr (S j) regs m)).

(* B82c84_at j: Inv_B82c84_at, SlotInv.v:3057 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82c84, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82c84_at : ctlcut := mkCtlCut
  0x82c84
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       spill regs m 272 (SM.t_k (c_in cx) j) /\ True  /\
       SM.t_want_m (c_in cx) j = 0 /\ PTL cx j phi fr regs m /\
       FTURN cx j phi regs m /\ IFS cx fr (S j) regs m /\ rgv regs 22 1).

(* B82c90_at j: Inv_B82c90_at, SlotInv.v:3072 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82c90, index [j], k <= 14+2j+1, own6, piece W4f
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`)
   DROPPED here, one conjunct: ctrl's `~ AC.a_in_fs AC.ASYMS m phi` (the turn's block is not in the
   FakeStack).  RESTATED by the core's world (a Theorem Labs lane 21:52Z): a live block's bytes are apresent and not
   aowned (AR_blocks_law, donor YG0d.v:422-428) while a fake-stack frame is owned, so a stage that needs it
   derives it from the journal *)
Definition C_B82c90_at : ctlcut := mkCtlCut
  0x82c90
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ LK cx fr j regs m /\
       SM.t_want_m (c_in cx) j = 0 /\
       PT32 cx j phi fr regs m /\
       FTK cx j fr regs m /\ FTURN cx j phi regs m /\ IFS cx fr (S j) regs m).

(* B82ca0_at j: Inv_B82ca0_at, SlotInv.v:3196 (shell FCUTP :2263 → CUTST :433 (FRA :330 + ENT :371)); pc 0x82ca0, index [j], k <= 14+2j+1, own6, piece W4g
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl hb stores `AC.a_size (flen g j)`) *)
Definition C_B82ca0_at : ctlcut := mkCtlCut
  0x82ca0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     fcutp_body cx j bl fr regs m (fun phi fr regs m =>
       LK cx fr j regs m /\
    spill regs m 272 (SM.t_k (c_in cx) j) /\ True  /\
    rgv regs 10 (SM.t_want (c_in cx) j) /\ rgv regs 23 (SM.t_want_m (c_in cx) j) /\
    rgv regs 18 phi /\ rgv regs 20 (SM.t_len (c_in cx) j) /\ spill regs m 152 (fr + 64) /\
    spill regs m 160 (fr + 32) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
    (Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
    FRM.stk segs m fr (fr + FRAME_BYTES) /\
    SM.t_want (c_in cx) j = SM.t_want_m (c_in cx) j /\
    IFS cx fr (S j) regs m /\ rgv regs 22 1)).

(* B82d1c_at j: Inv_B82d1c_at, SlotInv.v:3213 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82d1c, index [j], k <= 14+2j+2, own6, piece W4g
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B82d1c_at : ctlcut := mkCtlCut
  0x82d1c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 2)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ LK cx fr j regs m /\
    spill regs m 272 (SM.t_k (c_in cx) j) /\ True  /\
    spill regs m 224 (c_p cx + SM.t_body (c_in cx) j) /\
    rgv regs 21 (Z.of_nat j) /\
    rgv regs 23 (c_p cx + SM.t_body (c_in cx) j + SM.t_len (c_in cx) j) /\
    rgv regs 25 (SM.t_left (c_in cx) j - SM.t_h (c_in cx) j - SM.t_len (c_in cx) j) /\
    IFS cx fr (S j) regs m /\ rgv regs 22 1).

(* B82eac: Inv_B82eac, SlotInv.v:3336 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82eac, index [], k <= 526 (≤ EV_LIB; max: S_P12 14, S_F1 14+2j [dead edge, Notes], S_F38 14+2·255+2 = 526 with j ≤ 255 from LK SIv:1019), own6, piece W5
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B82eac : ctlcut := mkCtlCut
  0x82eac
  own6
  (fun _ _ => B.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\
    spill regs m 176 (fr + 2688) /\
    (exists nm, MEM.bytes_at segs m (fr + 2688) nm /\ length nm = 21%nat /\
       SFA.find_byte 0 (firstn 17 (skipn 3 nm)) <> None) /\
    ART.addressable m (fr + 2691) 17).

(* B82ecc: Inv_B82ecc, SlotInv.v:3344 (shell CUTST :433 (FRA :330 + ENT :371)); pc 0x82ecc, index [], k <= 526 (≤ EV_LIB), own6, piece W5
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (s5 = fr)
   live list (table): entry blocks *)
Definition C_B82ecc : ctlcut := mkCtlCut
  0x82ecc
  own6
  (fun _ _ => B.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ (exists q, a0v regs q /\ 0 < q < 2 ^ 64)).

(* Jrel: Inv_Jrel, SlotInv.v:3358 (shell CUTST0 :489 (FRAS :482 = FRAH :447 + ENT :371)); pc 0x82f2c, index [], k <= 526 (≤ EV_LIB); 0 on the dead S_A4 edge, own6, piece W5
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): class-full arm discharged by the model law at the fake-stack call, not walked; own resolves to own6 = [(6,fpos)] (sel = fr); S_Jrel's sel = 0 exit to B82f58 is therefore not taken
   live list (table): entry blocks *)
Definition C_Jrel : ctlcut := mkCtlCut
  0x82f2c
  own6
  (fun _ _ => B.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x41b58ab3 regs m /\
     rgv regs 24 sel /\ rgv regs 25 fr).

(* B82f48: Inv_B82f48, SlotInv.v:3364 (shell CUTSTR :495 (FRAR :485 = FRAH :447 + ENT :371)); pc 0x82f48, index [], k <= 526 (≤ EV_LIB), own6, piece W5
   live list (table): entry blocks *)
Definition C_B82f48 : ctlcut := mkCtlCut
  0x82f48
  own6
  (fun _ _ => B.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x45e0360e regs m /\
     sel = fr /\ a0v regs fr /\ rgv regs 11 FRAME_BYTES).

(* B82f58: Inv_B82f58, SlotInv.v:3369 (shell CUTSTR :495 (FRAR :485 = FRAH :447 + ENT :371)); pc 0x82f58, index [], k <= 526 (≤ EV_LIB), own0, piece W5
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): this cut lies on the discharged class-full arm (S_Jrel's sel = 0 exit, beqz s8 at 0x82f38); with sel = fr it has no live producer and is not walked
   live list (table): entry blocks
   NO RECORD (a Theorem Labs lane 21:52Z).  This is the release join of the CLASS-FULL REAL-STACK arm (ctrl's selector 0).
   That arm is not a live case: the stage at the fake-stack call discharges the machine's s8 = 0 branch from
   astack_malloc_realizes (donor YG0d.v:284-299) and stack_malloc_progress (YG05.v:69-84), since frames S = []
   at the entry.  No stage reaches this pc and the composition must not name it, so the row is transcribed as
   this note and NOT as a ctlcut.  Its ctrl text, for the record: Inv_B82f58 SlotInv.v:3369,
   CUTSTR 0x82f58 with `sel = 0 /\ a0v regs (Sfr fr) /\ rg regs 11 FRAME_SHADOW`. *)

(* B82f5c: Inv_B82f5c, SlotInv.v:3380 (shell own (no FRA): RT, aa_AH (g_H g), ro_agree, sink_none, saved regs, window, ENT :371 inline (:3383-3389)); pc 0x82f5c, index [], k <= 526 (≤ EV_LIB), own0, piece W5
   superseded: hands brief (a working note, not in this delivery) (a Theorem Labs lane 21:44Z; A-plan (a working note, not in this delivery) 21:30Z): the 'never taken' alternative of own is dead; own = [] after the release by __asan_stack_free_6 @0x82f48 (S_Y1); S_Y2's edge into this cut is on the discharged arm
   live list (table): entry blocks *)
Definition C_B82f5c : ctlcut := mkCtlCut
  0x82f5c
  own0
  (fun _ _ => B.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     rgv regs 8 (c_sp cx) /\ lib.Reusable.YK11.getr regs 3 = lib.Reusable.YK11.getr (c_regs cx) 3 /\ lib.Reusable.YK11.getr regs 4 = lib.Reusable.YK11.getr (c_regs cx) 4 /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx)).

End CtlCutP.
