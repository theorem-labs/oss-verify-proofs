(* lib/A/ACtlCutP.v -- the 100 cut bodies of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput, transcribed
   from ctrl's own cut text against the fixed interface of lib/A/ACtlCut.v.  Written by a Theorem Labs lane's
   transcription lane (a Theorem Labs lane); single writer.  DEFINITIONS ONLY: no Lemma, no Axiom, no Parameter, no
   Admitted, no tactic.

   WHAT THIS FILE IS
   ctrl's cut text of record is lib/A/Prog/SlotInv.v at d5e20dfd330 (3114 lines).  Its shells (FRA :334,
   FRAH :448, ENT :378, CUTST :436, CUTST0 :490, CUTSTR :496, PREF :943) speak the Theorem Labs lane frame vocabulary this
   walk replaces, so they are NOT transcribed: ACtlCut.v's ctl_base (the core's own lib pre), ctl_from and
   ctl_rt state them in the donor's form (the translation section of
   llvmf-cgif-walk-plan.md section 2.1 (a working note, not in this delivery)).  What IS transcribed is every cut's own
   register / memory predicate and the body bundles those predicates call, verbatim.  Each record is named
   C_<cut> after the cut column of v190/cut-table-A.tsv (a working note, not in this delivery) with the index
   letters dropped from the name (they are the record's idx argument): row "A815cc_at b" is C_A815cc_at.

   RULE 24 (released proofs first).  proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28
   20:16:23Z from e966c513ee6, ossv/recipes@a8831f7c5c): 30 files named for it, 1290 uses of its address,
   105 related; released proofs for seven other units, as ASan for bluez/fuzz_hci and for the donor
   cgif/cgif_file_fuzzer.  Second-agent check a Theorem Labs lane, 21:10Z: CONFIRM -- cgif is the only released ASan
   donor matching this unit on branch (ossv/recipes), LPS (2afba80c) and framework (afn_pre / ajournal); the
   donor's constants are A/ACfn.v:20-25.  This file restates ctrl's cut text against that donor's form.

   FIELD MAP (brief cutp-transcribe.md), applied to every body:
     g_p g -> c_p cx    g_n g -> c_n cx    g_in g -> c_in cx    g_regs g -> c_regs cx
     g_mem g -> c_mem cx    g_md g -> c_md cx    g_S g -> c_sp cx    rg -> ACtlCut.rgv
     AC.aspZ -> Reusable.YG0d.spZ    ASAN_K -> A.ACtlK.ASAN_K
   g_H and g_T have no counterpart.  A conjunct naming the live-heap ghost g_H becomes the body's own
   Permutation of bl (the live list ACtlCut.v hands the body) against the entry blocks; a conjunct naming the
   kept-block ghost g_T is dropped (plan 2.1, rows "ENT T subset H" and "DROP").  asan_cells / shadow_rw /
   ro_agree are dropped wherever a body names them: ctl_rt carries those three (plan 2.1, "Body bundles": PRO,
   f1_IN, FLV, f14_tail, FSREC).  mem_inv is dropped wherever a body names it and is NOT carried (ProgWorld
   00:34Z, accepted by a Theorem Labs lane: the core's world gives it no source).  The CUTST / CUTST0 / CUTSTR / b5_CUT / B7CUT wrapper is
   dropped with its configuration equation; CUTST0's and CUTSTR's selector becomes the body's sel argument.
   Every dropped conjunct is listed, record by record, in the transcription report.

   ctrl's OWN READERS, TRANSCRIBED HERE (ACtlCut.v keeps only rgv and a0v): q64 / u32 / u16 / b8 (SlotInv.v
   :282-285), Sfr (:296) and spill (:786-787), over lib/Lib's memory predicates, qualified, and AsanRT's
   shadow_addr.  ctrl writes them against the image's segment list rsegs; this file writes them against the
   walk's segs (the same image's list under the core's name), so lib/A/Img0.v is NOT in the closure.  If the
   core's segs is not definitionally ctrl's rsegs, that is one bridge lemma in lib/A/ProgBridge.v, not an edit
   here -- it is the only place the two lists meet.

   SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): getr, mkst, seg_rom exist in BOTH lib/Lib and the core's
   YK11 and DIFFER (lib/Lib's mkst empties the FP registers), so a file can build green and be wrong.  Every
   one of them here is Reusable.YK11.* (cfg_at: Reusable.YG0d.cfg_at), lib/Lib is never Imported, and lib/Lib
   is used only for the memory predicates (bytes_at, rw_cells / CB, addressable, stk, mbyte).  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlCutP.v
   Output: (empty -- no hit outside this comment).

   THE FAKE-STACK ARM (two Theorem Labs lanes, 21:29Z-21:30Z, ACtlCut.v section 3): the class-full arm,
   where __asan_stack_malloc_6 would return 0, is not a live case in the model -- at the entry frames S = [],
   so the room premise holds, astack_malloc_realizes has only the frame_addr outcome (YG0d.v:284-299) and
   stack_malloc_progress rules the null result out (YG05.v:69-84).  The stage at the fake-stack call discharges
   the machine's s5 = 0 branch from that law.  So every cut from the frame's allocation to its release owns the
   class-6 frame (own6), ENTRY and the post-release cuts own nothing (own0), and the shell passes sel = fr.

   MODULES THIS FILE REQUIRES (complete; no project module is Imported or Exported, every project name is fully
   qualified through the Module aliases below, so the auditor's check is
     grep -nE 'Require (Import|Export)' lib/A/ACtlCutP.v
   whose only two hits are the Coq stdlib line (ZArith List Permutation) and the LPS line (BvBase
   RiscvSemantics MemImageType State Run), as in ACtlCut.v and the donor's A/ACfn.v.)

     lib/Reusable/YK11.v                        the core's getr (shadowed name, always qualified)
     lib/Reusable/YA0n.v YG00.v YG01.v YG0f.v   the core's world / state / frames / layout vocabulary
     lib/Reusable/YG0n.v YG0d.v                 the core's blocks (ablocks) and spZ
     lib/Reusable/YC5d.v YCbq.v YM05.v          the core's meter, journal, run ceiling (this Section's shape)
     lib/Reusable/YK18.v YO09.v YI16.v          the core's realizes / lib shape / sink head (this Section's shape)
     lib/A/AB1v.v                               the core's segment list tfibsegs (segs)
     lib/A/ACfn.v                               the core's lib contract (A_LLVMF, RA_LLVMF)
     lib/A/ACtlK.v                              this walk's internal names (a Theorem Labs lane)
     lib/A/ACtlCut.v                            this walk's cut interface (a Theorem Labs lane)
     lib/A/AsanRT.v                             addressable, app_mem, end_in_app, APPMEM_END, shadow_addr,
                                                RT_LO / RT_HI and the runtime cells of rt_disjoint
     lib/A/AsanRTFacts.v                        all_app (one body: C_A81b80)
     lib/Lib/Mem.v Cells.v Step.v Frame.v       memory predicates only (porter 21:33Z), never Imported
     lib/A/Prog/SlotModel.v                     pure model (no frame vocabulary)
     lib/Prog/RcModel.v RcIdentModel.v RcFrag.v RcReply.v RcLeaf.v RcDecl.v RcParse.v RcPorts.v RcKind.v
       RcClassify.v                             pure models (no frame vocabulary)
     lib/A/Prog/reac_ctrl_kind_name_c.v         QMARK, kind_name_addr, kind_name_strings, KIND_NAME
     lib/A/Prog/bcmp_wrap_c.v memcmp_c.v        BCMP / REAL_BCMP / REAL_MEMCMP / GOT_CF / CF, MEMCMP
     lib/A/Prog/reac_box_catalogue_c.v          BOX_CATALOGUE
     lib/A/Prog/reac_ctrl_identity_fragment_c.v fg_mem, REAC_CTRL_IDENTITY_FRAGMENT_K
     lib/A/Prog/asan_memset_c.v                 ASAN_MEMSET_K (one body: C_A81b80)
     lib/A/Spec/StrFun.v                        memcmp_model, find_byte
   REAC_CTRL_IDENTITY_REPLY_K and REAC_CTRL_PARSE_BC are Section Variables, not Requires (see below).

   NOT required, and never to be: lib/A/Prog/SlotInv.v, lib/AZ/**, lib/AZ/AS/SpinAlg.v (not in this delivery), lib/A/Contract.v,
   lib/A/FrameAPI.v, lib/A/W6.  (a Theorem Labs lane's ruling, 21:29Z / 21:33Z: the landing list targets the FRAME
   route, not ctrl's pure input model or lib/Lib's memory predicates; Require without Import, fully qualified,
   is allowed.)

   CLOSURE, MEASURED FROM THIS FILE'S OWN REQUIRES (not assumed; the earlier scan started at SlotModel.v only
   and so missed this file's other 28 roots -- the composition lane found an AsanRTInv.v Require that way,
   22:01Z).  Command, run in proofs/libreac/fuzz_ctrl; it reads EVERY `From <prefix> Require [Import|Export]
   <names>.` AND EVERY absolute `Require [Import|Export] <qualids>.` of lib/A/ACtlCutP.v (batch 4, item B5.5: the
   six twin Reusable modules and the Bz-twinned lib/Lib modules are Required in the absolute form, which the
   From-only scan did not read), follows only names under OSSVerify.Proofs.libreac.fuzz_ctrl, and handles
   dotted module names (Reusable.YK11), which the first scan's regex did not:

     python3 - <<'EOF'
     import re,os,collections
     ROOT='OSSVerify.Proofs.libreac.fuzz_ctrl.'
     RE=re.compile(r'From\s+([\w.]+)\s+Require\s+((?:Import|Export)\s+)?([\w.\s]+?)\.(?=\s)',re.S)
     RA=re.compile(r'(?m)^\s*Require\s+((?:Import|Export)\s+)?([\w.\s]+?)\.(?=\s)')
     def path_of(m):
       p=m.replace('.','/')+'.v'
       return p if os.path.exists(p) else None
     def reqs(p):
       t=open(p).read()
       return ([(m.group(1),n) for m in RE.finditer(t) for n in m.group(3).split()] +
               [(n.rsplit('.',1)[0],n) for m in RA.finditer(t) for n in m.group(2).split()])
     def resolve(pref,n):
       if n.startswith(ROOT): return path_of(n[len(ROOT):])
       return path_of((pref[len(ROOT):]+'.'+n) if pref.startswith(ROOT) else n)
     q=[resolve(a,b) for a,b in reqs('lib/A/ACtlCutP.v') if a.startswith('OssFuzz')]
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
     FORB=['Prog/SlotInv.v','/AZ/','AsanRTInv.v','/A/Contract.v','FrameAPI.v','SpinAlg','/W6/','MemNorm.v','/A/Reusable/']
     print(len(files)); [print(' ',f) for f in sorted(files)]
     print('FORBIDDEN:',[f for f in sorted(files) if any(k in '/'+f for k in FORB)])
     print('NOT YET ON DISK (the core):',sorted(miss)); print('EXT:',sorted(ext))
     EOF

   Output (measured after batch 4 on the glue base, the tree of this commit): 278 files, and the line that matters --
     FORBIDDEN: 62 files (listed below)
   all reached through ONE edge: lib/A/Prog/bcmp_wrap_c.v:59 `From ...lib.A Require Contract.` (its IMG_HI is
   Contract.GT), from lib/A/Contract.v on to lib/A/MemNorm.v and lib/A/Reusable/*.  The earlier output here
   (206 files, FORBIDDEN: [], planning core 5a85b67a5d8) predates that Require.  The fixed scan's absolute-Require
   reading adds one file to the From-only scan's 277: lib/Img0.v.  The names it does not resolve on disk are
   Asan, OSSVerify.libreac.fuzz_ctrl.images.Asan, OSSVerify.libreac.fuzz_ctrl.images.Plain (the
   statements' generated image modules, outside proofs/).
   The 62 forbidden files:

     lib/A/Contract.v                                lib/A/MemNorm.v
     lib/A/Reusable/PlaceCap.v                       lib/A/Reusable/R/Cfg.v
     lib/A/Reusable/R/Place.v                        lib/A/Reusable/YK02.v
     lib/A/Reusable/YK0h.v                           lib/A/Reusable/YK0i.v
     lib/A/Reusable/YK0l.v                           lib/A/Reusable/YK0n.v
     lib/A/Reusable/YK0o.v                           lib/A/Reusable/YK0q.v
     lib/A/Reusable/YK0s.v                           lib/A/Reusable/YK0v.v
     lib/A/Reusable/YK10.v                           lib/A/Reusable/YK11.v
     lib/A/Reusable/YK14.v                           lib/A/Reusable/YK15.v
     lib/A/Reusable/YK16.v                           lib/A/Reusable/YK1a.v
     lib/A/Reusable/YK1b.v                           lib/A/Reusable/YK1c.v
     lib/A/Reusable/YK1d.v                           lib/A/Reusable/YK1i.v
     lib/A/Reusable/YK1j.v                           lib/A/Reusable/YL0g.v
     lib/A/Reusable/YM02.v                           lib/A/Reusable/YM03.v
     lib/A/Reusable/YM05.v                           lib/A/Reusable/YM06.v
     lib/A/Reusable/YM0b.v                           lib/A/Reusable/YO0d.v
     lib/A/Reusable/YO0f.v                           lib/A/Reusable/YO0g.v
     lib/A/Reusable/YO0h.v                           lib/A/Reusable/YO0i.v
     lib/A/Reusable/YO0q.v                           lib/A/Reusable/YO0s.v
     lib/A/Reusable/YO0t.v                           lib/A/Reusable/YO0u.v
     lib/A/Reusable/YO0v.v                           lib/A/Reusable/YO0w.v
     lib/A/Reusable/YO0x.v                           lib/A/Reusable/YO0y.v
     lib/A/Reusable/YO0z.v                           lib/A/Reusable/YO10.v
     lib/A/Reusable/YO11.v                           lib/A/Reusable/YO12.v
     lib/A/Reusable/YO13.v                           lib/A/Reusable/YO14.v
     lib/A/Reusable/YO15.v                           lib/A/Reusable/YO16.v
     lib/A/Reusable/YP09.v                           lib/A/Reusable/YP0e.v
     lib/A/Reusable/YP0m.v                           lib/A/Reusable/YZ00.v
     lib/A/Reusable/Z/MmapComplete.v                 lib/A/Reusable/Z/Placement.v
     lib/AZ/LibA/AcctCore.v                          lib/AZ/Spec/AsanCtrl.v
     lib/AZ/Spec/AsanCtrlProps.v                     lib/AZ/Spec/STree.v

   The 278 files:

     lib/A/AB1v.v                                    lib/A/ACfn.v
     lib/A/ACtlCut.v                                 lib/A/ACtlK.v
     lib/A/AE2k.v                                    lib/A/AsanLift.v
     lib/A/AsanRT.v                                  lib/A/AsanRTFacts.v
     lib/A/ClassConsDef.v                            lib/A/Contract.v
     lib/A/Img0.v                                    lib/A/MemNorm.v
     lib/A/Prog/ImgBounds.v                          lib/A/Prog/SlotModel.v
     lib/A/Prog/asan_memcpy_c.v                      lib/A/Prog/asan_memcpy_cF.v
     lib/A/Prog/asan_memset_c.v                      lib/A/Prog/bcmp_wrap_c.v
     lib/A/Prog/memcmp_c.v                           lib/A/Prog/reac_box_catalogue_c.v
     lib/A/Prog/reac_ctrl_identity_fragment_c.v      lib/A/Prog/reac_ctrl_kind_name_c.v
     lib/A/Prog/rng_asan.v                           lib/A/Reusable/PlaceCap.v
     lib/A/Reusable/R/Cfg.v                          lib/A/Reusable/R/Place.v
     lib/A/Reusable/YK02.v                           lib/A/Reusable/YK0h.v
     lib/A/Reusable/YK0i.v                           lib/A/Reusable/YK0l.v
     lib/A/Reusable/YK0n.v                           lib/A/Reusable/YK0o.v
     lib/A/Reusable/YK0q.v                           lib/A/Reusable/YK0s.v
     lib/A/Reusable/YK0v.v                           lib/A/Reusable/YK10.v
     lib/A/Reusable/YK11.v                           lib/A/Reusable/YK14.v
     lib/A/Reusable/YK15.v                           lib/A/Reusable/YK16.v
     lib/A/Reusable/YK1a.v                           lib/A/Reusable/YK1b.v
     lib/A/Reusable/YK1c.v                           lib/A/Reusable/YK1d.v
     lib/A/Reusable/YK1i.v                           lib/A/Reusable/YK1j.v
     lib/A/Reusable/YL0g.v                           lib/A/Reusable/YM02.v
     lib/A/Reusable/YM03.v                           lib/A/Reusable/YM05.v
     lib/A/Reusable/YM06.v                           lib/A/Reusable/YM0b.v
     lib/A/Reusable/YO0d.v                           lib/A/Reusable/YO0f.v
     lib/A/Reusable/YO0g.v                           lib/A/Reusable/YO0h.v
     lib/A/Reusable/YO0i.v                           lib/A/Reusable/YO0q.v
     lib/A/Reusable/YO0s.v                           lib/A/Reusable/YO0t.v
     lib/A/Reusable/YO0u.v                           lib/A/Reusable/YO0v.v
     lib/A/Reusable/YO0w.v                           lib/A/Reusable/YO0x.v
     lib/A/Reusable/YO0y.v                           lib/A/Reusable/YO0z.v
     lib/A/Reusable/YO10.v                           lib/A/Reusable/YO11.v
     lib/A/Reusable/YO12.v                           lib/A/Reusable/YO13.v
     lib/A/Reusable/YO14.v                           lib/A/Reusable/YO15.v
     lib/A/Reusable/YO16.v                           lib/A/Reusable/YP09.v
     lib/A/Reusable/YP0e.v                           lib/A/Reusable/YP0m.v
     lib/A/Reusable/YZ00.v                           lib/A/Reusable/Z/MmapComplete.v
     lib/A/Reusable/Z/Placement.v                    lib/A/Spec/StrFun.v
     lib/AZ/LibA/AcctCore.v                          lib/AZ/Spec/AsanCtrl.v
     lib/AZ/Spec/AsanCtrlProps.v                     lib/AZ/Spec/STree.v
     lib/AllocBound.v                                lib/AllocCount.v
     lib/AllocDepth.v                                lib/AllocFree.v
     lib/AllocFreeMB.v                               lib/AllocFreePath.v
     lib/AllocGS.v                                   lib/AllocMB.v
     lib/AllocMalloc.v                               lib/AllocMallocMB.v
     lib/AllocMallocPath.v                           lib/AllocRealloc.v
     lib/AllocReallocMB.v                            lib/AllocSI.v
     lib/AllocSlots.v                                lib/BWorld.v
     lib/Img0.v                                      lib/Lib/Acfg.v
     lib/Lib/AndN.v                                  lib/Lib/Arr.v
     lib/Lib/Bytes.v                                 lib/Lib/Ceiling.v
     lib/Lib/Cells.v                                 lib/Lib/ExN.v
     lib/Lib/Exec.v                                  lib/Lib/ExecF.v
     lib/Lib/FP.v                                    lib/Lib/Frame.v
     lib/Lib/Image.v                                 lib/Lib/LiaTwx2.v
     lib/Lib/MState.v                                lib/Lib/Mem.v
     lib/Lib/PropExec.v                              lib/Lib/RegisterBridge.v
     lib/Lib/Regs6ss.v                               lib/Lib/RngBytes.v
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
     lib/Reusable/R/Place.v                          lib/Reusable/YA0i.v
     lib/Reusable/YA0n.v                             lib/Reusable/YA0o.v
     lib/Reusable/YA0p.v                             lib/Reusable/YA0q.v
     lib/Reusable/YC5d.v                             lib/Reusable/YCbm.v
     lib/Reusable/YCbn.v                             lib/Reusable/YCbq.v
     lib/Reusable/YE00.v                             lib/Reusable/YE01.v
     lib/Reusable/YG00.v                             lib/Reusable/YG01.v
     lib/Reusable/YG02.v                             lib/Reusable/YG03.v
     lib/Reusable/YG04.v                             lib/Reusable/YG06.v
     lib/Reusable/YG07.v                             lib/Reusable/YG08.v
     lib/Reusable/YG09.v                             lib/Reusable/YG0a.v
     lib/Reusable/YG0d.v                             lib/Reusable/YG0f.v
     lib/Reusable/YG0n.v                             lib/Reusable/YG0p.v
     lib/Reusable/YG0q.v                             lib/Reusable/YG0s.v
     lib/Reusable/YG0v.v                             lib/Reusable/YI00.v
     lib/Reusable/YI04.v                             lib/Reusable/YI08.v
     lib/Reusable/YI09.v                             lib/Reusable/YI0t.v
     lib/Reusable/YI16.v                             lib/Reusable/YImgTop.v
     lib/Reusable/YK02.v                             lib/Reusable/YK04.v
     lib/Reusable/YK05.v                             lib/Reusable/YK06.v
     lib/Reusable/YK08.v                             lib/Reusable/YK0g.v
     lib/Reusable/YK0h.v                             lib/Reusable/YK0i.v
     lib/Reusable/YK0j.v                             lib/Reusable/YK0k.v
     lib/Reusable/YK0l.v                             lib/Reusable/YK0m.v
     lib/Reusable/YK0n.v                             lib/Reusable/YK0o.v
     lib/Reusable/YK0p.v                             lib/Reusable/YK0q.v
     lib/Reusable/YK0s.v                             lib/Reusable/YK0t.v
     lib/Reusable/YK0v.v                             lib/Reusable/YK0w.v
     lib/Reusable/YK0z.v                             lib/Reusable/YK10.v
     lib/Reusable/YK11.v                             lib/Reusable/YK14.v
     lib/Reusable/YK15.v                             lib/Reusable/YK16.v
     lib/Reusable/YK18.v                             lib/Reusable/YK1a.v
     lib/Reusable/YK1b.v                             lib/Reusable/YK1c.v
     lib/Reusable/YK1d.v                             lib/Reusable/YK1e.v
     lib/Reusable/YK1g.v                             lib/Reusable/YK1i.v
     lib/Reusable/YM00.v                             lib/Reusable/YM02.v
     lib/Reusable/YM03.v                             lib/Reusable/YM04.v
     lib/Reusable/YM05.v                             lib/Reusable/YM06.v
     lib/Reusable/YM0b.v                             lib/Reusable/YN32.v
     lib/Reusable/YN3v.v                             lib/Reusable/YO00.v
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
     lib/Reusable/YP00.v                             lib/Reusable/YP01.v
     lib/Reusable/YP02.v                             lib/Reusable/YP03.v
     lib/Reusable/YP04.v                             lib/Reusable/YP06.v
     lib/Reusable/YP08.v                             lib/Reusable/YP09.v
     lib/Reusable/YP0e.v                             lib/Reusable/YP0f.v
     lib/Reusable/YP0g.v                             lib/Reusable/YP0i.v
     lib/Reusable/YP0j.v                             lib/Reusable/YP0k.v
     lib/Reusable/YP0l.v                             lib/Reusable/YP0m.v
     lib/Reusable/YP0n.v                             lib/Reusable/YZ00.v
     lib/Reusable/Z/MmapComplete.v                   lib/Reusable/Z/Placement.v

   THREE ROOTS WERE REMOVED (a Theorem Labs lane 22:01Z), which cleared the scan on the planning core:
     lib/A/AsanRTInv.v      FORBIDDEN itself.  Its only use here was rt_disjoint, in C_A81b80's memset window;
                            restated above from AsanRTInv.v:12-20 over AsanRT.v's constants and lib/Lib's
                            disjoint_from.  No other conjunct of AsanRTInv is named by any body; the three
                            ctl_rt facts come from ACtlCut.ctl_rt, not from here.
     lib/A/Reusable/YP09.v  FORBIDDEN (the ASan-side lib/A/Reusable).  It had ZERO uses in the code: its two
                            names, writable_at and mbyte, appear only in shell conjuncts that section 2.1
                            drops, so the Require was dead.  Removed with its alias.
     lib/A/Prog/reac_ctrl_identity_reply_c.v and reac_ctrl_parse_c.v
                            allowed by name but FORBIDDEN BY CLOSURE: each reaches lib/AZ/LibA/AcctCore.v.
                            Their two constants are now Section Variables (above).
   The other seven callee contract files stayed: measured clean then (bcmp_wrap_c 21 files, memcmp_c 19,
   asan_memset_c 19, reac_box_catalogue_c 17, reac_ctrl_identity_fragment_c 25, reac_ctrl_kind_name_c 18,
   lib/A/Spec/StrFun.v 17, lib/A/AsanRTFacts.v 22 -- none reached a forbidden file).  bcmp_wrap_c has since gained
   `From ...lib.A Require Contract.` (bcmp_wrap_c.v:59), the one edge of the 62 forbidden files above; reported to the
   porter with batch 4.

   ONE-LINE SWAP.  Every model name here is reached through the Module alias SM (and the Rc* aliases).  If the
   porter rules the closure must be literally SlotModel-free, lib/A/ACtlM.v restates SlotModel.v's pure
   functions and ONE Require line plus ONE alias line change here; no record is touched.

   NAMES THIS FILE TAKES FROM A.ACtlK (its constants lane owns them; all four are defined there):
     A.ACtlK.ASAN_K     the shadow offset, for ctrl's inline shadow-byte conjuncts
     A.ACtlK.a_size     ctrl's AC.a_size (Contract.v:129): the allocator's block size for a request
                        (a_size 0 = 1), named only where a conjunct is about addressable bytes, i.e. in HB --
                        the live-block lists carry the REQUEST size, as the core's ablocks does
     A.ACtlK.ANMAX      ctrl's AC.ANMAX (Contract.v:50), the harness's maximum input length
     A.ACtlK.EV_LLVMF   the walk's measured event need, 526, which the six W5 rows use as their k bound
   The thread-pointer word and the frame header's entry word are NOT new names: they are Reusable.YG0f.as_tp B
   (the core's own symbol-bundle field, which its pre states) and A.ACfn.A_LLVMF.

   BUILD STATE (honest): the core is in this tree (lib/Reusable, lib/A/AE2k.v), and this file is built with it (lib/dune takes every .v file; lib/A/ACtl.v and lib/A/ACtlG/A1.v Require this file); before it landed this file was a labelled stand-in that TYPECHECKED on the image-A PLANNING core (a working branch
   5a85b67a5d8, merged on a working branch; TYPE-CHECK ONLY, its values did not count):
   `cb build` on the packed fuzz_ctrl base 362baf478bf5 (FACTS ed6b6b7b0ab, PAU pau-libreac-v190), with the
   core's undefined `port_core_refused_<hex>` names (lib/A/AE2k.v, which A.ACfn Imports) replaced by the hex
   literal in the build workspace only -- a core-file error, reported to the porter a Theorem Labs lane and never edited
   on this branch.  No Axiom, no Parameter, no Admitted. *)

From Coq Require Import ZArith List Permutation.
(* LPS's machine vocabulary (word, byte, bvmap, Model, Z_to_bv, ...) comes from LPS directly, as ACtlCut.v and
   the donor's A/ACfn.v do: YK11.v only Imports it, so `Reusable.YK11.word` does not resolve (composition lane,
   22:37Z).  Only the shadowed names getr / mkst / seg_rom / cfg_at stay YK11 / YG0d-qualified, and lib/Lib is
   never Imported. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v ACfn ACtlK ACtlCut.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AsanRT AsanRTFacts.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
(* the model, pure, Require only -- the ONE line lib/A/ACtlM.v would replace *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply RcLeaf RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcPorts RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_kind_name_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
Import ListNotations.
Local Open Scope Z_scope.

(* The model aliases (the swap point).  SM is ctrl's pure input model; the Rc* aliases are the target's own
   record / parse / reply / fragment models, which SlotModel is written over. *)
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
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
(* The memory vocabulary ctrl's bodies name and ACtlCut.v has no counterpart for.  Qualified use only. *)
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module CEL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module STP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
(* Program constants, under the aliases SlotInv.v itself uses. *)
Module KNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_kind_name_c.
Module BWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MCA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module CATA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module FGA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.
Module AMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c.
Module SFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.

(* The core's segment list, as ACtlCut.v takes it: a notation, not a Variable, so that `world segs` is the
   pre's type and not a new one (ACtlCut.v, 22:37Z; the donor's A/AB1v.v:11). *)
Local Notation segs := A.AB1v.tfibsegs.

Section CtlCutP.

(* The same Section shape as ACtlCut.v (its contexts and variables, in its order). *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}.
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

(* TWO CALLEE CONSTANTS, AS SECTION VARIABLES (a Theorem Labs lane 22:01Z).  ctrl's bodies name two sizes that live in callee
   contract files whose own closure reaches lib/AZ/LibA/AcctCore.v, which the porter forbids:
     REAC_CTRL_IDENTITY_REPLY_K   lib/A/Prog/reac_ctrl_identity_reply_c.v, the callee's stack need; C_A81bd8
     REAC_CTRL_PARSE_BC           lib/A/Prog/reac_ctrl_parse_c.v, the address of its .str.4 constant; C_A81bd8
   The core has no name for either yet, so they are Variables here: the one record that uses them takes them as
   arguments, and the stage that proves that cut gets them from the callee's spec (a Theorem Labs lane's ProgLift file
   for each callee), which is where the caller obligation is discharged anyway.  Nothing else in this file
   mentions them. *)
Variable REAC_CTRL_IDENTITY_REPLY_K : Z.
Variable REAC_CTRL_PARSE_BC : Z.

(* rt_disjoint, RESTATED here from lib/A/AsanRTInv.v:12-20 (a Theorem Labs lane 22:01Z: AsanRTInv.v is forbidden in a port
   file, and this is its only use -- C_A81b80's memset window).  Verbatim text, over AsanRT.v's runtime-cell
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
   frame loop, [j; i] for the four row cuts.  ctrl's bodies take b / j / i as nat and t as Z. *)
Definition ixn (k : nat) (idx : list Z) : nat := Z.to_nat (nth k idx 0).
Definition ixz (k : nat) (idx : list Z) : Z := nth k idx 0.

(* ---------------------------------------------------------------------------------------------------------
   1. The body predicates ctrl's cuts share, transcribed from SlotInv.v at d5e20dfd330 with their names kept.
   The first six are ctrl's own readers (:282-285, :296, :786-787), the rest are its cut bundles.  Each carries
   its source line; the conjuncts dropped from each are listed in the transcription report, bundle by bundle. *)

(* FRAME_BYTES, SlotInv.v:59 *)
Definition FRAME_BYTES : Z :=
  3136.

(* FRAME_SHADOW, SlotInv.v:60 *)
Definition FRAME_SHADOW : Z :=
  FRAME_BYTES / 8.

(* q64, SlotInv.v:282 *)
Definition q64 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a (MEM.le8 (Z_to_bv 64 v)).

(* u32, SlotInv.v:283 *)
Definition u32 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a (MEM.le4 (Z_to_bv 64 v)).

(* u16, SlotInv.v:284 *)
Definition u16 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a (MEM.le2 (Z_to_bv 64 v)).

(* b8, SlotInv.v:285 *)
Definition b8 (m : word -> option byte) (a v : Z) : Prop :=
  MEM.bytes_at segs m a [Z_to_bv 8 v].

(* saved_bytes, SlotInv.v:289 *)
Definition saved_bytes (cx : ctlcx) : list byte :=
  MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 27) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 26) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 25) ++
  MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 24) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 23) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 22) ++
  MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 21) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 20) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 19) ++
  MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 18) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 9) ++ MEM.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 8) ++ MEM.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF).

(* Sfr, SlotInv.v:296 *)
Definition Sfr (fr : Z) : Z :=
  ART.shadow_addr fr.

(* HB, SlotInv.v:771 *)
Definition HB (mem : word -> option byte) (phi len : Z) : Prop :=
  phi <> 0 /\ ART.addressable mem phi (A.ACtlK.a_size len).

(* rnb, SlotInv.v:772 *)
Definition rnb (cx : ctlcx) (b : nat) : Z :=
  SM.rt_n (c_in cx) (Z.of_nat b).

(* decl_slot, SlotInv.v:775 *)
Definition decl_slot (fr : Z) : Z :=
  fr + 2560.

(* spill, SlotInv.v:786 *)
Definition spill (regs : bvmap 5 word) (m : word -> option byte) (off v : Z) : Prop :=
  exists A, rgv regs 9 A /\ q64 m (A + off) v.

(* CUR, SlotInv.v:788 *)
Definition CUR (cx : ctlcx) (c : Z) (regs : bvmap 5 word) : Prop :=
  0 <= c <= c_n cx /\ rgv regs 22 (c_p cx + c) /\ rgv regs 25 (c_n cx - c).

(* OURb, SlotInv.v:790 *)
Definition OURb (cx : ctlcx) (fr : Z) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2624) (SM.OUR (c_in cx)).

(* PRO, SlotInv.v:805 *)
Definition PRO (cx : ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 40 (fr + 32) /\ spill regs m 120 (fr + 160) /\ spill regs m 136 (fr + 128) /\
  spill regs m 160 (fr + 528) /\ spill regs m 168 (fr + 2624) /\ spill regs m 176 (fr + 64) /\
  spill regs m 208 (fr + 448) /\ spill regs m 248 (fr + 176) /\
  ART.addressable m (fr + 2624) 6 /\
  MEM.bytes_at segs m (c_p cx) (c_in cx) /\
  (0 < c_n cx -> ART.addressable m (c_p cx) (c_n cx)) /\
  spill regs m 184 (fr + 336) /\ spill regs m 256 (fr + 256) /\ spill regs m 264 (fr + 304) /\
  spill regs m 272 (fr + 272) /\
  spill regs m 32 (fr + 2880).

(* OUTA, SlotInv.v:819 *)
Definition OUTA (fr : Z) (m : word -> option byte) : Prop :=
  ART.addressable m (fr + 544) 1492.

(* IDBr, SlotInv.v:820 *)
Definition IDBr (cx : ctlcx) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2176) idb.

(* FGBr, SlotInv.v:822 *)
Definition FGBr (cx : ctlcx) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2256) st.

(* IDBe, SlotInv.v:824 *)
Definition IDBe (cx : ctlcx) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2688) idb.

(* FGBe, SlotInv.v:826 *)
Definition FGBe (cx : ctlcx) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 2768) st.

(* RB, SlotInv.v:830 *)
Definition RB (cx : ctlcx) (fr : Z) (b : nat) (idb fgb : list byte) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b <= 6)%nat /\ CUR cx 7 regs /\ OURb cx fr m /\ rgv regs 23 (Z.of_nat b) /\ IDBr cx fr idb m /\ FGBr cx fr fgb m.

(* RS, SlotInv.v:832 *)
Definition RS (cx : ctlcx) (fr : Z) (b : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) regs m.

(* RFb, SlotInv.v:834 *)
Definition RFb (cx : ctlcx) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RB cx fr b idb fgb regs m /\ rnb cx b <> 0 /\ rgv regs 24 phi /\ MEM.bytes_at segs m phi (SM.rt_F (c_in cx) (Z.of_nat b)).

(* RFx, SlotInv.v:836 *)
Definition RFx (cx : ctlcx) (fr : Z) (b : nat) (idb fgb : list byte) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFb cx fr b idb fgb phi regs m /\ rgv regs 18 (rnb cx b).

(* RF, SlotInv.v:838 *)
Definition RF (cx : ctlcx) (fr : Z) (b : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RFx cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m.

(* RXS, SlotInv.v:855 *)
Definition RXS (cx : ctlcx) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 48 (fr + 2256) /\ spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\
  spill regs m 80 (fr + 2464) /\ spill regs m 72 (fr + 2496) /\
  spill regs m 8 (SM.mrow (c_in cx) + 16) /\ spill regs m 0 (SM.mrow (c_in cx) + 20) /\
  spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
  ART.addressable m (fr + 2256) 72.

(* IDb, SlotInv.v:864 *)
Definition IDb (cx : ctlcx) (fr : Z) (idb : list byte) (m : word -> option byte) : Prop :=
  IDBe cx fr idb m /\ RIM.id_ok idb.

(* FGb, SlotInv.v:866 *)
Definition FGb (cx : ctlcx) (fr : Z) (st : list byte) (m : word -> option byte) : Prop :=
  FGBe cx fr st m /\ SM.frag_ok st.

(* FSb, SlotInv.v:888 *)
Definition FSb (cx : ctlcx) (fr : Z) (s : SM.fstate) (st : list byte) (regs : bvmap 5 word) (m : word -> option byte) :
    Prop :=
  spill regs m 104 (SM.fs_have s) /\ spill regs m 112 (SM.fs_n s) /\
  MEM.bytes_at segs m (fr + 2880) (SM.fs_body s) /\ ART.addressable m (fr + 2880) 35 /\ SM.FI st s.

(* IDj, SlotInv.v:892 *)
Definition IDj (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  IDb cx fr (SM.t_ID (c_in cx) j) m.

(* FGj, SlotInv.v:893 *)
Definition FGj (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  FGb cx fr (SM.t_FG (c_in cx) j) m.

(* FSj, SlotInv.v:894 *)
Definition FSj (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FSb cx fr (SM.fst_at (c_in cx) j) (SM.t_FG (c_in cx) j) regs m.

(* IFS, SlotInv.v:896 *)
Definition IFS (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj cx fr j m /\ FGj cx fr j m /\ FSj cx fr j regs m.

(* LK, SlotInv.v:898 *)
Definition LK (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (j <= 255)%nat /\ rgv regs 21 (Z.of_nat j) /\ OURb cx fr m.

(* LI, SlotInv.v:900 *)
Definition LI (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK cx fr j regs m /\ CUR cx (SM.t_c (c_in cx) j) regs /\ 1 <= SM.t_left (c_in cx) j /\ IFS cx fr j regs m.

(* FC, SlotInv.v:902 *)
Definition FC (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 224 (SM.t_left (c_in cx) j - SM.t_h (c_in cx) j) /\ rgv regs 20 (c_p cx + SM.t_body (c_in cx) j) /\
  rgv regs 18 (SM.t_len (c_in cx) j).

(* FT, SlotInv.v:905 *)
Definition FT (cx : ctlcx) (fr : Z) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK cx fr j regs m /\ FC cx fr j regs m /\ rgv regs 23 phi /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j).

(* V7, SlotInv.v:907 *)
Definition V7 (cx : ctlcx) (j : nat) (regs : bvmap 5 word) : Prop :=
  rgv regs 24 (SM.t_k (c_in cx) j).

(* pBb, SlotInv.v:908 *)
Definition pBb (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m (fr + 176) (SM.t_B (c_in cx) j).

(* FB, SlotInv.v:910 *)
Definition FB (cx : ctlcx) (fr : Z) (j : nat) (phi : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FT cx fr j phi regs m /\ V7 cx j regs /\ rgv regs 25 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\ pBb cx fr j m.

(* PORTS, SlotInv.v:912 *)
Definition PORTS (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  (SM.t_rp (c_in cx) j = 0 ->
     u32 m (fr + 128) (4 * RLF.n_in (SM.t_pbs (c_in cx) j)) /\
     u32 m (fr + 132) (4 * RLF.n_out (SM.t_pbs (c_in cx) j)) /\
     u32 m (fr + 136) (16 * RLF.bt (SM.t_pbs (c_in cx) j) 7)) /\
  (SM.t_rp (c_in cx) j <> 0 -> u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7)).

(* FIRSTb, SlotInv.v:918 *)
Definition FIRSTb (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  b8 m (fr + 160) (SM.t_first (c_in cx) j).

(* fragb, SlotInv.v:927 *)
Definition fragb (fr : Z) : Z :=
  fr + 2768.

(* FLV, SlotInv.v:928 *)
Definition FLV (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 80 (fragb fr + 15) /\ spill regs m 88 (fragb fr + 19) /\ spill regs m 96 (fragb fr + 8) /\
  spill regs m 272 (fr + 272) /\ spill regs m 264 (fr + 304) /\
  (SM.t_rf (c_in cx) j = 1 ->
     q64 m (fr + 272) (fragb fr + 19) /\
     q64 m (fr + 304) (SM.f_pll (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j))).

(* X81640, SlotInv.v:1271 *)
Definition X81640 (cx : ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDBr cx fr (SM.RID (c_in cx) b) m /\ FGBr cx fr (SM.RFG (c_in cx) b) m /\
  MEM.bytes_at segs m (fr + 544) (SM.rt_F (c_in cx) (Z.of_nat b)) /\
  RXS cx fr regs m.

(* X81658, SlotInv.v:1296 *)
Definition X81658 (cx : ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RF cx fr b phi regs m /\ RXS cx fr regs m.

(* X81680, SlotInv.v:1313 *)
Definition X81680 (cx : ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  RF cx fr b phi regs m /\ RXS cx fr regs m /\
  a0v regs (SM.rt_k (c_in cx) (Z.of_nat b)) /\ rgv regs 27 4.

(* X816c4, SlotInv.v:1332 *)
Definition X816c4 (cx : ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (b = 3 \/ b = 4)%nat /\ a0v regs 1 /\ RF cx fr b phi regs m /\ RXS cx fr regs m /\
  STP.rw_cells segs m (fr + 2448) [CEL.CB 2 (RRP.reply_addr (SM.rt_g (c_in cx) (Z.of_nat b)))] /\
  STP.rw_cells segs m (fr + 2464) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (phi + 38)))] /\
  STP.rw_cells segs m (fr + 2496) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (RRP.ir_s (SM.rt_g (c_in cx) (Z.of_nat b)) - 13)))].

(* X81708, SlotInv.v:1353 *)
Definition X81708 (cx : ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  b = 6%nat /\ a0v regs 1 /\
  RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) (S b)) phi regs m /\ RXS cx fr regs m /\
  MEM.bytes_at segs m (fr + 2448)
    (MEM.le2 (Z_to_bv 64 (RFR.fg_addr (SM.RFG (c_in cx) b) (SM.rt_g (c_in cx) (Z.of_nat b))))) /\
  MEM.bytes_at segs m (fr + 2464) (MEM.le8 (Z_to_bv 64 (fr + 2256 + 19))) /\
  MEM.bytes_at segs m (fr + 2496)
    (MEM.le8 (Z_to_bv 64 (RFR.fg_T (SM.RFG (c_in cx) b) (SM.rt_g (c_in cx) (Z.of_nat b)) - 13))).

(* X81734, SlotInv.v:1381 *)
Definition X81734 (cx : ctlcx) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  a0v regs 1 /\ rgv regs 24 phi /\ RB cx fr b (SM.RID (c_in cx) (S b)) (SM.RFG (c_in cx) (S b)) regs m.

(* rsum, SlotInv.v:1409 *)
Definition rsum (cx : ctlcx) (b i : nat) : Z :=
  RMO.psum (skipn 18 (SM.rt_g (c_in cx) (Z.of_nat b))) i.

(* XC, SlotInv.v:1749 *)
Definition XC (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall A, rgv regs 9 A -> 0 <= A < 2 ^ 64 -> q64 m (A + 280) (fr + 3040)) /\
  ART.addressable m (fr + 3040) 1.

(* flen, SlotInv.v:1819 *)
Definition flen (cx : ctlcx) (j : nat) : Z :=
  SM.t_len (c_in cx) j.

(* f1_IN, SlotInv.v:1825 *)
Definition f1_IN (cx : ctlcx) (m : word -> option byte) : Prop :=
  ART.addressable m (c_p cx) (c_n cx) /\ MEM.bytes_at segs m (c_p cx) (c_in cx).

(* FLSH, SlotInv.v:1870 *)
Definition FLSH (cx : ctlcx) (j : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  PRO cx fr regs m /\
  spill regs m 128 (fr + 452) /\ FRM.stk segs m fr (fr + FRAME_BYTES) /\
  spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17.

(* FLC, SlotInv.v:1900 *)
Definition FLC (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 256 (fr + 256) /\ spill regs m 184 (fr + 336) /\ spill regs m 192 (fragb fr) /\
  spill regs m 80 (fragb fr + 15) /\ spill regs m 88 (fragb fr + 19) /\ spill regs m 96 (fragb fr + 8) /\
  spill regs m 272 (fr + 272) /\ spill regs m 264 (fr + 304) /\
  ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
  spill regs m 72 (fr + 186) /\ spill regs m 64 (fr + 180) /\
  spill regs m 56 (fr + 2889) /\ spill regs m 48 (fr + 2890).

(* FLSI, SlotInv.v:1907 *)
Definition FLSI (cx : ctlcx) (j : nat) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSH cx j fr regs m /\
  spill regs m 216 (c_p cx + SM.t_body (c_in cx) j) /\ spill regs m 224 (SM.t_left (c_in cx) j - SM.t_h (c_in cx) j) /\
  spill regs m 248 (fr + 176) /\ f1_IN cx m /\ FLC fr regs m.

(* FLS, SlotInv.v:1917 *)
Definition FLS (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSI cx j fr regs m /\
  rgv regs 18 (flen cx j) /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\ rgv regs 23 phi /\
  rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 25 (fr + 64) /\
  (50 <= flen cx j ->
     0 < phi /\ phi + 50 <= 2 ^ 64 /\
     MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\
     MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
     Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
  spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)).

(* FLSX, SlotInv.v:1935 *)
Definition FLSX (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSI cx j fr regs m /\
  rgv regs 18 (flen cx j) /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\ rgv regs 23 phi /\
  rgv regs 25 (fr + 64) /\
  (50 <= flen cx j ->
     0 < phi /\ phi + 50 <= 2 ^ 64 /\
     MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\
     MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
     Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
  spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)).

(* FLSF, SlotInv.v:1954 *)
Definition FLSF (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  FLSI cx j fr regs m /\
  rgv regs 18 (flen cx j) /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\ rgv regs 23 phi /\
  rgv regs 25 (fr + 64) /\
  (50 <= flen cx j -> 0 < phi /\ phi + 50 <= 2 ^ 64) /\
  spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)).

(* RL, SlotInv.v:1966 *)
Definition RL (cx : ctlcx) (j i : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (i <= 10)%nat /\ rgv regs 20 (SM.CAT + SM.CAT_ROW * Z.of_nat i) /\ rgv regs 24 (SM.CAT_N - Z.of_nat i) /\
  (forall i', (i' < i)%nat -> SM.t_blk (c_in cx) j <> SM.decl_i (Z.of_nat i')) /\
  SM.t_rowsel (c_in cx) j = true /\ FLSX cx j phi fr regs m.

(* LT, SlotInv.v:1976 *)
Definition LT (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IFS cx fr (S j) regs m.

(* ID1, SlotInv.v:1990 *)
Definition ID1 (cx : ctlcx) (j : nat) : list byte :=
  SM.rp_id (SM.t_ID (c_in cx) j) (flen cx j) (SM.t_g (c_in cx) j).

(* IDb1, SlotInv.v:1991 *)
Definition IDb1 (cx : ctlcx) (fr : Z) (j : nat) (m : word -> option byte) : Prop :=
  IDBe cx fr (ID1 cx j) m /\ RIM.id_ok (ID1 cx j).

(* IFS1, SlotInv.v:1993 *)
Definition IFS1 (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb1 cx fr j m /\ FGj cx fr j m /\ FSj cx fr j regs m.

(* IFS2, SlotInv.v:1995 *)
Definition IFS2 (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDb1 cx fr j m /\ FGj cx fr (S j) m /\ FSj cx fr j regs m.

(* IFS3, SlotInv.v:1997 *)
Definition IFS3 (cx : ctlcx) (fr : Z) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  IDj cx fr (S j) m /\ FGj cx fr (S j) m /\ FSj cx fr j regs m.

(* b5_sp, SlotInv.v:2024 *)
Definition b5_sp (regs : bvmap 5 word) (m : word -> option byte) (off v : Z) : Prop :=
  exists A, rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ q64 m (A + off) v.

(* b5_SPILL, SlotInv.v:2028 *)
Definition b5_SPILL (A fr : Z) (m : word -> option byte) : Prop :=
  q64 m (A + 248) (fr + 176) /\ q64 m (A + 256) (fr + 256) /\ q64 m (A + 144) (fr + 2688) /\
  q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\
  q64 m (A + 80) (fragb fr + 15) /\ q64 m (A + 88) (fragb fr + 19) /\ q64 m (A + 96) (fragb fr + 8) /\
  q64 m (A + 272) (fr + 272) /\ q64 m (A + 264) (fr + 304).

(* b5_FR, SlotInv.v:2035 *)
Definition b5_FR (cx : ctlcx) (j : nat) (fr : Z) (m : word -> option byte) : Prop :=
  ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
  MEM.bytes_at segs m (fragb fr) (SM.t_FG (c_in cx) j) /\ length (SM.t_FG (c_in cx) j) = 72%nat.

(* b5_RC, SlotInv.v:2040 *)
Definition b5_RC (fr : Z) (m : word -> option byte) : Prop :=
  ART.addressable m (fr + 256) 2 /\ ART.addressable m (fr + 272) 8 /\ ART.addressable m (fr + 304) 8.

(* b5_KN, SlotInv.v:2049 *)
Definition b5_KN (m : word -> option byte) : Prop :=
  MEM.bytes_at segs m KNA.KIND_NAME KNA.kind_name_bytes /\ ART.addressable m KNA.KIND_NAME 112.

(* b5_PH, SlotInv.v:2053
   DROPPED here, one conjunct: ctrl's `flen g j = 0 -> ~ AC.a_in_fs ASYMS m phi` (the empty-frame block is not
   in the FakeStack).  RESTATED by the core's world (a Theorem Labs lane 21:52Z): a live block's bytes are apresent and not
   aowned (AR_blocks_law, donor YG0d.v:422-428) while a fake-stack frame is owned, so a stage that needs it
   derives it from the journal *)
Definition b5_PH (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_g (c_in cx) j)) /\
  (50 <= flen cx j ->
     (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
     (phi + 50 <= Reusable.YG0d.spZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ Reusable.YG0d.spZ regs <= phi)).

(* rec_inv, SlotInv.v:2062 *)
Definition rec_inv (cx : ctlcx) (j : nat) (fr phi A : Z) (m : word -> option byte) : Prop :=
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ (50 <= flen cx j)%Z /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
  (forall a, phi <= a < phi + 50 -> ART.app_mem a) /\
  q64 m (A + 200) (phi + 18) /\
  MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
  MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
  (exists (field16 v14 v15 v16 v17 : Z),
     q64 m (A + 248) (fr + 176) /\ q64 m (A + 280) (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
     u16 m (fr + 176 + 20) field16 /\
     b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
     0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
     b8 m (Z.shiftr (phi + 14) 3 + A.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + A.ACtlK.ASAN_K) 0 /\
     b8 m (Z.shiftr (phi + 16) 3 + A.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + A.ACtlK.ASAN_K) 0 /\
     field16 = v14 + 256 * v15 /\
     (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if SM.t_k (c_in cx) j =? 1 then 1 else 0)).

(* rec_inv0, SlotInv.v:2085 *)
Definition rec_inv0 (cx : ctlcx) (j : nat) (fr phi A : Z) (m : word -> option byte) : Prop :=
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ (50 <= flen cx j)%Z /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
  (forall a, phi <= a < phi + 50 -> ART.app_mem a) /\
  q64 m (A + 200) (phi + 18) /\
  MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
  MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
  q64 m (A + 248) (fr + 176) /\ q64 m (A + 280) (SM.b2z (SM.t_sum_ok (c_in cx) j)).

(* rec_parse, SlotInv.v:2092 *)
Definition rec_parse (cx : ctlcx) (j : nat) (fr phi : Z) (m : word -> option byte) : Prop :=
  exists (field16 v14 v15 v16 v17 : Z),
    u16 m (fr + 176 + 20) field16 /\
    b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
    0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
    b8 m (Z.shiftr (phi + 14) 3 + A.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + A.ACtlK.ASAN_K) 0 /\
    b8 m (Z.shiftr (phi + 16) 3 + A.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + A.ACtlK.ASAN_K) 0 /\
    field16 = v14 + 256 * v15 /\
    (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if SM.t_k (c_in cx) j =? 1 then 1 else 0).

(* b5_C, SlotInv.v:2120 *)
Definition b5_C (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 23 phi /\ rgv regs 18 (flen cx j) /\
  (exists A, rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ b5_SPILL A fr m /\
     q64 m (A + 232) (if SM.t_big (c_in cx) j then 0 else 1)) /\
  b5_PH cx j phi fr regs m /\ b5_FR cx j fr m /\ b5_KN m /\
  FGj cx fr j m /\ FSj cx fr j regs m.

(* b5_K, SlotInv.v:2142 *)
Definition b5_K (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 20 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\
  rgv regs 24 (SM.t_k (c_in cx) j) /\
  rgv regs 25 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  b5_sp regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  u32 m (fr + 176) (SM.t_k (c_in cx) j) /\
  RRP.reply_args phi (fr + 256) (fr + 272) (fr + 304) = true.

(* b5_RPost, SlotInv.v:2151 *)
Definition b5_RPost (phi fr : Z) (G : list byte) (m : word -> option byte) : Prop :=
  STP.rw_cells segs m (fr + 256) [CEL.CB 2 (RRP.reply_addr G)] /\
  STP.rw_cells segs m (fr + 272) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (phi + 38)))] /\
  STP.rw_cells segs m (fr + 304) [CEL.CB 8 (MEM.le8 (Z_to_bv 64 (RRP.ir_s G - 13)))].

(* b5_F17, SlotInv.v:2167 *)
Definition b5_F17 (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ q64 m (A + 200) (phi + 18).

(* b5_W240, SlotInv.v:2171 *)
Definition b5_W240 (cx : ctlcx) (j : nat) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\
    exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
      (SM.t_8819 (c_in cx) j = true -> w240 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w240 = 0).

(* b5_PF, SlotInv.v:2192 *)
Definition b5_PF (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists A, rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\
    (50 <= flen cx j ->
       (exists rb, MEM.bytes_at segs m phi rb /\ (38 <= length rb)%nat) /\
       MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j)) /\
    (SM.t_8819 (c_in cx) j = true ->
       (exists (field16 v14 v15 v16 v17 : Z),
          u16 m (fr + 176 + 20) field16 /\
          b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
          0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
          b8 m (Z.shiftr (phi + 14) 3 + A.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + A.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 16) 3 + A.ACtlK.ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + A.ACtlK.ASAN_K) 0 /\
          field16 = v14 + 256 * v15 /\
          (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if SM.t_k (c_in cx) j =? 1 then 1 else 0)) /\
       (exists (ls rs : list byte),
          q64 m (A + 72) (fr + 186) /\ MEM.bytes_at segs m (fr + 186) ls /\ (6 <= length ls)%nat /\
          MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
          ART.addressable m (fr + 186) 6) /\
       (exists (ls2 rs2 : list byte),
          q64 m (A + 64) (fr + 180) /\ MEM.bytes_at segs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
          MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
          ART.addressable m (fr + 180) 6)).

(* frcl, SlotInv.v:2364 *)
Definition frcl (cx : ctlcx) (j : nat) (fr phi : Z) : RFR.fg_case :=
  RFR.fg_class (fragb fr) phi (fr + 256) (fr + 272) (fr + 304) (flen cx j) (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j).

(* frrec, SlotInv.v:2366 *)
Definition frrec (cx : ctlcx) (j : nat) (fr phi : Z) : list byte :=
  SM.fg_next (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j) (frcl cx j fr phi).

(* F17CARRY, SlotInv.v:2374 *)
Definition F17CARRY (cx : ctlcx) (j : nat) (fr phi A : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  rgv regs 23 phi /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\
  rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 18 (flen cx j) /\
  rgv regs 20 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
  q64 m (A + 232) (if SM.t_big (c_in cx) j then 0 else 1) /\ q64 m (A + 200) (phi + 18) /\
  q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
  spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  (exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
     (SM.t_8819 (c_in cx) j = true -> w240 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w240 = 0)) /\
  (50 <= flen cx j ->
     (exists rb, MEM.bytes_at segs m phi rb /\ (38 <= length rb)%nat) /\
     MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
     rec_inv0 cx j fr phi A m) /\
  (SM.t_8819 (c_in cx) j = true ->
     rec_parse cx j fr phi m /\
     (exists (ls rs : list byte),
        q64 m (A + 72) (fr + 186) /\ MEM.bytes_at segs m (fr + 186) ls /\ (6 <= length ls)%nat /\
        MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
        ART.addressable m (fr + 186) 6) /\
     (exists (ls2 rs2 : list byte),
        q64 m (A + 64) (fr + 180) /\ MEM.bytes_at segs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
        MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
        ART.addressable m (fr + 180) 6)).

(* F16CARRY, SlotInv.v:2410 *)
Definition F16CARRY (cx : ctlcx) (j : nat) (fr phi A : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  SM.frag_ok (SM.t_FG (c_in cx) j) /\ FSj cx fr j regs m /\
  (exists idb, MEM.bytes_at segs m (fr + 2688) idb /\ length idb = 38%nat) /\ ART.addressable m (fr + 2688) 38 /\
  q64 m (A + 144) (fr + 2688) /\
  F17CARRY cx j fr phi A regs m.

(* f14_tail, SlotInv.v:2481 *)
Definition f14_tail (cx : ctlcx) (j : nat) (fr phi : Z) (regs : bvmap 5 word) (m : word -> option byte)
    (A v w280 : Z) : Prop :=
  rgv regs 9 A /\ rgv regs 25 (RFR.fg_ret (frcl cx j fr phi)) /\ rgv regs 10 v /\
  0 <= A < 2 ^ 64 /\ 0 <= w280 < 2 ^ 64 /\ w280 = SM.b2z (SM.t_sum_ok (c_in cx) j) /\
  (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
  (phi + 50 <= Reusable.YG0d.spZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ Reusable.YG0d.spZ regs <= phi) /\
  FRM.stk segs m (Reusable.YG0d.spZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K) (Reusable.YG0d.spZ regs) /\
  q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\ q64 m (A + 280) w280 /\
  MEM.bytes_at segs m (fr + 336) (SM.t_FG (c_in cx) j) /\ ART.addressable m (fr + 336) 72 /\
  MEM.bytes_at segs m (fragb fr) (frrec cx j fr phi) /\ ART.addressable m (fragb fr) 72 /\
  MEM.bytes_at segs m BWA.REAL_BCMP (MEM.le8 (MEM.wa BWA.BCMP)) /\ MEM.bytes_at segs m BWA.REAL_MEMCMP (MEM.le8 (MEM.wa MCA.MEMCMP)) /\
  MEM.bytes_at segs m BWA.GOT_CF (MEM.le8 (MEM.wa BWA.CF)) /\
  MEM.bytes_at segs m (BWA.CF + 254) [Z_to_bv 8 1] /\ MEM.bytes_at segs m (BWA.CF + 255) [Z_to_bv 8 1] /\
  STP.rw_cells segs m (A + 256)
    [CEL.C8 (Z_to_bv 64 (fr + 256)); CEL.C8 (Z_to_bv 64 (fr + 304)); CEL.C8 (Z_to_bv 64 (fr + 272))] /\
  FGA.fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j) (frcl cx j fr phi) m /\
  F16CARRY cx j fr phi A regs m.

(* B7SPL, SlotInv.v:2795 *)
Definition B7SPL (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 136 (fr + 128) /\ spill regs m 120 (fr + 160) /\ spill regs m 176 (fr + 64).

(* B7K, SlotInv.v:2799 *)
Definition B7K (cx : ctlcx) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  LK cx fr j regs m /\ rgv regs 23 phi /\ rgv regs 22 (phi + 18) /\
  0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\
  MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
  spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
  rgv regs 18 (flen cx j) /\ spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
  MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
  Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j /\
  LT cx fr j regs m /\
  B7SPL fr regs m.

(* ---------------------------------------------------------------------------------------------------------
   1b. THE CARRIED PART OF ctrl's SHELLS.  ACtlCut.v's shell states the journal, the owned frames, the pc, the
   event bound and ctl_rt; the translation's section 2.1 marks three rows of ctrl's FRA / FRAH / PREF CARRY,
   i.e. they cross into the body unchanged, and every other row RESTATE or DROP.  The CARRY rows, transcribed
   here once and conjoined to every cut body (which shell per the row's shell column):
     FRA :341, :343-348  the sp / gp / tp / s0 / s1 / s3 / s10 pins, fr mod 32, the spill
                         base A with A mod 32, A <= S, sp <= A, fr + FRAME_BYTES <= A, A + 416 <= S,
                         S - 4096 < sp, S <= APPMEM_END, and the spills [A+304] / [A+24] / [A+16]
     FRA :354-355        the frame header words and the 392 frame shadow bytes
     FRA :357            the saved caller registers at [S - 104, S)
   The last two are what a cgif-form callee's achain obligation reads (a Theorem Labs lane's reply spec, via a Theorem Labs lane
   21:44Z).  TWO conjuncts of that CARRY range are NOT here (a Theorem Labs lane 23:05Z): ctrl's `(s5 = 0 \/ s5 = fr)` :346 /
   :460, because the shell passes sel = fr and the class-full arm is discharged at the fake-stack call; and
   `fr = frame_addr ly 6 fpos` in any FSREC-derived form, because ACtlCut.v's ctl_from now states the frame law
   itself (`forall cid pos, In (cid, pos) (cut_own X cx) -> fr = Reusable.YG0f.frame_addr (c_ly cx) cid pos`).  NOT transcribed, because section 2.1 marks them RESTATE or DROP and ACtlCut.v's shell or the
   core's pre states them: AsanRTInv.RT :337, aa_AH :338, ro_agree / sink_none / m_halted :339, G_img_c :340,
   aa_stklo :342, the real / side frame-location disjunction :349-353, stk :356, errno writable :358,
   frame_AG :359, the slot window minus the frame :362, aa_stkhi and the entry bytes above S :363-366, the hb
   length and live-bytes bounds :369, and the whole of ENT :378-432 (its only CARRY-looking row, :382-385, is
   RESTATE: the core's pre gives aspZ (c_regs cx) = c_sp cx and the tp word).

   ctrl's g_S is the ENTRY sp, so the field map's g_S -> c_sp cx is right here: c_sp cx is
   Reusable.YG0d.spZ (c_regs cx), the entry registers' sp, never the cut's own sp (which stays the
   existential sp below, pinned to register 2).

   ONE NAME THIS NEEDS FROM ACtlK: the thread-pointer word that ctrl writes AC.as_tp AC.ASYMS (:343 / :457 /
   PREF :949).  Contract.v is outside the port's closure, so it is Reusable.YG0f.as_tp B here; the frame-header entry
   word AF.ENTRY (:354 / :468) is the core's own A.ACfn.A_LLVMF, the function's entry address. *)
Definition FRAC (cx : ctlcx) (fr sel : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists A sp,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\
    Reusable.YG0d.spZ regs = sp /\
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) /\
    rgv regs 8 (c_sp cx) /\ rgv regs 9 A /\
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 3 /\
    rgv regs 19 (Sfr fr) /\ rgv regs 26 A.ACtlK.ASAN_K /\
    fr mod 32 = 0 /\ A mod 32 = 0 /\ A <= c_sp cx /\ sp <= A /\
    fr + FRAME_BYTES <= A /\ A + 416 <= c_sp cx /\ c_sp cx - 4096 < sp /\ c_sp cx <= ART.APPMEM_END /\
    q64 m (A + 304) fr /\ q64 m (A + 24) sel /\ q64 m (A + 16) fr /\
    q64 m fr 0x41b58ab3 /\ q64 m (fr + 16) A.ACfn.A_LLVMF /\
    (exists sh, MEM.bytes_at segs m (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx) /\
    q64 m (fr + 4088) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx)).

(* FRAH's CARRY part (SlotInv.v:455-471): FRA's, with the header word a parameter (FRAS 0x41b58ab3 :483,
   FRAR 0x45e0360e :486) and without the two spills [A+24] / [A+16], which the early edge 0x812c4 never
   writes (:442-447). *)
Definition FRAHC (cx : ctlcx) (fr sel hdr : Z) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists A sp,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\
    Reusable.YG0d.spZ regs = sp /\
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) /\
    rgv regs 8 (c_sp cx) /\ rgv regs 9 A /\
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 3 /\
    rgv regs 19 (Sfr fr) /\ rgv regs 26 A.ACtlK.ASAN_K /\
    fr mod 32 = 0 /\ A mod 32 = 0 /\ A <= c_sp cx /\ sp <= A /\
    fr + FRAME_BYTES <= A /\ A + 416 <= c_sp cx /\ c_sp cx - 4096 < sp /\ c_sp cx <= ART.APPMEM_END /\
    q64 m (A + 304) fr /\
    q64 m fr hdr /\ q64 m (fr + 16) A.ACfn.A_LLVMF /\
    (exists sh, MEM.bytes_at segs m (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx) /\
    q64 m (fr + 4088) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx)).

(* FAKE-FRAME TRAILER WORD (added by a Theorem Labs lane, the twin of image B's FRAC / FRAHC at
   a working branch a218ac85be5; a MEANING change, announced to every image-A stage lane): the
   last conjunct of FRAC and FRAHC.  The class-6 frame's last word, at fr + fs_frame_bytes 6 - 8 = fr + 4088, holds
   the frame's flag address.  The core's frame allocator post gives it (Reusable/YG0d.v:296; aj_stack_malloc_at,
   Reusable/YCbq.v:1764), and the frame release needs it (the astack_free_realizes premise, StackFreeDef.v:25 as
   image B's note cites it).  Neither AR nor ajournal carries it for the walk's OWN frame, so every body that
   carries FRAC or FRAHC carries it, in raw form like the other frame words.  The program writes only
   [fr, fr + FRAME_BYTES) of the frame, and FRAME_BYTES < 4088.  From batch 4 (item B5.3) the two PREFC cuts after
   A1's frame request, C_A80f54 and C_A80f88, carry the same word as their LAST conjunct: it is BORN at that request
   (0x80f50), and every own6 cut from there to the first FRAHC cut (C_A810e4) carries it.

   NON-STRICT TOP OF THE ENTRY SP (batch 4, item B5.4; image B's twin at a working branch): FRAC,
   FRAHC and PREFC state `c_sp cx <= ART.APPMEM_END`, in the place where ctrl's `S < APPMEM_END` was.  Nothing in
   the core's pre gives the strict bound: afn_pre's astk_ok gives sp0 <= ly_stk_hi <= kHighMemEnd (found by the
   ENTRY glue, lib/A/ACtlG/A1.v:21-22). *)

(* PREF's CARRY part (SlotInv.v:944-974), for the two pre-frame cuts A80f54 and A80f88: the same pins without
   the frame (no fr, no s3, no header, no frame shadow), with PREF's own spill-base window S - 432 <= A and
   its input bound.  PREF's A and sp are ctrl's parameters; they are existential here, pinned by register 2
   and register 9 exactly as the FRA form pins them. *)
Definition PREFC (cx : ctlcx) (regs : bvmap 5 word)
    (m : word -> option byte) : Prop :=
  exists A sp,
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 sp /\ sp mod 16 = 0 /\
    Reusable.YG0d.spZ regs = sp /\
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B) /\
    rgv regs 8 (c_sp cx) /\ rgv regs 9 A /\
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 3 /\ rgv regs 26 A.ACtlK.ASAN_K /\
    A mod 32 = 0 /\ A <= c_sp cx /\ c_sp cx - 432 <= A /\ sp <= A /\ A + 416 <= c_sp cx /\
    c_sp cx - 4096 < sp /\ c_sp cx <= ART.APPMEM_END /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx) /\
    c_n cx <= A.ACtlK.ANMAX.

(* ---------------------------------------------------------------------------------------------------------
   2. The two span shells of the frame loop, b5_CUT (SlotInv.v:2133) and B7CUT (:2815), with their CUTST
   wrapper dropped and their live list stated as the body's own Permutation of bl.  Sixteen F4-F12 cuts and
   eight F22-F28 cuts are written through them, exactly as ctrl writes them.

   THE LIVE-LIST ENTRY IS THE REQUEST SIZE (a Theorem Labs lane 21:52Z, settling the disagreement this lane reported): the
   core's ablocks records (res, n) with n the REQUEST (amalloc04_rule's post appends it, donor YC5d.v:67-74),
   while ctrl's `hb1 phi (AC.a_size (flen g j))` is a Theorem Labs lane's aa_AH convention, which the translation section of llvmf-cgif-walk-plan.md section 2.1 (a working note, not in this delivery) RESTATES.  So
   every live entry here is `(phi, flen cx j)` for the frame loop and `(phi, rnb cx b)` for the round trip.
   ctrl's a_size survives only where a body conjunct is about addressable BYTES, i.e. inside HB, verbatim. *)
Definition b5_body (cx : ctlcx) (j : nat) (bl : list (Z * Z)) (fr : Z)
    (regs : bvmap 5 word)
    (m : word -> option byte)
    (P : Z -> Z -> bvmap 5 word ->
         (word -> option byte) -> Prop) : Prop :=
  exists phi,
    Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
    c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
    LK cx fr j regs m /\ b5_C cx j phi fr regs m /\ P phi fr regs m.

Definition b7_body (cx : ctlcx) (j : nat) (bl : list (Z * Z)) (fr : Z)
    (regs : bvmap 5 word)
    (m : word -> option byte)
    (P : Z -> Z -> bvmap 5 word ->
         (word -> option byte) -> Prop) : Prop :=
  exists phi,
    Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
    c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
    B7K cx j phi fr regs m /\ P phi fr regs m.

(* ---------------------------------------------------------------------------------------------------------
   3. The 100 cuts, in the address order of the cut map, one record per row of
   cut-table-A.tsv (a working note, not in this delivery).  Each record's comment gives the row's cut
   name, its SlotInv.v definition and line at d5e20dfd330, ctrl's shell, the pc, the index shape, the event
   bound, the frame list and the W piece, plus the table's superseded note where it has one.

   EVERY CUT FROM A4's FRAME ALLOCATION TO ITS RELEASE OWNS THE CLASS-6 FAKE FRAME (own6).  The class-full
   arm, where __asan_stack_malloc_6 returns 0 and the frame would be the real stack, is DISCHARGED by the
   model law at the fake-stack call, not walked: astack_malloc_realizes has only the frame_addr outcome
   (YG0d.v:284-299) and stack_malloc_progress rules the null result out (YG05.v:69-84), since frames S = [] at
   the entry (two Theorem Labs lanes, 21:29Z-21:30Z).  ENTRY (before the frame) and the post-release cuts
   own nothing (own0).  The shell passes sel = fr. *)

(* ENTRY: Inv_ENTRY, SlotInv.v:749 (shell alib_pre (Inv_ENTRY :749)); pc 0x80edc, index [], k <= 0, own0, piece W0
   live list (table): entry blocks *)
Definition C_ENTRY : ctlcut := mkCtlCut
  0x80edc
  own0
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     Reusable.YG0d.spZ (c_regs cx) = c_sp cx /\
     (* the entry cut's registers ARE the contract's entry registers (batch 4, item B5.1): without it the
        ENTRY stage cannot pin the run's sp, gp, saved registers or a0 / a1 (lib/A/ACtlG/A1.v:19-20);
        the top closes it by reflexivity at regs3 := c_regs cx *)
     regs = c_regs cx).

(* A80f54: Inv_A80f54, SlotInv.v:976 (shell PREF :943 + ENT :378); pc 0x80f54, index [], k <= 0, own6, piece W0
   live list (table): entry blocks *)
Definition C_A80f54 : ctlcut := mkCtlCut
  0x80f54
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     PREFC cx regs m /\
     (* the frame request's result in a0 IS the selector: the shell passes sel = fr and the
        class-full (a0 = 0) arm is discharged at the fake-stack call, a Theorem Labs lane 23:05Z *)
     a0v regs sel /\ 0 <= sel < 2 ^ 64 /\
    rgv regs 23 (c_p cx) /\ rgv regs 24 (c_n cx) /\
    MEM.bytes_at segs m (c_p cx) (c_in cx) /\
    (0 < c_n cx -> ART.addressable m (c_p cx) (c_n cx)) /\
     (* the fake-frame trailer word, BORN at A1's frame request 0x80f50 (see FRAC; batch 4, item B5.3) *)
     q64 m (fr + 4088) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))).

(* A80f88: Inv_A80f88, SlotInv.v:992 (shell PREF :943 + ENT :378); pc 0x80f88, index [], k <= 0, own6, piece W0
   live list (table): entry blocks *)
Definition C_A80f88 : ctlcut := mkCtlCut
  0x80f88
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     PREFC cx regs m /\
     exists A,
     rgv regs 22 fr /\ fr mod 32 = 0 /\ (* s5, ctrl's selector register (SlotInv.v:280), is sel: see A80f54 *)
    rgv regs 21 sel /\ 0 <= fr < 2 ^ 64 /\ fr + FRAME_BYTES <= A /\
    rgv regs 23 (c_p cx) /\ rgv regs 24 (c_n cx) /\
    MEM.bytes_at segs m (c_p cx) (c_in cx) /\
    (0 < c_n cx -> ART.addressable m (c_p cx) (c_n cx)) /\
     (* the fake-frame trailer word, BORN at A1's frame request 0x80f50 (see FRAC; batch 4, item B5.3) *)
     q64 m (fr + 4088) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.flag_addr (c_ly cx) 6 (c_fpos cx))).

(* A810e4: Inv_A810e4, SlotInv.v:1013 (shell CUTST0 :490 (FRAH :448 + ENT :378)); pc 0x810e4, index [], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A810e4 : ctlcut := mkCtlCut
  0x810e4
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x41b58ab3 regs m /\
     c_n cx <= A.ACtlK.ANMAX /\
    rgv regs 18 (-8) /\ rgv regs 20 (-14) /\ rgv regs 21 sel /\ rgv regs 22 fr /\
    rgv regs 23 (c_p cx) /\ rgv regs 24 (c_n cx) /\ rgv regs 25 (Sfr fr + 68) /\
    MEM.bytes_at segs m (c_p cx) (c_in cx) /\
    (0 < c_n cx -> ART.addressable m (c_p cx) (c_n cx))).

(* A81400_at t: Inv_A81400_at, SlotInv.v:1058 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81400, index [t], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A81400_at : ctlcut := mkCtlCut
  0x81400
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     let t := ixz 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ 0 <= t <= 5 /\
    rgv regs 23 (c_p cx + Z.min t (c_n cx)) /\ rgv regs 24 (c_n cx - Z.min t (c_n cx)) /\
    MEM.bytes_at segs m (fr + 2624) (firstn (Z.to_nat t) (SM.OUR (c_in cx))) /\
    rgv regs 21 (fr + 2176) /\ rgv regs 28 (fr + 2256) /\ spill regs m 152 (Sfr fr + 68) /\
    rgv regs 18 (fr + 2656) /\ PRO cx fr regs m /\ rgv regs 7 (fr + 544) /\
    rgv regs 1 (fr + 2496) /\ rgv regs 11 t /\ rgv regs 12 6 /\ rgv regs 13 7 /\ rgv regs 14 (fr + 2624) /\
    rgv regs 29 (fr + 2368) /\ rgv regs 30 (fr + 2448) /\ rgv regs 31 (fr + 2464) /\
    b8 m (Sfr fr + 328) 6 /\ rgv regs 27 (fr + 2688) /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    (exists junk, length junk = Z.to_nat (6 - t) /\
       MEM.bytes_at segs m (fr + 2624) (firstn (Z.to_nat t) (SM.OUR (c_in cx)) ++ junk))).

(* A81414: Inv_A81414, SlotInv.v:1109 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81414, index [], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A81414 : ctlcut := mkCtlCut
  0x81414
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     exists t,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ 0 <= t <= 5 /\
    rgv regs 1 (fr + 2496) /\ rgv regs 7 (fr + 544) /\
    rgv regs 10 (fr + 2624 + t) /\ rgv regs 11 (t + 1) /\ rgv regs 12 6 /\ rgv regs 13 7 /\
    rgv regs 14 (fr + 2624 + t) /\ rgv regs 18 (fr + 2656) /\ rgv regs 21 (fr + 2176) /\
    rgv regs 22 (c_p cx + Z.min t (c_n cx)) /\ rgv regs 25 (c_n cx - Z.min t (c_n cx)) /\
    rgv regs 28 (fr + 2256) /\ rgv regs 29 (fr + 2368) /\ rgv regs 30 (fr + 2448) /\ rgv regs 31 (fr + 2464) /\
    spill regs m 152 (Sfr fr + 68) /\ PRO cx fr regs m /\
    b8 m (Sfr fr + 328) 6 /\ rgv regs 27 (fr + 2688) /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    (exists junk, length junk = Z.to_nat (6 - t) /\
       MEM.bytes_at segs m (fr + 2624) (firstn (Z.to_nat t) (SM.OUR (c_in cx)) ++ junk))).

(* A814f8: Inv_A814f8, SlotInv.v:1117 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x814f8, index [], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A814f8 : ctlcut := mkCtlCut
  0x814f8
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ a0v regs SM.CAT /\ OURb cx fr m /\
    spill regs m 152 (Sfr fr + 68) /\
    rgv regs 18 (fr + 2656) /\ q64 m (fr + 2656) SM.CAT_N /\ rgv regs 21 (fr + 2176) /\ CUR cx 7 regs /\
    spill regs m 48 (fr + 2256) /\ spill regs m 128 (fr + 544) /\
    PRO cx fr regs m /\
    rgv regs 23 (SM.mode (c_in cx)) /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\ spill regs m 80 (fr + 2464) /\
    spill regs m 72 (fr + 2496) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528)).

(* A8152c: Inv_A8152c, SlotInv.v:1137 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8152c, index [], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A8152c : ctlcut := mkCtlCut
  0x8152c
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ rgv regs 21 (fr + 2176) /\
    CUR cx 7 regs /\ spill regs m 48 (fr + 2256) /\ ART.addressable m (fr + 544) 1488 /\
    spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 152 (Sfr fr + 68) /\ spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\ spill regs m 80 (fr + 2464) /\
    spill regs m 72 (fr + 2496) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    rgv regs 18 (SM.mrow (c_in cx))).

(* A81578: Inv_A81578, SlotInv.v:1154 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81578, index [], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A81578 : ctlcut := mkCtlCut
  0x81578
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ CUR cx 7 regs /\ OURb cx fr m /\
    IDBr cx fr (SM.RID (c_in cx) 0) m /\ spill regs m 48 (fr + 2256) /\
    ART.addressable m (fr + 544) 1492 /\ ART.addressable m (fr + 2176) 38 /\ ART.addressable m (fr + 2256) 72 /\
    spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    rgv regs 21 (fr + 2176) /\ spill regs m 152 (Sfr fr + 68) /\ spill regs m 144 (fr + 2688) /\
    spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\ spill regs m 80 (fr + 2464) /\
    spill regs m 72 (fr + 2496) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    rgv regs 18 (SM.mrow (c_in cx))).

(* A81588: Inv_A81588, SlotInv.v:1173 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81588, index [], k <= 0, own6, piece W1
   live list (table): entry blocks *)
Definition C_A81588 : ctlcut := mkCtlCut
  0x81588
  own6
  (fun _ _ => 0)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ CUR cx 7 regs /\ OURb cx fr m /\ OUTA fr m /\
    IDBr cx fr (SM.RID (c_in cx) 0) m /\ FGBr cx fr (SM.RFG (c_in cx) 0) m /\
    spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    rgv regs 21 (fr + 2176) /\ spill regs m 152 (Sfr fr + 68) /\ spill regs m 144 (fr + 2688) /\
    spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 48 (fr + 2256) /\ spill regs m 56 (fr + 2368) /\ spill regs m 88 (fr + 2448) /\
    spill regs m 80 (fr + 2464) /\ spill regs m 72 (fr + 2496) /\
    spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\ ART.addressable m (fr + 2256) 72 /\
    ART.addressable m (fr + 2176) 38 /\
    rgv regs 18 (SM.mrow (c_in cx))).

(* A815cc_at b: Inv_A815cc_at, SlotInv.v:1199 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x815cc, index [b], k <= 2b, own6, piece W2
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry blocks *)
Definition C_A815cc_at : ctlcut := mkCtlCut
  0x815cc
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ RS cx fr b regs m /\ OUTA fr m /\
    spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\
    a0v regs (fr + 544) /\ rgv regs 24 36 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 112 (SM.mrow (c_in cx)) /\
    rgv regs 21 (fr + 2176) /\
    spill regs m 152 (Sfr fr + 68) /\
    spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2176) 38 /\ spill regs m 192 (fr + 2768) /\
    
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    RXS cx fr regs m).

(* A815ec_at b: Inv_A815ec_at, SlotInv.v:1237 (shell raw FRA :334 + ENT :378); pc 0x815ec, index [b], k <= 2b, own6, piece W2
   live list (table): entry blocks *)
Definition C_A815ec_at : ctlcut := mkCtlCut
  0x815ec
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     exists A,
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ 0 <= rnb cx b <= A.ACtlK.ANMAX /\
    0 <= A.ACtlK.a_size (rnb cx b) <= 616472576 /\
    0 <= A < 2 ^ 64 /\ rgv regs 9 A /\ rgv regs 24 36 /\ a0v regs (rnb cx b) /\ q64 m (A + 64) 0xe38f0000 /\
    spill regs m 128 (fr + 544) /\
    IDBr cx fr (SM.RID (c_in cx) b) m /\ FGBr cx fr (SM.RFG (c_in cx) b) m /\
    (rnb cx b <> 0 -> MEM.bytes_at segs m (fr + 544) (SM.rt_F (c_in cx) (Z.of_nat b))) /\
    rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 144 (fr + 2688) /\
    spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\ ART.addressable m (fr + 2176) 38 /\
    RXS cx fr regs m).

(* A81640_at b: Inv_A81640_at, SlotInv.v:1278 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81640, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81640_at : ctlcut := mkCtlCut
  0x81640
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ rnb cx b <> 0 /\
    a0v regs phi /\ HB m phi (rnb cx b) /\ rgv regs 18 (rnb cx b) /\ spill regs m 128 (fr + 544) /\
    ART.addressable m (fr + 544) (rnb cx b) /\
    (exists src, MEM.bytes_at segs m (fr + 544) src /\ Z.of_nat (length src) = rnb cx b) /\
    rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\
    ART.addressable m (fr + 2176) 38) /\
    X81640 cx b phi fr regs m).

(* A81658_at b: Inv_A81658_at, SlotInv.v:1298 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81658, index [b], k <= 2b+1, own6, piece W2
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81658_at : ctlcut := mkCtlCut
  0x81658
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\
    ART.addressable m (fr + 2176) 38) /\
    X81658 cx b phi fr regs m).

(* A81680_at b: Inv_A81680_at, SlotInv.v:1316 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81680, index [b], k <= 2b+1, own6, piece W2
   superseded: App B 21:00Z/21:02Z: reac_ctrl_identity_reply has no image-A proof, so this site is a NEW cgif-form walk citing its t<fn>_spec, not a callee-cut
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81680_at : ctlcut := mkCtlCut
  0x81680
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\
    ART.addressable m (fr + 2176) 38) /\
    X81680 cx b phi fr regs m).

(* A816c4_at b: Inv_A816c4_at, SlotInv.v:1337 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x816c4, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A816c4_at : ctlcut := mkCtlCut
  0x816c4
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\
    ART.addressable m (fr + 2176) 38) /\
    X816c4 cx b phi fr regs m).

(* A81708_at b: Inv_A81708_at, SlotInv.v:1361 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81708, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81708_at : ctlcut := mkCtlCut
  0x81708
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\
    ART.addressable m (fr + 2176) 38) /\
    X81708 cx b phi fr regs m).

(* A81734_at b: Inv_A81734_at, SlotInv.v:1383 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81734, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81734_at : ctlcut := mkCtlCut
  0x81734
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\ CUR cx 7 regs /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 128 (fr + 544) /\ PRO cx fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rgv regs 21 (fr + 2176) /\
    ART.addressable m (fr + 2176) 38 /\
    RXS cx fr regs m /\
    X81734 cx b phi fr regs m).

(* A81768_at b: Inv_A81768_at, SlotInv.v:1418 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81768, index [b], k <= 2b+1, own6, piece W2
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81768_at : ctlcut := mkCtlCut
  0x81768
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi (i : nat),
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
     CUR cx 7 regs /\
     (i <= 32)%nat /\ rgv regs 10 (phi + 18 + Z.of_nat i) /\ rgv regs 12 (phi + 18 + Z.of_nat i) /\
     rgv regs 13 (32 - Z.of_nat i)) /\
    b = 0%nat /\ (i < 32)%nat /\ rgv regs 11 (rsum cx b i) /\ RF cx fr b phi regs m /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 8 (SM.mrow (c_in cx) + 16) /\
    spill regs m 0 (SM.mrow (c_in cx) + 20) /\ spill regs m 200 (decl_slot fr) /\ spill regs m 216 (fr + 2528) /\
    ART.addressable m (fr + 2528) 12 /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A817c8_at b: Inv_A817c8_at, SlotInv.v:1443 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x817c8, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A817c8_at : ctlcut := mkCtlCut
  0x817c8
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
     CUR cx 7 regs) /\
    RB cx fr b (SM.RID (c_in cx) (S b)) (SM.RFG (c_in cx) (S b)) regs m /\ rgv regs 24 phi /\ a0v regs 0 /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 112 (SM.mrow (c_in cx)) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A817ec_at b: Inv_A817ec_at, SlotInv.v:1464 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x817ec, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A817ec_at : ctlcut := mkCtlCut
  0x817ec
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi (i : nat),
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
     CUR cx 7 regs /\
     (i <= 32)%nat /\ rgv regs 10 (phi + 18 + Z.of_nat i) /\ rgv regs 12 (phi + 18 + Z.of_nat i) /\
     rgv regs 13 (32 - Z.of_nat i)) /\
    (b = 1 \/ b = 2)%nat /\ (i < 32)%nat /\ rgv regs 11 (rsum cx b i) /\
    RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 112 (SM.mrow (c_in cx)) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A8183c_at b: Inv_A8183c_at, SlotInv.v:1488 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8183c, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A8183c_at : ctlcut := mkCtlCut
  0x8183c
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
     CUR cx 7 regs /\ spill regs m 216 (fr + 2528)) /\
    b = 0%nat /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ a0v regs (SM.mrow (c_in cx)) /\
    spill regs m 112 (SM.mrow (c_in cx)) /\ spill regs m 8 (SM.mrow (c_in cx) + 16) /\
    spill regs m 0 (SM.mrow (c_in cx) + 20) /\ spill regs m 200 (decl_slot fr) /\
    ART.addressable m (fr + 2528) 12 /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A81858_at b: Inv_A81858_at, SlotInv.v:1511 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81858, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A81858_at : ctlcut := mkCtlCut
  0x81858
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
     CUR cx 7 regs /\ spill regs m 200 (decl_slot fr)) /\
    b = 0%nat /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ rgv regs 27 (phi + 18) /\
    a0v regs 0 /\
    u32 m (fr + 2528) (4 * RLF.n_in (SM.rt_pbs (c_in cx))) /\
    u32 m (fr + 2532) (4 * RLF.n_out (SM.rt_pbs (c_in cx))) /\
    spill regs m 216 (fr + 2528) /\ spill regs m 8 (SM.mrow (c_in cx) + 16) /\
    spill regs m 0 (SM.mrow (c_in cx) + 20) /\ spill regs m 112 (SM.mrow (c_in cx)) /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A818d0_at b: Inv_A818d0_at, SlotInv.v:1537 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x818d0, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A818d0_at : ctlcut := mkCtlCut
  0x818d0
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi vd,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ OUTA fr m /\ rgv regs 10 vd /\
     vd <> 0 /\ rgv regs 27 (phi + 18) /\ rgv regs 18 (decl_slot fr) /\
     MEM.bytes_at segs m (decl_slot fr) (RDC.decl (SM.rt_mb (c_in cx)))) /\
    b = 0%nat /\ HB m phi (rnb cx b) /\ 0 <= vd < 2 ^ 64 /\ length (RDC.decl (SM.rt_mb (c_in cx))) = 32%nat /\
    ART.addressable m (decl_slot fr) 32 /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 112 (SM.mrow (c_in cx)) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A818e8_at b: Inv_A818e8_at, SlotInv.v:1560 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x818e8, index [b], k <= 2b+1, own6, piece W2
   live list (table): entry ++ [(φ, rnb g b)] (Perm) *)
Definition C_A818e8_at : ctlcut := mkCtlCut
  0x818e8
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, (rnb cx b))]) /\
     FRAC cx fr sel regs m /\
     (c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb cx b) /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
     CUR cx 7 regs) /\
    b = 0%nat /\ RFb cx fr b (SM.RID (c_in cx) b) (SM.RFG (c_in cx) b) phi regs m /\ a0v regs 0 /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 112 (SM.mrow (c_in cx)) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A81924_at b: Inv_A81924_at, SlotInv.v:1583 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81924, index [b], k <= 2b+2, own6, piece W2
   live list (table): entry blocks *)
Definition C_A81924_at : ctlcut := mkCtlCut
  0x81924
  own6
  (fun _ idx => 2 * Z.of_nat (ixn 0 idx) + 2)
  (fun cx idx bl fr sel regs m =>
     let b := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (b <= 6)%nat /\ rgv regs 23 (Z.of_nat b) /\ OURb cx fr m /\ OUTA fr m /\
    RB cx fr b (SM.RID (c_in cx) (S b)) (SM.RFG (c_in cx) (S b)) regs m /\
    spill regs m 128 (fr + 544) /\ 
    PRO cx fr regs m /\ spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ 
    spill regs m 64 0xe38f0000 /\ 
    rgv regs 21 (fr + 2176) /\ 
    spill regs m 112 (SM.mrow (c_in cx)) /\ 
    spill regs m 144 (fr + 2688) /\ 
    spill regs m 192 (fr + 2768) /\ 
    (exists idb, STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb]) /\ (exists junk, STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\ 
    (exists jy, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy]) /\ (exists junk, STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ 
    ART.addressable m (fr + 2176) 38 /\ 
    
    RXS cx fr regs m).

(* A81ac0: Inv_A81ac0, SlotInv.v:1643 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81ac0, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81ac0 : ctlcut := mkCtlCut
  0x81ac0
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ a0v regs 0 /\
    (exists Q, spill regs m 152 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    (exists (A : Z) (idb junk : list byte),
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\ rgv regs 27 (fr + 2688) /\ 0 <= A < 2 ^ 64 /\
       STP.rw_cells segs m (A + 192) [CEL.C8 (Z_to_bv 64 (fr + 2768))] /\
       STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb] /\
       STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk] /\
       q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
       (exists jy junk2 : list byte, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\ STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk2]))).

(* A81ac8: Inv_A81ac8, SlotInv.v:1654 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81ac8, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81ac8 : ctlcut := mkCtlCut
  0x81ac8
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ a0v regs 0 /\
    (exists Q, spill regs m 152 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    (exists (A : Z) (idb junk : list byte),
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\ rgv regs 27 (fr + 2688) /\ 0 <= A < 2 ^ 64 /\
       STP.rw_cells segs m (A + 192) [CEL.C8 (Z_to_bv 64 (fr + 2768))] /\
       STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb] /\
       STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk] /\
       q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
       (exists jy junk2 : list byte, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\ STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk2]))).

(* A81b10: Inv_A81b10, SlotInv.v:1665 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81b10, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81b10 : ctlcut := mkCtlCut
  0x81b10
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\
    (exists (A : Z) (idb junk : list byte),
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\ rgv regs 27 (fr + 2688) /\ 0 <= A < 2 ^ 64 /\
       STP.rw_cells segs m (A + 192) [CEL.C8 (Z_to_bv 64 (fr + 2768))] /\
       STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb] /\
       STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk] /\
       q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
       (exists jy junk2 : list byte, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\ STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk2]))).

(* A81b14: Inv_A81b14, SlotInv.v:1676 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81b14, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81b14 : ctlcut := mkCtlCut
  0x81b14
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\
    exists (spv A : Z) (idb junk : list byte),
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 spv /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\ rgv regs 27 (fr + 2688) /\
      0 <= A < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      STP.rw_cells segs m (A + 192) [CEL.C8 (Z_to_bv 64 (fr + 2768))] /\
      STP.rw_cells segs m (fr + 2688) [CEL.CB 38 idb] /\
      STP.rw_cells segs m (fr + 2768) [CEL.CB 72 junk] /\
      q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
      (exists jy junk2 : list byte, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\ STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk2])).

(* A81b80: Inv_A81b80, SlotInv.v:1711 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81b80, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81b80 : ctlcut := mkCtlCut
  0x81b80
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\
    exists (D spv A : Z) (junk : list byte),
      let W : list FRM.ivl := [(D, D + 72); (spv - AMC.ASAN_MEMSET_K, spv)] in
      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 = Z_to_bv 64 spv /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A /\
      0 <= A < 2 ^ 64 /\ 0 <= D < 2 ^ 64 /\ 0 <= spv < 2 ^ 64 /\
      STP.rw_cells segs m (A + 192) [CEL.C8 (Z_to_bv 64 D)] /\
      STP.rw_cells segs m D [CEL.CB 72 junk] /\ ART.addressable m D 72 /\ ART.end_in_app D 72 /\ ART.app_mem (D + 7) /\
      (D + 72 <= ART.RT_LO \/ ART.RT_HI <= D) /\
      (D + 72 <= spv - AMC.ASAN_MEMSET_K \/ spv <= D) /\
      (forall x, 0 <= x < 6283264 -> FRM.outside W x) /\
      (forall x, fr <= x < fr + 24 -> FRM.outside W x) /\
      (forall A0, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 304 <= x < A0 + 312 -> FRM.outside W x) /\
      (forall A0, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
         forall x, A0 + 16 <= x < A0 + 32 -> FRM.outside W x) /\
      (forall x, c_sp cx - 104 <= x < c_sp cx -> FRM.outside W x) /\
      (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> FRM.outside W x) /\
      (forall x, fr + 2624 <= x < fr + 2624 + Z.of_nat (length (SM.OUR (c_in cx))) -> FRM.outside W x) /\
      ARF.all_app W /\ rt_disjoint W /\
      D = fr + 2768 /\ q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
      (exists jy junk2 : list byte, STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\ STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk2]) /\
      ART.addressable m (fr + 2880) 35).

(* A81b90: Inv_A81b90, SlotInv.v:1738 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81b90, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81b90 : ctlcut := mkCtlCut
  0x81b90
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\
    exists (A : Z) (jy junk : list byte),
      rgv regs 9 A /\ 0 <= A /\ q64 m (A + 280) (fr + 3040) /\ q64 m (A + 240) (fr + 3056) /\
      STP.rw_cells segs m (fr + 3040) [CEL.CB 1 jy] /\ STP.rw_cells segs m (fr + 3056) [CEL.CB 32 junk] /\
      ART.addressable m (fr + 2880) 35).

(* A81bd8: Inv_A81bd8, SlotInv.v:1756 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81bd8, index [], k <= 14, own6, piece W3
   superseded: App B 21:00Z/21:02Z: reac_ctrl_identity_reply has no image-A proof, so this site is a NEW cgif-form walk citing its t<fn>_spec, not a callee-cut
   live list (table): entry blocks *)
Definition C_A81bd8 : ctlcut := mkCtlCut
  0x81bd8
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ XC fr regs m /\
    exists (A pa pp f : Z),
      rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ 0 <= pa < 2 ^ 64 /\ 0 <= pp < 2 ^ 64 /\
      q64 m (A + 232) pa /\ q64 m (A + 224) pp /\ q64 m (A + 192) f /\
      ART.addressable m (Reusable.YG0d.spZ regs - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
      ART.addressable m REAC_CTRL_PARSE_BC 6 /\
      ART.addressable m (fr + 2880) 35).

(* A81bf8: Inv_A81bf8, SlotInv.v:1768 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81bf8, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81bf8 : ctlcut := mkCtlCut
  0x81bf8
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ a0v regs (-1) /\
    (exists f, spill regs m 192 f) /\ XC fr regs m /\ ART.addressable m (fr + 2880) 35).

(* A81c20: Inv_A81c20, SlotInv.v:1774 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81c20, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81c20 : ctlcut := mkCtlCut
  0x81c20
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ a0v regs (-1) /\
    rgv regs 18 (-1) /\ XC fr regs m /\ ART.addressable m (fr + 2880) 35).

(* A81c34: Inv_A81c34, SlotInv.v:1780 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81c34, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81c34 : ctlcut := mkCtlCut
  0x81c34
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ a0v regs (-1) /\ XC fr regs m /\
    ART.addressable m (fr + 2880) 35).

(* A81c4c: Inv_A81c4c, SlotInv.v:1793 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81c4c, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81c4c : ctlcut := mkCtlCut
  0x81c4c
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ a0v regs (-1) /\
    rgv regs 18 (-1) /\ XC fr regs m /\ ART.addressable m (fr + 2880) 35).

(* A81c60: Inv_A81c60, SlotInv.v:1799 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81c60, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81c60 : ctlcut := mkCtlCut
  0x81c60
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ a0v regs (-1) /\
    b8 m (fr + 3040) 0 /\ XC fr regs m /\ ART.addressable m (fr + 2880) 35).

(* A81c84: Inv_A81c84, SlotInv.v:1807 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81c84, index [], k <= 14, own6, piece W3
   live list (table): entry blocks *)
Definition C_A81c84 : ctlcut := mkCtlCut
  0x81c84
  own6
  (fun _ _ => 14)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ a0v regs KNA.QMARK /\
    KNA.kind_name_strings m /\ ART.addressable m KNA.QMARK 2 /\ XC fr regs m /\ CUR cx (SM.c0 (c_in cx)) regs /\
    PRO cx fr regs m /\ spill regs m 144 (fr + 2688) /\ ART.addressable m (fr + 2691) 17 /\
    spill regs m 192 (fragb fr) /\ ART.addressable m (fragb fr) 72 /\ ART.addressable m (fr + 2688) 38 /\
    IDBe cx fr RIM.ID0 m /\ FGBe cx fr SM.z72 m /\ ART.addressable m (fr + 2880) 35).

(* A81d40_at j: Inv_A81d40_at, SlotInv.v:1999 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81d40, index [j], k <= 14+2j, own6, piece W4a
   live list (table): entry blocks *)
Definition C_A81d40_at : ctlcut := mkCtlCut
  0x81d40
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx))
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ LI cx fr j regs m /\ FLSH cx j fr regs m /\
    f1_IN cx m /\ spill regs m 248 (fr + 176) /\ FLC fr regs m).

(* A81da4_at j: Inv_A81da4_at, SlotInv.v:2003 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x81da4, index [j], k <= 14+2j+1, own6, piece W4a
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81da4_at : ctlcut := mkCtlCut
  0x81da4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ a0v regs phi /\ HB m phi (flen cx j) /\
       LK cx fr j regs m /\ FC cx fr j regs m /\ FLSH cx j fr regs m /\
       f1_IN cx m /\ spill regs m 248 (fr + 176) /\ IFS cx fr j regs m /\ FLC fr regs m).

(* A81dd0_at j: Inv_A81dd0_at, SlotInv.v:2219 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81dd0, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81dd0_at : ctlcut := mkCtlCut
  0x81dd0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       FC cx fr j regs m /\ (50 <= flen cx j -> rgv regs 22 0) /\
    (50 <= flen cx j -> MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j)) /\ IDj cx fr j m)).

(* A81dfc_at j: Inv_A81dfc_at, SlotInv.v:2227 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81dfc, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81dfc_at : ctlcut := mkCtlCut
  0x81dfc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       FC cx fr j regs m /\
    rgv regs 10 (SM.t_k (c_in cx) j) /\ rgv regs 25 (phi + 18) /\
    (50 <= flen cx j -> rgv regs 22 0) /\ u32 m (fr + 176) (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_PF cx j phi fr regs m)).

(* A81e54_at j: Inv_A81e54_at, SlotInv.v:2235 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81e54, index [j], k <= 14+2j+1, own6, piece W4a
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81e54_at : ctlcut := mkCtlCut
  0x81e54
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       flen cx j = 0 /\ (phi + 1 <= fr \/ fr + FRAME_BYTES <= phi) /\ IDj cx fr j m /\ b5_PF cx j phi fr regs m)).

(* A81e84_at j: Inv_A81e84_at, SlotInv.v:2240 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81e84, index [j], k <= 14+2j+1, own6, piece W4a
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81e84_at : ctlcut := mkCtlCut
  0x81e84
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       flen cx j < 50 /\ rgv regs 10 (SM.t_k (c_in cx) j) /\ u32 m (fr + 176) (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_PF cx j phi fr regs m)).

(* A81e88_at j: Inv_A81e88_at, SlotInv.v:2247 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81e88, index [j], k <= 14+2j+1, own6, piece W4a
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81e88_at : ctlcut := mkCtlCut
  0x81e88
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       flen cx j < 50 /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ u32 m (fr + 176) (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_PF cx j phi fr regs m)).

(* A81ea4_at j: Inv_A81ea4_at, SlotInv.v:2253 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81ea4, index [j], k <= 14+2j+1, own6, piece W4a
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81ea4_at : ctlcut := mkCtlCut
  0x81ea4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       50 <= flen cx j /\ rgv regs 22 0 /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 25 (phi + 18) /\
    SM.t_8819 (c_in cx) j = false /\ u32 m (fr + 176) (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_PF cx j phi fr regs m)).

(* A81ea8_at j: Inv_A81ea8_at, SlotInv.v:2260 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81ea8, index [j], k <= 14+2j+1, own6, piece W4a
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81ea8_at : ctlcut := mkCtlCut
  0x81ea8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       50 <= flen cx j /\ rgv regs 22 0 /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 25 (phi + 18) /\
    b5_sp regs m 240 (SM.b2z (SM.t_8819 (c_in cx) j)) /\ u32 m (fr + 176) (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A81ec0_at j: Inv_A81ec0_at, SlotInv.v:2268 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81ec0, index [j], k <= 14+2j+1, own6, piece W4a
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81ec0_at : ctlcut := mkCtlCut
  0x81ec0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       50 <= flen cx j /\
    rgv regs 10 (phi + 18) /\ rgv regs 11 0 /\ rgv regs 12 (phi + 18) /\ rgv regs 13 32 /\
    rgv regs 22 (phi + 18) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 25 (phi + 18) /\
    b5_sp regs m 240 (SM.b2z (SM.t_8819 (c_in cx) j)) /\ u32 m (fr + 176) (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A81f54_at j: Inv_A81f54_at, SlotInv.v:2278 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81f54, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81f54_at : ctlcut := mkCtlCut
  0x81f54
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A81f64_at j: Inv_A81f64_at, SlotInv.v:2283 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81f64, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81f64_at : ctlcut := mkCtlCut
  0x81f64
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ rgv regs 10 (SM.t_k (c_in cx) j) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A81f7c_at j: Inv_A81f7c_at, SlotInv.v:2289 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81f7c, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81f7c_at : ctlcut := mkCtlCut
  0x81f7c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ rgv regs 10 (KNA.kind_name_addr (SM.t_k (c_in cx) j)) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A81f88_at j: Inv_A81f88_at, SlotInv.v:2295 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81f88, index [j], k <= 14+2j+1, own6, piece W4b
   superseded: App B 21:00Z/21:02Z: reac_ctrl_identity_reply has no image-A proof, so this site is a NEW cgif-form walk citing its t<fn>_spec, not a callee-cut
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81f88_at : ctlcut := mkCtlCut
  0x81f88
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ rgv regs 10 (KNA.kind_name_addr (SM.t_k (c_in cx) j)) /\
    MEM.bytes_at segs m (KNA.kind_name_addr (SM.t_k (c_in cx) j))
      (RKN.cstr_bytes (RKN.kind_name (SM.t_k (c_in cx) j))) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A81ff4_at j: Inv_A81ff4_at, SlotInv.v:2304 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x81ff4, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A81ff4_at : ctlcut := mkCtlCut
  0x81ff4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ b5_RC fr m /\
    rgv regs 10 (RRP.reply_ret phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j)) /\
    (RRP.reply_ok phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j) = true ->
       b5_RPost phi fr (SM.t_g (c_in cx) j) m) /\ IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A8206c_at j: Inv_A8206c_at, SlotInv.v:2313 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x8206c, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8206c_at : ctlcut := mkCtlCut
  0x8206c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ b5_RC fr m /\
    50 <= flen cx j /\ SM.t_sum_ok (c_in cx) j = true /\
    RRP.reply_ok phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j) = true /\
    b5_RPost phi fr (SM.t_g (c_in cx) j) m /\
    rgv regs 10 (phi + 34) /\ rgv regs 11 (RRP.ir_s (SM.t_g (c_in cx) j) - 8) /\ rgv regs 12 (phi + 38) /\
    rgv regs 13 (RRP.ir_s (SM.t_g (c_in cx) j) - 13) /\ rgv regs 14 0 /\ rgv regs 15 (phi + 34) /\
    IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A820ac_at j: Inv_A820ac_at, SlotInv.v:2325 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x820ac, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A820ac_at : ctlcut := mkCtlCut
  0x820ac
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ b5_RC fr m /\
    50 <= flen cx j /\ SM.t_sum_ok (c_in cx) j = true /\
    RRP.reply_ok phi (flen cx j) (fr + 256) (fr + 272) (fr + 304) (SM.t_g (c_in cx) j) = true /\
    b5_RPost phi fr (SM.t_g (c_in cx) j) m /\
    rgv regs 11 0 /\ rgv regs 12 (phi + 38) /\ rgv regs 13 (RRP.ir_s (SM.t_g (c_in cx) j) - 13) /\
    IDj cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A820f8_at j: Inv_A820f8_at, SlotInv.v:2336 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x820f8, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A820f8_at : ctlcut := mkCtlCut
  0x820f8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ b5_RC fr m /\
    50 <= flen cx j /\ (exists v, rgv regs 10 v /\ 0 <= v < 2 ^ 63) /\ IDb1 cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A820fc_at j: Inv_A820fc_at, SlotInv.v:2344 (shell b5_CUT :2133 → CUTST :436 (FRA :334 + ENT :378)); pc 0x820fc, index [j], k <= 14+2j+1, own6, piece W4b
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A820fc_at : ctlcut := mkCtlCut
  0x820fc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b5_body cx j bl fr regs m (fun phi fr regs m =>
       b5_K cx j phi fr regs m /\ b5_RC fr m /\
    RRP.ir (flen cx j) (SM.t_g (c_in cx) j) = false /\ IDb1 cx fr j m /\
    b5_F17 cx j phi fr regs m /\ b5_W240 cx j regs m /\ b5_PF cx j phi fr regs m)).

(* A82138_at j: Inv_A82138_at, SlotInv.v:2422 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82138, index [j], k <= 14+2j+1, own6, piece W4c
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82138_at : ctlcut := mkCtlCut
  0x82138
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       exists (A v280 : Z),
         
         rgv regs 9 A /\ rgv regs 25 (fragb fr) /\
         0 <= A < 2 ^ 64 /\ 0 <= v280 < 2 ^ 64 /\ v280 = SM.b2z (SM.t_sum_ok (c_in cx) j) /\
         
         STP.rw_cells segs m (A + 256)
           [CEL.C8 (Z_to_bv 64 (fr + 256)); CEL.C8 (Z_to_bv 64 (fr + 304)); CEL.C8 (Z_to_bv 64 (fr + 272))] /\
         STP.rw_cells segs m (fragb fr) [CEL.CB 72 (SM.t_FG (c_in cx) j)] /\
         ART.addressable m (fragb fr) 72 /\
         ART.addressable m (fr + 256) 2 /\ ART.addressable m (fr + 272) 8 /\ ART.addressable m (fr + 304) 8 /\
         MEM.bytes_at segs m BWA.REAL_BCMP (MEM.le8 (MEM.wa BWA.BCMP)) /\ MEM.bytes_at segs m BWA.REAL_MEMCMP (MEM.le8 (MEM.wa MCA.MEMCMP)) /\
         MEM.bytes_at segs m BWA.GOT_CF (MEM.le8 (MEM.wa BWA.CF)) /\
         MEM.bytes_at segs m (BWA.CF + 254) [Z_to_bv 8 1] /\ MEM.bytes_at segs m (BWA.CF + 255) [Z_to_bv 8 1] /\
         
         q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\ q64 m (A + 280) v280 /\
         MEM.bytes_at segs m (fr + 336) (SM.t_FG (c_in cx) j) /\ ART.addressable m (fr + 336) 72 /\
         
         q64 m (A + 80) (fragb fr + 15) /\ q64 m (A + 88) (fragb fr + 19) /\ q64 m (A + 96) (fragb fr + 8) /\
         q64 m (A + 272) (fr + 272) /\ q64 m (A + 264) (fr + 304) /\
         
         F16CARRY cx j fr phi A regs m /\ IFS1 cx fr j regs m).

(* A82154_at j: Inv_A82154_at, SlotInv.v:2452 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82154, index [j], k <= 14+2j+1, own6, piece W4c
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82154_at : ctlcut := mkCtlCut
  0x82154
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       exists (A v280 : Z),
         rgv regs 9 A /\ rgv regs 10 (RFR.fg_ret (frcl cx j fr phi)) /\
         0 <= A < 2 ^ 64 /\ 0 <= v280 < 2 ^ 64 /\ v280 = SM.b2z (SM.t_sum_ok (c_in cx) j) /\
         (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
         (phi + 50 <= Reusable.YG0d.spZ regs - FGA.REAC_CTRL_IDENTITY_FRAGMENT_K \/ Reusable.YG0d.spZ regs <= phi) /\
         
         q64 m (A + 184) (fr + 336) /\ q64 m (A + 192) (fragb fr) /\ q64 m (A + 280) v280 /\
         MEM.bytes_at segs m (fr + 336) (SM.t_FG (c_in cx) j) /\ ART.addressable m (fr + 336) 72 /\
         MEM.bytes_at segs m (fragb fr) (frrec cx j fr phi) /\ ART.addressable m (fragb fr) 72 /\
         MEM.bytes_at segs m BWA.REAL_BCMP (MEM.le8 (MEM.wa BWA.BCMP)) /\ MEM.bytes_at segs m BWA.REAL_MEMCMP (MEM.le8 (MEM.wa MCA.MEMCMP)) /\
         MEM.bytes_at segs m BWA.GOT_CF (MEM.le8 (MEM.wa BWA.CF)) /\
         MEM.bytes_at segs m (BWA.CF + 254) [Z_to_bv 8 1] /\ MEM.bytes_at segs m (BWA.CF + 255) [Z_to_bv 8 1] /\
         STP.rw_cells segs m (A + 256)
           [CEL.C8 (Z_to_bv 64 (fr + 256)); CEL.C8 (Z_to_bv 64 (fr + 304)); CEL.C8 (Z_to_bv 64 (fr + 272))] /\
         q64 m (A + 80) (fragb fr + 15) /\ q64 m (A + 88) (fragb fr + 19) /\ q64 m (A + 96) (fragb fr + 8) /\
         q64 m (A + 272) (fr + 272) /\ q64 m (A + 264) (fr + 304) /\
         FGA.fg_mem (fragb fr) (fr + 256) (fr + 272) (fr + 304) (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j)
           (frcl cx j fr phi) m /\
         F16CARRY cx j fr phi A regs m /\ IFS2 cx fr j regs m).

(* A82174_at j: Inv_A82174_at, SlotInv.v:2500 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82174, index [j], k <= 14+2j+1, own6, piece W4c
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82174_at : ctlcut := mkCtlCut
  0x82174
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       FLV cx fr j regs m /\
       exists (vcmp A : Z),
         SFA.memcmp_model (SM.t_FG (c_in cx) j) (frrec cx j fr phi) 72 = Some vcmp /\
         f14_tail cx j fr phi regs m A vcmp 0 /\ IFS2 cx fr j regs m).

(* A82178_at j: Inv_A82178_at, SlotInv.v:2514 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82178, index [j], k <= 14+2j+1, own6, piece W4c
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82178_at : ctlcut := mkCtlCut
  0x82178
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       FLV cx fr j regs m /\
       (exists A v w280 : Z, f14_tail cx j fr phi regs m A v w280) /\ IFS2 cx fr j regs m).

(* A821d0_at j: Inv_A821d0_at, SlotInv.v:2523 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x821d0, index [j], k <= 14+2j+1, own6, piece W4c
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A821d0_at : ctlcut := mkCtlCut
  0x821d0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       FLV cx fr j regs m /\
       
       SM.t_rf (c_in cx) j = 1 /\
       
       rgv regs 10 (fragb fr + 15) /\ rgv regs 15 (fragb fr + 15) /\ rgv regs 11 0 /\
       rgv regs 12 (fragb fr + 19) /\ rgv regs 13 (SM.f_pll (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j)) /\
       rgv regs 14 (SM.f_pll (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j) + 5) /\
       
       MEM.bytes_at segs m (fragb fr) (SM.t_FGf (c_in cx) j) /\ ART.addressable m (fragb fr) 72 /\
       SM.frag_ok (SM.t_FG (c_in cx) j) /\ FSj cx fr j regs m /\
       
       u16 m (fr + 256) (RFR.fg_addr (SM.t_FG (c_in cx) j) (SM.t_g (c_in cx) j)) /\
       
       (exists idb, MEM.bytes_at segs m (fr + 2688) idb /\ length idb = 38%nat) /\ ART.addressable m (fr + 2688) 38 /\
       exists A, rgv regs 9 A /\
         
         q64 m (A + 192) (fragb fr) /\ q64 m (A + 256) (fr + 256) /\ q64 m (A + 144) (fr + 2688) /\
         F17CARRY cx j fr phi A regs m /\ IFS2 cx fr j regs m /\
         
         rgv regs 5 (SM.fs_n (SM.fst_at (c_in cx) j))).

(* A8229c_at j: Inv_A8229c_at, SlotInv.v:2584 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8229c, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: App B 21:00Z/21:03Z: M12 confirmed (seg_F17/seg_F17b unproved on v1.9); route (a) re-proves the region in W4c, route (b) needs its own F17 proof first
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8229c_at : ctlcut := mkCtlCut
  0x8229c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       rgv regs 23 phi /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\
       (50 <= flen cx j -> ART.addressable m phi 50 /\ (exists rb, MEM.bytes_at segs m phi rb /\ (38 <= length rb)%nat)) /\
       (exists v0, rgv regs 10 v0 /\ 0 <= v0 < 2 ^ 63) /\
       (exists A, rgv regs 9 A /\
          q64 m (A + 232) (if SM.t_big (c_in cx) j then 0 else 1) /\
          q64 m (A + 200) (phi + 18) /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          (forall a, A + 88 <= a < A + 120 -> ART.HIGHMEM_BEG <= a < ART.APPMEM_END) /\
          (exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
             (SM.t_8819 (c_in cx) j = true -> w240 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w240 = 0)) /\
          rgv regs 24 (SM.t_k (c_in cx) j) /\
          (50 <= flen cx j ->
             rec_inv0 cx j fr phi A m /\
             (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
             (phi + 50 <= A + 88 \/ A + 120 <= phi)) /\
          (SM.t_8819 (c_in cx) j = true ->
             rec_parse cx j fr phi m /\
             (exists (ls rs : list byte),
                q64 m (A + 72) (fr + 186) /\ MEM.bytes_at segs m (fr + 186) ls /\ (6 <= length ls)%nat /\
                MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                ART.addressable m (fr + 186) 6) /\
             (exists (ls2 rs2 : list byte),
                q64 m (A + 64) (fr + 180) /\ MEM.bytes_at segs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
                MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                ART.addressable m (fr + 180) 6))) /\
       
       rgv regs 18 (flen cx j) /\
       (50 <= flen cx j ->
          MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
          Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
       spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       IFS3 cx fr j regs m /\ rgv regs 20 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j))).

(* A822a0_at j: Inv_A822a0_at, SlotInv.v:2626 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x822a0, index [j], k <= 14+2j+1, own6, piece W4c
   superseded: App B 21:00Z/21:03Z: M12 confirmed (seg_F17/seg_F17b unproved on v1.9); route (a) re-proves the region in W4c, route (b) needs its own F17 proof first
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A822a0_at : ctlcut := mkCtlCut
  0x822a0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       rgv regs 23 phi /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\
       (50 <= flen cx j -> ART.addressable m phi 50 /\ (exists rb, MEM.bytes_at segs m phi rb /\ (38 <= length rb)%nat)) /\
       (exists A, rgv regs 9 A /\
          q64 m (A + 232) (if SM.t_big (c_in cx) j then 0 else 1) /\
          q64 m (A + 200) (phi + 18) /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          (forall a, A + 88 <= a < A + 120 -> ART.HIGHMEM_BEG <= a < ART.APPMEM_END) /\
          (exists w240, q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
             (SM.t_8819 (c_in cx) j = true -> w240 <> 0) /\ (SM.t_8819 (c_in cx) j = false -> w240 = 0)) /\
          rgv regs 24 (SM.t_k (c_in cx) j) /\
          (50 <= flen cx j ->
             rec_inv0 cx j fr phi A m /\
             (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
             (phi + 50 <= A + 88 \/ A + 120 <= phi)) /\
          (SM.t_8819 (c_in cx) j = true ->
             rec_parse cx j fr phi m /\
             (exists (ls rs : list byte),
                q64 m (A + 72) (fr + 186) /\ MEM.bytes_at segs m (fr + 186) ls /\ (6 <= length ls)%nat /\
                MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0 /\
                ART.addressable m (fr + 186) 6) /\
             (exists (ls2 rs2 : list byte),
                q64 m (A + 64) (fr + 180) /\ MEM.bytes_at segs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
                MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0 /\
                ART.addressable m (fr + 180) 6))) /\
       
       rgv regs 18 (flen cx j) /\
       (50 <= flen cx j ->
          MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
          Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
       spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       IFS3 cx fr j regs m /\ rgv regs 20 (1 - SM.b2z (SM.t_sum_ok (c_in cx) j))).

(* A823e8_at j: Inv_A823e8_at, SlotInv.v:2668 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x823e8, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A823e8_at : ctlcut := mkCtlCut
  0x823e8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       (exists (A w240 : Z),
          rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ Reusable.YG0d.spZ regs <= A /\
          rgv regs 23 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 22 (if SM.t_big (c_in cx) j then phi + 18 else 0) /\
          (50 <= flen cx j -> rec_inv0 cx j fr phi A m) /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          q64 m (A + 240) w240 /\ 0 <= w240 < 2 ^ 64 /\
          (SM.t_8819 (c_in cx) j = false -> w240 = 0) /\
          (SM.t_8819 (c_in cx) j = true ->
             w240 <> 0 /\ rec_parse cx j fr phi m /\
             exists (ls rs ls2 rs2 : list byte),
               q64 m (A + 72) (fr + 186) /\
               MEM.bytes_at segs m (fr + 186) ls /\ (6 <= length ls)%nat /\
               MEM.bytes_at segs m phi rs /\ (6 <= length rs)%nat /\
               SFA.memcmp_model ls rs 6 = Some 0 /\
               ART.addressable m (fr + 186) 6 /\ ART.addressable m phi 6 /\
               (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi) /\
               q64 m (A + 64) (fr + 180) /\
               MEM.bytes_at segs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
               MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\
               SFA.memcmp_model ls2 rs2 6 = Some 0 /\
               ART.addressable m (fr + 180) 6 /\ ART.addressable m (phi + 6) 6)) /\
       
       rgv regs 18 (flen cx j) /\ rgv regs 25 (fr + 64) /\
       (50 <= flen cx j ->
          MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
          Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j) /\
       spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\ spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       LT cx fr j regs m).

(* A82400_at j: Inv_A82400_at, SlotInv.v:2708 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82400, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82400_at : ctlcut := mkCtlCut
  0x82400
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       (exists (A : Z) (ls2 rs2 : list byte),
          rgv regs 9 A /\ 0 <= A < 2 ^ 64 /\ Reusable.YG0d.spZ regs <= A /\
          rgv regs 23 phi /\ rgv regs 24 (SM.t_k (c_in cx) j) /\ rgv regs 10 0 /\ rgv regs 22 (phi + 18) /\
          rec_inv cx j fr phi A m /\
          q64 m (A + 136) (fr + 128) /\ q64 m (A + 120) (fr + 160) /\ q64 m (A + 176) (fr + 64) /\
          q64 m (A + 64) (fr + 180) /\
          MEM.bytes_at segs m (fr + 180) ls2 /\ (6 <= length ls2)%nat /\
          MEM.bytes_at segs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\
          SFA.memcmp_model ls2 rs2 6 = Some 0 /\
          ART.addressable m (fr + 180) 6 /\ ART.addressable m (phi + 6) 6 /\
          (phi + 50 <= Reusable.YG0d.spZ regs - BWA.BCMP_WRAP_K \/ Reusable.YG0d.spZ regs <= phi)) /\
       
       rgv regs 18 (flen cx j) /\ spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
       MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
       Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j /\ LT cx fr j regs m).

(* A82418_at j: Inv_A82418_at, SlotInv.v:2737 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82418, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82418_at : ctlcut := mkCtlCut
  0x82418
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       rgv regs 23 phi /\ rgv regs 20 (phi + 18) /\ rgv regs 22 (phi + 18) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
       rgv regs 10 0 /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       spill regs m 136 (fr + 128) /\ spill regs m 120 (fr + 160) /\ spill regs m 176 (fr + 64) /\
       (exists v14 v15 v16 v17 field16,
          spill regs m 248 (fr + 176) /\
          u16 m (fr + 196) field16 /\
          b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\
          b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
          0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
          b8 m (Z.shiftr (phi + 14) 3 + A.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 15) 3 + A.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 16) 3 + A.ACtlK.ASAN_K) 0 /\
          b8 m (Z.shiftr (phi + 17) 3 + A.ACtlK.ASAN_K) 0 /\
          field16 = v14 + 256 * v15 /\
          (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if SM.t_k (c_in cx) j =? 1 then 1 else 0)) /\
       
       rgv regs 18 (flen cx j) /\ spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
       MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
       Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j /\ LT cx fr j regs m).

(* A824b4_at j: Inv_A824b4_at, SlotInv.v:2770 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x824b4, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A824b4_at : ctlcut := mkCtlCut
  0x824b4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\ LK cx fr j regs m /\
       rgv regs 10 (if RMO.blocksum (SM.t_blk (c_in cx) j) =? 0 then 0 else -1) /\
       rgv regs 23 phi /\ rgv regs 20 (phi + 18) /\ rgv regs 22 (phi + 18) /\ rgv regs 24 (SM.t_k (c_in cx) j) /\
       0 < phi /\ phi + 50 <= 2 ^ 64 /\ 50 <= flen cx j /\ 0 <= SM.t_k (c_in cx) j < 2 ^ 64 /\
       MEM.bytes_at segs m (phi + 18) (SM.t_blk (c_in cx) j) /\
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
       spill regs m 280 (SM.b2z (SM.t_sum_ok (c_in cx) j)) /\
       spill regs m 136 (fr + 128) /\ spill regs m 120 (fr + 160) /\ spill regs m 176 (fr + 64) /\
       
       rgv regs 18 (flen cx j) /\ spill regs m 152 (SM.b2z (SM.t_tfill (c_in cx) j)) /\
       MEM.bytes_at segs m phi (SM.t_g (c_in cx) j) /\ MEM.bytes_at segs m phi (SM.t_phi (c_in cx) j) /\
       Z.of_nat (length (SM.t_phi (c_in cx) j)) <= flen cx j /\ LT cx fr j regs m).

(* A82554_at j: Inv_A82554_at, SlotInv.v:2822 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x82554, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82554_at : ctlcut := mkCtlCut
  0x82554
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       MEM.bytes_at segs m (phi + 34) (RFR.bsl (SM.t_g (c_in cx) j) 34 6) /\
    RPA.cp_v (SM.t_g (c_in cx) j) 18 = 4 /\ RPA.cp_v (SM.t_g (c_in cx) j) 19 = 3 /\
    rgv regs 10 (phi + 34) /\ rgv regs 12 (phi + 34) /\ rgv regs 13 6 /\ rgv regs 11 0)).

(* A825a0_at j: Inv_A825a0_at, SlotInv.v:2829 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x825a0, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A825a0_at : ctlcut := mkCtlCut
  0x825a0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       rgv regs 10 (SM.t_want_v (c_in cx) j) /\ rgv regs 20 (SM.t_want_v (c_in cx) j))).

(* A825c8_at j: Inv_A825c8_at, SlotInv.v:2835 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x825c8, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A825c8_at : ctlcut := mkCtlCut
  0x825c8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       rgv regs 20 (fr + 128) /\
    u32 m (fr + 128) (-7) /\ u32 m (fr + 132) (-7) /\ u32 m (fr + 136) (-7) /\
    ART.addressable m (fr + 128) 12)).

(* A825d4_at j: Inv_A825d4_at, SlotInv.v:2842 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x825d4, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A825d4_at : ctlcut := mkCtlCut
  0x825d4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       rgv regs 10 (SM.t_rp (c_in cx) j) /\ PORTS cx fr j m /\ ART.addressable m (fr + 128) 12)).

(* A825f4_at j: Inv_A825f4_at, SlotInv.v:2848 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x825f4, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A825f4_at : ctlcut := mkCtlCut
  0x825f4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       rgv regs 25 (SM.t_rp (c_in cx) j) /\ rgv regs 10 (SM.t_unk (c_in cx) j) /\
    PORTS cx fr j m /\ FIRSTb cx fr j m /\
    ART.addressable m (fr + 128) 12 /\ ART.addressable m (fr + 160) 1)).

(* A82604_at j: Inv_A82604_at, SlotInv.v:2855 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x82604, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82604_at : ctlcut := mkCtlCut
  0x82604
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       rgv regs 25 (SM.t_rp (c_in cx) j) /\ rgv regs 20 (SM.t_unk (c_in cx) j) /\ rgv regs 10 (SM.t_unk (c_in cx) j) /\
    PORTS cx fr j m /\ FIRSTb cx fr j m /\
    ART.addressable m (fr + 128) 12 /\ ART.addressable m (fr + 160) 1)).

(* A8265c_at j: Inv_A8265c_at, SlotInv.v:2863 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x8265c, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8265c_at : ctlcut := mkCtlCut
  0x8265c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       SM.t_rp (c_in cx) j = 0 /\ 0 <= SM.t_unk (c_in cx) j /\ rgv regs 20 (SM.t_unk (c_in cx) j) /\ rgv regs 7 (fr + 128) /\
    PORTS cx fr j m /\ FIRSTb cx fr j m /\
    rgv regs 10 (phi + 26) /\ rgv regs 14 (phi + 26) /\ rgv regs 15 12 /\
    rgv regs 11 0 /\ rgv regs 12 0 /\ rgv regs 13 0 /\ rgv regs 16 0)).

(* A826d4_at j: Inv_A826d4_at, SlotInv.v:2873 (shell B7CUT :2815 → CUTST :436 (FRA :334 + ENT :378)); pc 0x826d4, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A826d4_at : ctlcut := mkCtlCut
  0x826d4
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     FRAC cx fr sel regs m /\
     b7_body cx j bl fr regs m (fun phi fr regs m =>
       SM.t_rp (c_in cx) j = 0 /\ 0 <= SM.t_unk (c_in cx) j /\ rgv regs 20 (SM.t_unk (c_in cx) j) /\ rgv regs 7 (fr + 128) /\
    PORTS cx fr j m /\ FIRSTb cx fr j m /\
    rgv regs 12 (RLF.n_in (SM.t_pbs (c_in cx) j)) /\ rgv regs 11 (RLF.n_out (SM.t_pbs (c_in cx) j)) /\
    rgv regs 13 (RLF.cnt SM.is_empty (SM.t_pbs (c_in cx) j) 12) /\
    rgv regs 17 (RPO.pu_first (SM.t_pbs (c_in cx) j) 12))).

(* A82750_at j: Inv_A82750_at, SlotInv.v:2889 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82750, index [j], k <= 14+2j+1, own6, piece W4d
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82750_at : ctlcut := mkCtlCut
  0x82750
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLS cx j phi fr regs m /\ LT cx fr j regs m)).

(* A8275c_at j: Inv_A8275c_at, SlotInv.v:2897 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8275c, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8275c_at : ctlcut := mkCtlCut
  0x8275c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLS cx j phi fr regs m /\ LT cx fr j regs m)).

(* A82798_at j: Inv_A82798_at, SlotInv.v:2905 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82798, index [j], k <= 14+2j+1, own6, piece W4e
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82798_at : ctlcut := mkCtlCut
  0x82798
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLS cx j phi fr regs m /\
        rgv regs 10 (RCL.cl_r (SM.t_cls (c_in cx) j)) /\
        MEM.bytes_at segs m (fr + 448) (SM.t_B (c_in cx) j) /\
        ART.addressable m (fr + 452) 6 /\
        (forall e, SM.t_cls (c_in cx) j = Some e -> u32 m (fr + 528) e) /\
        LT cx fr j regs m)).

(* A827d8_at j: Inv_A827d8_at, SlotInv.v:2917 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x827d8, index [j], k <= 14+2j+1, own6, piece W4e
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A827d8_at : ctlcut := mkCtlCut
  0x827d8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLS cx j phi fr regs m /\
        SM.t_cls (c_in cx) j <> None /\
        (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 0 <-> firstn 6 (skipn 4 (SM.t_B (c_in cx) j)) = SM.OUR (c_in cx)) /\
        (forall e, SM.t_cls (c_in cx) j = Some e -> u32 m (fr + 528) e) /\
        LT cx fr j regs m)).

(* A82800_at j: Inv_A82800_at, SlotInv.v:2930 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82800, index [j], k <= 14+2j+1, own6, piece W4e
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82800_at : ctlcut := mkCtlCut
  0x82800
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLS cx j phi fr regs m /\ LT cx fr j regs m)).

(* A8285c_at j: Inv_A8285c_at, SlotInv.v:2946 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8285c, index [j], k <= 14+2j+1, own6, piece W4e
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8285c_at : ctlcut := mkCtlCut
  0x8285c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLSX cx j phi fr regs m /\
        SM.t_rowsel (c_in cx) j = true /\
        rgv regs 10 CATA.BOX_CATALOGUE /\ rgv regs 24 (fr + 32) /\ q64 m (fr + 32) 11 /\
        LT cx fr j regs m)).

(* A8286c_at j i: Inv_A8286c_at, SlotInv.v:2956 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8286c, index [j; i], k <= 14+2j+1, own6, piece W4e
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8286c_at : ctlcut := mkCtlCut
  0x8286c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ (i <= 10)%nat /\ RL cx j i phi fr regs m /\ LT cx fr j regs m)).

(* A82888_at j i: Inv_A82888_at, SlotInv.v:2963 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82888, index [j; i], k <= 14+2j+1, own6, piece W4e
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82888_at : ctlcut := mkCtlCut
  0x82888
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ (i <= 10)%nat /\ RL cx j i phi fr regs m /\
        rgv regs 10 1 /\
        MEM.bytes_at segs m (fr + 64) (SM.decl_i (Z.of_nat i)) /\ ART.addressable m (fr + 64) 32 /\
        LT cx fr j regs m)).

(* A8289c_at j i: Inv_A8289c_at, SlotInv.v:2973 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x8289c, index [j; i], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A8289c_at : ctlcut := mkCtlCut
  0x8289c
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ RL cx j i phi fr regs m /\
        (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 0 <-> SM.t_blk (c_in cx) j = SM.decl_i (Z.of_nat i)) /\
        MEM.bytes_at segs m (fr + 64) (SM.decl_i (Z.of_nat i)) /\ ART.addressable m (fr + 64) 32 /\
        LT cx fr j regs m)).

(* A828a0_at j i: Inv_A828a0_at, SlotInv.v:2983 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x828a0, index [j; i], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A828a0_at : ctlcut := mkCtlCut
  0x828a0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     let i := ixn 1 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ RL cx j i phi fr regs m /\
        SM.t_blk (c_in cx) j <> SM.decl_i (Z.of_nat i) /\ ART.addressable m (fr + 64) 32 /\
        LT cx fr j regs m)).

(* A828bc_at j: Inv_A828bc_at, SlotInv.v:2992 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x828bc, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A828bc_at : ctlcut := mkCtlCut
  0x828bc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLSX cx j phi fr regs m /\
        SM.t_rowsel (c_in cx) j = true /\ SM.t_want_m (c_in cx) j = 0 /\ LT cx fr j regs m)).

(* A828c0_at j: Inv_A828c0_at, SlotInv.v:3007 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x828c0, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A828c0_at : ctlcut := mkCtlCut
  0x828c0
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLSX cx j phi fr regs m /\
        rgv regs 20 (SM.t_want_m (c_in cx) j) /\ LT cx fr j regs m)).

(* A828c8_at j: Inv_A828c8_at, SlotInv.v:2938 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x828c8, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A828c8_at : ctlcut := mkCtlCut
  0x828c8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLS cx j phi fr regs m /\
        SM.t_rowsel (c_in cx) j = false /\ LT cx fr j regs m)).

(* A828cc_at j: Inv_A828cc_at, SlotInv.v:3015 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x828cc, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A828cc_at : ctlcut := mkCtlCut
  0x828cc
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLSX cx j phi fr regs m /\
        rgv regs 20 (SM.t_want_m (c_in cx) j) /\ LT cx fr j regs m)).

(* A828d8_at j: Inv_A828d8_at, SlotInv.v:3023 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x828d8, index [j], k <= 14+2j+1, own6, piece W4f
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A828d8_at : ctlcut := mkCtlCut
  0x828d8
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLSX cx j phi fr regs m /\
        rgv regs 20 (SM.t_want_m (c_in cx) j) /\ rgv regs 10 (SM.t_want (c_in cx) j) /\ LT cx fr j regs m)).

(* A82940_at j: Inv_A82940_at, SlotInv.v:3032 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82940, index [j], k <= 14+2j+2, own6, piece W4f
   live list (table): entry blocks *)
Definition C_A82940_at : ctlcut := mkCtlCut
  0x82940
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 2)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ LK cx fr j regs m /\ FLSF cx j phi fr regs m /\ LT cx fr j regs m).

(* A82964_at j: Inv_A82964_at, SlotInv.v:3000 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82964, index [j], k <= 14+2j+1, own6, piece W4e
   superseded: App B 21:02Z: callee-cut site now cites the callee t<fn>_spec in cgif form (cut points no longer pending)
   live list (table): entry ++ [(φ, flen g j)] (Perm; ctrl stores a_size) *)
Definition C_A82964_at : ctlcut := mkCtlCut
  0x82964
  own6
  (fun _ idx => 14 + 2 * Z.of_nat (ixn 0 idx) + 1)
  (fun cx idx bl fr sel regs m =>
     let j := ixn 0 idx in
     exists phi,
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx) ++ [(phi, flen cx j)]) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen cx j) /\ FLSI cx j fr regs m /\
       (LK cx fr j regs m /\ FLSX cx j phi fr regs m /\
        rgv regs 20 (SM.t_want_m (c_in cx) j) /\ LT cx fr j regs m)).

(* A82b04: Inv_A82b04, SlotInv.v:3044 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82b04, index [], k <= 526 (≤ EV_LIB), own6, piece W5
   live list (table): entry blocks *)
Definition C_A82b04 : ctlcut := mkCtlCut
  0x82b04
  own6
  (fun _ _ => A.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\
    spill regs m 144 (fr + 2688) /\
    (exists nm, MEM.bytes_at segs m (fr + 2688) nm /\ length nm = 21%nat /\
       SFA.find_byte 0 (firstn 17 (skipn 3 nm)) <> None) /\
    ART.addressable m (fr + 2691) 17).

(* A82b20: Inv_A82b20, SlotInv.v:3051 (shell CUTST :436 (FRA :334 + ENT :378)); pc 0x82b20, index [], k <= 526 (≤ EV_LIB), own6, piece W5
   live list (table): entry blocks *)
Definition C_A82b20 : ctlcut := mkCtlCut
  0x82b20
  own6
  (fun _ _ => A.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAC cx fr sel regs m /\
     c_n cx < 2 ^ 26 /\ OURb cx fr m /\ (exists q, a0v regs q /\ 0 < q < 2 ^ 64)).

(* Jrel: Inv_Jrel, SlotInv.v:3064 (shell CUTST0 :490 (FRAH :448 + ENT :378)); pc 0x82b80, index [], k <= 526 (≤ EV_LIB), own6, piece W5
   live list (table): entry blocks *)
Definition C_Jrel : ctlcut := mkCtlCut
  0x82b80
  own6
  (fun _ _ => A.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x41b58ab3 regs m /\
     rgv regs 21 sel /\ rgv regs 22 fr).

(* A82b9c: Inv_A82b9c, SlotInv.v:3069 (shell CUTSTR :496 (FRAH :448 + ENT :378)); pc 0x82b9c, index [], k <= 526 (≤ EV_LIB), own6, piece W5
   live list (table): entry blocks *)
Definition C_A82b9c : ctlcut := mkCtlCut
  0x82b9c
  own6
  (fun _ _ => A.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     FRAHC cx fr sel 0x45e0360e regs m /\
     sel = fr /\ a0v regs fr /\ rgv regs 11 FRAME_BYTES).

(* A82bac: Inv_A82bac, SlotInv.v:3073 (shell CUTSTR :496 (FRAH :448 + ENT :378)); pc 0x82bac, index [], k <= 526 (≤ EV_LIB), own0, piece W5
   live list (table): entry blocks
   NO RECORD (a Theorem Labs lane 21:52Z).  This is the release join of the CLASS-FULL REAL-STACK arm (ctrl's selector 0).
   That arm is not a live case: the stage at the fake-stack call discharges the machine's s5 = 0 branch from
   astack_malloc_realizes (donor YG0d.v:284-299) and stack_malloc_progress (YG05.v:69-84), since frames S = []
   at the entry.  No stage reaches this pc and the composition must not name it, so the row is transcribed as
   this note and NOT as a ctlcut.  Its ctrl text, for the record: Inv_A82bac SlotInv.v:3073,
   CUTSTR 0x82bac with `s5 = 0 /\ a0v regs (Sfr fr) /\ rg regs 11 FRAME_SHADOW`. *)

(* A82bb0: Inv_A82bb0, SlotInv.v:3087 (shell own (no FRA)); pc 0x82bb0, index [], k <= 526 (≤ EV_LIB), own0, piece W5
   live list (table): entry blocks *)
Definition C_A82bb0 : ctlcut := mkCtlCut
  0x82bb0
  own0
  (fun _ _ => A.ACtlK.EV_LLVMF)
  (fun cx idx bl fr sel regs m =>
     Permutation bl (Reusable.YG0d.ablocks B (c_ly cx) (c_S cx)) /\
     rgv regs 8 (c_sp cx) /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 3 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (c_regs cx) 4 /\
    MEM.bytes_at segs m (c_sp cx - 104) (saved_bytes cx)).

End CtlCutP.
