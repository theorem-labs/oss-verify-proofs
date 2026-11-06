From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* fuzz_pcap's entry contract (row 11, the ASan build of libreac v1.9.0, image fuzz_pcap.asan sha256
   b7a91d9b1fb0017d...) at the instance: PcapEntryFinal.pcap_entry_final at SK := PcapSinkHeads.asan_sink_head (the
   ASan image's ofl_head 0x5f4f88, lib/Reusable/PcapSinkHeads.v:37, passed BY NAME at every sink-head position, as
   cgif's released instance passes tfib_sink_head, cgif lib/A/ACee.v:56), B := AD2l.PcapB (the core's concrete
   asyms), MT := YCbp.ameter_triv and XM_LIB = XN_LIB := fun _ => 0, in the form of cgif_file_fuzzer's released
   lib/A/ACed.v:102-104 (tfibX_AMALLOC4 / tfibX_AFREE4 / tfibX_AFREEN4) and lib/A/ACee.v (origin/ossv/recipes
   c8557374ad2e). pcap_entry_final stays general in SK; only this instance fixes it (a Theorem Labs lane, 11:32Z).

   Discharges (each by `fit`, which demands that the lemma's conclusion is SYNTACTICALLY the premise and logs as
   `ARGS_FIT CONVERSION` each argument whose type is its premise only up to conversion; `fitc` is `fit` that also
   accepts a conclusion that is the goal only up to conversion and logs it as a `CONCL_FIT CONVERSION` line; `fitc`
   is used only at the ruled conversions below):
     MTL      YCbp.ameter_triv_laws                    lib/Reusable/YCbp.v:21                      constr_eq
     HXM      PcapEntryDefs.pe_need_triv_budget        lib/A/Prog/PcapEntryDefs.v:568              constr_eq
     HXMN     inst_HXMN (lia)                          this file                                    constr_eq
     HMRA     inst_HMRA (computation: as_code PcapB = Tfib_code, AD2l.v:19)   this file           constr_eq
     HFRA     inst_HFRA (the same)                     this file                                    constr_eq
     HUNIV    AD2l.PcapB_universe                      lib/A/AD2l.v:43                              constr_eq
     MFSL     YCbp.ameter_triv_fs_laws                 lib/Reusable/YCbp.v:23                       constr_eq
     ML       PcapBFacts.PcapB_ML                      lib/A/PcapBFacts.v:53                        constr_eq
     LAWS     inst_LAWS: PcapBFacts.PcapB_LAWS         lib/A/PcapBFacts.v:57                        conversion
     AM       inst_AM: PcapBFacts.PcapB_AMALLOC4       lib/A/PcapBFacts.v:60                        conversion
     AF       inst_AF: PcapBFacts.PcapB_AFREE4         lib/A/PcapBFacts.v:62                        conversion
     ASM1     inst_ASM1: AF0s.stack_malloc1_contract at PcapB with PcapB_LAWS and AD2l.PcapB_syms
                                                       lib/A/AF0s.v:520                             conversion
     pcap_G_harness_gx_ok     inst_gx_ok: PcapGHarness.pcap_G_harness_gx_ok PcapB PcapB_syms
                                                       lib/A/PcapGHarness.v:97                      conversion
     pcap_G_harness_pe_bytes  inst_pe_bytes: PcapGHarness.pcap_G_harness_pe_bytes PcapB PcapB_syms
                                                       lib/A/PcapGHarness.v:109                     conversion
     ASM0     inst_ASM0: StackMalloc0.stack_malloc0_contract at PcapB with PcapB_LAWS and AD2l.PcapB_syms
                                                       lib/A/StackMalloc0.v:520                     conversion
     AMM      inst_AMM: Memmove.asan_memmove_contract at PcapB with PcapB_LAWS and AD2l.PcapB_syms
                                                       lib/A/Rt/Memmove.v:147                       conversion
     HGRO     inst_HGRO: PcapGHarness.pcap_hg_ro PcapB PcapB_syms, at ro_chunk_addr := PcapGHarness.ro_chunk_addr
                                                       lib/A/PcapGHarness.v:140                     conversion
     HROI     inst_HROI: AD1o.ro_img_of_arodata PcapB (w_H W) mem PcapB_syms, at ROI := AE3i.ro_img
                                                       lib/A/AD1o.v:49                              conversion
     HCPY     inst_HCPY: AE2q.asan_memcpy_realizes PcapB PcapB_LAWS PcapB_syms (__asan_memcpy, 0x51514)
                                                       lib/A/AE2q.v:144                             conversion
     HSET     inst_HSET (bridge, premise order): AE2r.asan_memset_realizes PcapB PcapB_LAWS PcapB_syms
              (__asan_memset, 0x519b0) with its premises reordered: amem_range d n moved back behind dest_ok
              (YG0d.v:322) and OSet's `True` premise (YG0d.v:324-327) dropped
                                                       lib/A/AE2r.v:568                             conversion
     ASIL     inst_ASIL: AD1u.tfib_ASIL at SK := asan_sink_head, with inst_pcap_head (sk_ofl_head asan_sink_head
              = 0x5f4f88, AD1u.v:54, by computation on the closed term)
                                                       lib/A/AD1u.v:86                              conversion
     RO       inst_RO: the read-only segments of Asan.M.loaded_segments end below 0x5f4f88 (vm_compute) and the
              RELRO window PCAP_RLO .. PCAP_RHI = 0x992d0 .. 0x9a528 lies below it (the A image's form of lib/B's
              pcap_ro_below, a working branch 08efd9be8f0 lib/B/Prog/PcapEntryTop.v:285)
                                                       this file                                    conversion
     FI       inst_FI: fi_sep = PcapFuzzFopen.fopen_img_tables's third conjunct (PcapFuzzFopen.v:496); fi_head
              and fi_kimg by computation at SK := asan_sink_head and pcap_KS
                                                       this file                                    conversion
     MCONSTS  inst_MCONSTS (bridge): proj2 of AE2j.strchr_lit_ro_of_img W mem (AE2j.v:99), at mc_lo / mc_hi :=
              AE39.MC_LO / AE39.MC_HI (0x10350 / 0x10370, AE39.v:31 mc_bounds)
                                                       lib/A/AE2j.v:99                              conversion
     ABCMP    inst_ABCMP: AE2s.bcmp_icpt_contract at PcapB with PcapB_LAWS and AD2l.PcapB_syms (the contract of
              __interceptor_trampoline_bcmp at 0x41570 = AE2s.MC_ENTRY, AE2s.v:31)
                                                       lib/A/AE2s.v:712                             conversion
     HPATH    inst_HPATH: PcapHPath.pcap_path_addressable at PcapB with AD2l.PcapB_syms, segs := pa_segs PI_pcap (the
              13 bytes of the listing's object 3 = 0x20d00, "<fuzz-input>" and its NUL)
                                                       lib/A/PcapHPath.v:38                         conversion
     TL       PcapInstLib.PcapB_PALib                  lib/A/Prog/PcapInstLib.v:37                  constr_eq
     TLF      PcapInstLib.PcapB_PALibF                 lib/A/Prog/PcapInstLib.v:52                  constr_eq
     FFL      PcapInstLib.PcapB_FFL                    lib/A/Prog/PcapInstLib.v:62                  constr_eq
     ROIMG_KEPT  inst_ROIMG_KEPT: PcapRoBridges.pcap_roimg_kept
                                                       lib/A/PcapRoBridges.v:38                     conversion
     ROIMG_LOW   inst_ROIMG_LOW: PcapRoBridges.pcap_roimg_low
                                                       lib/A/PcapRoBridges.v:48                     conversion
     FM       PFcloseInst.inst_FM                      lib/A/Stdio/PFcloseInst.v:109                constr_eq
     AFCLOSE  PFcloseInst.inst_AFCLOSE, at ra_fc1 / ra_fc2 := WFcloseI.WFI_FREE1 / WFcloseI.WFI_JOIN
                                                       lib/A/Stdio/PFcloseInst.v:130                constr_eq
     HUfc1    PFcloseInst.inst_HUfc1                   lib/A/Stdio/PFcloseInst.v:148                constr_eq
     HUfc2    PFcloseInst.inst_HUfc2                   lib/A/Stdio/PFcloseInst.v:153                constr_eq
     STRCMP   inst_STRCMP: StrcmpPath.astrcmp_path_at_of_syms at PcapB, segs := pa_segs PI_pcap, ROI := AE3i.ro_img,
              pc := the strcmp trampoline, x := object FO_PATH, with PcapB_LAWS, AD2l.PcapB_syms, the ROI premise
              fun m H => H and the three equations by eq_refl
                                                       lib/A/Rt/StrcmpPath.v:58                     constr_eq at the
                                                                                         conclusion, conversion at
                                                                                         the three equations
   The parameters ROI, ro_chunk_addr, mc_lo, mc_hi, ra_fc1 and ra_fc2 are values: AE3i.ro_img (lib/A/AE3i.v:76),
   PcapGHarness.ro_chunk_addr (lib/A/PcapGHarness.v:127, the bytes of AE3i's img_ro_chunks), AE39.MC_LO and
   AE39.MC_HI (lib/A/AE39.v:27-28, the window of __strchrnul's constants; a Theorem Labs lane's pcap_afmemopen_closed,
   a working branch c5180b0bcf1 lib/A/Stdio/PFmemopenC.v:23, states the same window, so AFMEMOPEN
   stays a hypothesis at these values), WFcloseI.WFI_FREE1 and WFcloseI.WFI_JOIN (lib/A/Stdio/WFcloseI.v:87-88,
   0x8e2b8 / 0x8e2c0: the return pcs of musl fclose's two free calls, the rows of ACej.TRACES_fclose, ACej.v:73-75;
   the values PFcloseInst.inst_AFCLOSE, inst_HUfc1 and inst_HUfc2 state).
   CLOSE (pb_pcap_source_closeX) and ASF (YG0t.astack_free_law_ok) are discharged inside pcap_entry_final, general in B.
   pcap_entry_final has no afree_null04_rule premise, so PcapBFacts.PcapB_AFREEN4 is not used. Each lemma that takes
   a sink head gets asan_sink_head by name (the @ form or a named argument): no instance search picks one.
   Every conversion is delta (with iota) of named Definitions only, the class a Theorem Labs lane ruled for ASIL (08:16Z) and
   FOPEN (08:4xZ): AB1v.tfibsegs := Asan.M.loaded_segments (lib/A/AB1v.v:13) and pa_segs PI_pcap :=
   Asan.M.loaded_segments (lib/A/Prog/PcapEntryTop.v:140-141) at every site; at ASM0 also NX_CID := 0
   (PcapSourceNextSpec.v:47), at AMM also pa_sigma PI_pcap PS___asan_memmove = 0x51bf0 (PcapAddr.v:41) (a Theorem Labs lane,
   10:2xZ); at HGRO and HROI also pa_relro_lo / pa_relro_hi PI_pcap := PCAP_RLO / PCAP_RHI (PcapEntryTop.v:154-155),
   and at HROI ACeg's arodata_ok / in_ro_tfa = PcapBase's arodata_okP / in_roP at tfibsegs, PCAP_RLO, PCAP_RHI
   (ACeg.v:60-65, PcapBase.v:17-22); at HCPY also aintrin_realizes OCpy (YG0d.v:318-336, with its match on the
   memop), which the lemma states unfolded, and pa_sigma PI_pcap PS___asan_memcpy = 0x51514 (PcapAddr.v:19); at HSET
   the same with OSet and pa_sigma PI_pcap PS___asan_memset = 0x519b0 (PcapAddr.v:20); at RO also sk_ofl_head
   asan_sink_head = 0x5f4f88 (PcapSinkHeads.v:37); at FI pa_val PI_pcap = PcapEntryTop.pcap_val (PcapEntryTop.v:67,
   :144) on the objects FO_LEN / FO_FILE; at MCONSTS mconsts_view (AE39.v:29-30), stated at tfibsegs; at ABCMP also
   pa_sigma PI_pcap PS___interceptor_trampoline_bcmp = 0x41570 (PcapEntryTop.v:145, PcapAddr.v:24); at HPATH pa_val
   PI_pcap (A_OBJ 3) = pcap_val (A_OBJ 3) = pcap_obj 3 = 0x20d00 (PcapEntryTop.v:67-68, :144, PcapAddr.v:49); at
   ROIMG_LOW also PcapFuzzFopenG.roimg_low (PcapFuzzFopenG.v:44-46); at STRCMP the three equations of
   astrcmp_path_at_of_syms: pa_segs PI_pcap = tfibsegs, pa_sigma PI_pcap PS___interceptor_trampoline_strcmp = 0x41564
   = StrcmpDef.SM_ENTRY (PcapAddr.v:14, StrcmpDef.v:35) and pa_val PI_pcap (A_OBJ FO_PATH) = pcap_obj 3 = 0x20d00 =
   StrcmpDef.A_FUZZ_PATH (PcapFuzzFopen.FO_PATH := 3, PcapAddr.v:49, StrcmpDef.v:36). Each site carries a
   `conversion:` comment, and the build log shows each one as a CONCL_FIT or ARGS_FIT CONVERSION line.
   Each discharger is passed BY NAME: the @ form with every argument written (a Theorem Labs lane's rule), so a reordered
   binder fails loudly.

   Every other premise of pcap_entry_final is a Section hypothesis of this file, with its name, its type at
   SK := asan_sink_head, B := PcapB, MT := ameter_triv, and its owner (the source files are in PcapEntryFinal.v's
   header table; owners as a Theorem Labs lane's map, 11:33Z). Every implicit argument of class type (sink head, FPState,
   RunCeil, PAImg) is given explicitly. The end of the file prints the instance theorem's application and statement
   under Set Printing All (every sink-head argument is PcapSinkHeads.asan_sink_head). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntryTop PcapEntryFinal PcapHarnessWalk
  PcapFuzzFopenG PcapFuzzFopen PcapSourceNextSpec PcapInstLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PSourceMeter PFreadISpec PFclose PFmemopenISpec
  PFcloseInst WFcloseI.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCbp PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase PcapRelro PcapRelroA PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require AB1v AD2l AF0s StackMalloc0 AE3i AD1o AE2q PcapBFacts
  PcapGHarness AE2r AE39 AE2j AD1u AE2s PcapHPath PcapRoBridges.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Memmove StrcmpPath.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceClose
  PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
Import ListNotations.
Open Scope Z_scope.

(* `fitc L` is PcapEntryFinal's `fit` (arguments logged by args_fit), except that a conclusion that is the goal only
   up to conversion is accepted and logged as a `CONCL_FIT CONVERSION` line with both types. Used only at the ruled
   conversions the header lists. *)
Ltac fitc L :=
  PcapEntryFinal.args_fit L;
  lazymatch goal with |- ?G =>
    let T := type of L in
    tryif constr_eq T G then idtac
    else idtac "CONCL_FIT CONVERSION: the term" L "has the type" T "where the goal is" G;
    exact L
  end.

Section inst.
Context {rc : YM05.RunCeil}.
(* The ASan image's sink head, by name (lib/Reusable/PcapSinkHeads.v:37: sk_ofl_head = 0x5f4f88, checked against the
   code by lib/A/PcapSinkHeadCheck.v); a Theorem Labs lane 11:32Z, as cgif's released instance (lib/A/ACee.v:56). *)
Local Notation SK := PcapSinkHeads.asan_sink_head.
Local Notation B := AD2l.PcapB.
Local Notation MT := YCbp.ameter_triv.
Local Notation SEGS := Asan.M.loaded_segments.
Local Notation PIp := (@PcapEntryTop.PI_pcap rc).
Local Notation GIx X fx := (X fx rc PIp B MT pcap_KS).
Local Notation SEGSp := (@pa_segs rc pcap_listing PIp).
Local Notation VALp a := (@pa_val rc pcap_listing PIp a).
Local Notation LOp := (@pa_relro_lo rc pcap_listing PIp).
Local Notation HIp := (@pa_relro_hi rc pcap_listing PIp).

(* ---- pcap_entry_final's premises that no lemma on the base discharges: name and type unchanged at
   SK := asan_sink_head, B := PcapB, MT := ameter_triv; OWNER as a Theorem Labs lane's map (11:33Z). ---- *)
(* OWNER: a Theorem Labs lane (lib/A/Stdio/PStdioImgA.v:46 FM_MALLOC_RA is the value pcap_afmemopen_closed states) *)
Variable FM_RA : Z.
(* OWNER: a Theorem Labs lane *)
Variable CTX : list (list Z).
(* ROI := a Theorem Labs lane's AE3i.ro_img (lib/A/AE3i.v:76), the value a Theorem Labs lane's DISCHARGER names; HROI, ROIMG_KEPT,
   ROIMG_LOW and STRCMP are proved at it below (inst_HROI, inst_ROIMG_KEPT, inst_ROIMG_LOW, inst_STRCMP). *)
Local Notation ROI := AE3i.ro_img.
(* TL, TLF: discharged in the instance application by a Theorem Labs lane's PcapInstLib.PcapB_PALib / PcapB_PALibF
   (lib/A/Prog/PcapInstLib.v:37, :52). RO: discharged below (inst_RO). HPATH: discharged below (inst_HPATH). *)
(* OWNER: a Theorem Labs lane *)
Hypothesis HCTX : In [VALp A_TEXT + PP_K7; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K7] CTX.
(* OWNER: a Theorem Labs lane *)
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).
(* FFL: discharged in the instance application by a Theorem Labs lane's PcapInstLib.PcapB_FFL (lib/A/Prog/PcapInstLib.v:62). *)
(* ro_chunk_addr := a Theorem Labs lane's PcapGHarness.ro_chunk_addr (lib/A/PcapGHarness.v:127, the bytes of AE3i's img_ro_chunks);
   HGRO and ROIMG_KEPT are proved at it below (inst_HGRO, inst_ROIMG_KEPT). *)
Local Notation ro_chunk_addr := PcapGHarness.ro_chunk_addr.
(* FM: discharged in the instance application by a Theorem Labs lane's PFcloseInst.inst_FM (lib/A/Stdio/PFcloseInst.v:109). *)
(* OWNER: a Theorem Labs lane. PROVED, NOT WIRED: PFreadC.pcap_afread_closed (a working branch 9d450c6144e,
   lib/A/Stdio/PFreadC.v:32; in this tree at lib/A/Stdio/PFreadC.v:33); wired after a Theorem Labs lane's musl-file split lands (a Theorem Labs lane, 11:21Z). *)
Hypothesis AFREAD : forall fx : YK11.FPState,
  @PFreadISpec.afread_spec fx rc SK SEGSp B pcap_KS (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fread).
(* ra_fc1 / ra_fc2 := WFcloseI.WFI_FREE1 / WFcloseI.WFI_JOIN (lib/A/Stdio/WFcloseI.v:87-88; 0x8e2b8 / 0x8e2c0, the
   return pcs of musl fclose's two free calls, the rows of ACej.TRACES_fclose, lib/A/ACej.v:73-75), the values
   PFcloseInst.inst_AFCLOSE, inst_HUfc1 and inst_HUfc2 state. *)
Local Notation ra_fc1 := WFcloseI.WFI_FREE1.
Local Notation ra_fc2 := WFcloseI.WFI_JOIN.
(* AFCLOSE, HUfc1, HUfc2: discharged in the instance application by a Theorem Labs lane's PFcloseInst.inst_AFCLOSE,
   inst_HUfc1 and inst_HUfc2 (lib/A/Stdio/PFcloseInst.v:130, :148, :153). *)
(* ASM0 and AMM: discharged below (inst_ASM0, inst_AMM). ROIMG_LOW: discharged below (inst_ROIMG_LOW). *)
(* mc_lo / mc_hi := AE39.MC_LO / AE39.MC_HI (lib/A/AE39.v:27-28; 0x10350 / 0x10370 by AE39.v:31 mc_bounds), the
   window of __strchrnul's constants that AE39.mconsts_view names; MCONSTS is proved at it below (inst_MCONSTS).
   a Theorem Labs lane's pcap_afmemopen_closed states the same window (0x10350 / 0x10370, PFmemopenC.v:23 on a working branch). *)
Local Notation mc_lo := AE39.MC_LO.
Local Notation mc_hi := AE39.MC_HI.
(* MCONSTS, FI: discharged below (inst_MCONSTS, inst_FI). STRCMP: discharged below (inst_STRCMP). *)
(* OWNER: a Theorem Labs lane. PROVED, NOT WIRED: PFmemopenC.pcap_afmemopen_closed (a working branch
   c5180b0bcf1, lib/A/Stdio/PFmemopenC.v:23, at FM_ENTRY, FM_MALLOC_RA, 0x10350, 0x10370; in this tree at the same line). *)
Hypothesis AFMEMOPEN : forall fx : YK11.FPState,
  @PFmemopenISpec.afmemopen_spec fx rc SK SEGSp B pcap_KS MT CTX
    (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fmemopen) FM_RA mc_lo mc_hi.
(* HSET: discharged below (inst_HSET). ABCMP: discharged below (inst_ABCMP). *)
(* OWNER: a Theorem Labs lane *)
Hypothesis HCTX_A : In [VALp A_TEXT + PP_K2; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K2] CTX.

(* ---- The discharges. ---- *)
Lemma inst_HXMN : forall n : Z, (fun _ : Z => 0) n <= (fun _ : Z => 0) n.
Proof. intros n. cbv beta. lia. Qed.

(* PcapB's code table is AF0m.Tfib_code (AD2l.v:19): its malloc / free return addresses, by computation. *)
Lemma inst_HMRA : pc_malloc_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z).
Proof. reflexivity. Qed.
Lemma inst_HFRA : pc_free_ra0 (as_code B) = (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z).
Proof. reflexivity. Qed.

Set Printing All.
Lemma inst_LAWS : @AR_laws rc SEGSp B.
Proof.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141) *)
  fitc (@PcapBFacts.PcapB_LAWS rc).
Qed.

Lemma inst_AM : forall fx : YK11.FPState, @amalloc04_rule fx rc SK SEGSp B MT.
Proof.
  intros fx.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141) *)
  fitc (@PcapBFacts.PcapB_AMALLOC4 fx rc SK).
Qed.

Lemma inst_AF : forall fx : YK11.FPState, @afree04_rule fx rc SK SEGSp B MT.
Proof.
  intros fx.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141) *)
  fitc (@PcapBFacts.PcapB_AFREE4 fx rc SK).
Qed.

Lemma inst_ASM1 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc SEGSp B 1.
Proof.
  intros fx.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141) *)
  fitc (@AF0s.stack_malloc1_contract fx rc B (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms).
Qed.

Lemma inst_gx_ok : gx_ok SEGS B G_HARNESS.
Proof.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13) *)
  fitc (PcapGHarness.pcap_G_harness_gx_ok B AD2l.PcapB_syms).
Qed.

Lemma inst_pe_bytes : forall a, inG G_HARNESS a ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ (as_meta_mem pcap_KS <= a < as_meta_mem pcap_KS + 8) /\
  ~ (as_errno B <= a < as_errno B + 4).
Proof.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13) *)
  fitc (PcapGHarness.pcap_G_harness_pe_bytes B AD2l.PcapB_syms).
Qed.

Lemma inst_ASM0 : forall fx : YK11.FPState, @astack_malloc_realizes fx rc SEGSp B PcapSourceNextSpec.NX_CID.
Proof.
  intros fx.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141), and NX_CID := 0 (PcapSourceNextSpec.v:47) *)
  fitc (@StackMalloc0.stack_malloc0_contract fx rc B (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms).
Qed.

Lemma inst_AMM : forall fx : YK11.FPState,
  @MemmoveDef.amemmove_realizes fx rc SEGSp B (@pa_sigma rc pcap_listing PIp PS___asan_memmove).
Proof.
  intros fx.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141), and pa_sigma PI_pcap PS___asan_memmove = 0x51bf0 (PcapAddr.v:41) *)
  fitc (@Memmove.asan_memmove_contract fx rc B (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms).
Qed.

Lemma inst_HGRO : forall a, ro_chunk_addr a ->
  in_roP SEGSp LOp HIp a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments and
     pa_relro_lo / pa_relro_hi PI_pcap = PCAP_RLO / PCAP_RHI (PcapEntryTop.v:140-141, :154-155) *)
  fitc (PcapGHarness.pcap_hg_ro B AD2l.PcapB_syms).
Qed.

Lemma inst_HROI : forall (W : world SEGSp) mem,
  arodata_okP SEGSp LOp HIp B (aview SEGSp (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Proof.
  intros W mem HRO.
  (* conversion: arodata_okP (pa_segs PI_pcap) (pa_relro_lo PI_pcap) (pa_relro_hi PI_pcap) PcapB at aview (pa_segs
     PI_pcap) = ACeg's arodata_ok PcapB at aview tfibsegs: pa_segs / pa_relro_lo / pa_relro_hi PI_pcap
     (PcapEntryTop.v:140-141, :154-155), tfibsegs (AB1v.v:13), in_roP = in_ro_tfa (PcapBase.v:17-22, ACeg.v:60-65) *)
  fitc (AD1o.ro_img_of_arodata B (w_H W) mem AD2l.PcapB_syms HRO).
Qed.

Lemma inst_HCPY : forall fx : YK11.FPState,
  @aintrin_realizes fx rc SEGSp B OCpy (@pa_sigma rc pcap_listing PIp PS___asan_memcpy).
Proof.
  intros fx.
  (* conversion: aintrin_realizes OCpy (YG0d.v:318-336, its match on OCpy) at tfibsegs = Asan.M.loaded_segments
     (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments (PcapEntryTop.v:140-141) and pa_sigma PI_pcap
     PS___asan_memcpy = 0x51514 (PcapAddr.v:19): the lemma states the unfolded body at 0x51514 *)
  fitc (@AE2q.asan_memcpy_realizes fx rc B (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms).
Qed.

(* HSET, a bridge (premise order only). aintrin_realizes OSet (YG0d.v:318-336) takes amem_range d n right after
   dest_ok (:322) and, for OSet, a premise that is `True` (:324-327); AE2r.asan_memset_realizes (AE2r.v:568), about
   __asan_memset at 0x519b0, takes amem_range d n last and has no `True` premise. Each premise is introduced in
   aintrin_realizes's order, the `True` one is dropped, and the lemma gets amem_range d n in its own last place. *)
Lemma inst_HSET : forall fx : YK11.FPState,
  @aintrin_realizes fx rc SEGSp B OSet (@pa_sigma rc pcap_listing PIp PS___asan_memset).
Proof.
  intros fx ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
  (* conversion: aintrin_realizes OSet's post (YG0d.v:328-336, its match on OSet) and premises at tfibsegs =
     Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments (PcapEntryTop.v:140-141) and
     pa_sigma PI_pcap PS___asan_memset = 0x519b0 (PcapAddr.v:20) *)
  fitc (AE2r.asan_memset_realizes B (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms
          ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.

(* AD1u's class premise at the instance's sink head: sk_ofl_head asan_sink_head = 0x5f4f88 (PcapSinkHeads.v:37,
   AD1u.v:54), by computation on the closed term, as lib/A/PcapDriver.v:47 pcap_drv_head (which is #[local]). *)
Lemma inst_pcap_head : @AD1u.pcap_head SK.
Proof. exact eq_refl. Qed.

Lemma inst_ASIL : asource_img_laws SK SEGS B pcap_KS.
Proof.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13) *)
  fitc (AD1u.tfib_ASIL (SK := PcapSinkHeads.asan_sink_head) (PH := inst_pcap_head) B AD2l.PcapB_syms).
Qed.

(* RO at the A image (the form of lib/B's pcap_ro_below, a working branch 08efd9be8f0
   lib/B/Prog/PcapEntryTop.v:285): every read-only segment of Asan.M.loaded_segments ends at or below 0x5f4f88
   (vm_compute), and the RELRO window PCAP_RLO .. PCAP_RHI = 0x992d0 .. 0x9a528 (PcapRelro.v:23-24) lies below it. *)
Lemma inst_RO : @ro_below_ofl SEGSp LOp HIp SK.
Proof.
  intros a Hro.
  (* conversion: pa_segs / pa_relro_lo / pa_relro_hi PI_pcap = Asan.M.loaded_segments / PCAP_RLO / PCAP_RHI
     (PcapEntryTop.v:140-141, :154-155), sk_ofl_head asan_sink_head = 0x5f4f88 (PcapSinkHeads.v:37) *)
  change (in_roP SEGS PCAP_RLO PCAP_RHI a) in Hro. change (a < (symaddr Symbols.Asan.s_ofl_head)).
  assert (HC : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? (symaddr Symbols.Asan.s_ofl_head)))
                 SEGS = true)
    by (clear; vm_compute; reflexivity).
  destruct Hro as [(s & Hs & Hw & Hr) | Hrel].
  - rewrite forallb_forall in HC. specialize (HC s Hs). rewrite Hw in HC. cbn [orb] in HC.
    apply Z.leb_le in HC. lia.
  - unfold PCAP_RLO, PCAP_RHI in Hrel. lia.
Qed.

(* FI at SK := asan_sink_head: fi_sep is PcapFuzzFopen.fopen_img_tables's third conjunct (PcapFuzzFopen.v:496,
   g_file_len 0x5d3f40 + 8 <= g_file 0x5d3f60); fi_head is as_ofl_head pcap_KS = 0x5f4f88 = AOFL_HEAD at
   asan_sink_head (YCbq.v:84), and fi_kimg bounds pcap_KS's six stdio cells below pcap_img_end, both by computation. *)
Lemma inst_FI : PcapFuzzFopenG.FopenImg SK (VALp (A_OBJ PcapFuzzFopen.FO_LEN)) (VALp (A_OBJ PcapFuzzFopen.FO_FILE))
  pcap_KS.
Proof.
  constructor.
  - (* conversion: pa_val PI_pcap = PcapEntryTop.pcap_val (PcapEntryTop.v:67, :144), which is pcap_obj on the
       objects FO_LEN / FO_FILE *)
    fitc (proj2 (proj2 PcapFuzzFopen.fopen_img_tables)).
  - reflexivity.
  - assert (C : forallb (fun a => (0 <=? a) && (a + 16 <=? pcap_img_end))
                  [as_threaded pcap_KS; as_need_locks pcap_KS; as_ofl_lock pcap_KS; as_mode pcap_KS;
                   as_rwa pcap_KS; as_canary pcap_KS] = true)
      by (vm_compute; reflexivity).
    apply Forall_forall. intros a Ha.
    pose proof (proj1 (forallb_forall _ _) C a Ha) as Hb. cbv beta in Hb.
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.

(* MCONSTS, a bridge: at mc_lo / mc_hi := AE39.MC_LO / AE39.MC_HI it is the second conjunct of
   AE2j.strchr_lit_ro_of_img W mem (AE2j.v:99), mconsts_view W mem (AE39.v:29-30), from ro_img. *)
Lemma inst_MCONSTS : forall (W : world SEGSp) (mem : word -> option byte), ROI (mrestrict (w_H W) mem) ->
  forall a, mc_lo <= a < mc_hi ->
  aview SEGSp (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGSp (Z_to_bv 64 a)).
Proof.
  intros W mem HRO.
  (* conversion: mconsts_view W mem (AE39.v:29-30) at tfibsegs = Asan.M.loaded_segments (AB1v.v:13) and pa_segs
     PI_pcap = Asan.M.loaded_segments (PcapEntryTop.v:140-141); W and HRO at tfibsegs likewise *)
  PcapEntryFinal.args_fit (AE2j.strchr_lit_ro_of_img W mem HRO).
  fitc (proj2 (AE2j.strchr_lit_ro_of_img W mem HRO)).
Qed.

(* ABCMP: a Theorem Labs lane's core AE2s.bcmp_icpt_contract (AE2s.v:712), the contract of __interceptor_trampoline_bcmp at 0x41570
   (AE2s.MC_ENTRY, AE2s.v:31), at PcapB with PcapB_LAWS and AD2l.PcapB_syms. *)
Lemma inst_ABCMP : forall fx : YK11.FPState,
  @abcmp_realizes fx rc SEGSp B (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_bcmp).
Proof.
  intros fx.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141), and pa_sigma PI_pcap PS___interceptor_trampoline_bcmp = pcap_sigma .. = 0x41570
     (PcapEntryTop.v:145, PcapAddr.v:24) *)
  fitc (@AE2s.bcmp_icpt_contract fx rc AD2l.PcapB (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms).
Qed.

(* HPATH: the core's PcapHPath.pcap_path_addressable (PcapHPath.v:38), general in segs: under AR the 13 bytes of the
   listing's object 3 (0x20d00, "<fuzz-input>" and its NUL) are range_addressable and their shadow hull is visible;
   at PcapB with AD2l.PcapB_syms and segs := pa_segs PI_pcap. *)
Lemma inst_HPATH : forall ly S (W : world SEGSp) mem md, @AR rc SEGSp B ly S W mem md ->
  range_addressable (aview SEGSp (w_H W) mem) SHADOW_OFF (VALp (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGSp (w_H W) mem) (VALp (A_OBJ 3)) 13.
Proof.
  (* conversion: pa_val PI_pcap = pcap_val (PcapEntryTop.v:144) and pcap_val (A_OBJ 3) = pcap_obj 3 = 0x20d00
     (PcapEntryTop.v:67-68, PcapAddr.v:49) *)
  fitc (@PcapHPath.pcap_path_addressable rc AD2l.PcapB AD2l.PcapB_syms SEGSp).
Qed.

(* ROIMG_KEPT: the core's PcapRoBridges.pcap_roimg_kept (PcapRoBridges.v:38), stated at tfibsegs. *)
Lemma inst_ROIMG_KEPT : forall m m' : word -> option byte,
  (forall a, ro_chunk_addr a -> mbyte SEGSp m' a = mbyte SEGSp m a) -> ROI m -> ROI m'.
Proof.
  (* conversion: tfibsegs = Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments
     (PcapEntryTop.v:140-141) *)
  fitc (@PcapRoBridges.pcap_roimg_kept).
Qed.

(* ROIMG_LOW: the core's PcapRoBridges.pcap_roimg_low (PcapRoBridges.v:48), roimg_low tfibsegs ro_img unfolded. *)
Lemma inst_ROIMG_LOW : @PcapFuzzFopenG.roimg_low rc SEGSp ROI.
Proof.
  (* conversion: PcapFuzzFopenG.roimg_low (PcapFuzzFopenG.v:44-46), a named Definition, unfolded; tfibsegs =
     Asan.M.loaded_segments (AB1v.v:13), pa_segs PI_pcap = Asan.M.loaded_segments (PcapEntryTop.v:140-141) *)
  fitc (@PcapRoBridges.pcap_roimg_low rc).
Qed.

(* STRCMP: a Theorem Labs lane's StrcmpPath.astrcmp_path_at_of_syms (Rt/StrcmpPath.v:58, from StrcmpIcpt.strcmp_lit_contract),
   at B := PcapB, segs := pa_segs PI_pcap, ROI := AE3i.ro_img, pc := the strcmp trampoline, x := object FO_PATH, with
   PcapB_LAWS, AD2l.PcapB_syms, the ROI premise fun m H => H (ROI is ro_img) and its three equations by eq_refl. *)
Lemma inst_STRCMP : forall fx : YK11.FPState,
  @PcapFuzzFopenG.astrcmp_path_at fx rc SEGSp B ROI (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_strcmp)
    (VALp (A_OBJ PcapFuzzFopen.FO_PATH)).
Proof.
  intros fx.
  (* conversion: at the three equations (arguments): pa_segs PI_pcap = Asan.M.loaded_segments (PcapEntryTop.v:140-141)
     = tfibsegs (AB1v.v:13); pa_sigma PI_pcap PS___interceptor_trampoline_strcmp = pcap_sigma .. = 0x41564 =
     StrcmpDef.SM_ENTRY (PcapEntryTop.v:145, PcapAddr.v:14, StrcmpDef.v:35); pa_val PI_pcap (A_OBJ FO_PATH) = pcap_val
     (A_OBJ 3) = pcap_obj 3 = 0x20d00 = StrcmpDef.A_FUZZ_PATH (PcapEntryTop.v:67-68, :144, PcapFuzzFopen.FO_PATH := 3,
     PcapAddr.v:49, StrcmpDef.v:36) *)
  fitc (@StrcmpPath.astrcmp_path_at_of_syms fx rc AD2l.PcapB SEGSp ROI
          (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_strcmp) (VALp (A_OBJ PcapFuzzFopen.FO_PATH))
          (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms
          (@eq_refl (list Segment) SEGSp)
          (fun m H => H)
          (@eq_refl Z (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_strcmp))
          (@eq_refl Z (VALp (A_OBJ PcapFuzzFopen.FO_PATH)))).
Qed.

(* ===================== the instance ===================== *)

Theorem pcap_entry_inst : @tfib_lib_contract_x_all_A rc SK B MT (fun _ : Z => 0) (fun _ : Z => 0) pcap_KS.
Proof.
  PcapEntryFinal.fit (@PcapEntryFinal.pcap_entry_final rc SK B MT (fun _ : Z => 0) (fun _ : Z => 0)
    YCbp.ameter_triv_laws PcapEntryDefs.pe_need_triv_budget inst_HXMN inst_gx_ok inst_pe_bytes
    inst_HMRA inst_HFRA AD2l.PcapB_universe inst_ASIL FM_RA CTX ROI inst_LAWS (@PcapInstLib.PcapB_PALib rc)
    (@PcapInstLib.PcapB_PALibF rc) inst_ASM1 inst_AM inst_AF inst_RO inst_HROI inst_HPATH HCTX HFMU PcapBFacts.PcapB_ML
    (@PcapInstLib.PcapB_FFL rc) YCbp.ameter_triv_fs_laws ro_chunk_addr inst_ROIMG_KEPT inst_HGRO
    (@PFcloseInst.inst_FM rc) AFREAD ra_fc1 ra_fc2 (@PFcloseInst.inst_AFCLOSE rc) (@PFcloseInst.inst_HUfc1)
    (@PFcloseInst.inst_HUfc2) inst_ASM0 inst_AMM inst_ROIMG_LOW mc_lo mc_hi inst_MCONSTS inst_FI inst_STRCMP AFMEMOPEN
    inst_HCPY inst_HSET HCTX_A inst_ABCMP).
Qed.
Unset Printing All.

Print Assumptions pcap_entry_inst.

(* Sink-head audit: the instance application and the discharges that take a sink head, printed in full, and the proof
   terms of a Theorem Labs lane's two (PFcloseInst.inst_FM, inst_AFCLOSE); every sink-head argument is
   PcapSinkHeads.asan_sink_head, by name. *)
Set Printing All.
Check (fun fx : YK11.FPState => @PcapBFacts.PcapB_AMALLOC4 fx rc SK).
Check (fun fx : YK11.FPState => @PcapBFacts.PcapB_AFREE4 fx rc SK).
Check inst_pcap_head.
Check inst_ASIL.
Check inst_RO.
Check inst_FI.
Check (@PFcloseInst.inst_FM rc).
Check (@PFcloseInst.inst_AFCLOSE rc).
Print PFcloseInst.inst_FM.
Print PFcloseInst.inst_AFCLOSE.
Check (@PcapEntryFinal.pcap_entry_final rc SK B MT (fun _ : Z => 0) (fun _ : Z => 0)
    YCbp.ameter_triv_laws PcapEntryDefs.pe_need_triv_budget inst_HXMN inst_gx_ok inst_pe_bytes
    inst_HMRA inst_HFRA AD2l.PcapB_universe inst_ASIL FM_RA CTX ROI inst_LAWS (@PcapInstLib.PcapB_PALib rc)
    (@PcapInstLib.PcapB_PALibF rc) inst_ASM1 inst_AM inst_AF inst_RO inst_HROI inst_HPATH HCTX HFMU PcapBFacts.PcapB_ML
    (@PcapInstLib.PcapB_FFL rc) YCbp.ameter_triv_fs_laws ro_chunk_addr inst_ROIMG_KEPT inst_HGRO
    (@PFcloseInst.inst_FM rc) AFREAD ra_fc1 ra_fc2 (@PFcloseInst.inst_AFCLOSE rc) (@PFcloseInst.inst_HUfc1)
    (@PFcloseInst.inst_HUfc2) inst_ASM0 inst_AMM inst_ROIMG_LOW mc_lo mc_hi inst_MCONSTS inst_FI inst_STRCMP AFMEMOPEN
    inst_HCPY inst_HSET HCTX_A inst_ABCMP).
Unset Printing All.

End inst.

Print Assumptions pcap_entry_inst.
Set Printing All.
Check @pcap_entry_inst.
Unset Printing All.

(* The plain build's sink head (Reusable/YI5b.v src0_sink_head) is loaded with PcapSinkHeads.v (its Require of YI5b,
   PcapSinkHeads.v:14), which removes it from the typeclass hints (PcapSinkHeads.v:33); no statement used or proved
   here names it: the Checks above show asan_sink_head at every sink-head position. *)
Locate src0_sink_head.
Locate sink_head.
Print Instances OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head.
