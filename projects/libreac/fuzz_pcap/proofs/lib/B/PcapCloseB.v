From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v, YD2p.v and YD1q.v
   (asan-ubsan), ossv/recipes c8557374ad2e, for fuzz_pcap: the closing of PcapAsanTop.ASAN_UBSAN_T from named parts;
   module paths changed, shape AgreePcap.ag_out_shape (PcapAsanTop.pcap_shape), fuzz_pcap's asan-ubsan image. Split
   out of lib/A/PcapClose.v (its asan-ubsan half, every name kept), as the donor keeps its asan-ubsan closers
   lib/YD2o.v / YD1q.v apart from the asan ones lib/A/AD2o.v / AD1q.v. *)
(* The closing side of fuzz_pcap's two asan-ubsan statements (rule 24: no function proved; this file is assembly).

   The asan twin is lib/A/PcapClose.v; its header gives the donor steps (YD2o.v applies YD1q.v tfib_srealizesX, which
   joins the start-up, the hand-off, the driver main and the spec link) and the open core item that H_DRIVER_U shares
   with H_DRIVER. Every input is bound to the image's named object or proved by a named lemma below, with the donor
   statement it stands for and the lane that supplies it: the same 13 rows as the asan file, with _U. No Section
   hypothesis is left (the last, HOPEN, is lib/B/PcapOpenInstB.v inst_HOPEN).

   Row 11_U is stated over lib/B's MEASURED instance lib/B/Prog/PcapEntry.v tfib_lib_contract_x_all_B (the generic
   contract at AsanUbsan.M.loaded_segments, lib/B/Prog/PcapRelro.v PCAP_RLO / PCAP_RHI = 0x99198 / 0x9a3f0,
   A_LLVMF 0x80818, RA_LLVMF 0x80684, A_EMPTY 0x5d3e20, LLVMF_STK 32768, G_HARNESS_U = [(0x5d3e40, 8); (0x5d3e60, 8)]),
   so no entry datum of the image is a free variable here. KS_U is lib/B/Stdio/PSourceK.v pcap_KS (its ofl_head
   0x5f4e88), SK_U is lib/Reusable/PcapSinkHeads.v asan_ubsan_sink_head (the same ofl_head, HSK_U), B_U is
   lib/Reusable/YD2l.v PcapB and the start-up tables are lib/Reusable/YB01.v HS_tfib / YB12.v TFIB.

   Row 11_U is DERIVED here (a Theorem Labs lane 07:12Z, gate 8), not assumed: H_PROG_LIBCONTRACT_U_of is lib/B/Prog/PcapEntryTop.v
   pcap_entry_top at MT := ameter_triv, SK := SK_U, B := B_U, KS := pcap_KS. Its allocator rules AMALLOC4 / AFREE4 come
   from rows 8 / 9 through lib/Reusable/YCbp.v amalloc04_rule_triv / afree04_rule_triv; its other premises are the
   lemmas of the block "ROW 11_U, DERIVED" below, with pcap_entry_top's names and types. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap Require Statements.
From OSSVerify.libreac.fuzz_pcap.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01 YG0f YG0d YC5d YCbp YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCejTfib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require
  PcapEntryTop PcapEntryDefs PcapPa PcapPaLib PcapFrame PcapList PcapSyms PcapEntryCalls PcapEntryEntry
  PcapSourceNext PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFclose PSourceMeta PSourceMeter PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCbq YG0n YA0n YK04 YG0v YCej YE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require
  YD2l YB01 YB12 YB1n PcapSinkHeads YF0w YF0q YD2m YG0q YG05 YG0t YF0s YD1u YCejSites.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require StackMalloc0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Rt Require Memmove.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapSourceOpen PcapAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YE2s YE2q YE2r.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PFreadI PFreadC.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YD2o.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require PFcloseInstB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require PcapBFacts.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B Require PcapOpenInstB.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import PcapAsanTop.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Local Unset Lia Cache. Local Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Local Open Scope Z_scope.

(* lib/B's program contract instance. lib/A/Prog/PcapEntry.v (the generic text) is loaded under the same short name,
   so lib/B's file is named by its full path. *)
Module PEB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntry.
(* The modules pcap_entry_top's premises name, by their full paths (lib/A and lib/U load modules of the same short
   names in this closure). *)
Module PET := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryTop.
Module PED := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryDefs.
Module PPA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPa.
Module PPL := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapPaLib.
Module PFR := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapFrame.
Module PLS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapList.
Module PSY := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSyms.
Module PEC := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryCalls.
Module PEE := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapEntryEntry.
Module PAT := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PaTable.
Module PBA := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapBase.
Module WJG := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.W_journalG.
Module PFC := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PFclose.
Module PSM := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PSourceMeta.
Module PSR := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PSourceMeter.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCbq.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0n.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YA0n.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YK04.
Module RG0v := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0v.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceNext.
Module PSND := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceNextDefs.
Module PFRD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PFreadISpec.
Module PMMV := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt.MemmoveDef.
Module RCej := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCej.
Module RE3i := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE3i.
Module RD2l := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2l.
Module RB01 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YB01.
Module RB12 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YB12.
Module RB1n := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YB1n.
Module RPSH := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.
Module RF0w := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YF0w.
Module RF0q := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YF0q.
Module RD2m := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2m.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0q.
Module RG05 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG05.
Module RG0t := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YG0t.
Module RF0s := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YF0s.
Module RD1u := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD1u.
Module RCejS := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YCejSites.
Module BSM0 := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.StackMalloc0.
Module BMMV := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Rt.Memmove.
Module PSO := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceOpen.
Module PADR := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapAddr.
Module RE2s := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE2s.
Module RE2q := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE2q.
Module RE2r := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YE2r.
Module BFRI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFreadI.
Module BFRC := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFreadC.
Module RD2o := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YD2o.
Module BFCI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PFcloseInstB.
Module BBF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapBFacts.
Module POIB := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.PcapOpenInstB.
(* PcapEntryTop.v's Section top abbreviations (PIp, PSEGS, VALp, RLOp, RHIp; pa_sigma), at a given rc. *)
Local Notation PIp rc := (@PET.PI_pcap rc).
Local Notation PSEGS rc := (@PPA.pa_segs rc PLS.pcap_listing (PIp rc)).
Local Notation VALp rc a := (@PPA.pa_val rc PLS.pcap_listing (PIp rc) a).
Local Notation SIGp rc s := (@PPA.pa_sigma rc PLS.pcap_listing (PIp rc) s).
Local Notation RLOp rc := (@PPA.pa_relro_lo rc PLS.pcap_listing (PIp rc)).
Local Notation RHIp rc := (@PPA.pa_relro_hi rc PLS.pcap_listing (PIp rc)).

Local Notation LS := PcapAsanTop.pcap_shape.

(* pcap_source_next's stack bound, inside pcap_entry_top's HNSTK range: NX_STK_B = 272 + AFREAD_STK = 8464
   (lib/B/Prog/PcapSourceNextDefs.v:132: its frame `addi sp,sp,-0x100` at 0x815b8 plus 16 of realignment, and the
   fread wrapper's AFREAD_STK 8192, lib/A/Stdio/PFreadISpec.v:77). *)
Lemma NX_STK_B_range : 0 <= PSND.NX_STK_B <= 32368.
Proof. unfold PSND.NX_STK_B, PFRD.AFREAD_STK. lia. Qed.

(* ---- pcap_entry_top's call-site values, fixed by the program; each measured on pin 9e66f771 (capstone 5.0.7) ---- *)
(* ra_fc1 / ra_fc2: the return addresses of musl fclose's two frees (fclose 0x8e0e0: `jal 0x52c24`
   __interceptor_trampoline_free at 0x8e180 (+0xa0) and at 0x8e188 (+0xa8)), the ra of the free traces AFCLOSE's
   premises and HUfc1 / HUfc2 name. The same pair is lib/B/Prog/PcapEntryDefs.v:382 PE_FCLOSE_FREE_RAS and
   lib/Reusable/YCej.v TRACES_fclose. *)
Definition RA_FC1_U : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0xa4)%Z).
Definition RA_FC2_U : Z := (symaddr (Symbols.AsanUbsan.s_fclose + 0xac)%Z).
Lemma RA_FC_U_pe : [RA_FC1_U; RA_FC2_U] = PED.PE_FCLOSE_FREE_RAS.
Proof. reflexivity. Qed.
(* FM_RA_K2 / FM_RA: the return address of musl fmemopen's malloc (fmemopen 0x8e73c: `jal 0x52c28`
   __interceptor_trampoline_malloc at 0x8e7d4 (+0x98); the +0xa8 call, buffer NULL, is never made by the harness),
   the ra after pc_malloc_ra0 in the open contract's trace premise at both call sites (one callee, so one value).
   The same address is lib/B/Prog/PcapEntryDefs.v:381 PE_FMEMOPEN_MALLOC_RA and lib/Reusable/YCej.v TRACES_fmemopen. *)
Definition FM_RA_U : Z := (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z).
Lemma FM_RA_U_pe : FM_RA_U = PED.PE_FMEMOPEN_MALLOC_RA.
Proof. reflexivity. Qed.
(* CTX_K2 / CTX: the call contexts of pcap_source_open, lib/Reusable/YCej.v:40 CTX_pcap_source_open =
   [[0x80a10]; [0x80a10; 0x80684]; [0x80e50]; [0x80e50; 0x80684]]: the return addresses of LLVMFuzzerTestOneInput's two
   `jal 0x811e0` pcap_source_open (at 0x80a0c, PP_K2, and 0x80e4c, PP_K7), with and without the return into
   target_run (`jal 0x80818` at 0x80680). The open contract's pre takes the caller's chain from this list; both call
   sites use the one table, as the donor's ACeb.v:38-39 does. *)
Definition CTX_U : list (list Z) := RCej.CTX_pcap_source_open.
Lemma CTX_U_K2 (rc : YM05.RunCeil) :
  In [VALp rc PAT.A_TEXT + PED.PP_K2; PEB.RA_LLVMF] CTX_U /\ In [VALp rc PAT.A_TEXT + PED.PP_K2] CTX_U.
Proof. rewrite (@PET.pi_pcap_text rc). split; vm_compute; auto. Qed.
Lemma CTX_U_K7 (rc : YM05.RunCeil) :
  In [VALp rc PAT.A_TEXT + PED.PP_K7; PEB.RA_LLVMF] CTX_U /\ In [VALp rc PAT.A_TEXT + PED.PP_K7] CTX_U.
Proof. rewrite (@PET.pi_pcap_text rc). split; vm_compute; auto. Qed.
(* ROI_K2 / ROI: the read-only image predicate, a Theorem Labs lane's asan-ubsan ro_img (lib/Reusable/YE3i.v:62): the image bytes
   of [0x10000, 0x2ee90) outside the generated owned statics (YE3i.v:58 img_ro_complement_ok, checked by
   computation; the RO PT_LOAD of the pin ends at 0x2efc0, YE3i.v:24). It is the predicate lib/B/Prog/PcapFuzzFopen.v:72
   names as this image's roimg. *)
Definition ROI_U : (word -> option byte) -> Prop := RE3i.ro_img.

(* The B listing's callee pcs (lib/B/Prog/PcapAddr.v:21, :22, :27, :37; PI_pcap's pa_sigma is pcap_sigma,
   lib/B/Prog/PcapEntryTop.v:149), by computation, are the pcs of the proved contracts used below: Reusable/YE2q.v:145
   asan_memcpy_realizes (0x51564), Reusable/YE2r.v:569 asan_memset_realizes (0x51a00), Reusable/YE2s.v:712
   bcmp_icpt_contract (0x415c0) and lib/B/Stdio/PFreadI.v:132 FR_ENTRY_U (0x415d0). *)
Lemma memcpy_pc_U : PADR.pcap_sigma PSY.PS___asan_memcpy = (symaddr Symbols.AsanUbsan.s___asan_memcpy).
Proof. vm_compute. reflexivity. Qed.
Lemma memset_pc_U : PADR.pcap_sigma PSY.PS___asan_memset = (symaddr Symbols.AsanUbsan.s___asan_memset).
Proof. vm_compute. reflexivity. Qed.
Lemma bcmp_pc_U : PADR.pcap_sigma PSY.PS___interceptor_trampoline_bcmp = (symaddr Symbols.AsanUbsan.s___wrap_bcmp).
Proof. vm_compute. reflexivity. Qed.
Lemma fread_pc_U : PADR.pcap_sigma PSY.PS___interceptor_trampoline_fread = BFRI.FR_ENTRY_U.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================================================== *)
(* ASan+UBSan image (donor lib/YD2o.v, YD2p.v, YD1q.v; the asan-ubsan core is a working branch)         *)
(* ===================================================================================================== *)
Section asan_ubsan.
Local Notation segs := OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.loaded_segments.
Local Notation ph := OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.phdrs.

(* START-UP (asan-ubsan). Row 1. HS_TBL_U := lib/Reusable/YB01.v:601 HS_tfib; row 2. TFIB_TBL_U := lib/Reusable/YB12.v:13
   TFIB: a Theorem Labs lane's generated asan-ubsan start-up tables (donor lib/YB01.v:597, lib/YB12.v:10), the ones
   lib/Reusable/YB1n.v tfib_startup_T1 is proved over. *)
Definition HS_TBL_U : nat -> option acs := RB01.HS_tfib.
Definition TFIB_TBL_U : atable := RB12.TFIB.
(* donor lib/YB1n.v:44-50 HS_ok. *)
Definition HS_okU (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL_U h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.
(* Row 3. H_STARTUP_U: PROVED, lib/Reusable/YB1n.v:55 tfib_startup_T1 (donor lib/YB1n.v:51-59), whose TSEGS / TPH are
   this image's segs / phdrs (Reusable/YB1h.v) and whose HS_ok is HS_okU at the two tables above. *)
Lemma H_STARTUP_U :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okU h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.
Proof. exact RB1n.tfib_startup_T1. Qed.

(* THE PARTS (donor lib/YD1q.v Section d, the twin of AD1q.v:41-63). *)
(* Row 4. B_U := lib/Reusable/YD2l.v:13 PcapB, the asan-ubsan core's asyms (donor lib/YD2l.v:11 TfibB); its symbol
   facts are YD2l.v:71 TfibB_syms : PcapSyms PcapB. *)
Definition B_U : asyms := RD2l.PcapB.
(* Row 5. The asan-ubsan program's read-only range, donor lib/YD1q.v:43 (Variables RLO RHI), bound at lib/YD2o.v:40
   to cgif's 0x9dca8 / 0x9ef18. Here row 11_U's instance binds it the same way, to lib/B/Prog/PcapRelro.v PCAP_RLO /
   PCAP_RHI = 0x99198 / 0x9a3f0 (the start of .data.rel.ro, the end of .got), so it is no Section variable. *)
(* Row 6. KS_U: the asan-ubsan image's source symbols (lib/A/Stdio/PSource.v:87 record; donor lib/YE2k.v:50 tfib_K):
   lib/B/Stdio/PSourceK.v pcap_KS (a Theorem Labs lane, its 22 numerals relocated on the asan-ubsan pin; ofl_head 0x5f4e88,
   PSourceK.pcap_KS_head). *)
Definition KS_U : asource_syms := OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio.PSourceK.pcap_KS.
(* Row 7. SK_U := lib/Reusable/PcapSinkHeads.v asan_ubsan_sink_head (ofl_head 0x5f4e88 = ofl_lock 0x5f4e80 + 8, the
   value of PSourceK.pcap_KS_head), the first explicit argument of row 11_U, passed BY NAME (donor: the global
   instance lib/YE2k.v:44 tfib_sink_head, passed explicitly at lib/YD2o.v:30-34); no instance search fills it. The
   class is named by its full path: lib/U/Reusable/YI16 (the U twin, its own sink_head class) is loaded here too. *)
Definition SK_U : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head := RPSH.asan_ubsan_sink_head.
Lemma HSK_U : @OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sk_ofl_head SK_U = (symaddr Symbols.AsanUbsan.s_ofl_head).
Proof. reflexivity. Qed.
(* Row 8 / row 9. H_ALLOC_MALLOC_U / H_ALLOC_FREE_U: PROVED, lib/Reusable/YF0w.v:44 tfib_amalloc_realizes and
   lib/Reusable/YF0q.v:10 afree_realizes_closed at PcapB (donor lib/YF0w.v:43, lib/YF0q.v:9). *)
Lemma H_ALLOC_MALLOC_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B_U.
Proof. intros rc fx. exact (@RF0w.tfib_amalloc_realizes fx rc B_U RD2l.TfibB_syms (fun _ => eq_refl)). Qed.
Lemma H_ALLOC_FREE_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B_U.
Proof. intros rc fx. exact (@RF0q.afree_realizes_closed fx rc B_U RD2l.TfibB_syms (fun _ => eq_refl)). Qed.
(* Row 10. H_RT_MEMCPY_U: PROVED, lib/Reusable/YD2m.v:16 tfib_AICPY at PcapB (donor lib/YD2m.v:15). *)
Lemma H_RT_MEMCPY_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U)).
Proof. intros rc fx. exact (@RD2m.tfib_AICPY fx rc B_U RD2l.TfibB_syms). Qed.
(* ---- ROW 11_U, DERIVED (a Theorem Labs lane 07:12Z, gate 8). ----
   donor lib/YD1q.v:46 LIBX : tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI (lib/YCfn.v:69), at the donor's
   binding lib/YD2o.v:40 (MT := ameter_triv; XM_LIB = XN_LIB := XL0 = fun _ => 0, lib/YCfi.v:54). fuzz_pcap's type is
   lib/B's measured instance lib/B/Prog/PcapEntry.v tfib_lib_contract_x_all_B (the generic text lib/A/Prog/PcapEntry.v
   tfib_lib_contract_x_all at the asan-ubsan image's segments, PCAP_RLO / PCAP_RHI, A_LLVMF / RA_LLVMF / A_EMPTY /
   LLVMF_STK and G_HARNESS_U), at SK_U (explicit, by position), B_U and KS_U. It is proved below from
   lib/B/Prog/PcapEntryTop.v pcap_entry_top (a working branch 97853c9e4c5): the meter premises at ameter_triv by
   YCbp.ameter_triv_laws, YCbp.ameter_triv_fs_laws, PcapEntryDefs.pe_need_triv_budget and Z.le_refl; AMALLOC4 /
   AFREE4 by YCbp.amalloc04_rule_triv / afree04_rule_triv from rows 8 / 9, whose image premise segs_low is
   PcapEntryTop.pcap_segs_low (proved for this image) and whose other premises errno_low, LAWS and ML are below;
   NSTK / HNSTK / HNEXT by PcapSourceNextDefs.NX_STK_B, NX_STK_B_range and PcapSourceNext.pb_pcap_source_nextX. Every
   other premise of pcap_entry_top is one lemma or value below, with pcap_entry_top's name and type
   (PcapEntryTop.v:324-427), quantified over rc where the type names rc. Row 10 (H_RT_MEMCPY_U, the memcpy interceptor
   at pc_wrap_memcpy (as_code B_U), the driver's call) does not give HMCPY (__asan_memcpy at the listing's
   PS___asan_memcpy, the program's calls): the two entry pcs differ, so HMCPY is its own lemma. *)
(* The core's facts at PcapB are PROVED in lib/B/PcapBFacts.v (BFacts a2a2af22378, the asan-ubsan twin of
   lib/A/PcapBFacts.v): errno_low (:151), TL (:163), TLF (:178), FFL (:203), HGOS (:223), HGERR (:232), HTRM (:251),
   HTRF (:261), AFM (:277), HROI (:284), HPATH (:350), each applied by name below. *)
Lemma errno_low : RCbq.api_env segs B_U.
Proof. exact BBF.PcapB_errno_low. Qed.
(* (2) the core's B and the runtime rules (PcapEntryTop.v:333-355). Owner: the asan-ubsan core (a10). *)
Lemma LAWS : forall rc : YM05.RunCeil, @AR_laws rc (PSEGS rc) B_U.
Proof. intros rc. exact (@RG0q.AR_laws_ok rc (PSEGS rc) B_U). Qed.
Lemma TL : forall rc : YM05.RunCeil, @PPL.PALib rc PLS.pcap_listing (PIp rc) B_U.
Proof. exact BBF.PcapB_TL. Qed.
Lemma TLF : forall rc : YM05.RunCeil, @PFR.PALibF rc PLS.pcap_listing (PIp rc) B_U.
Proof. exact BBF.PcapB_TLF. Qed.
Lemma ML : model_laws (as_universe B_U).
Proof. exact (RG05.model_laws_ok (as_universe B_U) RCej.Tfib_universe_ok). Qed.
Lemma ASF : forall rc : YM05.RunCeil, @astack_free_law rc (PSEGS rc) B_U.
Proof. intros rc. exact (@RG0t.astack_free_law_ok rc (PSEGS rc) B_U). Qed.
Lemma FFL : forall rc : YM05.RunCeil, @RCbq.frame_flag_lawP rc (PSEGS rc) B_U.
Proof. exact BBF.PcapB_FFL. Qed.
Lemma ASM1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc (PSEGS rc) B_U 1.
Proof. intros rc fx. exact (@RF0s.stack_malloc1_contract fx rc B_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms). Qed.
Lemma HGOS : forall a, WJG.inG PEB.G_HARNESS_U a -> ~ Exists (RG0n.in_zr a) (as_owned_static B_U).
Proof. exact BBF.PcapB_HGOS. Qed.
Lemma HGERR : forall a, WJG.inG PEB.G_HARNESS_U a -> ~ (as_errno B_U <= a < as_errno B_U + 4).
Proof. exact BBF.PcapB_HGERR. Qed.
Lemma HTRM : forall (rc : YM05.RunCeil) (cx : @PED.ecx rc (PIp rc)), raZ (PED.c_regs cx) = PEB.RA_LLVMF ->
  forall regsT : bvmap 5 word, In (raZ regsT - VALp rc PAT.A_TEXT) PED.PE_MALLOC_SITES ->
  In (RCbq.call_trace0 (pc_malloc_ra0 (as_code B_U)) regsT (PED.pch cx)) (as_universe B_U).
Proof. exact BBF.PcapB_HTRM. Qed.
Lemma HTRF : forall (rc : YM05.RunCeil) (cx : @PED.ecx rc (PIp rc)), raZ (PED.c_regs cx) = PEB.RA_LLVMF ->
  forall regsT : bvmap 5 word, In (raZ regsT - VALp rc PAT.A_TEXT) PED.PE_FREE_SITES ->
  In (RCbq.call_trace0 (pc_free_ra0 (as_code B_U)) regsT (PED.pch cx)) (as_universe B_U).
Proof. exact BBF.PcapB_HTRF. Qed.
(* (3) pcap_KS at B_U (PcapEntryTop.v:359-360). Owner: stdio (a Theorem Labs lane) with the core. *)
Lemma ASIL : forall rc : YM05.RunCeil, PSM.asource_img_laws SK_U (PSEGS rc) B_U KS_U.
Proof. intros rc. exact (@RD1u.tfib_ASIL SK_U HSK_U B_U RD2l.TfibB_syms). Qed.
Lemma AFM : forall rc : YM05.RunCeil, @PSR.asrc_file_meter rc SK_U (PSEGS rc) B_U ameter_triv.
Proof. exact BBF.PcapB_AFM. Qed.
(* (4) the callee contracts and their call-site facts (PcapEntryTop.v:375-420), at the bound values above. *)
(* AFCLOSE: PROVED, lib/B/Stdio/PFcloseInstB.v:134 inst_AFCLOSE_U (a Theorem Labs lane; the fclose
   interceptor and musl fclose walks WFcloseI / WFclose / WFflush / WMseek) at asan_ubsan_sink_head, PcapB, pcap_KS,
   with ra_fc1 / ra_fc2 = WFcloseI.WFI_FREE1 / WFI_JOIN (lib/B/Stdio/WFcloseI.v:240-241) = RA_FC1_U / RA_FC2_U. *)
Lemma AFCLOSE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PFC.afclose_source_spec fx rc SK_U (PSEGS rc) B_U KS_U
    (SIGp rc PSY.PS___interceptor_trampoline_fclose) RA_FC1_U RA_FC2_U (RLOp rc) (RHIp rc).
Proof. intros rc fx. exact (@BFCI.inst_AFCLOSE_U rc fx). Qed.
Lemma HUfc1 : In [pc_free_ra0 (as_code B_U); RA_FC1_U] (as_universe B_U).
Proof. exact (proj1 RCejS.fclose_free_in). Qed.
Lemma HUfc2 : In [pc_free_ra0 (as_code B_U); RA_FC2_U] (as_universe B_U).
Proof. exact (proj2 RCejS.fclose_free_in). Qed.
(* pcap_source_next's contract is PROVED: lib/B/Prog/PcapSourceNext.v pb_pcap_source_nextX (a Theorem Labs lane, a working branch 654436fa8b4)
   at SK_U, PI_pcap, B_U, ameter_triv and KS_U, at the stack bound NX_STK_B (so pcap_entry_top's NSTK is
   PcapSourceNextDefs.NX_STK_B and its HNSTK is NX_STK_B_range). Its premises are LAWS, TL, TLF, ML, ASF, FFL, ASIL
   above, MTL / MTF at ameter_triv (YCbp.ameter_triv_laws / ameter_triv_fs_laws), and the four below, with
   pb_pcap_source_nextX's names and types (PcapSourceNext.v:93-97), quantified over rc and fx where the type names
   them. *)
Lemma H_sm0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc (PSEGS rc) B_U 0.
Proof. intros rc fx. exact (@BSM0.stack_malloc0_contract fx rc B_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms). Qed.
Lemma SMP : RCbq.stack_malloc_progressP B_U.
Proof. exact (PSO.op_SMP B_U). Qed.
(* H_fread: PROVED, lib/B/Stdio/PFreadC.v:41 pcapu_afread_closed (a Theorem Labs lane, a working branch aa208b46fb8) at PcapB, SK_U and
   pcap_KS = KS_U, with LAWS, TfibB_syms and ASIL; FR_ENTRY_U = pa_sigma PS___interceptor_trampoline_fread (fread_pc_U).
   It is pcapu_afread_spec (PFreadI.v) with its one premise, the musl fread body's contract at PStdioImgB.PFREAD_U
   (fread+0 = 0x8ed28), discharged by a Theorem Labs lane's asan-ubsan walks PFreadMWB.rfread_contract_asan_ubsan,
   PFtoreadMWB.rtoread_contract_asan_ubsan and PFmreadMWB.rmread_contract_asan_ubsan. The seven fread files are taken by
   path from the counted B record union (a working branch a000e65343e), so the former Section hypothesis RFR is
   gone. *)
Lemma H_fread : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PFRD.afread_spec fx rc SK_U (PSEGS rc) B_U KS_U (SIGp rc PSY.PS___interceptor_trampoline_fread).
Proof.
  intros rc fx.
  exact (@BFRC.pcapu_afread_closed fx rc B_U SK_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms (ASIL rc)).
Qed.
Lemma H_memmove : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PMMV.amemmove_realizes fx rc (PSEGS rc) B_U (SIGp rc PSY.PS___asan_memmove).
Proof. intros rc fx. exact (@BMMV.asan_memmove_contract fx rc B_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms). Qed.
(* HMCPY / HMSET: PROVED, Reusable/YE2q.v:145 asan_memcpy_realizes and YE2r.v:569 asan_memset_realizes at PcapB (the
   twins of a Theorem Labs lane's A-side inst_HCPY / inst_HSET, lib/A/Prog/PcapEntryInst.v:321 / :335 on
   a working branch 8994a3154289); pcs memcpy_pc_U / memset_pc_U. HMSET is a Theorem Labs lane's bridge, premise
   order only: aintrin_realizes OSet (Reusable/YG0d.v:318-336) takes amem_range d n right after dest_ok and a `True`
   premise for OSet; asan_memset_realizes takes amem_range d n last and has no `True` premise. *)
Lemma HMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc (PSEGS rc) B_U OCpy (SIGp rc PSY.PS___asan_memcpy).
Proof. intros rc fx. exact (@RE2q.asan_memcpy_realizes fx rc B_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms). Qed.
Lemma HMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc (PSEGS rc) B_U OSet (SIGp rc PSY.PS___asan_memset).
Proof.
  intros rc fx ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
  exact (@RE2r.asan_memset_realizes fx rc B_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
(* ABCMP: PROVED, Reusable/YE2s.v:712 bcmp_icpt_contract at PcapB; pc bcmp_pc_U. *)
Lemma ABCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc (PSEGS rc) B_U (SIGp rc PSY.PS___interceptor_trampoline_bcmp).
Proof. intros rc fx. exact (@RE2s.bcmp_icpt_contract fx rc B_U (@RG0q.AR_laws_ok rc segs B_U) RD2l.TfibB_syms). Qed.
(* pcap_source_open at both call sites (PP_K2 and PP_K7): with FM_RA_K2 = FM_RA = FM_RA_U, CTX_K2 = CTX = CTX_U and
   ROI_K2 = ROI = ROI_U, pcap_entry_top's HOPEN and OPENS are one proposition, HROI_K2 and HROI are one, HFMU_K2 and
   HFMU are one; each is one lemma below, passed at both sites. HCTX_K2 / HCTX are proved (CTX_U_K2 / CTX_U_K7).
   HOPEN: PROVED, lib/B/PcapOpenInstB.v inst_HOPEN, lib/B/Prog/PcapSourceOpen.v:1706 pb_pcap_source_openX at this
   file's values (its FOPEN lib/B/Prog/PcapFuzzFopen.v pb_libreac_fuzz_fopenX; its ROK, MCONSTS, STRCMP and AFMEMOPEN
   lib/B/PcapRokB.v, PcapMconstsB.v, PcapStrcmpPathB.v, PcapAfmemopenB.v). fmemopen's buf == NULL arm is not
   assumed away: musl fmemopen's walk refutes it at its branch from b >= 4096 (PFmemopenMW.v phase C). *)
Lemma HOPEN : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PEC.AO.tpcap_source_open_specX fx rc SK_U (PSEGS rc) (RLOp rc) (RHIp rc) (VALp rc (PAT.A_OBJ 3))
    (VALp rc (PAT.A_OBJ 4)) (VALp rc (PAT.A_OBJ 2)) ROI_U B_U KS_U ameter_triv FM_RA_U CTX_U
    (VALp rc PAT.A_TEXT + PLS.AF_pcap_source_open).
Proof. exact POIB.inst_HOPEN. Qed.
Lemma HROI : forall (rc : YM05.RunCeil) (W : RA0n.world (PSEGS rc)) mem,
  PBA.arodata_okP (PSEGS rc) (RLOp rc) (RHIp rc) B_U (RG0n.aview (PSEGS rc) (RA0n.w_H W) mem) ->
  ROI_U (RK04.mrestrict (RA0n.w_H W) mem).
Proof. exact BBF.PcapB_HROI. Qed.
Lemma HPATH : forall (rc : YM05.RunCeil) ly S0 (W : RA0n.world (PSEGS rc)) mem md,
  RG0n.AR (PSEGS rc) B_U ly S0 W mem md ->
  RG0v.range_addressable (RG0n.aview (PSEGS rc) (RA0n.w_H W) mem) SHADOW_OFF (VALp rc (PAT.A_OBJ 3)) 13 /\
  shadow_hull_vis (RG0n.aview (PSEGS rc) (RA0n.w_H W) mem) (VALp rc (PAT.A_OBJ 3)) 13.
Proof. exact BBF.PcapB_HPATH. Qed.
(* HFMU: PROVED from errno_low's trace conjunct (YCbq.api_env) and lib/Reusable/YCejSites.v:41
   fmemopen_malloc_ctx_in (pc_malloc_ra0 (as_code PcapB) = 0x52ec4, FM_RA_U = 0x8e7d8, CTX_U its table). *)
Lemma HFMU : In [pc_malloc_ra0 (as_code B_U)] (as_universe B_U) /\
  (forall c, In c CTX_U -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B_U) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B_U) then [] else [r]) (FM_RA_U :: c))) (as_universe B_U)).
Proof.
  split.
  - exact (proj1 (proj2 (proj2 errno_low))).
  - intros c Hc. exact (RCejS.fmemopen_malloc_ctx_in FM_RA_U c (or_introl eq_refl) Hc).
Qed.

(* Row 11_U: pcap_entry_top at this file's parts. *)
Lemma H_PROG_LIBCONTRACT_U_of : forall (rc : YM05.RunCeil),
  @PEB.tfib_lib_contract_x_all_B rc SK_U B_U ameter_triv (fun _ => 0) (fun _ => 0) KS_U.
Proof.
  intros rc.
  exact (@PET.pcap_entry_top rc SK_U B_U ameter_triv (fun _ => 0) (fun _ => 0)
    ameter_triv_laws ameter_triv_fs_laws PED.pe_need_triv_budget (fun _ => Z.le_refl 0)
    (LAWS rc) (TL rc) (TLF rc) ML (ASF rc) (FFL rc) (ASM1 rc)
    (fun fx => @amalloc04_rule_triv fx rc SK_U segs B_U PET.pcap_segs_low errno_low (LAWS rc) ML
      (H_ALLOC_MALLOC_U rc fx))
    (fun fx => @afree04_rule_triv fx rc SK_U segs B_U PET.pcap_segs_low errno_low (LAWS rc) ML
      (H_ALLOC_FREE_U rc fx))
    HGOS HGERR (HTRM rc) (HTRF rc) (ASIL rc) (AFM rc) RA_FC1_U RA_FC2_U (AFCLOSE rc) HUfc1 HUfc2
    PSND.NX_STK_B NX_STK_B_range
    (fun fx => @PSN.pb_pcap_source_nextX fx rc SK_U (PIp rc) B_U ameter_triv KS_U (LAWS rc) (TL rc) (TLF rc) ML
      ameter_triv_laws ameter_triv_fs_laws (ASF rc) (FFL rc) (ASIL rc) (H_sm0 rc fx) SMP (H_fread rc fx)
      (H_memmove rc fx))
    (HMCPY rc) (HMSET rc) (ABCMP rc) FM_RA_U CTX_U ROI_U (HOPEN rc) (HROI rc) (CTX_U_K2 rc) HFMU
    FM_RA_U CTX_U ROI_U (HOPEN rc) (HROI rc) (HPATH rc) (CTX_U_K7 rc) HFMU).
Qed.
(* GUARD (a Theorem Labs lane): the head argument of row 11 is SK_U (asan_ubsan_sink_head, by name), by position.
   This Check does not build if row 11 had another closed head (such as YI5b.src0_sink_head, which inference picks
   where no head is given), nor if PcapEntry made SK implicit again (SK_U would then land on B's slot). The Fail line
   shows that the head matters. *)
Check (H_PROG_LIBCONTRACT_U_of : forall rc : YM05.RunCeil,
  PEB.tfib_lib_contract_x_all_B (rc:=rc) SK_U B_U ameter_triv (fun _ => 0) (fun _ => 0) KS_U).
Fail Check (fun SK' : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head =>
  (H_PROG_LIBCONTRACT_U_of : forall rc : YM05.RunCeil,
    PEB.tfib_lib_contract_x_all_B (rc:=rc) SK' B_U ameter_triv (fun _ => 0) (fun _ => 0) KS_U)).
(* donor lib/YD1q.v drv_mainX_stmt (the twin of AD1q.v:64-76). *)
Definition drv_mainU (rc : YM05.RunCeil) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_TBL_U h = Some ch ->
  cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
    FULL a = wrap_mem ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).
(* Row 12. H_TRACES_B_U: PROVED by reflexivity: lib/Reusable/YD2l.v PcapB's as_universe is YCej.Tfib_universe (donor
   lib/YD2l.v as_universe := Tfib_universe); trace lemmas Reusable/YCej.v:153 Tfib_universe_ok and
   Reusable/YCejTfib.v:25 Tfib_universe_drv (owner: a Theorem Labs lane; complete). *)
Lemma H_TRACES_B_U : as_universe B_U = YCej.Tfib_universe.
Proof. reflexivity. Qed.
(* Row 13. H_DRIVER_U: PROVED, lib/Reusable/YD2o.v:65 pcap_H_DRIVER (the driver main lib/B/PcapDriver.v DRV_MAINX at
   B := PcapB, SK := pcap_drv_SK = asan_ubsan_sink_head, KS := lib/B pcap_KS, the stdio sites bound to YD1k's xst / est
   and their proved site lemmas; donor lib/YD2o.v); its conclusion drv_mainX_stmt is drv_mainU at the bound tables, and
   it does not use the two trace premises. *)
Lemma H_DRIVER_U : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B_U) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B_U) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U))) ->
  @PEB.tfib_lib_contract_x_all_B rc SK_U B_U ameter_triv (fun _ => 0) (fun _ => 0) KS_U ->
  universe_ok (as_universe B_U) ->
  (forall t, In t YCejTfib.Tfib_drv_traces -> In t (as_universe B_U)) ->
  drv_mainU rc.
Proof. intros rc AM AF AI LIBX _ _. exact (RD2o.pcap_H_DRIVER rc AM AF AI LIBX). Qed.

Lemma HS_ok_openU : forall h sp rdraw brk0 argv envp uid hw fs c,
  HS_okU h sp rdraw brk0 argv envp uid hw fs c ->
  exists ch E R FULL model,
    HS_TBL_U h = Some ch /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk0 argv envp uid hw) n)
    /\ (forall a, YA02.argH0 ph sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a)
    /\ eb E = eb (YA02.E0 ph sp rdraw brk0 argv envp uid hw).
Proof.
  intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Section RCU. Context {rc : YM05.RunCeil}.
Lemma DRV_MAINU : drv_mainU rc.
Proof.
  apply (H_DRIVER_U rc (H_ALLOC_MALLOC_U rc) (H_ALLOC_FREE_U rc) (H_RT_MEMCPY_U rc) (H_PROG_LIBCONTRACT_U_of rc)).
  - rewrite H_TRACES_B_U. exact YCej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B_U. exact (YCejTfib.Tfib_universe_drv t Ht).
Qed.
(* donor lib/YD1q.v:75 tfib_srealizesX, the same proof. *)
Lemma pcap_srealizesXU_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_pcap.images.AsanUbsan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP_U sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
    (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (HS_ok_openU h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  exact (DRV_MAINU sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
    Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End RCU.

Theorem ASAN_UBSAN_T_of_parts : PcapAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@pcap_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowP sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

Theorem pcap_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (PcapAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Theorem pcap_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (PcapAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
(* Inside the Section, Print Assumptions lists what each statement rests on; no Section hypothesis is left. *)
Print Assumptions pcap_asan_ubsan_agrees_of_parts.
Print Assumptions pcap_asan_ubsan_halts_of_parts.
End asan_ubsan.
(* After the Section: About lists every part a statement rests on (its arguments, rows 1-13 and the premises of
   row 11_U's derivation, also the parts that occur only in other parts' types); Print Assumptions lists the axioms. *)
About H_PROG_LIBCONTRACT_U_of.
Print Assumptions H_PROG_LIBCONTRACT_U_of.
About ASAN_UBSAN_T_of_parts.
Print Assumptions ASAN_UBSAN_T_of_parts.
About pcap_asan_ubsan_agrees_of_parts.
Print Assumptions pcap_asan_ubsan_agrees_of_parts.
About pcap_asan_ubsan_halts_of_parts.
Print Assumptions pcap_asan_ubsan_halts_of_parts.
