(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan),
   ossv/recipes c8557374ad2e, for fuzz_pcap: the closing of PcapAsanTop.ASAN_T from named parts; module paths
   changed, shape AgreePcap.ag_out_shape (PcapAsanTop.pcap_shape), fuzz_pcap's images. The asan-ubsan twin (donor
   lib/YD2o.v, YD2p.v and YD1q.v) is lib/B/PcapCloseB.v. *)
(* The closing side of fuzz_pcap's four ASan statements (rule 24: no function proved; this file is assembly).

   The donor closes TFIB_T in two steps: AD2o.v:63-84 applies AD1q.v:79-98 tfib_srealizesX. tfib_srealizesX joins
   the start-up (AB1n.v:52 tfib_startup_T1), the hand-off (AB1n.v:74 HS_ok_open), the driver main (AD1q.v:64-78:
   AD1p.v:84 tfib_drv_main over the parts AD1q.v:41-63) and the spec link (YO01 specx_closedx_eq). This file does the
   same at the level whose TYPES are pushed on fuzz_pcap's union (a working branch 06287de1f53, a working branch
   feee1c79855, the tr files in it). Every input is bound to the image's named object or proved by a named lemma below,
   with the donor statement it stands for and the lane that supplies it; no Section variable or hypothesis is left.
   The asan-ubsan image has the same 13 rows, with _U, in
   lib/B/PcapCloseB.v.

   Open core item (a Theorem Labs lane, ruling 21:43Z): the driver's site lemma (AD1m.v:34-60 tfib_lib_site_x, AD1w.v:80
   lib_site_x) threads cgif's sink facts (asink_none: AD1m.v:52 builds it, AD1m.v:55-59 destructs it to restore FINV);
   fuzz_pcap's program contract (lib/A/Prog/PcapEntry.v, feee1c79855) states the source instead (asource_none segs KS,
   as_ofl_head KS = AOFL_HEAD, asrc_meta_inv segs KS); the fd-names conjunct of asink_none is dropped on pcap's side
   because pcap opens no descriptor by name (its fopen is wrapped to fmemopen; evidence in e7558c56fa6). The core
   restates FINV / lib_site_x over pcap's source; H_DRIVER below is the driver at that restated form.

   The sink head SK is lib/Reusable/PcapSinkHeads.v asan_sink_head (ofl_head 0x5f4f88), passed by name and by
   position to the program contract (rows 7 and 11, with a Check guard). KS is lib/A/Stdio/PSourceK.v pcap_KS, B is
   lib/A/AD2l.v PcapB and the start-up tables are lib/A/AB01.v HS_tfib / lib/A/AB12.v TFIB (a Theorem Labs lane 09:44Z: no free
   argument on the tops). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap Require Statements.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01 YG0f YG0d YC5d YCbp YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryA PcapEntryInst PcapEntryStdio
  PcapEntryFinal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PStdioImgA.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require ACej ACejTfib AD2l AB01 AB12 AB1n AF0w AF0q AD2m AD2o.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PcapSinkHeads.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import PcapAsanTop.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := PcapAsanTop.pcap_shape.

(* Row 11's program instance (lib/A/Prog/PcapEntryInst.v pcap_entry_inst) and its stdio premises
   (lib/A/Prog/PcapEntryStdio.v), by their full paths (lib/B and lib/U load modules of the same short names in other
   closures). *)
Module PEI := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapEntryInst.
Module PES := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapEntryStdio.

(* ===================================================================================================== *)
(* ASan image                                                                                              *)
(* ===================================================================================================== *)
Section asan.
Local Notation segs := OSSVerify.libreac.fuzz_pcap.images.Asan.M.loaded_segments.
Local Notation ph := OSSVerify.libreac.fuzz_pcap.images.Asan.M.phdrs.

(* START-UP. Row 1. HS_TBL := lib/A/AB01.v:600 HS_tfib, the start-up's hand-off states (donor lib/A/AB01.v:597,
   per-binary data). Row 2. TFIB_TBL := lib/A/AB12.v:12 TFIB, the image table of the start-up certificate (donor
   lib/A/AB12.v:10). *)
Definition HS_TBL : nat -> option acs := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AB01.HS_tfib.
Definition TFIB_TBL : atable := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AB12.TFIB.
(* donor lib/A/AB1n.v:45-51 HS_ok, at HS_TBL / TFIB_TBL and fuzz_pcap's ASan image. *)
Definition HS_okA (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.
(* Row 3. H_STARTUP: PROVED, lib/A/AB1n.v:55 tfib_startup_T1 (donor lib/A/AB1n.v:52-60, closed over
   tfib_startup_closed), whose TSEGS / TPH are Asan.M.loaded_segments / phdrs (lib/A/AB1h.v:19-20) and whose HS_ok is
   HS_okA at the two tables above. *)
Lemma H_STARTUP :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okA h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_pcap.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AB1n.tfib_startup_T1. Qed.

(* THE PARTS THE DRIVER CONSUMES (donor lib/A/AD1q.v:41-63, the Section of tfib_srealizesX), as far as their types
   are pushed. *)
(* Row 4. B := lib/A/AD2l.v:18 PcapB, the image's symbol and trace table (donor lib/A/AD2l.v:14 TfibB). *)
Definition B : asyms := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AD2l.PcapB.
(* Row 5. RLO / RHI: the program's read-only range, donor lib/A/AD1q.v:43 (Variables RLO RHI), bound at lib/A/AD2o.v:45
   to cgif's 0x9da38 / 0x9eca8. Here row 11's instance binds them the same way, to lib/A/Prog/PcapRelro.v:22-23
   PCAP_RLO / PCAP_RHI = 0x992d0 / 0x9a528 (inside the image: PcapRelro.v:28 pcap_relro_in_image_b). So the asan image
   has no free RLO / RHI. Owner: program a Theorem Labs lane. *)
(* Row 6. KS := lib/A/Stdio/PSourceK.v:96 pcap_KS, the source symbols (lib/A/Stdio/PSource.v:87 record; owner stdio
   a Theorem Labs lane). It replaces the donor's sink symbols tfib_K (lib/A/AE2k.v:50) in the program contract
   (PcapEntry over asrc_meta_inv segs KS). *)
Definition KS : asource_syms := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio.PSourceK.pcap_KS.
(* Row 7. SK := lib/Reusable/PcapSinkHeads.v asan_sink_head (ofl_head 0x5f4f88), the asan sink head, the first explicit
   argument of the program contract, passed by name (donor: the global instance lib/A/AE2k.v:44 tfib_sink_head,
   passed explicitly at AD2o.v:35-39). The class is named by its full path: lib/U/Reusable/YI16 (the U twin, its own
   sink_head class) is loaded in this closure too, so the short name YI16 depends on the Require order. *)
Definition SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head :=
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.asan_sink_head.
(* Row 8. H_ALLOC_MALLOC: PROVED, lib/A/AF0w.v:53 pcap_amalloc_realizes (donor lib/A/AD1q.v:43 AMALLOC, closed by
   AF0w.v:44 tfib_amalloc_realizes at PcapB). *)
Lemma H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AF0w.pcap_amalloc_realizes. Qed.
(* Row 9. H_ALLOC_FREE: PROVED, lib/A/AF0q.v:19 pcap_afree_realizes (donor lib/A/AD1q.v:44 AFREE). *)
Lemma H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AF0q.pcap_afree_realizes. Qed.
(* Row 10. H_RT_MEMCPY: PROVED, lib/A/AD2m.v:17 tfib_AICPY at PcapB with lib/A/AD2l.v:74 PcapB_syms (donor
   lib/A/AD1q.v:45 AICPY, the memcpy interceptor). *)
Lemma H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
  intros rc fx.
  exact (@OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AD2m.tfib_AICPY fx rc B
    OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AD2l.PcapB_syms).
Qed.
(* Row 11. H_PROG_LIBCONTRACT_of: donor lib/A/AD1q.v:50 LIBX : tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI
   (lib/A/ACfn.v:71, closed by lib/A/ACfi.v:139 tfib_lib_x_all), at the donor's binding lib/A/AD2o.v:45 (MT :=
   ameter_triv, Reusable/YCbp.v:16; XM_LIB = XN_LIB := XL0 = fun _ => 0, ACfi.v:56; RLO / RHI := the image's range).
   fuzz_pcap's type is the lib/A instance lib/A/Prog/PcapEntryA.v tfib_lib_contract_x_all_A
   (a working branch feee1c79855): the generic text PcapEntry.v:96-99 tfib_lib_contract_x_all at
   Asan.M.loaded_segments, PCAP_RLO / PCAP_RHI, A_LLVMF 0x807c8, RA_LLVMF 0x80634, A_EMPTY 0x5d3f20, LLVMF_STK 32768
   (PcapEntry.v:25-30) and G_HARNESS = [(0x5d3f40, 8); (0x5d3f60, 8)] (PcapEntry.v:36, the harness's globals the call
   writes: W_journal.v's ajournal_gx G, fuzz_pcap's addition); the donor's arguments plus SK (explicit, by position),
   G and KS. It is DERIVED below (H_PROG_LIBCONTRACT_of) from a Theorem Labs lane's lib/A/Prog/PcapEntryInst.v:473 pcap_entry_inst
   (a working branch 7d8c322a9df) at SK := asan_sink_head, B := AD2l.PcapB, MT := ameter_triv,
   XM_LIB = XN_LIB := fun _ => 0, KS := pcap_KS. Its seven stdio binders are a Theorem Labs lane's, from
   lib/A/Prog/PcapEntryStdio.v (:103-:168): FM_RA := PStdioImgA.FM_MALLOC_RA, CTX := ACej.CTX_pcap_source_open,
   HCTX / HCTX_A / HFMU := pcap_entry_HCTX / pcap_entry_HCTX_A / pcap_entry_HFMU, AFREAD / AFMEMOPEN :=
   pcap_entry_AFREAD / pcap_entry_AFMEMOPEN at SK := asan_sink_head and the instance's ASIL, PcapEntryInst.inst_ASIL.
   So row 11 has no Section argument. *)
(* Row 11: pcap_entry_inst at those premises, by name with every argument written, so a reordered binder fails
   loudly. SK / B / KS above are Definitions of asan_sink_head / PcapB / pcap_KS: they are unfolded, and
   PcapEntryFinal's fit logs each argument whose type is its premise only up to conversion and closes the goal only
   when the instance's conclusion is the goal syntactically. *)
Lemma H_PROG_LIBCONTRACT_of : forall (rc : YM05.RunCeil),
  @PcapEntryA.tfib_lib_contract_x_all_A rc SK B ameter_triv (fun _ => 0) (fun _ => 0) KS.
Proof.
  intros rc. unfold SK, B, KS.
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapEntryFinal.fit
    (@PEI.pcap_entry_inst rc PStdioImgA.FM_MALLOC_RA ACej.CTX_pcap_source_open (@PES.pcap_entry_HCTX rc)
      PES.pcap_entry_HFMU
      (@PES.pcap_entry_AFREAD rc OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.asan_sink_head
        PEI.inst_ASIL)
      (@PES.pcap_entry_AFMEMOPEN rc OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.PcapSinkHeads.asan_sink_head
        PEI.inst_ASIL)
      (@PES.pcap_entry_HCTX_A rc)).
Qed.
(* GUARD (a Theorem Labs lane): the head argument of row 11 is SK (asan_sink_head, by name), by position. This Check
   does not build if row 11 had another closed head (for YI5b.src0_sink_head, the global instance that inference
   picks where no head is given, the two types do not unify), nor if PcapEntry made SK implicit again (SK would then
   land on B's slot). The Fail line shows that the head matters: at any other head the type is a different
   proposition. *)
Check (H_PROG_LIBCONTRACT_of : forall rc : YM05.RunCeil,
  PcapEntryA.tfib_lib_contract_x_all_A (rc:=rc) SK B ameter_triv (fun _ => 0) (fun _ => 0) KS).
Fail Check (fun SK' : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head =>
  (H_PROG_LIBCONTRACT_of : forall rc : YM05.RunCeil,
    PcapEntryA.tfib_lib_contract_x_all_A (rc:=rc) SK' B ameter_triv (fun _ => 0) (fun _ => 0) KS)).
(* donor lib/A/AD1q.v:64-76 drv_mainX_stmt, at HS_TBL / TFIB_TBL, fuzz_pcap's ASan image and LS. *)
Definition drv_mainA (rc : YM05.RunCeil) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_TBL h = Some ch ->
  cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
    FULL a = wrap_mem ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).
(* Row 12. H_TRACES_B: PROVED, lib/A/AD2l.v:43 PcapB_universe (donor lib/A/AD2l.v:37 as_universe := Tfib_universe).
   With it the trace facts of the donor's TfibSyms (lib/A/AF0m.v:313-314, ts_universe / ts_universe_drv) come from the
   trace lane's lemmas directly (lib/A/ACej.v:153 Tfib_universe_ok, lib/A/ACejTfib.v:25 Tfib_universe_drv). *)
Lemma H_TRACES_B : as_universe B = ACej.Tfib_universe.
Proof. exact OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AD2l.PcapB_universe. Qed.
(* Row 13. H_DRIVER: PROVED, lib/A/AD2o.v:62 pcap_H_DRIVER (the driver main lib/A/PcapDriver.v DRV_MAINX at B := PcapB,
   SK := pcap_drv_SK = asan_sink_head, KS := pcap_KS, the stdio sites bound to AD1k's xst / est and their proved site
   lemmas; donor lib/A/AD2o.v:28-60, AD1p.v:84 tfib_drv_main); its conclusion drv_mainX_stmt is drv_mainA at the bound
   tables, and it does not use the two trace premises. *)
Lemma H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  @PcapEntryA.tfib_lib_contract_x_all_A rc SK B ameter_triv (fun _ => 0) (fun _ => 0) KS ->
  universe_ok (as_universe B) ->
  (forall t, In t ACejTfib.Tfib_drv_traces -> In t (as_universe B)) ->
  drv_mainA rc.
Proof.
  intros rc AM AF AI LIBX _ _.
  exact (OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.AD2o.pcap_H_DRIVER rc AM AF AI LIBX).
Qed.

(* donor lib/A/AB1n.v:74-87 HS_ok_open, the same proof (cs_ok's co_sinv field, Reusable/YA0e.v:233). *)
Lemma HS_ok_openA : forall h sp rdraw brk0 argv envp uid hw fs c,
  HS_okA h sp rdraw brk0 argv envp uid hw fs c ->
  exists ch E R FULL model,
    HS_TBL h = Some ch /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk0 argv envp uid hw) n)
    /\ (forall a, YA02.argH0 ph sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a)
    /\ eb E = eb (YA02.E0 ph sp rdraw brk0 argv envp uid hw).
Proof.
  intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Section RC. Context {rc : YM05.RunCeil}.
(* donor lib/A/AD1q.v:77-78 DRV_MAINX, from H_DRIVER and the parts. *)
Lemma DRV_MAINA : drv_mainA rc.
Proof.
  apply (H_DRIVER rc (H_ALLOC_MALLOC rc) (H_ALLOC_FREE rc) (H_RT_MEMCPY rc) (H_PROG_LIBCONTRACT_of rc)).
  - rewrite H_TRACES_B. exact ACej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B. exact (ACejTfib.Tfib_universe_drv t Ht).
Qed.
(* donor lib/A/AD1q.v:79-98 tfib_srealizesX, the same proof. *)
Lemma pcap_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_pcap.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
    (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (HS_ok_openA h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  exact (DRV_MAINA sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
    Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End RC.

(* donor lib/A/AD2o.v:75-84 tfib_srealizesX_top and TFIB_T_of_partsXF. *)
Theorem ASAN_T_of_parts : PcapAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@pcap_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowP sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan statements, given only the named parts above. *)
Theorem pcap_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (PcapAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem pcap_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (PcapAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.
End asan.
(* After the Section: About shows that no statement takes a Section argument (every part is bound or proved above);
   Print Assumptions lists the axioms. *)
About H_PROG_LIBCONTRACT_of.
About DRV_MAINA.
About pcap_srealizesX_rc.
About ASAN_T_of_parts.
Print Assumptions ASAN_T_of_parts.
About pcap_asan_agrees_of_parts.
Print Assumptions pcap_asan_agrees_of_parts.
About pcap_asan_halts_of_parts.
Print Assumptions pcap_asan_halts_of_parts.
