(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan),
    for fuzz_pcap: the closing of PcapAsanTop.ASAN_T from named parts; module paths
   changed, shape AgreePcap.ag_out_shape (PcapAsanTop.pcap_shape), fuzz_pcap's images. The asan-ubsan twin (donor
   lib/YD2o.v, YD2p.v and YD1q.v) is lib/B/PcapCloseB.v. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's channel-reader fact for fdchan's third conjunct; the CONFIG_RSEQ-sized auxiliary vector; the launch's ProcInput, mmap base and entry draw; the start-up hand-off states computed in the build; the launch input with its SIGPIPE default free; the reader fact threaded through the read loop; fdchan's third conjunct, the channel-reader flag, carried in cs_ok (co_rdr) and threaded to the fd sites; the launch's string area with the exec file name); internal commit ids in comments replaced by public commits or removed. *)
(* The closing side of fuzz_link's two ASan statements, asan_halts and asan_agrees (proves no function; kind:
   statement close). The shape is the file named above, row for row, at fuzz_link's ASan image, B := lib/A/AD2l.v
   PcapB and SK := lib/A/AMemFile.v link_asink_head.

   The ASan driver's closing lemma, lib/A/AD2o.v link_H_DRIVER, takes the same four premises as the donor's: the
   allocator's malloc and free realizers and the memcpy interceptor's realizer at every FP state, and the program
   contract at SK, B, the trivial meter and XM_LIB = XN_LIB = fun _ => 0. It takes no source symbols, so the donor's
   KS has no row, and no trace premises, so the donor's H_TRACES_B has no row. fuzz_link has no read source: its
   input is LLVMFuzzerTestOneInput's data and size arguments (projects/reac-pw/fuzz_link/source/fuzz_link.c:764),
   and its memory FILE is a WRITE sink for the marking policy's messages (fmemopen(g_said, sizeof g_said, "w"),
   fuzz_link.c:156), not an input stream. The donor's KS described fuzz_pcap's read source, a memory stream. The
   driver proves the exit with that memory FILE still open. The notice above was written for fuzz_pcap's closer,
   lib/A/PcapClose.v, and names its asan-ubsan twin lib/B/PcapCloseB.v. This unit has neither, and no lib/B: its
   one closer is this file.

   Which part is where:
   - PROVED here, from this tree: H_STARTUP (lib/A/AB1n.v tfib_startup_T1), H_ALLOC_MALLOC (lib/A/AF0w.v
     pcap_amalloc_realizes), H_ALLOC_FREE (lib/A/AF0q.v pcap_afree_realizes), H_RT_MEMCPY (lib/A/AE31.v
     memcpy_icpt_realizes, by the two-line proof of the donor's lib/A/AD2m.v tfib_AICPY).
   - PROVED here, now that both files are in this tree: H_PROG_LIBCONTRACT_of, the program contract, by the slot's
     closed lemma lib/A/Prog/LLVMFuzzerTestOneInputClose.v LLVMFuzzerTestOneInput_closed; and H_DRIVER, the ASan
     driver, by lib/A/AD2o.v:64-70 link_H_DRIVER. LIBX_T is no longer a Section variable: it IS
     lib/A/Prog/LinkEntryA.v:82 tfib_lib_contract_xf_all_A (the same arguments, the run ceiling explicit here).
   The two names of lib/A/LinkDriver.v that H_DRIVER's statement uses are written out: its sink head link_drv_SK is
   link_asink_head (LinkDriver.v:25), and its conclusion drv_mainX_stmt (LinkDriver.v:56-68) is drv_mainA below.
   The discharge is done: LIBX_T is the definition it stood for, and each former hypothesis is a Lemma with the SAME
   statement, proved by the lemma named above. About, after the Section, lists nothing open. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_link Require Statements.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1h AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB01r AB12 AB1n AD2l AF0w AF0q AE31 AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require ZComplete.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import LinkAsanTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD2o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require LLVMFuzzerTestOneInputClose.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := LinkAsanTop.link_shape.

(* ===================================================================================================== *)
(* ASan image                                                                                              *)
(* ===================================================================================================== *)
Section asan.
Local Notation segs := OSSVerify.reac_pw.fuzz_link.images.Asan.M.loaded_segments.
Local Notation ph := OSSVerify.reac_pw.fuzz_link.images.Asan.M.phdrs.

(* START-UP. Rows 1-2: the hand-off states lib/A/AB01.v HS_tfib and the image table of the start-up certificate
   lib/A/AB12.v TFIB, by name: lib/A/AB1n.v states HS_ok at them and drv_mainA below names them. *)
(* Row 3 (727298f3: the launch's kernel record, exec file name and SIGPIPE disposition, and its premises).
   H_STARTUP: PROVED, lib/A/AB1n.v tfib_startup_T1 (TSEGS / TPH are Asan.M.loaded_segments / phdrs,
   lib/A/AB1h.v:18-19; HS_ok is AB1n.v:48). *)
Lemma H_STARTUP :
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
(uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
(kb : KernelBuild) (execfn : list byte) (sdef : bool),
valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
valid_sigmask (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
valid_launch (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
forall T : TSet, T [] ->
(forall h c, OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AB1n.HS_ok h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
(fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_link.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AB1n.tfib_startup_T1. Qed.

(* THE PARTS THE DRIVER CONSUMES. *)
(* Row 4. B := lib/A/AD2l.v:18 PcapB, the image's symbol and trace table. *)
Definition B : asyms := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB.
(* Row 5. RLO / RHI: bound inside the program contract's type (lib/A/Prog/LinkEntryA.v: PcapRelro.v PCAP_RLO /
   PCAP_RHI, link's measured read-only range), so no free row. *)
(* Row 6. KS: none (see the head of this file). *)
(* Row 7. SK := lib/A/AMemFile.v:611 link_asink_head (ofl_head 0x652308), the ASan image's sink head, passed by name
   in rows 11 and 13 (the driver's lib/A/LinkDriver.v:25 link_drv_SK is this definition). *)
(* Row 8. H_ALLOC_MALLOC: PROVED, lib/A/AF0w.v:53 pcap_amalloc_realizes. *)
Lemma H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AF0w.pcap_amalloc_realizes. Qed.
(* Row 9. H_ALLOC_FREE: PROVED, lib/A/AF0q.v:19 pcap_afree_realizes. *)
Lemma H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AF0q.pcap_afree_realizes. Qed.
(* Row 10. H_RT_MEMCPY: PROVED, lib/A/AE31.v:170 memcpy_icpt_realizes at PcapB with lib/A/AD2l.v:74 PcapB_syms, by
   the proof of the donor's lib/A/AD2m.v tfib_AICPY (the memcpy interceptor). *)
Lemma H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
  intros rc fx.
  pose proof (@OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AE31.memcpy_icpt_realizes fx rc
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB (AR_laws_ok tfibsegs OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB)
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB_syms) as H.
  unfold B, aintrin_realizes.
  rewrite (ts_code OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB_syms).
  exact H.
Qed.

(* Row 11. The program contract.
   Its type: LIBX_T IS lib/A/Prog/LinkEntryA.v:82 tfib_lib_contract_xf_all_A, with the same arguments
   (SK, B, the meter, XM_LIB, XN_LIB) and the run ceiling, implicit there, explicit here. PROVED, not a Section
   variable: LinkEntryA.v is in this tree. *)
Definition LIBX_T (rc : YM05.RunCeil) := @OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog.LinkEntryA.tfib_lib_contract_xf_all_A rc.
(* H_PROG_LIBCONTRACT_of: the closed slot top, the ASan build's entry contract of LLVMFuzzerTestOneInput at
   SK := link_asink_head, B := PcapB, the trivial meter and XM_LIB = XN_LIB = fun _ => 0, at every run ceiling:
   the conclusion of lib/A/Prog/LLVMFuzzerTestOneInputInst.v:90 LLVMFuzzerTestOneInput_aproof_A, with its walk
   (LF_WHOLE_A) discharged by the slot's closing. PROVED by lib/A/Prog/LLVMFuzzerTestOneInputClose.v
   LLVMFuzzerTestOneInput_closed, whose premise lib/A/AD2o.v:68 link_H_DRIVER takes. *)
Lemma H_PROG_LIBCONTRACT_of : forall rc : YM05.RunCeil,
  LIBX_T rc OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AMemFile.link_asink_head
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YCbp.ameter_triv (fun _ => 0) (fun _ => 0).
Proof. intros rc. exact (@OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog.LLVMFuzzerTestOneInputClose.LLVMFuzzerTestOneInput_closed rc). Qed.

(* The ASan driver's conclusion, lib/A/LinkDriver.v drv_mainX_stmt, written out at its own names (727298f3:
   the hand-off state of the run's own CONFIG_RSEQ flag, the stack invariant abstract, entry_launch_ok_va). *)
Definition drv_mainA (rc : YM05.RunCeil) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
  (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AB01r.HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AB12.TFIB YA02.LIMIT (YA02.TOP sp) SINV
  (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
    (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
    (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
    (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
    (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
  (forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
    (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
    (in_execfn inp) (in_sigpipe_default inp) E a = true ->
  FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw a) ->
  srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).

(* Row 13. H_DRIVER: the statement of lib/A/AD2o.v:64-69 link_H_DRIVER, with LinkDriver.v's link_drv_SK and
   drv_mainX_stmt written out (link_asink_head, drv_mainA). PROVED by that lemma. *)
Lemma H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc tfibsegs OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc tfibsegs OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc tfibsegs OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB
     OCpy (pc_wrap_memcpy (as_code OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB))) ->
  LIBX_T rc OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AMemFile.link_asink_head
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2l.PcapB
    OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable.YCbp.ameter_triv (fun _ => 0) (fun _ => 0) ->
  drv_mainA rc.
Proof. exact OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AD2o.link_H_DRIVER. Qed.

Section RC. Context {rc : YM05.RunCeil}.
(* The donor's DRV_MAINA, from H_DRIVER and the parts. *)
Lemma DRV_MAINA : drv_mainA rc.
Proof.
  exact (H_DRIVER rc (H_ALLOC_MALLOC rc) (H_ALLOC_FREE rc) (H_RT_MEMCPY rc) (H_PROG_LIBCONTRACT_of rc)).
Qed.
(* The donor's srealizesX_rc, the same proof: start-up, hand-off (AB1n.v HS_ok_open), driver, spec link. *)
Lemma link_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_link.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil.
  (* 727298f3: the input taken apart into its fields; [Run.valid_input] fixes the abort and terminal-SIGPIPE
     declarations, the address size and the channel reader, and says the kernel record is its own
     [recorded_kernel], so the input is [YA02.inp] at that record (as reac-pw/fuzz_role's A/RoleClose.v). *)
  pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
    in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
  subst ab mmu cr spt.
  rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)) (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.AB1n.HS_ok_open h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  assert (SP0 : forall E' M, YA02.SINV0 ph sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
    kern execfn spd OSSVerify.reac_pw.fuzz_link.images.Asan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
  { intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact segs]. }
  exact (DRV_MAINA sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) h ch E R FULL model _
    Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End RC.

(* The donor's ASAN_T_of_parts. *)
Theorem ASAN_T_of_parts : LinkAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp Hlau.
  change target_alloc_limit with YA02.LIMIT.
  exact (@link_srealizesX_rc
    (YM05.RunCeilOf (bv_unsigned sp) (OSSVerify.Proofs.reac_pw.fuzz_link.lib.ZComplete.valid_sp_window_for_ceil sp Hsp) YA02.LIMIT)
    sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan statements, given only the parts above. *)
Theorem link_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (LinkAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem link_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (LinkAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.
End asan.
(* After the Section: About lists the arguments of each statement. The discharge is complete, so nothing is open -
   LIBX_T is a Definition and H_PROG_LIBCONTRACT_of and H_DRIVER are Lemmas; Print Assumptions lists the axioms. *)
About DRV_MAINA.
About link_srealizesX_rc.
About ASAN_T_of_parts.
About link_asan_agrees_of_parts.
Print Assumptions link_asan_agrees_of_parts.
About link_asan_halts_of_parts.
Print Assumptions link_asan_halts_of_parts.
