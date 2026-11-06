(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v for libreac/fuzz_grant's ASan build: module paths changed, names TfibB -> GrantB and TfibSyms -> GrantSyms, the library shape grant_shape, and the contract of the target's entry function taken as one hypothesis instead of cgif's three function contracts, so that ACfi.v and the cgif function files are not needed. *)
(* Modified by Theorem Labs, 2026-10: adapted from lib/A/AGrantT.v for image B (fuzz_grant.asan-ubsan, bin fde52226dc48), with lib/A/ACfn.v's tfib_lib_contract_x restated at image B and lib/A/Prog/GrantLibX.v's grant_lib_x (a working branch 7d31e8f3534) proved from image B's entry contract: the core facts as named hypotheses. *)
(* THE BRIDGE FROM IMAGE B'S ENTRY TOP TO TFIB_TB. This file proves no function: it composes and walks nothing.

   TFIB_TB (lib/B/GrantTFIBB.v:19) is the premise from which lib/B/AsanUbsanTop.v:30-58 derives
   Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts. grant_TFIB_TB_of_lib below proves it from:
   (a) the PROGRAM side: image B's entry top, tb_LLVMFuzzerTestOneInput_spec at image B's sink and image
       (lib/B/Prog/GrantBClose.v tb_LLVMFuzzerTestOneInput_holds_B), taken here by its theorem (entry_top_B), with
       the closer's named runtime and image facts as named Section hypotheses (RT_*, IMG_*, and the three facts of B H_*_B;
       RT_LAWS is proved by rt_laws_B); no walk is open. grant_lib_x_B turns it into image B's form of
       the driver's slot, tfib_lib_contract_xB (the twin of lib/A/ACfn.v:62 tfib_lib_contract_x). The shapes match
       one to one; the step is PROVED (it is image A's grant_lib_x, lib/A/Prog/GrantLibX.v:120-164 on a working branch
       7d31e8f3534, with image B's apost_base post in place of image A's phase machine);
   (b) the CORE side: every core fact that image A's composition lib/A/AGrantT.v takes by `Let`, as one named
       Section hypothesis H_<A theorem> (or, where image A proves the fact here, the proof). The B core (the
       relocation of image A's core, lib/B/Y*.v) is in this tree; lib/B/GrantBTop.v:182-184 instantiates each of these
       at GrantB. A form that image A defines with its own image's data (tfibsegs, the runtime's
       addresses, the start-up certificate's tables) is a Section variable <A form>_B here, of the A form's type,
       so that the B core discharges it by its relocated definition; a form that is generic
       (lib/Reusable) is used directly at image B's segments. Every number this file states is image B's.

   ---- THE HYPOTHESES AND WHAT EACH TWINS (file:line on this branch; lib/A unless named) ----------------------------
   Parameters (Section variables), each a value the B core supplies:
     B : asyms                     the runtime's symbol record          AGrantT.v:35 (GrantB, AD2l.v:15)
     tfib_K_B : asink_syms         the sink's symbol record             AE2k.v:43 tfib_K
     xst_B                         the stdout state after k lines       AD1k.v:125 xst        (AGrantT.v:50)
     est_B                         the stderr state                     AD1k.v:86 est         (AGrantT.v:54)
   Statement forms (Section variables, each of the A form's exact type as `Check @<A form>` prints it on this branch,
   so the B core's relocated definition instantiates it as it is; GrantSyms_B, xst_frame_tfa_B, est_img_tfa_B and
   est_frame_tfa_B take no fx and rc, the others take fx and rc first):
     GrantSyms_B                   AF0m.v:532 GrantSyms
     aread_check_stmt_B            AD1i.v:19 aread_check_stmt
     xst_frame_tfa_B               AD1w.v:129 xst_frame_tfa
     printf_first_tfa_B            AD1w.v:154 printf_first_tfa
     printf_next_tfa_B             AD1w.v:161 printf_next_tfa
     est_img_tfa_B                 AD1x.v:37 est_img_tfa
     est_frame_tfa_B               AD1x.v:38 est_frame_tfa
     fwrite_site_tfa_B             AD1x.v:57 fwrite_site_tfa
     fprintf_s_site_tfa_B          AD1x.v:69 fprintf_s_site_tfa
     refused_site_tfa_B            AD1x.v:83 refused_site_tfa
     exit_site_tfa_B               AD1x.v:94 exit_site_tfa
   Stated here, at image B (Definitions, not variables):
     in_ro_tfa_B                   ACeg.v:48 in_ro_tfa, at image B's .data.rel.ro + .got [0x9d000, 0x9e3c8)
     tfib_lib_contract_xB          ACfn.v:36-72 (pre, post, slot), at image B's entry 0x80a3c, return 0x80938,
                                   empty buffer 0x5d7fe0 and sink head 0x5f9008
     tfib_lib_contract_x_allB      ACfn.v:138
   Hypotheses (Section hypotheses):
     RT_* / IMG_* / H_*_B          the premises of GrantBClose.tb_LLVMFuzzerTestOneInput_holds_B, as the closer
                                   names them (image A: the open program parts of GrantTop.v, a working branch
                                   7d31e8f3534); RT_MALLOC / RT_FREE at fx0 are also AF0w.v:45
                                   tfib_amalloc_realizes / AF0q.v:13 afree_realizes_closed (AGrantT.v:43-44)
     H_tfib_AIL                    AD1u.v:43 tfib_AIL (GrantLibX.v:216 AILG on a working branch)
     H_GrantB_syms                 AD2l.v:73 GrantB_syms                (AGrantT.v:36)
     H_tfib_AICPY                  AD2m.v:17 tfib_AICPY                 (AGrantT.v:45)
     H_tfib_ARDCHK                 AD2m.v:22 tfib_ARDCHK                (AGrantT.v:48)
     H_tfib_xst_frame              AD1k.v:133 tfib_xst_frame            (AGrantT.v:51)
     H_tfib_printf_first           AD1o.v:244 tfib_printf_first         (AGrantT.v:52)
     H_tfib_printf_next            AD1o.v:280 tfib_printf_next          (AGrantT.v:53)
     H_tfib_est_img                AD1k.v:114 tfib_est_img              (AGrantT.v:55)
     H_tfib_est_frame              AD1k.v:116 tfib_est_frame            (AGrantT.v:56)
     H_tfib_fwrite_site            AD1k.v:282 tfib_fwrite_site          (AGrantT.v:57)
     H_tfib_refused_site           AD1k.v:323 tfib_refused_site         (AGrantT.v:58)
     H_tfib_fprintf_open_site      AD1l.v:147 tfib_fprintf_open_site    (AGrantT.v:59), format 0x1d6e7
     H_tfib_fprintf_rderr_site     AD1l.v:152 tfib_fprintf_rderr_site   (AGrantT.v:60), format 0x1d6fc
     H_tfib_fprintf_usage_site     AD1l.v:157 tfib_fprintf_usage_site   (AGrantT.v:61), format 0x1583c
     H_tfib_exit_site              AD1j.v:123 tfib_exit_site            (AGrantT.v:62)
     H_tfib_srealizesX             AD1q.v:146-183 tfib_srealizesX (the driver and the start-up, Section d)
   Proved here, not hypotheses:
     LAWS    (AGrantT.v:42)        rt_laws_B: Reusable/YG0q.v:804 AR_laws_ok, which holds for every segment list
                                   and symbol record; it is also GrantBContracts.RT_LAWS at image B
     MT_FREE (AGrantT.v:49)        the meter that counts nothing (Reusable/YCbp.v ameter_triv)
     RO_IN   (AGrantT.v:47)        from in_ro_tfa_B's second case
     LIBX    (AGrantT.v:46)        grant_lib_x_B, from entry_top_B and H_tfib_AIL
     LAWS of the closer            RT_LAWS of GrantBClose.v is rt_laws_B, for every rc
   At fx0, image A's tfib_amalloc_realizes / afree_realizes_closed are the same Props as GrantBContracts.RT_MALLOC
   (amalloc_is_rt_malloc) and GrantBContracts.RT_FREE (afree_is_rt_free); this file names each once, as RT_MALLOC /
   RT_FREE.
   The start-up certificate's AR at main (AD1g.v:1428 tfib_ARm, AD1f.v:240 tfib_AR) and the init path are no Let
   of AGrantT.v: AD1q.v's driver takes them inside its own proof (tfib_AR at AD1p.v:109), so on image B they are part
   of H_tfib_srealizesX. The exit path (the module destructor, __do_fini) is inside tfib_exit_site's proof, so it is
   part of H_tfib_exit_site.

   IMAGE B'S NUMBERS, and where each is read:
     segments            AsanUbsan.M.loaded_segments (GrantTFIBB.v:18, GrantTop.v:15)
     entry 0x80a3c       LLVMFuzzerTestOneInput (GrantAddr.v grant_text + GrantList.v AF_LLVMFuzzerTestOneInput,
                         checked by a_llvmf_b_layer); return 0x80938 in target_run, empty buffer 0x5d7fe0
                         (oft_aligned_copy.empty), stack 32768, events 2000, live bytes 2 ^ 33 (GrantBContracts.v
                         RA_LLVMF_B, A_EMPTY_B, STK_LLVMFuzzerTestOneInput, EV_LIB_B, LIVE_LIB_B)
     RLO / RHI           0x9d000 / 0x9e3c8: .data.rel.ro begins at 0x9d000 and .got ends at 0x9e3c8 in image B's
                         section headers (image A: 0x9c1a0 / 0x9d568, the same two sections); they are also
                         GrantImg.v's grant_relro_lo / grant_relro_hi (rlo_rhi_b_layer)
     sink head 0x5f9008  ofl_head (GrantBClose.v:78 / :82, B_ofl_head / grantB_sink_head, used here by name)
     formats             0x1d6e7 "cli: cannot open %s\n", 0x1d6fc "cli: read error on %s\n", 0x1583c
                         "usage: %s INPUT\n" (image A: 0x1d7b0, 0x1d7c5, 0x15905), checked against image B's bytes
                         by b_fmt_check *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_grant.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YN3g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YE01 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import GrantShape.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require GrantTFIBB.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo GrantImg GrantBContracts.
(* The closing composition of image B's walks: its entry top tb_LLVMFuzzerTestOneInput_holds_B, its sink head
   grantB_sink_head (0x5f9008) and its named runtime and image facts. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantBClose.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require YCej.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- image B's sink head: GrantBClose.grantB_sink_head (ofl_head 0x5f9008), named explicitly below ------------ *)
#[local] Notation grantB_sink_head := GrantBClose.grantB_sink_head.
#[local] Existing Instance GrantBClose.grantB_sink_head.
(* What a bare `sink_head` resolves to in this file: image B's own head, the closer's. *)
Definition sk_probe_tfib : YI16.sink_head := _.
Lemma sk_probe_tfib_is_B : sk_probe_tfib = grantB_sink_head.
Proof. reflexivity. Qed.

(* ---- image B's numbers of the driver's slot ---------------------------------------------------------------------- *)
(* LLVMFuzzerTestOneInput, the entry the slot calls: the walk layer's own address of it. *)
Definition A_LLVMF_B : Z := 0x80a3c.
Lemma a_llvmf_b_layer : grant_val A_TEXT + AF_LLVMFuzzerTestOneInput = A_LLVMF_B.
Proof. vm_compute. reflexivity. Qed.
(* The read-only range the slot is stated over: image B's .data.rel.ro and .got. *)
Definition RLO_B : Z := 0x9d000.
Definition RHI_B : Z := 0x9e3c8.
Lemma rlo_rhi_b_layer : RLO_B = grant_relro_lo /\ RHI_B = grant_relro_hi.
Proof. split; reflexivity. Qed.
(* The meter the walk carries: it counts nothing. *)
Definition XL0_B : Z -> Z := fun _ => 0.
(* The three format strings the driver passes to fprintf (sites FPO, FPR, FPU of AGrantT.v:59-61). *)
Definition FMT_OPEN_B : Z := 0x1d6e7.
Definition FMT_RDERR_B : Z := 0x1d6fc.
Definition FMT_USAGE_B : Z := 0x1583c.
Definition romB_str (a : Z) (n : nat) : list (option Z) := map (fun j => romB8 (a + Z.of_nat j)) (seq 0 n).
Definition cstrZ (bs : list byte) : list (option Z) := map (fun b : byte => Some (bv_unsigned b)) (bs ++ [Z_to_bv 8 0]).
Lemma b_fmt_check :
  romB_str FMT_OPEN_B 21 = cstrZ (YO05.strB "cli: cannot open %s"%string ++ YO05.nlB) /\
  romB_str FMT_RDERR_B 23 = cstrZ (YO05.strB "cli: read error on %s"%string ++ YO05.nlB) /\
  romB_str FMT_USAGE_B 17 = cstrZ (YO05.strB "usage: %s INPUT"%string ++ YO05.nlB).
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The read-only set of image B the driver's core speaks of (ACeg.v:48 in_ro_tfa at image B): the non-writable
   PT_LOADs, and image B's .data.rel.ro and .got. *)
Definition in_ro_tfa_B (a : Z) : Prop :=
(exists s, In s grantsegsB0 /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (0x9d000 <= a < 0x9e3c8).

(* ---- the driver's slot at image B (ACfn.v:36-72 and :138) --------------------------------------------------------- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable tfib_K_B : asink_syms.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Local Notation segs := grantsegsB0.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition tfib_lib_pre_xB (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B STK_LLVMFuzzerTestOneInput ly S W regs mem md [] /\
raZ regs = RA_LLVMF_B /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY_B) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB_B <= EV_MAX /\ blocks_bytes S + LIVE_LIB_B <= LIVE_MAX /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
asink_none segs tfib_K_B (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K_B ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).
Definition tfib_lib_post_xB (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B STK_LLVMFuzzerTestOneInput (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB_B /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K_B (rd W' mem') md' /\
ameta_inv segs tfib_K_B ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tfib_lib_contract_xB : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_xB regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF_B regs' mem' md' /\
tfib_lib_post_xB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF_B regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition tfib_lib_contract_x_allB {rc : YM05.RunCeil} {LS : lib_shape} (tfib_K_B : asink_syms) (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_xB fx rc LS tfib_K_B B MT XM_LIB XN_LIB RLO RHI.

(* ---- (a) the program side: the slot from image B's entry contract --------------------------------------------------
   Image A's grant_lib_x (lib/A/Prog/GrantLibX.v:120-164, a working branch 7d31e8f3534) with image B's entry contract in
   place of image A's phase machine. Premise by premise, the slot's pre-condition holds every premise of
   tb_LLVMFuzzerTestOneInput_spec (GrantBContracts.v tb_LLVMFuzzerTestOneInput_spec): the read-only view at
   [RLO_B, RHI_B) is the walk layer's view at [pa_relro_lo, pa_relro_hi), the same range. Conjunct by conjunct, the
   contract's post (apost_base: back at the caller's ra, a journal with no footprint and no frame of its own,
   a0 = 0, the blocks a permutation, the input bytes kept) gives the slot's post: the journal with the sink token
   (a journal that opens no sink carries over), the file descriptors and the file system kept (aos_step with no
   sink), and the sink and allocator-metadata invariants kept (asink_img_laws, H_tfib_AIL). *)
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma grant_inFP_nil_B : forall a, ~ inFP [] a.
Proof. intros a (r & Hin & _). exact Hin. Qed.
(* A journal that opened no sink carries over to any token list (GrantLibX.v:54 grant_journal_fp). *)
Lemma grant_journal_fp_B : forall segs B STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
    (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
  split; [intros q m i H1 H2 Hi _; apply (F2 q m i H1 H2 Hi); apply grant_inFP_nil_B|].
  split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed;
          intros Ho; exact (sink_closed_nil Ho)|].
  split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply grant_inFP_nil_B|].
  split; [intros q m i H1 H2 Hi; exfalso; exact (grant_inFP_nil_B _ (Hgone q m i H1 H2 Hi))|].
  split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
(* What a journal that opened no sink leaves of the file system (GrantLibX.v:72 grant_journal_io). *)
Lemma grant_journal_io_B : forall segs B STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
  intros segs B STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ.
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
  unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.

Variable tfib_K_B : asink_syms.
Variable B : asyms.
(* The entry top at this fx and rc (GrantBClose.v:428). *)
Hypothesis ENTRY : tb_LLVMFuzzerTestOneInput_spec (SK := grantB_sink_head) (PI := @PI_grant rc) B.
(* The sink's laws at image B (AD1u.v:43 tfib_AIL). *)
Hypothesis AIL : asink_img_laws (SK := grantB_sink_head) grantsegsB0 B tfib_K_B.

Theorem grant_lib_x_B : tfib_lib_contract_xB (LS := grant_shape) tfib_K_B B ameter_triv XL0_B XL0_B RLO_B RHI_B.
Proof.
  intros ly S W regs mem md p n pl M K HAI HPRE HK.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS &
                    HSNK & HFD & HSORT & HAM & HMOK).
  assert (HRO : arodata_okP (pa_segs (PAImg := @PI_grant rc)) (pa_relro_lo (PAImg := @PI_grant rc))
                  (pa_relro_hi (PAImg := @PI_grant rc)) B (aview (pa_segs (PAImg := @PI_grant rc)) (w_H W) mem)).
  { intros a Ha. exact (HROS a Ha). }
  pose proof (ENTRY ly S W regs mem md p n pl HFN Hra Hp Hn Hpn Hnpl HPL Hfr Hev Hlive HRO) as HSR.
  change (LIBK pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
  rewrite <- a_llvmf_b_layer.
  apply (HSR HAI).
  intros W' c' Hwle HAI' HPOST.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJ & HPR & Ha0 & Hfr' & HPerm & HFkeep).
  destruct (grant_journal_io_B grantsegsB0 B STK_LLVMFuzzerTestOneInput (spZ regs) ly S W mem md [] ly' S' W' mem' md'
              EV_LIB_B HJ) as [Efds Efs].
  apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
  exists ly', S', regs', mem', md', EV_LIB_B.
  split.
  { rewrite Ec. unfold cfg_at. f_equal. f_equal.
    unfold w64. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold tfib_lib_post_xB. cbn [ll_fs ll_ret ll_out].
  split; [exact (grant_journal_fp_B grantsegsB0 B STK_LLVMFuzzerTestOneInput (spZ regs) [sink_token] ly S W mem md []
                   ly' S' W' mem' md' EV_LIB_B HJ)|].
  split; [lia|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
  split; [intros fd; rewrite Efds; reflexivity|].
  split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
  split; [exact (asink_none_kept grantsegsB0 B tfib_K_B AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ sink_closed_nil HSNK)|].
  split; [exact (ameta_inv_kept grantsegsB0 B tfib_K_B AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
  split; [exact I|].
  intros i Hi. exact (HFkeep i Hi).
Qed.
End j.

(* ---- LAWS (AGrantT.v:42): AR_laws holds for every segment list and symbol record (Reusable/YG0q.v:804); at image B
   it is also GrantBContracts.RT_LAWS, which GrantBClose.v takes as a hypothesis; entry_top_B gives it this proof. *)
Lemma rt_laws_B : forall (rc : YM05.RunCeil) (B : asyms), GrantBContracts.RT_LAWS (rc := rc) (PI := @PI_grant rc) B.
Proof. intros rc B. exact (AR_laws_ok _ B). Qed.

(* ---- (b) the driver and the start-up over the slot (AGrantT.v Section b, AD1q.v Section d) ------------------------ *)
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance grant_shape.
Lemma valid_sp_windowB : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
(* At fx0, image A's two core facts tfib_amalloc_realizes and afree_realizes_closed are the same Props as the closer's
   RT_MALLOC and RT_FREE. *)
Lemma amalloc_is_rt_malloc : forall (rc : YM05.RunCeil) (B : asyms),
  amalloc_realizes (fx := YK11.fx0) (rc := rc) grantsegsB0 B = GrantBContracts.RT_MALLOC (rc := rc) (PI := @PI_grant rc) B.
Proof. reflexivity. Qed.
Lemma afree_is_rt_free : forall (rc : YM05.RunCeil) (B : asyms),
  afree_realizes (fx := YK11.fx0) (rc := rc) grantsegsB0 B = GrantBContracts.RT_FREE (rc := rc) (PI := @PI_grant rc) B.
Proof. reflexivity. Qed.

Section b.
(* -- the values the B core supplies -- *)
Variable B : asyms.
Variable tfib_K_B : asink_syms.
Variable xst_B : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable est_B : (word -> bool) -> (word -> option byte) -> Prop.
(* -- the B core's statement forms -- *)
Variable GrantSyms_B : asyms -> Prop.
Variable aread_check_stmt_B : YK11.FPState -> YM05.RunCeil -> asyms -> Prop.
Variable xst_frame_tfa_B : (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable printf_first_tfa_B : YK11.FPState -> YM05.RunCeil -> asyms -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable printf_next_tfa_B : YK11.FPState -> YM05.RunCeil -> asyms -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable est_img_tfa_B : ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable est_frame_tfa_B : ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable fwrite_site_tfa_B : YK11.FPState -> YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable fprintf_s_site_tfa_B : YK11.FPState -> YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) ->
  Z -> list byte -> list byte -> Prop.
Variable refused_site_tfa_B : YK11.FPState -> YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable exit_site_tfa_B : YK11.FPState -> YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) ->
  (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.

(* -- (a): the program side -- *)
(* The entry top is GrantBClose.tb_LLVMFuzzerTestOneInput_holds_B (lib/B/Prog/GrantBClose.v), taken by its theorem at every
   run ceiling and float state (tfib_lib_contract_x_allB quantifies the float state). Its premises are the closer's
   named facts and open walks, restated here once each, at every rc (and fx where the fact depends on it), with the
   closer's names (no walk is open). RT_LAWS is not among them: rt_laws_B proves it for every B. RT_MALLOC and RT_FREE are, at fx0, the
   same Props as image A's core facts tfib_amalloc_realizes (AF0w.v:45) and afree_realizes_closed (AF0q.v:13)
   (amalloc_is_rt_malloc, afree_is_rt_free), so they serve both and are named once. *)
(* RT_PALIB: PALib: the walk layer's library facts. *)
Hypothesis RT_PALIB : forall rc : YM05.RunCeil, GrantBContracts.RT_PALIB (rc := rc) (PI := @PI_grant rc) B.
(* RT_PALIBF: PALibF: the side-stack library facts. *)
Hypothesis RT_PALIBF : forall rc : YM05.RunCeil, GrantBContracts.RT_PALIBF (rc := rc) (PI := @PI_grant rc) B.
(* RT_ML: model_laws of the trace universe. *)
Hypothesis RT_ML : GrantBContracts.RT_ML B.
(* RT_SMP: stack_malloc_progressP. *)
Hypothesis RT_SMP : GrantBContracts.RT_SMP B.
(* RT_ASF: astack_free_law. *)
Hypothesis RT_ASF : forall rc : YM05.RunCeil, GrantBContracts.RT_ASF (rc := rc) (PI := @PI_grant rc) B.
(* RT_FFL: frame_flag_lawP. *)
Hypothesis RT_FFL : forall rc : YM05.RunCeil, GrantBContracts.RT_FFL (rc := rc) (PI := @PI_grant rc) B.
(* RT_TP_FS: the fake stack's thread-local pointer. *)
Hypothesis RT_TP_FS : forall rc : YM05.RunCeil, GrantBContracts.RT_TP_FS (rc := rc) (PI := @PI_grant rc) B.
(* RT_MALLOC: the malloc wrapper's jump 0x52edc. *)
Hypothesis RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_MALLOC (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_FREE: the free wrapper's jump 0x52ed8. *)
Hypothesis RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_FREE (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_MEMCPY: __asan_memcpy 0x51b88. *)
Hypothesis RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_MEMCPY (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_MEMSET: __asan_memset 0x52024. *)
Hypothesis RT_MEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_MEMSET (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_BCMP: the bcmp wrapper's jump 0x424d0. *)
Hypothesis RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_BCMP (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_SM0: __asan_stack_malloc_0 0x3cf4c. *)
Hypothesis RT_SM0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SM (fx := fx) (rc := rc) (PI := @PI_grant rc) B 0.
(* RT_SM1: __asan_stack_malloc_1 0x3d0c0. *)
Hypothesis RT_SM1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SM (fx := fx) (rc := rc) (PI := @PI_grant rc) B 1.
(* RT_SM2: __asan_stack_malloc_2 0x3d250. *)
Hypothesis RT_SM2 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SM (fx := fx) (rc := rc) (PI := @PI_grant rc) B 2.
(* RT_SM4: __asan_stack_malloc_4 0x3d3ec. *)
Hypothesis RT_SM4 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SM (fx := fx) (rc := rc) (PI := @PI_grant rc) B 4.
(* RT_SM6: __asan_stack_malloc_6 0x3d5b8. *)
Hypothesis RT_SM6 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SM (fx := fx) (rc := rc) (PI := @PI_grant rc) B 6.
(* RT_SF6: __asan_stack_free_6 0x3d754. *)
Hypothesis RT_SF6 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SF6 (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_SS00: __asan_set_shadow_00 0x54a48. *)
Hypothesis RT_SS00 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SS00 (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_SSF5: __asan_set_shadow_f5 0x54b50. *)
Hypothesis RT_SSF5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SSF5 (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_SSF8: __asan_set_shadow_f8 0x54b68. *)
Hypothesis RT_SSF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), GrantBContracts.RT_SSF8 (fx := fx) (rc := rc) (PI := @PI_grant rc) B.
(* RT_IMGSH: the shadow of image B's read range is mapped. *)
Hypothesis RT_IMGSH : forall rc : YM05.RunCeil, GrantBContracts.RT_IMGSH (rc := rc) (PI := @PI_grant rc) B.
(* RT_GLOBS: image B's 13 registered globals are marked. *)
Hypothesis RT_GLOBS : forall rc : YM05.RunCeil, GrantBContracts.RT_GLOBS (rc := rc) (PI := @PI_grant rc) B.
(* IMG_CTRL_ROW: the row B_ROW 0x9d4d0: aligned, placed, in as_zero_shadow, apart. *)
Hypothesis IMG_CTRL_ROW : forall rc : YM05.RunCeil, GrantBContracts.IMG_CTRL_ROW (rc := rc) (PI := @PI_grant rc) B.
(* IMG_CTRL_ROW_FIN: the row's bytes ctrl_finish reads. *)
Hypothesis IMG_CTRL_ROW_FIN : forall rc : YM05.RunCeil, GrantBContracts.IMG_CTRL_ROW_FIN (rc := rc) (PI := @PI_grant rc) B.
(* IMG_CTRL_LAY_JT: entry 2 of ctrl_lay_block's jump table 0x21034. *)
Hypothesis IMG_CTRL_LAY_JT : forall rc : YM05.RunCeil, GrantBContracts.IMG_CTRL_LAY_JT (rc := rc) (PI := @PI_grant rc) B.
(* IMG_CTRL_STAMP_TM: the last conjunct of IMG_CTRL_STAMP: the template TM the row names. *)
Hypothesis IMG_CTRL_STAMP_TM : forall rc : YM05.RunCeil, exists TM, GrantBContracts.tmpl_place (rc := rc) (PI := @PI_grant rc) B TM /\
    GrantBContracts.IMG_CTRL_ROW_LAY (rc := rc) (PI := @PI_grant rc) B TM /\ GrantBContracts.IMG_CTRL_TMPL (rc := rc) (PI := @PI_grant rc) B TM.
(* IMG_BGS_ROWS: the three row tables reac_ctrl_build_grant_sweep copies. *)
Hypothesis IMG_BGS_ROWS : forall rc : YM05.RunCeil, GrantBContracts.IMG_BGS_ROWS (rc := rc) (PI := @PI_grant rc) B.
(* IMG_reac_ctrl_parse: .str.4 (object 15): its entry, place and six 0xff bytes. *)
Hypothesis IMG_reac_ctrl_parse : forall rc : YM05.RunCeil, GrantBContracts.IMG_reac_ctrl_parse (rc := rc) (PI := @PI_grant rc) B.
(* IMG_check_groupa: __const.check_groupa.frame (object 9). *)
Hypothesis IMG_check_groupa : forall rc : YM05.RunCeil, GrantBContracts.IMG_check_groupa (rc := rc) (PI := @PI_grant rc) B.
(* H_universe_B, H_malloc_ra0_B, H_free_ra0_B: the three facts of B from which GrantBClose.v proves IMG_LLVMF_TRACES
   (GrantBTraces.img_llvmf_traces_grant); A: lib/A/AD2l.v:38, lib/A/AF0l.v:10, :11. Each closes by reflexivity at
   image B's concrete asyms record (lib/B/GrantBCloseInst.v:366, :369, :372; given at lib/B/GrantBTop.v:227-229). *)
Hypothesis H_universe_B : as_universe B = YCej.Tfib_universe.
Hypothesis H_malloc_ra0_B : pc_malloc_ra0 (as_code B) = 0x53178.
Hypothesis H_free_ra0_B : pc_free_ra0 (as_code B) = 0x53018.
(* IMG_LLVMF_SWEEP: the four read-only tables the entry reads. *)
Hypothesis IMG_LLVMF_SWEEP : forall rc : YM05.RunCeil, GrantBContracts.IMG_LLVMF_SWEEP (rc := rc) (PI := @PI_grant rc) B.
(* IMG_NEXT_DIV3: reac_headamp_tx_next's multiplier 0xAAAAAAAAAAAAAAAB at object 34 (0x10320); b_next_div3_check checks its bytes on image B, the image-view form stays a premise like the other IMG_ facts. *)
Hypothesis IMG_NEXT_DIV3 : forall rc : YM05.RunCeil, GrantBContracts.IMG_NEXT_DIV3 (rc := rc) (PI := @PI_grant rc) B.
(* H_tfib_AIL: the sink's laws at image B (AD1u.v:43 tfib_AIL; GrantLibX.v:216 AILG on a working branch). *)
Hypothesis H_tfib_AIL : asink_img_laws (SK := grantB_sink_head) grantsegsB0 B tfib_K_B.

(* The entry top at every rc and fx, from the closer's theorem and the facts above. *)
Lemma entry_top_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  tb_LLVMFuzzerTestOneInput_spec (fx := fx) (rc := rc) (SK := grantB_sink_head) (PI := @PI_grant rc) B.
Proof.
  intros rc fx. eapply (@GrantBClose.tb_LLVMFuzzerTestOneInput_holds_B fx rc B).
  all: first
    [ exact (rt_laws_B rc B)
    | match goal with H : forall (_ : YM05.RunCeil) (_ : YK11.FPState), _ |- _ => exact (H rc fx) end
    | match goal with H : forall _ : YM05.RunCeil, _ |- _ => exact (H rc) end
    | assumption ].
Qed.

(* -- (b): the core facts, one named hypothesis each -- *)
(* H_GrantB_syms: the symbol record is image B's runtime (AD2l.v:73 GrantB_syms; AGrantT.v:36 HB). *)
Hypothesis H_GrantB_syms : GrantSyms_B B.
(* The malloc and free wrappers (AF0w.v:45, AF0q.v:13; AGrantT.v:43-44) are RT_MALLOC / RT_FREE above, at fx0. *)
(* H_tfib_AICPY: the memcpy wrapper (AD2m.v:17; AGrantT.v:45). *)
Hypothesis H_tfib_AICPY : forall rc : YM05.RunCeil,
  aintrin_realizes (fx := YK11.fx0) (rc := rc) grantsegsB0 B OCpy (pc_wrap_memcpy (as_code B)).
(* H_tfib_ARDCHK: the read interceptor's check (AD2m.v:22; AGrantT.v:48). *)
Hypothesis H_tfib_ARDCHK : forall rc : YM05.RunCeil, aread_check_stmt_B YK11.fx0 rc B.
(* H_tfib_xst_frame (AD1k.v:133; AGrantT.v:51). *)
Hypothesis H_tfib_xst_frame : xst_frame_tfa_B xst_B.
(* H_tfib_printf_first / H_tfib_printf_next: the printf site, first and next line (AD1o.v:244, :280; AGrantT.v:52-53). *)
Hypothesis H_tfib_printf_first : forall rc : YM05.RunCeil, printf_first_tfa_B YK11.fx0 rc B xst_B.
Hypothesis H_tfib_printf_next : forall rc : YM05.RunCeil, printf_next_tfa_B YK11.fx0 rc B xst_B.
(* H_tfib_est_img / H_tfib_est_frame: the stderr state (AD1k.v:114, :116; AGrantT.v:55-56). *)
Hypothesis H_tfib_est_img : est_img_tfa_B est_B.
Hypothesis H_tfib_est_frame : est_frame_tfa_B est_B.
(* H_tfib_fwrite_site / H_tfib_refused_site (AD1k.v:282, :323; AGrantT.v:57-58). *)
Hypothesis H_tfib_fwrite_site : forall rc : YM05.RunCeil, fwrite_site_tfa_B YK11.fx0 rc B est_B.
Hypothesis H_tfib_refused_site : forall rc : YM05.RunCeil, refused_site_tfa_B YK11.fx0 rc B est_B.
(* H_tfib_fprintf_*_site: the three fprintf sites at image B's format strings (AD1l.v:147, :152, :157; AGrantT.v:59-61). *)
Hypothesis H_tfib_fprintf_open_site : forall rc : YM05.RunCeil,
  fprintf_s_site_tfa_B YK11.fx0 rc B est_B FMT_OPEN_B (YO05.strB "cli: cannot open "%string) YO05.nlB.
Hypothesis H_tfib_fprintf_rderr_site : forall rc : YM05.RunCeil,
  fprintf_s_site_tfa_B YK11.fx0 rc B est_B FMT_RDERR_B (YO05.strB "cli: read error on "%string) YO05.nlB.
Hypothesis H_tfib_fprintf_usage_site : forall rc : YM05.RunCeil,
  fprintf_s_site_tfa_B YK11.fx0 rc B est_B FMT_USAGE_B (YO05.strB "usage: "%string) (YO05.strB " INPUT"%string ++ YO05.nlB).
(* H_tfib_exit_site: the exit path (AD1j.v:123; AGrantT.v:62). *)
Hypothesis H_tfib_exit_site : forall rc : YM05.RunCeil, exit_site_tfa_B YK11.fx0 rc B est_B xst_B.
(* H_tfib_srealizesX: the driver and the start-up over the slot (AD1q.v:146-183 tfib_srealizesX), at image B: its
   segments, start pc and program headers, the B core's forms, the slot tfib_lib_contract_x_allB and image B's
   format strings. Its binders are AD1q.v Section d's, in order. *)
Hypothesis H_tfib_srealizesX : forall (rc : YM05.RunCeil),
  GrantSyms_B B ->
  amalloc_realizes (fx := YK11.fx0) (rc := rc) grantsegsB0 B ->
  afree_realizes (fx := YK11.fx0) (rc := rc) grantsegsB0 B ->
  aintrin_realizes (fx := YK11.fx0) (rc := rc) grantsegsB0 B OCpy (pc_wrap_memcpy (as_code B)) ->
  aread_check_stmt_B YK11.fx0 rc B ->
  forall (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z),
  (forall S m, mo_ok MT S m) ->
  (forall a, RLO <= a < RHI -> in_ro_tfa_B a) ->
  tfib_lib_contract_x_allB (rc := rc) (LS := grant_shape) tfib_K_B B MT XM_LIB XN_LIB RLO RHI ->
  forall xst : nat -> (word -> bool) -> (word -> option byte) -> Prop,
  xst_frame_tfa_B xst -> printf_first_tfa_B YK11.fx0 rc B xst -> printf_next_tfa_B YK11.fx0 rc B xst ->
  forall est : (word -> bool) -> (word -> option byte) -> Prop,
  est_img_tfa_B est -> est_frame_tfa_B est ->
  fwrite_site_tfa_B YK11.fx0 rc B est -> refused_site_tfa_B YK11.fx0 rc B est ->
  fprintf_s_site_tfa_B YK11.fx0 rc B est FMT_OPEN_B (YO05.strB "cli: cannot open "%string) YO05.nlB ->
  fprintf_s_site_tfa_B YK11.fx0 rc B est FMT_RDERR_B (YO05.strB "cli: read error on "%string) YO05.nlB ->
  fprintf_s_site_tfa_B YK11.fx0 rc B est FMT_USAGE_B (YO05.strB "usage: "%string) (YO05.strB " INPUT"%string ++ YO05.nlB) ->
  exit_site_tfa_B YK11.fx0 rc B est xst ->
  forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk grantsegsB0 brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  srealizes grantsegsB0 (init_config grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX inp).

Section RC. Context {rc : YM05.RunCeil}.
(* LIBX (AGrantT.v:46): the slot, from the entry top (part (a)). *)
Let LIBX : tfib_lib_contract_x_allB (rc := rc) (LS := grant_shape) tfib_K_B B ameter_triv XL0_B XL0_B RLO_B RHI_B :=
  fun fx => grant_lib_x_B (fx := fx) (rc := rc) tfib_K_B B (entry_top_B rc fx) H_tfib_AIL.
(* MT_FREE (AGrantT.v:49). *)
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
(* RO_IN (AGrantT.v:47). *)
Let RO_IN : forall a, RLO_B <= a < RHI_B -> in_ro_tfa_B a := fun a H => or_intror H.
Lemma grant_srealizesX_rc_B : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk grantsegsB0 brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes grantsegsB0 (init_config grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
exact (H_tfib_srealizesX rc H_GrantB_syms (RT_MALLOC rc YK11.fx0) (RT_FREE rc YK11.fx0) (H_tfib_AICPY rc)
  (H_tfib_ARDCHK rc) ameter_triv XL0_B XL0_B RLO_B RHI_B MT_FREE RO_IN LIBX
  xst_B H_tfib_xst_frame (H_tfib_printf_first rc) (H_tfib_printf_next rc)
  est_B H_tfib_est_img H_tfib_est_frame (H_tfib_fwrite_site rc) (H_tfib_refused_site rc)
  (H_tfib_fprintf_open_site rc) (H_tfib_fprintf_rderr_site rc) (H_tfib_fprintf_usage_site rc) (H_tfib_exit_site rc)
  sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem grant_srealizesX_top_B : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk grantsegsB0 brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes grantsegsB0 (init_config grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@grant_srealizesX_rc_B (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowB sp Hsp)) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
Theorem grant_TFIB_TB_of_lib : GrantTFIBB.TFIB_TB.
Proof.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
exact (grant_srealizesX_top_B sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp).
Qed.

(* Inside the Section, Print Assumptions lists what TFIB_TB rests on here: the Section variables (the values and
   forms the B core supplies, the closer's RT_* / IMG_* facts and H_*_B facts, H_tfib_AIL and the core facts
   H_tfib_<name>) next to the axioms
   toolchain/allowed-axioms.txt allows. *)
Print Assumptions grant_TFIB_TB_of_lib.
End b.

(* After the Section, the closed form: every Section variable is a premise of its type, and Print Assumptions lists
   only the axioms. *)
Check grant_TFIB_TB_of_lib.
Print Assumptions grant_TFIB_TB_of_lib.
