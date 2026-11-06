(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 167 of its 196 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacBoxName.v, with its module paths and module names changed; 545 of its 601 lines of code are new or changed and 140 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntryInv.v, with its module paths changed; 140 of its 173 lines of code are new or changed and 568 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCbq.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.

Definition exit_post_fp_stmt (FP : list (Z * Z)) : Prop :=
  forall (fq : YK11.FPState) (cx : dcx) ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' k,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k ->
  k <= EV_LIB ->
  Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) ->
  aregs_preserved (c_regs cx) regs' -> getr regs' 10 = w64 0 ->
  tLLVMFuzzerTestOneInput_post B MT XN_LIB tfib_K (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    (c_p cx) (c_n cx) (c_M cx) W'
    (mkCfg (YK11.mkst (fx := fq) regs' (getr (c_regs cx) 1) mem' (YK11.seg_rom SEGS)) md').

Lemma ajournal_of_closed : forall (FP FP' : list (Z * Z)) STK sp0 ly S (W : world SEGS) mem md own
    ly' S' (W' : world SEGS) mem' md' k,
  (forall a, ~ inFP FP a) ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  ajournal SEGS B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros FP FP' STK sp0 ly S W mem md own ly' S' W' mem' md' k HN
    (HAR & Hly & Hsecs & Hwle & Hos & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
  assert (Hcl : ~ YI16.sink_open_fp FP) by (intros Ho; exact (HN 0 Ho)).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply aos_step_mono; [|exact Hos]; intros Ho; exfalso; exact (Hcl Ho)|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
  split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply HN|].
  split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; exact Hcl|].
  split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply HN|].
  split; [intros p n i H1 H2 Hi; exfalso; exact (HN (p + i) (Hgone p n i H1 H2 Hi))|].
  split; [exact Hpres|]. split; [exact Hstk|]. split; [exact F5 | exact HQT].
Qed.

Theorem exit_post_closed : forall FP : list (Z * Z), (forall a, ~ inFP FP a) -> exit_post_fp_stmt FP.
Proof.
  intros FP HN fq cx ly' S' W' regs' mem' md' k HF0 HBASE HJ Hk HPerm HPR Ha0.
  assert (Hcl : ~ YI16.sink_open_fp FP) by (intros Ho; exact (HN 0 Ho)).
  destruct HBASE as (HPRE & _).
  destruct HPRE as (HAR0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK0 & HFD0 & HSORT0 &
    HAM0 & HMOK).
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed FP (c_md cx) md' Hcl Hos) as (Efd & Efsys & Eproc & Eio).
  unfold tLLVMFuzzerTestOneInput_post. exists fq. split; [exact HF0|]. unfold apost_base.
  exists fq, ly', S', regs', mem', md'.
  split; [reflexivity|]. split; [intros; reflexivity|]. split; [left; reflexivity|].
  split; [eapply ajournal_of_closed; [exact HN | eapply ajournal_mono_k; [exact HJ | exact Hk]]|].
  split; [exact HPR|].
  split; [exact Ha0|].
  split; [exact HPerm|].
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efsys; reflexivity|].
  split; [exact (asink_none_kept SEGS B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hcl HSNK0)|].
  split; [exact (ameta_inv_kept SEGS B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM0)|].
  split; [rewrite MT_TRIV; exact I|].
  intros i Hi.
  destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (F2 (c_p cx) (c_n cx) i Hpin).
  - eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpin].
  - unfold req_size. destruct (Z.eqb_spec (c_n cx) 0) as [Heq0|Hne0];
      [exfalso; clear - Hnpos Heq0; lia | exact Hi].
  - apply HN.
Qed.

Theorem exit_post_nil : exit_post_fp_stmt [].
Proof. apply exit_post_closed. exact inFP_nil. Qed.

Lemma sink_lookup_none : forall (fds : list (word * FdEntry)) fd off,
  Namei.fd_names_path fds YI16.sink_path = false ->
  fd_lookup fds fd = Some (FdFileW YI16.sink_path off) -> False.
Proof.
  induction fds as [|[k e0] r IH]; intros fd off Hs Hl; [discriminate Hl|].
  cbn [fd_lookup] in Hl.
  assert (Hr : Namei.fd_names_path r YI16.sink_path = false).
  { cbn [Namei.fd_names_path] in Hs. destruct e0; try exact Hs;
      apply Bool.orb_false_iff in Hs; exact (proj2 Hs). }
  destruct (bv_eqb k fd); [|exact (IH fd off Hr Hl)].
  injection Hl as ->. cbn [Namei.fd_names_path] in Hs.
  apply Bool.orb_false_iff in Hs. destruct Hs as [Hs _]. rewrite Fs.path_eqb_refl in Hs. discriminate Hs.
Qed.

Lemma fds_restored_of_asink : forall md md',
  YI16.fds_rel (m_fds md) (m_fds md') ->
  Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
  Namei.fd_names_path (m_fds md') YI16.sink_path = false ->
  forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd.
Proof.
  intros md md' HR Hn Hn' fd. destruct (HR fd) as [E | [S1 S2]]; [exact E|].
  destruct S1 as [E1 | (o1 & E1)]; destruct S2 as [E2 | (o2 & E2)].
  - rewrite E1, E2. reflexivity.
  - exfalso. exact (sink_lookup_none (m_fds md') fd o2 Hn' E2).
  - exfalso. exact (sink_lookup_none (m_fds md) fd o1 Hn E1).
  - exfalso. exact (sink_lookup_none (m_fds md) fd o1 Hn E1).
Qed.

Definition exit_post_carry_stmt : Prop :=
  forall (fq : YK11.FPState) (cx : dcx) ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' k,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) DFP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k ->
  k <= EV_LIB ->
  Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) ->
  aregs_preserved (c_regs cx) regs' -> getr regs' 10 = w64 0 ->
  asink_none SEGS tfib_K (rd W' mem') md' ->
  m_fs md' = m_fs (c_md cx) ->
  tLLVMFuzzerTestOneInput_post B MT XN_LIB tfib_K (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    (c_p cx) (c_n cx) (c_M cx) W'
    (mkCfg (YK11.mkst (fx := fq) regs' (getr (c_regs cx) 1) mem' (YK11.seg_rom SEGS)) md').

Theorem exit_post_carry : AR_laws SEGS B -> exit_post_carry_stmt.
Proof.
  intros LAWS fq cx ly' S' W' regs' mem' md' k HF0 HBASE HJ Hk HPerm HPR Ha0 HSNK' Efs.
  assert (HnFP : forall a, 4096 <= a -> ~ inFP DFP a).
  { intros a Ha (r & Hin & Hr). unfold DFP in Hin. cbn [In] in Hin.
    destruct Hin as [<-|[]]. unfold YI16.sink_token in Hr. cbn [fst snd] in Hr. clear - Ha Hr. lia. }
  destruct HBASE as (HPRE & _).
  destruct HPRE as (HAR0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK0 & HFD0 & HSORT0 &
    HAM0 & HMOK).
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  pose proof Hos as (_ & _ & Hfds & _).
  unfold tLLVMFuzzerTestOneInput_post. exists fq. split; [exact HF0|]. unfold apost_base.
  exists fq, ly', S', regs', mem', md'.
  split; [reflexivity|]. split; [intros; reflexivity|]. split; [left; reflexivity|].
  split; [eapply ajournal_mono_k; [exact HJ | exact Hk]|].
  split; [exact HPR|].
  split; [exact Ha0|].
  split; [exact HPerm|].
  split; [exact (fds_restored_of_asink (c_md cx) md' Hfds (proj2 (proj2 HSNK0)) (proj2 (proj2 HSNK')))|].
  split; [exact Efs|].
  split; [exact HSNK'|].
  split; [exact (ameta_inv_kept SEGS B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM0)|].
  split; [rewrite MT_TRIV; exact I|].
  intros i Hi.
  destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) (proj1 HAR0) Hpin) as (_ & Hp4096 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (F2 (c_p cx) (c_n cx) i Hpin).
  - eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpin].
  - unfold req_size. destruct (Z.eqb_spec (c_n cx) 0) as [Heq0|Hne0];
      [exfalso; clear - Hnpos Heq0; lia | exact Hi].
  - apply HnFP. clear - Hp4096 Hi. lia.
Qed.

End h.
End f.
End d.
