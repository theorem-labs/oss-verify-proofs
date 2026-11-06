(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: written for libreac/fuzz_decode's ASan+UBSan build (image B): the kernel
   refutation of the Section hypothesis HB_SINK_KEPT of lib/B/DecodeBClose.v as typed there (:328-331, the HSINK_KEPT
   premise of the frozen dec_llvmf_holds_stmt, lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:233-235). The A twin is
   lib/A/DecodeASinkRoProbe.v.

   HB_SINK_KEPT quantifies over every journal footprint FP. A journal whose FP holds the sink token (0, 1) lets the
   model's fd table change by YI16.fds_rel (lib/Reusable/YI16.v:51): a free fd may become a write fd on the sink
   path, and AR reads the model only through its vm maps, lazy list and eager count (lib/Reusable/YG0n.v:535
   ALedger_same, :439 amwf_same). So from any state where afn_pre, asink_none and a free fd hold (afn_pre, asink_none
   and the free fd alloc_fd are conjuncts of LLVMFuzzerTestOneInput's precondition dec_lib_pre_x,
   LLVMFuzzerTestOneInput_cg.v:109, :117, :118) there is a journal step with FP = [YI16.sink_token], no memory change
   and that fd added, after which an fd names the sink path; a Theorem Labs lane's asink_none rules that out (its third conjunct
   `Namei.fd_names_path (m_fds md) sink_path = false`, lib/Reusable/YE00.v:126-128 on -core e2ad4d7aa34). A Theorem Labs lane's
   own asink_none_kept (lib/B/YE01.v:85-88 on -coreB) has the premise `~ YI16.sink_open_fp FP`, which HB_SINK_KEPT
   lacks.

   The statement is stated for every symbol record B, sink record KS and sink predicate asink_none that rules out an
   fd on the sink path, so that it compiles on the closing tree before image B's core (TfibB, tfib_K, YE00) is merged;
   decode B's instance is B := TfibB, KS := tfib_K, asink_none := YE00.asink_none, whose side condition is
   `fun _ _ _ _ H => proj2 (proj2 H)`. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK04 YA0i YA0n YG00 YG0f YG0n YG0d YI16 YCbq YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YE00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YD2l YE2k.
Import ListNotations.
Open Scope Z_scope.

(* lib/B/DecodeBClose.v:328-331 HB_SINK_KEPT, verbatim, with the Section variables B, asink_syms, KS and asink_none
   as parameters and segs := decodesegsB0 (DecodeBClose.v:92). *)
Definition HB_SINK_KEPT_stmt (B : asyms) (asink_syms : Type) (KS : asink_syms)
    (asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc dec_B_sink_head decodesegsB0 B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    asink_none decodesegsB0 KS (mrestrict (w_H W0) mem0) md0 ->
    asink_none decodesegsB0 KS (mrestrict (w_H W') mem') md'.

(* with_fds changes the fd table only: the parts of the model aos_step and AR read are unchanged. *)
Lemma dec_B_with_fds_kept : forall (fds : list (word * FdEntry)) (md : Model),
  m_io (with_fds fds md) = m_io md /\ m_pipes (with_fds fds md) = m_pipes md /\
  m_fs (with_fds fds md) = m_fs md /\ m_fds (with_fds fds md) = fds /\
  m_vmmaps (with_fds fds md) = m_vmmaps md /\ m_vm_lazy (with_fds fds md) = m_vm_lazy md /\
  eager_used (with_fds fds md) = eager_used md /\ proc_but_pins md (with_fds fds md).
Proof.
intros fds [fd vm io fs [h ti c ss sm ch u sa k sp at_ pins] li tm].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

(* The witness journal: FP = [YI16.sink_token], own = [], k = 0, the same layout, state, world and memory, and the
   model with one more fd: fd, open for writing on the sink path at offset 0. *)
Theorem HB_SINK_KEPT_false :
  forall (B : asyms) (asink_syms : Type) (KS : asink_syms)
    (asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop),
  (forall segs K m md, asink_none segs K m md -> Namei.fd_names_path (m_fds md) sink_path = false) ->
  forall (rc : YM05.RunCeil) STK ly S (W : world decodesegsB0) regs mem md ch fd,
    @afn_pre rc decodesegsB0 B STK ly S W regs mem md ch ->
    asink_none decodesegsB0 KS (mrestrict (w_H W) mem) md ->
    fd_lookup (m_fds md) fd = None ->
  ~ HB_SINK_KEPT_stmt B asink_syms KS asink_none.
Proof.
intros B asink_syms KS asink_none NAMES rc STK ly0 S0 W regs mem md ch fd0 Hpre Hsn Hfree KEPT.
unfold HB_SINK_KEPT_stmt in KEPT.
generalize (dec_B_with_fds_kept ((fd0, FdFileW sink_path (Z_to_bv 64 0)) :: m_fds md) md).
generalize (with_fds ((fd0, FdFileW sink_path (Z_to_bv 64 0)) :: m_fds md) md).
intros md' (Eio & Epi & Efs & Efd & Evm & Elz & Eeu & Epp).
assert (J0 : @ajournal rc dec_B_sink_head decodesegsB0 B STK (spZ regs) [YI16.sink_token]
               ly0 S0 W mem md [] ly0 S0 W mem md 0)
  by (eapply ajournal_init; exact Hpre).
destruct J0 as (HAR & Hly & Hsecs & Hwle & _ & REST).
assert (J : @ajournal rc dec_B_sink_head decodesegsB0 B STK (spZ regs) [YI16.sink_token]
              ly0 S0 W mem md [] ly0 S0 W mem md' 0).
{ split; [|split; [exact Hly|split; [exact Hsecs|split; [exact Hwle|split; [|exact REST]]]]].
  - destruct HAR as (M & L & BU & MW & HS).
    split; [exact M|]. split; [eapply ALedger_same; [exact L | exact Evm | exact Elz | exact Eeu]|].
    split; [exact BU|]. split; [eapply amwf_same; [exact Evm | exact Elz | exact MW] | exact HS].
  - split; [exact Eio|]. split; [exact Epi|]. split.
    + intros fd. rewrite Efd. cbn [fd_lookup]. destruct (bv_eqb fd0 fd) eqn:E.
      * right. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst fd.
        split; [left; exact Hfree | right; exists (Z_to_bv 64 0); reflexivity].
      * left. reflexivity.
    + split; [rewrite Efs; apply YI16.fs_rel_refl|]. split; [rewrite Efs; auto|]. split; [exact Epp|].
      intros Hn. exfalso. apply Hn. apply YI16.sink_open_token. left. reflexivity. }
pose proof (NAMES _ _ _ _ (KEPT rc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J Hsn)) as Hn.
rewrite Efd in Hn. cbn [Namei.fd_names_path] in Hn. rewrite Fs.path_eqb_refl in Hn. cbn [orb] in Hn.
discriminate Hn.
Qed.

(* Decode B's instance: the composition's bindings B := TfibB (lib/B/YD2l.v:12), KS := tfib_K (lib/B/YE2k.v),
   asink_syms / asink_none := a Theorem Labs lane's lib/Reusable/YE00.v, whose asink_none (:126-128) has the fd conjunct third. *)
Module RE00 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YE00.
Module BD2l := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YD2l.
Module BE2k := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YE2k.
Theorem HB_SINK_KEPT_false_TfibB :
  forall (rc : YM05.RunCeil) STK ly S (W : world decodesegsB0) regs mem md ch fd,
    @afn_pre rc decodesegsB0 BD2l.TfibB STK ly S W regs mem md ch ->
    RE00.asink_none decodesegsB0 BE2k.tfib_K (mrestrict (w_H W) mem) md ->
    fd_lookup (m_fds md) fd = None ->
  ~ HB_SINK_KEPT_stmt BD2l.TfibB RE00.asink_syms BE2k.tfib_K RE00.asink_none.
Proof.
intros rc STK ly S W regs mem md ch fd Hpre Hsn Hfree.
exact (HB_SINK_KEPT_false BD2l.TfibB RE00.asink_syms BE2k.tfib_K RE00.asink_none
         (fun _ _ _ _ H => proj2 (proj2 H)) rc STK ly S W regs mem md ch fd Hpre Hsn Hfree).
Qed.

Print Assumptions HB_SINK_KEPT_false.
Print Assumptions HB_SINK_KEPT_false_TfibB.
