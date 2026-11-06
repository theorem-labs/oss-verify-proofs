(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v (srz_enter, the journal over a token list), ACk2.v (the file system a closed journal keeps), ACfj.v (tfib_lib_x) and ACfi.v (tfib_lib_x_all) for libreac/fuzz_grant: module paths, GrantB, the library shape grant_shape, and the entry function's phase machine of lib/A/Prog/GrantEntryDefs.v in place of cgif's. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryChain.v and lib/A/Prog/GrantLibX.v, over the phase definitions of lib/A/Prog/GrantEntryDefs.v. *)
(* Ported from lib/A/Prog/GrantEntryChain.v at a working branch 5651bf66924 (blob 6650b8120af) and the closing half of lib/A/Prog/GrantLibX.v at a working branch 552860c636687 (blob 79cffc88c05; the GrantLibX.v beside the first file differs). Both heads carry lib/A/AB01.v 1e6f4323d1e, the current start-up-table generation. *)
(* The walk of image B's entry function LLVMFuzzerTestOneInput (fuzz_grant.asan-ubsan
   0x80a3c, 1422 instructions): the phase machine chained into the whole call, and that
   call turned into the contract `tb_LLVMFuzzerTestOneInput_spec` of
   lib/B/Prog/GrantBContracts.v.

   The phases are cut as image A's walk cuts them (lib/A/Prog/GrantEntryDefs.v of
   a working branch 5651bf66924; this file is the image-B twin of lib/A/Prog/GrantEntryChain.v and of
   the closing half of lib/A/Prog/GrantLibX.v), with image B's own cut addresses:

     0x80a3c entry -> 0x80d04 GI_hdr -> 0x80db0 GI_mallocT -> 0x80ef8 GI_set (loop)
     -> 0x81224 GI_unset0 -> 0x81300 GI_admit -> 0x81390 GI_sweep -> 0x8181c GI_raw
     -> 0x81944 GI_sched0 -> 0x81bb0 GI_sched (loop) -> 0x81da4 GI_freeT
     -> 0x80cd8 GI_leave -> 0x80d94 ret.

   Two cuts have a second way in, as on image A: GI_unset0 (an input that sets no cell
   skips the set loop) and GI_freeT (a frame count of 0 skips the scheduler). Image B
   adds a third: the release block 0x80cd8 sits BEFORE the body, so GI_leave is reached
   both by `j 0x80cd8` at 0x81e94 and by the early return of an input of 2 ^ 26 bytes
   or more (`beq a3,zero,0x80d00` at 0x80cd4 failing).

   The allocator meter is the trivial one: image B's contract states no meter clause
   (tb_LLVMFuzzerTestOneInput_post is apost_base, with no `mo_le`), so every phase is
   instantiated at `ameter_triv`, whose `mo_ok` and `mo_le` are True. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntryDefs LLVMFEntrySeat GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntryHead LLVMFEntryHdr LLVMFEntryInit LLVMFEntrySet LLVMFEntryUnset
LLVMFEntryAdmit LLVMFEntrySweep LLVMFEntryRaw LLVMFEntrySchedSetup LLVMFEntrySchedTurn
LLVMFEntryEnd.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section H.
Variable B : asyms.

(* ---- the phase machine ------------------------------------------------------------
   One Definition per phase, each the statement that phase's file proves, at the
   post-condition of the whole call. The shapes are image A's (GrantEntryChain.v);
   `ph_head` and `ph_init` and `ph_setup` take two next phases because their stretch of
   image B's code ends in a two-way split. *)
#[local] Notation MT := ameter_triv.
#[local] Notation P := (ge_post B MT).

Definition ph_head : Prop :=
  ge_from B MT P (GI_hdr B) -> ge_from B MT P (GI_leave B MT) -> ge_start B MT P.
Definition ph_hdr : Prop := ge_from B MT P (GI_mallocT B) -> ge_from B MT P (GI_hdr B).
Definition ph_init : Prop :=
  ge_from B MT P (GI_set B MT) -> ge_from B MT P (GI_unset0 B MT) -> ge_from B MT P (GI_mallocT B).
Definition ph_set : Prop := ge_from B MT P (GI_unset0 B MT) -> ge_from B MT P (GI_set B MT).
Definition ph_unset : Prop := ge_from B MT P (GI_admit B MT) -> ge_from B MT P (GI_unset0 B MT).
Definition ph_admit : Prop := ge_from B MT P (GI_sweep B MT) -> ge_from B MT P (GI_admit B MT).
Definition ph_sweep : Prop := ge_from B MT P (GI_raw B MT) -> ge_from B MT P (GI_sweep B MT).
Definition ph_raw : Prop := ge_from B MT P (GI_sched0 B MT) -> ge_from B MT P (GI_raw B MT).
Definition ph_setup : Prop :=
  ge_from B MT P (GI_sched B MT) -> ge_from B MT P (GI_freeT B MT) -> ge_from B MT P (GI_sched0 B MT).
Definition ph_turn : Prop := ge_from B MT P (GI_freeT B MT) -> ge_from B MT P (GI_sched B MT).
Definition ph_end : Prop := ge_from B MT P (GI_freeT B MT).
Definition ph_leave : Prop := ge_from B MT P (GI_leave B MT).

(* The chain, as image A chains it (GrantEntryChain.v:49-57). *)
Theorem ge_chain : ph_head -> ph_hdr -> ph_init -> ph_set -> ph_unset -> ph_admit ->
  ph_sweep -> ph_raw -> ph_setup -> ph_turn -> ph_end -> ph_leave -> ge_start B MT P.
Proof.
  intros PH_head PH_hdr PH_init PH_set PH_unset PH_admit PH_sweep PH_raw PH_setup PH_turn
    PH_end PH_leave.
  pose proof (PH_turn PH_end) as Hsched.
  pose proof (PH_setup Hsched PH_end) as Hsched0.
  pose proof (PH_unset (PH_admit (PH_sweep (PH_raw Hsched0)))) as Hunset0.
  exact (PH_head (PH_hdr (PH_init (PH_set Hunset0) Hunset0)) PH_leave).
Qed.

(* ---- the call, at image B's contract ----------------------------------------------
   `ge_start` gives the run from the first slot under `ge_base`; the contract asks for
   the run from the first slot under `afn_pre` and the premises of
   tb_LLVMFuzzerTestOneInput_spec. The two differ in three places only:
   - the context record `ecx` has to be built, with the realigned stack pointer
     32 * ((sp - 288) / 32), the entry environment `Ereg regs [w64 SHADOW_OFF]` and the
     budget 0 (at the trivial meter `GE_NEED` is 0 and `mo_ok` is True);
   - the call traces of the six wrapper calls are the contract's own named image fact
     IMG_LLVMF_TRACES, whose shape is `gch`'s;
   - `ge_post` reports the journal at some k <= GE_EV, while `apost_base` names the
     event bound EV_LIB_B: ajournal_mono_k (YCbq.v:394) closes that gap, and
     `frames S' = []` comes from ajournal's own clause `frames S' = own ++ frames S`
     (YCbq.v:355) with own = [] and the contract's premise `frames S = []`. *)
Definition llvmf_cx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (pl : list byte) : ecx (PI := PI) :=
  mkECX (PI := PI) ly S W regs mem md p pl
    (32 * ((spZ regs + -288) / 32)) (Ereg regs [w64 SHADOW_OFF]) 0.

Lemma llvmf_of_start :
  IMG_LLVMF_TRACES B -> ge_start B MT (ge_post B MT) -> tb_LLVMFuzzerTestOneInput_spec B.
Proof.
  intros HTR START.
  unfold tb_LLVMFuzzerTestOneInput_spec.
  intros ly S W regs mem md p n pl HPRE Hra H10 H11 Hpn Hnpl HPL Hfr Hev Hlive HRO.
  set (cx := llvmf_cx ly S W regs mem md p pl).
  assert (HB : ge_base B MT cx).
  { unfold ge_base, cx, llvmf_cx, c_n.
    cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_sp1 c_E0 c_T].
    rewrite <- Hnpl.
    split; [exact HPRE|]. split; [exact H10|]. split; [exact H11|].
    split; [exact Hpn|]. split; [exact HPL|]. split; [exact Hfr|].
    split; [exact Hev|]. split; [exact Hlive|]. split; [exact HRO|].
    split; [reflexivity|].
    split; [intros m0 r Hm0; exact (ew_Ereg_nat regs _ m0 r Hm0)|].
    split; [exact (f_equal (fun w => bv_unsigned w) (ew_Ereg_nat regs _ 2 2%bv eq_refl))|].
    split; [exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)|].
    split; [exact I|].
    (* `ge_base`'s trace clause counts the six wrapper return addresses from BASE and
       names them through GE_MSITES / GE_FSITES, which are TB_LLVMF_MSITES /
       TB_LLVMF_FSITES; IMG_LLVMF_TRACES counts them from BASE + AF_LLVMFuzzerTestOneInput.
       The two agree because this function is the listing's first slot, AF_... = 0. *)
    split;
    [ intros pcf regsT Hsite; unfold GE_MSITES, GE_FSITES in Hsite;
      apply (HTR ly regs regsT pcf Hra);
      replace (BASE + AF_LLVMFuzzerTestOneInput) with (BASE : Z)
        by (unfold AF_LLVMFuzzerTestOneInput; lia);
      exact Hsite |].
    reflexivity. }
  eapply SRr_mono; [exact (START cx HB)|].
  intros W' c' Hwle HPOST.
  unfold ge_post, cx, llvmf_cx in HPOST.
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T] in HPOST.
  destruct HPOST as (ly' & S' & regs' & mem' & md' & k & Ec & HJ & Hk & HPR & Ha0 & HPerm & _ & HKeep).
  unfold tb_LLVMFuzzerTestOneInput_post, apost_base.
  exists ly', S', regs', mem', md'.
  split; [exact Ec|].
  (* `ge_post` reports the journal at some k <= GE_EV; `apost_base` names the event
     bound EV_LIB_B, and GE_EV is EV_LIB_B, so the journal weakens to it. *)
  split; [eapply ajournal_mono_k; [exact HJ | exact Hk]|].
  split; [exact HPR|].
  split; [exact Ha0|].
  split.
  { pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs, Hfr. reflexivity. }
  split; [exact HPerm|].
  intros i Hi. apply HKeep. unfold c_n. cbn [c_pl]. lia.
Qed.

(* ---- the walk ---------------------------------------------------------------------
   `walk_LLVMFuzzerTestOneInput B` is `hyps_LLVMFuzzerTestOneInput B`, then the contract
   of each of the thirteen program functions the call makes, implying the contract of
   the call. Each phase file closes its Section over exactly the runtime laws and callee
   contracts its own proof uses, so each phase theorem takes a different prefix of
   them; the wiring therefore `eapply`s each phase and closes every premise from the
   context, rather than spelling out twelve argument lists that would break whenever a
   phase stops needing a law.
   The allocator rules at the trivial meter are built once from RT_MALLOC / RT_FREE, as
   image A's GrantLibXClosed.v builds them (lib/Reusable/YCbp.v). *)
Theorem pb_LLVMFuzzerTestOneInput : walk_LLVMFuzzerTestOneInput B.
Proof.
  unfold walk_LLVMFuzzerTestOneInput, hyps_LLVMFuzzerTestOneInput.
  (* The conjuncts in the order GrantBContracts.v states them at a working branch
     4d7ced43548: the runtime laws, then IMG_RO_BELOW (a walk that reads an image byte
     through arodata_okP after its own side-stack call needs ro_below_ofl to transport
     it, PaBase.v:38 arodata_ok_journalP), IMG_LLVMF_TRACES, and IMG_LLVMF_SWEEP (the
     bytes, GRANT_GLOBS_B entries and image bounds of the four read-only tables the
     sweep compares with __wrap_bcmp: HEAD_ACK object 4, HEAD_MARK object 5, POLL object
     6, GRANT_GROUPB object 19). *)
  intros (HL & HTL & HTLF & HML & HSMP & HASF & HFFL & HMALLOC & HFREE & HMEMSET &
          HBCMP & HSM4 & HSSF5 & HIMGSH & HGLOBS & HTPFS & HROB & HTRACES & HSWEEP)
         HINIT HSET HEFF HDFLT HFITS HALLOC HBSW HWANT HGROUPA HPOLL HARM HRSW HNEXT.
  unfold RT_LAWS, RT_PALIB, RT_PALIBF, RT_ML, RT_SMP, RT_ASF, RT_FFL, RT_MALLOC, RT_FREE,
    RT_MEMSET, RT_BCMP, RT_SM, RT_SSF5, RT_IMGSH, RT_GLOBS, RT_TP_FS, IMG_RO_BELOW in *.
  pose proof ameter_triv_laws as HMTL.
  pose proof ameter_triv_fs_laws as HMTF.
  pose proof (amalloc04_rule_triv SEGS B pa_segs_low (pal_env B HTL) HL HML HMALLOC) as HAM4.
  pose proof (afree04_rule_triv SEGS B pa_segs_low (pal_env B HTL) HL HML HFREE) as HAF4.
  pose proof (afree_null04_rule_triv SEGS B pa_segs_low (pal_env B HTL) HL HML HFREE) as HAFN4.
  apply (llvmf_of_start HTRACES).
  (* A phase may take its runtime laws as ONE bundled premise (the sweep phase's
     GSW_RT is a twelve-way conjunction of conjuncts of hyps_LLVMFuzzerTestOneInput plus
     the trivial-meter laws and rules posed above), so a premise that no hypothesis
     matches is unfolded once and split before each piece is closed from the context.
     The split is `apply conj` only: `split` would also open the Records among the
     conjuncts (AR_laws, PALib, PALibF), whose hypotheses would then no longer match. *)
  apply ge_chain; red; intros; first
    [ eapply LLVMFEntryHead.ge_head
    | eapply LLVMFEntryHdr.ge_hdr_read
    | eapply LLVMFEntryInit.ge_init
    | eapply LLVMFEntrySet.ge_set
    | eapply LLVMFEntryUnset.ge_unset
    | eapply LLVMFEntryAdmit.ge_admit
    | eapply LLVMFEntrySweep.ge_sweep
    | eapply LLVMFEntryRaw.ge_raw
    | eapply LLVMFEntrySchedSetup.ge_sched_setup
    | eapply LLVMFEntrySchedTurn.ge_sched_turn
    | eapply LLVMFEntryEnd.ge_end
    | eapply LLVMFEntryEnd.ge_leave ];
    first [ eassumption | (progress red; repeat (apply conj); eassumption) ].
Qed.

End H.
End F.
End W.
