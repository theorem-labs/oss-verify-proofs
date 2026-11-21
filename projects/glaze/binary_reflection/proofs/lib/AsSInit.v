(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput, the rseq-sized auxv and the strings above the AT_RANDOM block in the initial facts; the reserved ledger's vDSO pair at the start state, from the model's vdso_top_init_model and vdso_reserved_entry_ok; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymStepR AzSymExec3 AzSymExec3B AzSymExec3Sound AzSymRun3 AzPlanCore AzPlan AzAPS AzGPS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.

(* The EXACT size of the initial stack image.  Linux's block now runs from the
   entry stack pointer to the stack VMA's end, so it is [ed_top - sp]
   ([Run.entry_launch_ok_va], [PropExec.length_entry_stack_image_launch]).  It
   WAS a sum over the model's own short block, which ended sixteen bytes above
   the AT_RANDOM bytes and carried no pad and no exec file name. *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  (* The image's ELF entry: [Run.init_config]'s pc, and the auxv's AT_ENTRY.
     It is a Section variable because the revision's auxv reads it, so the
     stack image is a function of it; it WAS only [init_cfg_eq_at]'s local
     quantifier. *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  (* The whole process input, projected below rather than built here.
     [State.ProcInput] gained five fields at this revision ([in_tmp] was
     already present; [in_kernel], [in_execfn], [in_channel_reader],
     [in_sigpipe_default], [in_sigpipe_terminal] are the new ones), and a
     definition that names the record's arity breaks again the next time one
     is added.  Every consumer reads the fields through the projections, so
     [m_fs (init_model _ _ _ _ _ inp) = in_fs inp] and its siblings still hold
     by [reflexivity] for a variable [inp] ([State.m_fs_init_model]). *)
  Variable inp : ProcInput.

  Local Notation argv   := (in_argv inp) (only parsing).
  Local Notation envp   := (in_envp inp) (only parsing).
  Local Notation fs     := (in_fs inp) (only parsing).
  Local Notation uid    := (in_uid inp) (only parsing).
  Local Notation gid    := (in_gid inp) (only parsing).
  Local Notation hw     := (in_hwcap inp) (only parsing).
  Local Notation execfn := (in_execfn inp) (only parsing).
  (* CONFIG_RSEQ is the run's own: the auxv is 29 pairs / 464 bytes with it
     and 27 / 432 without ([StackLayout.auxv_count], [StackLayout.auxv_size]),
     and nothing below may fix it. *)
  Local Notation rseq   := (kb_rseq (in_kernel inp)) (only parsing).
  Local Notation entryw := (Z_to_bv 64 (Z.of_N apc)) (only parsing).
  Local Notation top    := (ed_top rdraw) (only parsing).
  Local Notation la     := (launch_auxv inp sp mbase) (only parsing).
  (* The plan's [r], instantiated at THIS run's flag.  The plan expressions
     and tables took an [r : Z] parameter at this revision; the value a
     consumer must supply is the run's own CONFIG_RSEQ, which is exactly
     [AzPlanCore.rseq_z (kb_rseq (in_kernel inp))].  It is not pinned: it
     varies with [inp] like every other projection above. *)
  Local Notation RS := (rseq_z rseq) (only parsing).

  Hypothesis IMG  : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hsp  : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb  : valid_mmap_base mbase.
  Hypothesis Hva  : valid_argv (in_argv inp).
  Hypothesis Hve  : valid_envp (in_envp inp).
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id (in_uid inp).
  (* [comment removed for export] *)
  Hypothesis Hhw  : valid_hwcap (in_hwcap inp).
  (* [Run.valid_input]'s last conjunct: the exec file name is one [execve]
     admits and the launch fits under E2BIG. *)
  Hypothesis Hvl  : valid_launch inp.
  (* [valid_input_core]'s reader clause (Common/AsanAcctShape.v), itself
     [Run.valid_input]'s at Run.v:4589.  [init_model] seeds
     [procst_channel_reader] from it (State.v:7781) and nothing writes the
     field afterwards, which is what lets [cs_ok]'s [co_rdr] be discharged
     here by conversion. *)
  Hypothesis Hrdr : in_channel_reader inp = true.
  (* [Run.valid_entry]'s fifth conjunct: the start state is exactly a Linux
     launch.  It is what pins the stack VMA's end, the entry stack pointer
     inside the [arch_align_stack] window and the mmap base, so it is what
     bounds the pad and the image's length now that the image is the whole
     block from [sp] to [ed_top]. *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  (* The mapped image IS Linux's whole block, sp .. ed_top: there is no page
     tail to append any more, so [bsb] and [SIMG] are the same list and the
     old [length_app] over image-plus-slack has no [++] left to split. *)
  Let SIMG := entry_stack_image inp mbase ph entryw sp rdraw.
  Let bsb := SIMG.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [V_W] CHANGES MEANING at this revision.  It WAS the number of 8-byte
     words of string block below the AT_RANDOM bytes, spelled from the image
     length as [(length bsb - 16 - (8*argc + 8*envc + 184)) / 8] -- a form
     whose 184 is 24 + the old fixed 160-byte auxv, and which is false once
     the auxv is 432 or 464 and the strings sit ABOVE the random bytes.
     It IS now [StackLayout.block_pad_len]: the pad [arch_align_stack] left
     between the random block and argv[0], in BYTES, 0..4110. *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).

  (* [V_G] is new: [StackLayout.block_items argv envp mod 2], the 8-byte gap
     [STACK_ROUND] clears below the AT_RANDOM block so it lands 16-aligned.
     It is 0 or 1 and the plan scales it by 8 ([e_atrandom]'s
     [escale 8 (EVar V_G)]), which is why the value here is the remainder and
     not the gap in bytes. *)
  Let GAP := Z.of_nat (block_items argv envp mod 2).

  (* [comment removed for export] *)
  Let TV := (usp - 160 + 4095) / 4096 - 8 * (usp / 32768).
  Let PV := usp / 4096 - 8 * (usp / 32768).
  (* [BV] and [R8V] are the environment's own account of [e_bend64]'s
     position, so they move with the AT_RANDOM block.  Old beside new:
       BV  := (usp + length bsb + 63) / 64
       R8V := (64 * BV - (usp + length bsb)) / 8
       BV  := (usp + block_head_size rseq argv envp + 63) / 64
       R8V := (64 * BV - (usp + block_head_size rseq argv envp)) / 8
     [e_bend r] is [eaddz (e_atrandom r) 16] (AsStartupTabs.v:59), the TOP of
     the sixteen AT_RANDOM bytes, and [e_atrandom r] is now their BASE at
     [sp + (C - 16)] ([StackLayout.at_random_ptr], StackLayout.v:425-427), so
     [e_bend r] denotes [usp + C] exactly.  It WAS [usp + length bsb] only
     because the random bytes used to be the last thing below the top; the
     pad and the strings now sit ABOVE them, so the two differ by
     [pad + L + 8] with [L = launch_string_bytes >= 1] always.  [e_bend64 r]
     is [e_bend r + 8*V_R8], so [R8V] is the slack to the next 64 boundary
     above [usp + C], not above the image's end.
     THIS IS AN ENVIRONMENT VALUE, NOT A DESCRIPTION OF ONE.  [R8V] is
     [vals0]'s entry 12 and [uE0_R8] reads it straight out with
     [cbn ... nth vals0 V_R8], so leaving it over the old position does not
     merely make a lemma false -- it VALUES the plan variable [V_R8] off the
     pre-reordering layout.  Same class as [V_G := 13] indexing past a
     thirteen-entry [vals0]: both compile, and no arity or literal sweep can
     see either. *)
  Let BV := (usp + Z.of_nat (block_head_size rseq argv envp) + 63) / 64.
  Let R8V := (64 * BV - (usp + Z.of_nat (block_head_size rseq argv envp))) / 8.

  (* THIRTEEN entries WAS right when the plan had thirteen variables.  [V_G]
     is the fourteenth (index 13) and MUST be appended here: [E0] is
     [nth n vals0 (Z_to_bv 64 0)], so a missing entry does not fail -- it
     silently denotes ZERO, which would erase the STACK_ROUND gap from every
     address built on [e_atrandom] and be wrong by 16 bytes whenever
     [block_items] is odd. *)
  (* LPS 727298f3: [V_GID] (index 14) is AT_GID / AT_EGID, [in_gid inp]. *)
  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid;
     hw; Z_to_bv 64 TV; Z_to_bv 64 PV; Z_to_bv 64 R8V; Z_to_bv 64 GAP; gid].
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0)) (fun _ => []).

  (* [comment removed for export] *)
  (* The startup lane's hidden set: the envp array, the string block and, since the
     revision's [read_cstr_toolong_of_rdn] (LPS 26feb4a5, FileSim.v:475-479) asks for
     [bv_unsigned a + 4096 <= TASK_SIZE], every address at or above [TASK_SIZE].  Bytes
     there are pinned by [SINV0] to [FULL0], which maps nothing there ([FULL0_task]:
     the stack block ends at [top <= sp_window_hi = TASK_SIZE], [top_le]).  The
     startup lane's soundness keeps hidden bytes unchanged ([SINV_frame], AzAPS.v:111),
     so the memory at [main] still maps nothing there ([SINV0_task]). *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    ((uE E e_sp0 =? usp) &&
     ((((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
       (* The string block.  Old beside new:
            base   usp + 8*argc + 8*envc + 184        -> usp + cat_string_off …
            length 8 * W  (W = string words)          -> launch_string_bytes argv envp execfn
          Both halves had to move together: [W] is now [block_pad_len], a
          byte count for the PAD, so [8 * W] is no longer the string block's
          length and the old 184 is no longer its base.  Leaving either
          behind compiles and describes the wrong bytes.  The block runs from
          [sp + block_head_size + block_pad_len] for [launch_string_bytes]
          bytes, with the eight-byte slot create_init_stack_vma skipped above
          it -- i.e. sp + C + W + L + 8 = top. *)
       || ((usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) <=? z)
           && (z <? usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                    + Z.of_nat (launch_string_bytes argv envp execfn))))
      || (TASK_SIZE <=? z)))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NXS)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> sp_window_lo <= bv_unsigned a /\ bv_unsigned (edenot E ISP_S) <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H. destruct Hsp as (Hlo & Hhi & _).
    pose proof (valid_argv_len argv Hva).
    apply andb_prop in H as [He H]. apply Z.eqb_eq in He. unfold ISP_S. unfold uE in He. rewrite He.
    apply orb_prop in H as [H|H].
    - apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in H |- *; lia.
    - apply Z.leb_le in H. unfold usp, TASK_SIZE, sp_window_lo, sp_window_hi in *. lia.
  Qed.

  Lemma e_sp0_vars : expr_vars_lt NXS e_sp0 = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NXS E E' -> argH0 E a = argH0 E' a.
  Proof.
    intros E E' a Hag. unfold argH0, uE. rewrite (edenot_agree NXS E E' e_sp0 Hag e_sp0_vars). reflexivity.
  Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NXS E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M Hag0 [H1 H2]. pose proof Hag0 as [Hag _]. split.
    - intros n Hn. rewrite <- (Hag n) by (unfold NXS in *; lia). apply H1. exact Hn.
    - intros a Ha. apply H2. rewrite (argH0_agree E E' a Hag0). exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.

  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  (* The image's length is no longer a sum over a short block: Linux's block
     runs from the entry stack pointer to the stack VMA's end, so it is
     [ed_top - sp] ([PropExec.length_entry_stack_image_launch]).  The old
     proof summed the head, the strings and a sixteen-byte tail; there is no
     [++] left to split that way, and the strings are now anchored at the top
     rather than at [sp].  Same shape as [DrvS0Dir.BLEN_eq]. *)
  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size sp top.
  Proof.
    unfold bsb, SIMG, stack_image_size.
    rewrite (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
    reflexivity.
  Qed.

  (* [DrvS0Dir.top_le]: the launch's own ceiling on the stack VMA's end. *)
  Lemma top_le : bv_unsigned top <= 2 ^ 47.
  Proof.
    pose proof Hlau as (Ht & _). destruct Ht as (_ & Ht & _). cbn [va_stack_top] in Ht.
    unfold sp_window_hi in Ht. lia.
  Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof top_le. rewrite length_bsb_eq. unfold stack_image_size, usp. lia.
  Qed.

  (* The second conjunct is RESTATED 184-free, not dropped: two proofs consume
     it (:490's R8V/BV bound and :1101's A_bytes bound).  It said
     [(length bsb - 16 - (8*argc + 8*envc + 184)) mod 8 = 0]; since
     16 + 184 = 200 and 200 mod 8 = 0, and 8*argc and 8*envc are multiples of
     8, that is exactly [length bsb mod 8 = 0].  Same fact, same proof from
     the launch (the stack VMA's end is page aligned and [sp] is 16 aligned),
     no dependence on the old auxv size -- and every [bsb_ge as [G _]],
     [as [G GM]] and [as [_ GM]] destructure unchanged. *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 200 <= Z.of_nat (length bsb)
                 /\ Z.of_nat (length bsb) mod 8 = 0.
  Proof.
    (* [stack_image_size] is now [ed_top - sp] (Common/AsanInit.v:356 at
       75d69e00, which WAS :159 at f1006fe8, where it summed the model's own
       short block).  The old proof matched on that sum's padding term
       [((8 - ?l mod 8) mod 8)], which the goal no longer contains.  Both
       conjuncts come from the launch instead ([Run.entry_launch_ok_va]):
       - the stack VMA's end is page aligned and [sp] is 16 aligned, so the
         block's length is a multiple of 8, which is the divisibility;
       - [sp <= launch_sp_hi top inp] puts the whole block head C below
         [top - 8 - L], and C alone is at least [8 * argc + 8 * envc + 464]
         ([StackLayout.block_head_size]: the vector, the 432-or-464-byte auxv,
         the gap and the sixteen random bytes), which is the lower bound. *)
    pose proof Hlau as (Ht & Hsw & _).
    destruct Ht as (Htp & _ & _). destruct Hsw as (Hspm & _ & Hsphi).
    unfold page_size in Htp.
    assert (HC : (8 * length argv + 8 * length envp + 200
                  <= block_head_size rseq argv envp)%nat).
    { unfold block_head_size, block_items, auxv_size, auxv_count.
      destruct rseq; lia. }
    unfold launch_sp_hi in Hsphi.
    pose proof (align_down16_le
      (bv_unsigned top - 8
       - Z.of_nat (launch_string_bytes argv envp execfn))) as Hal.
    rewrite length_bsb_eq. unfold stack_image_size, argc, envc.
    split; lia.
  Qed.

  (* The head's own facts, beside [bsb_ge] and by [bsb_ge]'s route, because
     [BV] and [R8V] are now stated over [block_head_size] and [usp_fit] --
     which bounds [usp + length bsb] -- no longer reaches them.  NO NEW MODEL
     FACT IS NEEDED; two conjuncts are the model's own lemmas and the rest is
     [bsb_ge]'s chain:
     - the EXACT head equation
         C = 8*argc + 8*envc + 16*auxv_count rseq + 8*GAP + 40
       is [StackLayout.block_head_size] read off (StackLayout.v:399-401):
       [8*block_items + auxv_size + 8*(items mod 2) + 16] with
       [block_items = argc + envc + 3] and [auxv_size = 16*auxv_count].  It is
       stated rather than the two-sided bound alone because THE rseq TERM IS
       LOAD-BEARING DOWNSTREAM: [e_atr8]'s own [KRange] upper bound carries a
       [- 4 * r] (AsStartupTabs.v:81, :90) that no rseq-free bound can meet.
     - the two-sided bound is [Run.block_head_size_bounds] (Run.v:3889 at
       75d69e00, :3884 at 08b1429; statement IDENTICAL across the pair),
       480 <= C <= 10752 with [len_av]/[len_ev].  Kept beside the
       equation so sites that only need a size do not have to case-split.
     - [C mod 16 = 0] is [Run.block_head_size_mod16] (Run.v:3904 / :3899,
       statement), the fact that makes [R8V] even (0/2/4/6), not merely 0..7.
     - [usp + C <= 2^47 - 16], and the SIXTEEN IS NOT SLOP.  [Hlau] gives
       [sp <= launch_sp_hi top inp], [launch_sp_hi] is
       [align_down16 (top - 8 - L) - C] (Run.v:3641-3646 / :3636-3641), so
       [usp + C <= top - 8 - L <= top - 9 <= 2^47 - 9] by
       [Run.align_down16_le] (Run.v:3851 / :3846), [top_le] and [L >= 1]; and
       [usp + C] is a multiple of 16 ([usp_al] and the conjunct above), so it
       is at most [2^47 - 16].  [e_atr8]'s [KRange] upper bound is TIGHT at
       exactly this value -- [2^44 - 61 - 4*r] -- so a plain [<= 2^47] misses
       it by two.
     - [C + 9 <= length bsb] is the same chain plus [length_bsb_eq]:
       [length bsb = top - usp], [usp + C <= top - 8 - L], [L >= 1].
       [atrandom_byte] needs it to place the sixteen bytes inside the image
       now that they are no longer at its top.
     [L >= 1] is [launch_string_bytes]'s own trailing [+ 1], the execfn NUL
     (StackLayout.v:406-409); no model lemma is needed for it. *)
  Lemma head_fit :
    Z.of_nat (block_head_size rseq argv envp)
      = 8 * argc + 8 * envc + 16 * Z.of_nat (auxv_count rseq) + 8 * GAP + 40
    /\ (8 * argc + 8 * envc + 472 <= Z.of_nat (block_head_size rseq argv envp)
        <= 8 * argc + 8 * envc + 512)
    /\ Z.of_nat (block_head_size rseq argv envp) mod 16 = 0
    /\ usp + Z.of_nat (block_head_size rseq argv envp) <= 2 ^ 47 - 16
    /\ Z.of_nat (block_head_size rseq argv envp) + 9 <= Z.of_nat (length bsb).
  Proof.
    pose proof top_le. pose proof len_av. pose proof len_ev. pose proof usp_al.
    pose proof (block_head_size_bounds rseq argv envp) as HB.
    pose proof (block_head_size_mod16 rseq argv envp) as HM.
    assert (HL : 1 <= Z.of_nat (launch_string_bytes argv envp execfn))
      by (unfold launch_string_bytes; lia).
    pose proof Hlau as (_ & Hsw & _). destruct Hsw as (_ & _ & Hsphi).
    unfold launch_sp_hi in Hsphi.
    pose proof (align_down16_le
      (bv_unsigned top - 8
       - Z.of_nat (launch_string_bytes argv envp execfn))) as Hal.
    assert (HLb : Z.of_nat (length bsb) = bv_unsigned top - bv_unsigned sp)
      by (rewrite length_bsb_eq; reflexivity).
    assert (HCe : Z.of_nat (block_head_size rseq argv envp)
                  = 8 * argc + 8 * envc + 16 * Z.of_nat (auxv_count rseq) + 8 * GAP + 40).
    (* The failing tactic is the FINAL [lia], not any [unfold].  [lia] is
       [PuLia.lia_nd] here (:19), whose body is
       [first [ solve [zify_nodiv; xlia zchecker] | Zify.zify; xlia zchecker ]]
       (PuLia.v:14-18), and "No applicable tactic." is what an exhausted
       [first] says; an unresolvable [unfold] says something else.  The
       reported line is always the line carrying [lia], which is why the
       error appears to "move" each time that line moves (the reported line
       is the failing tactic's, not the subgoal's).
       WHY [lia] CANNOT CLOSE IT: [GAP] is [Z.of_nat (block_items argv envp
       mod 2)] (:146), so unfolding [GAP] puts [block_items] back into the
       goal AFTER the only [unfold block_items] has already run.  The left
       side then carries [(length argv + length envp + 3) mod 2] (via
       [block_head_size]'s [let items := block_items argv envp], StackLayout.v
       :399-401 at 75d69e00) while the right carries the opaque atom
       [block_items argv envp mod 2].  Two atoms for one quantity, so the
       goal is not linear-arithmetic-closable as it stands.  The fix is the
       ORDER: the local [Let]s expand FIRST and [block_items] LAST, so one
       [unfold block_items] catches both occurrences.
       [unfold a, b, c] IS sequential -- :319 of this file compiles with
       [auxv_size] and [auxv_count], which only appear after
       [block_head_size] expands.  That green line also supplies the other
       half: [destruct rseq] before [lia], because [auxv_count rseq] is
       [if rseq then 29%nat else 27%nat] (StackLayout.v:276-277) and stands
       on BOTH sides of this equation. *)
    { unfold GAP, argc, envc, block_head_size, auxv_size, auxv_count, block_items.
      cbv zeta. destruct rseq; lia. }
    try unfold argc in *. try unfold envc in *. try unfold usp in *.
    split; [|split; [|split; [|split]]]; lia.
  Qed.

  (* [V_W] is now [block_pad_len], so its range is the pad's, 0..4110 -- NOT
     the old string-word count's 0..280000.  Old beside new:
       W_range : 0 <= W /\ 8 * W = length bsb - 16 - (8*argc + 8*envc + 184)
                 /\ W <= 280000
       W_range : 0 <= W <= 4110
     The middle conjunct is GONE rather than restated: it equated the pad with
     an image-length expression built on the old 184 offset, which is false
     once the auxv is 432/464 and the strings sit above the random bytes.

     WHERE 4110 COMES FROM, and it is the launch's own lower bound on [sp]
     rather than an estimate.  [Run.valid_launch_sp] is
       sp mod 16 = 0 /\ launch_sp_lo top inp <= sp <= launch_sp_hi top inp
     and [Run.launch_sp_lo] is
       align_down16 (top - 8 - L - 4095) - C,   L = launch_string_bytes,
                                                C = block_head_size.
     [block_pad_len] is [top - 8 - L - sp - C], so the LOWER bound on [sp]
     gives the UPPER bound on the pad:
       pad <= (top - 8 - L) - align_down16 (top - 8 - L - 4095)
           <= 4095 + 15                              [Run.align_down16_ge]
           =  4110.
     That is arch_align_stack's own 0..4095 plus the fifteen bytes the
     low-four-bit mask can leave -- which is why the bound is 4110 and not
     4095.  The old proof discarded this conjunct as [_]; it is the one that
     carries the bound. *)
  Lemma W_range : 0 <= W <= 4110.
  Proof.
    pose proof Hlau as (_ & Hsw & _).
    destruct Hsw as (_ & Hsplo & _).
    unfold launch_sp_lo in Hsplo.
    pose proof (align_down16_ge
      (bv_unsigned top - 8
       - Z.of_nat (launch_string_bytes argv envp execfn) - 4095)) as Hal.
    unfold W, block_pad_len. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 208 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. lia. Qed.


  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W3).
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.


  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  Lemma u_sp8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [V_G] follows the shape this file already uses for every variable above
     [V_BRK] -- [uE0_L1], [uE0_uid], [uE0_hw], [uE0_T], [uE0_P], [uE0_R8] are
     each standalone rather than conjuncts of [uE0].  Stating it this way
     means none of the eleven [destruct uE0 as (...)] sites changes arity.
     [GAP] is [block_items argv envp mod 2], so it is 0 or 1 and the
     [u64_lit] side condition is immediate.
     It sits HERE, above [u_e_str0], because [u_e_str0] is its first
     consumer; stated below it, the file fails with
     "The variable uE0_G was not found in the current environment"
     (AsSInit.v:437). *)
  Lemma uE0_G : uE E0 (EVar V_G) = GAP.
  Proof.
    assert (HG : 0 <= GAP <= 1).
    { unfold GAP. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_G]. rewrite u64_lit by lia. reflexivity.
  Qed.

  (* Old beside new:
       u_e_str0 : uE E0 e_str0      = usp + 8*argc + 8*envc + 184
       u_e_str0 : uE E0 (e_str0 RS) = usp + cat_string_off rseq sp top argv envp execfn
     The 184 was 24 + the old fixed 160-byte auxv and is false at this
     revision.  The new right-hand side is NOT a linear form in argc/envc:
     the string base now sits above an rseq-sized auxv, a 0-or-8 gap and a
     0..4110 pad, so it is spelled with the model's own offset
     (Common/CatExec.v:578 = block_head_size + block_pad_len).
     Arithmetic: e_auxv = usp + 8*argc + 8*envc + 24 = usp + 8*block_items
     (block_items = argc + envc + 3); AUXSZ RS = auxv_size rseq by AUXSZ_of;
     8*GAP is the STACK_ROUND gap; +16 the random block; +W the pad.  Summing
     gives usp + block_head_size + block_pad_len. *)
  Lemma u_e_str0 : uE E0 (e_str0 RS)
    = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof W_range as (W1 & W3).
    pose proof u_e_auxv as UA. pose proof uE0_G as UG.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof (AUXSZ_of rseq) as HA.
    (* [u64_lit]'s side conditions meet the literal [AUXSZ RS]; its range,
       432..464 for either CONFIG_RSEQ, comes from [rseq_z_range]. *)
    assert (HAS : 432 <= AUXSZ RS <= 464)
      by (pose proof (rseq_z_range rseq); unfold AUXSZ; lia).
    assert (HG : 0 <= GAP <= 1).
    { unfold GAP. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. }
    unfold e_str0, e_atrandom, eadd, eaddz, escale, uE in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite UA, UG, U6, HA.
    rewrite !Z.mod_small by lia.
    (* [W] stays folded so that [W_range] still bounds it; the head and the
       pad are read off [head_fit] and [cat_string_off]'s definition. *)
    pose proof head_fit as (HCe & _).
    assert (HAX : Z.of_nat (auxv_size rseq) = 16 * Z.of_nat (auxv_count rseq))
      by (unfold auxv_size; lia).
    assert (HSO : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                  = Z.of_nat (block_head_size rseq argv envp) + W)
      by (unfold cat_string_off, W; lia).
    lia.
  Qed.

  Lemma u_e_str1 : uE E0 (e_str1 RS)
    = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    (* [Z.mod_small] needs the string base's range: the head's from [head_fit],
       the pad's from [W_range]. *)
    pose proof head_fit as (_ & (HC1 & HC2) & _).
    pose proof W_range as (W1 & W3).
    assert (HSO : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                  = Z.of_nat (block_head_size rseq argv envp) + W)
      by (unfold cat_string_off, W; lia).
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* Old beside new -- and the OLD ONE IS FALSE FOR EVERY INPUT, not merely
     unprovable:
       u_e_atrandom : uE E0 (e_atrandom RS) = usp + length bsb - 16
       u_e_atrandom : uE E0 (e_atrandom RS)
                        = usp + block_head_size rseq argv envp - 16
     The sixteen AT_RANDOM bytes USED to be the last thing below the top, so
     "top - 16" named them.  At this revision build_stack_bytes is
     head(C-16) ++ at_random(16) ++ pad ++ strings ++ 8 zero bytes
     (StackLayout), i.e. THE STRINGS SIT ABOVE THEM, and the model's own
     at_random_ptr is sp + (block_head_size - 16).  The two differ by
     pad + L + 8 where L = launch_string_bytes, and L >= 1 ALWAYS -- the
     execfn NUL alone -- so the old right-hand side is wrong for every input.
     Same shape as :894's ak: a value that was right before the reordering
     and is silently wrong after, stated over [length bsb] instead of a
     literal so no arity sweep could see it.
     ARITHMETIC, and it is one derivation shared with u_e_str0 rather than a
     second one: e_atrandom r denotes
       e_auxv + AUXSZ r + 8*V_G = usp + 8*argc + 8*envc + 24 + auxv_size + 8*GAP,
     and block_head_size = 8*block_items + auxv_size + 8*GAP + 16 with
     block_items = argc + envc + 3, so 8*block_items = 8*argc + 8*envc + 24
     and the two sides differ by exactly the 16.  u_e_str0 then adds 16 + W
     to reach cat_string_off = block_head_size + block_pad_len, which is why
     THAT lemma was already right: the +16 cancels this -16.
     The proof is u_e_str0's, stopped one step earlier -- same UA/UG/HA
     rewrites, no U6 because e_atrandom carries no V_W. *)
  Lemma u_e_atrandom : uE E0 (e_atrandom RS)
    = usp + Z.of_nat (block_head_size rseq argv envp) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit.
    pose proof len_av. pose proof len_ev.
    pose proof (rseq_z_range rseq) as HR.
    pose proof u_e_auxv as UA. pose proof uE0_G as UG.
    pose proof (AUXSZ_of rseq) as HA.
    assert (HAS : 432 <= AUXSZ RS <= 464) by (unfold AUXSZ; lia).
    assert (HG : 0 <= GAP <= 1).
    { unfold GAP. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. }
    unfold e_atrandom, eadd, eaddz, escale, uE in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite UA, UG, HA.
    rewrite !Z.mod_small by lia.
    pose proof head_fit as (HCe & _).
    assert (HAX : Z.of_nat (auxv_size rseq) = 16 * Z.of_nat (auxv_count rseq))
      by (unfold auxv_size; lia).
    lia.
  Qed.

  (* Old beside new, and the OLD one is FALSE for every input:
       u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + W
       u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + GAP
     [e_atr8] is [4096*V_S1 + 2*V_S2 + (V_ARGC + (V_ENVC + V_G))]
     (AzPlanCore.v:3625-3626) -- it carries [V_G], NOT [V_W].  The old
     statement named [W] and the old proof closed it by rewriting [U6]
     ([uE E0 (EVar V_W) = W]) into a goal that has no [V_W] in it.  The two
     differ by [block_pad_len - (block_items mod 2)], i.e. by up to 4110,
     and nothing pins the pad, so the statement is false rather than loose.
     The falsehood shows only when everything the AT_RANDOM derivation feeds
     is re-measured; this lemma's own text looks right.  [e_atr8] is
     [e_atrandom/8] less the
     rseq-dependent constant [3 + 2*auxv_count rseq], which is what the
     [- 4 * r] in its own [KRange] (AsStartupTabs.v:81, :90) is for.
     The old proof also ran [clear ... W2] with no [W2] in scope -- a leftover
     from when [W_range] had three conjuncts; it is gone with [W_range]. *)
  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + GAP.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    assert (HG : 0 <= GAP <= 1).
    { unfold GAP. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. }
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8.
    pose proof uE0_G as UG.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U8 by lia.
    rewrite U1, U2, U3, U4, UG in *.
    rewrite U8. clear U1 U2 U3 U4 U5 U6 U7 U8. clearbody GAP.
    assert (B8 : 0 <= usp / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    set (q := usp / 8) in *. clearbody q.
    rewrite (Z.mod_small (envc + GAP)) by lia. rewrite (Z.mod_small (argc + (envc + GAP))) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma TV_range : 0 <= TV <= 8 /\ 0 <= (usp mod 32768) + 3935 - 4096 * TV <= 4095.
  Proof. pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold TV. split; [split|split]; nia || lia. Qed.

  Lemma PV_range : 0 <= PV <= 7 /\ 0 <= (usp mod 32768) - 4096 * PV <= 4095 /\ 0 <= TV - PV <= 1.
  Proof. pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold TV, PV. lia. Qed.

  (* RE-DERIVED against the new [BV]/[R8V], not carried: the third conjunct is
     the equation that makes [u_e_bend64] true, and it is now over
     [block_head_size].  THE LITERAL BOUNDS ARE UNCHANGED AND STAY SOUND, so
     no consumer of [BV_range] moves: [usp + C >= 0x7fff80000000 + 480] gives
     [BV >= 0x1FFFE000008], above the stated 0x1FFFE000004, and
     [usp + C <= 2^47] with 64 | 2^47 gives [64 * BV <= 2^47], i.e.
     [BV <= 0x20000000000].
     [R8V] is EVEN here -- 0, 2, 4 or 6 -- because [head_fit]'s
     [C mod 16 = 0] and [usp_al] put [usp + C] on a 16 boundary.  The OLD
     [R8V] was identically ZERO: it was the slack above [usp + length bsb],
     which is [top], and the stack VMA's end is page aligned.  Stated 0..7
     all the same, because that is the plan's own [KRange (EVar V_R8) 0 7]. *)
  Lemma BV_range : 0x1FFFE000004 <= BV <= 0x20000000000 /\ 0 <= R8V <= 7
                   /\ 64 * BV = usp + Z.of_nat (block_head_size rseq argv envp) + 8 * R8V.
  Proof.
    pose proof usp_lo. pose proof len_av. pose proof len_ev. pose proof usp_al.
    pose proof head_fit as (HCe & (HC1 & HC2) & HCm & HCf & _).
    unfold R8V, BV. lia.
  Qed.

  Lemma uE0_R8 : uE E0 (EVar V_R8) = R8V.
  Proof. pose proof BV_range as (_ & [? ?] & _). unfold uE. cbn [edenot E0 ev nth vals0 V_R8]. rewrite u64_lit by lia. reflexivity. Qed.


  Lemma uE0_hw : edenot E0 (EVar V_HW) = hw.
  Proof. reflexivity. Qed.

  Lemma uE0_T : uE E0 (EVar V_T) = TV.
  Proof. pose proof TV_range as [[? ?] _]. unfold uE. cbn [edenot E0 ev nth vals0 V_T]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma uE0_P : uE E0 (EVar V_P) = PV.
  Proof. pose proof PV_range as [[? ?] _]. unfold uE. cbn [edenot E0 ev nth vals0 V_P]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma u_e_top : uE E0 e_top = 32768 * (usp / 32768) + 4096 * TV.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof TV_range as [[? ?] _]. destruct uE0 as (U1 & _).
    pose proof uE0_T as UT. unfold e_top, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UT. rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_ISPD : uE E0 ISPD = 32768 * (usp / 32768) + 4096 * PV.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof PV_range as [[? ?] _]. destruct uE0 as (U1 & _).
    pose proof uE0_P as UP. unfold ISPD, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UP. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* Old beside new, and the OLD one is FALSE for every input:
       u_e_bend : uE E0 (e_bend RS) = usp + length bsb
       u_e_bend : uE E0 (e_bend RS) = usp + block_head_size rseq argv envp
     [e_bend r := eaddz (e_atrandom r) 16] (AsStartupTabs.v:59-60) is the TOP
     of the sixteen AT_RANDOM bytes.  That point WAS the image's end; at this
     revision the pad and the strings sit above it, so it is short of
     [usp + length bsb] by [pad + L + 8] with [L >= 1] always.
     DERIVED DIRECTLY FROM [u_e_atrandom] + 16, not propagated through
     [u_e_str0] - W as the old proof was: [u_e_str0]'s route goes up through
     the pad and back down, and inherits whatever [V_W] means that day.  The
     rewrite chain is the one AsSInit already runs on this very expression at
     the [KRange (eaddz (e_atrandom RS) 16)] entry inside [init_kn3_ok]. *)
  Lemma u_e_bend : uE E0 (e_bend RS) = usp + Z.of_nat (block_head_size rseq argv envp).
  Proof.
    pose proof usp_lo. pose proof len_av. pose proof len_ev.
    pose proof head_fit as (_ & (HC1 & HC2) & _ & HCf & _).
    unfold e_bend, eaddz, uE. rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia.
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U.
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* The STATEMENT survives the move and the proof does not: [= 64 * BV] is
     true only because [BV] was redefined under it.  Propagating this lemma
     from a sibling instead of re-deriving it would have kept a true-looking
     equation over a [BV] still anchored at the image's end. *)
  Lemma u_e_bend64 : uE E0 (e_bend64 RS) = 64 * BV.
  Proof.
    pose proof usp_lo. pose proof head_fit as (_ & _ & _ & HCf & _).
    pose proof BV_range as (? & [? ?] & HB). pose proof uE0_R8 as UR. pose proof u_e_bend as UB.
    unfold e_bend64, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
    rewrite u_add64, u_mul64, u64_lit by lia. rewrite UB, UR. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [Run.init_config]'s model: [State.init_model] at the run stack pointer,
     with the launch's vDSO draw copied in by [State.with_vdso] — the wrapper
     [Run.init_config] applies and this definition used to omit. *)
  Definition model0 : Model :=
    with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT_S inp).

  Let cs0 := init_acs3 RS A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* The reserved ledger is NO LONGER just the image's segments.  At this
     revision [State.init_reserved] (State.v:7702-7707) appends the launch's
     vDSO reservation, and [State.vm_reserved_init_model] (:7830-7834) states
     the result; the old conjunct `= segments_reserved segs` is FALSE, not
     merely stale.  [with_vdso] rebuilds [mkVmState] around the SAME
     [m_vmmaps] (State.v:5019-5022), so it does not affect this. *)
  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0)
       = segments_reserved segs
         ++ vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps model0))
    /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT_S /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  (* The reserved conjunct is NOT [reflexivity]: [vdso_top] of this model is
     convertible to [page_round_down_Z (Z.min mbase (sp - stack_max_size))]
     only through [State.page_round_down_Z_min_r], which is what
     [State.vdso_top_init_model] and hence [State.vm_reserved_init_model]
     (State.v:7830-7837) carry.  Kept in the FOLDED [vdso_top] form because
     that is the shape the downstream [incl (vdso_reserved (m_kernel model)
     (vdso_top (m_vmmaps model))) (vm_reserved (m_vmmaps model))] obligation
     wants; [State.with_vdso] rebuilds [mkVmState] around the same
     [m_vmmaps] (State.v:5019-5022), so the wrapper is transparent here. *)
  Proof.
    repeat split; try reflexivity.
    exact (vm_reserved_init_model (segments_reserved segs) brk0 mbase sp LIMIT_S inp).
  Qed.

  (* [comment removed for export] *)
  Lemma alloc_top0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. unfold alloc_top. replace (vm_init_sp (m_vmmaps model0)) with sp by reflexivity. unfold stack_max_size, usp. lia. Qed.

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* At this revision [PropExec.wrap_mem]'s zero window under [sp] starts at
     [Run.stack_window_lo] = max (top - stack_max_size) (mbase + guard gap), not at
     [sp - stack_max_size].  [StoreOk.stack_window_lo_valid] bounds it by
     [sp + stack_window_reach - stack_max_size] = [sp - 6144513] (8388608 - 2244095),
     the window [stack_window_ok] below already states. *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs.
    pose proof (stack_window_lo_valid inp sp brk0 mbase rdraw Hvl Hlau) as Hwin.
    destruct (Z.leb_spec (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) as [H1|H1];
      [| unfold stack_window_reach, stack_max_size, usp in *; lia].
    destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned sp)) as [H2|H2]; [reflexivity | unfold usp in *; lia].
  Qed.

  (* Below [sp - stack_max_size] nothing is mapped: the window's floor is at least
     [top - stack_max_size], and [top] is above [sp] ([length_bsb_eq], [bsb_ge]). *)
  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs.
    assert (Hfl : bv_unsigned top - stack_max_size <= stack_window_lo (in_kernel inp) mbase rdraw)
      by (unfold stack_window_lo; lia).
    pose proof length_bsb_eq as HL. pose proof bsb_ge as [G _]. unfold stack_image_size in HL. unfold argc, envc in G.
    destruct (Z.leb_spec (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) as [H1|H1];
      [unfold stack_max_size, usp in *; lia | reflexivity].
  Qed.

  (* At or above [TASK_SIZE] the initial memory maps nothing: the stack block ends at
     [usp + length bsb <= 2^47] ([usp_fit], from the launch's [top <= sp_window_hi],
     [top_le]) and the zero window lies below [sp]. *)
  Lemma FULL0_task : forall a : word, TASK_SIZE <= bv_unsigned a -> FULL0 a = None.
  Proof.
    intros a Ha. pose proof usp_fit as F. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. destruct (Z.leb (bv_unsigned sp) (bv_unsigned a)); [|reflexivity].
      replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length SIMG))) with false; [reflexivity|].
      symmetry. apply Z.ltb_ge. unfold bsb, usp, TASK_SIZE in *. lia. }
    fold SIMG. rewrite Hs.
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with false by (symmetry; apply Z.ltb_ge; unfold usp, TASK_SIZE in *; lia).
    rewrite andb_false_r. reflexivity.
  Qed.

  (* Any memory [SINV0] admits, under an env whose stack pointer is [sp], maps nothing at
     or above [TASK_SIZE]: those bytes are in [argH0], so [SINV0] pins them to [FULL0]. *)
  Lemma SINV0_task : forall E M, SINV0 E M -> uE E e_sp0 = usp ->
    forall a : word, TASK_SIZE <= bv_unsigned a -> M a = None.
  Proof.
    intros E M [_ H2] U a Ha. rewrite (H2 a); [exact (FULL0_task a Ha)|].
    unfold argH0. cbv zeta. rewrite U, Z.eqb_refl. cbn [andb].
    apply orb_true_intro. right. apply Z.leb_le. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
    rewrite <- (rdn_wrap_stack_above segs inp mbase ph entryw sp rdraw a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp in *; lia | apply Hvis; exact Hx].
  Qed.

  Lemma split_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e ->
    bv_unsigned (edenot E b) + k = uE E e.
  Proof.
    intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) <= bv_unsigned a
       < usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)
         + Z.of_nat (launch_string_bytes argv envp execfn)
    \/ TASK_SIZE <= bv_unsigned a.
  Proof.
    intros a H. unfold argH0 in H. pose proof W_range as (W1 & W3).
    apply andb_prop in H as [_ H].
    apply orb_prop in H as [H|H]; [|right; right; apply Z.leb_le; exact H].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right; left]; lia.
  Qed.


  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16
     \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a
         < usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn))
     \/ usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)
        + Z.of_nat (launch_string_bytes argv envp execfn) <= bv_unsigned a < TASK_SIZE)
    -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _]. pose proof usp_fit.
    (* the string base sits above the whole head ([head_fit], [W_range]) *)
    pose proof head_fit as (_ & (HC1 & HC2) & _ & HCf & _). pose proof W_range as (W1 & W3).
    assert (HSO : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                  = Z.of_nat (block_head_size rseq argv envp) + W)
      by (unfold cat_string_off, W; lia).
    (* [StackLayout.block_pad_len]: the pad is what lies between the head and the
       strings, so the string base is [top - 8 - L] whenever that is above the head. *)
    pose proof top_le.
    assert (HW : W = Z.max 0 (bv_unsigned top - 8 - Z.of_nat (launch_string_bytes argv envp execfn)
                              - usp - Z.of_nat (block_head_size rseq argv envp)))
      by (unfold W, block_pad_len, usp; lia).
    unfold TASK_SIZE in *.
    destruct (Z.max_spec 0 (bv_unsigned top - 8 - Z.of_nat (launch_string_bytes argv envp execfn)
                              - usp - Z.of_nat (block_head_size rseq argv envp))) as [[_ EM]|[_ EM]];
      rewrite EM in HW;
      destruct H as [H|[H|H]]; destruct Ha as [Ha|[Ha|Ha]]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 Mr0 (KWord (SA b k) 8 v).
  Proof.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* The model's [auxv_words] takes EIGHT arguments at the checker's revision
     ([75d69e00:theories/LinuxProcessSem/Mh32]-side donor [Mh32.read_auxv_word],
     [Mh32.v:2227-2237]); this tree spelled four, which was its shape before the
     revision.  The worked application is [RefStartup.v:305-318], which discharges
     the section context with [lctx] rather than naming it -- that is what lets
     this file apply it without reconstructing the Section discharge list.
     UNITS: [j] below is a WORD index (bound [2 * auxv_count rseq], 54 or 58);
     [i] in [auxw_ok] is a PAIR index (bound [auxv_count rseq], 27 or 29).  The
     multiplier at each site is the tell: [8 * j] here, [16 * i] in [auxw]. *)
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hhi' ].

  Local Notation AUXW :=
    (auxv_words la ph entryw uid gid hw (at_random_ptr sp rseq argv envp)
       (at_execfn_ptr top execfn)) (only parsing).

  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    (* The vector now has [2 * auxv_count rseq] words (54 or 58), so the words lie
       inside the head by [head_fit] rather than by [bsb_ge]'s old 200-byte floor. *)
    pose proof head_fit as (HF1 & _ & _ & _ & HF5). pose proof W_range as (W1 & _).
    assert (HSO : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                  = Z.of_nat (block_head_size rseq argv envp) + W)
      by (unfold cat_string_off, W; lia).
    assert (HG0 : 0 <= GAP) by (unfold GAP; lia).
    assert (Hj58 : (j < 58)%nat) by (clear - Hj; unfold auxv_count in Hj; destruct (kb_rseq (in_kernel inp)); lia).
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
    - rewrite <- Hv. eapply read_auxv_word; first [ lctx | exact Hj ].
  Qed.

  (* The pair indices against [auxv_count] (27 or 29 pairs), without a case split on
     the section's [kb_rseq] term. *)
  Lemma auxv_idx_lit : forall (b : bool) (i : Z), 0 <= i <= 26 -> 0 <= i < Z.of_nat (auxv_count b).
  Proof. intros [] i H; cbn; lia. Qed.
  Lemma auxv_idx_null : forall b : bool, 0 <= 26 + 2 * rseq_z b < Z.of_nat (auxv_count b).
  Proof. intros []; cbn; lia. Qed.

  Lemma auxw_ok : forall i ty v,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
      apply auxv_word_ok; [lia|].
      rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia.
      apply auxv_word_ok; [lia|].
      exact H2.
  Qed.

  (* LPS 727298f3: a type word alone, for the pairs whose value stays unknown. *)
  Lemma auxt_ok : forall i ty,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty)).
  Proof.
    intros i ty Hi H1.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|].
    rewrite H1. reflexivity.
  Qed.

  (* LPS 727298f3: the whole vector is readable ([KUnk]); its bytes are stack-image
     bytes between the envp array and the AT_RANDOM block. *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RS))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof head_fit as (HCe & (HC1 & HC2) & _ & HCf & HCb).
    pose proof W_range as (W1 & W3).
    pose proof (AUXSZ_of rseq) as HA.
    assert (HAX : Z.of_nat (auxv_size rseq) = 16 * Z.of_nat (auxv_count rseq))
      by (unfold auxv_size; lia).
    assert (HAS : 432 <= AUXSZ RS <= 464)
      by (pose proof (rseq_z_range rseq); unfold AUXSZ; lia).
    assert (HSO : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                  = Z.of_nat (block_head_size rseq argv envp) + W)
      by (unfold cat_string_off, W; lia).
    assert (HG : 0 <= GAP <= 1).
    { unfold GAP. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. }
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (AUXSZ RS)) = AUXSZ RS) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia
                          | apply not_argH0; rewrite u64_lit; unfold usp, TASK_SIZE in *; lia].
    unfold FULL0. rewrite wrap_above_sp by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold bsb; lia).
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length SIMG)) with true
      by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
  Qed.

  Lemma stack_window_ok :
    (* 12i: the model certifies writes only from [MemSplit.wok_lo sp0 = sp0 - 6144513];
       the old 8388608 window claimed 2,244,095 bytes too much and was FALSE at the
       revision.  The proof is unchanged in shape -- it closes by [lia] against
       [usp_lo]/[usp_hi], and a NARROWER window is strictly easier to discharge. *)
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-6144513)) (ELit 6144513))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-6144513)) (ELit 6144513)).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-6144513)) = usp - 6144513).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 6144513) = 6144513) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-6144513)) (elenZ E0 (ELit 6144513))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN inp Hva). }
      rewrite <- Hv. apply RW. pose proof usp_fit as UF. unfold bsb, SIMG in UF. unfold usp in *. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RS)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 8 (e_str0 RS) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0 Hav0) as RW.
      (* [cat_argv_ptr] is (top) (av ev) (execfn) (k) at this revision
         (Common/CatExec.v:575), anchored at the stack VMA's end; its value is
         [sp + cat_string_off + bytes before k] by Mh32.RefLayout.u_cat_argv_ptr. *)
      assert (U : bv_unsigned (cat_argv_ptr top argv envp execfn 0)
                  = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn
                                    + total_arg_bytes_nat (firstn 0 argv)))
        by (eapply u_cat_argv_ptr with (ph := ph) (entry := entryw); first [lctx | exact Hlo' | exact Hav0]).
      assert (Hv : cat_argv_ptr top argv envp execfn 0 = edenot E0 (e_str0 RS)).
      { apply bv_eq. rewrite U.
        pose proof u_e_str0 as UE. unfold uE in UE. rewrite UE.
        replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity. lia. }
      rewrite <- Hv. apply RW. pose proof usp_fit as UF. unfold bsb, SIMG in UF. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RS)).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 (e_argv1w RS) = if (1 <? argc) then edenot E0 (e_str1 RS) else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 (e_str1 RS))).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 (e_argv1w RS) (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1 Hav1) as RW.
        assert (U : bv_unsigned (cat_argv_ptr top argv envp execfn 1)
                    = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn
                                      + total_arg_bytes_nat (firstn 1 argv)))
          by (eapply u_cat_argv_ptr with (ph := ph) (entry := entryw); first [lctx | exact Hlo' | exact Hav1]).
        assert (Hv : cat_argv_ptr top argv envp execfn 1 = edenot E0 (e_str1 RS)).
        { apply bv_eq. rewrite U.
          pose proof u_e_str1 as UE. unfold uE in UE. rewrite UE.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0. lia. }
        rewrite <- Hv. apply RW. pose proof usp_fit as UF. unfold bsb, SIMG in UF. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        assert (RW : rdn segs (stack_to_mem sp SIMG) (sp + nat_to_word (8 + 8 * length argv)) 8%nat
                     = Some (word_le8 (Z_to_bv 64 0)))
          by (eapply read_argv_null with (ph := ph) (entry := entryw); first [lctx | exact Hlo']).
        rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* Old beside new, and the OLD one is FALSE for every input:
       atrandom_byte : ... Mr0 (Z_to_bv 64 (usp + length bsb - 16 + i)) ...
       atrandom_byte : ... Mr0 (Z_to_bv 64 (usp + C - 16 + i)) ...,
                       C = block_head_size rseq argv envp
     It must be the same TERM as [u_e_atrandom]'s and [atrb_start]'s, not
     merely the same value, because [atrandom_unk_ok] and [atrandom_wr_ok]
     feed it to a goal [rewrite atrb_start] has already put over
     [block_head_size].
     THE DONOR WAS ALREADY IN THIS FILE'S CONTEXT AND THE OLD PROOF DID NOT
     USE IT: [Mh32.at_random_off]'s second conjunct is
     [off = (block_head_size rseq argv envp - 16)%nat]
     (an earlier revision of
      projects/glaze/binary_reflection/proofs/lib/Mh32.v:2316-2321, statement
      and proof, itself [StackLayout.at_random_ptr], StackLayout.v:425-427).
     It is bound here as [Hlen] -- a name left over from when that conjunct
     was a length fact -- and the old proof took the position from its own
     statement instead, which is exactly how the stale position survived.
     [at_random_ptr] TAKES THE FLAG at this revision; the three-argument
     spelling below was the pre-revision one. *)
  Lemma atrandom_byte : forall i, 0 <= i < 16 ->
    exists b, Mr0 (Z_to_bv 64 (usp + Z.of_nat (block_head_size rseq argv envp) - 16 + i)) = Some b.
  Proof.
    intros i Hi. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof bsb_ge as [G _]. pose proof head_fit as (_ & (HC1 & HC2) & _ & HCf & HCb).
    assert (HAR : exists off : nat, at_random_ptr sp rseq argv envp = (sp + nat_to_word off)%bv
                  /\ off = (block_head_size rseq argv envp - 16)%nat /\ (Z.of_nat off mod 8 = 0)%Z
                  /\ forall j n, (j + n <= 16)%nat ->
                       rdn segs (stack_to_mem sp SIMG) (at_random_ptr sp rseq argv envp + nat_to_word j)%bv n
                       = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))))
      by (eapply at_random_off with (ph := ph) (entry := entryw); first [lctx | exact Hlo']).
    destruct HAR as [off (Hp & Hlen & Hmod & Hrd)].
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    rewrite (BackingAlgebra.AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv
                 = Z_to_bv 64 (usp + Z.of_nat (block_head_size rseq argv envp) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    (* The random bytes lie in the head, below the pad and the strings. *)
    pose proof W_range as (W1 & _).
    assert (HSO : Z.of_nat (cat_string_off rseq sp top argv envp execfn)
                  = Z.of_nat (block_head_size rseq argv envp) + W)
      by (unfold cat_string_off, W; lia).
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp, TASK_SIZE in *; lia].
    unfold FULL0. rewrite wrap_above_sp by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (block_head_size rseq argv envp) - 16 + i))) as [b|] eqn:Hstk.
    - exists b. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (block_head_size rseq argv envp) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by apply Nat.le_refl.
      replace (usp + Z.of_nat (block_head_size rseq argv envp) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* Old beside new, and the OLD one cannot be repaired by re-measuring it:
       Hak : ak = 184
       Hak : ak = 24 + AUXSZ RS
     [ak] is [snd (e_atrb RS)], the literal part [split_lit] peels off
     [e_atrandom RS].  At this revision
       e_atrandom r = eadd (eaddz e_auxv (AUXSZ r)) (escale 8 (EVar V_G))
     (AzPlanCore.v:3621), and [e_auxv]'s own literals are 16 and 8
     (AzPlanCore.v:3613-3614, confirmed by u_e_auxv's "+ 24" above), so the
     literal part is 24 + AUXSZ r.  The old 184 was 24 + the old FIXED
     160-byte auxv, which is the same arithmetic over a constant that no
     longer exists.
     IT IS NOT A NUMBER ANY MORE, and that is the point: AUXSZ RS is
     432 + 32 * rseq_z rseq with [rseq] a Section variable, so the term is
     OPEN and `vm_compute; reflexivity` cannot decide it -- no round can
     ever report a single value for it.  456 at rseq = false, 488 at
     rseq = true.  Writing either literal would pin the flag and narrow the
     claim; writing their difference away is impossible.  So the assert is
     stated symbolically and the flag is CASE-SPLIT, with closed arithmetic
     in each branch -- rule 12's licensed shape, the same one AUXSZ_of
     (AzPlanCore.v:3607) uses.
     The two [lia] side conditions below need [ak]'s range rather than its
     value, which [rseq_z_range] supplies: 456 <= ak <= 488.
     THE CONCLUSION ALSO MOVED, not only the OFFSET (the [ak] assert).
     The POSITION [usp + length bsb - 16] is the pre-port statement's, and
     re-deriving the offset from the expression does not re-measure it: the
     position has to be measured on its own against the layout at this
     revision, as below.
     The position is one of the six false
     statements u_e_atrandom documents: the strings sit ABOVE the random
     bytes at this revision, so the block is at
     [usp + block_head_size - 16], not at the top minus sixteen.
     Derived here DIRECTLY from u_e_atrandom's four rewrites rather than by
     arithmetic off the old conclusion, so nothing wrong in the old form can
     be inherited. *)
  Lemma e_atrb_off : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
  Proof. intros [|]; vm_compute; reflexivity. Qed.
  Lemma auxv_count_rz : forall b, Z.of_nat (auxv_count b) = 27 + 2 * rseq_z b.
  Proof. intros [|]; reflexivity. Qed.
  (* The AT_NULL key, the vector's last pair, at pair index 26 + 2 r. *)
  Lemma auxv_null_key : forall la p0 e0 u0 g0 h0 ar ae,
    nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
        (flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la p0 e0 u0 g0 h0 ar ae))
        (Z_to_bv 64 0)
    = Z_to_bv 64 0.
  Proof. intros [ehdr c msz [|]] p0 e0 u0 g0 h0 ar ae; reflexivity. Qed.
  Lemma auxv_null_val : forall la p0 e0 u0 g0 h0 ar ae,
    nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
        (flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la p0 e0 u0 g0 h0 ar ae))
        (Z_to_bv 64 0)
    = Z_to_bv 64 0.
  Proof. intros [ehdr c msz [|]] p0 e0 u0 g0 h0 ar ae; reflexivity. Qed.
  (* The CONFIG_RSEQ pair (AT_RSEQ_FEATURE_SIZE 27 -> 28, AT_RSEQ_ALIGN 28 -> 32) at pair
     indices 26 and 27 when the flag is set ([StackLayout.auxv_entries]).  Closed, so the
     consumer cases on the boolean in its goal only, never on the section's flag term. *)
  Lemma auxv_idx_rseq : forall b : bool, (rseq_z b =? 1) = true -> 0 <= 27 < Z.of_nat (auxv_count b).
  Proof using. intros [] E; vm_compute in E |- *; [split; first [discriminate | reflexivity] | discriminate E]. Qed.
  Lemma auxv_rseq_words : forall la p0 e0 u0 g0 h0 ar ae,
    (rseq_z (la_rseq la) =? 1) = true ->
    nth (Z.to_nat (2 * 26))
        (flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la p0 e0 u0 g0 h0 ar ae))
        (Z_to_bv 64 0) = Z_to_bv 64 27
    /\ nth (Z.to_nat (2 * 26 + 1))
        (flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la p0 e0 u0 g0 h0 ar ae))
        (Z_to_bv 64 0) = Z_to_bv 64 28
    /\ nth (Z.to_nat (2 * 27))
        (flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la p0 e0 u0 g0 h0 ar ae))
        (Z_to_bv 64 0) = Z_to_bv 64 28
    /\ nth (Z.to_nat (2 * 27 + 1))
        (flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries la p0 e0 u0 g0 h0 ar ae))
        (Z_to_bv 64 0) = Z_to_bv 64 32.
  Proof using.
    intros [ehdr c msz [|]] p0 e0 u0 g0 h0 ar ae E; [| vm_compute in E; discriminate E].
    split; [reflexivity | split; [reflexivity | split; reflexivity]].
  Qed.

  Lemma atrb_start : estart E0 (SA (fst (e_atrb RS)) (snd (e_atrb RS)))
    = usp + Z.of_nat (block_head_size rseq argv envp) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof (rseq_z_range rseq) as HR.
    assert (Hab : split_lit (e_atrandom RS) = (fst (e_atrb RS), snd (e_atrb RS)))
      by (unfold e_atrb; destruct (split_lit (e_atrandom RS)); reflexivity).
    set (ab := fst (e_atrb RS)) in *. set (ak := snd (e_atrb RS)) in *.
    pose proof (split_u E0 (e_atrandom RS) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RS) by (subst ak; apply e_atrb_off).
    unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)). unfold estart; cbn [a_base a_off]. lia.
  Qed.

  Lemma atrandom_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst (e_atrb RS)) (snd (e_atrb RS))) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof head_fit as (_ & (HC1 & HC2) & _ & HCf & _).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite atrb_start, Hl.
    split; [unfold flat; rewrite atrb_start; unfold usp in *; lia|].
    intros i Hi. destruct (atrandom_byte i Hi) as [b Hb]. rewrite Hb. discriminate.
  Qed.

  Lemma atrandom_wr_ok : kentry_ok segs E0 Mr0 (KWr (SA (fst (e_atrb RS)) (snd (e_atrb RS))) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof head_fit as (_ & (HC1 & HC2) & _ & HCf & _).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite atrb_start, Hl.
    split; [unfold flat; rewrite atrb_start; unfold usp in *; lia|].
    intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by (unfold usp in *; lia); [unfold usp in *; lia|].
    intros x Hx. unfold wview.
    destruct (atrandom_byte (bv_unsigned x - (usp + Z.of_nat (block_head_size rseq argv envp) - 16)) ltac:(lia)) as [b Hb].
    replace (Z_to_bv 64 (usp + Z.of_nat (block_head_size rseq argv envp) - 16
                         + (bv_unsigned x - (usp + Z.of_nat (block_head_size rseq argv envp) - 16)))) with x in Hb
      by (apply bv_eq; rewrite u64_lit; [lia | pose proof (u64_range x); lia]).
    rewrite Hb. discriminate.
  Qed.

  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  (* [at_random_ptr] takes the CONFIG_RSEQ flag at this revision
     (StackLayout.v:425-427); the three-argument spelling was pre-revision.
     The position comes from [u_e_atrandom] and [Mh32.at_random_off]'s
     [off = C - 16], which agree by construction now that both are over
     [block_head_size]. *)
  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RS).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof head_fit as (_ & (HC1 & HC2) & _ & HCf & _).
    assert (HAR : exists off : nat, at_random_ptr sp rseq argv envp = (sp + nat_to_word off)%bv
                  /\ off = (block_head_size rseq argv envp - 16)%nat /\ (Z.of_nat off mod 8 = 0)%Z
                  /\ forall j n, (j + n <= 16)%nat ->
                       rdn segs (stack_to_mem sp SIMG) (at_random_ptr sp rseq argv envp + nat_to_word j)%bv n
                       = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))))
      by (eapply at_random_off with (ph := ph) (entry := entryw); first [lctx | exact Hlo']).
    destruct HAR as [off (Hp & Hlen & Hmod & _)].
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
  Qed.

  Lemma init_kn3_ok : know_ok segs E0 Mr0 (init_kn3 RS A).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W3).
    pose proof head_fit as (HCe & (HC1 & HC2) & HCm & HCf & HCb).
    pose proof (rseq_z_range rseq) as HR.
    (* [auxv_count] in closed form, ONCE, for the whole table.  [e_atr8]'s own
       KRange upper bound is [0xFFFFFFFFFC3 - 4 * r] (AsStartupTabs.v:81, :90)
       and it is TIGHT: with [head_fit]'s [usp + C <= 2^47 - 16] and [HCe],
       [usp/8 + argc + envc + GAP <= 2^44 - 7 - 2*auxv_count rseq], which meets
       [2^44 - 61 - 4*r] exactly and only because [auxv_count rseq = 27 + 2*r].
       An rseq-free bound misses it by two. *)
    assert (HN : Z.of_nat (auxv_count rseq) = 27 + 2 * RS)
      by apply auxv_count_rz.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as [G _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3). pose proof usp_al.
    pose proof TV_range as [[T1 T2] [T3 T4]]. pose proof PV_range as ([Q1 Q2] & [Q3 Q4] & [Q5 Q6]).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hmod : usp mod 32768 = usp - 32768 * (usp / 32768)) by lia.
    assert (HG : 0 <= GAP <= 1).
    { unfold GAP. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. }
    clearbody W TV PV BV R8V.   (* [comment removed for export] *)
    unfold init_kn3.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; unfold uE; rewrite uE0_hw; pose proof Hhw as HW'; unfold valid_hwcap, hwcap_rv64gc, hwcap_rv64gcv in HW';
                          destruct HW' as [HW' | HW']; rewrite HW'; rewrite u64_lit by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_T; lia|].
      apply Forall_cons.
      { apply kr_ok. unfold eaddz, esub, escale, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
        rewrite u_add64, u_sub64, !u_mul64, !u64_lit by lia.
        pose proof uE0_T as UT; unfold uE in UT; unfold uE in U2; rewrite U2, UT.
        rewrite (Z.mod_small (16 * _)) by lia. rewrite (Z.mod_small (4096 * _)) by lia.
        rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [apply kr_ok; rewrite uE0_P; lia|].
      apply Forall_cons.
      { apply kr_ok. unfold esub, escale, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
        rewrite u_sub64, !u_mul64, !u64_lit by lia.
        pose proof uE0_P as UP; unfold uE in UP; unfold uE in U2; rewrite U2, UP.
        rewrite (Z.mod_small (16 * _)) by lia. rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons.
      { apply kr_ok. unfold esub, uE. rewrite mkAlu_denot, u_sub64.
        pose proof uE0_T as UT; pose proof uE0_P as UP; unfold uE in UT, UP; rewrite UT, UP. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons.
      { apply kr_ok. unfold uE. cbn [edenot]. rewrite u_sub64.
        pose proof u_e_sp0 as US; pose proof u_ISPD as UI; unfold uE in US, UI; rewrite US, UI. rewrite Z.mod_small by lia. lia. }
      pose proof BV_range as ([BV1 BV2] & [BV3 BV4] & BV5).
      apply Forall_cons; [apply kr_ok; rewrite uE0_R8; lia|].
      apply Forall_cons.
      { apply kr_ok. unfold eadd, uE. rewrite mkAlu_denot, u_add64.
        pose proof u_e_atr8 as UA; pose proof uE0_R8 as UR; unfold uE in UA, UR; rewrite UA, UR. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [apply kr_ok; rewrite u_e_bend64; lia|].
      apply Forall_cons.
      { (* THE 64-ALIGNMENT ENTRY, AND THE PLAN SIDE OF IT MOVES WITH THIS
           PROOF.  AsStartupTabs.v:91's entry before this revision is
             KRange (AND (V_ARGC + (V_ENVC + (V_W + 2*V_S2))) 7 + V_R8) 7 7,
           i.e. [R8V = 7 - ((argc + envc + W + 2*b) mod 8)].  That is EXACTLY
           [e_bend64]'s 64-alignment UNDER THE OLD LAYOUT, and it reproduces
           the old arithmetic term for term, which identifies it as the
           old entry: with W the string WORDS below
           the random bytes, [length bsb = 8*(argc + envc + 25 + W)], so
           [(usp + length bsb)/8 mod 8 = 2b + argc + envc + W + 1] and the
           entry reads off exactly.
           IT IS FALSE UNDER BOTH READINGS OF [R8V], so it is dead in the old
           text -- its old discharge here goes through [W_range]'s DELETED
           middle conjunct and could not have closed either:
           - over the image top (the pre-restatement [R8V]): [top] is page
             aligned, so [R8V] was identically 0 and the entry asserts
             [(argc + envc + W + 2b) mod 8 = 7], which nothing forces --
             [W mod 8 = (- L) mod 8] and L is free;
           - over [block_head_size]: the pad drops out of the position
             entirely, because it is ABOVE the random bytes now.
           Both sides now read
             (usp + C)/8 = 4096*S1 + 2b + argc + envc + GAP
                           + 2*auxv_count rseq + 5,
           with [2*auxv_count rseq = 54 + 4*RS], giving
             R8V = 7 - ((argc + envc + GAP + 2*b + 2 + 4*RS) mod 8).
           AsStartupTabs.v:91 is restated to match, by
           the same derivation; it is that table's only prover
           (`git grep -n init_kn3 -- proofs/lib` names AsSInit.v alone, with
           AsStartupTabs.v's own definition as the control).
           The operand is now spelled as the code computes it,
           ((argc + (envc + (2*b + GAP))) + (2 + 4*RS)): s1_planTb's respell
           of the shadow address matches this entry only in that spelling. *)
        apply kr_ok. unfold eadd, uE. rewrite mkAlu_denot. cbn [edenot].
        pose proof uE0_R8 as UR. pose proof uE0_G as UG.
        unfold uE in UR, UG, U3, U4, U2. cbn [edenot] in UR, UG, U3, U4, U2.
        rewrite u_add64, u_and64, !u_add64, u_mul64, !u64_lit by lia. rewrite UR, UG, U3, U4, U2.
        rewrite (Z.mod_small (2 * _)) by lia. rewrite (Z.mod_small (2 * _ + _)) by lia.
        rewrite (Z.mod_small (envc + _)) by lia. rewrite (Z.mod_small (argc + _)) by lia.
        rewrite (Z.mod_small (_ + (2 + 4 * RS))) by lia.
        replace (Z.land (argc + (envc + (2 * (usp mod 32768 / 16) + GAP)) + (2 + 4 * RS)) 7)
          with (Z.land (argc + (envc + (2 * (usp mod 32768 / 16) + GAP)) + (2 + 4 * RS)) (Z.ones 3)) by reflexivity.
        rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        set (b := usp mod 32768 / 16) in *.
        assert (Hu : usp = 32768 * (usp / 32768) + 16 * b) by (subst b; lia).
        (* [HA] was here; [HN] in the preamble subsumes it. *)
        (* The environment's own equation over [block_head_size].  It replaces
           [8 * BV = 4096*(usp/32768) + 2*b + W + argc + envc + 25 + R8V],
           which was already underivable here: its route ran through
           [W_range]'s deleted middle conjunct, the one that equated the pad
           with an image-length expression built on the old 184 offset.
           Three linear facts and nothing else: [BV_range]'s [BV5]
           (64*BV = usp + C + 8*R8V), [head_fit]'s [HCe] (C in closed form)
           and [Hu] (usp split at the 32768 boundary).  No unfolding, which
           is what kept the old version fragile. *)
        assert (H8 : 8 * BV = 4096 * (usp / 32768) + 2 * b + argc + envc + GAP
                              + 2 * Z.of_nat (auxv_count rseq) + 5 + R8V) by lia.
        assert (HM : (argc + (envc + (2 * b + GAP)) + (2 + 4 * RS)) mod 8 = 7 - R8V).
        { replace (argc + (envc + (2 * b + GAP)) + (2 + 4 * RS))
            with ((7 - R8V) + (BV - 512 * (usp / 32768) - 8) * 8) by lia.
          rewrite Z.mod_add, Z.mod_small by lia. reflexivity. }
        rewrite HM. rewrite Z.mod_small by lia. lia. }
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons;
        [apply kr_ok; rewrite uE0_G; unfold GAP;
         pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    1-10: apply auxw_ok; [first [apply auxv_idx_null | apply auxv_idx_lit; lia] | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    1: exact (auxv_null_key (launch_auxv inp sp mbase) _ _ _ _ _ _ _).
    1: rewrite edenot_lit; exact (auxv_null_val (launch_auxv inp sp mbase) _ _ _ _ _ _ _).
    apply Forall_cons; [exact atrandom_unk_ok|].
    apply Forall_cons; [exact atrandom_wr_ok|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
    (* LPS 727298f3: the pairs musl's [__init_libc] loop also reads, from
       [StackLayout.auxv_entries]: AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY (the ELF
       entry, [Hapc]), AT_GID / AT_EGID ([V_GID] = [in_gid inp]). *)
    1-6: apply auxw_ok; [first [apply auxv_idx_null | apply auxv_idx_lit; lia] | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, Hapc; reflexivity.
    (* the vector readable, and the type words of the pairs whose value stays unknown *)
    apply Forall_cons; [exact auxv_unk_ok|].
    repeat (apply Forall_cons;
            [apply auxt_ok; [first [apply auxv_idx_null | apply auxv_idx_lit; lia]
                            | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; reflexivity] |]).
    apply Forall_nil.
    (* the CONFIG_RSEQ pair (AT_RSEQ_FEATURE_SIZE 28, AT_RSEQ_ALIGN 32), claimed when the flag is set.
       A case on the boolean in the goal only, never on the section's [kb_rseq] term (the
       section's [Let]s, [cs0] among them, mention it); each branch by a closed lemma. *)
    destruct (rseq_z (kb_rseq (in_kernel inp)) =? 1) eqn:E; [| apply Forall_nil].
    pose proof (auxv_idx_rseq _ E) as HI.
    pose proof (auxv_rseq_words (launch_auxv inp sp mbase) ph entryw uid gid hw
                  (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn) E)
      as (A52 & A53 & A54 & A55).
    apply Forall_app; split;
      (apply auxw_ok;
       [ lia
       | rewrite auxv_words_eq; first [exact A52 | exact A54]
       | rewrite auxv_words_eq, edenot_lit; first [exact A53 | exact A55] ]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  Lemma init_regs_ok : regs_ok E0 init_regs R0.
  Proof.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; clear - H2; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  Lemma allowA_init : allowA A E0 cs0 =
    flat_map (allow1 A E0) (init_vis3 RS A).
  Proof. unfold allowA, cs0, init_acs3. cbn [a_vis a_ghost]. rewrite app_nil_r. reflexivity. Qed.

  Lemma A_bytes_app : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
  Proof. induction l1 as [|[a b] l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.

  (* [comment removed for export] *)
  Lemma allow1_cost : forall p n, 0 <= uE E0 (snd p) <= n -> 0 <= uE E0 (fst p) -> uE E0 (fst p) mod 8 = 0 -> 0 <= shadow_off A ->
    A_bytes (allow1 A E0 p) <= vis_cost n.
  Proof.
    intros [b l] n Hn Hb Hal HS. clearbody W TV PV BV R8V.   (* [comment removed for export] *)
    unfold allow1, sh_lo, sh_hi. cbn [fst snd A_bytes] in *. unfold vis_cost.
    pose proof (pageup_minus_pagedown (uE E0 b) (uE E0 b + uE E0 l) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + uE E0 b / 8) (shadow_off A + (uE E0 b + uE E0 l) / 8) ltac:(lia)).
    assert ((uE E0 b + uE E0 l) / 8 - uE E0 b / 8 <= n / 8) by (apply Z.le_trans with ((uE E0 b + n) / 8 - uE E0 b / 8); [apply Z.sub_le_mono_r; apply Z.div_le_mono; lia | lia]).
    lia.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= init_abytes A /\ init_abytes A <= LIMIT_S.
  Proof.
    clearbody W TV PV BV R8V.   (* [comment removed for export] *)
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    pose proof TV_range as [[T1 T2] [T3 T4]]. pose proof usp_al.
    rewrite allowA_init. unfold init_vis3. cbn [flat_map]. rewrite !A_bytes_app. cbn [A_bytes app]. rewrite Z.add_0_r.
    unfold init_abytes. split; [| unfold vis_cost, LIMIT_S, STACK_MAX, WBLK2_LEN; rewrite StoreOk.RunLim.LMIN_val; lia].   (* [comment removed for export] *)
    assert (NEG8 : bv_unsigned (Z_to_bv 64 (- STACK_MAX)) = 2 ^ 64 - 8388608) by (rewrite Z_to_bv_unsigned; reflexivity).
    assert (NEG4 : bv_unsigned (Z_to_bv 64 (- WBLK2_LEN)) = 2 ^ 64 - 4194304) by (rewrite Z_to_bv_unsigned; reflexivity).
    assert (USP8 : uE E0 (EAlu Instr.ALU_ADD e_sp0 (ELit (- STACK_MAX))) = usp - 8388608).
    { pose proof u_e_sp0 as US. unfold uE in *. cbn [edenot]. rewrite u_add64, NEG8, US.
      replace (usp + (2 ^ 64 - 8388608)) with ((usp - 8388608) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
    assert (TOP8 : uE E0 (EAlu Instr.ALU_ADD e_top (ELit (- STACK_MAX))) = 32768 * (usp / 32768) + 4096 * TV - 8388608).
    { pose proof u_e_top as UT. unfold uE in *. cbn [edenot]. rewrite u_add64, NEG8, UT.
      replace (32768 * (usp / 32768) + 4096 * TV + (2 ^ 64 - 8388608)) with ((32768 * (usp / 32768) + 4096 * TV - 8388608) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia. }
    pose proof BV_range as ([BV1 BV2] & [BV3 BV4] & BV5).
    assert (BEND4 : uE E0 (eaddz (e_bend64 RS) (- WBLK2_LEN)) = 64 * BV - 4194304).
    { pose proof u_e_bend64 as UB. unfold eaddz, uE in *. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, NEG4, UB.
      replace (64 * BV + (2 ^ 64 - 4194304)) with ((64 * BV - 4194304) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia. }
    assert (LIT : forall z, 0 <= z < 2 ^ 64 -> uE E0 (ELit z) = z) by (intros z Hz; unfold uE; rewrite edenot_lit, u64_lit by lia; reflexivity).
    pose proof bsb_ge as [_ GM].
    assert (C1 : A_bytes (allow1 A E0 (ELit (img_lo A), ELit (img_hi A - img_lo A))) <= vis_cost (img_hi A - img_lo A)).
    { apply allow1_cost; cbn [fst snd]; rewrite ?LIT by lia; lia. }
    assert (C2 : A_bytes (allow1 A E0 (EAlu Instr.ALU_ADD e_sp0 (ELit (- STACK_MAX)), ELit STACK_MAX)) <= vis_cost STACK_MAX).
    { apply allow1_cost; cbn [fst snd]; rewrite ?USP8, ?LIT by (unfold STACK_MAX; lia); unfold STACK_MAX; lia. }
    assert (C3 : A_bytes (allow1 A E0 (EAlu Instr.ALU_ADD e_top (ELit (- STACK_MAX)), ELit STACK_MAX)) <= vis_cost STACK_MAX).
    { apply allow1_cost; cbn [fst snd]; rewrite ?TOP8, ?LIT by (unfold STACK_MAX; lia); unfold STACK_MAX; lia. }
    assert (C4 : A_bytes (allow1 A E0 (eaddz (e_bend64 RS) (- WBLK2_LEN), ELit WBLK2_LEN)) <= vis_cost WBLK2_LEN).
    { apply allow1_cost; cbn [fst snd]; rewrite ?BEND4, ?LIT by (unfold WBLK2_LEN; lia); unfold WBLK2_LEN; lia. }
    lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIMIT_S SINV0 argH0 ISP_S fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2]. pose proof usp_lo. pose proof usp_hi.
    constructor; cbn [cs0 init_acs3 a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_meter a_fake a_fbud];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn3_ok.
    - reflexivity.
    - reflexivity.     (* [comment removed for export] *)
    - reflexivity.
    - reflexivity.
    - (* co_res (AzAPS.cs_ok's three parts) at the start state, proved as
         DrvRootP.VM0_init and MhInv.reserved_layout_vdso prove the vDSO pair's
         layout: the pair sits below [vdso_top = page_round_down_Z (Z.min mbase
         (sp - stack_max_size))] (State.vdso_top_init_model), which the launch's
         valid_mmap_base and valid_sp put in [mmap_base_min, 2^47 - page_size];
         each entry is page aligned and inside [top - vdso_len, top)
         (State.vdso_reserved_entry_ok, State.vdso_len_bounds); no map yet (M5);
         the pair is the ledger's tail (M4). *)
      pose proof Hmb as HMB. unfold valid_mmap_base in HMB. destruct HMB as (Hmblo & Hmbhi & _).
      pose proof Hsp as HSP. unfold valid_sp in HSP. destruct HSP as (Hsplo & Hsphi & _).
      assert (Hrange : mmap_base_min <= Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) < 2 ^ 47).
      { split.
        - apply Z.min_glb; [exact Hmblo|]. unfold mmap_base_min, stack_max_size, sp_window_lo in *. lia.
        - pose proof (Z.le_min_l (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
          unfold mmap_base_max, sp_window_hi in Hmbhi. lia. }
      pose proof (page_round_down_Z_within mmap_base_min (2 ^ 47)
                    (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))
                    eq_refl eq_refl Hrange) as (Htoplo & Htophi).
      assert (VT : vdso_top (m_vmmaps model0)
                   = page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))
        by exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT_S inp).
      assert (VA : vdso_top (m_vmmaps model0) mod page_size = 0)
        by (rewrite VT; unfold page_round_down_Z; apply Z_mod_mult).
      pose proof (vdso_len_bounds (in_kernel inp)) as VL.
      rewrite ?M4, ?M5. change (m_kernel model0) with (in_kernel inp).
      split; [|split].
      + exists (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps model0))).
        split; [reflexivity|]. split; [|split].
        * apply Forall_forall. intros [a n] Hin.
          destruct (vdso_reserved_entry_ok (in_kernel inp) (vdso_top (m_vmmaps model0)) a n
                      ltac:(unfold page_size, mmap_base_min in *; lia)
                      ltac:(unfold two_pow_64, page_size in *; lia) VA Hin) as (HN & HA & HS & HLO & HHI).
          unfold APS.resx_entry_ok. cbn [fst snd]. unfold page_size, APC.KHI, mmap_base_min in *.
          repeat split; try assumption; lia.
        * unfold vdso_reserved, APS.n_resx. cbv zeta.
          destruct (vdso_top (m_vmmaps model0) - vdso_len (in_kernel inp) <? page_size); cbn; lia.
        * pose proof (APS.sum_sizes_vdso_bound [] (in_kernel inp) (vdso_top (m_vmmaps model0))) as V.
          cbn [app sum_sizes] in V. lia.
      + constructor.
      + apply incl_appr, incl_refl.
    - reflexivity.
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - intros z Hz. exact Hz.   (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - (* co_totsz.  [vm_reserved] here is [segments_reserved segs ++ vdso_reserved
         (in_kernel inp) (vdso_top (m_vmmaps model0))] -- M4, rewritten at :1470 --
         NOT the image's segments alone, so the vDSO tail must be charged.
         [if_sizes] supplies the image half and is left BARE on purpose: it bounds
         the IMAGE's own list and widening it to [vm_reserved] would make it false. *)
      rewrite app_nil_r.
      eapply Z.le_trans; [apply APS.sum_sizes_vdso_bound|].
      rewrite (if_sizes _ _ _ IMG).
      unfold APC.resx_budget, APS.resx_bytes, APS.p_resx. cbn. lia.
    - unfold ISP_S. rewrite edenot_e_sp0. reflexivity.   (* [comment removed for export] *)
    - split; [unfold model0; apply init_sp_ok_init_model; exact Hsp | cbn; exact Hhi'].   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.   (* [comment removed for export] *)
    - cbn. lia.        (* [comment removed for export] *)
    - lia.             (* [comment removed for export] *)
    - exact AB1.       (* [comment removed for export] *)
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].   (* [comment removed for export] *)
    - intros a _ Hm. cbn in Hm. discriminate Hm.   (* [comment removed for export] *)
    - intros a Hm _. cbn in Hm. discriminate Hm.   (* [comment removed for export] *)
    - intros a Hp. cbn in Hp. discriminate Hp.     (* [comment removed for export] *)
    - split; [intros; reflexivity | intros a Ha; reflexivity].   (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - constructor.     (* [comment removed for export] *)
    - (* co_rdr: [model0] is [with_vdso … (init_model … inp)] and [init_model]
         seeds [procst_channel_reader] from [in_channel_reader inp]
         (State.v:7781), so the goal is [Hrdr] up to conversion. *)
      exact Hrdr.
  Qed.




  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition model0_at (LIM : Z) : Model :=
    with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIM inp).


  Lemma model0_at_facts : forall LIM,
    m_halted (model0_at LIM) = None /\ m_fds (model0_at LIM) = fds_std /\ m_tid (model0_at LIM) = None
    /\ vm_reserved (m_vmmaps (model0_at LIM))
       = segments_reserved segs
         ++ vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps (model0_at LIM)))
    /\ vm_maps (m_vmmaps (model0_at LIM)) = []
    /\ vm_noaccess (m_vmmaps (model0_at LIM)) = [] /\ m_vm_lazy (model0_at LIM) = [] /\ m_vm_materialized (model0_at LIM) = []
    /\ vm_limit (m_vmmaps (model0_at LIM)) = LIM /\ vm_brk (m_vmmaps (model0_at LIM)) = brk0 /\ vm_start_brk (m_vmmaps (model0_at LIM)) = brk0
    /\ vm_mmap_base (m_vmmaps (model0_at LIM)) = mbase /\ eager_used (model0_at LIM) = 0
    /\ alloc_top (m_vmmaps (model0_at LIM)) = alloc_top (m_vmmaps model0) /\ vm_init_sp (m_vmmaps (model0_at LIM)) = sp.
  Proof.
    intros LIM. repeat split; try reflexivity.
    exact (vm_reserved_init_model (segments_reserved segs) brk0 mbase sp LIM inp).
  Qed.

  (* [comment removed for export] *)
  Lemma hid_at : forall LIM, hid A argH0 E0 cs0 (model0_at LIM) = hid A argH0 E0 cs0 model0.
  Proof. intros LIM. reflexivity. Qed.
  Lemma Mr_at : forall LIM, Mr A argH0 E0 cs0 (model0_at LIM) FULL0 = Mr A argH0 E0 cs0 model0 FULL0.
  Proof. intros LIM. reflexivity. Qed.

  Theorem init_cs_ok_at : forall LIM : Z, LIMIT_S <= LIM -> cs_ok segs A LIMIT_S SINV0 argH0 ISP_S fs E0 cs0 R0 FULL0 (model0_at LIM).
  Proof.
    intros LIM HLIM. pose proof init_cs_ok as H.
    destruct (model0_at_facts LIM) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15).
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    destruct H; constructor; rewrite ?hid_at, ?Mr_at, ?N1, ?N2, ?N3, ?N4, ?N5, ?N6, ?N7, ?N8, ?N9, ?N10, ?N11, ?N12, ?N14, ?N15;
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M10, ?M11, ?M12 in *; try assumption; try exact HLIM.
    all: try exact Hrdr.   (* co_rdr: [model0_at LIM] and [model0] share [m_proc] *)
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- MInv _ _ =>
             lazymatch goal with MI : MInv _ model0 |- _ =>
               destruct MI as [_ _ _ _ B5]; constructor; rewrite ?N7, ?N8, ?N9, ?N13;
                 [constructor | intros p [] | intros p [] | intros p [] | rewrite M9, M13 in B5; lia] end
         | |- model_ivs_wf _ =>
             unfold model_ivs_wf; rewrite N5, N6, N7; repeat split; try (intros q []); unfold model0_at; apply init_sp_ok_init_model; exact Hsp
         | |- init_sp_ok _ /\ _ =>
             split; [unfold model0_at; apply init_sp_ok_init_model; exact Hsp |];
             lazymatch goal with I : init_sp_ok _ /\ _ |- _ => exact (proj2 I) end
         | |- fds_ok _ _ _ => lazymatch goal with F : fds_ok _ _ model0 |- _ => exact F end
         | |- _ = edenot _ ISP_S => lazymatch goal with I : _ = edenot _ ISP_S |- _ => exact I end
         | |- _ <= a_eager _ => lazymatch goal with EG : _ <= a_eager _ |- _ => rewrite M13 in EG; exact EG end
         end.
  Qed.

  (* [apc] is a Section variable now — the auxv carries AT_ENTRY — so the pc
     is no longer this theorem's own quantifier and [Hapc] is the Section
     hypothesis that ties it to the table's entry. *)
  Theorem init_cfg_eq_at : forall LIM : Z,
    init_config segs apc ph sp brk0 mbase rdraw LIM inp = cfg_of segs R0 (a_entry A) FULL0 (model0_at LIM).
  Proof.
    intros LIM. unfold init_config, cfg_of, FULL0, model0_at. rewrite init_mkst, Hapc. reflexivity.
  Qed.
  Theorem init_cfg_eqF_at : forall LIM : Z,
    init_config segs apc ph sp brk0 mbase rdraw LIM inp = GPS.cfgF segs fx0 R0 (a_entry A) FULL0 (model0_at LIM).
  Proof. intros LIM. rewrite (init_cfg_eq_at LIM). reflexivity. Qed.
End Init.
