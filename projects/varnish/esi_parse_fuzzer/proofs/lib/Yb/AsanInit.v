(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the twenty-field process input (kernel build, exec file name, stdout reader, SIGPIPE disposition), the entry stack Linux lays (the 27/29-pair auxv, STACK_ROUND's gap, the strings above the AT_RANDOM bytes, the arch_align_stack pad), the initial model with the launch's vDSO draw and reserved pair, the zero window below sp at the depth every launch gives, and the start state's facts about the rest of the auxv (every type word, the values the launch fixes, AT_GID and AT_EGID as the group id in a new thirteenth slot of the initial valuation, the CONFIG_RSEQ pair, the whole vector readable); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Starulm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starulm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.RefL1zx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.ArgvEnv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asancq9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Back4sr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac chkp_cleanup :=
  repeat
    (repeat match goal with
       | [ H : (0 <= ?x < _)%Z |- _ ] =>
          destruct H;
          try (lazymatch type of H with (* [comment removed for export] *)
            | (0 <= x < _)%Z => clear H (* [comment removed for export] *)
          end)
          (* [comment removed for export] *)
       end;
     repeat match goal with
       | [ H : (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
       | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
       | [ H : ?A -> (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
       | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       end;
     repeat match goal with
       | [ H : ?x = ?x -> ?Q |- _ ] => specialize (H eq_refl)
       | [ H : ?T -> ?Q, H' : ?T |- _ ] => specialize (H H')
       | [ H : ?A -> ?x = ?x -> ?Q |- _ ] => specialize (fun a => H a eq_refl)
       | [ H : ?A -> ?B -> ?Q, H' : ?B |- _ ] => specialize (fun a => H a H')
       | [ H : (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : ?A -> (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
       | [ H : ?A -> (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
       end).
Local Ltac nia := Zify.zify; chkp_cleanup; xnia zchecker.
Local Ltac liac := Zify.zify; chkp_cleanup; xlia zchecker.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

(* [comment removed for export] *)
Class BootLim : Type := mkBootLim { blim : Z ; blim_ge : 2 ^ 34 <= blim }.
Definition LIMIT_S : Z := source_alloc_limit.
Lemma LIMIT_ge34 : 2 ^ 34 <= LIMIT.
Proof. vm_compute. discriminate. Qed.
Lemma LIMIT_S_ge34 : 2 ^ 34 <= LIMIT_S.
Proof. vm_compute. discriminate. Qed.
Definition BL_T : BootLim := {| blim := LIMIT ; blim_ge := LIMIT_ge34 |}.
Definition BL_S : BootLim := {| blim := LIMIT_S ; blim_ge := LIMIT_S_ge34 |}.

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

(* The EXACT size of the initial stack image.  At LPS 727298f3 the image is
   Linux's whole block, from the entry stack pointer to the stack VMA's end
   [ed_top] ([Run.entry_stack_image], [PropExec.length_entry_stack_image_launch]),
   so its size is a function of (sp, top).  It WAS a sum over (argv, envp) with
   the old 160-byte auxv and the strings inside the block, which is false now. *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* AT_NULL closes the vector: pair 28 with CONFIG_RSEQ, pair 26 without
   ([StackLayout.auxv_entries]), so its two words are [2 * (26 + 2 * r)] and one
   more, at the flag's [r = rseq_z (la_rseq la)].  Model form:
   [theories/Common/AsanInit.v] at 727298f3, [auxv_words_null]. *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

(* The CONFIG_RSEQ pair, pairs 26 and 27, when the flag is set
   ([StackLayout.auxv_entries]): AT_RSEQ_FEATURE_SIZE (27) = 28 and
   AT_RSEQ_ALIGN (28) = 32. *)
Lemma auxv_words_rseq : forall la ph entry uid gid hw ar ae,
  la_rseq la = true ->
  nth (Z.to_nat (2 * 26)) (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 27
  /\ nth (Z.to_nat (2 * 26 + 1)) (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth (Z.to_nat (2 * 27)) (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 28
  /\ nth (Z.to_nat (2 * 27 + 1)) (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 32.
Proof.
  intros [ehdr c msz r] ph entry uid gid hw ar ae Hr. cbn [la_rseq] in Hr. subst r.
  split; [|split; [|split]]; reflexivity.
Qed.

(* The AT_RANDOM block's literal offset off [e_atrb]'s base: the argc slot, the
   two NULLs (24) and the auxv itself, under BOTH layouts: 456 without
   CONFIG_RSEQ, 488 with it.  It WAS the single literal 184 (the old 160-byte
   auxv). *)
Lemma e_atrb_off : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* the entry draw: ed_random = the AT_RANDOM bytes, ed_top = the stack VMA's end, ed_vdso = the vDSO draw *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  (* [comment removed for export] *)
  Variables nofile sigmask : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variable urandom : InputStream.
  (* LPS 727298f3 widened [State.mkProcInput_full] from fifteen places to twenty.
     The three new places the published statements leave free are Section
     variables, so every launch [Run.valid_input] admits is an instance:
     - [kb], the kernel build ([in_kernel]): its CONFIG_RSEQ flag fixes the
       auxv's size, its vDSO the reserved pair, its ASLR switch the stack window;
     - [execfn], the exec file name ([in_execfn]): AT_EXECFN and the top of the
       string area; [Run.valid_input] constrains it only through [valid_launch];
     - [sigdfl], the SIGPIPE disposition at exec ([in_sigpipe_default]), which
       [Run.valid_input] leaves free and [State.init_model] reads.
     The two places [Run.valid_input] pins ([in_channel_reader = true],
     [in_sigpipe_terminal = false]) are literals in [inp]; [init_config_inp_of]
     below takes them as premises, and so does every caller, from
     [Run.valid_input]. *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sigdfl : bool.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hhw : valid_hwcap hw.

  (* [comment removed for export] *)
  Definition inp : ProcInput :=
    mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urandom []
      kb execfn true sigdfl false.
  (* [Run.valid_input]'s [valid_launch] conjunct: the exec file name is one
     [execve] admits and the launch fits under E2BIG. *)
  Hypothesis Hlaunch : valid_launch inp.
  (* [Run.valid_entry]'s FIFTH conjunct: the start state is exactly a Linux
     launch.  It pins the stack VMA's end, the entry stack pointer inside the
     [arch_align_stack] window and the mmap base, so it is what bounds the pad
     [V_W] and the image's length. *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  (* THE STACK'S VIEW OF THE INPUT.  The entry stack image and the zero window
     below sp read only argv, envp, the exec file name, uid, gid, AT_HWCAP and
     the kernel build ([Run.entry_stack_image], [Run.stack_window_lo]); the
     other fields are fixed here so that [SINV0], which the plan carries
     through every node, is a function of those and not of the whole input.
     [wrap_mem_stk] is the tie, by conversion. *)
  Definition stk_inp : ProcInput :=
    mkProcInput_full argv envp [] IEof uid gid [] net_silent default_nofile (Z_to_bv 64 0) hw false Sv48
      default_urandom [] kb execfn true true false.

  (* the image's ELF entry as the auxv's AT_ENTRY: [init_cfg_eq] ties it to the
     run's pc through [Z.of_N apc = a_entry A] *)
  Let entryw : word := Z_to_bv 64 (a_entry A).
  (* the run's CONFIG_RSEQ flag, and the plan's 0 or 1 for it *)
  Let rseq : bool := kb_rseq kb.
  Let RZ : Z := rseq_z rseq.
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  Let top : word := ed_top rdraw.
  (* the mapped image IS Linux's block, sp .. [ed_top] *)
  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let utop := bv_unsigned top.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [StackLayout.block_items mod 2]: the 8-byte gap [STACK_ROUND] clears below
     the AT_RANDOM block, in words: the plan's [V_G] *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* C, sp to the top of the AT_RANDOM bytes *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* L, the string bytes with their NULs, the exec file name included *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  (* V_W CHANGED MEANING: it is now the [arch_align_stack] pad between the
     AT_RANDOM bytes and argv[0], in BYTES.  It WAS a count of string words, the
     strings sitting just above the auxv. *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* argv[0]'s first byte: the string area is at the TOP of the block now *)
  Let STR0 := usp + CHEAD + W.

  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.

  Lemma wrap_mem_stk : wrap_mem stk_inp mbase ph entryw sp rdraw = wrap_mem inp mbase ph entryw sp rdraw.
  Proof using. reflexivity. Qed.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 32768) / 16); Z_to_bv 64 L1; uid; hw;   (* [comment removed for export] *)
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 G;   (* the twelfth slot is [V_G] (index 11; [V_T0] is 10) *)
     gid].   (* the thirteenth is [V_GID] (index 12): AT_GID and AT_EGID's value *)
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* The hidden argument bytes: the envp pointer array (with its NULL) and the
     string area, now [STR0 .. ed_top) at the top of the block.  It WAS
     [usp + 8*argc + 8*envc + 184 .. + 8*W], the strings just above the old
     auxv. *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    (((usp + 8 * argc + 16 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
     || ((STR0 <=? z) && (z <? utop)))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem stk_inp mbase ph entryw sp rdraw a).

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

  (* [Run.entry_stack_fits]'s span still counts the OLD 160-byte auxv (it is a
     lower bound on Linux's block), so it bounds sp with no launch premise. *)
  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof.
    pose proof len_av. pose proof len_ev.
    pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
    unfold entry_stack_fits, entry_stack_span, sp_window_hi in Hfit.
    unfold usp, argc, envc in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a.
  Proof using Hsp Hva.
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    pose proof (valid_argv_len argv Hva).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold STR0, usp, argc, envc in H; lia.
  Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof using. intros E E' a _. reflexivity. Qed.

  (* [comment removed for export] *)

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof using. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof using.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range rseq). Qed.

  (* the vector's length, the ONE case split on the flag the arithmetic needs *)
  Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
  Proof. unfold RZ, rseq, rseq_z, auxv_count. destruct (kb_rseq kb); reflexivity. Qed.

  Lemma gap_range : 0 <= G <= 1.
  Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  (* C = 8*items + AUXSZ RZ + 8*g + 16, with items = argc + envc + 3 and the auxv
     [AUXSZ RZ = 432 + 32 * RZ] bytes: 29 entries with CONFIG_RSEQ, 27 without *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * G.
  Proof.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA. change (rseq_z rseq) with RZ in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items.
    lia.
  Qed.

  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof.
    pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  (* L >= 2: argv[0]'s NUL and the exec file name's NUL are both in the string
     area ([copy_strings] / [copy_string_kernel], fs/exec.c, Linux v6.18.46). *)
  Lemma lstr_lo : 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma s0_in_strings : L0 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* the pad as a closed form, with no launch premise: [block_pad_len] is a
     [Z.to_nat] of [top - 8 - L - sp - C] *)
  Lemma W_def : W = Z.max 0 (utop - 8 - LSTR - usp - CHEAD).
  Proof.
    unfold W, block_pad_len, utop, LSTR, usp, CHEAD. lia.
  Qed.

  Lemma W_bnd : 0 <= W /\ usp + CHEAD + W < 2 ^ 64.
  Proof.
    pose proof W_def. pose proof usp_hi. pose proof chead_range. pose proof lstr_lo.
    pose proof (u64_range top) as [T1 T2]. unfold utop in *. lia.
  Qed.

  (* [Run.valid_input]'s E2BIG half, in this file's names *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (* The pad [arch_align_stack] left.  [launch_sp_hi] is [align_down16(top - 8 - L) - C]
     and [launch_sp_lo] the same with [top - 8 - L - 4095], so the pad is r
     (0..4095) plus the remainder the low-four-bit mask leaves: at most 4110. *)
  Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
  Proof.
    destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    rewrite inp_argv, inp_envp, inp_execfn, inp_rseq in Hslo, Hshi.
    change (ed_top rdraw) with top in Hslo, Hshi.
    fold LSTR in Hslo, Hshi. fold CHEAD in Hslo, Hshi. fold utop usp in Hslo, Hshi.
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR - 4095) 16 ltac:(lia)).
    lia.
  Qed.

  Lemma pad_eq : W = utop - 8 - LSTR - usp - CHEAD.
  Proof. pose proof pad_bounds_Z. pose proof W_def. lia. Qed.

  (* REPLACES the old [W_range]'s [W <= 280000], the old word-count bound *)
  Lemma pad_range : 0 <= W <= 4110.
  Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.

  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size sp top.
  Proof.
    unfold bsb, stack_image_size.
    exact (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma length_bsb_sum : Z.of_nat (length bsb) = CHEAD + W + LSTR + 8.
  Proof.
    pose proof pad_eq. rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. lia.
  Qed.

  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof.
    unfold usp, bsb.
    exact (entry_stack_image_no_wrap Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  (* the stack VMA's end is at or below [va_stack_top Sv48 = sp_window_hi = 2^47]
     ([Run.valid_stack_top_va], the launch's first conjunct) *)
  Lemma utop_hi : utop <= 2 ^ 47.
  Proof.
    destruct Hlau as (Htop & _ & _). destruct Htop as (_ & Hhi & _).
    cbn [va_stack_top] in Hhi. unfold sp_window_hi in Hhi. unfold utop, top. lia.
  Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. pose proof utop_hi. lia.
  Qed.

  (* Everything the block holds: the pointer vector (8*items), the auxv (at
     least 432), the gap, the random bytes, the pad, the strings (at least two
     NULs) and the eight-byte slot.  Stated at the smaller layout so it holds for
     both.  It WAS [8*argc + 8*envc + 200 <= |bsb|] with a mod-8 conjunct for the
     old word-count [W]; that conjunct has no consumer left. *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof. unfold STR0. pose proof pad_eq. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 32768) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof using Hsp Hva Hve Hfit.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_bnd as [W1 W2].
    pose proof chead_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  (* [comment removed for export] *)

  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  (* the valuation of [V_GID], the thirteenth slot: the group id *)
  Lemma uE0_gid : edenot E0 (EVar V_GID) = gid.
  Proof. reflexivity. Qed.

  (* the valuation of the plan's [V_G], the twelfth slot; [uE0] covers only the
     seven variables the pre-revision plan had *)
  Lemma uE0_G : uE E0 (EVar V_G) = G.
  Proof.
    pose proof gap_range. unfold uE. cbn [edenot E0 ev nth vals0 V_G].
    rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof using Hsp Hva Hve Hfit.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof using Hsp Hva Hve Hfit. apply bv_eq. exact u_e_sp0. Qed.

  (* [comment removed for export] *)
  Lemma uE0_t0 : uE E0 (EVar V_T0) = (usp mod 32768) / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold uE. cbn [edenot E0 ev nth vals0 V_T0].
    rewrite u64_lit by lia. reflexivity.
  Qed.
  Lemma u_e_pgsp0 : uE E0 e_pgsp0 = pagedown usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_t0 as UT.
    unfold e_pgsp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, UT. unfold pagedown.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_e_link : uE E0 (esub (escale 16 (EVar V_S2)) (escale 4096 (EVar V_T0))) = usp mod 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (_ & U2 & _). pose proof uE0_t0 as UT.
    unfold esub, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [alu64 alu]. rewrite bv_sub_unsigned.
    rewrite !u_mul64, !u64_lit by lia. rewrite U2, UT. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite !(Z.mod_small (16 * _)) by lia. rewrite !(Z.mod_small (4096 * _)) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argH0_top : forall E M a, SINV0 E M -> argH0 E a = true -> uE E e_sp0 <= bv_unsigned a.
  Proof using Hsp Hva Hve Hfit.
    intros E M a [H1 _] Ha. pose proof len_av. pose proof len_ev.
    assert (HC : 0 <= CHEAD) by (unfold CHEAD; lia).
    assert (HW : 0 <= W) by (unfold W; lia).
    assert (US : uE E e_sp0 = usp).
    { rewrite <- u_e_sp0. unfold uE, e_sp0, eadd, escale. rewrite !mkAlu_denot, !mkMd_denot. cbn [edenot].
      rewrite (H1 V_S1) by (unfold V_S1, NX0; lia). rewrite (H1 V_S2) by (unfold V_S2, NX0; lia). reflexivity. }
    rewrite US. unfold argH0 in Ha.
    apply orb_prop in Ha as [Ha|Ha]; apply andb_prop in Ha as [Ha _]; apply Z.leb_le in Ha; unfold STR0 in Ha; lia.
  Qed.

  Lemma u_sp8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof using Hsp Hva Hve Hfit.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof using Hsp Hva Hve Hfit.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* STATEMENT CHANGED: the AT_RANDOM bytes sit at the top of the HEAD,
     [usp + CHEAD - 16], not at the top of the image; it WAS
     [uE E0 e_atrandom = usp + |bsb| - 16]. *)
  Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
  Proof using Hsp Hva Hve Hfit.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof u_e_auxv as UA. pose proof uE0_G as UG.
    unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UG.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* STATEMENT CHANGED: argv[0] is at [STR0 = usp + CHEAD + W], above the random
     bytes and the pad; it WAS [usp + 8*argc + 8*envc + 184]. *)
  Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
  Proof using Hsp Hva Hve Hfit.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range. pose proof W_bnd as [W1 W2].
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA.
    unfold e_str0, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6.
    rewrite !Z.mod_small by lia. unfold STR0. lia.
  Qed.

  (* argv[1] is argv[0] + L0 + 1; below 2^64 because the string area ends at
     [ed_top <= 2^47] (the launch premise) *)
  Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
  Proof using Hsp Hva Hve Hfit Hlau.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof chead_range. pose proof W_bnd as [W1 W2]. pose proof str0_hi. pose proof s0_in_strings. pose proof utop_hi.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5.
    rewrite !Z.mod_small by (unfold STR0 in *; lia). lia.
  Qed.

  (* STATEMENT CHANGED: [e_atr8] reads [V_G] where it read [V_W] (the auxv's size
     cancels out of it); it WAS [usp / 8 + argc + envc + W]. *)
  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & _). pose proof uE0_G as UG.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U3, U4, UG.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  Context {BL : BootLim}.   (* [comment removed for export] *)
  (* STATEMENT CHANGED: [Run.init_config]'s model at LPS 727298f3 carries the
     launch's vDSO draw ([with_vdso (vdso_run_init (ed_vdso draw))]).  [with_vdso]
     rebuilds only the VM subsystem's vDSO field, so [m_vmmaps], [m_kernel],
     [m_vm_lazy], [m_vm_materialized] and [m_proc] keep their values by
     computation and [model0_facts] still closes by [reflexivity]. *)
  Definition model0 : Model :=
    with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp blim inp).  (* [comment removed for export] *)

  Let cs0 := init_acs_of RZ A.
  Let cs0z := init_acs_of_zero RZ A.   (* [comment removed for export] *)
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* THE LAUNCH'S RESERVED LEDGER is the image's reservations AND the vDSO pair
     ([State.init_reserved]), placed below [VTOP], the page-rounded lower of the
     mmap base and the allocation top. *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved kb VTOP.

  (* STATEMENT CHANGED: the ledger conjunct WAS [= segments_reserved segs], which
     is false at every launch of the revision; conjunct ORDER is unchanged. *)
  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = blim /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

  Lemma vdso_top_model0 : vdso_top (m_vmmaps model0) = VTOP.
  Proof. exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp blim inp). Qed.

  Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
  Proof.
    induction l1 as [|iv l1 IH]; intro l2; cbn [app sum_sizes]; [lia|]. rewrite IH. lia.
  Qed.

  Lemma mb_range : mmap_base_min <= bv_unsigned mbase <= mmap_base_max
                   /\ bv_unsigned mbase mod page_size = 0.
  Proof. destruct Hmb as (Y1 & Y2 & Y3). repeat split; assumption. Qed.

  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (* the pair, for EVERY kernel build: four vvar pages, then one to sixteen text
     pages ([State.vdso_text_pages_pos] / [_le]).  Stated through [vdso_len] and
     [vdso_text_pages], not computed at one build: [kb] is free. *)
  Lemma resx_shape :
    RESX = [(Z_to_bv 64 (VTOP - vdso_len kb), Z_to_bv 64 (vdso_vvar_pages * page_size));
            (Z_to_bv 64 (VTOP - vdso_len kb + vdso_vvar_pages * page_size),
             Z_to_bv 64 (vdso_text_pages kb * page_size))].
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof (vdso_len_bounds kb).
    assert (Hb : (VTOP - vdso_len kb <? page_size) = false)
      by (apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    (* [vdso_reserved]'s [let base := ..] by conversion, so the test is the
       syntactic [Hb] whatever the reduction flags do to section [Let]s *)
    change RESX with
      (if (VTOP - vdso_len kb <? page_size) then []
       else [(Z_to_bv 64 (VTOP - vdso_len kb), Z_to_bv 64 (vdso_vvar_pages * page_size));
             (Z_to_bv 64 (VTOP - vdso_len kb + vdso_vvar_pages * page_size),
              Z_to_bv 64 (vdso_text_pages kb * page_size))]).
    rewrite Hb. reflexivity.
  Qed.

  Lemma resx_len : (length RESX <= NRESX)%nat.
  Proof. rewrite resx_shape. cbn [length]. unfold NRESX. lia. Qed.

  Lemma resx_sum : sum_sizes RESX = vdso_len kb.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
    rewrite resx_shape. cbn [sum_sizes fst snd].
    unfold vdso_len, vdso_vvar_pages, page_size in *.
    rewrite !u64_lit by lia. lia.
  Qed.

  Lemma resx_ok : Forall (resx_entry_ok A) RESX.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
    pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
    rewrite resx_shape. unfold resx_entry_ok, vdso_len, vdso_vvar_pages, page_size in *.
    repeat constructor; cbn [fst snd];
      rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_top_model0 : alloc_top (m_vmmaps model0) = usp - 8388608.
  Proof. reflexivity. Qed.

  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APS.in_hull A (bv_unsigned a) || (usp - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite alloc_top_model0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  (* STATEMENT CHANGED: [PropExec.wrap_mem] zero-fills only down to
     [Run.stack_window_lo (in_kernel inp) mbase rdraw], the larger of
     [ed_top - stack_max_size] and the mmap base plus the guard gap.  [ed_top] is
     above sp, so the old [usp - 8388608] window is FALSE at every launch.
     6144513 is [StoreOk.stack_window_depth] ([stack_window_depth_val]), what
     [StoreOk.stack_window_lo_valid] guarantees at every kernel build. *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
                 <= bv_unsigned sp + stack_window_reach - stack_max_size)
      by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hlaunch Hlau).
    assert (Hs : stack_to_mem sp bsb a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold bsb. rewrite Hs.
    unfold stack_window_reach, stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  (* STATEMENT UNCHANGED at 8388608: [stack_window_lo_ge_sp] gives
     [sp - stack_max_size <= stack_window_lo], so nothing below the old window is
     filled either. *)
  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    pose proof (stack_window_lo_ge_sp inp sp brk0 mbase rdraw Hlau) as HW.
    assert (Hs : stack_to_mem sp bsb a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold bsb. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp bsb) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold bsb.
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

  (* STATEMENT CHANGED, following [argH0]: the string area is [STR0 .. utop). *)
  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  (* the complement: below the envp pointers, between them and argv[0], and at or
     above the stack VMA's end *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 8 * argc + 16 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof gap_range. pose proof RZ_range.
    pose proof W_bnd as [W1 W2]. pose proof str0_hi. pose proof lstr_lo. unfold STR0 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp bsb) w 8%nat = Some (word_le8 (edenot E0 v)) ->
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

  (* the auxv words the launch wrote *)
  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* STATEMENT CHANGED: the vector is [2 * auxv_count rseq] words (58 with
     CONFIG_RSEQ, 54 without) of the eight-argument [auxv_words]; it WAS
     [(j < 20)] over the old four-argument [auxv_words]. *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    pose proof auxv_count_RZ. pose proof str0_hi. pose proof pad_eq.
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
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold STR0 in *. lia.
    - rewrite <- Hv.
      exact (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hj).
  Qed.

  (* STATEMENT CHANGED for [auxv_word_ok]'s reasons: the pair index ranges over
     [auxv_count rseq] (27 or 29), not 0..9. *)
  Lemma auxw_ok : forall i ty v,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* STATEMENT CHANGED with [FULL0_below]: the window is 6144513 deep. *)
  Lemma Mr0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
  Qed.

  (* STATEMENT CHANGED: the plan's zero window ([Asanz3l.init_kn_with]) is
     6144513 deep below sp; it WAS 8388608, false at every launch of the revision
     (see [FULL0_below]). *)
  Lemma stack_window_ok :
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
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof RZ_range. pose proof str0_hi. pose proof pad_eq.
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* argv[0]'s address as the launch wrote it: the bottom of the string area,
     [cat_string_off] bytes above sp ([MmapSim.CatExec.cat_string_base_offset]). *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
    pose proof lstr_lo.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
    change (in_argv inp) with argv. change (in_envp inp) with envp.
    unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof RZ_range. pose proof str0_hi. pose proof pad_eq.
    apply (kword_stack e_sp0 8 (e_str0 RZ) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp, STR0 in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 (e_str0 RZ)).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RZ)).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof RZ_range. pose proof str0_hi. pose proof pad_eq.
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 (e_argv1w RZ) = if (1 <? argc) then edenot E0 (e_str1 RZ) else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 (e_str1 RZ))).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 (e_argv1w RZ) (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp, STR0 in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 (e_str1 RZ)).
        { apply bv_eq.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U. pose proof s0_in_strings. pose proof lstr_lo.
          rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
          rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
          change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
          change (in_argv inp) with argv. change (in_envp inp) with envp.
          rewrite U. unfold STR0, CHEAD, W, usp, L0, rseq, top, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* STATEMENT UNCHANGED; three steps inside it moved with the layout: the block's
     literal offset is [24 + AUXSZ RZ] ([e_atrb_off]), its start is
     [usp + CHEAD - 16] (the top of the HEAD, not of the image), and so is the
     launch's [at_random_ptr]. *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
    set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
    pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by exact (e_atrb_off rseq). unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd.
    rewrite (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp, STR0 in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp bsb (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length bsb)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* [comment removed for export] *)

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

  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof chead_range. pose proof gap_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb. pose proof RZ_range.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* AT_NULL, the one claimed pair whose index moves with the flag: pair
     [26 + 2 * RZ] ([auxv_words_null]). *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (auxv_words_null la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
    apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
  Qed.

  (* The rest of the vector, [Asanz3l.auxv_rest]: the same route as fuzz_bigint's
     [AsanInitK.v] ([auxt_ok], [auxv_unk_ok], [auxv_rseq_ok], [auxv_rest_ok]). *)
  (* a type word alone (the pairs whose value stays unknown) *)
  Lemma auxt_ok : forall i ty,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty)).
  Proof.
    intros i ty Hi H1.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
  Qed.

  (* the whole vector is readable ([KUnk]): it is visible block memory below
     argv[0], [usp + 8*argc + 8*envc + 24] for [AUXSZ RZ] bytes *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    (* [STR0] is an atom here; [str0_hi] with [pad_eq] give it a value, as in [auxv_word_ok] *)
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (AUXSZ RZ)) = AUXSZ RZ) by (apply elenZ_lit; unfold AUXSZ; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. unfold AUXSZ in *.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold bsb.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length bsb)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* the CONFIG_RSEQ pair (26, 27), claimed only at [RZ = 1], where it is in the
     vector ([auxv_words_rseq]) *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb RZ 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (Z.eqb RZ 1) eqn:HR; [| exact (Forall_nil _)].
    apply Z.eqb_eq in HR.
    assert (Hr : la_rseq la = true).
    { (* [la_rseq la] converts to [rseq] through [launch_auxv] and [in_kernel inp] *)
      change (la_rseq la) with rseq.
      destruct (Bool.bool_dec rseq true) as [Hb|Hb]; [exact Hb|].
      apply Bool.not_true_is_false in Hb. unfold RZ in HR. rewrite Hb in HR. cbn in HR. discriminate HR. }
    destruct (auxv_words_rseq la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn) Hr) as (N1 & N2 & N3 & N4).
    apply Forall_app; split.
    - apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
    - apply auxw_ok; [lia | exact N3 | rewrite edenot_lit; exact N4].
  Qed.

  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest RZ A).
  Proof.
    pose proof RZ_range. pose proof auxv_count_RZ.
    unfold auxv_rest.
    apply Forall_app; split.
    { (* the eleven type words, pairs 0..9 and 25 (AT_EXECFN): below the
         CONFIG_RSEQ pair, the same words under both layouts *)
      do 11 (apply Forall_cons;
        [ apply auxt_ok;
          [ lia
          | unfold AUXW, auxv_words, auxv_entries;
            cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
            reflexivity ]
        | ]).
      apply Forall_nil. }
    (* AT_CLKTCK (12), AT_BASE (16), AT_FLAGS (17), AT_ENTRY (18), AT_GID (21),
       AT_EGID (22): below the CONFIG_RSEQ pair; AT_ENTRY's value is [entryw],
       AT_GID's and AT_EGID's are [gid], the [V_GID] slot of [vals0] *)
    do 6 (apply Forall_app; split;
      [ apply auxw_ok;
        [ lia
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          reflexivity
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          first [ reflexivity | (rewrite edenot_lit; reflexivity) | (symmetry; exact uE0_gid) ] ]
      | ]).
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_cons; [exact auxv_unk_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof pad_range. pose proof gap_range. pose proof chead_range.
    (* [usp_fit] bounds [usp + |bsb|]; the AT_RANDOM range's [<= 2^47] and the
       [e_atr8] bound are stated in [CHEAD], so [length_bsb_sum] connects them *)
    pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range. pose proof auxv_count_RZ.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as Gb. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    (* [auxv_rest] is proved apart ([auxv_rest_ok]); hiding it keeps the
       [Forall_app] split below from opening it *)
    remember (auxv_rest RZ A) as REST eqn:EREST.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite uE0_t0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_link; pose proof usp_al; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_pgsp0; unfold pagedown; lia|].
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
      apply Forall_cons; [apply kr_ok; unfold uE; cbn [edenot E0 ev nth vals0 V_HW];
                          assert (Hh : bv_unsigned hw = 0x112D \/ bv_unsigned hw = 0x20112D)
                            by (destruct Hhw as [Hq|Hq]; rewrite Hq; [left|right]; reflexivity); lia |].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_G; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* AT_NULL (pair [26 + 2 * RZ]): its index is symbolic in the free flag *)
    10: exact auxv_null_ok.
    (* AT_RANDOM (pair 24): its value is the plan's [e_atrandom RZ], equal only by [atr_ptr_eq] *)
    9: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           reflexivity
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           exact atr_ptr_eq ].
    (* pairs 13 (AT_PHDR), 14, 15, 10 (AT_HWCAP), 11 (AT_PAGESZ), 19 (AT_UID), 20 (AT_EUID),
       23 (AT_SECURE): all below the CONFIG_RSEQ pair, the same words under both layouts *)
    1-8: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           try reflexivity .. ].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
    rewrite EREST. exact auxv_rest_ok.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.


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
        do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pusp_bounds : usp - 4080 <= pagedown usp <= usp /\ 0x7fff80000000 <= pagedown usp /\ pagedown usp mod 4096 = 0.
  Proof. pose proof usp_lo. pose proof usp_hi. pose proof usp_al. unfold pagedown.
    lia.
  Qed.
  Lemma u_band_lo : uE E0 (eaddz e_pgsp0 (-8388608)) = pagedown usp - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof pusp_bounds as (PB1 & PB2 & PB3). pose proof u_e_pgsp0 as US. unfold eaddz, uE in *.
    rewrite mkAlu_denot, edenot_lit, u_add64, US.
    change (bv_unsigned (Z_to_bv 64 (-8388608))) with (2 ^ 64 - 8388608).
    replace (pagedown usp + (2 ^ 64 - 8388608)) with ((pagedown usp - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.
  Lemma u_band_len : uE E0 e_band_len = 2 ^ 47 + 8388608 - pagedown usp.   (* [comment removed for export] *)
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof pusp_bounds as (PB1 & PB2 & PB3). pose proof u_e_pgsp0 as US. unfold e_band_len, esub, uE in *.
    rewrite mkAlu_denot, edenot_lit. cbn [alu64 alu]. rewrite bv_sub_unsigned, US, u64_lit by lia.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (pagedown usp - 8388608), pageup ((pagedown usp - 8388608) + (2 ^ 47 + 8388608 - pagedown usp)));
     (pagedown (shadow_off A + (pagedown usp - 8388608) / 8), pageup (shadow_off A + ((pagedown usp - 8388608) + (2 ^ 47 + 8388608 - pagedown usp)) / 8))].   (* [comment removed for export] *)
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_band_lo, !u_band_len.
    unfold uE. rewrite !edenot_lit, !u64_lit by (unfold CEIL; lia). reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 + 8388608 - CEIL)
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 + 8388608 - CEIL) <= blim.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_lo. pose proof usp_hi.
    pose proof pusp_bounds as (PB1 & PB2 & PB3).   (* [comment removed for export] *)
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, CEIL. pose proof (blim_ge) as HBL.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    replace (pagedown usp - 8388608 + (2 ^ 47 + 8388608 - pagedown usp)) with (2 ^ 47) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    rewrite (P2 (2 ^ 47) eq_refl).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (pagedown usp - 8388608) / 8) (shadow_off A + (2 ^ 47) / 8) ltac:(lia)).
    assert (PD : pagedown usp - 8388608 - 4096 <= pagedown (pagedown usp - 8388608)) by (unfold pagedown; lia).
    split; lia.
  Qed.

  (* Signature pinned by [Proof using All]: every Section variable and hypothesis
     in declaration order, [BL] implicit: segs A ph sp rdraw brk0 mbase argv envp
     fs stdin uid gid nofile sigmask hw groups net urandom kb execfn sigdfl IMG Hsp
     Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau {BL}. *)
  Theorem init_cs_ok : cs_ok segs A blim SINV0 argH0 fs E0 cs0 R0 FULL0 model0.
  Proof using All.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - (* [m_fs model0] is [in_fs inp] = [fs_seed_tmp fs []], which is [fs] by computation *)
      reflexivity.
    - reflexivity.
    - (* co_res: the launch reserves the vDSO pair beside the image.  The witness is
         [RESX]: the ledger equation is [model0_facts]'s conjunct, the geometry
         [resx_ok], the count [resx_len], the size [vdso_len kb <= 20 pages]
         ([State.vdso_len_bounds]), at every kernel build. *)
      exists RESX. split; [reflexivity|].
      split; [exact resx_ok|].
      split; [exact resx_len|].
      rewrite resx_sum. pose proof (vdso_len_bounds kb). unfold RESX_BYTES, page_size in *. lia.
    - (* co_vd: the pair [vdso_reserved (m_kernel model0) (vdso_top (m_vmmaps model0))] IS
         [RESX]: the kernel is [kb] by computation and [vdso_top] of the initial
         ledger is [VTOP] ([State.vdso_top_init_model]). *)
      intros e He. rewrite vdso_top_model0 in He. apply in_or_app. right. exact He.
    - (* co_rdr: [in_channel_reader inp] is [true] ([Run.valid_input]'s value, a premise
         of [init_config_inp_of]) *)
      reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (intros q []).
      exact (init_sp_ok_init_model (segments_reserved segs) brk0 mbase sp blim inp Hsp).  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* co_totsz: the image's reservations and the vDSO pair, within [img + RESX_BYTES] *)
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof (vdso_len_bounds kb). unfold RESX_BYTES, page_size in *. lia.
    - exact I.   (* [comment removed for export] *)
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - (* co_sinv: [SINV0] reads the stack through [stk_inp], the same bytes ([wrap_mem_stk]) *)
      split; [intros; reflexivity | intros a _; exact (f_equal (fun f => f a) (eq_sym wrap_mem_stk))].
    - (* [comment removed for export] *) rewrite alloc_top_model0, u_e_sp0. lia.
    - (* [comment removed for export] *) rewrite alloc_top_model0, u_e_pgsp0. pose proof usp_lo. unfold pagedown. lia.
    - (* [comment removed for export] *) intros z Hz. discriminate Hz.
    - (* [comment removed for export] *) rewrite alloc_top_model0. destruct Hsp as (_ & Hhi & _). unfold sp_window_hi in Hhi. unfold usp, TOPMAX. lia.
    - (* [comment removed for export] *) constructor.
    - (* co_mres: no tracked mapping at start *)
      constructor.
  Qed.


  (* [comment removed for export] *)
  (* The entry stays a quantified [apc] with [Z.of_N apc = a_entry A]: the stack
     image's AT_ENTRY is [Z_to_bv 64 (a_entry A)] here ([entryw]), which the
     equation rewrites [init_config]'s [Z_to_bv 64 (Z.of_N apc)] to.  Signature
     pinned by [Proof using]: segs A ph sp rdraw brk0 mbase argv envp fs stdin uid
     gid nofile sigmask hw groups net urandom kb execfn sigdfl {BL}, then apc Hpc. *)
  Theorem init_cfg_eq : forall apc : N, Z.of_N apc = a_entry A ->
    init_config segs apc ph sp brk0 mbase rdraw blim inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof using.
    intros apc Hpc. unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp]. rewrite init_mkst. rewrite Hpc. reflexivity.
  Qed.
End Init.

(* [comment removed for export] *)
(* The bridge from a published input to this file's [inp].  [Run.valid_input]
   gives the three premises (its [in_abort_terminal], [in_channel_reader] and
   [in_sigpipe_terminal] conjuncts).  [init_config] reads the input's filesystem
   only through [in_fs], which [inp] takes whole (seeded with the declared /tmp,
   and an empty declaration on top of it is the same filesystem), and it never
   reads [in_va_size]. *)
Lemma init_config_inp_of : forall segs pc ph sp brk0 mbase rdraw lim (i : ProcInput),
  in_abort_terminal i = false -> in_channel_reader i = true -> in_sigpipe_terminal i = false ->
  init_config segs pc ph sp brk0 mbase rdraw lim
    (inp (in_argv i) (in_envp i) (in_fs i) (in_stdin i) (in_uid i) (in_gid i) (in_nofile i) (in_sigmask i) (in_hwcap i)
         (in_groups i) (in_net i) (in_urandom i) (in_kernel i) (in_execfn i) (in_sigpipe_default i))
  = init_config segs pc ph sp brk0 mbase rdraw lim i.
Proof.
  intros segs pc ph sp brk0 mbase rdraw lim i Hab Hrd Hst.
  destruct i as [argv envp ifs stdin uid gid groups net nofile sigmask hw abt va urnd tmp kb execfn rdr sgd sgt].
  cbn in Hab, Hrd, Hst. subst abt rdr sgt.
  reflexivity.   (* by conversion: [init_config] unfolds, and [in_fs] of the rebuilt input is
                    [fs_seed_tmp (fs_seed_tmp ifs tmp) []], which reduces to [fs_seed_tmp ifs tmp] *)
Qed.
