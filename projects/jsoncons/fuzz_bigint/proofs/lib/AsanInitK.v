(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the initial state takes the full launch input (kernel build, exec file name, gid, groups, network queue, SIGPIPE disposition) and the image's entry pc with the launch facts (valid_launch, entry_launch_ok_va), the model starts with the vDSO pair (with_vdso) and the launch's extra reservations in its reserved ledger, the stack image is Linux's block from sp to the stack mapping's top with the strings at its top, the arch_align_stack pad (V_W), STACK_ROUND's gap (V_G) and an auxv of 27 or 29 pairs by the run's CONFIG_RSEQ flag, the zero window is 6144513 bytes, was 8388608, and the channel reader is set; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanCeil.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

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
  if_shadow : 0 <= shadow_off A <= 2 ^ 47;
  (* The table's bounds on the launch's extra reserved intervals hold for the
     pair Linux installs -- two intervals of at most twenty pages
     ([State.vdso_len_bounds] gives 5..20 pages, and a sixteen-page vDSO text
     reaches the top of that).  It is the last field, after the positional
     projections of [img_facts].
     Model donor [75d69e00:theories/Common/AsanInit.v:63];
     donor shape: the field [if_resx] at line 47 of projects/openssl/pem/proofs/lib/Common/AsanInit.v as in the LPS 727298f3 update. *)
  if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.

(* [comment removed for export] *)
(* The image is Linux's whole block from sp to the stack VMA's end (at
   75d69e00), so its size is a function of (sp, top), not of (argv, envp):
   [stack_image_size sp top = bv_unsigned top - bv_unsigned sp].
   Model donor [c0dd863a:theories/Common/AsanInit.v:71]. *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* AT_NULL closes the vector: pair 28 with CONFIG_RSEQ, pair 26 without
   ([StackLayout.auxv_entries]), so its two words are [2 * (26 + 2 * r)] and
   one more, at the flag's [r = rseq_z (la_rseq la)].  Model donor
   [75d69e00:theories/Common/AsanInit.v:77]; the K cone has no copy of it, so
   it is stated here rather than in [AsanPlanCoreK.v], where [e_auxv]'s
   Section would have to be reopened. *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

(* The AT_RANDOM block's literal offset off [e_auxb]'s base: the pointer
   vector's NULLs and argc (24) plus the auxv itself, under BOTH layouts.  It
   is not a single literal: 456 at [rseq = false], 488 at [rseq = true].
   Model donor [75d69e00:theories/Common/AsanPlanCore.v:3874]; the tie to the
   model's own auxv size is [AsanPlanCoreK.AUXSZ_of], which is
   hypothesis-free. *)
Lemma e_atrb_off : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Init.
  Variable segs : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variable nofile : word.
  Variable sigmask : word.
  (* [abrt] is the abort declaration ([State.in_abort_terminal]); [sdf] is the
     launch's SIGPIPE disposition at entry ([State.in_sigpipe_default]).
     [Run.valid_input] leaves the disposition FREE
     ([727298f3:theories/LinuxProcessSem/Run.v:4636-4642]: a launcher that ran
     `signal(SIGPIPE, SIG_IGN)` before execve starts an ordinary Linux
     process), so it is a Variable and [inp] writes it into its nineteenth
     place; a caller passes its input's own [in_sigpipe_default]. *)
  Variables abrt sdf : bool.
  Variable ur : InputStream.
  (* [State.mkProcInput_full] has twenty places.  [kb] is a Variable so every
     free field of the build is free:
     a run under [Run.valid_input] satisfies
     [in_kernel inp = recorded_kernel (in_kernel inp)]
     ([Run.valid_input_recorded_kernel]), so it instantiates [kb] with its own
     build.  Shape and argument order follow the model's own fixture at
     [c0dd863a:theories/Common/AsanInit.v:137-141]. *)
  Variable kb : KernelBuild.
  (* The exec file name is free for the same reason, and NOT
     [State.default_execfn] as the model's fixture has it: that section builds
     its own input, whereas this one must accept the input the published
     statement quantifies over, and [Run.valid_input] constrains the name only
     through [valid_launch] -- it never pins it.  A pin here would be a premise
     no caller could discharge. *)
  Variable execfn : list byte.
  (* The image's ELF entry: [Run.init_config]'s pc, and the auxv's AT_ENTRY.
     It is a Section Variable because the auxv -- hence the stack image --
     reads it.  Shape and reason follow the model's own fixture at
     [c0dd863a:theories/Common/AsanInit.v:91] and [:161]. *)
  Variable apc : N.

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
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Definition inp : ProcInput :=
    mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw
      abrt Sv48 ur [] (recorded_kernel kb) execfn true sdf false.  (* [comment removed for export] *)
  (* [Run.valid_input]'s last conjunct: the exec file name is a name [execve]
     admits and the launch fits under E2BIG.  Model donor
     [c0dd863a:theories/Common/AsanInit.v:146]. *)
  Hypothesis Hlaunch : valid_launch inp.
  (* [Run.valid_entry]'s FIFTH conjunct: the start state is exactly a Linux
     launch.  It pins the stack VMA's end, the entry stack pointer inside the
     [arch_align_stack] window, and the mmap base -- so it is what bounds the
     pad [V_W] and the image's length.  Model donor
     [c0dd863a:theories/Common/AsanInit.v:151]. *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* [comment removed for export] *)

  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  (* the auxv the launch builds; [Run.launch_auxv] copies CONFIG_RSEQ straight
     off the kernel build, so [la_rseq la] IS this Section's [rseq]
     ([RefLayout.lay_rseq]).  Model donor [c0dd863a:theories/Common/AsanInit.v:162]. *)
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  (* The mapped image IS Linux's block, sp .. [ed_top]: at 75d69e00
     [entry_stack_image] is [build_stack_bytes ...] exactly ([Run.v]), so [bsb]
     and [SIMG] are the SAME list. *)
  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
  Let SIMG := entry_stack_image inp mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* The run's CONFIG_RSEQ flag, kept SYMBOLIC: it is the one field of
     [Run.launch_auxv] that [Run.valid_input] leaves free (the other three --
     [vdso_text_base], [launch_cache_words], [min_sigframe_size] -- are pinned
     and come free from [Run.valid_input_recorded_kernel]), and it is the one
     that reaches [cat_string_off].  Never pinned to [default_kernel]. *)
  Let rseq := kb_rseq (in_kernel inp).
  Let top := ed_top rdraw.
  Let utop := bv_unsigned top.
  (* [StackLayout.block_items mod 2]: STACK_ROUND's 8-byte gap, in words.  This
     is the plan's variable [V_G], at index 11, with [V_GID] at 12 and [NX0] at 13.
     Value as in the model ([c0dd863a:theories/Common/AsanInit.v:212]). *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* V_W is [W := Z.of_nat (block_pad_len rseq sp top argv envp execfn)], the
     [arch_align_stack] pad in BYTES: the plan's [e_str0 r := eadd (eaddz
     (e_atrandom r) 16) (EVar V_W)] makes V_W the distance from the top of the
     AT_RANDOM bytes up to argv[0], because the strings are ABOVE the random
     bytes.  [execfn] is this Section's free
     Variable, NOT [State.default_execfn]: the published statement hands the
     section an arbitrary exec name and [Run.valid_input] constrains it only
     through [valid_launch]. *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* argv[0]'s first byte.  [CatExec.v:338] has [cat_string_off = block_head_size
     + block_pad_len], so this IS the model's [usp + CHEAD + W], and the same
     quantity [AsanNodesStartXK.v]'s STR0 names. *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  (* the plan's CONFIG_RSEQ flag as 0 or 1: the plan's interface, [r : Z]
     instantiated with [rseq_z (kb_rseq (in_kernel inp))] *)
  Let RZ := rseq_z rseq.
  (* C, sp to the top of the AT_RANDOM bytes *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* L, the string bytes with their NULs, the exec file name included *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).

  (* the input's fields, by conversion, so the arithmetic below stays a
     function of (sp, rdraw, argv, envp, execfn, kb) and not of the whole input *)
  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 G;
     (* [V_GID] (index 12): AT_GID and AT_EGID, both [gid] ([AsanPlanCoreK.V_GID]) *)
     gid].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    ((uE E e_sp0 <=? z) &&
     (((usp + 24 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
      (* The string area, [STR0 .. utop], at the TOP of the stack VMA.
         Shape from the model, [c0dd863a:theories/Common/AsanInit.v:237]. *)
      || ((STR0 <=? z) && (z <? utop))))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Proof.
    (* [argH0] has two disjuncts, the second the string range
       [STR0 <= z < utop], so no inner [orb_prop] split is needed.
       The [Nat2Z.is_nonneg] is load-bearing: the
       second disjunct gives [STR0 <= bv_unsigned a], and unfolding [STR0]
       exposes [bv_unsigned sp + Z.of_nat (cat_string_off ...)], whose
       [Z.of_nat] [lia] will not find a lower bound for on its own.  The
       conclusion's second conjunct comes from [HS], the leading
       [uE E e_sp0 <=? z] guard this file keeps and the model's own [argH0]
       does not have. *)
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)).
    apply andb_prop in H as [HS H]. apply Z.leb_le in HS.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold usp, argc, envc, STR0 in H; lia.
  Qed.

  Lemma e_sp0_init : expr_vars_lt NX0 e_sp0 = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof.
    intros E E' a Hag. unfold argH0, uE. rewrite (APSK.edenot_agree' NX0 E E' e_sp0 Hag e_sp0_init). reflexivity.
  Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M HAG [H1 H2]. pose proof HAG as [Hag _]. split.
    - intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
    - intros a Ha. apply H2. rewrite (argH0_agree E E' a HAG). exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range rseq). Qed.

  (* the vector's length, the ONE case split on the flag the arithmetic needs *)
  Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
  Proof. unfold RZ, rseq_z, auxv_count. destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.

  Lemma gap_range : 0 <= G <= 1.
  Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  (* C = 8*items + AUXSZ RZ + 8*g + 16, with items = argc + envc + 3 and the
     auxv AUXSZ RZ = 432 + 32*RZ bytes: 29 entries with CONFIG_RSEQ, 27 without *)
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
     area ([copy_strings] / [copy_string_kernel], fs/exec.c, Linux v6.18.46,
     commit 1f99e9ab748f).  The model's proof unfolds [default_execfn] here;
     ours CANNOT -- [execfn] is a free Variable -- so this goes through [Hav0]
     (argv is non-empty) instead, which holds for every exec name. *)
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

  (* The pad [arch_align_stack] left.  [launch_sp_hi] is
     [align_down16(top - 8 - L) - C] and [launch_sp_lo] the same with
     [top - 8 - L - 4095], so the pad is r (0..4095) plus the remainder the
     low-four-bit mask leaves -- at most 4110, NOT 4095. *)
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
  Proof.
    pose proof pad_bounds_Z.
    unfold W, block_pad_len, LSTR, CHEAD, utop, usp in *.
    rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  (* The [arch_align_stack] pad is 0..4110 bytes ([pad_bounds_Z]). *)
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

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
    unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
  Qed.

  (* The bound counts the vector, the 432-byte auxv at 27 pairs, STACK_ROUND's
     gap, the sixteen random bytes, the pad, the strings and the eight-byte
     slot.  Stated at the SMALLER layout (RZ = 0,
     G = 0, L = 2) so it holds for every value of the free field kb_rseq. *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof.
    unfold STR0, cat_string_off. pose proof pad_eq.
    fold CHEAD. fold W. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as Gb. pose proof len_av. pose proof len_ev. lia. Qed.

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof gap_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0_s2a : uE E0 (EVar V_S2A) = (usp mod 32768) / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold uE. cbn [edenot E0 ev nth vals0 V_S2A].
    rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma edenot_uid : uid = edenot E0 (EVar V_UID).
  Proof. reflexivity. Qed.

  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  Lemma uE0_hw : uE E0 (EVar V_HW) = bv_unsigned hw.
  Proof. reflexivity. Qed.
  Lemma hw_range : bv_unsigned hw = 0x112d \/ bv_unsigned hw = 0x20112d.
  Proof. destruct Hhw as [-> | ->]; [left|right]; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma u_e_sppg : uE E0 e_sppg = usp / 4096 * 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_s2a as U2A.
    unfold e_sppg, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2A.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof u_e_sppg as UP.
    rewrite e_sp0_unfold. unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite UP, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  (* [comment removed for export] *)
  Lemma u_e_top : uE E0 e_top = usp / 4096 * 4096 - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold e_top, eaddz, uE. rewrite mkAlu_denot, edenot_lit.
    pose proof u_e_sppg as U. unfold uE in U. rewrite u_add64, U, u_lit64. unfold two64.
    replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
    replace (usp / 4096 * 4096 + (2 ^ 64 - 8388608)) with ((usp / 4096 * 4096 - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
  Qed.
  Lemma u_e_stk_len : uE E0 e_stk_len = 2 ^ 47 + 8388608 - usp / 4096 * 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold e_stk_len, esub, uE. rewrite mkAlu_denot, edenot_lit.
    pose proof u_e_sppg as U. unfold uE in U. rewrite u_sub64, U, u_lit64. unfold two64.
    rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia. rewrite Z.mod_small; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_s2a as U2A.
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U2A.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_sppg8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 512 (EVar V_S2A))) = usp / 4096 * 512.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_s2a as U2A.
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2A.
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

  (* The valuation of the plan variable [V_G], the twelfth slot.  Stated
     beside [uE0_s2a] and [uE0_L1] because [uE0] covers seven variables
     only. *)
  Lemma uE0_G : uE E0 (EVar V_G) = G.
  Proof.
    pose proof gap_range. unfold uE. cbn [edenot E0 ev nth vals0 V_G].
    rewrite u64_lit by lia. reflexivity.
  Qed.

  (* [uE E0 (e_atrandom RZ) = usp + CHEAD - 16]: the sixteen AT_RANDOM bytes
     sit at the top of the HEAD, not at the top of the IMAGE:
     [create_elf_tables] lays the vector down from them and [copy_strings] has
     already put the strings above them (fs/exec.c, fs/binfmt_elf.c, Linux
     v6.18.46, commit 1f99e9ab748f).  Model's own form:
     [75d69e00:theories/Common/AsanInit.v:482]. *)
  Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof u_e_auxv as UA. pose proof uE0_G as UG.
    unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UG.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [uE E0 (e_str0 RZ) = STR0]: the strings are at the top of the stack VMA,
     and [STR0] is
     [usp + cat_string_off rseq sp top argv envp execfn], which
     [CatExec.v:338] defines as [block_head_size + block_pad_len] -- the
     model's [usp + CHEAD + W] ([c0dd863a:theories/Common/AsanInit.v:220], [:492]) -- so it is a
     function of the FREE [kb_rseq] through [RZ] and of the
     [arch_align_stack] pad, never a constant. *)
  Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof pad_range. pose proof pad_eq. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA.
    unfold e_str0, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6.
    rewrite !Z.mod_small by lia.
    unfold STR0, cat_string_off. fold CHEAD. fold W. lia.
  Qed.

  (* Same move, one string along: argv[1] is argv[0] + L0 + 1. *)
  Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof pad_range. pose proof pad_eq. pose proof str0_hi. pose proof s0_in_strings.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [uE E0 e_atr8 = usp / 8 + argc + envc + G]: the plan's [e_atr8] reads
     [EVar V_G] ([AsanPlanCoreK.v:3234]), because the quantity it bounds is the
     shadow of the argument block below the random bytes -- the auxv size
     cancels out of it, which is why it is the one expression of this family
     that takes no [rz] ([c0dd863a:theories/Common/AsanPlanCore.v:3275-3279] states the same
     independence).
     [W] is the pad in BYTES and is not a quotient, so it is not related to
     [G]. *)
  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8. pose proof uE0_G as UG.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot.
    rewrite !u_add64 by lia. rewrite U8, U3, U4, UG. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [model0 := with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
     (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)] is
     [Run.init_config]'s model: the launch's vDSO draw is copied into the start
     state.  [with_vdso] rebuilds only the VM subsystem's vDSO
     field: [m_vmmaps], [m_kernel], [m_vm_lazy], [m_vm_materialized] and
     [m_proc] are each preserved BY [reflexivity]
     ([75d69e00:theories/LinuxProcessSem/State.v:5046-5062]), so [model0_facts]
     closes by [repeat split; reflexivity].
     Model donor [75d69e00:theories/LinuxProcessSem/State.v:5031-5034] for the
     setter and [75d69e00:theories/LinuxProcessSem/Vdso.v:254] for [vdso_run_init]; donor shape projects/openssl/pem/proofs/lib/Common/AsanInit.v
     lines 655-659 as in the LPS 727298f3 update (`with_vdso (vdso_run_init (ed_vdso rdraw))`). *)
  Definition model0 : Model :=
    with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  Let cs0 := init_acs_of RZ A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (** THE LAUNCH'S RESERVED LEDGER is the image's reservations AND the vDSO pair
      ([State.init_reserved]), placed at [State.vdso_top] of the initial ledger,
      which for [mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp] is
      [page_round_down_Z (Z.min mbase (sp - stack_max_size))].
      Model donor [75d69e00:theories/LinuxProcessSem/State.v:7716-7721, 7836-7838];
      donor shape projects/openssl/pem/proofs/lib/Common/AsanInit.v lines 668-670 as in the LPS 727298f3 update. *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  Lemma sum_sizes_app : forall l1 l2, APSK.sum_sizes (l1 ++ l2) = APSK.sum_sizes l1 + APSK.sum_sizes l2.
  Proof.
    induction l1 as [|iv l1 IH]; intro l2; cbn [app APSK.sum_sizes]; [lia|]. rewrite IH. lia.
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

  (** the pair, for ANY kernel build: four vvar pages, then one to sixteen text
      pages.  Stated through [vdso_len] / [vdso_text_pages] rather than computed
      at one build, so it holds for every value of the free kernel fields.
      Donor shape projects/openssl/pem/proofs/lib/Common/AsanInit.v lines 703-713 as in the LPS 727298f3 update; the model's own
      [75d69e00:theories/Common/AsanInit.v:593-604] pins [vdso_len] to 24576 by
      [vm_compute], which this cone must NOT do -- its kernel is free. *)
  Lemma resx_shape :
    RESX = [(Z_to_bv 64 (VTOP - vdso_len (in_kernel inp)), Z_to_bv 64 (vdso_vvar_pages * page_size));
            (Z_to_bv 64 (VTOP - vdso_len (in_kernel inp) + vdso_vvar_pages * page_size),
             Z_to_bv 64 (vdso_text_pages (in_kernel inp) * page_size))].
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof (vdso_len_bounds (in_kernel inp)).
    unfold RESX, vdso_reserved. cbv zeta.
    replace (VTOP - vdso_len (in_kernel inp) <? page_size) with false
      by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    reflexivity.
  Qed.

  Lemma resx_len : (length RESX <= 2)%nat.
  Proof. rewrite resx_shape. cbn [length]. lia. Qed.

  Lemma resx_sum : APSK.sum_sizes RESX = vdso_len (in_kernel inp).
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
    rewrite resx_shape. cbn [APSK.sum_sizes fst snd].
    unfold vdso_len, vdso_vvar_pages, page_size in *.
    rewrite !u64_lit by lia. lia.
  Qed.

  Lemma resx_bytes_lo : 81920 <= resx_bytes A.
  Proof.
    pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. unfold resx_bytes. lia.
  Qed.

  Lemma resx_ok : Forall (APSK.resx_entry_ok A) RESX.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
    pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
    rewrite resx_shape. unfold APSK.resx_entry_ok, vdso_len, vdso_vvar_pages, page_size in *.
    repeat constructor; cbn [fst snd];
      rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
  Qed.

  (* [vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX] with
     [RESX := vdso_reserved (in_kernel inp) VTOP]: [init_model] seeds the
     reserved ledger with [init_reserved reserved mbase sp (in_kernel inp)],
     which appends the vdso/vvar pair [execve] installed above the image
     ([75d69e00:theories/LinuxProcessSem/State.v:7786], the
     [mkVmMapsFull (init_reserved reserved mbase sp (in_kernel inp)) ...]
     field; [init_reserved] itself at :7716-7721).  This is that term with
     [init_reserved] unfolded, the shape [co_res] consumes, and it closes by
     [reflexivity] for EVERY value of the free kernel fields -- [kb_rseq]
     included -- because [vdso_reserved] is applied to [in_kernel inp] rather
     than computed at one build.  Its consumers are [hid0_eq] (:737, which
     destructs positions 5/6/7 -- [vm_maps], [vm_noaccess], [m_vm_lazy] -- and
     never reads this conjunct, since [vis] at [AsanPlanSoundK.v:224] reads
     [vm_maps], [vm_noaccess] and [m_vm_lazy] only) and [init_cs_ok]
     (:1485, [rewrite ?M4] among all thirteen); no other file mentions
     [model0_facts]. *)
  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX
    /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma utop0 : APSK.utop E0 = usp / 4096 * 4096 - 8388608.
  Proof. unfold APSK.utop, APSK.pagedown. rewrite u_e_sp0. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APSK.in_hull A (bv_unsigned a) || (usp / 4096 * 4096 - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite utop0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp / 4096 * 4096 - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia). rewrite orb_true_r. reflexivity.
  Qed.

  (* [usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some 0], not 8388608:
     [PropExec.wrap_mem] ([PropExec.v:2459-2468]) zero-fills down to
     [Run.stack_window_lo (in_kernel inp) mbase rdraw]
     = [Z.max (ed_top rdraw - stack_max_size) (mbase + stack_guard_gap_bytes kb)]
     ([75d69e00:theories/LinuxProcessSem/Run.v:1379]).  Since [ed_top rdraw] is
     strictly ABOVE sp ([pad_eq]: [W = utop - 8 - LSTR - usp - CHEAD >= 0] with
     [LSTR >= 2]), [stack_window_lo > usp - 8388608] on every run.  6144513 is
     [StoreOk.stack_window_depth]
     ([StoreOk.v:141-147]: [stack_max_size - stack_window_reach] with
     [stack_window_reach = 2244095]), which is what
     [StoreOk.stack_window_lo_valid] bounds [stack_window_lo] by, for every
     value of the free kernel fields -- [kb_rseq] and [kb_aslr] both, the
     latter being the one [stack_window_lo_valid] case-splits on internally.
     Model donor [75d69e00:theories/Common/AsanInit.v:639].
     Its consumers: [Mr0_below] and [stack_window_ok] below (both at 6144513),
     and [atrandom_ok]/[rdn_Mr0_stack], which apply it at or above sp. *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
                 <= bv_unsigned sp + stack_window_reach - stack_max_size)
      by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hlaunch Hlau).
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_window_reach, stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  (* At 8388608: [stack_window_lo_ge_sp] gives
     [sp - stack_max_size <= stack_window_lo], so nothing below
     [usp - 8388608] is filled.  Model donor [c0dd863a:theories/Common/AsanInit.v:653]. *)
  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    pose proof (stack_window_lo_ge_sp inp sp brk0 mbase rdraw Hlau) as HW.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
    rewrite <- (rdn_wrap_stack_above segs inp mbase ph entryw sp rdraw a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp, CEIL in *; lia | apply Hvis; exact Hx].
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

  (* Two disjuncts, following [argH0]: the string area is [STR0 .. utop].
     Model's shape: [75d69e00:theories/Common/AsanInit.v:237]. *)
  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H. apply andb_prop in H as [_ H].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
      apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left | right]; lia.
  Qed.

  (* The complement, in the same two ranges: below the argv pointers, between
     them and argv[0], and above the stack VMA's end. *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 24 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    (* [STR0], [utop], [CHEAD], [W] and [LSTR] stay ATOMS here: every relation
       the contradiction needs is among the posed facts ([str0_hi] and [pad_eq]
       together give [STR0 = usp + CHEAD + W], [chead_eq] with [gap_range] and
      [RZ_range] give [CHEAD >= 8*argc + 8*envc + 472]).  Unfolding
      [STR0, cat_string_off] and folding [CHEAD]/[W] does not work here:
      [CHEAD] and [W] are Section [Let]s in the
       context, so [fold .. in *] folds them inside their own bodies and Rocq
       refuses with "Cannot create self-referring hypothesis CHEAD". *)
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range.
    pose proof gap_range. pose proof str0_hi. pose proof pad_eq. pose proof lstr_lo.
    pose proof RZ_range. lia.
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

  Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  (* the auxv words the launch wrote, named once.  Model donor
     [c0dd863a:theories/Common/AsanInit.v:736]. *)
  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* [(j < 2 * auxv_count rseq)%nat -> nth j AUXW (Z_to_bv 64 0) = edenot E0 v
     -> ...]: [StackLayout.auxv_words] takes eight arguments
     ([la ph entry uid gid hw ar ae]), and the vector is 58 words (29 pairs)
     with CONFIG_RSEQ and 54 (27) without.  [auxv_count rseq] is symbolic in
     the free field [kb_rseq], so the bound holds at BOTH builds
     ([auxv_count_RZ] is the only case split).  Model donor
     [c0dd863a:theories/Common/AsanInit.v:740]; the
     read-back is [RefLayout.read_auxv_word], whose own bound is the same
     [2 * auxv_count (kb_rseq (in_kernel inp))].  Its one consumer is
     [auxw_ok], below. *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    pose proof auxv_count_RZ.
    (* [STR0] is [usp + Z.of_nat (cat_string_off ..)] here, an ATOM, where the
       model defines it as [usp + CHEAD + W] outright
       ([c0dd863a:theories/Common/AsanInit.v:220]).  [str0_hi] with
       [pad_eq] is the tie -- together they give [STR0 = usp + CHEAD + W] --
       and the fourth bullet below needs it: an auxv word sits at
       [usp + 8*argc + 8*envc + 24 + 8*j], which [not_argH0]'s MIDDLE disjunct
       covers only once [STR0] has a value. *)
    pose proof str0_hi. pose proof pad_eq.
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
    - rewrite <- Hv.
      exact (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hj).
  Qed.

  (* [(0 <= i < Z.of_nat (auxv_count rseq)) -> nth .. AUXW .. -> ...], for
     [auxv_word_ok]'s two reasons; the plan claims pair [26 + 2 * RZ]
     ([AsanPlanCoreK.v:3867]).  Its consumers are [auxv_null_ok] and
     [init_kn_with_ok], both below. *)
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

  (* [usp - stack_window_depth <= bv_unsigned a < usp -> Mr0 a = Some 0], for
     [FULL0_below]'s reason, stated through [StoreOk.stack_window_depth] rather
     than its numeral, so a model change to [stack_window_reach] moves this in
     one place ([stack_window_depth = 6144513], [StoreOk.v:144-147].)  Model
     donor [75d69e00:theories/Common/AsanInit.v:779]. *)
  Lemma Mr0_below : forall a : word, usp - stack_window_depth <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av. pose proof stack_window_depth_val.
    rewrite Mr0_visible; [apply FULL0_below; lia | lia | apply not_argH0; lia].
  Qed.

  (* This is the ONE place in the cone where the plan's zero window is proved
     from the model (see [FULL0_below] for why its width is not 8388608): the
     [KWr] and [KZero] entries at [-stack_window_depth] / [stack_window_depth].
     [AsanPlanCoreK.v:3856-3857]'s two entries match the model's own plan
     ([75d69e00:theories/Common/AsanPlanCore.v:3911], which spells the numeral
     6144513), as does [has_window] in the four Drv libs.  Nothing here reads
     [kb_rseq], and [stack_window_lo_valid] discharges [kb_aslr] internally, so
     the statement holds at every kernel build. *)
  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth)).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof stack_window_depth_val as HD.
    assert (Hst : estart E0 (SA e_sp0 (-stack_window_depth)) = usp - stack_window_depth).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit stack_window_depth) = stack_window_depth) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-stack_window_depth)) (elenZ E0 (ELit stack_window_depth))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        pose proof len_av. unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* argv[0] is at the BOTTOM OF THE STRING AREA, [cat_string_off] bytes above
     sp, and [STR0] is the name this Section gives that address.  Spelled with
     [in_argv inp] and [ed_top rdraw] rather than the Section's abbreviations,
     because that is the form [CatExec]'s lemmas rewrite to.  Model donor
     [c0dd863a:theories/Common/AsanInit.v:820]. *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
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
    apply (kword_stack e_sp0 8 (e_str0 RZ) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
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
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 (e_str1 RZ)).
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U.
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

  (* [atrandom_ok] reads the AT_RANDOM bytes at the top of the HEAD, not of
     the image:
       Hak : ak = 24 + AUXSZ RZ          (456 at rseq = false, 488 at true)
       Hst : estart E0 (SA ab ak) = usp + CHEAD - 16
       Hu  : bv_unsigned (at_random_ptr ..) = usp + CHEAD - 16
     [snd (e_atrb RZ)] is [24 + AUXSZ RZ] because [e_atrandom] adds the auxv's
     own size ([AsanPlanCoreK.v:275]); no literal is right at both builds, and
     the tie to the model's [auxv_size] is the hypothesis-free
     [AsanPlanCoreK.AUXSZ_of].  The position is [CHEAD - 16] because the
     strings and the [arch_align_stack] pad are above the random bytes
     ([u_e_atrandom] above, model donor
     [75d69e00:theories/Common/AsanInit.v:482]).  Model donor for this proof:
     [:892]. *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range.
    (* [str0_hi] with [pad_eq] gives [STR0 = usp + CHEAD + W], which the
       [not_argH0] side condition needs: the random bytes end at [usp + CHEAD],
       at or below [STR0]. *)
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
    (* ONE name for the image, and it must be the goal's.  [bsb] and [SIMG] are
       the same list, so [fold bsb in Hrd] succeeds and then
       [fold SIMG in Hrd] is a no-op -- leaving [Hrd] on [bsb] while the goal
       (through [wrap_above_sp] and [fold SIMG] below) is on [SIMG].  The
       [destruct .. eqn:Hstk] then rewrites only the goal's copy and
       [injection Hrd] fails with "Nothing to inject". *)
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold SIMG in Hrd.
    rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      (* [bsb] and [SIMG] are the same list, so this is [le_n]. *)
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
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
     [26 + 2 * RZ] ([AsanPlanCoreK.v:3867], [auxv_words_null] above).  It is
     closed apart from [init_kn_with_ok]'s uniform [cbn; try reflexivity] block,
     which cannot reduce a symbolic [nth]. *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (auxv_words_null la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
    apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
  Qed.

  (* The rest of the vector ([AsanPlanCoreK.auxv_rest]). *)
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

  (* the whole vector is readable ([KUnk]): it is visible block memory below argv[0] *)
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
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* the CONFIG_RSEQ pair (26, 27), claimed only at [RZ = 1], where it is in the vector *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb RZ 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    unfold RZ, rseq, rseq_z in *. unfold AUXW, la, launch_auxv in *.
    (* [kb_rseq (in_kernel inp)] is the body of the Section's [Let rseq]; split on it
       through [bool_dec] and rewrite in the goal only *)
    destruct (Bool.bool_dec (kb_rseq (in_kernel inp)) true) as [Hr|Hr]; [| apply Bool.not_true_is_false in Hr];
      rewrite Hr; cbn [Z.eqb Pos.eqb]; [|constructor].
    apply Forall_app; split; apply auxw_ok;
      unfold AUXW, rseq, la, launch_auxv, auxv_words, auxv_entries, auxv_count in *; cbn [la_rseq];
      rewrite ?Hr;
      first [ (cbn; lia)
            | (cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
               first [reflexivity | (rewrite edenot_lit; reflexivity)])
            | fail 1 "AUXRSEQ:" ].
  Qed.

  (* STACK_ROUND's gap, [usp + 8*argc + 8*envc + 24 + AUXSZ RZ] for [8*G] bytes,
     and the arch_align_stack pad, [usp + CHEAD] for [W] bytes: both visible
     block memory below argv[0] ([STR0 = usp + CHEAD + W]), so readable, as
     [auxv_unk_ok] is for the vector. *)
  Lemma gap_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb + AUXSZ RZ)) (escale 8 (EVar V_G))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab (ak + AUXSZ RZ)) = usp + 8 * argc + 8 * envc + 24 + AUXSZ RZ)
      by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (escale 8 (EVar V_G)) = 8 * G).
    { pose proof uE0_G as UG. unfold elenZ, escale, uE in *. rewrite mkMd_denot, edenot_lit.
      rewrite u_mul64, u64_lit, UG by lia. rewrite Z.mod_small by lia. reflexivity. }
    cbn [kentry_ok]. rewrite Hst, Hl. unfold AUXSZ in *.
    split; [unfold flat; rewrite Hst; unfold AUXSZ, usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + (432 + 32 * RZ) + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
    replace (usp + 8 * argc + 8 * envc + 24 + (432 + 32 * RZ) + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  Lemma pad_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst (e_atrb RZ)) (snd (e_atrb RZ) + 16)) (EVar V_W)).
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
    assert (Hst : estart E0 (SA ab (ak + 16)) = usp + CHEAD) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (EVar V_W) = W) by (destruct uE0 as (_ & _ & _ & _ & _ & U6 & _); exact U6).
    cbn [kentry_ok]. rewrite Hst, Hl.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + CHEAD + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
    replace (usp + CHEAD + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest RZ A).
  Proof.
    pose proof RZ_range. pose proof auxv_count_RZ.
    unfold auxv_rest.
    (* AT_CLKTCK, AT_BASE, AT_FLAGS, AT_ENTRY, AT_GID, AT_EGID: below the
       CONFIG_RSEQ pair, so the same words under both layouts; AT_ENTRY from
       [Hapc]; AT_GID/AT_EGID are [gid], slot [V_GID] of [vals0] *)
    do 6 (apply Forall_app; split;
      [ apply auxw_ok;
        [ lia
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          reflexivity
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          first [ reflexivity
                | (rewrite edenot_lit; reflexivity)
                | (rewrite edenot_lit; unfold entryw; rewrite Hapc; reflexivity)
                | fail 1 "AUXREST-PAIR:" ] ]
      | ]).
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_cons; [exact auxv_unk_ok|].
    (* the eleven type words, written out so a miss names itself *)
    do 11 (apply Forall_cons;
      [ first [ (apply auxt_ok;
                 [ lia
                 | unfold AUXW, auxv_words, auxv_entries;
                   cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                   reflexivity ])
              | fail 1 "AUXT:" ] |]).
    apply Forall_cons; [exact gap_unk_ok|].
    apply Forall_cons; [exact pad_unk_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof gap_range. pose proof chead_range.
    (* [usp_fit] bounds [usp + |bsb|], so every upper bound below that is
       stated in [CHEAD] -- the AT_RANDOM range's [<= 2^47] first -- needs
       [length_bsb_sum] to connect the two, and [chead_eq] with [RZ_range] for
       [CHEAD]'s own shape.  Model donor [c0dd863a:theories/Common/AsanInit.v:1013-1015]. *)
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
      apply Forall_cons; [apply kr_ok; rewrite uE0_s2a; lia|].   (* [comment removed for export] *)
      (* [KRange (e_str0 r) 0x7fff80000000 (2^47 - 10)]: argv[0]'s address is [STR0]
         ([u_e_str0]), at or above sp, and the strings and the eight-byte slot above it
         end at the stack top, at or below 2^47 ([str0_hi], [pad_eq], [usp_fit]) *)
      apply Forall_cons;
        [ pose proof u_e_str0 as US; pose proof str0_hi; pose proof pad_eq;
          apply kr_ok; rewrite US; lia | ].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      (* [KRange e_auxv (0x7fff80000000 + 24) (2^47 - AUXSZ r - 16)]
         ([AsanPlanCoreK.v:3827]): the auxv's own size is IN the bound, so
         [AUXSZ] has to be unfolded before [lia] sees a linear term in [RZ]. *)
      apply Forall_cons; [apply kr_ok; rewrite u_e_auxv; unfold AUXSZ; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sppg; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite u_sppg8; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_hw; pose proof hw_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      (* [KRange (EVar V_G) 0 1], the plan's variable [V_G] ([AsanPlanCoreK.v:3837],
         after [V_W]): [uE0] is a seven-tuple over
         S1/S2/ARGC/ENVC/L0/W/BRK and does not carry it, so the bullet reads
         [uE0_G]. *)
      apply Forall_cons; [apply kr_ok; rewrite uE0_G; pose proof gap_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* AT_NULL (pair [26 + 2 * RZ]): its index is symbolic in the free field,
       so no [cbn] closes it -- [auxv_words_null] is the only case split. *)
    10: exact auxv_null_ok.
    (* AT_RANDOM (pair 24): its value is the plan's [e_atrandom RZ]; no
       [try reflexivity] here, the two sides are only equal by [atr_ptr_eq] *)
    9: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           reflexivity
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           exact atr_ptr_eq ].
    (* pairs 13, 14, 15, 11, 10, 19, 20, 23: all below the CONFIG_RSEQ pair, so
       the same words under both layouts *)
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
  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (usp / 4096 * 4096 - 8388608), pageup ((usp / 4096 * 4096 - 8388608) + (2 ^ 47 + 8388608 - usp / 4096 * 4096)));
     (pagedown (shadow_off A + (usp / 4096 * 4096 - 8388608) / 8),
      pageup (shadow_off A + ((usp / 4096 * 4096 - 8388608) + (2 ^ 47 + 8388608 - usp / 4096 * 4096)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_e_top, !u_e_stk_len.
    unfold uE. rewrite !edenot_lit, !u64_lit by (unfold CEIL; lia). reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL)
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL) <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo as UL. pose proof usp_hi as UH.
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, CEIL, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    set (P := usp / 4096 * 4096). assert (HP : usp - 4095 <= P <= usp) by (unfold P; lia).   (* [comment removed for export] *)
    replace ((P - 8388608) + (2 ^ 47 + 8388608 - P)) with (2 ^ 47) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    rewrite (P2 (2 ^ 47) eq_refl).
    assert (PD : forall z, z - 4095 <= pagedown z <= z) by (intros z; unfold pagedown; lia).
    pose proof (PD (P - 8388608)).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (P - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    clearbody P. split; lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* co_res: the launch reserves the vDSO pair beside the image.  The witness
         is [RESX] and its four clauses are: the ledger equality by
         [reflexivity] (that IS [model0_facts]'s conjunct); the geometry by
         [resx_ok]; [length RESX <= 2 <= n_resx A] by [if_resx]; and
         [sum_sizes RESX = vdso_len (in_kernel inp) <= 20 pages <= resx_bytes A]
         by [State.vdso_len_bounds] and [if_resx].  Every step is stated over
         [in_kernel inp], so it holds at EVERY kernel build.
         Model donor [75d69e00:theories/Common/AsanInit.v:1228-1238]. *)
      pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
      pose proof (vdso_len_bounds (in_kernel inp)).
      exists RESX. split; [reflexivity|].
      split; [exact resx_ok|].
      split; [pose proof resx_len; lia | rewrite resx_sum; unfold page_size in *; lia].
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* co_totsz: the image's reservations and the vDSO pair.
         Model donor [75d69e00:theories/Common/AsanInit.v:1251-1253]. *)
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof (vdso_len_bounds (in_kernel inp)). pose proof resx_bytes_lo.
      unfold page_size in *. lia.
    - (* [comment removed for export] *) rewrite u_e_sp0, u_e_sppg. unfold APSK.pagedown, model0, with_vdso, init_model, usp. cbn -[Z.mul Z.div Z.sub Z.add].
      destruct Hsp as (S1 & S2 & S3). repeat split; [lia | exact S2].
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) intros HH. discriminate HH.
    - (* co_mres: no tracked mappings at start, so nothing to be apart from *)
      constructor.
    - (* co_vdso: the ledger ends with the launch's own pair.
         Model donor [727298f3:theories/Common/AsanInit.v:1277-1281]. *)
      replace (m_kernel model0) with (in_kernel inp) by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
      apply incl_appr, incl_refl.
    - (* co_rdr: [inp] passes [true] for the channel reader *)
      reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = ...] over the
     Section's [apc] and [Hapc]: [apc] is this Section's Variable (the auxv,
     hence the stack image, reads the entry), so the lemma does not quantify
     over the entry.  The quantifier is not needed: the statement
     [forall apc' : N, Z.of_N apc' = a_entry A -> init_config segs apc' ...]
     follows from this one, because [Z.of_N] is injective.  This is the
     model's own form ([c0dd863a:theories/Common/AsanInit.v:1358-1359]).  Its consumers are
     As0StartupK.v:265,282 and Bo0StartupK.v:266,283, which pass [apc] and
     [Hapc] after [execfn]. *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp].
    (* [FULL0] hides one occurrence of [entryw = Z_to_bv 64 (Z.of_N apc)], which
       [rewrite Hapc] cannot see; unfold both so the entry rewrites on BOTH
       sides and the two [mkst]s become syntactically equal. *)
    unfold FULL0, entryw. rewrite init_mkst. rewrite Hapc. reflexivity.
  Qed.
End Init.
