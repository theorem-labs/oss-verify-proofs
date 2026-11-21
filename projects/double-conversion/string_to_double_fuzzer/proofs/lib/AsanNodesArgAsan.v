(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the new initial stack layout; the start-up taken per CONFIG_RSEQ value; the reader fact of the output channels; the mapping ledger's reserved ranges and mmap base; the SIGPIPE disposition). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib RefLayout ArgvEnv StartupAux.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape AsanAcctImages AsanMemcpyBase AsanMemcpy AsanMemchr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcctNoLazy AsanStdioDefs AsanStdioWriteS.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ArgLoops AsanNodesArg AsanNodesArgSound AsanNodesEmitSound AsanNodesFactSound  AsanPlanImagesInit.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Asan_code_87000_88000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.

Fixpoint noblob (e : expr) : bool :=
  match e with
  | EBlob _ _ _ _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => noblob a && noblob b
  | EExt _ _ _ a => noblob a
  | _ => true
  end.

Lemma edenot_ev_only : forall E E' b e,
  expr_vars_lt b e = true -> noblob e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros E E' b e. induction e; intros Hv Hb Hag; cbn [edenot]; cbn [expr_vars_lt noblob] in Hv, Hb; try reflexivity.
  - apply Hag. apply Nat.ltb_lt. exact Hv.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - discriminate.
Qed.

Lemma total_firstn1 : forall (l : list (list byte)), (0 < length l)%nat ->
  total_arg_bytes_nat (firstn 1 l) = (length (nth 0 l []) + 1)%nat.
Proof. intros [|a r] H; [cbn in H; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat (firstn 0 r)) with 0%nat. lia. Qed.

Definition idx1 (i : nat) : nat := match i with O => 0%nat | _ => 1%nat end.
End FPW_1.


#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
(* [comment removed for export] *)
#[local] Ltac kept_in_list Hin :=
  cbn [In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [in_list|]); destruct Hin.
Section FPW_2. Context {fx : PropExec.FPState}.


Section AsanInst.
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Variable apc : N.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variable ur : InputStream.
  Variable kern : KernelBuild.
  Variable execfn : list byte.
  Variable nofile : word.
  Variable sigmask : word.
  Variables abt sdf : bool.
  Hypothesis Hkernel : in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf).
  Variable FS0 : Fs.Fs.

  (* #38 re-packed the launch argument list.  build_stack_bytes takes a LaunchAuxv FIRST and a
     PhdrInfo SECOND (75d69e00 StackLayout.v:483-485, twelve arguments); entry_stack_image takes
     a ProcInput FIRST, mbase second, the PhdrInfo third (Run.v:1344-1345, six).  APH is a correct
     PhdrInfo (AsanPlanImagesInit.v:15, ImgA.M.phdrs) sitting in the new first slot -- the SHRINK
     direction, where nothing is missing and a well-typed term is simply in the wrong place.
     Every term below is taken from a GREEN in-unit call site at this sha, not from another tree:
       AsanInit.v:119  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
       AsanInit.v:142  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
       PropExec.v:2466-2470  entry_stack_image_block, which states the two forms EQUAL:
         entry_stack_image inp mbase ph entry sp draw
           = build_stack_bytes (launch_auxv inp mbase) ph entry sp (ed_top draw)
               (in_argv inp) (in_envp inp) (in_execfn inp) (in_uid inp) (in_gid inp) (in_hwcap inp) draw
     The ProcInput is already spelled twice above, in Hkernel and Hlau, so nothing is introduced. *)
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Let bsb := build_stack_bytes
               (launch_auxv (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) sp mbase)
               APH entryw sp (ed_top rdraw) argv envp execfn uid gid hw rdraw.
  Let SIMG := entry_stack_image
                (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)
                mbase APH entryw sp rdraw.   (* [comment removed for export] *)
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  Let argv1 := nth 1 argv [].
  Let L0 := Z.of_nat (length argv0).
  Let L1 := Z.of_nat (length argv1).
  (* #38 moved the strings from just above the auxv to the TOP of the stack VMA
     (75d69e00 StackLayout.v:439-506, Run.v:3610-3658).  The Lets below are AsanInit's own,
     term for term at this sha (AsanInit.v:118,121,153,155,157,159), so every AsanInit layout
     lemma matches them by conversion:
       CHEAD = block_head_size rseq argv envp               argc, the two pointer arrays,
                                                            the auxv, the gap, AT_RANDOM
       W     = block_pad_len rseq sp top argv envp execfn   arch_align_stack's pad, 0..4110
       LSTR  = launch_string_bytes argv envp execfn         the strings with their NULs
     STR0 WAS usp + 8*argc + 8*envc + 184; the 184 is the pre-#38 auxv block size and is FALSE
     at #38, which is why W_range was deleted rather than re-proved.  TOP is the end of the
     string area, utop - 8: the eight bytes above it are the slot create_init_stack_vma
     skipped (StackLayout.v:459). *)
  Let rseq : bool := kb_rseq kern.
  Let top : word := ed_top rdraw.
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Let STR0 := usp + CHEAD + W.
  Let TOP := STR0 + LSTR.

  (* [comment removed for export] *)
  Definition SINV1 (E : env) (M : word -> option byte) : Prop :=
    SINV0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf E M /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.

  Lemma SINV1_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SINV1 E M -> SINV1 E M'.
  Proof. intros E M M' Hf (H0 & H1 & H2). split; [|auto]. eapply SINV0_frame; eassumption. Qed.

  Lemma SINV1_agree : forall E E' M, env_agree NX0 E E' -> SINV1 E M -> SINV1 E' M.
  Proof.
    intros E E' M Hag (H0 & H1 & H2). pose proof Hag as [_ Heb]. split; [|rewrite <- Heb; auto].
    eapply SINV0_agree; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp. Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0. Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.
  Lemma L0_le : L0 <= 131071.
  Proof. unfold L0, argv0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.
  Lemma L1_le : L1 <= 131071.
  Proof.
    unfold L1, argv1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - apply (valid_argv_str_len argv 1 Hva Hl).
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  (* RESTATED, not re-proved: the old form baked in 184, the pre-#38 auxv block size.  The
     replacement is AsanInit's own length_bsb_sum (AsanInit.v:299), and SIMG -- not bsb -- is
     the entry_stack_image that lemma is about. *)
  Lemma W_facts : 0 <= W /\ Z.of_nat (length SIMG) = CHEAD + W + LSTR + 8.
  Proof.
    split; [unfold W; lia|].
    exact (length_bsb_sum APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw
             groups net ur kern execfn nofile sigmask abt sdf Hlau).
  Qed.

  (* stack_image_size sp top is bv_unsigned top - bv_unsigned sp, so this is AsanInit's
     length_bsb_eq (AsanInit.v:293) up to conversion. *)
  Lemma length_SIMG_eq : Z.of_nat (length SIMG) = bv_unsigned top - usp.
  Proof.
    exact (length_bsb_eq APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw
             groups net ur kern execfn nofile sigmask abt sdf Hlau).
  Qed.

  Lemma TOP_utop : TOP + 8 = bv_unsigned top.
  Proof.
    pose proof W_facts as [W1 W2]. pose proof length_SIMG_eq as LE.
    unfold TOP, STR0. lia.
  Qed.

  Lemma TOP_eq : TOP = usp + Z.of_nat (length SIMG) - 8.
  Proof. pose proof W_facts as [W1 W2]. unfold TOP, STR0. lia. Qed.

  (* The head carries the sixteen AT_RANDOM bytes and at least the shorter auxv's 27 pairs
     (AsanInit.auxv_count_ge27, stated outside that file's section). *)
  Lemma chead_lo : 448 <= CHEAD.
  Proof.
    pose proof (auxv_count_ge27 rseq).
    unfold CHEAD, block_head_size, auxv_size, block_items. lia.
  Qed.

  (* argv[0] and its NUL are the lowest bytes of the string area
     (75d69e00 StackLayout.v:406-409, launch_string_bytes). *)
  Lemma s0_fit : L0 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0, argv0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    (* the two `pose proof`s above are anonymous, so they take H and H0; name this one *)
    assert (Hav : (0 < length argv)%nat) by (destruct Hva as [Hva1 _]; lia).
    destruct argv as [|a t]; [cbn in Hav; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma s01_fit : 2 <= argc -> L0 + 1 + L1 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0, L1, argv0, argv1, argc.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    destruct argv as [|a0 [|a1 r]]; cbn [length]; try lia.
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* TOP + 8 <= 2^47, not TOP + 16: at #38 the strings end eight bytes below the stack VMA's
     top (the slot create_init_stack_vma skipped), where before they ended sixteen below the
     image's end.  AsanNodesArgSound's Lay hypothesis carries the same 8.
     The two hard conjuncts are lemmas of their own rather than arms of one `repeat split`:
     AsanInit's usp_fit is stated over ITS OWN section Lets, so after discharge its type is a
     let-expression that `exact` accepts by conversion and `lia` does not see through.  Stating
     the bound locally and discharging it with `exact` is what moves it into lia's view -- the
     same technique length_SIMG_eq above already uses for length_bsb_eq. *)
  Lemma TOP_hi : TOP + 8 <= 2 ^ 47.
  Proof.
    assert (UF : usp + Z.of_nat (length SIMG) <= 2 ^ 47)
      by exact (usp_fit APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw
                  groups net ur kern execfn nofile sigmask abt sdf Hlau).
    pose proof TOP_utop as TU. pose proof length_SIMG_eq as LE. lia.
  Qed.

  (* the stack VMA's top is page-aligned (75d69e00 Run.v:3610-3615), and TOP is eight below it *)
  Lemma TOP_mod8 : TOP mod 8 = 0.
  Proof.
    pose proof TOP_utop as TU.
    assert (HM : bv_unsigned top mod 4096 = 0)
      by (destruct Hlau as (HST & _ & _); destruct HST as (HM0 & _ & _); exact HM0).
    assert (HK : exists k, bv_unsigned top = 4096 * k).
    { exists (bv_unsigned top / 4096).
      pose proof (Z.div_mod (bv_unsigned top) 4096 ltac:(lia)). lia. }
    destruct HK as [k Hk].
    assert (HT8 : TOP = 8 * (512 * k - 1)) by lia.
    rewrite HT8, Z.mul_comm. apply Z.mod_mul. lia.
  Qed.

  Lemma Lay_asan : 0x7fff80000000 <= usp /\ usp + 176 <= STR0 /\ STR0 + L0 + 1 <= TOP
                   /\ (2 <= argc -> STR0 + L0 + 1 + L1 + 1 <= TOP)
                   /\ TOP mod 8 = 0 /\ TOP + 8 <= 2 ^ 47 /\ L0 <= 131071 /\ L1 <= 131071 /\ 1 <= argc <= 1024.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_al. pose proof L0_le. pose proof L1_le.
    pose proof W_facts as [W1 W2]. pose proof chead_lo. pose proof s0_fit.
    pose proof TOP_hi. pose proof TOP_mod8.
    unfold TOP, STR0 in *.
    repeat split; try lia; try (intros Hargc2; pose proof (s01_fit Hargc2); lia).
  Qed.

  (* [comment removed for export] *)
  Lemma Hnz_asan : forall i j, (j < length (ARG argv0 argv1 i))%nat -> bv_unsigned (byte_at (ARG argv0 argv1 i) j) <> 0.
  Proof.
    intros i j Hj Hz.
    assert (GEN : forall k, (k < length argv)%nat -> (j < length (nth k argv []))%nat -> bv_unsigned (byte_at (nth k argv []) j) = 0 -> False).
    { intros k Hk Hjk Hz'. apply (byte_at_nz (nth k argv []) j (valid_argv_str_nz argv k Hva Hk) Hjk).
      apply bv_eq. rewrite Hz'. reflexivity. }
    destruct i as [|i]; cbn [ARG] in Hj, Hz.
    - apply (GEN 0%nat); [destruct Hva as [H _]; lia | exact Hj | exact Hz].
    - destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
      + apply (GEN 1%nat Hl Hj Hz).
      + unfold argv1 in Hj. rewrite nth_overflow in Hj by lia. cbn in Hj. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let NX0_ge : APS.nx0_ok NX0 := Nat.le_refl NX0.

  Lemma argH0_high_asan : forall E (a : word), argH0 sp rdraw argv envp kern execfn E a = true -> CEIL <= bv_unsigned a.
  (* arity-free: AsanInit.argH0_high's discharged prefix is not (sp rdraw ...) at #38 -- R1b
     reported `sp` against an expected N -- and
     AsanNodesStartXInit.v:179-180 already carries the shape that does not care. *)
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.

  Lemma vals_of_SINV1 : forall E M, SINV1 E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof.
    intros E M ((Hev & Hmem) & B1 & B2).
    assert (AG : forall e, expr_vars_lt NX0 e = true -> noblob e = true -> edenot E e = edenot (E0 sp rdraw brk0 argv envp uid gid hw kern execfn) e).
    { intros e He Hb. apply (edenot_ev_only E _ NX0 e He Hb). exact Hev. }
    pose proof (u_e_sp0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau) as U0.
    pose proof (u_e_str0 APH apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net ur kern execfn Hsp Hva Hve Hfit nofile sigmask abt sdf Hlau) as U1.
    unfold uE in *. rewrite (AG e_sp0) by reflexivity. rewrite (AG e_str0) by reflexivity.
    change (edenot E (EVar V_L0)) with (ev E 3%nat). change (edenot E (EVar V_ARGC)) with (ev E 1%nat).
    change (edenot E (EVar V_L1)) with (ev E 7%nat).
    rewrite (Hev 3%nat), (Hev 1%nat), (Hev 7%nat) by (unfold NX0; lia).
    repeat split; try assumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_of_SINV1 : forall E M (a : word), SINV1 E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof.
    intros E M a ((Hev & Hmem) & _ & _) Ha.
    pose proof W_facts as [W1 W2]. pose proof TOP_eq as TE. pose proof TOP_utop as TU.
    pose proof chead_lo. pose proof len_av. pose proof len_ev.
    rewrite Hmem.
    2:{ unfold argH0. apply orb_true_intro. right. apply andb_true_intro.
        unfold TOP, STR0, CHEAD, LSTR, W, rseq, top in *. unfold usp, argc, envc in *.
        split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite wrap_above_sp by (unfold usp, STR0 in *; lia). fold entryw. fold SIMG. unfold stack_to_mem. fold usp.
    replace (usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; unfold STR0 in Ha; lia).
    replace (bv_unsigned a - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; unfold STR0 in Ha; lia).
    destruct (nth_error SIMG (Z.to_nat (bv_unsigned a - usp))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. unfold STR0 in Ha. lia.
  Qed.

  (* [comment removed for export] *)
  (* #38's cat_argv_ptr is top-first and takes the exec file name (CatExec.v:403-405); the old
     call was sp-first with four arguments.  argv[0] is no longer a literal offset above sp, so
     the address comes from cat_string_base_offset (CatExec.v:465) exactly as the model's own
     Common/AsanNodesStartX.v:210 STR0_eq takes it. *)
  Lemma cat_argv_ptr_STR : forall i, arg_ok argc i ->
    cat_argv_ptr top argv envp execfn (idx1 i) = Z_to_bv 64 (STR STR0 argv0 i).
  Proof.
    intros i Hi. pose proof len_av as LA. pose proof len_ev as LE.
    assert (Hk : (idx1 i < length argv)%nat) by (destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    rewrite (cat_argv_ptr_offset top argv envp execfn (idx1 i) Hk).
    assert (HB : cat_string_base top argv envp execfn
                 = (sp + nat_to_word (cat_string_off rseq sp top argv envp execfn))%bv)
      by exact (cat_string_base_offset Sv48
                  (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)
                  mbase sp brk0 rdraw Hlau).
    rewrite HB, nat_to_word_add_merge, word_add_nat. fold usp. apply f_equal.
    unfold cat_string_off.
    destruct i as [|i]; cbn [idx1 STR].
    - change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat. unfold STR0, CHEAD, W. lia.
    - rewrite total_firstn1 by lia. unfold STR0, CHEAD, W, argv0. lia.
  Qed.

  Lemma str_of_SINV1 : forall E M i j, SINV1 E M -> arg_ok argc i -> (j <= length (ARG argv0 argv1 i))%nat ->
    M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = Some (byte_at (ARG argv0 argv1 i) j).
  Proof.
    intros E M i j HS Hi Hj.
    pose proof Lay_asan as LAY. pose proof (STR_range usp STR0 TOP argc argv0 argv1 LAY i Hi) as [R1 R2].
    pose proof (STR_bounds usp STR0 TOP argc argv0 argv1 LAY i) as SB.
    pose proof (STR0_le STR0 TOP argv0 argv1 i) as S0.
    unfold LEN in R2.
    destruct (rd_of_SINV1 E M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) HS) as [b Hb].
    { rewrite u64_lit; lia. }
    rewrite Hb. f_equal.
    destruct HS as ((Hev & Hmem) & _ & _).
    assert (Hk : (idx1 i < length argv)%nat) by (pose proof len_av; destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    assert (Harg : nth (idx1 i) argv [] = ARG argv0 argv1 i) by (destruct i; reflexivity).
    (* read_argv_byte_k is top-level at #38 and carries the launch conjunct itself
       (CatExec.v:656-664), so lay_bsb_nw is no longer threaded through it. *)
    (* Restored to r33's text verbatim.  r34 put a ZZDBG print inside the `ltac:(…)` argument
       (37 min, cancelled) and r35 replaced the whole application with `unshelve epose proof …
       _` to get the print onto its own line (45 min, cancelled).  Both touched this
       application's elaboration and both blew the unit's 14-minute norm; r33, which is this
       text, took 14 minutes.  A print in term position is re-run on every elaboration
       attempt, and an evar-heavy `unshelve` on a dependent application of this size is no
       cheaper.  If this side condition needs its goal printed, get it some other way --
       `About read_argv_byte_k` for the premise's shape costs nothing. *)
    pose proof (read_argv_byte_k Sv48 ASEGS
                  (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)
                  mbase APH entryw sp brk0 rdraw (idx1 i) j Hlau Hk
                  ltac:(change (in_argv (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) with argv;
                        rewrite Harg; exact Hj)) as RD.
    fold top in RD.
    (* RD speaks of [in_argv (inp …)], [in_envp (inp …)], [in_execfn (inp …)]; [rewrite] is
       syntactic, so name them as cat_argv_ptr_STR does before rewriting (AsanInit.v:381-382). *)
    change (in_argv (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) with argv in RD.
    change (in_envp (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) with envp in RD.
    change (in_execfn (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) with execfn in RD.
    rewrite (cat_argv_ptr_STR i Hi), word_add_nat, u64_lit in RD by lia. rewrite Harg in RD. fold SIMG in RD.
    rewrite <- wrap_above_sp in RD |- * || idtac.
    assert (Hm : M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = stack_to_mem sp SIMG (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))).
    { rewrite Hmem.
      2:{ pose proof W_facts as [W1 W2]. pose proof TOP_utop as TU. pose proof chead_lo.
          pose proof len_av. pose proof len_ev.
          unfold argH0. apply orb_true_intro. right. apply andb_true_intro.
          rewrite u64_lit by (unfold STR0, CHEAD, W in *; lia).
          unfold TOP, STR0, CHEAD, LSTR, W, rseq, top in *. unfold usp, argc, envc in *.
          split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      unfold SIMG. apply wrap_above_sp. rewrite u64_lit by lia. fold usp. lia. }
    rewrite Hm in Hb. cbn [rdn] in RD. rewrite Hb in RD. injection RD as RD'. unfold byte_at. exact RD'.
  Qed.

  (* [comment removed for export] *)
  Lemma istrlen_ecalls : is_ecall W_87b9c = false /\ is_ecall W_87ba0 = false /\ is_ecall W_87ba4 = false /\ is_ecall W_87ba8 = false
                         /\ is_ecall W_87bac = false /\ is_ecall W_87bb0 = false /\ is_ecall W_87bb4 = false.
  Proof. repeat split; reflexivity. Qed.

  Lemma Gro_asan : img_lo ASAN <= g_ro_lo (argtab_of ASAN) /\ g_ro_hi (argtab_of ASAN) <= img_hi ASAN.
  Proof. cbn. lia. Qed.

  Lemma Gfile_asan : img_lo ASAN <= g_file_lo (argtab_of ASAN) /\ g_file_hi (argtab_of ASAN) <= img_hi ASAN
                     /\ img_lo ASAN <= g_canary_got (argtab_of ASAN) /\ g_canary_got (argtab_of ASAN) + 8 <= img_hi ASAN
                     /\ img_lo ASAN <= g_canary (argtab_of ASAN) /\ g_canary (argtab_of ASAN) + 8 <= img_hi ASAN.
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma memchr_asan : forall mem (s : word) (buf : list byte) (K n : Z) rom regs (ret : word),
    rdn ASEGS mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    K + 8 <= n -> n < 2 ^ 64 ->
    (forall i, g_ro_lo (argtab_of ASAN) <= i < g_ro_hi (argtab_of ASAN) -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps ASEGS (mkst regs (Z_to_bv 64 (g_memchr (argtab_of ASAN))) mem rom) (mkst regs' ret mem rom)
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (bv_unsigned s + K).
  Proof.
    intros mem s buf K n rom regs ret Hbuf Hwin Hnw HK0 Hz Hnzj HKn Hn64 Hro Hret H1 H10 H11 H12.
    assert (HOK : mchrH mem s buf K n) by (constructor; try assumption; exact Hro).
    destruct (ref_memchr0 mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12) as (regs' & Hms & Hkc & Ha0).
    exists regs'. split; [replace (Z_to_bv 64 (g_memchr (argtab_of ASAN))) with (0x11caa4%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
    split; [|exact Ha0]. apply kept_regs. intros k Hin. apply Hkc. unfold callee_saved. kept_in_list Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma memcpy_asan : forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn ASEGS mem0 src (length bs) = Some bs ->
    store_ok ASEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps ASEGS (mkst regs (Z_to_bv 64 (x_memcpy ASAN)) mem0 (seg_rom ASEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom ASEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
  Proof.
    intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
    pose proof (u64_range dst) as Hdr.
    assert (HOK : mcH mem0 dst src n bs) by (constructor; try assumption; lia).
    destruct (AsanMemcpy.ref_memcpy mem0 dst src n bs (seg_rom ASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
    exists regs'. split; [replace (Z_to_bv 64 (x_memcpy ASAN)) with (0x11cba0%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
    split; [|rewrite <- R10; apply Hk; unfold callee_kept; in_list].
    apply kept_regs. intros k Hin. apply Hk. unfold callee_kept. kept_in_list Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma stdio_asan : forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments ASEGS H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok ASEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
    g_file_lo (argtab_of ASAN) <= f -> f + 232 <= g_file_hi (argtab_of ASAN) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn ASEGS mem (Z_to_bv 64 (g_canary_got (argtab_of ASAN))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary (argtab_of ASAN)))) ->
    rdn ASEGS mem (Z_to_bv 64 (g_canary (argtab_of ASAN))) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader model = true ->
    m_halted model = None ->
    0 <= wb <= wp -> wp < 0x800000000000 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->   (* [comment removed for export] *)
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 40 ->   (* [comment removed for export] *)
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 0x800000000000 ->   (* [comment removed for export] *)
    rdn ASEGS mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn ASEGS mem s (length extra) = Some extra ->
    ret_ok ret -> K [] ->
    (forall regs' mem',
       getr regs' 10%bv = l -> getr regs' 2%bv = Z_to_bv 64 su -> getr regs' 1%bv = ret ->
       getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
       getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
       getr regs' 21%bv = getr regs 21%bv -> getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv ->
       getr regs' 24%bv = getr regs 24%bv -> getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv ->
       getr regs' 27%bv = getr regs 27%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
       (forall x : word, ~ (su - 112 <= bv_unsigned x < su) -> ~ (f + 32 <= bv_unsigned x < f + 48) ->
                          ~ (f + 56 <= bv_unsigned x < f + 64) -> mem' x = mem x) ->
       mem_grows mem mem' ->
       rdn ASEGS mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn ASEGS mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn ASEGS mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       srealizes ASEGS (mkCfg (mkst regs' ret mem' (seg_rom ASEGS)) model) K) ->
    srealizes ASEGS (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write (argtab_of ASAN))) mem (seg_rom ASEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Proof.
    intros H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
           HH HL AVF AVP AVE Hsp' Ha0 Ha1 Ha2 Hra SUlo SUhi SOK0 Flo Fhi Fwp Fwb Ffd Fbuf Fbsz C1 C2 FD Hfd Hrdr Hh WBP WPhi
           LENP LENE MAX M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
    replace (Z_to_bv 64 (g_stdio_write (argtab_of ASAN))) with (0x113470%bv : word) by (apply bv_eq; reflexivity).
    apply (asan_stdio_write_s H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K); try assumption.
    - constructor; assumption.
    - split; [exact C1 | exact C2].
    - intros regs' mem' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      apply (HK regs' mem'); assumption.
  Qed.

  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kern execfn E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 sp rdraw argv envp kern execfn).
  (* [comment removed for export] *)
  Variable LINV : (word -> option byte) -> Prop.
  Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.

  Lemma vals_of_SV : forall E M, SV E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof. intros E M H. exact (vals_of_SINV1 E M (SV_to1 E M H)). Qed.
  Lemma rd_of_SV : forall E M (a : word), SV E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof. intros E M a H. exact (rd_of_SINV1 E M a (SV_to1 E M H)). Qed.
  Lemma str_of_SV : forall E M i j, SV E M -> arg_ok argc i -> (j <= length (ARG argv0 argv1 i))%nat ->
    M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = Some (byte_at (ARG argv0 argv1 i) j).
  Proof. intros E M i j H. exact (str_of_SINV1 E M i j (SV_to1 E M H)). Qed.

  Theorem asan_ext_sound : ext_stmt ASEGS ASAN NX0 LIMIT (xn ASEGS ASAN NX0) SV AH LINV FS0.
  Proof.
    intros id args.
    pose proof Lay_asan as LAY. pose proof istrlen_ecalls as EC.
    destruct id as [|[|[|[|[|[|[|[|id]]]]]]]]; cbn [xn].
    - eapply (xn_sound_argstrlen ASEGS ASAN NX0 LIMIT SV AH LINV FS0 asan_wx asan_in_hull asan_hull_ok SV_frame LINV_frame
               W_87b9c W_87ba0 W_87ba4 W_87ba8 W_87bac W_87bb0 W_87bb4);
        [cbn; lia | exact F_87b9c | exact F_87ba0 | exact F_87ba4 | exact F_87ba8 | exact F_87bac | exact F_87bb0 | exact F_87bb4
        | exact EC | exact D_87b9c | exact D_87ba0 | exact D_87ba4 | exact D_87ba8 | exact D_87bac | exact D_87bb0 | exact D_87bb4
        | exact LAY | exact Hnz_asan | exact vals_of_SV | exact str_of_SV ].
    - eapply (xn_sound_argmemchr ASEGS ASAN NX0 LIMIT SV AH LINV FS0 asan_wx asan_in_hull asan_hull_ok argH0_high_asan
               (argH0_agree sp rdraw argv envp kern execfn) NX0_ge SV_frame SV_agree LINV_frame);
        [exact LAY | exact Hnz_asan | exact vals_of_SV | exact rd_of_SV | exact str_of_SV | exact Gro_asan | exact memchr_asan].
    - eapply (xn_sound_argnul ASEGS ASAN NX0 LIMIT SV AH LINV FS0 asan_wx asan_in_hull asan_hull_ok SV_frame LINV_frame);
        [exact LAY | exact vals_of_SV | exact str_of_SV].
    - eapply (xn_sound_memcpyarg ASEGS ASAN NX0 LIMIT SV AH LINV FS0 asan_wx asan_in_hull asan_hull_ok argH0_high_asan
               (argH0_agree sp rdraw argv envp kern execfn) NX0_ge SV_frame SV_agree LINV_frame);
        [exact LAY | exact vals_of_SV | exact str_of_SV | exact memcpy_asan].
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
    - apply xn_sound_reldiff.
    - apply xn_sound_zerocover.
    - apply xn_sound_srlbound.
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
  Qed.

  Theorem asan_emit_sound : emit_stmt' ASEGS ASAN NX0 LIMIT SV AH LINV FS0.
  Proof.
    pose proof Lay_asan as LAY. pose proof istrlen_ecalls as EC.
    eapply (xe_sound ASEGS ASAN NX0 LIMIT SV AH LINV FS0 asan_in_hull asan_hull_ok argH0_high_asan
             (argH0_agree sp rdraw argv envp kern execfn) NX0_ge SV_frame SV_agree LINV_frame
             W_87b9c W_87ba0 W_87ba4 W_87ba8 W_87bac W_87bb0 W_87bb4);
      [cbn; lia | exact EC | exact LAY | exact vals_of_SV | exact str_of_SV | exact Gro_asan | exact stdio_asan | exact Gfile_asan
      | (* [comment removed for export] *)
        intros z Hz1 Hz2; change (g_file_lo (argtab_of ASAN)) with 0x12e590 in Hz1; change (g_file_hi (argtab_of ASAN)) with 0x12e988 in Hz2;
        unfold in_lfp; cbn [lib_fp ASAN existsb fst snd];
        destruct (Z.leb_spec 7279008 z); destruct (Z.ltb_spec z 6707736); cbn; try reflexivity; lia ].
  Qed.

End AsanInst.

(* [comment removed for export] *)
(* The section now ranges over the whole launch tuple (SINV1 is SINV0 of all of it), so the
   corollaries quantify over the same tuple and take every section premise; each goal
   [asan_ext_sound] leaves is one of them, or SINV1's own frame and agreement lemmas. *)
Corollary asan_ext_sound1 : forall sp rdraw brk0 mbase argv envp fs stdin uid hw apc gid groups net ur kern execfn nofile sigmask abt sdf,
  valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) ->
  forall (LINV : (word -> option byte) -> Prop),
  (forall M M' : word -> option byte, (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M') ->
  forall FS0, ext_stmt ASEGS ASAN NX0 LIMIT (xn ASEGS ASAN NX0) (SINV1 sp rdraw brk0 mbase argv envp fs stdin uid hw apc gid groups net ur kern execfn nofile sigmask abt sdf) (argH0 sp rdraw argv envp kern execfn) LINV FS0.
Proof.
  intros sp rdraw brk0 mbase argv envp fs stdin uid hw apc gid groups net ur kern execfn nofile sigmask abt sdf
    Hsp Hbrk Hmb Hva Hve Hfit Hkernel Hlau LINV LINV_frame FS0.
  eapply asan_ext_sound.
  all: first [ exact (fun E M H => H) | eassumption | (eapply SINV1_frame; eassumption) | (eapply SINV1_agree; eassumption) ].
Qed.
Corollary asan_emit_sound1 : forall sp rdraw brk0 mbase argv envp fs stdin uid hw apc gid groups net ur kern execfn nofile sigmask abt sdf,
  valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) = recorded_kernel (in_kernel (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf)) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (inp argv envp fs stdin uid gid hw groups net ur kern execfn nofile sigmask abt sdf) ->
  forall (LINV : (word -> option byte) -> Prop),
  (forall M M' : word -> option byte, (forall a : word, in_lfp ASAN (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M') ->
  forall FS0, emit_stmt ASEGS ASAN NX0 LIMIT (xe ASEGS ASAN NX0) (SINV1 sp rdraw brk0 mbase argv envp fs stdin uid hw apc gid groups net ur kern execfn nofile sigmask abt sdf) (argH0 sp rdraw argv envp kern execfn) LINV FS0.
Proof.
  intros sp rdraw brk0 mbase argv envp fs stdin uid hw apc gid groups net ur kern execfn nofile sigmask abt sdf
    Hsp Hbrk Hmb Hva Hve Hfit Hkernel Hlau LINV LINV_frame FS0.
  eapply asan_emit_sound.
  all: first [ exact (fun E M H => H) | eassumption | (eapply SINV1_frame; eassumption) | (eapply SINV1_agree; eassumption) ].
Qed.

End FPW_2.
