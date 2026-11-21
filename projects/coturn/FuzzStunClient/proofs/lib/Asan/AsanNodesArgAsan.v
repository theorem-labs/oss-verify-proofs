(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the argument nodes use AsanInit's full LPS 727298f3 launch and the top-relative strings, with layout and read proofs following AsanNodesStartX.v, carry the flag of the flagged relation SpinAlg.srealizesM and the launch's rseq layout, and take the stdio write's channel reader. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib RefLayout ArgvEnv StartupAux AsanAcct AsanAcctShape.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanAcctImages AsanMemcpyBase AsanMemcpy AsanMemchr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanAcctNoLazy AsanStdioDefs AsanStdioWriteS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import ArgLoops AsanNodesArg AsanNodesArgSound AsanNodesEmitSound AsanNodesFactSound Arg_code_istrlen_asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Fixpoint noblob (e : expr) : bool :=
  match e with
  | EBlob _ _ _ _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => noblob a && noblob b
  | EExt _ _ _ a => noblob a
  | _ => true
  end.

Lemma edenot_ev_only : forall E E' b e,
  expr_vars_lt b e = true -> noblob e = true -> (forall n, (n < b)%N -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros E E' b e. induction e; intros Hv Hb Hag; cbn [edenot]; cbn [expr_vars_lt noblob] in Hv, Hb; try reflexivity.
  - apply Hag. apply N.ltb_lt. exact Hv.
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

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
(* [comment removed for export] *)
#[local] Ltac kept_in_list Hin :=
  cbn [In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [in_list|]); destruct Hin.

Section AsanInst.
Context {sfl : bool}.   (* the flag of [SpinAlg.srealizesM] *)
  Context {rsb : bool}.   (* the launch's kb_rseq; the table is ASAN_at/BOTH_at (rseq_z rsb) *)
  Variable ph : PhdrInfo.
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Context {sigpipe_default : bool}.   (* AsanInit's: the launch's SIGPIPE disposition at entry *)
  Variable FS0 : Fs.Fs.

  Let INP := @AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default.
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  Hypothesis IMG : img_facts ASEGS (ASAN_at (rseq_z rsb)) ph.
  Hypothesis Hapc : Z.of_N apc = a_entry (ASAN_at (rseq_z rsb)).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hrs : a_rseq (ASAN_at (rseq_z rsb)) = rseq_z (kb_rseq kb).

  Let rseq := kb_rseq kb.
  Let top := ed_top rdraw.
  Let bsb := entry_stack_image INP mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  Let argv1 := nth 1 argv [].
  Let L0 := Z.of_nat (length argv0).
  Let L1 := Z.of_nat (length argv1).
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Let TOP := bv_unsigned top - 8.
  #[local] Notation E0L := (E0 sp rdraw brk0 argv envp uid gid kb execfn).

  (* [comment removed for export] *)
  Definition SINV1 (E : env) (M : word -> option byte) : Prop :=
    @SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default E M
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.

  Lemma SINV1_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV1 E M -> SINV1 E M'.
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

  Lemma W_facts : 0 <= W <= 4110.
  Proof. unfold W, rseq, top. eapply AsanInit.pad_range; eassumption. Qed.

  Lemma str0_split : STR0 = usp + CHEAD + W.
  Proof. unfold STR0, CHEAD, W, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = bv_unsigned top.
  Proof.
    rewrite str0_split. unfold usp, CHEAD, W, LSTR, rseq, top.
    eapply AsanInit.str0_hi; eassumption.
  Qed.

  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof.
    unfold usp, bsb.
    exact (entry_stack_image_no_wrap Sv48 INP mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma TOP_eq : TOP = usp + Z.of_nat (length bsb) - 8.
  Proof.
    unfold bsb. rewrite (length_entry_stack_image_launch Sv48 INP mbase ph entryw sp brk0 rdraw Hlau).
    unfold TOP, usp, top. lia.
  Qed.

  Lemma str0_ge : usp <= STR0.
  Proof. unfold STR0. lia. Qed.

  Lemma strings_fit : Z.of_nat (total_arg_bytes_nat argv) <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes. rewrite !PropExec.length_flatten_strings. lia.
  Qed.

  Lemma argv0_fit : L0 + 1 <= Z.of_nat (total_arg_bytes_nat argv).
  Proof.
    unfold L0, argv0. destruct argv as [|a0 rest]; [destruct Hva as [H _]; cbn in H; lia|].
    cbn [nth]. rewrite total_arg_bytes_cons. lia.
  Qed.

  Lemma argv01_fit : 2 <= argc -> L0 + 1 + L1 + 1 <= Z.of_nat (total_arg_bytes_nat argv).
  Proof.
    unfold L0, L1, argv0, argv1, argc. destruct argv as [|a0 [|a1 rest]]; cbn [length nth]; try lia.
    rewrite !total_arg_bytes_cons. lia.
  Qed.

  Lemma Lay_asan : 0x7fff80000000 <= usp /\ usp + 176 <= STR0 /\ STR0 + L0 + 1 <= TOP
                   /\ (2 <= argc -> STR0 + L0 + 1 + L1 + 1 <= TOP)
                   /\ TOP mod 8 = 0 /\ TOP + 8 <= 2 ^ 47 /\ L0 <= 131071 /\ L1 <= 131071 /\ 1 <= argc <= 1024.
  Proof.
    pose proof len_av. pose proof usp_lo. pose proof L0_le. pose proof L1_le.
    pose proof W_facts. pose proof strings_fit. pose proof argv0_fit. pose proof str0_hi. pose proof str0_split.
    assert (HC : 480 <= CHEAD <= 10752) by (unfold CHEAD, rseq; eapply AsanInit.chead_range; eassumption).
    assert (HT : bv_unsigned top <= 2 ^ 47).
    { pose proof (entry_page_top_within_window Sv48 INP mbase sp brk0 rdraw Hlau) as HT.
      change (bv_unsigned top <= 2 ^ 47) in HT. exact HT. }
    assert (HA : bv_unsigned top mod 4096 = 0).
    { pose proof Hlau as HL. destruct HL as ((HA & _ & _) & _ & _).
      change (bv_unsigned top mod 4096 = 0) in HA. exact HA. }
    pose proof (Z.div_mod (bv_unsigned top) 4096 ltac:(lia)).
    unfold TOP in *. repeat split; try lia.
    intros Hargc2. pose proof (argv01_fit Hargc2). lia.
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
  Lemma argH0_high_asan : forall E (a : word), argH0 sp rdraw argv envp kb execfn E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply AsanInit.argH0_high; eassumption. Qed.

  Lemma vals_of_SINV1 : forall E M, SINV1 E M ->
    uE E e_sp0 = usp /\ uE E (e_str0 (ASAN_at (rseq_z rsb))) = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof.
    intros E M ((Hev & Hmem) & B1 & B2).
    assert (AG : forall e, expr_vars_lt NX0 e = true -> noblob e = true -> edenot E e = edenot E0L e).
    { intros e He Hb. apply (edenot_ev_only E _ NX0 e He Hb). exact Hev. }
    assert (U0 : uE E0L e_sp0 = usp) by (unfold usp; eapply AsanInit.u_e_sp0; eassumption).
    assert (U1 : uE E0L (e_str0 (ASAN_at (rseq_z rsb))) = usp + CHEAD + W)
      by (unfold usp, CHEAD, W, rseq, top; eapply AsanInit.u_e_str0; eassumption).
    rewrite <- str0_split in U1.
    unfold uE in *. rewrite (AG e_sp0) by reflexivity.
    rewrite (AG (e_str0 (ASAN_at (rseq_z rsb)))) by (destruct rsb; reflexivity).
    change (edenot E (EVar V_L0)) with (ev E 3%N). change (edenot E (EVar V_ARGC)) with (ev E 1%N).
    change (edenot E (EVar V_L1)) with (ev E 7%N).
    rewrite (Hev 3%N), (Hev 1%N), (Hev 7%N) by (unfold NX0; lia).
    repeat split; try assumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_of_SINV1 : forall E M (a : word), SINV1 E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof.
    intros E M a ((Hev & Hmem) & _ & _) Ha. pose proof TOP_eq. pose proof str0_ge.
    rewrite Hmem.
    2:{ unfold argH0. apply orb_true_intro. right. apply andb_true_intro.
        (* [HBL] says [bv_unsigned top] while the goal says [bv_unsigned (ed_top rdraw)]; [lia] is
           syntactic on atoms, so it treats them as two unrelated quantities although they are
           convertible.  Pose everything BEFORE the [unfold … in *] so the same normalisation reaches
           the hypotheses and the goal together. *)
        assert (HT : bv_unsigned sp + Z.of_nat (block_head_size rseq argv envp)
                     + Z.of_nat (block_pad_len rseq sp top argv envp execfn)
                     + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top)
          by (unfold rseq, top; eapply AsanInit.str0_hi; eassumption).
        assert (HBL : Z.of_nat (length bsb) = bv_unsigned top - bv_unsigned sp)
          by (unfold bsb, top; eapply AsanInit.length_bsb_eq; eassumption).
        pose proof strings_fit.
        rewrite str0_split in Ha. unfold usp, CHEAD, W, rseq, top, TOP in *.
        split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    (* The goal has the image EXPANDED — [entry_stack_image (inp argv envp …) mbase ph
       (Z_to_bv 64 (Z.of_N apc)) sp rdraw] — where [bsb]'s body names the two let-bound atoms [INP]
       and [entryw], so a bare [fold bsb] matches nothing and the [if] stays stuck.  Fold the two inner
       lets first, so the goal and the hypotheses speak of the same atoms. *)
    rewrite wrap_above_sp by (fold usp; lia). unfold stack_to_mem.
    fold INP. fold entryw. fold bsb. fold usp.
    replace (usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia).
    replace (bv_unsigned a - usp <? Z.of_nat (length bsb)) with true
      by (symmetry; apply Z.ltb_lt; lia).
    destruct (nth_error bsb (Z.to_nat (bv_unsigned a - usp))) as [b|] eqn:Hn;
      [exists b;
       reflexivity |].
    apply nth_error_None in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cat_argv_ptr_STR : forall i, arg_ok argc i ->
    cat_argv_ptr top argv envp execfn (idx1 i) = Z_to_bv 64 (STR STR0 argv0 i).
  Proof.
    intros i Hi. pose proof len_av as LA.
    assert (Hk : (idx1 i < length argv)%nat) by (destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    rewrite (cat_argv_ptr_offset top argv envp execfn (idx1 i) Hk).
    (* Same let-vs-body family as [bsb] above: the equation comes out over [in_argv INP] … while
       the goal names the section variables, so the rewrite found no subterm.  Reduce the record
       projections of [INP] (AsanInit.inp_argv/_envp/_execfn) and fold [top] first. *)
    pose proof (cat_string_base_offset Sv48 INP mbase sp brk0 rdraw Hlau) as CSB.
    unfold INP in CSB.
    (* The kernel projection goes with the other three: without it [kb_rseq (in_kernel (inp …))] and
       [kb_rseq kb] stay apart as two atoms. *)
    rewrite ?AsanInit.inp_argv, ?AsanInit.inp_envp, ?AsanInit.inp_execfn, ?AsanInit.inp_kernel in CSB.
    fold top in CSB. rewrite CSB. clear CSB.
    rewrite nat_to_word_add_merge, word_add_nat. f_equal.
    destruct i as [|i]; cbn [idx1 STR].
    - change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat. unfold STR0, usp, rseq, top.
      lia.
    - rewrite total_firstn1 by (unfold argc in LA; lia). unfold STR0, usp, rseq, top, argv0.
      lia.
  Qed.

  Lemma str_of_SINV1 : forall E M i j, SINV1 E M -> arg_ok argc i -> (j <= length (ARG argv0 argv1 i))%nat ->
    M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = Some (byte_at (ARG argv0 argv1 i) j).
  Proof.
    intros E M i j HS Hi Hj.
    pose proof Lay_asan as LAY. pose proof (STR_range usp STR0 TOP argc argv0 argv1 LAY i Hi) as [R1 R2].
    pose proof (STR_bounds usp STR0 TOP argc argv0 argv1 LAY i) as SB.
    assert (S0 : STR0 <= STR STR0 argv0 i) by (destruct i; cbn [STR]; lia).
    unfold LEN in R2.
    destruct (rd_of_SINV1 E M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) HS) as [b Hb].
    { rewrite u64_lit; lia. }
    rewrite Hb. f_equal.
    destruct HS as ((Hev & Hmem) & _ & _).
    assert (Hk : (idx1 i < length argv)%nat) by (pose proof len_av; destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    assert (Harg : nth (idx1 i) argv [] = ARG argv0 argv1 i) by (destruct i; reflexivity).
    pose proof (read_argv_byte_k Sv48 ASEGS INP mbase ph entryw sp brk0 rdraw (idx1 i) j Hlau Hk
                  ltac:(rewrite <- Harg in Hj; exact Hj)) as RD.
    (* [read_argv_byte_k] comes out over [INP]'s projections; put it back in this Section's names
       before the rewrites below look for [argv]/[top]. *)
    unfold INP in RD.
    rewrite ?AsanInit.inp_argv, ?AsanInit.inp_envp, ?AsanInit.inp_execfn, ?AsanInit.inp_kernel in RD.
    fold top in RD. fold entryw in RD.
    rewrite (cat_argv_ptr_STR i Hi), word_add_nat, u64_lit in RD by lia. rewrite Harg in RD.
    (* The last step rewrites [Hb] into [RD], which needs [RD]'s memory to be the folded
       [stack_to_mem sp bsb …] again, so put [INP]/[entryw]/[bsb] back now that the rewrites
       that needed them open are done. *)
    fold INP in RD. fold entryw in RD. fold bsb in RD.
    assert (Hm : M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))
                 = stack_to_mem sp bsb (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))).
    { rewrite Hmem.
      2:{ unfold argH0. apply orb_true_intro. right. apply andb_true_intro.
          rewrite u64_lit by lia. pose proof str0_hi. pose proof str0_split as SS.
          (* [STR], [ARG] and [LEN] are matches on [i], which [lia] cannot see through, and
             [rewrite str0_split in S0] would also rewrite the [STR0] INSIDE the atom
             [STR STR0 argv0 i].  Case-split [i] instead.  Each branch then needs
             [STR0 + j < bv_unsigned (ed_top rdraw)].
             That is [Lay_asan]'s third and fourth conjuncts ([STR0 + L0 + 1 <= TOP], and with two
             arguments [STR0 + L0 + 1 + L1 + 1 <= TOP]), so take them rather than rebuild the
             arithmetic; [STR0] stays folded so it is one atom on both sides, and only the names
             the goal spells out are opened. *)
          pose proof len_av.
          pose proof Lay_asan as LY; destruct LY as (LY1 & LY2 & LY3 & LY4 & _).
          (* [unfold … in *] leaves a name folded in a hypothesis when it does not also occur in
             the goal ([top] in [LY3], where the goal says [ed_top rdraw]).  Open the two bounds in
             the hypotheses themselves. *)
          unfold L0, TOP, top in LY3.
          assert (B1 : 2 <= argc ->
                       STR0 + Z.of_nat (length argv0) + 1 + Z.of_nat (length argv1) + 1
                       <= bv_unsigned (ed_top rdraw) - 8)
            by (intros A2; specialize (LY4 A2); unfold L0, L1, TOP, top in LY4; exact LY4).
          clear LY4;
          destruct i; cbn [STR ARG LEN idx1 arg_ok] in *;
          [ clear B1
          | specialize (B1 ltac:(unfold argc in *; lia)) ];
          unfold usp, CHEAD, W, rseq, top in *; try (unfold TOP in *);
          (split; [apply Z.leb_le | apply Z.ltb_lt]);
            lia. }
      apply wrap_above_sp. rewrite u64_lit by lia. fold usp. lia. }
    rewrite Hm in Hb. cbn [rdn] in RD. rewrite Hb in RD. injection RD as RD'. unfold byte_at. exact RD'.
  Qed.

  (* [comment removed for export] *)
  Lemma istrlen_ecalls : is_ecall W_66310 = false /\ is_ecall W_66314 = false /\ is_ecall W_66318 = false /\ is_ecall W_6631c = false
                         /\ is_ecall W_66320 = false /\ is_ecall W_66324 = false /\ is_ecall W_66328 = false.
  Proof. repeat split; reflexivity. Qed.

  Lemma Gro_asan : img_lo (ASAN_at (rseq_z rsb)) <= g_ro_lo (argtab_of (ASAN_at (rseq_z rsb))) /\ g_ro_hi (argtab_of (ASAN_at (rseq_z rsb))) <= img_hi (ASAN_at (rseq_z rsb)).
  Proof. cbn. lia. Qed.

  Lemma Gfile_asan : img_lo (ASAN_at (rseq_z rsb)) <= g_file_lo (argtab_of (ASAN_at (rseq_z rsb))) /\ g_file_hi (argtab_of (ASAN_at (rseq_z rsb))) <= img_hi (ASAN_at (rseq_z rsb))
                     /\ img_lo (ASAN_at (rseq_z rsb)) <= g_canary_got (argtab_of (ASAN_at (rseq_z rsb))) /\ g_canary_got (argtab_of (ASAN_at (rseq_z rsb))) + 8 <= img_hi (ASAN_at (rseq_z rsb))
                     /\ img_lo (ASAN_at (rseq_z rsb)) <= g_canary (argtab_of (ASAN_at (rseq_z rsb))) /\ g_canary (argtab_of (ASAN_at (rseq_z rsb))) + 8 <= img_hi (ASAN_at (rseq_z rsb)).
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma memchr_asan : forall mem (s : word) (buf : list byte) (K n : Z) rom regs (ret : word),
    rdn ASEGS mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    K + 8 <= n -> n < 2 ^ 64 ->
    (forall i, g_ro_lo (argtab_of (ASAN_at (rseq_z rsb))) <= i < g_ro_hi (argtab_of (ASAN_at (rseq_z rsb))) -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps ASEGS (mkst regs (Z_to_bv 64 (g_memchr (argtab_of (ASAN_at (rseq_z rsb))))) mem rom) (mkst regs' ret mem rom)
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (bv_unsigned s + K).
  Proof.
    intros mem s buf K n rom regs ret Hbuf Hwin Hnw HK0 Hz Hnzj HKn Hn64 Hro Hret H1 H10 H11 H12.
    assert (HOK : mchrH mem s buf K n) by (constructor; try assumption; exact Hro).
    destruct (ref_memchr0 mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12) as (regs' & Hms & Hkc & Ha0).
    exists regs'. split; [replace (Z_to_bv 64 (g_memchr (argtab_of (ASAN_at (rseq_z rsb))))) with (0xa40b0%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
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
      msteps ASEGS (mkst regs (Z_to_bv 64 (x_memcpy (ASAN_at (rseq_z rsb)))) mem0 (seg_rom ASEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom ASEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
  Proof.
    intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
    pose proof (u64_range dst) as Hdr.
    assert (HOK : mcH mem0 dst src n bs) by (constructor; try assumption; lia).
    destruct (AsanMemcpy.ref_memcpy mem0 dst src n bs (seg_rom ASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
    exists regs'. split; [replace (Z_to_bv 64 (x_memcpy (ASAN_at (rseq_z rsb)))) with (0xa41ac%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
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
    g_file_lo (argtab_of (ASAN_at (rseq_z rsb))) <= f -> f + 232 <= g_file_hi (argtab_of (ASAN_at (rseq_z rsb))) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn ASEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn ASEGS mem (Z_to_bv 64 (g_canary_got (argtab_of (ASAN_at (rseq_z rsb))))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary (argtab_of (ASAN_at (rseq_z rsb)))))) ->
    rdn ASEGS mem (Z_to_bv 64 (g_canary (argtab_of (ASAN_at (rseq_z rsb))))) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    (* LPS 08b1429: [asan_stdio_write_s]'s own visible reader premise (AsanStdioWriteS.v:811),
       matching the [STDIO] hypothesis this lemma discharges. *)
    m_channel_reader model = true ->
    m_halted model = None ->
    0 <= wb <= wp -> wp <= 2 ^ 47 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 2 ^ 47 ->
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
       srealizesM ASEGS sfl (mkCfg (mkst regs' ret mem' (seg_rom ASEGS)) model) K) ->
    srealizesM ASEGS sfl (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write (argtab_of (ASAN_at (rseq_z rsb))))) mem (seg_rom ASEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Proof.
    intros H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
           HH HL AVF AVP AVE Hsp' Ha0 Ha1 Ha2 Hra SUlo SUhi SOK0 Flo Fhi Fwp Fwb Ffd Fbuf Fbsz C1 C2 FD Hfd HCR Hh WBP WPhi
           LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
    replace (Z_to_bv 64 (g_stdio_write (argtab_of (ASAN_at (rseq_z rsb))))) with (0x9fea4%bv : word) by (apply bv_eq; reflexivity).
    apply (asan_stdio_write_s H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K); try assumption.
    (* The remaining goals are dispatched by shape, not by position. *)
    all: try (intros regs' mem'; repeat intro;
              (* The continuation's POST is the RECORD [sw_post mem su f bufp bufsz mem']
                 (AsanStdioDefs.v:41-52, fields swp_agree swp_grows swp_wend swp_wpos swp_wbase), not a conjunction. *)
              repeat match goal with
                     | H : _ /\ _ |- _ => destruct H
                     | H : sw_post _ _ _ _ _ _ |- _ => destruct H
                     end;
              apply (HK regs' mem'); assumption).
    all: try (split; [exact C1 | exact C2]).
    all: try (constructor; assumption).
  Qed.

  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 sp rdraw argv envp kb execfn).

  Lemma vals_of_SV : forall E M, SV E M ->
    uE E e_sp0 = usp /\ uE E (e_str0 (ASAN_at (rseq_z rsb))) = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof. intros E M H. exact (vals_of_SINV1 E M (SV_to1 E M H)). Qed.
  Lemma rd_of_SV : forall E M (a : word), SV E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof. intros E M a H. exact (rd_of_SINV1 E M a (SV_to1 E M H)). Qed.
  Lemma str_of_SV : forall E M i j, SV E M -> arg_ok argc i -> (j <= length (ARG argv0 argv1 i))%nat ->
    M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = Some (byte_at (ARG argv0 argv1 i) j).
  Proof. intros E M i j H. exact (str_of_SINV1 E M i j (SV_to1 E M H)). Qed.

  Lemma NX0_ok_asan : APS.nx0_ok NX0.   (* [comment removed for export] *)
  Proof. unfold APS.nx0_ok, NX0. lia. Qed.

  (* NO #[using]: an explicit list force-generalises every name in it, used or not, and would carry [Hzr]
     ([AsanCeil.zero_random_draw]), which AsanInit's own comment records as FALSE on every real run, into a
     theorem whose layout and read proofs never touch it — making the exported [ext_stmt] conditional on a
     draw no real launch satisfies, and vacuous exactly where it is meant to apply.  Rocq's own discharge
     generalises over what the proof term reads and nothing else. *)
  Theorem asan_ext_sound : ext_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT (xn ASEGS (ASAN_at (rseq_z rsb)) NX0) SV AH FS0 sfl.
  Proof.
    intros id args.
    pose proof Lay_asan as LAY. pose proof istrlen_ecalls as EC.
    destruct id as [|[|[|[|[|[|[|[|id]]]]]]]]; cbn [xn].
    - eapply (xn_sound_argstrlen ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT SV AH FS0 asan_wx asan_in_hull asan_hull_ok SV_frame
               W_66310 W_66314 W_66318 W_6631c W_66320 W_66324 W_66328)
        with (usp := usp) (STR0 := STR0) (TOP := TOP) (argc := argc) (argv0 := argv0) (argv1 := argv1);
        [cbn; lia | exact F_66310 | exact F_66314 | exact F_66318 | exact F_6631c | exact F_66320 | exact F_66324 | exact F_66328
        | exact EC | exact D_66310 | exact D_66314 | exact D_66318 | exact D_6631c | exact D_66320 | exact D_66324 | exact D_66328
        | exact LAY | exact Hnz_asan | exact vals_of_SV | exact str_of_SV ].
    - eapply (xn_sound_argmemchr ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT SV AH FS0 asan_wx asan_in_hull asan_hull_ok argH0_high_asan
               (argH0_agree sp rdraw argv envp kb execfn) SV_frame SV_agree)
        with (usp := usp) (STR0 := STR0) (TOP := TOP) (argc := argc) (argv0 := argv0) (argv1 := argv1);
        [exact NX0_ok_asan | exact LAY | exact Hnz_asan | exact vals_of_SV | exact rd_of_SV | exact str_of_SV | exact Gro_asan | exact memchr_asan].
    - eapply (xn_sound_argnul ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT SV AH FS0 asan_wx asan_in_hull asan_hull_ok SV_frame)
        with (usp := usp) (STR0 := STR0) (TOP := TOP) (argc := argc) (argv0 := argv0) (argv1 := argv1);
        [exact LAY | exact vals_of_SV | exact str_of_SV].
    - eapply (xn_sound_memcpyarg ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT SV AH FS0 asan_wx asan_in_hull asan_hull_ok argH0_high_asan
               (argH0_agree sp rdraw argv envp kb execfn) SV_frame SV_agree)
        with (usp := usp) (STR0 := STR0) (TOP := TOP) (argc := argc) (argv0 := argv0) (argv1 := argv1);
        [exact NX0_ok_asan | exact LAY | exact vals_of_SV | exact str_of_SV | exact memcpy_asan | idtac ..].
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
    - apply xn_sound_reldiff.
    - apply xn_sound_zerocover.
    - apply xn_sound_srlbound.
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
  Qed.

  (* NO #[using]: see [asan_ext_sound] above — an explicit list would force [Hzr] into this statement too. *)
  Theorem asan_emit_sound : emit_stmt' ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT SV AH FS0 sfl.
  Proof.
    pose proof Lay_asan as LAY. pose proof istrlen_ecalls as EC.
    eapply (xe_sound ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT SV AH FS0 asan_in_hull asan_hull_ok argH0_high_asan
             (argH0_agree sp rdraw argv envp kb execfn) SV_frame SV_agree NX0_ok_asan
             W_66310 W_66314 W_66318 W_6631c W_66320 W_66324 W_66328)
      with (usp := usp) (STR0 := STR0) (TOP := TOP) (argc := argc) (argv0 := argv0) (argv1 := argv1);
      [cbn; lia | exact EC | exact LAY | exact vals_of_SV | exact str_of_SV | exact Gro_asan | exact stdio_asan | exact Gfile_asan].
  Qed.

End AsanInst.

(* [comment removed for export] *)
Corollary asan_ext_sound1 {rsb : bool} :
  forall ph apc sp (rdraw : EntryDraw) brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default,
  img_facts ASEGS (ASAN_at (rseq_z rsb)) ph -> Z.of_N apc = a_entry (ASAN_at (rseq_z rsb)) ->
  valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
  valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid ->
  (* NO [AsanCeil.zero_random_draw] premise: AsanInit records it as FALSE on every real run, and neither
     this statement nor [asan_ext_sound] reads it.  Carrying it would make the exported [ext_stmt] vacuous
     exactly where it is meant to apply. *)
  valid_launch (@AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (@AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default) ->
  a_rseq (ASAN_at (rseq_z rsb)) = rseq_z (kb_rseq kb) ->
  forall FS0 (sfl : bool), ext_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT (xn ASEGS (ASAN_at (rseq_z rsb)) NX0)
    (@SINV1 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default)
    (argH0 sp rdraw argv envp kb execfn) FS0 sfl.
Proof.
  intros ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default
    IMG Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hlaunch Hlau Hrs FS0 sfl.
  eapply asan_ext_sound;
    solve [ eassumption | exact (fun E M H => H) | apply SINV1_frame | apply SINV1_agree ].
Qed.
Corollary asan_emit_sound1 {rsb : bool} :
  forall ph apc sp (rdraw : EntryDraw) brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default,
  img_facts ASEGS (ASAN_at (rseq_z rsb)) ph -> Z.of_N apc = a_entry (ASAN_at (rseq_z rsb)) ->
  valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
  valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid ->
  (* NO [AsanCeil.zero_random_draw] premise: see [asan_ext_sound1] above. *)
  valid_launch (@AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (@AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default) ->
  a_rseq (ASAN_at (rseq_z rsb)) = rseq_z (kb_rseq kb) ->
  forall FS0 (sfl : bool), emit_stmt ASEGS (ASAN_at (rseq_z rsb)) NX0 LIMIT (xe ASEGS (ASAN_at (rseq_z rsb)) NX0)
    (@SINV1 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default)
    (argH0 sp rdraw argv envp kb execfn) FS0 sfl.
Proof.
  intros ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sigpipe_default
    IMG Hapc Hsp Hbrk Hmb Hva Hve Hfit Huid Hlaunch Hlau Hrs FS0 sfl.
  eapply asan_emit_sound;
    solve [ eassumption | exact (fun E M H => H) | apply SINV1_frame | apply SINV1_agree ].
Qed.
