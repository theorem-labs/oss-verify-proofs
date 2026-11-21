(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the reserved-interval ledger, the nine-byte string read-ahead, the rseq-dependent auxv, the launch input's kernel build): changed AH, CHKD, CHKS and 25 more; added A0, CSOK, Hapc and 44 more; removed entg_stack_defined, g_argH_defined, g_simg_top and 1 more. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm9DefsK Pm9PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Pm9HandoffK Pm9ArtCellsK Pm9DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface HeapIfaceA ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition tid_chk (cs : acs) : bool :=
  match kfind_word (kn cs) (ELit 0) 0x691ce8 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end.

(* The usage path (argc <> 2): the same entry facts as [Pm9DrvEntryK] at any argc,
   for argv[0] only.

   PORT, old beside new, in one place so the lemmas below can stay short:
     OLD  Section over sp brk0 rdraw argv envp uid hw fs (Hsp Hva Hve Hfit), with
          drv_chk / stk_chk unparameterised, the string area just above the auxv
          ([usp + 8*argc + 8*envc + 184]) and every [Pm9DrvEntryK] lemma applied
          positionally over those eight places.
     NEW  [HandoffBridgeK] Section Image's 22-place launch Section; drv_chk/stk_chk
          take the run's CONFIG_RSEQ flag [RZ]; argv[0] is at [STRLO], the top of
          the stack VMA less the string bytes; every [Pm9DrvEntryK] lemma is reached
          by [eapply X; sec], because a Section lemma's arity is the set of Section
          variables its proof USES, which the text does not show.
   Deleted: [wsb_eqG] (its subject, a count of string WORDS below AT_RANDOM, no
   longer exists -- see [Pm9DrvEntryK]'s note at [wsb_eq]) and the private
   [entg_stack_defined] copy (the stack-wide lemma is argc-general and lives in
   [Pm9DrvEntryK] alone). *)
Section EntryG.
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation rseq := (kb_rseq (in_kernel INP)).
  #[local] Notation RZ := (rseq_z rseq).
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKD : drv_chk RZ cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation A0 := (as0_A0 EXTRA cs E).
  #[local] Notation Hx := (ahid A0 model).
  #[local] Notation MV := (mrestrict Hx FULL).
  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation argc := (Z.of_nat (length argv)).
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation L0 := (Z.of_nat (length (nth 0 argv []))).
  #[local] Notation utop := (bv_unsigned (ed_top rdraw)).
  #[local] Notation STRLO := (usp + Z.of_nat (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)).

  Local Ltac sec := first [ eassumption | exact asan0_in_hull | exact asan0_hull_ok | exact asan0_img_facts ].

  Ltac LINEQ e Hn H :=
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.
  Ltac rz_split Ers := destruct (kb_rseq (in_kernel INP)) eqn:Ers; cbn [rseq_z AUXSZ] in *.

  Lemma g_vals : VZ E 1 = argc /\ VZ E 2 = envc /\ VZ E 3 = L0 /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. eapply ent_vals; sec. Qed.
  Lemma g_sp0 : uE E e_sp0 = usp.
  Proof. eapply sp0_val; sec. Qed.
  Lemma g_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.
  Lemma g_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256 /\ 0 <= L0 <= 131071.
  Proof.
    pose proof Hve as [Hle _]. pose proof Hva as (Hac & _ & Hfa & _).
    split; [exact Hac|]. split; [lia|]. split; [lia|].
    destruct argv as [|a l]; [cbn in Hac; lia|]. inversion Hfa as [|x l' Hx _]; subst. cbn [nth]. exact Hx.
  Qed.
  (* [vis_high] stays at [usp - 8388608]: weaker than the narrowed window supports,
     not false (the lead's ruling); its callers pass addresses above [usp]. *)
  Lemma g_vis_high : forall x : word, usp - 8388608 <= bv_unsigned x -> Hx x = false.
  Proof. intros x H. eapply vis_high; sec. Qed.

  (* [Pm9DrvEntryK.drv_chk_parts] at this launch, restated by statement so that
     nothing below depends on that lemma's discharged arity. *)
  Lemma g_dparts :
    pc cs = 0xaf0a4
    /\ (forall r e, In (r, e) DRV_REGS -> sr_get (s_regs (a_ss cs)) (Z_to_bv 5 r) = e)
    /\ lin_nowrapR (kn cs) e_sp0 = true /\ lin_nowrapR (kn cs) (KE_SPK (-48)) = true /\ lin_nowrapR (kn cs) (KE_SPK 8) = true
    /\ lin_nowrapR (kn cs) e_envp = true /\ lin_nowrapR (kn cs) (e_str0 RZ) = true /\ lin_nowrapR (kn cs) (e_str1 RZ) = true
    /\ kfind_word (kn cs) e_sp0 0 8 = Some (EVar 1) /\ kfind_word (kn cs) e_sp0 8 8 = Some (e_str0 RZ)
    /\ kfind_word (kn cs) e_sp0 16 8 = Some (e_argv1w RZ)
    /\ kfind_wr (kn cs) e_sp0 (- DRV_WINDOW) = Some (ELit DRV_WINDOW)
    /\ (exists v, kfind_word (kn cs) (ELit 0) 0x6b1dd0 8 = Some v /\ kfind_word (kn cs) (ELit 0) 0x691d80 8 = Some v)
    /\ (forall lo hi, In (lo, hi) DRV_IMG -> img_cover (kn cs) lo hi = true)
    /\ a_fd cs = FdStd.
  Proof. eapply drv_chk_parts; sec. Qed.

  Lemma gval_spk48 : edenot E (KE_SPK (-48)) = Z_to_bv 64 (usp - 48).
  Proof.
    destruct g_dparts as (_ & _ & _ & L2 & _). destruct g_vals as (_ & _ & _ & U0). pose proof g_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK (-48)))) as x eqn:Ex. LINEQ (KE_SPK (-48)) L2 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma gval_spk8 : edenot E (KE_SPK 8) = Z_to_bv 64 (usp + 8).
  Proof.
    destruct g_dparts as (_ & _ & _ & _ & L3 & _). destruct g_vals as (_ & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK 8))) as x eqn:Ex. LINEQ (KE_SPK 8) L3 H0. rewrite <- Ex in H0. lia.
  Qed.
  (* RENAME, value unchanged: [KE_ENVP] -> the plan's [e_envp]. *)
  Lemma gval_envp : edenot E e_envp = Z_to_bv 64 (usp + 16 + 8 * argc).
  Proof.
    destruct g_dparts as (_ & _ & _ & _ & _ & L4 & _). destruct g_vals as (U1 & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E e_envp)) as x eqn:Ex. LINEQ e_envp L4 H0. rewrite <- Ex in H0. lia.
  Qed.
  (* STATEMENT CHANGED, old beside new:
       OLD  edenot E KE_P0 = Z_to_bv 64 (usp + 8*argc + 8*envc + 184)
       NEW  edenot E (e_str0 RZ) = Z_to_bv 64 (usp + 8*argc + 8*envc + 472 + 32*RZ + 8*(VZ E 11) + VZ E 4)
     [Pm9DrvEntryK.val_p0] at any argc: e_auxv (usp + 8*argc + 8*envc + 24) + AUXSZ RZ
     + the STACK_ROUND gap 8*G + the sixteen AT_RANDOM bytes + the pad W.  The flag
     is split above the [vm_compute] and the statement stays parametric in [RZ]. *)
  Lemma gval_p0 : edenot E (e_str0 RZ) = Z_to_bv 64 (usp + 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * VZ E 11 + VZ E 4).
  Proof.
    destruct g_dparts as (_ & _ & _ & _ & _ & _ & L5 & _). destruct g_vals as (U1 & U2 & _ & U0).
    pose proof g_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (e_str0 RZ))) as x eqn:Ex.
    rz_split Ers; [ LINEQ (e_str0 1) L5 H0 | LINEQ (e_str0 0) L5 H0 ];
      rewrite <- Ex in H0; lia.
  Qed.
  Lemma gval_argc : edenot E (EVar 1) = Z_to_bv 64 argc.
  Proof. destruct g_vals as (U1 & _). apply word_of_u. exact U1. Qed.

  Definition DRV_REGVG : list (Z * Z) :=
    [(1, 0x134bcc); (2, usp - 48); (3, 0x10800); (4, 0x691d90); (8, usp + 8); (9, argc); (10, argc); (11, usp + 8);
     (12, usp + 16 + 8 * argc); (18, 0xaf0a4); (19, usp + 16 + 8 * argc); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].

  Lemma g_reg : forall r e, In (r, e) DRV_REGS -> getr R (Z_to_bv 5 r) = edenot E e.
  Proof. intros r e Hin. eapply ent_reg; sec. Qed.

  Theorem entg_regs : forall r v, In (r, v) DRV_REGVG -> getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Proof.
    intros r v Hin. unfold DRV_REGVG in Hin.
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 1 (ELit 0x134bcc)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk48|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 4 (ELit 0x691d90)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 12 e_envp) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 18 (ELit 0xaf0a4)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 19 e_envp) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 20 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 21 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 22 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 23 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 24 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 25 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 26 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 27 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin.
  Qed.

  Lemma g_stkword : forall off v, kfind_word (kn cs) e_sp0 off 8 = Some v ->
    rdn ASEGS0 MV (Z_to_bv 64 (usp + off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof. intros off v Hk. eapply ent_stkword; sec. Qed.

  (* STATEMENT CHANGED, old beside new: the address is still [usp + 8] and its value
     moves with [e_str0]:
       OLD  .. (usp + 8) = usp + 8*argc + 8*envc + 184
       NEW  .. (usp + 8) = usp + 8*argc + 8*envc + 472 + 32*RZ + 8*(VZ E 11) + VZ E 4 *)
  Theorem entg_stack_words :
    rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 argc))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8
       = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * VZ E 11 + VZ E 4))).
  Proof.
    destruct g_dparts as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & _).
    pose proof (g_stkword 0 _ K0) as H0. pose proof (g_stkword 8 _ K8) as H8.
    rewrite Z.add_0_r, gval_argc in H0. rewrite gval_p0 in H8. auto.
  Qed.

  (* [Pm9DrvEntryK]'s string-band lemmas at this launch.  None of them reads the
     argc = 2 premise of that file's Section, so they hold here unchanged. *)
  Lemma g_top : utop mod 4096 = 0 /\ utop <= 2 ^ 47.
  Proof. eapply ent_top; sec. Qed.
  Lemma g_bsb_lower : STRLO + Z.of_nat (total_arg_bytes_nat argv) + 9 <= utop.
  Proof. eapply ent_bsb_lower; sec. Qed.
  Lemma g_hbi_wg : VZ E 4 = Z.of_nat (block_pad_len rseq sp (ed_top rdraw) argv envp execfn)
                   /\ VZ E 11 = Z.of_nat (block_items argv envp mod 2).
  Proof. edestruct ent_hbi as (_ & _ & _ & _ & _ & _ & W & _ & _ & _ & _ & G); [sec .. | exact (conj W G)]. Qed.

  (* NEW, as Pm9DrvEntryK.ent_str0_off at any argc: the plan's [e_str0] value and CatExec's
     string offset are the same number ([cat_string_off = block_head_size + block_pad_len],
     [block_head_size = 8*(argc + envc + 3) + auxv_size + 8*G + 16]). *)
  Lemma entg_str0_off : Z.of_nat (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)
                        = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * VZ E 11 + VZ E 4.
  Proof.
    destruct g_hbi_wg as (W4 & G11). rewrite W4, G11.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA.
    (* one name per unfold: [block_head_size] only appears once [cat_string_off] has expanded *)
    unfold cat_string_off. unfold block_head_size. unfold block_items. cbv zeta. lia.
  Qed.

  Lemma g_ptr : forall k, (k < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn k) = STRLO + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof. intros k Hk. eapply ent_ptr; sec. Qed.

  (* NEW: argv[0]'s pointer is the word [entg_stack_words] reads at [usp + 8]. *)
  Lemma entg_p0_eq : cat_argv_ptr (ed_top rdraw) argv envp execfn 0
                     = Z_to_bv 64 (usp + 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * VZ E 11 + VZ E 4).
  Proof.
    pose proof g_bounds as GB. assert (Hk0 : (0 < length argv)%nat) by lia.
    apply bv_eq. rewrite (g_ptr 0 Hk0). change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat.
    pose proof g_bsb_lower as Hlow. destruct g_top as (_ & T2). pose proof g_rng as SR.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)) as Z1.
    pose proof entg_str0_off as OFF.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma g_band_defined : forall x : word, STRLO <= bv_unsigned x < utop -> FULL x <> None.
  Proof. intros x Hx. eapply ent_band_defined; sec. Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  forall x, usp + 8*argc + 8*envc + 184 <= x < usp + |build_stack_bytes ..| - 16 ->
              MV x = wrap_mem APH0 sp argv envp uid hw rdraw x
       NEW  forall x, STRLO <= x < utop -> MV x = wrap_mem INP mbase APH0 ENT sp rdraw x
     [Pm9DrvEntryK.ent_strblock] at any argc: the strings are at the top of the
     stack VMA at the revision, not above the auxv. *)
  Theorem entg_strblock : forall x : word,
    STRLO <= bv_unsigned x < utop ->
    MV x = wrap_mem INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw x.
  Proof. intros x Hx. eapply ent_strblock; sec. Qed.

  (* STATEMENT CHANGED, old beside new:
       OLD  rdn .. (cat_argv_ptr sp argv envp 0) .. /\
            bv_unsigned (cat_argv_ptr sp argv envp 0) = usp + 8*argc + 8*envc + 184
       NEW  the pointer is [cat_argv_ptr (ed_top rdraw) argv envp execfn 0] and its
            value is [STRLO].  The old proof unfolded [auxv_size]; nothing here does. *)
  Theorem entg_str0 :
    rdn ASEGS0 MV (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) (length (nth 0 argv []) + 1) = Some (nth 0 argv [] ++ [Z_to_bv 8 0])
    /\ bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) = STRLO.
  Proof.
    pose proof g_rng as SR. pose proof g_bounds as GB.
    assert (Hk0 : (0 < length argv)%nat) by lia.
    assert (Hk' : (0 < length (in_argv INP))%nat) by exact Hk0.
    pose proof (g_ptr 0 Hk0) as Hu. change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in Hu. rewrite Z.add_0_r in Hu.
    pose proof g_bsb_lower as Hlow. destruct g_top as (_ & T2).
    pose proof (total_arg_bytes_firstn_within argv 0 Hk0) as Hw. change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in Hw.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    split; [|exact Hu].
    transitivity (rdn ASEGS0 (stack_to_mem sp (entry_stack_image INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp rdraw))
                    (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) (length (nth 0 argv []) + 1)).
    - apply rdn_ext; [lia|]. intros x Hxr.
      rewrite entg_strblock by lia. apply wrap_above_sp. lia.
    - exact (read_argv_cstr_k Sv48 ASEGS0 INP mbase APH0 (Z_to_bv 64 (Z.of_N apc)) sp brk0 rdraw 0 Hlau Hk').
  Qed.

  (* STATEMENT CHANGED, old beside new -- the string slack, Main's ruling (a):
       OLD  bv_unsigned (cat_argv_ptr sp argv envp 0) + L0 + 1 + 16 <= 2^47
       NEW  bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) + L0 + 1 + 9 <= 2^47
     Sixteen past argv[0]'s NUL is FALSE at the revision when argc = 1, envp = []
     and the exec name is one byte: ten bytes then the end of the VMA (see
     [Pm9DrvEntryK.ent_str_hi]).  Eight is what the Diag chain reads. *)
  Theorem entg_str0_hi : bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) + L0 + 1 + 9 <= 2 ^ 47.
  Proof.
    pose proof g_bounds as GB. assert (Hk0 : (0 < length argv)%nat) by lia.
    rewrite (g_ptr 0 Hk0). pose proof g_bsb_lower as Hlow. destruct g_top as (_ & T2).
    pose proof (total_arg_bytes_firstn_within argv 0 Hk0) as Hw. lia.
  Qed.

  Hypothesis CHKS : stk_chk RZ cs = true.

  (* The page above sp: [Pm9DrvEntryK.ent_stack_defined_top] at this launch.  OLD:
     a private copy of the whole stack-wide argument ([entg_stack_defined]); that
     argument is argc-general and is kept in one file only. *)
  Corollary entg_stack_defined_top : forall top, top mod 4096 = 0 -> top <= usp + 4096 ->
    forall i, 0 <= i < top - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof. intros top Hm Hle i Hi. eapply ent_stack_defined_top; sec. Qed.

  (* STATEMENT CHANGED, old beside new -- the string slack, as [entg_str0_hi]:
       OLD  forall i, 0 <= i < L0 + 1 + 16 -> FULL (.. (cat_argv_ptr sp argv envp 0) + i) <> None
       NEW  forall i, 0 <= i < L0 + 1 + 8 -> FULL (.. (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) + i) <> None
     Every byte asked for is inside the string band, so the proof no longer goes
     through the stack-wide lemma. *)
  Theorem entg_str0_defined :
    forall i, 0 <= i < L0 + 1 + 8 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) + i)) <> None.
  Proof.
    intros i Hi. pose proof g_rng as SR. pose proof g_bounds as GB. assert (Hk0 : (0 < length argv)%nat) by lia.
    rewrite (g_ptr 0 Hk0). change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat.
    pose proof g_bsb_lower as Hlow. destruct g_top as (_ & T2).
    pose proof (total_arg_bytes_firstn_within argv 0 Hk0) as Hw. change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat in Hw.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp (ed_top rdraw) argv envp execfn)) as Z0.
    apply g_band_defined. rewrite u_small by lia. lia.
  Qed.

  Theorem entg_tid : tid_chk cs = true -> exists tid : word,
    1 <= bv_unsigned tid <= 4194303 /\ rdn ASEGS0 MV (Z_to_bv 64 0x691ce8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros CT. unfold tid_chk in CT.
    destruct (kfind_word (kn cs) (ELit 0) 0x691ce8 4) as [v|] eqn:K2; [|discriminate].
    exists (edenot E v).
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC CT) as RG. cbn [kentry_ok] in RG.
    split; [exact RG|].
    eapply ent_litcell; first [sec | lia].
  Qed.
End EntryG.
