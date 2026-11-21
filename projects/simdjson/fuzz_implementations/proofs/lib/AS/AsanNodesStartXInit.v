(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the generic start-up scan section takes the run's whole launch input and every launch hypothesis AsanInit reads; argv[0] is found at the top of the start block (cat_string_off) instead of at a fixed offset after the auxv; the scan nodes take the run's CONFIG_RSEQ flag; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/AS/AsanNodesStartXInit.v, 91 lines within its lines 14-201. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.

  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (* LPS 727298f3: the run, as AS/AsanInit.v's Section Init names it.  [SINV0],
     [argH0] and [E0] read the run's whole launch input [inp], the mmap base
     (AT_SYSINFO_EHDR) and the image's entry (AT_ENTRY), so this Section
     carries every variable and hypothesis of AsanInit's Section Init that they
     read; [eassumption] discharges the ones each AsanInit lemma reads.  Same shape
     as 727298f3:theories/Common/AsanNodesStartXInit.v's Section GenericInit. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable FS0 : Fs.Fs.
  Variable inp : ProcInput.

  #[local] Notation INP := inp.
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation uid := (in_uid inp).
  Let entryw : word := Z_to_bv 64 (a_entry A).

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  #[local] Notation SINV0r := (SINV0 A ph sp rdraw brk0 mbase inp).
  #[local] Notation argH0r := (argH0 sp rdraw inp).
  #[local] Notation E0r := (E0 sp rdraw brk0 inp).

  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0r E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0r E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (* the run's CONFIG_RSEQ flag and exec name, spelled as AS/AsanInit.v spells them *)
  Let rseq := kb_rseq (in_kernel INP).
  Let RZ := rseq_z rseq.
  Let execfn := in_execfn INP.
  Let top := ed_top rdraw.
  (* argv[0]: the top of the AT_RANDOM bytes plus the [arch_align_stack] pad.
     It WAS [usp + 8*argc + 8*envc + 184]. *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  Lemma nb_lt_e_str0_b : forall b, nb_lt NX0 (e_str0 (rseq_z b)) = true.
  Proof. intros [|]; reflexivity. Qed.

  (* AsanInit's [STR0] ([usp + C + pad]) and AsanNodesStartX's ([usp + cat_string_off]) are the
     same number *)
  Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size rseq argv envp)
                                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Proof. unfold STR0, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 RZ) = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (U1 : uE E0r e_envp = usp + 8 * argc + 16) by (eapply u_e_envp; eassumption).
    assert (U3 : uE E0r (e_str0 RZ)
                 = usp + Z.of_nat (block_head_size rseq argv envp)
                   + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
      by (eapply u_e_str0; eassumption).
    assert (U2 : uE E0r (EVar V_ENVC) = envc)
      by (edestruct uE0 as (_ & _ & _ & U & _); first [exact U | eassumption]).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0r n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E E0r e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E E0r (e_str0 RZ) (nb_lt_e_str0_b rseq) Hev7).
    split; [exact U1|]. split; [|rewrite U3; symmetry; exact str0_split].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E E0r (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. apply argH0_of_old. unfold argH0_old. cbv zeta.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* the string area runs from argv[0] to the stack VMA's end, and argv[0]
     with its NUL is inside it ([AsanNodesStartX.s0_le_strings_gen]), so the bytes the
     progname scan reads are hidden by [argH0] *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    unfold argH0. cbv zeta. apply orb_true_intro. right.
    pose proof (s0_le_strings_gen argv envp execfn Hva) as HS0.
    pose proof (length_entry_stack_image_launch Sv48 INP mbase ph entryw sp brk0 rdraw Hlau) as HL.
    assert (HT : Z.of_nat (length (entry_stack_image INP mbase ph entryw sp rdraw))
                 = Z.of_nat (block_head_size rseq argv envp)
                   + Z.of_nat (block_pad_len rseq sp top argv envp execfn)
                   + Z.of_nat (launch_string_bytes argv envp execfn) + 8).
    { rewrite entry_stack_image_block, length_build_stack_bytes.
      change (la_rseq (launch_auxv INP sp mbase)) with rseq.
      change (in_argv INP) with argv. change (in_envp INP) with envp.
      change (in_execfn INP) with execfn. change (ed_top rdraw) with top. lia. }
    rewrite str0_split in Ha. unfold s0 in Ha.
    unfold rseq, execfn, top, usp in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma argH0_high_r : forall E (a : word), argH0r E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.

  Lemma argH0_agree_r : forall E E' (a : word), env_agree NX0 E E' -> argH0r E a = argH0r E' a.
  Proof. reflexivity. Qed.

  Lemma SINV0_sp' : forall E M, SINV E M -> uE E e_sp0 = bv_unsigned sp.
  Proof. intros E M HS. apply SINV_SINV0 in HS. eapply SINV0_sp; eassumption. Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs A NX0 LIMIT RZ SINV argH0r FS0 XEnvScan.
  Proof.
    eapply x_sound_envscan;
      solve [ eassumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact SINV0_sp'
            | exact argH0_high_r | exact argH0_agree_r ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A NX0 LIMIT RZ SINV argH0r FS0 XPnScan.
  Proof.
    eapply x_sound_pnscan;
      solve [ eassumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact SINV0_sp'
            | exact argH0_high_r | exact argH0_agree_r ].
  Qed.
  Theorem init_x_sound_layout :
    x_stmt segs A NX0 LIMIT RZ SINV argH0r FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
