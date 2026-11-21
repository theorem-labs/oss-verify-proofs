(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: Section GenericInit takes the entry address, the image facts, the mmap base and the launch's whole input (the seeded file system, the executable name and a free kernel build) with the valid_launch and entry_launch_ok_va premises, places the first string at cat_string_off for the run's rseq flag (str0_split), and states the XEnvScan, XPnScan and XLayout soundness lemmas at that flag over the new SINV0 and argH0; the launch's SIGPIPE disposition sgd is a Section variable, passed after kb. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.CatExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import CatSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require SymStepR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SymStepR.SeqExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.StoreOk.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require MemSplit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.MemSplit.AgentLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanAcct AsanAcctShape.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AsanCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  (* the seeded image [AsanInit.inp] takes (its [in_fs] is [fs_seed_tmp ifs tmp]) *)
  Variable ifs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.

  (* the input fields the start-up does not pin (AsanInit.inp) *)
  Variables nof sigm : word.
  Variable abt : bool.
  Variable urnd : InputStream.
  Variable tmp : Fs.Fs.
  Variable xfn : list byte.
  (* the kernel build, free in the five fields Run.valid_input leaves free and
     default_kernel's in the eight Run.recorded_kernel pins.  AsanInit declares it at
     AsanInit.v:134, between xfn (:128) and Hlaunch (:140), so every AsanInit export this
     Section applies takes it immediately after xfn.  It is NEVER instantiated here. *)
  Variable kb : KernelBuild.
  (* the launch's SIGPIPE disposition (in_sigpipe_default), which Run.valid_input leaves free *)
  Variable sgd : bool.
  Let INP := inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd.
  Let entryw := Z_to_bv 64 (Z.of_N apc).

  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch INP.             (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 ph apc sp rdraw brk0 mbase argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp xfn kb E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  #[local] Notation E0x := (E0 sp rdraw brk0 argv envp uid gid hw xfn kb).
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Lemma argH0_agree_nx : forall E E' (a : word), env_agree nx0 E E' -> argH0 sp rdraw argv envp xfn kb E a = argH0 sp rdraw argv envp xfn kb E' a.
  Proof. intros E E' a [Hag Hb]. apply (argH0_agree sp rdraw argv envp xfn kb). split; [|exact Hb]. intros n Hn. apply Hag. lia. Qed.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (* spelled kb_rseq kb, not kb_rseq (in_kernel INP). The two are convertible (INP's kernel field is
     recorded_kernel kb, which copies kb_rseq through), but AsanInit states its lemmas over kb_rseq kb and
     eapply does not reduce through the projection to unify in_kernel INP with kb, so every assert below uses
     the donor's spelling. *)
  Let rseq := kb_rseq kb.
  Let execfn := in_execfn INP.
  Let top := ed_top rdraw.
  (* [comment removed for export] *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.
  Lemma inp_argv' : in_argv INP = argv.   Proof. reflexivity. Qed.
  Lemma inp_envp' : in_envp INP = envp.   Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size rseq argv envp)
                                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  Proof. unfold STR0, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 (rseq_z (kb_rseq kb))) = STR0.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (U1 : uE E0x e_envp = usp + 8 * argc + 16)
      by (unfold usp, argc; eapply u_e_envp; eassumption).
    assert (U3 : uE E0x (e_str0 (rseq_z (kb_rseq kb)))
                 = usp + Z.of_nat (block_head_size rseq argv envp)
                   + Z.of_nat (block_pad_len rseq sp top argv envp execfn))
      by (unfold usp, rseq, execfn, top; eapply u_e_str0; eassumption).
    assert (U2 : uE E0x (EVar V_ENVC) = envc)
      by (unfold envc; eapply uE0_envc; eassumption).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0x n)
      by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E E0x e_envp eq_refl Hev7).
    (* e_str0 is parametric in rz, so this side condition is not a closed term while kb is a Section Variable:
       nb_lt NX0 (e_str0 (rseq_z (kb_rseq kb))) does not reduce to true. rz never enters as an EVar index, it
       only moves Z literals inside the expression, so the bound holds at both values of the flag; splitting
       on the bool first makes each branch a ground expr that computes (as AUXSZ_of is closed, by intros [|];
       vm_compute; reflexivity). The two neighbouring calls keep their eq_refl because e_envp and EVar V_ENVC
       carry no rz. *)
    rewrite (edenot_ev_agree NX0 E E0x (e_str0 (rseq_z (kb_rseq kb)))
               ltac:(destruct (kb_rseq kb); reflexivity) Hev7).
    split; [exact U1|]. split; [|rewrite U3; symmetry; exact str0_split].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E E0x (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0x n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE. rewrite (edenot_ev_agree NX0 E E0x e_sp0 eq_refl Hev7).
    unfold usp. eapply u_e_sp0; eassumption.
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. right.
    assert (HS0 : Z.of_nat (length (nth 0 argv [])) + 1
                  <= Z.of_nat (launch_string_bytes argv envp execfn))
      by (unfold execfn; eapply s0_in_strings; eassumption).
    assert (HT : usp + Z.of_nat (block_head_size rseq argv envp)
                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn)
                 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top)
      (* [comment removed for export] *)
      by (unfold usp, rseq, execfn, top; eapply AsanInit.str0_hi; eassumption).
    rewrite str0_split in Ha. unfold s0 in Ha.
    (* [comment removed for export] *)
    unfold rseq, execfn, top, usp in Ha, HT, HS0.
    (* fold the kernel field straight to [rseq]: kb_rseq (recorded_kernel kb) is only
       CONVERTIBLE to kb_rseq kb, and lia compares atoms syntactically *)
    change (kb_rseq (in_kernel INP)) with rseq in Ha, HT, HS0.
    change (in_execfn INP) with xfn in Ha, HT, HS0.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)


  Theorem init_x_sound_envscan :
    x_stmt segs A nx0 LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 XEnvScan.
  Proof.
    (* `rz` IS AN ARGUMENT OF x_stmt AND IS NOT AN ARGUMENT OF x_sound_envscan, and the
       difference is visible only in the two Sections' binder KINDS.  In AsanPlanSound.v's
       Section rz is a Variable, so the discharged x_stmt takes it in slot 5 — which is why
       the statement on the line above type-checks.  In AsanNodesStartX.v's Section NodesD
       it is a Let (`Let rz : Z := rseq_z rseq`, :118), and a Let is INLINED by discharge,
       never turned into an argument.  So x_sound_envscan's slots are
         SEGS A nx0 LIMIT SINV argH FS0 …
       and passing rz fifth put a Z where SINV belongs: "The term rseq_z (kb_rseq kb) has
       type Z while it is expected to have type env → (word → option byte) → Prop".
       Its conclusion carries rz already, inlined as rseq_z (kb_rseq (in_kernel inp)), which
       apply matches against this goal's rseq_z (kb_rseq kb) up to conversion, INP being a
       constructor application — the same convertibility :230 has to spell out for `change`,
       because change matches syntactically and apply does not.
       x_sound_layout at :263 needs no such edit: Section LayoutSound has no inp, so there
       rz really is a Variable (:424) and apply determines it from the goal. *)
    apply (x_sound_envscan segs A nx0 LIMIT SINV (argH0 sp rdraw argv envp xfn kb) FS0
              SEGS_wx SEGS_in_hull HULL_ok SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_sp0 | exact SINV0_envp | exact SINV0_str0 ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A nx0 LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 XPnScan.
  Proof.
    (* same Section NodesD, same Let-not-Variable rz; see :241. *)
    apply (x_sound_pnscan segs A nx0 LIMIT SINV (argH0 sp rdraw argv envp xfn kb) FS0
              SEGS_wx SEGS_in_hull HULL_ok
              (argH0_high apc sp rdraw argv envp Hsp Hva xfn kb) argH0_agree_nx
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph INP mbase entryw sp brk0 rdraw);
      solve [ assumption | exact sp_lo | exact sp_hi
            | exact SINV0_vals | exact SINV0_sp0 | exact SINV0_envp | exact SINV0_str0 ].
  Qed.
  Theorem init_x_sound_layout :
    x_stmt segs A nx0 LIMIT (rseq_z (kb_rseq kb)) SINV (argH0 sp rdraw argv envp xfn kb) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
