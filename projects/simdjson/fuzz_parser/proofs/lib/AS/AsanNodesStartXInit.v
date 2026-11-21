(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the generic start-up scan section takes the run's whole launch input, its entry pc and the launch hypotheses AsanInit reads in place of argv, envp, uid and hw; argv[0] is found at the top of the start block (cat_string_off) instead of at a fixed offset after the auxv; the scan nodes take the run's CONFIG_RSEQ flag and a CEIL bound below the stack; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/AS/AsanNodesStartXInit.v, 41 lines within its lines 60-195. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX.
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

  (* LPS 727298f3: the launch is the run's whole input [inp] (AS/AsanInit.v's Section Init takes
     it so); this Section carries every variable and hypothesis of that Section that the AsanInit
     lemmas below read, and [eassumption] discharges them. *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation SINV0r := (SINV0 ph apc sp rdraw brk0 mbase inp).
  #[local] Notation argH0r := (argH0 sp rdraw inp).
  #[local] Notation E0r := (E0 sp rdraw brk0 inp).
  Let entryw : word := Z_to_bv 64 (Z.of_N apc).

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0r E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0r E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  Lemma argH0_agree_nx : forall E E' (a : word), env_agree nx0 E E' -> argH0r E a = argH0r E' a.
  Proof. reflexivity. Qed.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (* the run's CONFIG_RSEQ flag and exec name, as AS/AsanInit.v reads them *)
  Let rseq := kb_rseq (in_kernel inp).
  Let RZ := rseq_z rseq.
  Let execfn := in_execfn inp.
  Let top := ed_top rdraw.
  (* argv[0]'s first byte: above the auxv, AT_RANDOM and the [arch_align_stack] pad *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.
  (* CEIL is [sp_window_lo] less the 8 MiB stack limit *)
  Lemma ceil_sp : CEIL <= bv_unsigned sp - stack_max_size.
  Proof. pose proof sp_lo. unfold CEIL, sp_window_lo, stack_max_size in *. lia. Qed.

  Lemma nb_lt_e_str0_b : forall b, nb_lt NX0 (e_str0 (rseq_z b)) = true.
  Proof. intros [|]; reflexivity. Qed.

  (* AsanInit's argv[0] ([usp + head + pad]) and AsanNodesStartX's ([usp + cat_string_off]) are
     the same number *)
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
    assert (U2 : uE E0r (EVar V_ENVC) = envc) by (eapply uE0_envc; eassumption).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E0r n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *.
    rewrite (edenot_ev_agree NX0 E E0r e_envp eq_refl Hev7).
    rewrite (edenot_ev_agree NX0 E E0r (e_str0 RZ) (nb_lt_e_str0_b rseq) Hev7).
    split; [exact U1|]. split; [|rewrite U3; symmetry; exact str0_split].
    change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
    rewrite (edenot_ev_agree NX0 E E0r (EVar V_ENVC) eq_refl Hev7).
    apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof. intros E M HS. apply SINV_SINV0 in HS. eapply SINV0_sp; eassumption. Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. apply orb_true_intro. left.
    assert (LAV : 1 <= Z.of_nat (length argv) <= 1024) by (destruct Hva as [H _]; lia).
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma s0_le_strings_gen : forall (av ev : list (list byte)) (xf : list byte), valid_argv av ->
    Z.of_nat (length (nth 0 av [])) + 1 <= Z.of_nat (launch_string_bytes av ev xf).
  Proof.
    intros av ev xf Hav. unfold launch_string_bytes.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings ev))).
    pose proof (Nat2Z.is_nonneg (length xf)).
    destruct av as [|a t].
    - destruct Hav as [[Hc _] _]. cbn in Hc. lia.
    - cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* the string area runs from argv[0] to the stack VMA's end, so the bytes the progname scan
     reads are hidden by [argH0] *)
  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
    M a = wrap_mem inp mbase ph entryw sp rdraw a.
  Proof.
    intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM.
    unfold argH0. apply orb_true_intro. right.
    pose proof (s0_le_strings_gen argv envp execfn Hva) as HS0.
    (* the block runs from sp to the stack VMA's end: AsanInit's [str0_hi] (qualified: AsanNodesStartX
       exports a lemma of the same name) *)
    assert (HT : usp + Z.of_nat (block_head_size rseq argv envp)
                 + Z.of_nat (block_pad_len rseq sp top argv envp execfn)
                 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top).
    { unfold usp, rseq, top. eapply AsanInit.str0_hi; eassumption. }
    rewrite str0_split in Ha. unfold s0 in Ha.
    unfold rseq, execfn, top, usp in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    (* a variable the lemma's proof read but its statement does not fix *)
    Unshelve. all: first [exact ph | exact apc | exact mbase | exact brk0].
  Qed.

  Lemma argH0_high_r : forall E (a : word), argH0r E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. eapply argH0_high; eassumption. Qed.

  Theorem init_x_sound_envscan :
    x_stmt segs A nx0 LIMIT RZ SINV argH0r FS0 XEnvScan.
  Proof.
    eapply x_sound_envscan;
      solve [ eassumption | exact sp_lo | exact sp_hi | exact ceil_sp
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact SINV0_sp0
            | exact argH0_high_r | exact argH0_agree_nx ].
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs A nx0 LIMIT RZ SINV argH0r FS0 XPnScan.
  Proof.
    eapply x_sound_pnscan;
      solve [ eassumption | exact sp_lo | exact sp_hi | exact ceil_sp
            | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact SINV0_sp0
            | exact argH0_high_r | exact argH0_agree_nx ].
  Qed.
  Theorem init_x_sound_layout :
    x_stmt segs A nx0 LIMIT RZ SINV argH0r FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
