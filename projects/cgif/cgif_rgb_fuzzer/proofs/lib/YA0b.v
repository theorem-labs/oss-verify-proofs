(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the section is over the run's ProcInput with valid_launch, entry_launch_ok_va and the recorded-kernel conjunct in place of argv, envp, uid, hwcap and entry_stack_fits; SINV0, argH0 and wrap_mem take the run; argv[0]'s string sits at the new layout's offset, which depends on the run's CONFIG_RSEQ flag, proved by a case on that flag; the scan statements take the flag). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK15 YK18 YK00 YK05 YK06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0d YK0f YK0g YK0a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA0c YA0e YA02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA03 YA0a.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b.
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
(* 08b1429 (recipes/procinput-fields.md step 3): over the run's input [inp], as YA02. *)
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable inp : ProcInput.
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
(* #38 (rules 12f, 12r): the kernel pin is replaced by [valid_input]'s own
   recorded-kernel conjunct, as in YA02 - it leaves [kb_rseq] free. *)
Hypothesis Hrec : in_kernel inp = recorded_kernel (in_kernel inp).
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 A ph sp rdraw brk0 mbase inp E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0G E E' -> SINV E M -> SINV E' M.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let execfn := in_execfn inp.
Let rseq := kb_rseq (in_kernel inp).
(* #38: the plan's CONFIG_RSEQ flag as 0 or 1, off this section's own run. *)
Let RZ : Z := rseq_z rseq.
Let top := ed_top rdraw.
Let entryw : word := Z_to_bv 64 (a_entry A).
Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let s0 := nth 0 argv [].
Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
Let TOP : Z := YA02.TOP sp.
Lemma TOP_ok' : top_ok TOP. Proof. exact (top_ok0 sp Hsp). Qed.
Lemma TOP_sp : TOP + 8388608 = bv_unsigned sp. Proof. unfold TOP, YA02.TOP. lia. Qed.
Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
Proof. destruct Hsp as (_ & H & _). exact H. Qed.
Lemma SINV0_vals : forall E M, SINV E M ->
uE E e_envp = usp + 8 * argc + 16
/\ ev E V_ENVC = Z_to_bv 64 envc
/\ uE E (e_str0 RZ) = STR0.
Proof.
intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
assert (U1 : uE (E0 sp rdraw brk0 inp) e_envp = usp + 8 * argc + 16)
by (unfold usp, argc, argv; eapply u_e_envp; eassumption).
assert (U3 : uE (E0 sp rdraw brk0 inp) (e_str0 RZ) = STR0).
{ unfold STR0, cat_string_off, rseq, argv, envp, execfn, top, usp. rewrite Nat2Z.inj_add, Z.add_assoc.
eapply u_e_str0; eassumption. }
assert (U2 : uE (E0 sp rdraw brk0 inp) (EVar V_ENVC) = envc)
by (unfold envc, envp; eapply uE0_envc; eassumption).
assert (Hev7 : forall n, (n < NX0G)%nat -> ev E n = ev (E0 sp rdraw brk0 inp) n) by (intros n Hn; apply Hev; exact Hn).
unfold uE in *.
rewrite (edenot_ev_agree NX0G E (E0 sp rdraw brk0 inp) e_envp eq_refl Hev7).
rewrite (edenot_ev_agree NX0G E (E0 sp rdraw brk0 inp) (e_str0 RZ)
ltac:(unfold RZ, rseq; destruct (kb_rseq (in_kernel inp)); vm_compute; reflexivity) Hev7).
split; [exact U1|]. split; [|exact U3].
change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
rewrite (edenot_ev_agree NX0G E (E0 sp rdraw brk0 inp) (EVar V_ENVC) eq_refl Hev7).
apply bv_eq. rewrite U2. unfold envc, envp. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
Qed.
Lemma SINV0_envp : forall E M (a : word), SINV E M ->
usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 -> M a = wrap_mem inp mbase ph entryw sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM. unfold argH0. apply orb_true_intro. left.
apply andb_true_intro. unfold usp, argc, envc, argv, envp in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
M a = wrap_mem inp mbase ph entryw sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM. unfold argH0. apply orb_true_intro. right.
assert (HS0 : Z.of_nat (length (nth 0 (in_argv inp) [])) + 1
<= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))
by (eapply s0_in_strings; eassumption).
assert (HT : bv_unsigned sp + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
+ Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))
+ Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)) + 8 = bv_unsigned (ed_top rdraw))
by (eapply YA02.str0_hi; eassumption).
unfold STR0, s0, cat_string_off, rseq, argv, envp, execfn, top, usp in Ha. rewrite Nat2Z.inj_add in Ha.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Theorem init_x_sound_envscan :
x_stmt segs A NX0G LIMIT TOP RZ SINV (argH0 sp rdraw inp) FS0 XEnvScan.
Proof.
apply (x_sound_envscan segs A NX0G LIMIT TOP SINV (argH0 sp rdraw inp) FS0
SEGS_wx SEGS_in_hull HULL_ok TOP_ok' SINV_frame
we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
ph inp mbase entryw sp brk0 rdraw);
solve [ assumption | exact sp_lo | exact sp_hi | exact TOP_sp
| exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 ].
Qed.
Theorem init_x_sound_pnscan :
x_stmt segs A NX0G LIMIT TOP RZ SINV (argH0 sp rdraw inp) FS0 XPnScan.
Proof.
apply (x_sound_pnscan segs A NX0G LIMIT TOP SINV (argH0 sp rdraw inp) FS0
SEGS_wx SEGS_in_hull HULL_ok
TOP_ok' (argH0_high sp rdraw inp Hsp Hva) (argH0_agree sp rdraw inp)
SINV_frame SINV_agree
wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
ph inp mbase entryw sp brk0 rdraw);
solve [ assumption | exact sp_lo | exact sp_hi | exact TOP_sp
| exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 ].
Qed.
Theorem init_x_sound_layout :
x_stmt segs A NX0G LIMIT TOP RZ SINV (argH0 sp rdraw inp) FS0 XLayout.
Proof. apply (x_sound_layout segs A NX0G LIMIT TOP SINV (argH0 sp rdraw inp) FS0 RZ). Qed.
End b.
