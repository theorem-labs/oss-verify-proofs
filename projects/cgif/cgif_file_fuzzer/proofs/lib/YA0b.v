(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the launch's group id; the launch's SIGPIPE disposition left free): changed uid, hw, SINV_SINV0, SINV_frame, SINV0_vals, SINV0_envp, SINV0_str0, init_x_sound_envscan and 2 more; added apc, groups, net, nofile, urnd, tmp, kb, execfn and 24 more; removed s0_fits. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK18 YK00 YK04 YK05.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA0c YA0e YA02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0b YK06.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA03 YA0a.
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
Variable apc : N.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable FS0 : Fs.Fs.
Variable uid gid : word.
Variable hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdef : bool.
Let INP := inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
Let entryw := Z_to_bv 64 (Z.of_N apc).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hapc : Z.of_N apc = a_entry A.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hzr : YK06.zero_random_draw (ed_random rdraw).
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Huid : valid_id uid.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
(* Mirrors YA02's premise split, and now mirrors its completion: the 13-field record pin
   [kb = default_kernel] went in the CONFIG_RSEQ port, and [Hypothesis Hrseq : kb_rseq kb = true],
   which that change kept here beside [valid_input], goes with this one.  [kb_rseq] is one of
   the five fields [Run.valid_input]'s conjunct 17 leaves FREE
   (75d69e00:theories/LinuxProcessSem/Run.v:4596), so no caller could discharge [Hrseq] and
   keeping it narrowed the published theorem to rseq-on kernels.  The YA02 section lemmas
   applied below no longer ask for it: their plan takes the flag as [YK09.rseq_z] writes it. *)
Hypothesis Hvi : valid_input INP.
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M ->
SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw argv envp kb execfn E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0G E E' -> SINV E M -> SINV E' M.
Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let s0 := nth 0 argv [].
Let TOP : Z := YA02.TOP sp.
Lemma TOP_ok' : top_ok TOP. Proof. exact (top_ok0 sp Hsp). Qed.
Lemma TOP_sp : TOP + 8388608 = bv_unsigned sp. Proof. unfold TOP, YA02.TOP. lia. Qed.
Let rseq := kb_rseq (in_kernel INP).
(* The flag as the PLAN spells it.  [YA02.E0] and [YA02.argH0] gained [kb] as a discharged
   section argument in the CONFIG_RSEQ port, when [Let rseq] stopped reading [default_kernel] and
   started reading the section's own [kb]; the applications below are corrected for that at
   the same time, since this file is the only one in proofs/ that was already on the start-up
   port's spelling of either name (control: the same grep finds 23 files still on the older
   [argH0 TPH sp rdraw argv envp uid hw] spelling). *)
Let RZ : Z := rseq_z rseq.
Let top := ed_top rdraw.
Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
Proof. destruct Hsp as (_ & H & _). exact H. Qed.
Lemma inp_argv' : in_argv INP = argv.   Proof. reflexivity. Qed.
Lemma inp_envp' : in_envp INP = envp.   Proof. reflexivity. Qed.
(* Was [rseq_default : rseq = kb_rseq default_kernel], which needed the record pin.  Over the
   section's own [kb] it is [reflexivity], and [kb_rseq] stays free. *)
Lemma rseq_kb : rseq = kb_rseq kb.
Proof. reflexivity. Qed.
Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
+ Z.of_nat (block_pad_len (kb_rseq kb) sp top argv envp execfn).
(* rz_range: STR0 unfolds through CHEAD, which carries 472 + 32*RZ since the
   parameterisation, so lia needs RZ bounded.  Monotone: an extra true hypothesis
   cannot break a lia that already closed. *)
Proof. unfold STR0, cat_string_off. rewrite rseq_kb. rewrite Nat2Z.inj_add. pose proof rz_range. lia. Qed.
(* [nb_lt NX0G (e_str0 r)] is NOT [eq_refl] at a symbolic [r]: [e_str0 r] threads
   [AUXSZ r] through [eaddz]/[mkAlu], whose [unlin] branches on [Z.eqb (fst x) 0]
   (YK0c.v:252-256), so the term is a stuck match until the flag is a literal -- the
   same obstruction YA02.v:106-110 records for [e_atrandom RZ].  [e_envp] at :141
   below carries no flag and keeps its [eq_refl].  The certificate is stated once per
   CLOSED flag value and joined under [forall b : bool]; the flag itself stays free.
   [RZ = rseq_z (kb_rseq (in_kernel INP))] then matches [b] by UNIFICATION, which is
   what [apply] can do and what no [exact eq_refl] can (11c-GAP-KIND: the projection
   [kb_rseq (in_kernel INP)] is not convertible to either literal). *)
Lemma nb_str0_flag : forall b : bool, nb_lt NX0G (e_str0 (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma nb_str0 : nb_lt NX0G (e_str0 RZ) = true.
Proof. unfold RZ, rseq. apply nb_str0_flag. Qed.
Lemma SINV0_vals : forall E M, SINV E M ->
uE E e_envp = usp + 8 * argc + 16
/\ ev E V_ENVC = Z_to_bv 64 envc
/\ uE E (e_str0 RZ) = STR0.
Proof.
intros E M HS. apply SINV_SINV0 in HS. destruct HS as (Hev & _ & _).
assert (U1 : uE (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) e_envp = usp + 8 * argc + 16).
{ unfold usp, argc. eapply u_e_envp; try eassumption. Unshelve. all: assumption. }
assert (U3 : uE (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) (e_str0 RZ)
= usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
+ Z.of_nat (block_pad_len (kb_rseq kb) sp top argv envp execfn)).
{ unfold usp, top. eapply u_e_str0; try eassumption. Unshelve. all: assumption. }
assert (U2 : uE (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) (EVar V_ENVC) = envc).
{ unfold envc. eapply uE0_envc; try eassumption. Unshelve. all: assumption. }
assert (Hev7 : forall n, (n < NX0G)%nat -> ev E n = ev (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) n)
by (intros n Hn; apply Hev; exact Hn).
unfold uE in *.
rewrite (edenot_ev_agree NX0G E (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) e_envp eq_refl Hev7).
rewrite (edenot_ev_agree NX0G E (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) (e_str0 RZ) nb_str0 Hev7).
split; [exact U1|]. split; [|rewrite U3; symmetry; exact str0_split].
change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
rewrite (edenot_ev_agree NX0G E (E0 sp rdraw brk0 argv envp uid gid hw kb execfn) (EVar V_ENVC) eq_refl Hev7).
apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
Qed.
Lemma SINV0_envp : forall E M (a : word), SINV E M ->
usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
M a = wrap_mem INP mbase ph entryw sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM. unfold argH0. apply orb_true_intro. left.
apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
M a = wrap_mem INP mbase ph entryw sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM. unfold argH0. apply orb_true_intro. right.
assert (HS0 : Z.of_nat (length (nth 0 argv [])) + 1
<= Z.of_nat (launch_string_bytes argv envp execfn)).
{ eapply s0_in_strings; try eassumption. Unshelve. all: assumption. }
assert (HT : usp + Z.of_nat (block_head_size (kb_rseq kb) argv envp)
+ Z.of_nat (block_pad_len (kb_rseq kb) sp top argv envp execfn)
+ Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top).
{ unfold usp, top. eapply YA02.str0_hi; try eassumption. Unshelve. all: assumption. }
rewrite str0_split in Ha. unfold s0 in Ha.
unfold top, usp in Ha, HT, HS0.
pose proof rz_range.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma argH0_high' : forall E (a : word), argH0 sp rdraw argv envp kb execfn E a = true -> TOP <= bv_unsigned a.
Proof. intros E a H. unfold TOP. eapply argH0_high; try eassumption. Unshelve. all: assumption. Qed.
Lemma argH0_agree' : forall E E' (a : word), env_agree NX0G E E' ->
argH0 sp rdraw argv envp kb execfn E a = argH0 sp rdraw argv envp kb execfn E' a.
Proof. reflexivity. Qed.
Theorem init_x_sound_envscan :
x_stmt segs A NX0G LIMIT TOP SINV (argH0 sp rdraw argv envp kb execfn) FS0 RZ XEnvScan.
Proof.
apply (x_sound_envscan segs A NX0G LIMIT TOP SINV (argH0 sp rdraw argv envp kb execfn) FS0
SEGS_wx SEGS_in_hull HULL_ok TOP_ok' SINV_frame
we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
ph INP mbase entryw sp brk0 rdraw);
solve [ assumption | exact sp_lo | exact sp_hi | exact TOP_sp
| exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 ].
Qed.
Theorem init_x_sound_pnscan :
x_stmt segs A NX0G LIMIT TOP SINV (argH0 sp rdraw argv envp kb execfn) FS0 RZ XPnScan.
Proof.
apply (x_sound_pnscan segs A NX0G LIMIT TOP SINV (argH0 sp rdraw argv envp kb execfn) FS0
SEGS_wx SEGS_in_hull HULL_ok
TOP_ok' argH0_high' argH0_agree'
SINV_frame SINV_agree
wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
ph INP mbase entryw sp brk0 rdraw);
solve [ assumption | exact sp_lo | exact sp_hi | exact TOP_sp
| exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 ].
Qed.
Theorem init_x_sound_layout :
x_stmt segs A NX0G LIMIT TOP SINV (argH0 sp rdraw argv envp kb execfn) FS0 RZ XLayout.
Proof. apply x_sound_layout. Qed.
End b.
