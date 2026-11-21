(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: the start-up section takes the launch's input, entry address apc, image facts and the launch premises valid_launch and entry_launch_ok_va; the CONFIG_RSEQ flag of the start-up layer: e_str0 at rseq_z; the entry stack layout: the first string at cat_string_off, past the block head and pad, in place of the fixed 184-byte offset; the start-up scan nodes init_x_sound_envscan, init_x_sound_pnscan and init_x_sound_layout at the launch's stack image). *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYLF.Mq1.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma nb_lt_e_str0 : forall b, nb_lt NX0 (e_str0 (rseq_z b)) = true.
Proof. intros [|]; reflexivity. Qed.

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
Variable nofile sigmask : word.
Variable abort_terminal : bool.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable rdr sgd sgt : bool.

Let INP := inp argv envp fs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt.
Let entryw := Z_to_bv 64 (Z.of_N apc).

Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hapc : Z.of_N apc = a_entry A.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Huid : valid_id uid.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hkernel : in_kernel INP = recorded_kernel (in_kernel INP).
Hypothesis Hlaunch : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

Let argHx := argH0 sp rdraw argv envp kb execfn.
Let SINV0x := SINV0 ph apc sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt.

Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0x E M.
Hypothesis SINV_frame : forall E M M', (forall a, argHx E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Variable nx0 : nat.
Hypothesis NX0_le : (NX0 <= nx0)%nat.
Lemma nx0_S : APS.nx0_ge nx0.
Proof. unfold APS.nx0_ge. pose proof NX0_le as H. unfold NX0 in H. lia. Qed.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let s0 := nth 0 argv [].
Let rseq := kb_rseq kb.
Let RZ := rseq_z rseq.
Let top := ed_top rdraw.

Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

Lemma str0_split : STR0 = usp + Z.of_nat (block_head_size rseq argv envp)
+ Z.of_nat (block_pad_len rseq sp top argv envp execfn).
Proof. unfold STR0, cat_string_off. rewrite Nat2Z.inj_add. lia. Qed.

Lemma SINV0_vals : forall E M, SINV E M ->
uE E e_envp = usp + 8 * argc + 16
/\ ev E V_ENVC = Z_to_bv 64 envc
/\ uE E (e_str0 RZ) = STR0.
Proof.
intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
match type of Hev with forall n, _ -> _ = ev ?e0 n => set (E0x := e0) in Hev end.
assert (U1 : uE E0x e_envp = usp + 8 * argc + 16) by (subst E0x; eapply u_e_envp; eassumption).
assert (U3 : uE E0x (e_str0 RZ) = usp + Z.of_nat (block_head_size rseq argv envp)
+ Z.of_nat (block_pad_len rseq sp top argv envp execfn))
by (subst E0x; eapply u_e_str0; eassumption).
assert (U2 : uE E0x (EVar V_ENVC) = envc) by (subst E0x; eapply uE0_envc; eassumption).
unfold uE in *.
rewrite (edenot_ev_agree NX0 E E0x e_envp eq_refl Hev).
rewrite (edenot_ev_agree NX0 E E0x (e_str0 RZ) (nb_lt_e_str0 rseq) Hev).
split; [exact U1|]. split; [|rewrite U3, str0_split; reflexivity].
change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
rewrite (edenot_ev_agree NX0 E E0x (EVar V_ENVC) eq_refl Hev).
apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
Qed.

Lemma SINV0_envp : forall E M (a : word), SINV E M ->
usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 -> M a = wrap_mem INP mbase ph entryw sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. cbv zeta.
apply orb_true_intro. left. apply orb_true_intro. left. apply orb_true_intro. left.
pose proof Hva as [LAV _].
apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
M a = wrap_mem INP mbase ph entryw sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0. cbv zeta.
apply orb_true_intro. right.
assert (HS0 : Z.of_nat (length (nth 0 argv [])) + 1
<= Z.of_nat (launch_string_bytes argv envp execfn))
by (eapply s0_in_strings; eassumption).
assert (HT : usp + Z.of_nat (block_head_size rseq argv envp)
+ Z.of_nat (block_pad_len rseq sp top argv envp execfn)
+ Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned top)
by (eapply QpvH.str0_hi; eassumption).
rewrite str0_split in Ha. unfold s0 in Ha. unfold top, usp, rseq in Ha, HT.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
Proof. destruct Hsp as (_ & H & _). exact H. Qed.

Lemma argH0_agree_nx0 : forall E E' (a : word), env_agree nx0 E E' -> argHx E a = argHx E' a.
Proof. intros E E' a _. reflexivity. Qed.

Lemma argH0_high_x : forall E a, argHx E a = true -> CEIL <= bv_unsigned a.
Proof. intros E a H. eapply argH0_high; eassumption. Qed.

(* The start-up scan nodes at the launch's stack image, the form of the source unit's
init_x_sound_* (QYLF's x_sound_* take the launch's ProcInput, mmap base, entry address and
draw; SINV0_vals / SINV0_envp / SINV0_str0 discharge their stack premises). *)
Theorem init_x_sound_envscan :
x_stmt segs A nx0 LIMIT RZ (bv_unsigned sp) SINV argHx FS0 XEnvScan.
Proof.
eapply (x_sound_envscan segs A nx0 LIMIT RZ sp SINV argHx FS0)
with (we1 := we1) (we2 := we2) (we3 := we3)
(ph := ph) (inp := INP) (mbase := mbase) (entry := entryw) (brk := brk0) (rdraw := rdraw);
solve [ assumption | exact sp_lo | exact sp_hi
| exact SINV0_vals | exact SINV0_envp | exact SINV0_str0
| exact argH0_agree_nx0 | exact argH0_high_x | exact nx0_S ].
Qed.

Theorem init_x_sound_pnscan :
x_stmt segs A nx0 LIMIT RZ (bv_unsigned sp) SINV argHx FS0 XPnScan.
Proof.
eapply (x_sound_pnscan segs A nx0 LIMIT RZ sp SINV argHx FS0)
with (wp0 := wp0) (wp1 := wp1) (wp2 := wp2) (wp3 := wp3) (wp4 := wp4)
(ph := ph) (inp := INP) (mbase := mbase) (entry := entryw) (brk := brk0) (rdraw := rdraw);
solve [ assumption | exact sp_lo | exact sp_hi
| exact SINV0_vals | exact SINV0_envp | exact SINV0_str0
| exact argH0_agree_nx0 | exact argH0_high_x | exact nx0_S ].
Qed.

Theorem init_x_sound_layout :
x_stmt segs A nx0 LIMIT RZ (bv_unsigned sp) SINV argHx FS0 XLayout.
Proof. apply x_sound_layout. Qed.
End GenericInit.
