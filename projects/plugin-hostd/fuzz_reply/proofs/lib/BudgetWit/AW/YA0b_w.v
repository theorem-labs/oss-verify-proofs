(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0b.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA0b.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK00 YK04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YA0e_w YA02_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.BudgetWit.AW Require Import YA03_w YA0a_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [e_str0]'s variables are below NX0G at either CONFIG_RSEQ flag; the flag is free, so
   the check is closed per flag. *)
Lemma nb_e_str0 : forall b, nb_lt NX0G (e_str0 (rseq_z b)) = true.
Proof. intros [|]; reflexivity. Qed.
Section b.
Variable segs : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Hypothesis SEGS_wx : wx_segs_nowrap segs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis RES_cover : res_cover_ok segs A.
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
(* 727298f3 (75d69e00 launch): [YA02]'s Section takes the whole packed input, the mmap base,
   the kernel build and the entry pc, and its stack strings sit at the TOP of the stack VMA.
   This Section declares the same variables and hypotheses, in [YA02]'s order, so that each
   [YA02] lemma below is applied by unification ([eapply] then [eassumption]) rather than by
   a positional list. *)
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
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
Variable sdef : bool.
Variable apc : N.
Variable FS0 : Fs.Fs.
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Let INP := YA02_w.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef.
Hypothesis Hnof : valid_nofile nofile.
Hypothesis Hsig : valid_sigmask INP.
Hypothesis Hapc : Z.of_N apc = a_entry A.
Hypothesis Hvl : valid_launch INP.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
Let ENTRY : word := Z_to_bv 64 (Z.of_N apc).
Let RSEQ := kb_rseq (in_kernel INP).
Let RZ := rseq_z RSEQ.
#[local] Notation ARGH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
#[local] Notation E00 := (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M ->
SINV0 segs ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef apc E M.
Hypothesis SINV_frame : forall E M M', (forall a, ARGH E a = true -> M' a = M a) ->
(YAkMemnorm.memnorm segs M -> YAkMemnorm.memnorm segs M') -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0G E E' -> SINV E M -> SINV E' M.
Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let s0 := nth 0 argv [].
Let STR0 := usp + Z.of_nat (cat_string_off RSEQ sp (ed_top rdraw) argv envp execfn).
Let TOP : Z := YA02_w.TOP sp.
Lemma TOP_ok' : top_ok TOP. Proof. exact (top_ok0 sp Hsp). Qed.
Lemma TOP_sp : TOP + 8388608 = bv_unsigned sp. Proof. unfold TOP, YA02_w.TOP. lia. Qed.
Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
Proof. destruct Hsp as (_ & H & _). exact H. Qed.
Lemma ARGH_high : forall E (a : word), ARGH E a = true -> TOP <= bv_unsigned a.
Proof. intros E a H. eapply argH0_high; try eassumption. Unshelve. all: assumption. Qed.
Lemma ARGH_agree : forall E E' (a : word), env_agree NX0G E E' -> ARGH E a = ARGH E' a.
Proof. intros E E' a H. eapply argH0_agree; try eassumption. Unshelve. all: assumption. Qed.
Lemma SINV0_vals : forall E M, SINV E M ->
uE E e_envp = usp + 8 * argc + 16
/\ ev E V_ENVC = Z_to_bv 64 envc
/\ uE E (e_str0 RZ) = STR0.
Proof.
intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
assert (U1 : uE E00 e_envp = usp + 8 * argc + 16).
{ eapply u_e_envp; try eassumption. Unshelve. all: assumption. }
assert (U3 : uE E00 (e_str0 RZ) = STR0).
{ eapply u_e_str0; try eassumption. Unshelve. all: assumption. }
assert (Hev7 : forall n, (n < NX0G)%nat -> ev E n = ev E00 n) by (intros n Hn; apply Hev; exact Hn).
unfold uE in *.
rewrite (edenot_ev_agree NX0G E E00 e_envp eq_refl Hev7).
rewrite (edenot_ev_agree NX0G E E00 (e_str0 RZ) (nb_e_str0 RSEQ) Hev7).
split; [exact U1|]. split; [|exact U3].
(* [E0]'s fourth value word is the envp count itself *)
rewrite (Hev7 V_ENVC ltac:(apply Nat.ltb_lt; reflexivity)). reflexivity.
Qed.
Lemma SINV0_envp : forall E M (a : word), SINV E M ->
usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
M a = wrap_mem INP mbase ph ENTRY sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM. apply argH0_of_core. unfold argH0_core. apply orb_true_intro. left.
apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) ->
M a = wrap_mem INP mbase ph ENTRY sp rdraw a.
Proof.
intros E M a HS Ha. apply SINV_SINV0 in HS. destruct HS as (_ & HM & _). apply HM. apply argH0_of_core. unfold argH0_core. apply orb_true_intro. right.
(* the strings run from [STR0] to the stack VMA's end, argv[0] and its NUL first *)
assert (S1 : STR0 + Z.of_nat (launch_string_bytes argv envp execfn) + 8 = bv_unsigned (ed_top rdraw)).
{ eapply YA02_w.str0_hi; try eassumption. Unshelve. all: assumption. }
assert (S2 : Z.of_nat (length (nth 0 argv [])) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn)).
{ eapply YA02_w.s0_in_strings; try eassumption. Unshelve. all: assumption. }
apply andb_true_intro. unfold s0 in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold STR0, RSEQ, INP, usp in *; lia.
Qed.
Theorem init_x_sound_envscan : x_stmt segs A NX0G LIMIT RZ TOP SINV ARGH FS0 XEnvScan.
Proof.
eapply (x_sound_envscan segs A NX0G LIMIT TOP SINV ARGH FS0);
first [ eassumption | exact TOP_ok' | exact sp_lo | exact sp_hi | exact TOP_sp
      | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact ARGH_high | exact ARGH_agree ].
Unshelve. all: assumption.
Qed.
Theorem init_x_sound_pnscan : x_stmt segs A NX0G LIMIT RZ TOP SINV ARGH FS0 XPnScan.
Proof.
eapply (x_sound_pnscan segs A NX0G LIMIT TOP SINV ARGH FS0);
first [ eassumption | exact TOP_ok' | exact sp_lo | exact sp_hi | exact TOP_sp
      | exact SINV0_vals | exact SINV0_envp | exact SINV0_str0 | exact ARGH_high | exact ARGH_agree ].
Unshelve. all: assumption.
Qed.
Theorem init_x_sound_layout : x_stmt segs A NX0G LIMIT RZ TOP SINV ARGH FS0 XLayout.
Proof. apply x_sound_layout. Qed.
End b.
