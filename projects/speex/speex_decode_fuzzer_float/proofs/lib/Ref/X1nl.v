(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up to main from the launch's own initial state over the process input and the mmap base: entry_stack_image as the entry block, the launch's auxv words, and the 6144512-byte stack window below sp; the state at main records the launch's head-size and stack-top bounds; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl X1ri.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0pw X0qx X0qy X0qw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1ff X1fd X1nm X1nn X1ea.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Notation rsegs := X1ff.rsegs.

Section AtMain.
(* LPS 727298f3: the state at main over the launch's own input and mmap base ([init_ms]): the
   entry block is [entry_stack_image]; the zero window below sp is at least 6144512 bytes
   ([X0pw.launch_window_lo]). *)
Variables (sp0 mbase : word) (rnd : EntryDraw) (inp : ProcInput).

Variable (F : bvmap 5 word).
Notation usp0 := (bv_unsigned sp0).

Definition rcrt_written : list (Z * Z) :=
[(0x35df0, 0x35df1); (0x45e70, 0x45e78); (0x45e78, 0x45fc8); (0x65f50, 0x65f80); (0x661a8, 0x661b0); (0x661b8, 0x66238)]%Z.

Definition rat_main : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(t P0 : Z) (pg : word) (m' : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 0x29d04) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x45f40)
t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc inp))
(Z_to_bv 64 (argc inp)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 inp)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x1ba70) (Z_to_bv 64 (envp_addr sp0 inp)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1ba70) (Z_to_bv 32 0) None m' (seg_rom rsegs)
/\ mem_inv rsegs m'
/\ stk rsegs m' (usp0 - 6144512) (usp0 + -48)

/\ rw_cells rsegs m' 0x45e78 [C8 (Z_to_bv 64 0x45e78); C8 (Z_to_bv 64 0x45e78); C8 (Z_to_bv 64 0x45e78); C8 z64; C4 (Z_to_bv 64 t)]

/\ rw_cells rsegs m' 0x45e9c [C4 z64]

/\ rw_cells rsegs m' 0x45ea0 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x45ef0);
CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x66200); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (canary_of (rnd_w0 rnd));
C8 (Z_to_bv 64 0x45f50); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]

/\ rw_cells rsegs m' 0x661c8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]

/\ rw_cells rsegs m' 0x661d0 [C8 (Z_to_bv 64 (auxv_addr sp0 inp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]

/\ rw_cells rsegs m' 0x65f48 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]

/\ rw_cells rsegs m' 0x661b0 [C8 z64]
/\ rw_cells rsegs m' 0x661b8 [C8 pg; C8 (Z_to_bv 64 P0)]
/\ rw_cells rsegs m' 0x66230 [C8 (in_hwcap inp)]
/\ rw_cells rsegs m' 0x45e70 [C8 (Z_to_bv 64 (envp_addr sp0 inp))]
/\ rw_cells rsegs m' 0x35de0 [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' 0x661a8 [C8 (canary_of (rnd_w0 rnd))]

/\ rw_cells rsegs m' 0x34ad8 [C8 z64]
/\ rw_cells rsegs m' 0x34ae0 [C8 (Z_to_bv 64 0x1ba70); C8 (Z_to_bv 64 0x299e4); C8 (Z_to_bv 64 0x2a14c); C8 z64]
/\ rw_cells rsegs m' 0x34b00 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64]
/\ rw_cells rsegs m' 0x34b10 [C8 (Z_to_bv 64 0x34ac0)]
/\ rw_cells rsegs m' 0x34b98 [C8 (Z_to_bv 64 0x45e70); C8 (Z_to_bv 64 0x661c0); C8 (Z_to_bv 64 0x661b8)]
/\ rw_cells rsegs m' 0x34bb0 [C8 (Z_to_bv 64 0x341e0); C8 (Z_to_bv 64 0x341d8)]
/\ rw_cells rsegs m' 0x34bc0 [C8 (Z_to_bv 64 0x661a8)]
/\ rw_cells rsegs m' 0x34bc8 [C8 (Z_to_bv 64 0x341e8); C8 (Z_to_bv 64 0x341e0)]

/\ rw_cells rsegs m' 0x341d8 [C8 (Z_to_bv 64 0x1b96c)]
/\ rw_cells rsegs m' 0x341e0 [C8 (Z_to_bv 64 0x1b9e0)]
/\ rw_cells rsegs m' 0x34ac0 [C8 (Z_to_bv 64 0x35c00)]

/\ rw_cells rsegs m' 0x35df0 [C1 (Z_to_bv 8 1)]
/\ rw_cells rsegs m' 0x35e38 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m' 0x661a0 [C4 z64]

/\ rw_cells rsegs m' 0x35dd8 [C8 (Z_to_bv 64 0x35cf0)]
/\ rw_cells rsegs m' 0x35ce8 [C8 (Z_to_bv 64 0x35c00)]
/\ rw_cells rsegs m' 0x665e8 [C8 z64]
/\ rw_cells rsegs m' 0x665f8 [C8 z64]
/\ stdout_file m' stdout_init
/\ stderr_file m'

/\ bytes_at rsegs m' usp0 (entry_stack_image inp mbase Plain.M.phdrs (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) sp0 rnd)
/\ wr_at rsegs m' usp0 (Z.of_nat (length (entry_stack_image inp mbase Plain.M.phdrs (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) sp0 rnd)))
/\ nth_error (argv_ptrs inp rnd) 0 = Some (Z_to_bv 64 P0)

/\ (forall a : word, (0x34000 <= bv_unsigned a < 0x67000)%Z -> outside rcrt_written (bv_unsigned a) -> m' a = None)
/\ (0 < t < 4194304)%Z
(* the launch's head-size bound ([X0pw.launch_hsp]) and the top of its stack block, which the stack
   image's layout lemmas and the auxv facts take *)
/\ (usp0 + head_size inp <= bv_unsigned (ed_top rnd) - 8 - str_len inp)%Z
/\ (bv_unsigned (ed_top rnd) <= 0x800000000000)%Z.

Lemma rat_main_hsp : forall ms, rat_main ms -> (usp0 + head_size inp <= bv_unsigned (ed_top rnd) - 8 - str_len inp)%Z.
Proof.
intros ms H. unfold rat_main in H. repeat match goal with H : ex _ |- _ => destruct H as [? H] end.
repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption.
Qed.
End AtMain.

Ltac rimg_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].

Ltac rimg_chunk' NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].

Section Proof.
Variables (sp0 brk0 mbase : word) (rnd : EntryDraw) (inp : ProcInput).
Hypothesis VSP : valid_sp sp0.
Hypothesis VARGV : valid_argv (in_argv inp).
Hypothesis VENVP : valid_envp (in_envp inp).
Hypothesis VL : valid_launch inp.
Hypothesis LOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rnd) inp.
Notation ph := Plain.M.phdrs.
Notation usp0 := (bv_unsigned sp0).
Notation argv := (in_argv inp).
Notation envp := (in_envp inp).
Notation ent := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)).
Notation la := (launch_auxv inp sp0 mbase).
Notation cc := (la_cache (launch_auxv inp sp0 mbase)).
Notation img := (entry_stack_image inp mbase Plain.M.phdrs (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) sp0 rnd).

(* the launch's auxv words ([X0pw.auxv_words]) are [X1nn.rauxv] at the input's CONFIG_RSEQ flag *)
Lemma rauxv_eq : auxv_words inp mbase ph ent sp0 rnd
= rauxv (kb_rseq (in_kernel inp)) (la_sysinfo_ehdr la) (cw_l1i_size cc) (cw_l1i_geom cc) (cw_l1d_size cc)
(cw_l1d_geom cc) (cw_l2_size cc) (cw_l2_geom cc) (cw_l3_size cc) (cw_l3_geom cc) (la_minsigstksz la)
(in_hwcap inp) ent (in_uid inp) (in_gid inp) (Z_to_bv 64 (rnd_addr inp sp0)) (Z_to_bv 64 (execfn_addr inp rnd)).
Proof.
unfold auxv_words, auxv_entries, rauxv. change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)).
destruct (kb_rseq (in_kernel inp)); reflexivity.
Qed.

#[using="VSP VARGV VENVP VL LOK"] Theorem rstartup_spec_gen : forall F : bvmap 5 word,
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 mbase rnd inp F))
(MS (mkR_init sp0) F ent (Z_to_bv 32 0) None (wrap_mem inp mbase ph ent sp0 rnd) (seg_rom rsegs)).
Proof.
intros F.
pose proof (launch_hsp Sv48 inp mbase sp0 brk0 rnd LOK) as HSP.
pose proof (launch_window_lo inp sp0 brk0 mbase rnd VL LOK) as WLO.
pose proof LOK as LOK'. cbn [entry_launch_ok_va] in LOK'. destruct LOK' as ((_ & TOPHI & _) & LSP & _).
pose proof (launch_top_minus_sp inp (ed_top rnd) sp0 VL LSP) as TMS.
pose proof (image_length inp mbase ph ent sp0 rnd HSP) as IL.
pose proof (image_hi inp mbase ph ent sp0 rnd HSP) as IMGHI.
pose proof (head_size_ge inp) as HSG. unfold argc, envc in HSG.
pose proof (str_base_eq inp mbase ph ent sp0 rnd HSP) as SBE.
pose proof VSP as (SPLO & SPHI & SP16). unfold sp_window_lo, sp_window_hi, stack_max_size in SPLO, SPHI.
assert (TOP : (bv_unsigned (ed_top rnd) <= 0x800000000000)%Z) by (unfold va_stack_top, sp_window_hi in TOPHI; exact TOPHI).
assert (WLE : (stack_window_lo (in_kernel inp) mbase rnd <= usp0)%Z) by lia.
assert (WLO0 : (0x67000 <= stack_window_lo (in_kernel inp) mbase rnd)%Z).
{ unfold stack_window_lo, stack_max_size. pose proof (Nat2Z.is_nonneg (length img)). lia. }
unfold mkR_init.
set (m := wrap_mem inp mbase ph ent sp0 rnd).
change (Z.of_N Plain.M.init_pc) with 0x1b924%Z.
assert (NONE : forall a : word, (bv_unsigned a < 0x67000)%Z -> m a = None).
{ intros a Ha. apply (init_none inp mbase ph ent sp0 rnd WLE). lia. }
pose proof (init_stk rsegs inp mbase ph ent sp0 rnd (usp0 - 6144512) ltac:(lia) WLO) as ST. fold m in ST.
assert (MI : mem_inv rsegs m).
{ apply (init_mem_inv' rsegs inp mbase ph ent sp0 rnd WLE); [unfold TASK_SIZE; lia|].
change (segs_top rsegs) with 0x67000%Z. exact WLO0. }
pose proof (init_stack_bytes rsegs inp mbase ph ent sp0 rnd IMGHI) as IMG. fold m in IMG.
pose proof (init_stack_wr rsegs inp mbase ph ent sp0 rnd IMGHI) as WR. fold m in WR.
destruct (init_pieces rsegs inp mbase ph ent sp0 rnd HSP) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB).
fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
rewrite rauxv_eq in AUXW.

destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
{ destruct (nth_error argv 0) as [a|] eqn:EA; [exists a; reflexivity|].
exfalso. apply nth_error_None in EA. lia. }
destruct Harg0 as [arg0 Harg0].
destruct (init_argv_string rsegs inp mbase ph ent sp0 rnd HSP 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
fold m in STR.
pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
{ apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs inp rnd)).
{ apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
pose proof (envp_ptr_bounds inp mbase ph ent sp0 rnd HSP i w Hi).
pose proof (total_arg_bytes_nonneg argv). unfold env_base in *. lia. }

assert (RND : bytes_at rsegs m (rnd_addr inp sp0) (le8 (rnd_w0 rnd))).
{ rewrite rnd_bytes_eq in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
assert (RLO : (usp0 <= rnd_addr inp sp0)%Z) by (unfold rnd_addr; lia).

rimg_chunk NONE m 0x661b8%Z [C8 z64; C8 z64] G2.
rimg_chunk NONE m 0x66230%Z [C8 z64] HWC.
rimg_chunk NONE m 0x45e70%Z [C8 z64] ENVC.
rimg_chunk NONE m 0x661b0%Z [C8 z64] SI.
rimg_chunk NONE m 0x661c8%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
rimg_chunk NONE m 0x45e78%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
rimg_chunk NONE m 0x65f48%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
rimg_chunk NONE m 0x35de0%Z [C4 (Z_to_bv 64 0x20000)] DS.
rimg_chunk NONE m 0x661a8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
rimg_chunk NONE m 0x34b98%Z [C8 (Z_to_bv 64 0x45e70); C8 (Z_to_bv 64 0x661c0); C8 (Z_to_bv 64 0x661b8)] GOT3.
rimg_chunk NONE m 0x34bc0%Z [C8 (Z_to_bv 64 0x661a8)] GG.
rimg_chunk NONE m 0x34ad8%Z [C8 z64] GD.
rimg_chunk NONE m 0x34ae0%Z [C8 (Z_to_bv 64 0x1ba70); C8 (Z_to_bv 64 0x299e4); C8 (Z_to_bv 64 0x2a14c); C8 z64] GOT0.
rimg_chunk NONE m 0x34bb0%Z [C8 (Z_to_bv 64 0x341e0); C8 (Z_to_bv 64 0x341d8)] GIN.
rimg_chunk NONE m 0x341d8%Z [C8 (Z_to_bv 64 0x1b96c)] INA.
rimg_chunk NONE m 0x35df0%Z [C1 (Z_to_bv 8 0)] INI.
unfold libc_cells in LC. unfold td_cells in TDC.
assert (HC : argc inp = Z.of_nat (length argv)) by reflexivity.
assert (HE : envc inp = Z.of_nat (length envp)) by reflexivity.
assert (P0GE : (usp0 + 16 <= P0)%Z) by lia.
pose proof (munch_refl [(usp0 - 6144512, usp0); (0x35df0, 0x35df1); (0x45e70, 0x45e78); (0x45e78, 0x45fc8); (0x65f50, 0x65f80);
(0x661a8, 0x661b0); (0x661b8, 0x66238)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
clearbody m.

change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
iprefix.

do 7 lstep.

pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc inp))))) with (le4 (Z_to_bv 64 (argc inp))) in RD.
let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
lstep. clear RD.
replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
replace (sx32 (Z_to_bv 64 (argc inp))) with (Z_to_bv 64 (argc inp)).
2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
steps_to 0x29c60%Z.

carve_frame 32%nat ST.
do 8 lstep.

pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
lstep. clear RD ARGV.
do 3 lstep.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc inp) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 inp))
by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

assert (ENV : bytes_at rsegs m1 (envp_addr sp0 inp)
(u64s (envp_ptrs inp rnd) ++ le8 z64 ++ u64s (rauxv (kb_rseq (in_kernel inp)) (la_sysinfo_ehdr la) (cw_l1i_size cc)
(cw_l1i_geom cc) (cw_l1d_size cc) (cw_l1d_geom cc) (cw_l2_size cc) (cw_l2_geom cc) (cw_l3_size cc) (cw_l3_geom cc)
(la_minsigstksz la) (in_hwcap inp) ent (in_uid inp) (in_gid inp) (Z_to_bv 64 (rnd_addr inp sp0))
(Z_to_bv 64 (execfn_addr inp rnd))))).
{ rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
- rewrite u64s_length, envp_ptrs_length. exact E2.
- rewrite u64s_length, envp_ptrs_length, length_le8.
replace (usp0 + 8 * (argc inp + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
with (usp0 + 8 * (argc inp + envc inp + 3))%Z by lia.
exact AUXW. }
clear ENVP AUXW ARGC RNDB.
lstep. name_sp sp0 (-32)%Z.
icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 6144512)%Z
(envp_addr sp0 inp) (envp_ptrs inp rnd) (in_uid inp) (in_hwcap inp) (rnd_addr inp sp0) (rnd_w0 rnd) P0 arg0
(kb_rseq (in_kernel inp)) (la_sysinfo_ehdr la) (cw_l1i_size cc) (cw_l1i_geom cc) (cw_l1d_size cc) (cw_l1d_geom cc)
(cw_l2_size cc) (cw_l2_geom cc) (cw_l3_size cc) (cw_l3_geom cc) (la_minsigstksz la) ent (in_gid inp)
(Z_to_bv 64 (execfn_addr inp rnd))).
all: lazymatch goal with
| |- forall _, _ => ipost rsegs; unname_sp
| |- Forall _ _ => first [exact EPS | exact NONUL]
| |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
end.
rename PC into ST.
unfold td_cells, rtd_cells, libc_cells, envp_addr in *.

repeat match goal with
| H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
| H : bytes_at _ _ P0 _ |- _ => clear H
| H : bytes_at _ _ (rnd_addr _ _) _ |- _ => clear H
end.
clear EPS NONUL NONUL0 VA2 VA3 VA4 VA5 P0HI RLO.

steps_to 0x29cbc%Z. release_frame FR ST (bv_unsigned sp0). astep.

carve_frame 48%nat ST. steps_to 0x29c14%Z.

carve_frame 32%nat ST. steps_to 0x1b96c%Z.

carve_frame 16%nat ST. steps_to 0x1b9dc%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
steps_to 0x29c5c%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

steps_to 0x1ba70%Z.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc inp) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc inp + 2)))
by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

unfold id in IMG, WR.
lazymatch type of MU with munch ?W m ?mf =>
apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
assert (NONE' : forall a : word, (bv_unsigned a < 0x67000)%Z ->
outside [(usp0 - 6144512, usp0); (0x35df0, 0x35df1); (0x45e70, 0x45e78); (0x45e78, 0x45fc8); (0x65f50, 0x65f80);
(0x661a8, 0x661b0); (0x661b8, 0x66238)]%Z (bv_unsigned a) -> mf a = None)
by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
rimg_chunk' NONE' mf 0x34b00%Z [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64] GCX;
rimg_chunk' NONE' mf 0x34b10%Z [C8 (Z_to_bv 64 0x34ac0)] GSE;
rimg_chunk' NONE' mf 0x34bc8%Z [C8 (Z_to_bv 64 0x341e8); C8 (Z_to_bv 64 0x341e0)] GFI;
rimg_chunk' NONE' mf 0x341e0%Z [C8 (Z_to_bv 64 0x1b9e0)] FIA;
rimg_chunk' NONE' mf 0x34ac0%Z [C8 (Z_to_bv 64 0x35c00)] SEP;
rimg_chunk' NONE' mf 0x35e38%Z [C1 (Z_to_bv 8 0)] FIN;
rimg_chunk' NONE' mf 0x661a0%Z [C4 z64] EXL;
rimg_chunk' NONE' mf 0x35dd8%Z [C8 (Z_to_bv 64 0x35cf0)] SOU;
rimg_chunk' NONE' mf 0x35ce8%Z [C8 (Z_to_bv 64 0x35c00)] SEU;
rimg_chunk' NONE' mf 0x665e8%Z [C8 z64] SIN;
rimg_chunk' NONE' mf 0x665f8%Z [C8 z64] OFL;
rimg_chunk' NONE' mf 0x35cf0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x2dbec 0x66610 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
rimg_chunk' NONE' mf 0x66610%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
rimg_chunk' NONE' mf 0x35c00%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x2da54 0x66608 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
end.

lazymatch goal with TD : rw_cells _ _ 0x45e78 _ |- _ =>
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
match type of ERR with rw_cells _ _ ?A _ => replace A with 0x45e9c%Z in ERR by reflexivity end.
match type of TDb with rw_cells _ _ ?A _ => replace A with 0x45ea0%Z in TDb by reflexivity end.
lazymatch goal with L : rw_cells _ _ 0x661c8 _ |- _ =>
rewrite envp_ptrs_length in L;
replace (usp0 + 8 * (argc inp + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 inp) in L
by (unfold auxv_addr; lia);
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
match type of LCb with rw_cells _ _ ?A _ => replace A with 0x661d0%Z in LCb by reflexivity end.
apply evt_done. unfold rat_main, envp_addr.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
repeat match goal with |- _ /\ _ => split end.
all: lazymatch goal with
| |- stdout_file _ _ =>
exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024);
cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length to_bytes map firstn];
split; [exact SOF|]; split; [reflexivity|]; split; [exact SBUF|]; split; [reflexivity|];
split; [apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity|]; intros _; reflexivity
| |- stderr_file _ => exists (Z_to_bv 64 5), z64, 0%Z, 0%Z, (repeat (Z_to_bv 8 0) 80); exact SEF
| |- nth_error _ _ = _ => exact HP0
| |- wr_at _ _ _ _ => exact WR
| |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
unfold rcrt_written in Hout; cbn [outside] in Hout |- *; lia
| |- _ => first [hyp_by_addr | lia]
end.
Qed.

#[using="VSP VARGV VENVP VL LOK"] Theorem rstartup_spec :
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 mbase rnd inp bvmap_empty))
(init_ms rsegs Plain.M.init_pc Plain.M.phdrs sp0 mbase rnd inp).
Proof. exact (rstartup_spec_gen bvmap_empty). Qed.

#[using="VSP VARGV VENVP VL LOK"] Theorem rstartup_specF :
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 mbase rnd inp mkF0))
(init_msF rsegs Plain.M.init_pc Plain.M.phdrs sp0 mbase rnd inp).
Proof. exact (rstartup_spec_gen mkF0). Qed.
End Proof.
