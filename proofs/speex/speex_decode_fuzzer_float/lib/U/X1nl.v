(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0pw X0qx X0qy X0qw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd X1nm X1nn X1ea.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Notation rsegs := X1ff.rsegs.

Section AtMain.
Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).

Variables (hw : word) (rnd : EntryDraw).

Variable (F : bvmap 5 word).
Notation usp0 := (bv_unsigned sp0).

Definition rcrt_written : list (Z * Z) :=
[(0x3d300, 0x3d301); (0x4d380, 0x4d388); (0x4d388, 0x4d4d8); (0x6d460, 0x6d490); (0x6d6b8, 0x6d6c0); (0x6d6c8, 0x6d748)]%Z.

Definition rat_main : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(t P0 : Z) (pg : word) (m' : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 0x310d0) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x4d450)
t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
(Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x1bc88) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bc88) (Z_to_bv 32 0) None m' (seg_rom rsegs)
/\ mem_inv rsegs m'
/\ stk rsegs m' (usp0 - 8388608) (usp0 + -48)

/\ rw_cells rsegs m' 0x4d388 [C8 (Z_to_bv 64 0x4d388); C8 (Z_to_bv 64 0x4d388); C8 (Z_to_bv 64 0x4d388); C8 z64; C4 (Z_to_bv 64 t)]

/\ rw_cells rsegs m' 0x4d3ac [C4 z64]

/\ rw_cells rsegs m' 0x4d3b0 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x4d400);
CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x6d710); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (canary_of (rnd_w0 rnd));
C8 (Z_to_bv 64 0x4d460); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]

/\ rw_cells rsegs m' 0x6d6d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]

/\ rw_cells rsegs m' 0x6d6e0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]

/\ rw_cells rsegs m' 0x6d458 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]

/\ rw_cells rsegs m' 0x6d6c0 [C8 z64]
/\ rw_cells rsegs m' 0x6d6c8 [C8 pg; C8 (Z_to_bv 64 P0)]
/\ rw_cells rsegs m' 0x6d740 [C8 hw]
/\ rw_cells rsegs m' 0x4d380 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
/\ rw_cells rsegs m' 0x3d2f0 [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' 0x6d6b8 [C8 (canary_of (rnd_w0 rnd))]

/\ rw_cells rsegs m' 0x3bfe8 [C8 z64]
/\ rw_cells rsegs m' 0x3bff0 [C8 (Z_to_bv 64 0x1bc88); C8 (Z_to_bv 64 0x30db0); C8 (Z_to_bv 64 0x31518); C8 z64]
/\ rw_cells rsegs m' 0x3c010 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64]
/\ rw_cells rsegs m' 0x3c020 [C8 (Z_to_bv 64 0x3bfd0)]
/\ rw_cells rsegs m' 0x3c0a8 [C8 (Z_to_bv 64 0x4d380); C8 (Z_to_bv 64 0x6d6d0); C8 (Z_to_bv 64 0x6d6c8)]
/\ rw_cells rsegs m' 0x3c0c0 [C8 (Z_to_bv 64 0x3b6f0); C8 (Z_to_bv 64 0x3b6e8)]
/\ rw_cells rsegs m' 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)]
/\ rw_cells rsegs m' 0x3c0d8 [C8 (Z_to_bv 64 0x3b6f8); C8 (Z_to_bv 64 0x3b6f0)]

/\ rw_cells rsegs m' 0x3b6e8 [C8 (Z_to_bv 64 0x1bb84)]
/\ rw_cells rsegs m' 0x3b6f0 [C8 (Z_to_bv 64 0x1bbf8)]
/\ rw_cells rsegs m' 0x3bfd0 [C8 (Z_to_bv 64 0x3d110)]

/\ rw_cells rsegs m' 0x3d300 [C1 (Z_to_bv 8 1)]
/\ rw_cells rsegs m' 0x3d348 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m' 0x6d6b0 [C4 z64]

/\ rw_cells rsegs m' 0x3d2e8 [C8 (Z_to_bv 64 0x3d200)]
/\ rw_cells rsegs m' 0x3d1f8 [C8 (Z_to_bv 64 0x3d110)]
/\ rw_cells rsegs m' 0x6daf8 [C8 z64]
/\ rw_cells rsegs m' 0x6db08 [C8 z64]
/\ stdout_file m' stdout_init
/\ stderr_file m'

/\ bytes_at rsegs m' usp0 (build_stack_bytes Ubsan.M.phdrs sp0 argv envp uid hw rnd)
/\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes Ubsan.M.phdrs sp0 argv envp uid hw rnd)))
/\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)

/\ (forall a : word, (0x3b000 <= bv_unsigned a < 0x6e000)%Z -> outside rcrt_written (bv_unsigned a) -> m' a = None)
/\ (0 < t < 4194304)%Z.
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
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
Hypothesis VSP : valid_sp sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.

Hypothesis FIT : entry_stack_fits sp0 argv envp.
Notation ph := Ubsan.M.phdrs.
Notation usp0 := (bv_unsigned sp0).
Notation img := (build_stack_bytes Ubsan.M.phdrs sp0 argv envp uid hw rnd).

#[using="VARGV VENVP"] Lemma rimg_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
Proof.
rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
pose proof (raw_len_nonneg argv envp). unfold raw_len, struct_size, argc, envc in *. lia.
Qed.

#[using="VSP VARGV VENVP"] Lemma rsp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= 2^64)%Z /\
(usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
Proof.
destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *.
pose proof rimg_len_bound. lia.
Qed.

#[using="VSP VARGV VENVP FIT"] Theorem rstartup_spec_gen : forall F : bvmap 5 word,
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 argv envp uid hw rnd F))
(MS (mkR_init sp0) F (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) (Z_to_bv 32 0) None
(wrap_mem Ubsan.M.phdrs sp0 argv envp uid hw rnd) (seg_rom rsegs)).
Proof.
intros F.
first [ sf_destruct 4%nat rsp_facts as SPLO IMGHI SP16 SPW | sf_fb; destruct rsp_facts as (SPLO & IMGHI & SP16 & SPW) ].
pose proof rimg_len_bound as IL.
unfold mkR_init. change (Z.of_N Ubsan.M.init_pc) with 0x1bb3c%Z.
set (m := wrap_mem ph sp0 argv envp uid hw rnd).
assert (NONE : forall a : word, (bv_unsigned a < 0x6e000)%Z -> m a = None).
{ intros a Ha. apply init_none. unfold stack_max_size. lia. }
pose proof (init_stk rsegs ph sp0 argv envp uid hw rnd SPLO) as ST. fold m in ST.
change stack_max_size with 8388608%Z in ST.
assert (PGTS : (entry_page_top sp0 img <= TASK_SIZE)%Z).
{ pose proof (entry_page_top_within_window ph sp0 argv envp uid hw rnd FIT) as X. unfold sp_window_hi in X. unfold TASK_SIZE. exact X. }
pose proof (init_mem_inv' rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI ltac:(change (segs_top rsegs) with 0x6e000%Z; unfold stack_max_size; lia) PGTS) as MI.
fold m in MI.
pose proof (init_stack_bytes rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as IMG. fold m in IMG.
pose proof (init_wr rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw rnd) in WR.
first [ pose proof (init_pieces rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as sfP_; sf_destruct 7%nat sfP_ as ARGC ARGV ENVP AUXW _ _ RNDB | sf_fb; destruct (init_pieces rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB) ]. fold m in ARGC, ARGV, ENVP, AUXW, RNDB.

first [ sf_destruct 5%nat VARGV as VA1 VA2 VA3 VA4 VA5 | sf_fb; destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5) ].
assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
{ destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
destruct Harg0 as [arg0 Harg0].
first [ pose proof (init_argv_string rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI 0 arg0 Harg0) as sfP_; sf_destruct 5%nat sfP_ as P0 HP0 P0LO P0HI STR | sf_fb; destruct (init_argv_string rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR) ].
fold m in STR.
pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
{ apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
{ apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
pose proof (envp_ptr_bounds ph sp0 argv envp uid hw rnd IMGHI i w Hi).
pose proof (raw_len_nonneg argv envp). unfold env_base, str_base, struct_size in *. lia. }

assert (RND : bytes_at rsegs m (rnd_addr sp0 argv envp) (le8 (rnd_w0 rnd))).
{ rewrite rnd_bytes_eq in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
{ pose proof (raw_len_nonneg argv envp). unfold rnd_addr, raw_len. lia. }

rimg_chunk NONE m 0x6d6c8%Z [C8 z64; C8 z64] G2.
rimg_chunk NONE m 0x6d740%Z [C8 z64] HWC.
rimg_chunk NONE m 0x4d380%Z [C8 z64] ENVC.
rimg_chunk NONE m 0x6d6c0%Z [C8 z64] SI.
rimg_chunk NONE m 0x6d6d8%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
rimg_chunk NONE m 0x4d388%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
rimg_chunk NONE m 0x6d458%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
rimg_chunk NONE m 0x3d2f0%Z [C4 (Z_to_bv 64 0x20000)] DS.
rimg_chunk NONE m 0x6d6b8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
rimg_chunk NONE m 0x3c0a8%Z [C8 (Z_to_bv 64 0x4d380); C8 (Z_to_bv 64 0x6d6d0); C8 (Z_to_bv 64 0x6d6c8)] GOT3.
rimg_chunk NONE m 0x3c0d0%Z [C8 (Z_to_bv 64 0x6d6b8)] GG.
rimg_chunk NONE m 0x3bfe8%Z [C8 z64] GD.
rimg_chunk NONE m 0x3bff0%Z [C8 (Z_to_bv 64 0x1bc88); C8 (Z_to_bv 64 0x30db0); C8 (Z_to_bv 64 0x31518); C8 z64] GOT0.
rimg_chunk NONE m 0x3c0c0%Z [C8 (Z_to_bv 64 0x3b6f0); C8 (Z_to_bv 64 0x3b6e8)] GIN.
rimg_chunk NONE m 0x3b6e8%Z [C8 (Z_to_bv 64 0x1bb84)] INA.
rimg_chunk NONE m 0x3d300%Z [C1 (Z_to_bv 8 0)] INI.
unfold libc_cells in LC. unfold td_cells in TDC.
assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
assert (P0GE : (usp0 + 184 <= P0)%Z).
{ pose proof (raw_len_nonneg argv envp). unfold str_base, struct_size in P0LO. lia. }
pose proof (munch_refl [(usp0 - 8388608, usp0); (0x3d300, 0x3d301); (0x4d380, 0x4d388); (0x4d388, 0x4d4d8); (0x6d460, 0x6d490);
(0x6d6b8, 0x6d6c0); (0x6d6c8, 0x6d748)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
clearbody m.

change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
iprefix.

do 7 lstep.

pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
lstep. clear RD.
replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
steps_to 0x3102c%Z.

carve_frame 32%nat ST.
do 8 lstep.

pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
lstep. clear RD ARGV.
do 3 lstep.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

assert (ENV : bytes_at rsegs m1 (envp_addr sp0 argv)
(u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (rauxv20 uid hw (Z_to_bv 64 (rnd_addr sp0 argv envp))))).
{ rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
- rewrite u64s_length, envp_ptrs_length. exact E2.
- rewrite u64s_length, envp_ptrs_length, length_le8.
replace (usp0 + 8 * (argc argv + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
with (usp0 + 8 * (argc argv + envc envp + 3))%Z by lia.
exact AUXW. }
clear ENVP AUXW ARGC RNDB.
lstep. name_sp sp0 (-32)%Z.
icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608)%Z
(envp_addr sp0 argv) (envp_ptrs sp0 argv envp) uid hw (rnd_addr sp0 argv envp) (rnd_w0 rnd) P0 arg0).
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
| H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
end.
clear EPS NONUL NONUL0 VA2 VA3 VA4 VA5 P0HI RLO.

steps_to 0x31088%Z. release_frame FR ST (bv_unsigned sp0). astep.

carve_frame 48%nat ST. steps_to 0x30fe0%Z.

carve_frame 32%nat ST. steps_to 0x1bb84%Z.

carve_frame 16%nat ST. steps_to 0x1bbf4%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
steps_to 0x31028%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

steps_to 0x1bc88%Z.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

unfold id in IMG, WR.
lazymatch type of MU with munch ?W m ?mf =>
apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
assert (NONE' : forall a : word, (bv_unsigned a < 0x6e000)%Z ->
outside [(usp0 - 8388608, usp0); (0x3d300, 0x3d301); (0x4d380, 0x4d388); (0x4d388, 0x4d4d8); (0x6d460, 0x6d490);
(0x6d6b8, 0x6d6c0); (0x6d6c8, 0x6d748)]%Z (bv_unsigned a) -> mf a = None)
by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
rimg_chunk' NONE' mf 0x3c010%Z [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64] GCX;
rimg_chunk' NONE' mf 0x3c020%Z [C8 (Z_to_bv 64 0x3bfd0)] GSE;
rimg_chunk' NONE' mf 0x3c0d8%Z [C8 (Z_to_bv 64 0x3b6f8); C8 (Z_to_bv 64 0x3b6f0)] GFI;
rimg_chunk' NONE' mf 0x3b6f0%Z [C8 (Z_to_bv 64 0x1bbf8)] FIA;
rimg_chunk' NONE' mf 0x3bfd0%Z [C8 (Z_to_bv 64 0x3d110)] SEP;
rimg_chunk' NONE' mf 0x3d348%Z [C1 (Z_to_bv 8 0)] FIN;
rimg_chunk' NONE' mf 0x6d6b0%Z [C4 z64] EXL;
rimg_chunk' NONE' mf 0x3d2e8%Z [C8 (Z_to_bv 64 0x3d200)] SOU;
rimg_chunk' NONE' mf 0x3d1f8%Z [C8 (Z_to_bv 64 0x3d110)] SEU;
rimg_chunk' NONE' mf 0x6daf8%Z [C8 z64] SIN;
rimg_chunk' NONE' mf 0x6db08%Z [C8 z64] OFL;
rimg_chunk' NONE' mf 0x3d200%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x350fc 0x6db20 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
rimg_chunk' NONE' mf 0x6db20%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
rimg_chunk' NONE' mf 0x3d110%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x34f64 0x6db18 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
end.

lazymatch goal with TD : rw_cells _ _ 0x4d388 _ |- _ =>
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
match type of ERR with rw_cells _ _ ?A _ => replace A with 0x4d3ac%Z in ERR by reflexivity end.
match type of TDb with rw_cells _ _ ?A _ => replace A with 0x4d3b0%Z in TDb by reflexivity end.
lazymatch goal with L : rw_cells _ _ 0x6d6d8 _ |- _ =>
rewrite envp_ptrs_length in L;
replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
by (unfold auxv_addr; lia);
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
match type of LCb with rw_cells _ _ ?A _ => replace A with 0x6d6e0%Z in LCb by reflexivity end.
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

#[using="VSP VARGV VENVP FIT"] Theorem rstartup_spec :
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 argv envp uid hw rnd bvmap_empty))
(init_ms rsegs Ubsan.M.init_pc Ubsan.M.phdrs sp0 argv envp uid hw rnd).
Proof. exact (rstartup_spec_gen bvmap_empty). Qed.

#[using="VSP VARGV VENVP FIT"] Theorem rstartup_specF :
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 argv envp uid hw rnd mkF0))
(init_msF rsegs Ubsan.M.init_pc Ubsan.M.phdrs sp0 argv envp uid hw rnd).
Proof. exact (rstartup_spec_gen mkF0). Qed.
End Proof.
