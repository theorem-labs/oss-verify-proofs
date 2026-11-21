(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the proof takes the launch's ProcInput (argv, envp, uid and hwcap read from it), mmap base and brk, with valid_launch and the entry's launch check as hypotheses, and builds the launch values as the local instance lx0 (launch_of); the entry stack image (build_stack_bytes' new arguments, the auxv's entry, gid and exec-name values) in pat_main and pstartup_spec, pat_main's argv pointers at L_TOP with the exec name; the stack window from im_stack_depth below sp, not 8,388,608; psp_facts restated (image below 2^47, block below L_TOP, stack_window_lo bounds, image at most 2,101,782 bytes), pimg_len_bound removed; pstartup_spec starts from init_ms with the mmap base and the ProcInput; #[using] lists of psp_facts and pstartup_spec updated; 1 recorded proof replaced by a written proof (pstartup_spec); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg F_memset F_memcpy Startup_A Startup_B StdioFiles.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation rsegs := PImg.psegs.
(* The image's entry address, as the auxv publishes it (AT_ENTRY). *)
Notation pentry := (Z_to_bv 64 (Z.of_N p_init_pc)) (only parsing).
Section AtMain.
  Context {lx : launchT}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
Notation usp0 := (bv_unsigned sp0).
Definition pcrt_written : list (Z * Z) :=
[(0x1eaf0, 0x1eaf1); (0x2eb70, 0x2eb78); (0x2eb78, 0x2ecc8); (0x4ec50, 0x4ec80); (0x4eeb0, 0x4eeb8); (0x4eec0, 0x4ef40)]%Z.
Definition pat_main : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(t P0 : Z) (pg : word) (m' : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 0x14780) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x2ec40)
t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
(Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x1306c) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
bvmap_empty (Z_to_bv 64 0x1306c) (Z_to_bv 32 0) None m' (seg_rom rsegs)
/\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - im_stack_depth) (usp0 + -48)
/\ rw_cells rsegs m' 0x2eb78 [C8 (Z_to_bv 64 0x2eb78); C8 (Z_to_bv 64 0x2eb78); C8 (Z_to_bv 64 0x2eb78); C8 z64; C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' 0x2eb9c [C4 z64]
/\ rw_cells rsegs m' 0x2eba0 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x2ebf0);
CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x4ef08); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
C8 (Z_to_bv 64 0x2ec50); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
/\ rw_cells rsegs m' 0x4eed0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
/\ rw_cells rsegs m' 0x4eed8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
/\ rw_cells rsegs m' 0x4ec48 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' 0x4eeb8 [C8 z64]
/\ rw_cells rsegs m' 0x4eec0 [C8 pg; C8 (Z_to_bv 64 P0)]
/\ rw_cells rsegs m' 0x4ef38 [C8 hw]
/\ rw_cells rsegs m' 0x2eb70 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
/\ rw_cells rsegs m' 0x1eae8 [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' 0x4eeb0 [C8 c]
/\ rw_cells rsegs m' 0x1d850 [C8 z64]
/\ rw_cells rsegs m' 0x1d858 [C8 (Z_to_bv 64 0x1306c); C8 (Z_to_bv 64 0x14460); C8 (Z_to_bv 64 0x14c78); C8 z64]
/\ rw_cells rsegs m' 0x1d878 [C8 (Z_to_bv 64 0x14bac); C8 z64]
/\ rw_cells rsegs m' 0x1d888 [C8 (Z_to_bv 64 0x1d838)]
/\ rw_cells rsegs m' 0x1d8a0 [C8 (Z_to_bv 64 0x2eb70); C8 (Z_to_bv 64 0x4eec8); C8 (Z_to_bv 64 0x4eec0)]
/\ rw_cells rsegs m' 0x1d8b8 [C8 (Z_to_bv 64 0x1d830); C8 (Z_to_bv 64 0x1d828)]
/\ rw_cells rsegs m' 0x1d8c8 [C8 (Z_to_bv 64 0x4eeb0)]
/\ rw_cells rsegs m' 0x1d8d0 [C8 (Z_to_bv 64 0x1d838); C8 (Z_to_bv 64 0x1d830)]
/\ rw_cells rsegs m' 0x1d828 [C8 (Z_to_bv 64 0x12f68)]
/\ rw_cells rsegs m' 0x1d830 [C8 (Z_to_bv 64 0x12fdc)]
/\ rw_cells rsegs m' 0x1d838 [C8 (Z_to_bv 64 0x1e908)]
/\ rw_cells rsegs m' 0x1eaf0 [C1 (Z_to_bv 8 1)]
/\ rw_cells rsegs m' 0x1eb38 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m' 0x4eea8 [C4 z64]
/\ rw_cells rsegs m' 0x1eae0 [C8 (Z_to_bv 64 0x1e9f8)]
/\ rw_cells rsegs m' 0x1e9f0 [C8 (Z_to_bv 64 0x1e908)]
/\ rw_cells rsegs m' 0x4f2f0 [C8 z64]
/\ rw_cells rsegs m' 0x4f300 [C8 z64]
/\ stdout_file m' stdout_init
/\ stderr_file m'
    /\ bytes_at rsegs m' usp0 (build_stack_bytes L_LA p_phdrs pentry sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw)
    /\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes L_LA p_phdrs pentry sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw)))
    /\ nth_error (argv_ptrs L_TOP argv envp L_EXECFN) 0 = Some (Z_to_bv 64 P0)
/\ (forall a : word, (0x1d000 <= bv_unsigned a < 0x50000)%Z -> outside pcrt_written (bv_unsigned a) -> m' a = None)
/\ (0 < t < 4194304)%Z.
End AtMain.
Ltac pimg_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Ltac pimg_chunk' NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Section Proof.
  Variables (inp : ProcInput) (mbase brk sp0 : word) (draw : EntryDraw).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation uid := (in_uid inp).
  Notation hw := (in_hwcap inp).
Hypothesis VSP : valid_sp sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
  Hypothesis VLAUNCH : valid_launch inp.
  Hypothesis VOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase draw) inp.
  Local Instance lx0 : launchT := launch_of inp sp0 mbase draw.
Notation ph := p_phdrs.
Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes L_LA p_phdrs pentry sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Notation LOW := (stack_window_lo (in_kernel inp) mbase draw).
  #[using="VSP VARGV VENVP VLAUNCH VOK"] Lemma psp_facts : (usp0 + Z.of_nat (length img) <= 2^47)%Z /\
                    (usp0 + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z /\
                    (LOW <= usp0 - im_stack_depth)%Z /\ (usp0 - 8388608 <= LOW)%Z /\
                    (Z.of_nat (length img) <= 2101782)%Z.
Proof.
    pose proof (launch_facts inp sp0 brk mbase draw VLAUNCH VOK) as (H16 & HP & HD & HT & HL1 & HL2).
    pose proof (launch_image_length inp sp0 brk mbase ph pentry draw VLAUNCH VOK) as HLEN.
    change (entry_stack_image inp mbase ph pentry sp0 draw) with img in HLEN.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi in *.
    split; [lia|]. split; [exact HP|]. split; [exact H16|]. split; [lia|]. split; [exact HL1|].
    split; [unfold stack_max_size in HL2; lia|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>17364011611.1400000=S1L1H1M2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).
  #[using="VSP VARGV VENVP VLAUNCH VOK"] Theorem pstartup_spec :
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => pat_main sp0 argv envp uid hw draw pcanary))
         (init_ms rsegs p_init_pc p_phdrs sp0 mbase draw inp).
Proof.
    destruct psp_facts as (IMGHI & PADOK & SP16 & SPW & LOWHI & LOWLO & IL).
    pose proof LOWHI as LOWHI'. unfold im_stack_depth in LOWHI'.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph pentry sp0 draw).
    change (Z.of_N p_init_pc) with 0x12f20%Z.
assert (NONE : forall a : word, (bv_unsigned a < 0x50000)%Z -> m a = None).
    { intros a Ha. apply init_none; [lia|].
lia. }
    assert (ST0 : stk rsegs m LOW usp0) by (apply init_stk; lia).
    assert (ST : stk rsegs m (usp0 - im_stack_depth) usp0).
    { destruct ST0 as (A & B & C). unfold im_stack_depth in *. split; [lia|]. split; [lia|]. intros a Ha. apply C. lia. }
    clear ST0.
    (* the frame carves below read the stack's bottom, a constant lia does not unfold *)
    assert (ISD : im_stack_depth = 6144513%Z) by reflexivity.
    pose proof (init_mem_inv' rsegs inp mbase ph pentry sp0 draw ltac:(lia) ltac:(lia)
                  ltac:(change (segs_top rsegs) with 0x50000%Z; lia)) as MI.
fold m in MI.
    assert (IMG : bytes_at rsegs m usp0 img)
      by (apply init_stack_bytes; change (entry_stack_image inp mbase ph pentry sp0 draw) with img; lia).
    assert (WR : wr_at rsegs m usp0 (Z.of_nat (length img)))
      by (apply init_stack_wr; change (entry_stack_image inp mbase ph pentry sp0 draw) with img; lia).
    destruct (stack_pieces rsegs m L_LA ph pentry sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw IMG PADOK)
      as (ARGC & ARGV & ENVP & AUXW & RNDB & _ & _).
destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
{ destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string rsegs m L_LA ph pentry sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw IMG PADOK 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (layout_bounds L_LA sp0 L_TOP argv envp L_EXECFN PADOK) as (LB1 & LB2 & LB3 & LB4).
    pose proof (hsz_eq (la_rseq L_LA) argv envp) as HSZ.
    assert (AC : (27 <= auxv_count (la_rseq L_LA))%nat) by (destruct (la_rseq L_LA); cbv; lia).
pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
{ apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs L_TOP argv envp L_EXECFN)).
{ apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds L_LA sp0 L_TOP argv envp L_EXECFN PADOK i w Hi).
      unfold argc, envc in HSZ. lia. }
    assert (RND : bytes_at rsegs m (rnd_addr sp0 (la_rseq L_LA) argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
{ rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    assert (RLO : (usp0 <= rnd_addr sp0 (la_rseq L_LA) argv envp)%Z).
    { unfold rnd_addr. unfold argc, envc in HSZ. lia. }
pimg_chunk NONE m 0x4eec0%Z [C8 z64; C8 z64] G2.
pimg_chunk NONE m 0x4ef38%Z [C8 z64] HW.
pimg_chunk NONE m 0x2eb70%Z [C8 z64] ENVC.
pimg_chunk NONE m 0x4eeb8%Z [C8 z64] SI.
pimg_chunk NONE m 0x4eed0%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
pimg_chunk NONE m 0x2eb78%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
pimg_chunk NONE m 0x4ec48%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
pimg_chunk NONE m 0x1eae8%Z [C4 (Z_to_bv 64 0x20000)] DS.
pimg_chunk NONE m 0x4eeb0%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
pimg_chunk NONE m 0x1d8a0%Z [C8 (Z_to_bv 64 0x2eb70); C8 (Z_to_bv 64 0x4eec8); C8 (Z_to_bv 64 0x4eec0)] GOT3.
pimg_chunk NONE m 0x1d8c8%Z [C8 (Z_to_bv 64 0x4eeb0)] GG.
pimg_chunk NONE m 0x1d850%Z [C8 z64] GD.
pimg_chunk NONE m 0x1d858%Z [C8 (Z_to_bv 64 0x1306c); C8 (Z_to_bv 64 0x14460); C8 (Z_to_bv 64 0x14c78); C8 z64] GOT0.
pimg_chunk NONE m 0x1d8b8%Z [C8 (Z_to_bv 64 0x1d830); C8 (Z_to_bv 64 0x1d828)] GIN.
pimg_chunk NONE m 0x1d828%Z [C8 (Z_to_bv 64 0x12f68)] INA.
pimg_chunk NONE m 0x1eaf0%Z [C1 (Z_to_bv 8 0)] INI.
unfold libc_cells in LC. unfold td_cells in TDC.
assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
assert (P0GE : (usp0 + 184 <= P0)%Z).
    { unfold argc, envc in HSZ. lia. }
    pose proof (munch_refl [(usp0 - im_stack_depth, usp0); (0x1eaf0, 0x1eaf1); (0x2eb70, 0x2eb78); (0x2eb78, 0x2ecc8); (0x4ec50, 0x4ec80);
(0x4eeb0, 0x4eeb8); (0x4eec0, 0x4ef40)]%Z m) as MU.
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
steps_to 0x146dc%Z.
carve_frame 32%nat ST.
do 8 lstep.
pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
lstep. clear RD ARGV.
do 3 lstep.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (ENV : bytes_at rsegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs L_TOP argv envp L_EXECFN) ++ le8 z64
                     ++ u64s (pauxv L_LA pentry uid L_GID hw (Z_to_bv 64 (rnd_addr sp0 (la_rseq L_LA) argv envp))
                                (Z_to_bv 64 (execfn_ptr L_TOP L_EXECFN))))).
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
    icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - im_stack_depth)%Z
              (envp_addr sp0 argv) (envp_ptrs L_TOP argv envp L_EXECFN) (rnd_addr sp0 (la_rseq L_LA) argv envp) P0 arg0 _ _ _ _ uid hw
              (Z_to_bv 64 (draw_canary draw)) _ L_LA pentry L_GID (Z_to_bv 64 (execfn_ptr L_TOP L_EXECFN))).
all: lazymatch goal with
| |- forall _, _ => ipost rsegs; unname_sp
| |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr, im_stack_depth; lia ]
end.
rename PC into ST.
unfold td_cells, rtd_cells, libc_cells, envp_addr in *.
repeat match goal with
| H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
| H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO LB1 LB2 LB3 LB4 HSZ AC.
steps_to 0x14738%Z. release_frame FR ST (bv_unsigned sp0). astep.
carve_frame 48%nat ST. steps_to 0x14690%Z.
carve_frame 32%nat ST. steps_to 0x12f68%Z.
carve_frame 16%nat ST. steps_to 0x12fd8%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
steps_to 0x146d8%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
steps_to 0x1306c%Z.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
unfold id in IMG, WR.
lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; unfold im_stack_depth; lia];
apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
assert (NONE' : forall a : word, (bv_unsigned a < 0x50000)%Z ->
                outside [(usp0 - im_stack_depth, usp0); (0x1eaf0, 0x1eaf1); (0x2eb70, 0x2eb78); (0x2eb78, 0x2ecc8); (0x4ec50, 0x4ec80);
(0x4eeb0, 0x4eeb8); (0x4eec0, 0x4ef40)]%Z (bv_unsigned a) -> mf a = None)
by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
pimg_chunk' NONE' mf 0x1d878%Z [C8 (Z_to_bv 64 0x14bac); C8 z64] GCX;
pimg_chunk' NONE' mf 0x1d888%Z [C8 (Z_to_bv 64 0x1d838)] GSE;
pimg_chunk' NONE' mf 0x1d8d0%Z [C8 (Z_to_bv 64 0x1d838); C8 (Z_to_bv 64 0x1d830)] GFI;
pimg_chunk' NONE' mf 0x1d830%Z [C8 (Z_to_bv 64 0x12fdc)] FIA;
pimg_chunk' NONE' mf 0x1d838%Z [C8 (Z_to_bv 64 0x1e908)] SEP;
pimg_chunk' NONE' mf 0x1eb38%Z [C1 (Z_to_bv 8 0)] FIN;
pimg_chunk' NONE' mf 0x4eea8%Z [C4 z64] EXL;
pimg_chunk' NONE' mf 0x1eae0%Z [C8 (Z_to_bv 64 0x1e9f8)] SOU;
pimg_chunk' NONE' mf 0x1e9f0%Z [C8 (Z_to_bv 64 0x1e908)] SEU;
pimg_chunk' NONE' mf 0x4f2f0%Z [C8 z64] SIN;
pimg_chunk' NONE' mf 0x4f300%Z [C8 z64] OFL;
pimg_chunk' NONE' mf 0x1e9f8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x173e8 0x4f318 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
pimg_chunk' NONE' mf 0x4f318%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
pimg_chunk' NONE' mf 0x1e908%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x17250 0x4f310 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
end.
lazymatch goal with TD : rw_cells _ _ 0x2eb78 _ |- _ =>
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
match type of ERR with rw_cells _ _ ?A _ => replace A with 0x2eb9c%Z in ERR by reflexivity end.
match type of TDb with rw_cells _ _ ?A _ => replace A with 0x2eba0%Z in TDb by reflexivity end.
lazymatch goal with L : rw_cells _ _ 0x4eed0 _ |- _ =>
rewrite envp_ptrs_length in L;
replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
by (unfold auxv_addr; lia);
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
match type of LCb with rw_cells _ _ ?A _ => replace A with 0x4eed8%Z in LCb by reflexivity end.
apply evt_done. unfold pat_main, envp_addr.
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
unfold pcrt_written in Hout; cbn [outside] in Hout |- *; lia
| |- _ => first [hyp_by_addr | lia]
end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proof.
