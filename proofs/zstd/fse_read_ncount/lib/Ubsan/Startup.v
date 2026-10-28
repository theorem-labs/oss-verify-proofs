(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_memset F_memcpy Startup_A Startup_B StdioFiles.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation rsegs := UImg.usegs.
Section AtMain.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
Notation usp0 := (bv_unsigned sp0).
Definition pcrt_written : list (Z * Z) :=
[(0x1ede0, 0x1ede1); (0x2ee60, 0x2ee68); (0x2ee68, 0x2efb8); (0x4ef40, 0x4ef70); (0x4f1a0, 0x4f1a8); (0x4f1b0, 0x4f230)]%Z.
Definition pat_main : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(t P0 : Z) (pg : word) (m' : word -> option byte),
ms' = MS (mkR (Z_to_bv 64 0x14a68) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x2ef30)
t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
(Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x13088) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
bvmap_empty (Z_to_bv 64 0x13088) (Z_to_bv 32 0) None m' (seg_rom rsegs)
/\ mem_inv rsegs m'
/\ stk rsegs m' (usp0 - 8388608) (usp0 + -48)
/\ rw_cells rsegs m' 0x2ee68 [C8 (Z_to_bv 64 0x2ee68); C8 (Z_to_bv 64 0x2ee68); C8 (Z_to_bv 64 0x2ee68); C8 z64; C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' 0x2ee8c [C4 z64]
/\ rw_cells rsegs m' 0x2ee90 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x2eee0);
CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x4f1f8); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
C8 (Z_to_bv 64 0x2ef40); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
/\ rw_cells rsegs m' 0x4f1c0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
/\ rw_cells rsegs m' 0x4f1c8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
/\ rw_cells rsegs m' 0x4ef38 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' 0x4f1a8 [C8 z64]
/\ rw_cells rsegs m' 0x4f1b0 [C8 pg; C8 (Z_to_bv 64 P0)]
/\ rw_cells rsegs m' 0x4f228 [C8 hw]
/\ rw_cells rsegs m' 0x2ee60 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
/\ rw_cells rsegs m' 0x1edd0 [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' 0x4f1a0 [C8 c]
/\ rw_cells rsegs m' 0x1db38 [C8 z64]
/\ rw_cells rsegs m' 0x1db40 [C8 (Z_to_bv 64 0x13088); C8 (Z_to_bv 64 0x14748); C8 (Z_to_bv 64 0x14f60); C8 z64]
/\ rw_cells rsegs m' 0x1db60 [C8 (Z_to_bv 64 0x14e94); C8 z64]
/\ rw_cells rsegs m' 0x1db70 [C8 (Z_to_bv 64 0x1db20)]
/\ rw_cells rsegs m' 0x1db88 [C8 (Z_to_bv 64 0x2ee60); C8 (Z_to_bv 64 0x4f1b8); C8 (Z_to_bv 64 0x4f1b0)]
/\ rw_cells rsegs m' 0x1dba0 [C8 (Z_to_bv 64 0x1db18); C8 (Z_to_bv 64 0x1db10)]
/\ rw_cells rsegs m' 0x1dbb0 [C8 (Z_to_bv 64 0x4f1a0)]
/\ rw_cells rsegs m' 0x1dbb8 [C8 (Z_to_bv 64 0x1db20); C8 (Z_to_bv 64 0x1db18)]
/\ rw_cells rsegs m' 0x1db10 [C8 (Z_to_bv 64 0x12f84)]
/\ rw_cells rsegs m' 0x1db18 [C8 (Z_to_bv 64 0x12ff8)]
/\ rw_cells rsegs m' 0x1db20 [C8 (Z_to_bv 64 0x1ebf0)]
/\ rw_cells rsegs m' 0x1ede0 [C1 (Z_to_bv 8 1)]
/\ rw_cells rsegs m' 0x1ee28 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m' 0x4f198 [C4 z64]
/\ rw_cells rsegs m' 0x1edc8 [C8 (Z_to_bv 64 0x1ece0)]
/\ rw_cells rsegs m' 0x1ecd8 [C8 (Z_to_bv 64 0x1ebf0)]
/\ rw_cells rsegs m' 0x4f5e0 [C8 z64]
/\ rw_cells rsegs m' 0x4f5f0 [C8 z64]
/\ stdout_file m' stdout_init
/\ stderr_file m'
/\ bytes_at rsegs m' usp0 (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)
/\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)))
/\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
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
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
Hypothesis VSP : valid_sp sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Notation ph := u_phdrs.
Notation usp0 := (bv_unsigned sp0).
Notation img := (build_stack_bytes u_phdrs sp0 argv envp uid hw draw).
Notation simg := (entry_stack_image u_phdrs sp0 argv envp uid hw draw).
#[using="VARGV VENVP"] Lemma pimg_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
Proof.
rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
pose proof (raw_len_nonneg argv envp). unfold raw_len, struct_size, argc, envc in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59699364112.1400000?S2A12A22E12E21H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="VSP VARGV VENVP"] Lemma psp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length simg) <= 2^64)%Z /\
(usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
Proof.
destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *.
pose proof pimg_len_bound. pose proof (length_simg_bound u_phdrs sp0 argv envp uid hw draw). Local Ltac2 Set LiaHints.tbl := fun () => "0010>17364011611.1400000=S1L1H1M2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).
#[using="VSP VARGV VENVP"] Theorem pstartup_spec :
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => pat_main sp0 argv envp uid hw draw pcanary))
(init_ms rsegs u_init_pc u_phdrs sp0 argv envp uid hw draw).
Proof.
destruct psp_facts as (SPLO & IMGHI & SP16 & SPW).
pose proof pimg_len_bound as IL. pose proof (length_simg_bound u_phdrs sp0 argv envp uid hw draw) as ILS.
unfold init_ms, mkR_init. change (Z.of_N u_init_pc) with 0x12f3c%Z.
set (m := wrap_mem ph sp0 argv envp uid hw draw).
assert (NONE : forall a : word, (bv_unsigned a < 0x50000)%Z -> m a = None).
{ intros a Ha. apply init_none. unfold stack_max_size. Local Ltac2 Set LiaHints.tbl := fun () => "0330?10070414107.48 10248252334.56 10388827377.31 10637993098.79 10656864309.56 11113827900.80 11483769539.86 12385124117.85 12395247488.46 12664622354.88 13206176911.64 14394566956.80 15045343677.64 16075377781.64 17799843423.67 17811593679.46 18216447625.87 18496384439.44 18875603732.43 19372245699.88 19372245699.89 19621599171.73 19621599171.83 20668380775.78 20891375131.46 20902092430.85 2164407698.89  2166682268.45  21718101121.97 22707086531.76 22707086531.85 23031486095.43 23546943427.88 24374343941.63 24769663939.84 24885038966.90 25500707465.88 25630914020.43 265078479.90   27136713373.58 27630458514.91 2813090755.88  28697891979.90 29419089816.92 29588601993.52 29784364028.66 29784543482.79 30032995318.82 30510454375.84 30707906395.18 31012906773.63 31398085315.86 32101940251.90 32101940253.81 32600510915.87 32706278665.91 33848481433.82 34147624451.92 34263294510.80 35046270212.81 35632207290.79 35632518844.66 35993291285.47 36149829018.55 3673275331.89  3673275331.90  36952585843.76 37206732592.53 3745707623.88  38124880667.49 38256400657.50 39806217206.85 40253174032.90 40424375814.81 40796593913.81 40914699165.81 41201790582.85 42382893968.86 42554324245.83 44510515979.51 44682177565.84 45411169678.47 4559945606.84  46360778002.52 46487942930.87 46746329739.57 47013515907.93 47291585127.89 47472668807.96 48620102794.50 51134774028.54 51244920423.87 52354692483.97 52370152275.63 52513925490.10052526506853.45 52526506853.46 52526506853.47 52526506853.48 52526506853.49 52526506853.50 52526506853.51 52526506853.52 52526506853.53 52526506853.54 52526506853.55 52526506853.56 52526506853.57 52526506853.58 52526506853.59 52526506853.60 52526506853.82 52526506853.83 52526506853.84 52526506853.85 52526506853.86 52526506853.87 52526506853.88 52526506853.89 52526506853.90 52526506853.91 52526506853.92 52526506853.93 52526506853.94 52526506853.95 52566903287.79 53193183275.64 53699193447.86 53920826015.63 54275884647.88 54571412491.86 54590717134.77 54856257723.75 54856326432.64 55179078700.44 56044795708.79 56203865191.76 57227484418.82 57239504852.64 57465737899.53 57627976193.55 5777391462.77  5843300923.62  59315449551.76 59315449551.85 59548510311.73 5981763352.93  60310494835.90 61064364176.51 61357533030.76 61733728519.45 61735648777.89 61767467224.75 61821510595.78 61821510595.86 61892971191.80 62092207555.86 62092207555.87 62371883756.79 62577245174.90 64361010534.66 64793354502.58 65121514518.92 66051197543.88 66094744694.86 66165028624.57 66788317838.83 67167658112.48 67204360828.67 68056849040.64 68294959255.54 68498130535.86 71800583.79    7191075638.67  7428666775.67  8106088953.63  8190124262.80  8672338560.49  8793840459.100 8806420828.82  8806420828.83  8806420828.84  8806420828.85  8806420828.86  8806420828.87  8806420828.88  8806420828.89  8806420828.90  8806420828.91  8806420828.92  8806420828.93  8806420828.94  8806420828.95  9077079040.18  9397368423.86  00000500:00C00D00I00N00S00T00Y00Z00c00d00i01201:01H01I01N01S01X01]01b01g01l02102202302802>02C02H02M02R02[02`02a02b02i02n03303403903:03;03@03E03F03G03L03X03]03b03n04:04?04@04A04B04C04H04M04R04W04\04a04f04k05005505:05?05@05A05B05G05H05I05J05K05P05Q05V05W05\05]05b05c05h06006506:06?06E06O06S06W06[06_06c06g06k06o07307707;07?07C07G07K07O07S07W07[07_07c07g07k07o08308708;08?08C08G08K08T08]08b08n09309409909>09C09H09M09R09S09X09]09b09g0:;0:@0:E0:J0:K0:P0:U0:Z0:_0:`0:e0:j0:o0;00;50;:0;?0;@0;E0;J0;K0;P0;Q0;V0;W0;\0;a0;f0;k0<00<50<@0<I0<R0<W0<\0<m0=90=E0=Q0=]0=i0>50>A0>M0>Y0>e0?10?=0?I0?U0?^0?cS3ILSS3ILSS3ILS3VA1FS3ILSS3ILSS3ILSSS3ILSSS3SPW3ILSSS3ILSS3ILS3VA1S3ILS2HES3SPW3ILS1H2H0SS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSSSS3ILSS4PC15S3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3ILSSSS3ILS1HS3ILSS3ILSSS3ILSSSS3ILSS3ILSSSS3ILSS3SPW3ILS2HaS3ILSS3ILSS3ILS3VA12HCS3ILS3VA12HCS3ILSSSSFS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSSSSS3ILSSSSSS3ILSSS3ILSSS3ILSSS3ILSSS3ILSS3ILS2HES3ILSS3ILSS3ILSS4POSTS3ILS4P0GES2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS3SPW3ILSS3ILS3VA1S3ILSS3ILS3VA12HCS3ILSSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSSS3ILSS3ILSS3ILSS3ILSS3ILS3VA14P0LO2HC2HES3ILSS3ILSS3ILSSS3ILSS3ILSS3ILSS3ILSSS3ILSS3ILSS3ILSSS3ILSS3ILSS3ILSSS3ILSS3ILSSS3ILSSS3ILSSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILS1HS3ILS3VA1S3ILS3RLOS3ILSS3ILSS3SPW3ILS2Ha4HoutS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILSS3ILS".
lia. }
pose proof (init_stk rsegs ph sp0 argv envp uid hw draw SPLO) as ST. fold m in ST.
change stack_max_size with 8388608%Z in ST.
pose proof (init_mem_inv' rsegs ph sp0 argv envp uid hw draw SPLO IMGHI ltac:(change (segs_top rsegs) with 0x50000%Z; unfold stack_max_size; lia)) as MI.
fold m in MI.
pose proof (init_stack_bytes rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as IMG. fold m in IMG.
pose proof (init_wr rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw draw) in WR.
destruct (init_pieces rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
{ destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
destruct Harg0 as [arg0 Harg0].
destruct (init_argv_string rsegs ph sp0 argv envp uid hw draw SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
fold m in STR.
pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
{ apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
{ apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
pose proof (envp_ptr_bounds ph sp0 argv envp uid hw draw IMGHI i w Hi).
pose proof (raw_len_nonneg argv envp). unfold env_base, str_base, struct_size in *. lia. }
assert (RND : bytes_at rsegs m (rnd_addr sp0 argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
{ rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
{ pose proof (raw_len_nonneg argv envp). unfold rnd_addr, raw_len. lia. }
pimg_chunk NONE m 0x4f1b0%Z [C8 z64; C8 z64] G2.
pimg_chunk NONE m 0x4f228%Z [C8 z64] HW.
pimg_chunk NONE m 0x2ee60%Z [C8 z64] ENVC.
pimg_chunk NONE m 0x4f1a8%Z [C8 z64] SI.
pimg_chunk NONE m 0x4f1c0%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
pimg_chunk NONE m 0x2ee68%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
pimg_chunk NONE m 0x4ef38%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
pimg_chunk NONE m 0x1edd0%Z [C4 (Z_to_bv 64 0x20000)] DS.
pimg_chunk NONE m 0x4f1a0%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
pimg_chunk NONE m 0x1db88%Z [C8 (Z_to_bv 64 0x2ee60); C8 (Z_to_bv 64 0x4f1b8); C8 (Z_to_bv 64 0x4f1b0)] GOT3.
pimg_chunk NONE m 0x1dbb0%Z [C8 (Z_to_bv 64 0x4f1a0)] GG.
pimg_chunk NONE m 0x1db38%Z [C8 z64] GD.
pimg_chunk NONE m 0x1db40%Z [C8 (Z_to_bv 64 0x13088); C8 (Z_to_bv 64 0x14748); C8 (Z_to_bv 64 0x14f60); C8 z64] GOT0.
pimg_chunk NONE m 0x1dba0%Z [C8 (Z_to_bv 64 0x1db18); C8 (Z_to_bv 64 0x1db10)] GIN.
pimg_chunk NONE m 0x1db10%Z [C8 (Z_to_bv 64 0x12f84)] INA.
pimg_chunk NONE m 0x1ede0%Z [C1 (Z_to_bv 8 0)] INI.
unfold libc_cells in LC. unfold td_cells in TDC.
assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
assert (P0GE : (usp0 + 184 <= P0)%Z).
{ pose proof (raw_len_nonneg argv envp). unfold str_base, struct_size in P0LO. lia. }
pose proof (munch_refl [(usp0 - 8388608, usp0); (0x1ede0, 0x1ede1); (0x2ee60, 0x2ee68); (0x2ee68, 0x2efb8); (0x4ef40, 0x4ef70);
(0x4f1a0, 0x4f1a8); (0x4f1b0, 0x4f230)]%Z m) as MU.
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
steps_to 0x149c4%Z.
carve_frame 32%nat ST.
do 8 lstep.
pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
lstep. clear RD ARGV.
do 3 lstep.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (ENV : bytes_at rsegs m1 (envp_addr sp0 argv)
(u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 (rnd_addr sp0 argv envp))))).
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
(envp_addr sp0 argv) (envp_ptrs sp0 argv envp) (rnd_addr sp0 argv envp) P0 arg0 _ _ _ _ uid hw (Z_to_bv 64 (draw_canary draw))).
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
clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO.
steps_to 0x14a20%Z. release_frame FR ST (bv_unsigned sp0). astep.
carve_frame 48%nat ST. steps_to 0x14978%Z.
carve_frame 32%nat ST. steps_to 0x12f84%Z.
carve_frame 16%nat ST. steps_to 0x12ff4%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
steps_to 0x149c0%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
steps_to 0x13088%Z.
replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
unfold id in IMG, WR.
lazymatch type of MU with munch ?W m ?mf =>
apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
assert (NONE' : forall a : word, (bv_unsigned a < 0x50000)%Z ->
outside [(usp0 - 8388608, usp0); (0x1ede0, 0x1ede1); (0x2ee60, 0x2ee68); (0x2ee68, 0x2efb8); (0x4ef40, 0x4ef70);
(0x4f1a0, 0x4f1a8); (0x4f1b0, 0x4f230)]%Z (bv_unsigned a) -> mf a = None)
by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
pimg_chunk' NONE' mf 0x1db60%Z [C8 (Z_to_bv 64 0x14e94); C8 z64] GCX;
pimg_chunk' NONE' mf 0x1db70%Z [C8 (Z_to_bv 64 0x1db20)] GSE;
pimg_chunk' NONE' mf 0x1dbb8%Z [C8 (Z_to_bv 64 0x1db20); C8 (Z_to_bv 64 0x1db18)] GFI;
pimg_chunk' NONE' mf 0x1db18%Z [C8 (Z_to_bv 64 0x12ff8)] FIA;
pimg_chunk' NONE' mf 0x1db20%Z [C8 (Z_to_bv 64 0x1ebf0)] SEP;
pimg_chunk' NONE' mf 0x1ee28%Z [C1 (Z_to_bv 8 0)] FIN;
pimg_chunk' NONE' mf 0x4f198%Z [C4 z64] EXL;
pimg_chunk' NONE' mf 0x1edc8%Z [C8 (Z_to_bv 64 0x1ece0)] SOU;
pimg_chunk' NONE' mf 0x1ecd8%Z [C8 (Z_to_bv 64 0x1ebf0)] SEU;
pimg_chunk' NONE' mf 0x4f5e0%Z [C8 z64] SIN;
pimg_chunk' NONE' mf 0x4f5f0%Z [C8 z64] OFL;
pimg_chunk' NONE' mf 0x1ece0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x176d0 0x4f608 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
pimg_chunk' NONE' mf 0x4f608%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
pimg_chunk' NONE' mf 0x1ebf0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x17538 0x4f600 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
end.
lazymatch goal with TD : rw_cells _ _ 0x2ee68 _ |- _ =>
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
match type of ERR with rw_cells _ _ ?A _ => replace A with 0x2ee8c%Z in ERR by reflexivity end.
match type of TDb with rw_cells _ _ ?A _ => replace A with 0x2ee90%Z in TDb by reflexivity end.
lazymatch goal with L : rw_cells _ _ 0x4f1c0 _ |- _ =>
rewrite envp_ptrs_length in L;
replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
by (unfold auxv_addr; lia);
apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
match type of LCb with rw_cells _ _ ?A _ => replace A with 0x4f1c8%Z in LCb by reflexivity end.
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
