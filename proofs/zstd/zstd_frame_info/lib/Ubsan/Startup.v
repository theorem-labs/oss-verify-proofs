(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_memset F_memcpy Startup_A Startup_B StdioFiles.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := UImg.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
  (* [comment removed for export] *)
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition pcrt_written : list (Z * Z) :=
    [(0x1dee0, 0x1dee1); (0x2df60, 0x2df68); (0x2df68, 0x2e0b8); (0x4e040, 0x4e070); (0x4e298, 0x4e2a0); (0x4e2a8, 0x4e328)]%Z.

  Definition pat_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13cdc) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x2e030)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x127ec) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x127ec) (Z_to_bv 32 0) None m' (seg_rom rsegs)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2df68 [C8 (Z_to_bv 64 0x2df68); C8 (Z_to_bv 64 0x2df68); C8 (Z_to_bv 64 0x2df68); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2df8c [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x2df90 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x2dfe0);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x4e2f0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
                                 C8 (Z_to_bv 64 0x2e040); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x4e2b8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x4e2c0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x4e038 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x4e2a0 [C8 z64]
    /\ rw_cells rsegs m' 0x4e2a8 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells rsegs m' 0x4e320 [C8 hw]
    /\ rw_cells rsegs m' 0x2df60 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells rsegs m' 0x1ded8 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' 0x4e298 [C8 c]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x1cc40 [C8 z64]
    /\ rw_cells rsegs m' 0x1cc48 [C8 (Z_to_bv 64 0x127ec); C8 (Z_to_bv 64 0x139bc); C8 (Z_to_bv 64 0x14124); C8 z64]
    /\ rw_cells rsegs m' 0x1cc68 [C8 (Z_to_bv 64 0x14058); C8 z64]
    /\ rw_cells rsegs m' 0x1cc78 [C8 (Z_to_bv 64 0x1cc28)]
    /\ rw_cells rsegs m' 0x1cc90 [C8 (Z_to_bv 64 0x2df60); C8 (Z_to_bv 64 0x4e2b0); C8 (Z_to_bv 64 0x4e2a8)]
    /\ rw_cells rsegs m' 0x1cca8 [C8 (Z_to_bv 64 0x1cc20); C8 (Z_to_bv 64 0x1cc18)]
    /\ rw_cells rsegs m' 0x1ccb8 [C8 (Z_to_bv 64 0x4e298)]
    /\ rw_cells rsegs m' 0x1ccc0 [C8 (Z_to_bv 64 0x1cc28); C8 (Z_to_bv 64 0x1cc20)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x1cc18 [C8 (Z_to_bv 64 0x126e8)]
    /\ rw_cells rsegs m' 0x1cc20 [C8 (Z_to_bv 64 0x1275c)]
    /\ rw_cells rsegs m' 0x1cc28 [C8 (Z_to_bv 64 0x1dcf8)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x1dee0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs m' 0x1df28 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0x4e290 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x1ded0 [C8 (Z_to_bv 64 0x1dde8)]
    /\ rw_cells rsegs m' 0x1dde0 [C8 (Z_to_bv 64 0x1dcf8)]
    /\ rw_cells rsegs m' 0x4e6d8 [C8 z64]
    /\ rw_cells rsegs m' 0x4e6e8 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' usp0 (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)
    /\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x1c000 <= bv_unsigned a < 0x4f000)%Z -> outside pcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac pimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).

  #[using="VSP VARGV VENVP"] Theorem pstartup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => pat_main sp0 argv envp uid hw draw pcanary))
         (init_ms rsegs u_init_pc u_phdrs sp0 argv envp uid hw draw).
  Proof.
    destruct psp_facts as (SPLO & IMGHI & SP16 & SPW).
    pose proof pimg_len_bound as IL. pose proof (length_simg_bound u_phdrs sp0 argv envp uid hw draw) as ILS.
    unfold init_ms, mkR_init. change (Z.of_N u_init_pc) with 0x126a0%Z.
    set (m := wrap_mem ph sp0 argv envp uid hw draw).
    assert (NONE : forall a : word, (bv_unsigned a < 0x4f000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. Local Ltac2 Set LiaHints.tbl := fun () => "07f0?10068007177.88 10224280728.89 10237535901.58 10263306008.87 10268871186.89 10274202092.79 10274202092.93 10388827377.31 10509430936.79 10509430936.89 10509430936.91 10667250950.58 10781987992.89 10869356312.87 10873507702.82 11113827900.80 11176140568.87 1123096707.92  11483769539.86 11806655000.81 11806655000.91 11806655000.92 12066282988.79 12066282988.93 12216817688.81 12216817688.91 12216817688.92 12444241166.81 12664422411.57 13037471212.79 13037471212.93 13206176911.64 13234623000.87 13328422296.89 14340668681.52 14722868868.99 14826596632.79 14850439021.76 15045343677.64 15215617816.87 15539463119.81 15670301260.77 15823283329.55 16075377781.64 16119225496.89 16193897880.89 16462209579.53 16546012056.89 16547368728.87 16774719132.45 16787763480.81 16787763480.91 16787763480.92 1694482328.89  17034181170.79 17223795648.74 17799843423.67 17811593679.46 17834013066.79 18217605400.81 18217605400.91 18217605400.92 182209452.80   18494412681.91 18604744471.54 18913659377.97 19042827563.75 19042827563.88 19042827563.89 19358229784.81 19358229784.91 19358229784.92 19365407768.76 19365407768.89 19365407768.90 19372245699.88 19372245699.89 19411207320.79 19411207320.89 19411207320.91 19563105944.79 19563105944.89 19563105944.91 19621599171.73 19621599171.83 19964125230.80 20225713540.99 20495584512.46 20667246060.79 20667246060.93 20668380775.78 20728007223.80 21226110747.49 21226158224.90 21698355151.86 21718101121.97 21788391190.88 21968898001.83 22387597248.85 22707086531.76 22707086531.85 22999058864.53 23077509607.78 23077509607.92 23223914816.77 23283716588.79 23283716588.93 23546943427.88 24374343941.63 24769663939.84 24956574232.87 25042987031.93 25125205380.99 25333160075.51 25500379024.57 25630914020.43 25632264527.82 25632264527.85 26313435160.76 26313435160.89 26313435160.90 26471014607.86 265078479.90   26596665143.44 26596744320.48 26604760216.89 26702847261.81 26980036244.43 26980051733.85 27147338155.78 27147338155.88 27147338155.90 27284310508.79 27284310508.93 27346961284.99 27363063576.87 27450494619.46 2745835288.87  27478109676.79 27478109676.93 27630327445.83 27716611864.76 27716611864.89 27716611864.90 27820079222.90 27829487411.79 28072922155.86 2813090755.88  28406852928.87 28420759039.99 28828584216.76 28828584216.89 28828584216.90 29015312408.81 29015312408.91 29015312408.92 29271837848.79 29271837848.89 29271837848.91 29624125464.76 29624125464.89 29624125464.90 29784364028.66 29784543482.79 29823858968.81 29823858968.91 29823858968.92 30487722008.81 30487722008.91 30487722008.92 30510454375.84 30650514820.99 30707906395.18 3084545980.79  31012906773.63 31036938449.87 31398085315.86 31718565522.87 31770388120.79 31770388120.89 31770388120.91 31793141171.91 31904217881.79 31978967295.99 32101940251.90 32101940253.81 32153104530.52 32442164504.81 32442164504.91 32442164504.92 32600101849.98 32600510915.87 32706147598.83 32762049119.76 32803748867.93 32907263168.89 32985609624.89 33039915414.92 33313664792.76 33313664792.89 33313664792.90 33534703512.93 33924000758.85 33924000758.90 34086726124.79 34086726124.93 34169650127.87 34440526528.88 34581657368.87 34770220056.76 34770220056.89 34770220056.90 35046270212.81 35526766232.79 35526766232.89 35526766232.91 35632207290.79 35632518844.66 36319061784.92 3673275331.89  3673275331.90  36802289280.49 36802369803.90 36925003916.54 36952585843.76 3745707623.88  37937718111.81 37964217134.56 38270180589.79 3850242702.85  3850260239.43  38541588376.89 38679688671.79 38908001203.91 38908001203.92 38911347919.87 39065172822.80 39113643908.99 39196035793.86 39197252870.84 4002602141.84  402109031.87   40460011584.87 40776591384.81 40776591384.91 40776591384.92 40796593913.81 41621998744.89 4163812241.50  41779725592.81 41779725592.91 41779725592.92 41918306513.84 42096762392.87 42648081816.89 42706650505.89 42846887832.76 43032395394.82 43136937240.81 43136937240.91 43136937240.92 43407189580.91 445243152.51   4481707727.87  44851328263.45 45225311439.87 4534952836.99  45742248344.79 45742248344.89 45742248344.91 46101533848.79 46101533848.89 46101533848.91 46168270654.81 46386664472.76 46386664472.89 46386664472.90 46462227904.89 47016595062.85 47291585127.89 47328938628.99 47349350067.89 47472668807.96 48313144512.87 48519237912.81 48519237912.91 48519237912.92 48562591384.79 48562591384.89 48562591384.91 48941763344.86 48990548559.87 49009737496.87 49483552408.79 49483552408.89 49483552408.91 49663609880.76 49663609880.89 49663609880.90 49873949293.81 50626392856.76 50626392856.89 50626392856.90 50667478351.87 50885055896.79 50885055896.89 50885055896.91 51073615253.47 51244920423.87 51326157700.99 51407635864.79 51407635864.89 51407635864.91 51551565292.79 51551565292.93 5170374848.79  52354692483.97 52370152275.63 52513925490.10052526506853.45 52526506853.46 52526506853.47 52526506853.48 52526506853.49 52526506853.50 52526506853.51 52526506853.52 52526506853.53 52526506853.54 52526506853.55 52526506853.56 52526506853.57 52526506853.58 52526506853.59 52526506853.60 52526506853.82 52526506853.83 52526506853.84 52526506853.85 52526506853.86 52526506853.87 52526506853.88 52526506853.89 52526506853.90 52526506853.91 52526506853.92 52526506853.93 52526506853.94 52526506853.95 52566903287.79 52577538839.76 52577538839.79 52577538839.81 52577538839.87 52577538839.89 52577538839.90 52577538839.91 52577538839.92 52577538839.93 52577538839.99 52579502455.80 52579502455.87 52579502455.88 52853961481.87 52877465881.82 53003761688.76 53003761688.89 53003761688.90 53184435608.79 53184435608.89 53184435608.91 53193183275.64 53511454222.47 53660321578.79 53699193447.86 53920826015.63 53958185452.79 53958185452.93 54275884647.88 54315287064.87 54315885120.89 54505215896.89 54590717134.77 54605059791.84 54625414206.76 54673589656.79 54673589656.89 54673589656.91 54856257723.75 54856326432.64 55177106962.91 55841003544.76 55841003544.89 55841003544.90 56044795708.79 5607884440.81  56203865191.76 56961190296.79 56961190296.89 56961190296.91 57109141272.76 57109141272.89 57109141272.90 57239504852.64 57541014225.81 5777391462.77  58339098092.79 58339098092.93 5843300923.62  58579945240.76 58579945240.89 58579945240.90 59315449551.76 59315449551.85 594016748.79   594016748.93   59426343926.86 59548510311.73 59622888068.99 59922101071.87 60310494835.90 60334854080.90 6038730191.87  60534122449.82 60534122449.85 60684552472.81 60684552472.91 60684552472.92 61357533030.76 61767467224.75 61821510595.78 61821510595.86 62072628396.44 62072807195.48 62092207555.86 62092207555.87 62371883756.79 62637849068.79 62637849068.93 62675629707.86 63014573208.89 63124363140.99 636342916.99   63677959192.81 63677959192.91 63677959192.92 63709060378.55 64361010534.66 64926728684.79 64926728684.93 65168669365.56 65212743211.80 65212743211.90 65212743211.91 66051197543.88 66118714776.89 66468786574.79 66500441476.99 66723971774.79 67170134674.88 67204360828.67 67210899763.91 6722522879.99  67455461400.87 67543153284.99 67968927366.81 67981895704.76 67981895704.89 67981895704.90 68056849040.64 68481107479.93 68498130535.86 6863291727.83  71800583.79    7191075638.67  721185103.83   7428666775.67  8106088953.63  8109761546.50  8190124262.80  8469109262.76  8603416747.88  8793840459.100 8806420828.82  8806420828.83  8806420828.84  8806420828.85  8806420828.86  8806420828.87  8806420828.88  8806420828.89  8806420828.90  8806420828.91  8806420828.92  8806420828.93  8806420828.94  8806420828.95  9050768876.79  9050768876.93  9077079040.18  9397368423.86  9941432856.87  00000500>00C00L00Q00Z00c00l01501>01G01L01U01^01c01h02102602;02D02M02V02_02h03103:03C03L03Q03Z03c03l04504>04C04H04R04W04\04e04f04o05405=05F05O05T05]05f05k06406=06F06O06T06]06i07707807A07J07S07X07]07b07g08008908B08K08T08]08f08o09809=09B09K09T09]09f09o0:80:=0:B0:C0:H0:M0:V0:_0:d0:i0:n0;30;40;>0;?0;L0;U0;Z0;_0;d0;m0<60<?0<H0<Q0<V0<_0<d0<m0=20=70=<0=A0=L0=M0=N0=W0=`0=i0>60>;0>@0>E0>N0>S0>X0>]0>f0>o0?80?A0?J0?O0?X0?]0?f0?o0@80@=0@F0@O0@X0@]0A00A90A>0AG0AP0AY0Ab0Ak0B40B=0BF0BO0BX0Ba0Bj0C30C<0CA0CF0CO0CX0Ca0Cj0D30D<0DA0DF0DR0D\0Da0Dn0E30E80EA0EJ0ES0EX0E]0Ef0F60FF0FK0FT0F]0Ff0Fk0G00G50GH0GM0GV0G_0Gd0Gm0H60H?0HD0HI0HN0HW0H`0Hm0I60I?0IH0IQ0IZ0I_0Ih0J10J:0J?0JD0JI0JN0JS0JX0J]0Jb0Jg0Jl0K?0KD0KI0KN0KS0K\0Ko0L40L90LF0LG0LL0LY0L^0Lc0M50M>0MG0MP0MY0M^0Mg0Ml0N50N>0NG0NT0N]0Nf0Nk0O50O:0OC0OL0OU0O^0Oc0P00P50P60P;0PD0PM0PV0P_0Ph0Q10Q60Q?0QH0QQ0QZ0Q_0Qd0Qi0Qn0R:0RC0RL0RU0R^0Rg0S00S90S>0SK0ST0S]0Sf0So0T80TA0TJ0TO0TX0Ta0Tj0U70U@0UI0UR0UW0U\0Ua0Uj0V30V<0VE0VN0VW0Va0Vk0W30W;0WC0WK0WS0W[0Wc0Wk0X30X;0XC0XK0XS0X[0Xc0Xk0Y30Y;0YC0YK0YS0Y[0Yc0Yk0Z30Z;0ZC0ZK0ZS0Z[0Zc0Zl0[10[60[;0[@0[E0[J0[O0[T0[Y0[^0[_0\00\10\60\;0\D0\M0\V0\_0\h0]10]:0]?0]H0]M0]]0]f0]o0^40^=0^F0^O0^T0^U0^Z0^c0^l0_50_:0_?0_D0_M0_V0__0_d0_n0`30`<0`E0`N0`W0``0`i0`n0a;0a@0aI0aR0aj0b30b<0bE0bJ0bO0bX0ba0bf0bk0c00c=0cB0cK0cX0ce0d20d;0dD0dM0dR0dW0d\0da0df0dk0e00e50e:0eC0eL0eQ0eZ0e_0ed0em0f60f?0fD0fI0fR0f[0f`0fi0g20g;0g@0gI0gR0gW0g\0ga0gf0gk0h40h=0hB0hG0hP0hY0hb0hg0hl0i10i20i70iB0iO0iX0ia0if0ik0j40j=0jN0jZ0jf0k20k>0kJ0kV0kb0kn0l:0lF0lR0l^0lj0m60m?0mH0mQ0mV0m_S3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILS3VA1S3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILS3RLOS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILS4P0GES3ILSS3ILSS3SPW3ILSFS3SPW3ILSS3ILSS3ILS3VA1S3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILS2HES3SPW3ILS1H2H0FS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSFS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3ILSFS3ILS4PC15FS3SPW3ILS3HspS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILS1HFFS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILS3HspS3ILSS3ILSS3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILS3VA12HC2HES3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILS2HaS3ILS4P0GES3ILSS3SPW3ILS3HspS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILS3VA12HCS3SPW3ILS3VA12HCS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILS3VA12HC2HES3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILS3HspS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILS3VA12HC2HES3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILS3VA12HC2HES3ILSS3ILSS3SPW3ILS3HspFS3ILSS3SPW3ILS3HspS3ILSS3ILSS3SPW3ILS4P0GE3HspS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILS3HspS3SPW3ILSS3SPW3ILSS3ILSS3ILS4P0GES3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILS3HspS3ILSFS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILS2HES3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILS3HspS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILS3HspS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILS4POSTS3ILS4P0GES3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3ILS2HaS3SPW3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSFS3SPW3ILS3RLO3HspFS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILS3VA1S3ILSS3ILS3RLOS3ILSS3SPW3ILS3VA12HCS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSFS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILS4P0GES3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILS3HspS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILS3VA14P0LO2HC2HES3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3SPW3ILS3HspS3ILSS3SPW3ILSS3SPW3ILS3HspS3SPW3ILS3HspS3SPW3ILS3HspS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILSS3ILS3RLOS3ILSS3ILSS3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3ILSS3ILSFS3ILSS3SPW3ILS1HS3SPW3ILS3HspS3ILS3VA1S3ILS3RLOS3ILSS3ILSS3ILS3RLOS3SPW3ILSS3SPW3ILS2Ha4HoutS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILS2HaS3SPW3ILSS3SPW3ILSS3SPW3ILSS3ILSS3SPW3ILS".
lia. }
    pose proof (init_stk rsegs ph sp0 argv envp uid hw draw SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' rsegs ph sp0 argv envp uid hw draw SPLO IMGHI ltac:(change (segs_top rsegs) with 0x4f000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as IMG. fold m in IMG.
    pose proof (init_wr rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw draw) in WR.
    destruct (init_pieces rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    assert (RND : bytes_at rsegs m (rnd_addr sp0 argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
    { rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg argv envp). unfold rnd_addr, raw_len. lia. }
    (* [comment removed for export] *)
    pimg_chunk NONE m 0x4e2a8%Z [C8 z64; C8 z64] G2.
    pimg_chunk NONE m 0x4e320%Z [C8 z64] HW.
    pimg_chunk NONE m 0x2df60%Z [C8 z64] ENVC.
    pimg_chunk NONE m 0x4e2a0%Z [C8 z64] SI.
    pimg_chunk NONE m 0x4e2b8%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    pimg_chunk NONE m 0x2df68%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    pimg_chunk NONE m 0x4e038%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    pimg_chunk NONE m 0x1ded8%Z [C4 (Z_to_bv 64 0x20000)] DS.
    pimg_chunk NONE m 0x4e298%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    pimg_chunk NONE m 0x1cc90%Z [C8 (Z_to_bv 64 0x2df60); C8 (Z_to_bv 64 0x4e2b0); C8 (Z_to_bv 64 0x4e2a8)] GOT3.
    pimg_chunk NONE m 0x1ccb8%Z [C8 (Z_to_bv 64 0x4e298)] GG.
    pimg_chunk NONE m 0x1cc40%Z [C8 z64] GD.
    pimg_chunk NONE m 0x1cc48%Z [C8 (Z_to_bv 64 0x127ec); C8 (Z_to_bv 64 0x139bc); C8 (Z_to_bv 64 0x14124); C8 z64] GOT0.
    pimg_chunk NONE m 0x1cca8%Z [C8 (Z_to_bv 64 0x1cc20); C8 (Z_to_bv 64 0x1cc18)] GIN.
    pimg_chunk NONE m 0x1cc18%Z [C8 (Z_to_bv 64 0x126e8)] INA.
    pimg_chunk NONE m 0x1dee0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { pose proof (raw_len_nonneg argv envp). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0x1dee0, 0x1dee1); (0x2df60, 0x2df68); (0x2df68, 0x2e0b8); (0x4e040, 0x4e070);
                            (0x4e298, 0x4e2a0); (0x4e2a8, 0x4e328)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.
    (* [comment removed for export] *)
    do 7 lstep.
    (* [comment removed for export] *)
    pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x13c38%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO.
    (* [comment removed for export] *)
    steps_to 0x13c94%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x13bec%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x126e8%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x12758%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x13c34%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x127ec%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x4f000)%Z ->
                outside [(usp0 - 8388608, usp0); (0x1dee0, 0x1dee1); (0x2df60, 0x2df68); (0x2df68, 0x2e0b8); (0x4e040, 0x4e070);
                         (0x4e298, 0x4e2a0); (0x4e2a8, 0x4e328)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      pimg_chunk' NONE' mf 0x1cc68%Z [C8 (Z_to_bv 64 0x14058); C8 z64] GCX;
      pimg_chunk' NONE' mf 0x1cc78%Z [C8 (Z_to_bv 64 0x1cc28)] GSE;
      pimg_chunk' NONE' mf 0x1ccc0%Z [C8 (Z_to_bv 64 0x1cc28); C8 (Z_to_bv 64 0x1cc20)] GFI;
      pimg_chunk' NONE' mf 0x1cc20%Z [C8 (Z_to_bv 64 0x1275c)] FIA;
      pimg_chunk' NONE' mf 0x1cc28%Z [C8 (Z_to_bv 64 0x1dcf8)] SEP;
      pimg_chunk' NONE' mf 0x1df28%Z [C1 (Z_to_bv 8 0)] FIN;
      pimg_chunk' NONE' mf 0x4e290%Z [C4 z64] EXL;
      pimg_chunk' NONE' mf 0x1ded0%Z [C8 (Z_to_bv 64 0x1dde8)] SOU;
      pimg_chunk' NONE' mf 0x1dde0%Z [C8 (Z_to_bv 64 0x1dcf8)] SEU;
      pimg_chunk' NONE' mf 0x4e6d8%Z [C8 z64] SIN;
      pimg_chunk' NONE' mf 0x4e6e8%Z [C8 z64] OFL;
      pimg_chunk' NONE' mf 0x1dde8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x167dc 0x4e700 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      pimg_chunk' NONE' mf 0x4e700%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      pimg_chunk' NONE' mf 0x1dcf8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x16644 0x4e6f8 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    (* [comment removed for export] *)
    lazymatch goal with TD : rw_cells _ _ 0x2df68 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x2df8c%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x2df90%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x4e2b8 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x4e2c0%Z in LCb by reflexivity end.
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
