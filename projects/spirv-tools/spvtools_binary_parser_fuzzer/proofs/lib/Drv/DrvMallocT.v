(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatSim ShapeAlg SRealizes RefMemcpyLib AllocCeil RunRandom LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Cells.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_DrvMallocT () := "C46Stdlib5Lists4List6map_idC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7map_mapC49OSSVerify5KrLib8LibIface2ASC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4ainvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib9RunRandom9rr_canaryC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib5Lists7ListDef3mapc59OSSVerify5KrLib3Drv:DrvMallocT9mcg_guardC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface?ai_static_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC46Stdlib5Lists4List7map_extC46Stdlib5Lists4List:length_mapC59OSSVerify5KrLib3Drv7S1Cells4cellC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~i59OSSVerify5KrLib3Drv:DrvMallocT:mi_constsG00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8S1Layout1LC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition LIBC : Z := 0x120948.

Section MainMem.
Context {AC : AllocCeiling} {RRND : RunRandom}.

Record drv_main_mem (M : LibIface.mem) : Prop := DRV_MAIN_MEM {
  mm_ctx    : img_clear M 0x120ac0 0x120e68;
  mm_vmlock : img_clear M 0x1216ac 0x1216b0;
  mm_libc0  : cell M LIBC 1 1;
  mm_libc1  : cell M (LIBC + 1) 1 0;
  mm_libc2  : cell M (LIBC + 2) 1 0;
  mm_libc3  : cell M (LIBC + 3) 1 0;
  mm_libc4  : cell M (LIBC + 4) 4 0;
  mm_auxv   : exists auxv, 0 <= auxv < 2 ^ 64 /\ cell M (LIBC + 8) 8 auxv;
  mm_tlshd  : cell M (LIBC + 16) 8 0;
  mm_tlssz  : cell M (LIBC + 24) 8 224;
  mm_tlsal  : cell M (LIBC + 32) 8 8;
  mm_tlscnt : cell M (LIBC + 40) 8 0;
  mm_pgsz   : cell M (LIBC + 48) 8 4096;
  mm_gloc   : forall i, 0 <= i < 48 -> exists b, rdn SEGS M (Z_to_bv 64 (LIBC + 56 + i)) 1 = Some [b] /\ b = Z_to_bv 8 0;

  mm_guard  : cell M 0x120928 8 rr_canary;
  mm_ro     : img_ro_clear L M
}.

Record drv_main_model {AMB : Amb} (mo : Model) : Prop := DRV_MAIN_MODEL {
  mo_maps  : vm_maps (m_vmmaps mo) = [];
  mo_noacc : vm_noaccess (m_vmmaps mo) = [];
  mo_resv  : vm_reserved (m_vmmaps mo) = segments_reserved SEGS;
  mo_brk   : vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo);
  mo_sb    : valid_brk SEGS (vm_start_brk (m_vmmaps mo));
  mo_sbhi  : bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * 4096 <= alloc_ceiling;
  mo_lim   : 2 ^ 34 <= vm_limit (m_vmmaps mo);
  mo_lazy  : m_vm_lazy mo = [];
  mo_mat   : m_vm_materialized mo = []
}.

Definition auxv_words (x3 x4 x5 x16 x6 x11 x12 x23 rnd : Z) : list Z :=
  [3; x3; 4; x4; 5; x5; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].
Definition drv_auxv (M : LibIface.mem) (sp : Z) : Prop :=
  exists av x3 x4 x5 x16 x6 x11 x12 x23 rnd,
    cell M (LIBC + 8) 8 av
    /\ (forall i, (i < 20)%nat -> cell M (av + 8 * Z.of_nat i) 8 (nth i (auxv_words x3 x4 x5 x16 x6 x11 x12 x23 rnd) 0))
    /\ cell M (rnd + 8) 8 rr_secret
    /\ alloc_ceiling <= sp /\ sp <= av /\ av + 160 <= 2 ^ 64 /\ sp <= rnd + 8 /\ rnd + 16 <= 2 ^ 64
    /\ Forall (fun x => 0 <= x < 2 ^ 64) [x3; x4; x5; x16; x6; x11; x12; x23; rnd].

End MainMem.

Section G.
  Context {AC : AllocCeiling} {RRND : RunRandom}.
  Context {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variable AINV0 : AS MI -> LibIface.mem -> Model -> Prop.
  Variables (TIGHT FRESH44 : AS MI -> Prop).

  #[local] Notation cfg fx R pc M model :=
    (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Definition ainv_initG : Prop :=
    forall (M : LibIface.mem) (mo : Model),
      drv_main_mem M -> drv_main_model mo ->
      exists A : AS MI,
        AINV0 A M mo /\ live MI A = [] /\ caps MI A = lib_caps /\ bigcap MI A = LIB_BIGCAP
        /\ (forall a, owned MI A a -> in_ranges (ly_img L) a -> mng_static a) /\ TIGHT A /\ FRESH44 A.

  Definition ainv0_frameG : Prop :=
    forall A M M' mo mo', AINV0 A M mo ->
      (forall a : word, owned MI A (bv_unsigned a) -> M' a = M a) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> AINV0 A M' mo'.

  Definition ainv0_ownedG : Prop :=
    forall A M mo a, AINV0 A M mo -> owned MI A a -> ~ in_ranges (ly_img L) a -> 0 < a < alloc_ceiling.

  Definition free_TG : Prop :=
    forall (fx : FPState) (A : AS MI) R M mo (p n sp ret : Z) (K : TSet),
      ainv MI A M mo -> TIGHT A -> mstd mo -> img_ro_clear L M ->
      call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
      (p = 0 /\ n = 0 \/ In (p, n) (live MI A)) ->
      alloc_ceiling + MALLOC_STACK MI <= sp ->
      stack_room SEGS M sp (MALLOC_STACK MI) ->
      (forall a, zwin (sp - MALLOC_STACK MI) sp a -> ~ owned MI A a) ->
      (forall A' R' M' mo', ainv MI A' M' mo' -> TIGHT A' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
          kept R R' -> live_del p (live MI A) (live MI A') -> caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
          (forall a, owned MI A' a -> owned MI A a \/ (p <= a < p + n)) ->
          frame_eq (fun a => owned MI A a \/ (p <= a < p + n) \/ zwin (sp - MALLOC_STACK MI) sp a \/ errno_win L a) M M' ->
          (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win L (bv_unsigned a)) ->
          srealizes SEGS (cfg fx R' ret M' mo') K) ->
      srealizes SEGS (cfg fx R (ly_free L) M mo) K.

  Definition malloc_TG : Prop :=
    forall (fx : FPState) (A : AS MI) R M mo (n sp ret : Z) (Ksucc : TSet),
      ainv MI A M mo -> TIGHT A -> (BIG MI <= n \/ (n = 65536 /\ FRESH44 A)) ->
      mstd mo -> img_ro_clear L M ->
      call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 n -> 0 <= n <= NMAX MI ->
      alloc_ceiling + MALLOC_STACK MI <= sp ->
      stack_room SEGS M sp (MALLOC_STACK MI) ->
      (forall a, zwin (sp - MALLOC_STACK MI) sp a -> ~ owned MI A a) ->
      room_for MI A n ->
      (forall A' R' M' mo' (p : Z),
          ainv MI A' M' mo' -> TIGHT A' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
          kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
          live_add p n (live MI A) (live MI A') -> caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
          (forall a, owned MI A' a -> owned MI A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
          frame_eq (fun a => owned MI A' a \/ (p <= a < p + n) \/ zwin (sp - MALLOC_STACK MI) sp a \/ errno_win L a) M M' ->
          (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
          srealizes SEGS (cfg fx R' ret M' mo') Ksucc) ->
      srealizes SEGS (cfg fx R (ly_malloc L) M mo) Ksucc.

  Definition malloc_firstG : Prop :=
    forall (fx : FPState) (A : AS MI) R M mo (n sp ret : Z) (Ksucc : TSet),
      AINV0 A M mo -> drv_auxv M sp -> TIGHT A -> n = 65536 -> FRESH44 A ->
      live MI A = [] ->
      mstd mo -> img_ro_clear L M ->
      call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 n ->
      alloc_ceiling + MALLOC_STACK MI <= sp ->
      stack_room SEGS M sp (MALLOC_STACK MI) ->
      (forall a, zwin (sp - MALLOC_STACK MI) sp a -> ~ owned MI A a) ->
      (forall A' R' M' mo' (p : Z),
          ainv MI A' M' mo' -> TIGHT A' -> mstd mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
          kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
          live_add p n (live MI A) (live MI A') -> caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
          (forall a, owned MI A' a -> owned MI A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
          frame_eq (fun a => owned MI A' a \/ (p <= a < p + n) \/ zwin (sp - MALLOC_STACK MI) sp a \/ errno_win L a) M M' ->
          (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
          srealizes SEGS (cfg fx R' ret M' mo') Ksucc) ->
      srealizes SEGS (cfg fx R (ly_malloc L) M mo) Ksucc.

  Record mi_constsG : Prop := MI_CONSTSG {
    mcg_stack : MALLOC_STACK MI = 8192;
    mcg_big   : BIG MI = 131052;
    mcg_nmax  : NMAX MI = 2 ^ 28;
    mcg_round : forall n, 0 <= n -> n <= round_big MI n <= n + 4116;
    mcg_guard : In (0x120928, map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 rr_canary))) (static_cells MI);
    mcg_nlock : In (0x12094b, [0]) (static_cells MI);
    mcg_pgsz  : In (0x120978, [0; 16; 0; 0; 0; 0; 0; 0]) (static_cells MI)
  }.

  Lemma mcg_guard_cell : mi_constsG -> forall A M mo, ainv MI A M mo -> cell M 0x120928 8 rr_canary.
Proof.
ltac2:(KReplay.run1 (kr_t_DrvMallocT ()) ["G"] "h01Hh11lh21xh31Ah42AIh51Ch61Mh71bh82moh91np;4p;7p;1p;2p;;p;3p;6g0000R0p4p710g000KR1p4p710R2p8g000gR3p4p73110P2p8g001Cj4OTg0023j7NTg002ej15Tg003Jj14Tg003oj1ITg004Mj1:Tg004kj1BTg005Nj1@j2ATg0068j12Tg006Wj1>Tg007Oj29j1CTg0085j2<Tg009=j48Tg009Yj1MTg00:Vl;LTg00;Sj1HTg00<3j1ETg00<Uj2;Tg00=5j26Tg00=Wj30TP3j6DTP1j67Tg00>1j2FTg00>cj6GTP0j2?Tg00??j4JTg00?^j4KTg00@Sj4=Tf0R0#4#4p=1g00ADR1f2R3f1R2P0C=p=3g00C9p,2ACR4P1g00D9R5p,2MIR6COg00Dhg00EYP4P1P5P6P3P2P0FNP4P1P5P6f3R6P3P2g00FOR2#1#5#4#1#1#5#1#5#1#5#4#5#4#1#IR5%42#1R2#:R1#BR4g00G4R7%@1R8g00GR#2#2#2#2#2#2#2#2R9%42#1#:R2p,4RRND#>R:'9'<R;C8R<P0f4R=#MM;L%H4R>#ER?1925R21;7<R@533P7P4%C1RAP<C8R<,6>30P>P<A3=2@R=16>0R<50?X1>P0P4P41A10,91X24RBP;C8RCP4P7P4P8PAP;EDE7A362@16>C50?P>PCf5?32@RC=0?<X1>P0P4P4P0X24R6P;C8RAP4P4PBP61F10X74P;EGE716>A90?=P>PAf6RA?32@=0?<X1>P0P;1?4;E716>;R>90?Cg00H1RCP@f7?320=0?>X9CP01;4;RCP4P7P8P;CJE7A3A2C=0?>P0b0b0b0b0b0P3P5P9P:CKeW4W8W6W3W5o"). Qed.

  Record drv_mallocT : Prop := DRV_MALLOCT {
    dm_consts : mi_constsG;
    dm_init   : ainv_initG;
    dm_frame0 : ainv0_frameG;
    dm_owned0 : ainv0_ownedG;
    dm_first  : malloc_firstG;
    dm_malloc : malloc_TG;
    dm_free   : free_TG
  }.
End G.
