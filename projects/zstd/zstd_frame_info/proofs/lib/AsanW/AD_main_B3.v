(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A AD_main_B1 AD_main_B2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).




Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma shiftr26_zero_iff : forall a, 0 <= a -> (Z.shiftr a 26 = 0 <-> a < 67108864).
Proof.
  intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0050=11305535983.418930777879.518932961611.659314825068.665031309085.300000600700800=00>S2Ha1HSSS1H1MS".
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma is_primary_big : forall n, 65536 <= n -> AsanCtrl.is_primary n = false.
Proof.
  intros n Hn. unfold AsanCtrl.is_primary, AsanCtrl.needed0, AsanCtrl.rounded_size, AsanCtrl.rz_size, AsanCtrl.rz_log, AsanCtrl.rup, AsanCtrl.K_MAX_SIZE.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0=2484822568.3 31130073652.332490755378.336000985010.34354944178.3 52673924530.357455143858.360090944434.362248010674.39880878002.3 00000400500900=00A00E00I00M00Q00US2HnFS2HnS2HnS2HnS2HnS2HnS2HnS2HnS2Hn".
repeat (replace (n <=? _) with false by (symmetry; apply Z.leb_gt; lia)).
  change (Z.shiftl 16 7) with 2048. apply Z.leb_gt.
  rewrite Z.max_l by lia. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma implMA_bind_assoc : forall {X Y W} RNG (ma : @Monad.M APS X) (g : X -> @Monad.M APS Y) (f : Y -> @Monad.M APS W) s Q ms,
  implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms -> implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms.
Proof.
  intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
  apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
  intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
Qed.

(* [comment removed for export] *)
Section B3.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -128 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).
  (* [comment removed for export] *)
  Variable J8 : list byte.
  Notation ABASE' := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK canary).
  Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  (* [comment removed for export] *)
  Hypothesis UM_e48 : In [AMALLOC_PC; 0x7f7e4] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0x7f838] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0x7f85c] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0x7f98c] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0x7fac4] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0x7fb58] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).
  Notation BUF' := (BUF AI L).
  Notation RDINV' := (RDINV AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation RDBRK' := (RDBRK AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Notation POSTBODY' := (POSTBODY AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L argv P0 P1 slack0 slack1 RA0 RA1 J8).
  Hypothesis ARGC2 : argc = 2.

  (* [comment removed for export] *)
  #[using="USP16 USPLO USPHI BOT argv geoA'"] Lemma dpost_block_cells : forall LB m m' p A n cs,
    aheap_pres CI LB (usp + -128) m m' -> astk_shadow_pres (usp + -128) m m' -> In (HB p A n) LB ->
    rw_cells asegs m A cs -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs m' A cs.
  Proof.
    intros LB m m' p A n cs HP HS HIN RW SZ. eapply rw_cells_magree; [eapply magree_of_dpost; [exact HP| exact HS]| exact RW|].
    intros a Ha. left. right; right; left. exists (HB p A n). Local Ltac2 Set LiaHints.tbl := fun () => "0010>31223313840.7400000=S3BOT2SZ2Ha1H".
split; [exact HIN| cbn; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  (* [comment removed for export] *)
  #[using="DRV_CI"] Lemma dpost_stage : forall LB m m' sj,
    aheap_pres CI LB (usp + -128) m m' -> astk_shadow_pres (usp + -128) m m' -> STAGE m sj -> STAGE m' sj.
  Proof.
    intros LB m m' sj HP HS SJ. unfold STAGE in SJ. unfold STAGE.
    eapply rw_cells_magree; [eapply magree_of_dpost; [exact HP| exact HS]| exact SJ|].
    intros a Ha. left. right; left. exists (0x5c34c0, 0x5d3500). split; [apply DRV_CI; unfold drv_img_ranges; cbn; repeat (first [left; reflexivity | right])|].
    cbn in Ha. unfold ASTAGE in Ha. cbn [fst snd]. clear - Ha. pose proof ASTAGE_LEN_Z as STGZ. Local Ltac2 Set LiaHints.tbl := fun () => "0010=31651059977.3000009S2Ha4STGZ".
Stdlib.micromega.Lia.lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition after_test (fd : Z) (st : rd_st) : @Monad.M APS (rd_st + rd_result) :=
    g <- (if MAX_INPUT <=? rd_cap st then io_diag ioS DTooBig ;;; mret None
          else nb <- amalloc_M (rd_cap st * 2) ;;
               match nb with
               | None => io_diag ioS DOom ;;; mret None
               | Some nb' => afree_M (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
               end) ;;
    match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd ASTAGE cnt) (dec_read ASTAGE cnt) ;;
         match a with
         | RdErr _ => io_diag ioS (DReadError arg1) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end.

  (* [comment removed for export] *)
  #[using="RSTK_lo RSTK_hi USP16 USPLO USPHI DRV_CI HT BOT ASHENV HSTRN geoA' ARGC2"] Lemma rd_nogrow : forall (fd : Z) (st : rd_st) (s : APS) RNG x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : amem) (A : Z) (DATA junk sj : list byte),
    3 <= fd < 2^32 ->
    rd_content st = map bv_unsigned DATA -> BUF' mm s RNG (rd_buf st) A (rd_cap st) DATA junk -> STAGE mm sj -> Z.of_nat (length DATA) < rd_cap st ->
    ABASE' stdout_init mm -> AARGV' mm -> RNGS' RNG -> frm0 fc ->
    implMA RNG (rd_read_part fd arg1 st) s (POSTBODY' fd)
      (GST 0x7f81c x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 (zlength (rd_content st))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 ASTAGE) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm).
  Proof.
    intros until sj. intros FD HC BU SJ LT BA ARG RG FRM.
    pose proof BA as (_ & MI & _).
    apply implMA_from_evtF. zstep. zstep. apply evtF_done.
    Local Ltac2 Set LiaHints.tbl := fun () => "00;0>17794525788.9819186184958.9821309524942.9827002495482.9829673881651.9837426498562.9845264780135.9859392662801.9863329107040.9867748317801.9868277396194.9800000900=00>00E00I00J00S00T00[00h00mS7RSTK_hiS2LTFS5USPLOS2HTFS7RSTK_loFS5USPHIS5USP163BOT1HS3BOT".
eapply rd_read; first [exact ARGC2 | exact FD | exact HC | exact BU | exact SJ | exact BA | exact ARG | exact RG | exact FRM | lia | eassumption].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs_mono RSTK_lo RSTK_hi RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI HT BOT DMALLOC DFREE ASHENV HSTRN geoA' UM_e9c UF_ec0 UM0 UF0 ARGC2"] Lemma rd_grow : forall (fd : Z) (st : rd_st) (s : APS) RNG x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : amem) (A : Z) (DATA junk sj : list byte),
    3 <= fd < 2^32 ->
    rd_content st = map bv_unsigned DATA -> BUF' mm s RNG (rd_buf st) A (rd_cap st) DATA junk -> STAGE mm sj -> Z.of_nat (length DATA) = rd_cap st ->
    ABASE' stdout_init mm -> AARGV' mm -> RNGS' RNG -> frm0 fc ->
    implMA RNG (after_test fd st) s (POSTBODY' fd)
      (GST 0x7f824 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 (zlength (rd_content st))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 ASTAGE) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm).
  Proof.
    intros until sj. intros FD HC BU SJ K00 BA ARG RG FRM.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *. atop_facts.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0h & SO0 & RK & HA & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR & RGA & RGAS). unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & [errv ERR] & SOF). unfold AMFRAME in FR. rewrite errno_addr_ATP in ERR.
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & RGa0 & RRa0 & RG1).
    pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
    pose proof ASTAGE_LEN_Z as STGZ. pose proof SJ as SJ0. unfold STAGE, ASTAGE in SJ.
    rewrite LENZ. unfold after_test.
    apply implMA_from_evtF.
    Local Ltac2 Set LiaHints.tbl := fun () => "02U0?10607278173.33610617847967.20110707187043.24610717554743.25410717554871.26210717947959.26410719592881.15410719710504.1551079841822.289 11087775529.15512712817566.28813441275451.2751351869856.267 14645002939.2461473318365.275 15338302364.27516075584200.22616075584458.15416083456451.16216083456461.16216088012821.27516088085075.29516695035536.18116697361805.15516746639024.27516757156969.26617287020696.15517289234853.30017841986114.27518169629689.3341845742078.275 18657190153.27518834773242.30019659284528.30019661726391.32520889489715.15520904122382.30020912835713.30021078793969.33521693040241.27521693377591.29521706042413.22622034872381.15522037311744.3002351573387.275 24499555748.30024506156185.15524556702716.15524933770943.26625075764918.28625075764918.28725075764918.28825567288002.3002563677443.288 25690453695.15525696599938.30025730265771.28526922745722.28527116424168.30027122729685.15527433677254.25427510397339.27527644371777.15528306620142.26628818342369.2752885965632.300 28890522000.28528890713046.27528905345114.2672900598397.155 29106819816.27530665476638.28930672425959.26730683023467.27530683357741.2853224192851.300 33021635930.1553370034632.246 3374513468.155 34142630324.33434157230131.33534696248305.15534710581964.30035268731712.27535308732952.3343580950330.335 36133447983.27537143477278.28937703826287.27537710084534.26638635681839.15538902798750.28939394884449.27539898093265.30040871980593.30040882874124.15541418087371.33443189686586.15543201768511.27543909580169.28643909580169.28743993632135.15544053177505.1  45122803018.26646164448178.27546221827503.24646507703259.15546522495718.30047593260143.19348034948147.28948221936022.15548294005567.33448728312165.33550320688888.28950494439974.15550760795626.27550983745419.27551611281456.15551792496826.33451806994749.33553199769566.28954047614024.27554196435355.22554319842229.15555083553950.28955181160242.19455198330301.26655500981329.27556434502525.28856829351892.30056829363977.27556829439311.29556831628627.32556833564148.18156835759849.1555699165000.300 57626599513.29558477110430.28959308628304.22659308628433.22659579458053.15759815210681.29062411522989.26762431962834.2  62775395401.26763211114414.32863631210689.27563755559215.26765031319246.33565031368398.15465895396557.27565921868235.25465962335170.2886632962320.275 66395352041.2546751638716.335 6753752705.155 6753819963.334 67700414597.2758458694576.300 8468997773.155 9373243880.275 9538480250.335 9936876884.275 9941179535.290 00001301J01S01`02102B02G02L02n02o04205005E05R05c06406W07807Y08908h09W09\09a0:60:K0:L0:M0:^0;30;D0;Y0;j0<;0<L0<Q0<b0<c0=40=k0>b0?E0?J0?[0@^0B40BI0BJ0B_0B`0Ba0Cc0Cd0DV0D[0Dl0E=0EN0EO0EP0Ea0F60FL0Fa0GX0GY0H\0I_0Jb0Jc0K40KV0Kg0L80LI0LJ0Lc0MQ0MR0NU0OX0Oc0P:0PO0P`0Q50Qd0RF0RW0Rh0SC0Se0T:0T;0TY0Tk0U<0U=0UR0US0UT0UY0UZ0W40WE0WR0WS0WT0Wj0Wk0Wl0Wm0Y50Y60Y?0Z50ZJ0ZR0Zg0[<0[^0\`0]?0]D0]f0^50^K0^`0^a0_E0_i0`M0a10aI0aa0b20c40cV0cf0dH0dM0dj0e?0e@0fZ0g]0hP0he0i60i;0j50k00kA0lD0lU0lf0lk0m<0mM0m^0mc0o:0oK10N11PS3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT2G21H4CAPR3K0'3BL2S3BL23BM2S3BL23BM23Ha5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL2S3BL2S3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5FS3BOT3K002G21H3K0'3BL13BL24STGZ3BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT3K002G21H3K0'3BL13BL23LTM3BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BL23BM13BM23Ha53Hb5S3BL23BM23Aa3S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BOT3K002G22G43K0'3BL23BM13BM23BM3S3BOT3K002G24CAPR3K0'3BL13BL23BL3S3BOT3K002G24CAPR3K0'3BL13BL23BL3S3BOT3K002G23K0'3BL13BL23BL33LTMS3BOT3K002G22G43K0'3BL23BM13BM23BM33Ab43Ha53Hb5S3BOT3K002G22G43K0'3BL23BM13BM23BM33Ab43Ha53Hb5S3BL2S3BL2S3K003BL23BM23Ha53Hb5S3K003BL23BM23Ha53Hb5FFS3BL23BM23Ha53Hb5S3BL23LTM3BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha33Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL2S3BL23BM23Ha53Hb5FS3BL23BM23Ha53Hb5S3BOT3K002G22G43K0'3BL23BQ23BM13BM23BM33Ab43Ha53Hb23Hb5S3BOT3K002G22G43K0'3BL23BQ23BM13BM23BM33Ab43Ha53Hb23Hb5S3BOT2G22G43K0'3BL23BQ23BM13BM23BM3S3BL2S3BL23BM23Ha53Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT3K002G22G51H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S3BOT2G22G51H3K0'3BL2FS3BL13BL23BM23Ha53Hb5FFS3BOT3K002G21H3K0'3BL13BL23BQ23BM13BM23BM33Aa43Ab43Ha23Ha53Hb23Hb5FS3BOT3K002G21H3K0'3BL23BQ23BM23BM33Ab43Ha53Hb23Hb5S3BL2S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5FFS3BL23BM23Ab33Ha5S3BL23BM23Ha53Hb13Hb5S3BOT3K002G21H3K0'3BL2S3BL23BL43BM23Ha53Hb5S3BOT3K002G22G43K0'3BL13BL23BL33BQ23BM23Aa43Ha23Ha53Hb5FS3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5FS3BL23BM23Ha53Hb5S3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5FS3BOT3K002G21H3K0'3BL22L'S3BOT3K002G21H3K0'3BL13BL23BQ23BM13BM23Aa43Ab4FS3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S5USPHI3BL2S5USPHI3BL23BM23Ha53Hb5S3K003BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3K0'3BL23BM23Ha53Hb5S3BOT3K002G22G43K0'3BL23BL33BM23Ha53Ha63Hb53Pa6S3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BOT2G21H4CAPR3K0'3BL23LTMS3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5S3BL23BM23Ha53Hb23Hb5FS3BOT2G21H3K0'3BL23BM23Ha53Hb5S3BOT2G21H3K0'3BL2S3BL23BM23Ha53Hb5FS3BL23BM23Ha13Ha53Hb5FFS3BL2SS3BOT3K002G22G51H4CAPR3K0'3BR43BL13BL23BQ23BM13BM23Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S3BL23BM23Ha53Hb5S3BL13BL23BM2FFS3BOT3K002G21H3K0'3BL2FFFS3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb54CAP2FS3BL23LTMS3BOT3K002G21H3K0'3BL23BQ23BM13BM23Ab43Ha53Hb23Hb43Hb5S3BL23BM23Ha53Hb33Hb5S3BL22GES3K0'3BL23BM23Ha53Hb5S3K0'3BL23BM23Ha53Hb5S3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5S3BOT3K002G21H3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha43Ha53Hb23Hb5S3BOT3K002G21H4CAPR3K0'3BL23BM2S3BL2S3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5S2G43K0'3BL22HaS4CAPR3BL23BM23Ha53Hb5S3BL23BM23Ha23Ha53Hb5FS5USPHI3BOT2G21H3K0'3BL23BM23Ha53Hb5S5USPHI3BOT2G21H3K0'3BL23BM23Ha53Hb5S5USPHI3BOT2G21H3K0'3BL23BM23Ha53Hb5S5USPHI3BOT2G21H3K0'3BL23BM23Ha53Hb5S5USPHI3BOT2G21H3K0'3BL2S5USPHI3BOT2G21H3K0'3BL2S3BL23BM23Ha53Hb5S3BOT3K002G21H3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb53Ha'S3BOT2G21H3K0'3BL23BM13BM23Ha53Hb5S3BL23BM13BM22K1S3BOT3K002G21H4CAPR3K0'3BL23BM22K2S3BL2S5USPLO5USPHI3BL23BM23Ha53Hb5S3BL23BM23BM43Ha53Hb5SS3BOT3K002G22G51H4CAPR3K0'3BL13BL23BQ23BQ43BM13BM23Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3BOT3K002G22G43K0'3BL23BQ23BM23BM33Ha53Hb53Hb63Pb6S3BL23BQ23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL2S3BOT3K002G21H3K0'3BL23BL33BQ23BM13BM23Aa43Ha23Ha53Hb23Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha5S3BL23BM23Ha53Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM23BM33Aa43Ab43Ha23Ha53Hb23Hb5S3BL23BM13BM23Ha5S3BL23BM23Ha53Hb5S3BL2S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL23BM23Ha53Hb5S3BL2S3BOT3K002G22G51H4CAPR3K0'3BL13BL23BQ23BM24DISJ3Aa23Aa43Ab23Ab43Ha23Ha43Ha53Hb23Hb43Hb5S3BL23BM23Ha53Hb5S3BOT3K002G21H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb5S3K001H4CAPR3K0'3BL13BL23BQ23BM13BM23Aa43Ab43Ha23Ha53Hb23Hb52Y12Y4".
zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (GE : 67108864 <= rd_cap st).
      { destruct (Z.lt_ge_cases (rd_cap st) 67108864) as [L'|G]; [| exact G]. exfalso. apply K0.
        apply (proj2 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). lia. }
      replace (MAX_INPUT <=? rd_cap st) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      destruct (drv_got_of_aheap AI _ _ _ _ _ P0h) as (GSE & PSE & _). unfold AGOT_STDERRP, ASTDERRP in GSE, PSE.
      zstep. zstep. zstep. zstep. zstep. zstep. apply evtF_done.
      apply implMA_bind_assoc. cbn [io_diag ioA io_S].
      eapply afprintf_exit with (LB := [HB (rd_buf st) A (rd_cap st)]) (d := DTooBig);
        lazymatch goal with
        | |- adiag_args _ _ _ _ _ _ _ => cbn [adiag_args]; split; [reflexivity|]; rewrite unsigned_lit by lia; reflexivity
        | |- forall ms'', aat_exit _ _ _ ms'' -> _ => intros ms'' AE; apply implMA_mret_bind; cbv beta iota; apply implMA_ret; apply evtF_done; exact AE
        | |- _ => eassumption
        end. }
    (* [comment removed for export] *)
    assert (LTM : rd_cap st < 67108864).
    { rewrite <- K00. apply (proj1 (shiftr26_zero_iff (Z.of_nat (length DATA)) ltac:(lia))). exact K0. }
    replace (MAX_INPUT <=? rd_cap st) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
    zstep. zstep. zstep. apply evtF_done.
    apply implMA_bind_assoc.
    replace (Z.shiftl (Z.of_nat (length DATA)) 1) with (rd_cap st * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    eapply implMA_bind.
    { eapply (dmalloc_M AI DMALLOC L RNG) with (lo := LO); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
        first [ exact P0h | exact MI | exact ST | exact BOT | unfold AMALLOC_STACK; lia | unfold AREQMAX; lia | exact UM_e9c | exact UM0 | exact RGtop | exact RK | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AMALLOC_PC; lia. }
    cbv beta. intros r s1 RNG1 ms1 [SOE PO].
    destruct PO as (LE1 & u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MI1 & ST1 & HPR & HSP & RR).
    rewrite ?(unsigned_lit (usp + -128)) in ST1, HPR, HSP by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in RR.
    assert (RG1' : RNGS' RNG1) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE1| exact RG]).
    pose proof RG1' as (RGstk1 & RGtop1 & RGimg1 & RGimsh1 & RGfs1 & RRS1 & RRF1 & RRB1 & RG01 & _).
    assert (ARG1m : AARGV' m1) by (eapply (AARGV_after_dpost AI usp USP16 USPLO USPHI); [exact HPR| exact HSP| exact ARG]).
    assert (FR1 : AMFRAME' m1).
    { unfold AMFRAME. eapply rw_cells_magree; [eapply magree_of_dpost; [exact HPR| exact HSP]| exact FR|]. intros a Ha. left. left. cbn in Ha. lia. }
    assert (BLK1 : rw_cells asegs m1 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st - Z.of_nat (length DATA))) junk]).
    { eapply dpost_block_cells; [exact HPR| exact HSP| left; reflexivity| exact BLK| cbn; lia]. }
    assert (SJ1 : STAGE m1 sj) by (eapply dpost_stage; [exact HPR| exact HSP| exact SJ0]).
    clear SJ. pose proof SJ1 as SJ1u. unfold STAGE, ASTAGE in SJ1u.
    destruct r as [nb|].
    2:{ (* [comment removed for export] *)
        destruct RR. }
    destruct RR as (A' & junk' & -> & BR' & HEAP1 & NBLK & RGN & RGNS & HEXP).
    specialize (HEXP (is_primary_big (rd_cap st * 2) ltac:(lia))).
    assert (BA1 : ABASE' stdout_init m1).
    { eapply (ABASE_after_dpost AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI canary);
        [exact HPR| exact HSP| exact HEAP1| exact MI1| exact ST1| exact BA]. }
    pose proof BR' as (BQ1 & BQ2 & BQ3 & BQ4). pose proof (ablk_lin _ _ BQ1) as (BM1 & BM2 & BM3 & BM4). unfold AIMG_HI in BM1.
    pose proof (AI_hb_ids AI _ _ _ _ _ HEAP1) as ND.
    assert (DISJ : A' + rd_cap st * 2 <= A \/ A + rd_cap st <= A').
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB nb A' (rd_cap st * 2)) (HB (rd_buf st) A (rd_cap st)) HEAP1 ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
      cbn [ab_addr ab_size] in D. apply D. intros E. injection E. intros _ _ Eid.
      unfold hb_ids in ND. cbn [flat_map ab_kind] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI. rewrite Eid. left. reflexivity. }
    apply implMA_bind_assoc.
    pose proof BA1 as (ST1' & _ & _ & AS1 & SE1 & GU1 & TR1 & HI1 & ROD1 & RCS1 & RCB1 & RSG1 & [errv1 ERR1] & SOF1). rewrite errno_addr_ATP in ERR1.
    apply implMA_from_evtF. zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
    zstep. zstep. if_cases K2; zify_cond K2; try (exfalso; lia). clear K2.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep.
    apply (rw_cells_split_CB _ _ _ [] _ _ [] [length DATA; Z.to_nat (rd_cap st * 2) - length DATA]%nat) in NBLK; [| cbn; lia]. cbn [mk_CB_cells app] in NBLK.
    apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) (firstn (length DATA) junk')] _)) in NBLK. destruct NBLK as [NB1 NB2]. cbn [cells_size csize Nat.add] in NB2.
    pose proof BLK1 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in SRC. destruct SRC as [SRC _].
    pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB. clear SRC.
    (* [comment removed for export] *)
    pose proof (AI_block AI _ _ _ _ _ (rd_buf st) A (rd_cap st) HEAP1 ltac:(right; left; reflexivity)) as (_ & _ & RGA1 & _ & SHA1 & _ & _ & (RLOa & RHIa & Aa1 & Aa2 & Aa3 & Aa4 & ARRa & ARWa)).
    pose proof (AI_block AI _ _ _ _ _ nb A' (rd_cap st * 2) HEAP1 ltac:(left; reflexivity)) as (_ & _ & _ & _ & SHN1 & _ & _ & (RLOb & RHIb & Ab1 & Ab2 & Ab3 & Ab4 & ARRb & ARWb)).
    pose proof (block_hull RNG1 m1 A (Z.of_nat (length DATA)) RLOa RHIa ltac:(lia) Aa1 Aa2 ltac:(lia) ltac:(lia) ltac:(lia) ARRa ARWa) as (HRa & HWa & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6).
    pose proof (block_hull RNG1 m1 A' (Z.of_nat (length DATA)) RLOb RHIb ltac:(lia) Ab1 Ab2 ltac:(lia) ltac:(lia) ltac:(lia) ARRb ARWb) as (HRb & HWb & Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
    pose proof (hull_props A (Z.of_nat (length DATA)) ltac:(lia)) as (_ & _ & _ & _ & Pa5 & Pa6). pose proof (hull_props A' (Z.of_nat (length DATA)) ltac:(lia)) as (_ & _ & _ & _ & Pb5 & Pb6).
    assert (UPa : unpoisoned m1 A (A + Z.of_nat (length DATA))).
    { eapply unpoisoned_sub; [apply (ablock_unpoisoned m1 A (rd_cap st) SHA1); first [lia | clear -BR4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | lia | lia]. }
    assert (UPb : unpoisoned m1 A' (A' + Z.of_nat (length DATA))).
    { eapply unpoisoned_sub; [apply (ablock_unpoisoned m1 A' (rd_cap st * 2) SHN1); first [lia | clear -BQ4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia] | lia | lia]. }
    pose proof (ASHENV _ _ _ _ _ HEAP1) as ENV1. pose proof ENV1 as (Rgot & Rric & Rshb & Rini & Rlay & Rmem & _).
    eapply evtF_cut.
    { eapply (memcpy_i_spec RNG1) with (lo := LO) (src := DATA) (junk := firstn (length DATA) junk')
                                        (RLO1 := hull_lo A) (RHI1 := hull_hi A (Z.of_nat (length DATA))) (RLO2 := hull_lo A') (RHI2 := hull_hi A' (Z.of_nat (length DATA)));
        rewrite ?unsigned_lit by lia;
        lazymatch goal with
        | |- mem_inv _ _ => exact MI1
        | |- stk _ _ _ _ => exact ST1
        | |- bytes_at _ _ _ _ => exact SRCB
        | |- rw_cells _ _ _ [CB _ _] => replace (Z.to_nat (Z.of_nat (length DATA))) with (length DATA) by lia; exact NB1
        | |- rw_cells _ _ _ _ => assumption
        | |- length _ = _ => lia
        | |- app_blk A _ => eapply ablk_app_blk; [eapply ablk_sub; [exact BR1| lia| lia]| lia]
        | |- app_blk A' _ => eapply ablk_app_blk; [eapply ablk_sub; [exact BQ1| lia| lia]| lia]
        | |- app_blk _ _ => unfold app_blk, KLOW, KHIGH, KEND in *; lia
        | |- unpoisoned _ _ _ => assumption
        | |- wr_at _ _ _ _ => assumption
        | |- rng_aimg _ => exact RGimg1
        | |- rng _ (shad _) _ => assumption
        | |- rng _ LO _ => eapply rng_sub'; [exact RGstk1| lia]
        | |- rng _ A _ => eapply rng_sub'; [exact RGA1| lia]
        | |- rng _ A' _ => eapply rng_sub'; [exact RGN| lia]
        | |- _ /\ _ => unfold KEND in *; repeat match goal with |- _ /\ _ => split end; lia
        | |- _ => unfold KHIGH in *; lia
        end. }
    cbv beta. intros ms2 PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & ST2 & NB1' & _).
    rewrite !(unsigned_lit A') in MUc, NB1' by lia. rewrite !(unsigned_lit (Z.of_nat (length DATA))) in MUc, NB1' by lia. rewrite ?(unsigned_lit (usp + -128)) in MUc, ST2 by lia.
    clear BLK1 SRCB ARWa ARWb HWa HWb.   (* [comment removed for export] *)
    transport_after_call asegs m1 m2 MUc WMc.
    fix_ret.
    assert (WOKW : Forall (WOK usp) [(usp + -128 - 2240, usp + -128); (A', A' + Z.of_nat (length DATA))]).
    { unfold WOK, WOKb, ALO. constructor; [cbn [fst snd]; lia| constructor; [| constructor]].
      cbn [fst snd]. right; right; right; left. eapply ablk_sub; [exact BQ1| lia| lia]. }
    assert (P2 : AHEAP AI L RNG1 (aps_m s1) [HB nb A' (rd_cap st * 2); HB (rd_buf st) A (rd_cap st)] m2).
    { eapply (AI_frame AI); [exact HEAP1| exact MUc| exact WMc|].
      pose proof (AI_layout AI _ _ _ _ _ HEAP1) as (Y1 & Y2 & Y3 & Y4 & _). unfold ALO in *.
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - left. left. lia.
      - right; left. exists (HB nb A' (rd_cap st * 2)). split; [left; reflexivity| cbn; lia]. }
    assert (BA2 : ABASE' stdout_init m2).
    { eapply (ABASE_munch usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK USP16 USPLO USPHI canary); [exact BA1| exact WOKW| exact MUc| exact WMc| exact MI2| exact ST2| |].
      - destruct SE1 as (flags & mode & ee & wend & tail & Hc & HRR). exists flags, mode, ee, wend, tail. split; [| exact HRR].
        eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact Hc|]. intros a' Ha'. cbn in Ha' |- *. lia.
      - exists errv1. rewrite errno_addr_ATP.
        first [ exact ERR1 | eapply rw_cells_magree; [eapply magree_of_munch; [exact MUc| exact WMc]| exact ERR1|]; intros a' Ha'; cbn in Ha' |- *; lia ]. }
    assert (ARG2m : AARGV' m2) by (eapply (AARGV_munch usp USP16 USPLO USPHI argv P0 P1 slack0 slack1 RA0 RA1 (usp + -128)); [lia| exact WOKW| exact MUc| exact WMc| exact ARG1m]).
    clear MUc WMc WOKW.
    pose proof BA2 as (ST2' & _ & FR2 & AS2 & SE2 & GU2 & TR2 & HI2 & ROD2 & RCS2 & RCB2 & RSG2 & [errv2 ERR2] & SOF2). unfold AMFRAME in FR2. rewrite errno_addr_ATP in ERR2.
    (* [comment removed for export] *)
    zstep. zstep. apply evtF_done.
    eapply implMA_bind.
    { eapply (dfree_M AI DFREE L RNG1) with (lo := LO) (p := rd_buf st) (A := A) (n := rd_cap st); try reflexivity; rewrite ?(unsigned_lit (usp + -128)) by lia;
        first [ exact P2 | right; left; reflexivity | exact MI2 | exact ST2 | exact BOT | unfold AFREE_STACK; lia | exact UF_ec0 | exact UF0 | exact RGtop1 | match goal with Hr : rng ?R ?l _ |- rng ?R ?l _ => eapply (rng_sub _ _ _ _ _ Hr); lia end | eapply aps_ok_rest; [exact SOE| exact RK] | idtac ].
      all: rewrite ?unsigned_lit by lia; unfold AFREE_PC; lia. }
    cbv beta. intros [] s2 RNG2 ms3 [SOE3 PO].
    destruct PO as (LE2 & w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & HPR3 & HSP3 & HEAP3).
    rewrite ?(unsigned_lit (usp + -128)) in ST3, HPR3, HSP3 by lia.
    fix_ret. cbn [aps_m aset_m fst snd] in HEAP3.
    rewrite (lb_remove_secondA (rd_buf st) A (rd_cap st) (HB nb A' (rd_cap st * 2)) [] ND) in HPR3, HEAP3.
    assert (RG2' : RNGS' RNG2) by (eapply (RNGS_mono rng_fs rng_fs_mono); [exact LE2| exact RG1']).
    assert (BA3 : ABASE' stdout_init m3).
    { eapply (ABASE_after_dpost AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI canary);
        [exact HPR3| exact HSP3| exact HEAP3| exact MI3| exact ST3| exact BA2]. }
    assert (ARG3 : AARGV' m3) by (eapply (AARGV_after_dpost AI usp USP16 USPLO USPHI); [exact HPR3| exact HSP3| exact ARG2m]).
    assert (NB3 : rw_cells asegs m3 A' [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) (firstn (Z.to_nat (rd_cap st * 2) - length DATA)%nat (skipn (length DATA) junk'))]).
    { eapply dpost_block_cells; [exact HPR3| exact HSP3| left; reflexivity| | cbn; lia].
      apply (proj2 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)). split; [replace (length DATA) with (Z.to_nat (Z.of_nat (length DATA))) at 1 by (clear; lia); exact NB1'|].   (* [comment removed for export] *)
      cbn [cells_size csize Nat.add]. replace (Z.to_nat (rd_cap st * 2 - Z.of_nat (length DATA))) with (Z.to_nat (rd_cap st * 2) - length DATA)%nat by (first [clear; lia | lia]). exact NB2. }
    assert (SJ3 : STAGE m3 sj).
    { eapply dpost_stage; [exact HPR3| exact HSP3|]. unfold STAGE, ASTAGE. exact SJ1u. }
    (* [comment removed for export] *)
    pose proof (AI_block AI _ _ _ _ _ nb A' (rd_cap st * 2) HEAP3 ltac:(left; reflexivity)) as (_ & _ & RGN3 & RGNS3 & _ & _ & (ch3 & CH3 & SZ3 & UB3) & _).
    assert (HA3 : A' = aptr_addr_M s2 nb).
    { unfold aptr_addr_M, AsanCtrl.aptr_addr. rewrite CH3. apply UB3. apply is_primary_big. lia. }
    clear HPR3 NB1' NB2.
    (* [comment removed for export] *)
    apply implMA_mret_bind. cbv beta iota.
    rewrite <- LENZ.
    eapply (rd_read AI rng_fs usp TID S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 RSTK canary L) with (st1 := mkRd nb (rd_cap st * 2) (rd_content st)) (s := s2);
      cbn [rd_buf rd_cap rd_content]; first [exact FD | exact HC | exact SJ3 | exact BA3 | exact ARG3 | exact RG2' | exact FRM | eassumption | lia | idtac].
    split; [exact HEAP3|]. split; [rewrite (aps_so_of_rest _ _ SOE3), (aps_so_of_rest _ _ SOE); exact SO0|].
    split; [eapply aps_ok_rest; [exact SOE3|]; eapply aps_ok_rest; [exact SOE| exact RK]|]. split; [exact HA3|]. split; [exact NB3|].
    assert (CAP2 : rd_cap st * 2 <= 67108864).
    { rewrite CAPK in LTM |- *. change 67108864 with (2 ^ 26) in LTM |- *. apply Z.pow_lt_mono_r_iff in LTM; [| lia| lia].
      replace (2 ^ k * 2) with (2 ^ (k + 1)) by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    unfold MAX_INPUT. split; [split; [lia| exists (k + 1); split; [lia| rewrite CAPK, Z.pow_add_r by lia; lia]]|]. split; [lia|].
    split; [exact BR'|]. split; [exact RGN3| exact RGNS3].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rng_fs_mono RSTK_lo RSTK_hi RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI HT BOT DMALLOC DFREE ASHENV HSTRN geoA' UM_e9c UF_ec0 UM0 UF0 ARGC2"] Lemma rd_body : forall (fd : Z) (st : rd_st) (s : APS) RNG ms,
    3 <= fd < 2^32 -> RDINV' fd st s RNG ms ->
    implMA RNG (read_loop_body ioS amalloc_M afree_M ASTAGE fd arg1 st) s (POSTBODY' fd) ms.
  Proof.
    intros fd st s RNG ms FD RI.
    destruct RI as (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & DATA & junk & sj & pc
                    & -> & PCX & HC & BU & SJ & BA & ARG & RG & FRM).
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    assert (LENZ : zlength (rd_content st) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    pose proof BU as (P0h & SO0 & RK & HA & BLK & [CAPR [k [K0' CAPK]]] & LENR & BR & RGA & RGAS). unfold MAX_INPUT in CAPR.
    pose proof BA as (ST & MI & _).
    rewrite read_loop_body_eq. unfold rd_grow_part. rewrite LENZ.
    apply implMA_from_evtF.
    destruct PCX as [[-> ->]|[-> HNIL]].
    - (* [comment removed for export] *)
      zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090?16073487306.11619186184958.11727441129745.11736937412524.11738699712511.11845363628902.11645363628902.11759314873579.11863456396529.11800000?00I00^01501H01N01T01k021S4CAPR3K0'4LENRS4LENR3K00S3BOT2G22G53K0'3K001HS3BOT2G23K0'4LENR3K001HS3BOT2G24CAPR3K0'1HS4CAPRS4CAPRS3BOT2G24CAPR3K0'3K001HS4CAPR".
if_cases K00; zify_cond K00.
      + (* [comment removed for export] *)
        replace (Z.of_nat (length DATA) =? rd_cap st) with true by (symmetry; apply Z.eqb_eq; lia).
        apply evtF_done.
        rewrite <- LENZ. eapply (rd_grow fd st s RNG); rewrite ?LENZ; first [exact FD | exact HC | exact BU | exact SJ | exact BA | exact ARG | exact RG | exact FRM | lia].
      + (* [comment removed for export] *)
        replace (Z.of_nat (length DATA) =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
        apply evtF_done.
        apply implMA_mret_bind. cbv iota beta.
        rewrite <- LENZ. eapply (rd_nogrow fd st s RNG); first [exact FD | exact HC | exact BU | exact SJ | exact BA | exact ARG | exact RG | exact FRM | lia].
    - (* [comment removed for export] *)
      assert (D0 : DATA = []) by (destruct DATA; [reflexivity| rewrite HNIL in HC; discriminate]). subst DATA. cbn [length Z.of_nat] in *. change (Z.of_nat 0) with 0 in *.
      zstep. if_cases K00; zify_cond K00; [| exfalso; rewrite ?unsigned_lit in K00 by lia; lia].
      replace (0 =? rd_cap st) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evtF_done.
      apply implMA_mret_bind. cbv iota beta.
      rewrite <- LENZ. eapply (rd_nogrow fd st s RNG); first [exact FD | exact HC | exact BU | exact SJ | exact BA | exact ARG | exact RG | exact FRM | cbn [length Z.of_nat]; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition POSTLOOP (fd : Z) (r : rd_result) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    match r with
    | RdExit => aat_exit 2 s RNG ms
    | RdDone b c => RDBRK' fd b c s RNG ms
    end.

  #[using="rng_fs_mono RSTK_lo RSTK_hi RSTK_rlo USP16 USPLO USPHI DRV_CI CLI_CI HT BOT DMALLOC DFREE ASHENV HSTRN geoA' UM_e9c UF_ec0 UM0 UF0 ARGC2"] Lemma rd_loop : forall (fuel : nat) (fd : Z) (st : rd_st) (s : APS) RNG ms,
    3 <= fd < 2^32 -> RDINV' fd st s RNG ms ->
    implMA RNG (mloop fuel (read_loop_body ioS amalloc_M afree_M ASTAGE fd arg1) st) s (POSTLOOP fd) ms.
  Proof.
    induction fuel as [|fuel IH]; intros fd st s RNG ms FD RI.
    - cbn [mloop]. apply implMA_unr.
    - apply implMA_loop_S. eapply implMA_mono; [apply rd_body; [exact FD| exact RI]|].
      cbv beta. intros [st'|[|b c]] s' RNG' ms' PO; cbn [POSTBODY POSTLOOP] in PO |- *.
      + apply IH; [exact FD| exact PO].
      + apply evtF_done. exact PO.
      + apply evtF_done. exact PO.
  Qed.
End B3.
End CANSEC1.
