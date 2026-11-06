(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells AProto ABase F_tryinit F_aunwind F_tlsga F_m2s_b.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit FsKit AFake_sm0.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land8191_mod64 : forall x, Z.land (x mod 18446744073709551616) 8191 = Z.land x 8191.
Proof.
  intros x. change 8191 with (Z.ones 13). rewrite !Z.land_ones by lia.
  change 18446744073709551616 with (2^64). rewrite (Z.mod_mod_divide _ (2^64) (2^13)) by (exists (2^51); reflexivity).
  reflexivity.
Qed.

Lemma land8191_bound : forall x, 0 <= Z.land x 8191 < 8192.
Proof. intros x. change 8191 with (Z.ones 13). Local Ltac2 Set LiaHints.tbl := fun () => "0020=18930165734.15692546614.1 000001002SS".
rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma land8191_inj : forall h i j, 0 <= i < 8192 -> 0 <= j < 8192 -> i <> j ->
  Z.land (h + i) 8191 <> Z.land (h + j) 8191.
Proof.
  intros h i j Hi Hj N. change 8191 with (Z.ones 13). Local Ltac2 Set LiaHints.tbl := fun () => "0040=18933043916.936122715842.95691721024.6 59308587280.800000100;00<00BSS2Hi2Hj2HqSS1N2Hq".
rewrite !Z.land_ones by lia. change (2^13) with 8192. intros E.
  assert (E2 : (i - j) mod 8192 = 0).
  { replace (i - j) with ((h + i) - (h + j)) by ring. rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
  apply Z.mod_divide in E2; [| lia]. destruct E2 as [q Hq]. assert (q = 0) by lia. subst q. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma swrap32_small1K : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. change (bv_swrap 32 z) with ((z + 2147483648) mod 4294967296 - 2147483648). Local Ltac2 Set LiaHints.tbl := fun () => "0020=25814551290.255506994229.2000001005SS2Hz".
rewrite Z.mod_small by lia. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section CANSEC1. Context {rc : runConstT}.
Definition ASTKMALLOC1 : Z := 0x3c724.
Definition SM1_LOOP : Z := 0x3c7b8.
Definition SM1_FOUND : Z := 0x3c830.

(* [comment removed for export] *)
Definition sm1_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (shad F, shad F + 16)].

Definition sm1_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h0 h2 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sm1_W (bv_unsigned sp) fs flag F) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fs [C8 h0; C8 (Z_to_bv 64 (h + 1)); C8 h2; CB 64 hs]
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' (F + 24) [C8 sp]
    /\ rw_cells asegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma sm1_probe_loop : forall RNG (POST : machine_state -> Prop)
    ra sp gp tp t1 t2 s0 s1 a1 a3 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (fs h : Z) (n : nat),
  Z.of_nat n < 8192 -> 0 <= fs -> fs + 11571200 < 2^64 ->
  a3 = Z_to_bv 64 (fs + 20480) -> a4 = Z_to_bv 64 8191 ->
  rng RNG fs 11571200 ->
  (forall j, (j < n)%nat -> rw_cells asegs m (fs + 20480 + Z.land (h + Z.of_nat j) 8191) [C1 (Z_to_bv 8 1)]) ->
  rw_cells asegs m (fs + 20480 + Z.land (h + Z.of_nat n) 8191) [C1 (Z_to_bv 8 0)] ->
  (forall a0 a2 a5 a7 t0 : word,
     a0 = Z_to_bv 64 (8192 - Z.of_nat n) -> a2 = Z_to_bv 64 (h + Z.of_nat n) ->
     a5 = Z_to_bv 64 (fs + 20480 + Z.land (h + Z.of_nat n) 8191) -> a7 = Z_to_bv 64 (Z.land (h + Z.of_nat n) 8191) ->
     t0 = Z_to_bv 64 0 ->
     evtF asegs RNG POST
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 SM1_FOUND) fc None m (seg_rom asegs))) ->
  forall (i : nat) (a0 a2 a5 a7 t0 : word), (i <= n)%nat ->
  a0 = Z_to_bv 64 (8192 - Z.of_nat i) -> a2 = Z_to_bv 64 (h + Z.of_nat i) ->
  evtF asegs RNG POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 SM1_LOOP) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros NB FS0 FSH A3 A4 RFS BUSY FREE K. subst a3 a4. unfold SM1_LOOP, SM1_FOUND in *.
  assert (IND : forall (d i : nat) (a0 a2 a5 a7 t0 : word), (n - i = d)%nat -> (i <= n)%nat ->
            a0 = Z_to_bv 64 (8192 - Z.of_nat i) -> a2 = Z_to_bv 64 (h + Z.of_nat i) ->
            evtF asegs RNG POST
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (fs + 20480)) (Z_to_bv 64 8191) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  FR (Z_to_bv 64 0x3c7b8) fc None m (seg_rom asegs))).
  { induction d as [|d IH]; intros i a0 a2 a5 a7 t0 Hd Hi A0 A2; subst a0 a2.
    - (* [comment removed for export] *)
      Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10694425001.5610694425001.6123495062912.5323802480751.5524115025146.6024432187974.5524432187974.6024493864992.4843287385484.554681720013.55 48582953726.5048582953726.5552067438401.5553768766698.4859308634759.1 59308634884.5 61165712313.5461873373248.468902107170.55 00000700B00M00X00f01001>01E01P01[01\01]01k02202602A02O02V02aS2Hi2HdS2Hd2Hi3HinS2Hd2Hi3HinS2Hd2Hi3HinS2NB2Hd2Hi3HinS2Hi2Hd2PBS2Hd2Hi3Hin2PBS2Hi2HdS2Hd2Hi3HinS2Hd2Hi3HinFFS2NB2Hd2Hi3HinS2Hd2HiS2KdS2NB3Hin2KeS2NB2Hd2Hi3HinS2Hd2HiS2Hd2Hi3Hin".
assert (i = n) by lia. subst i.
      pose proof (land8191_bound (h + Z.of_nat n)) as PB.
      set (pos := Z.land (h + Z.of_nat n) 8191) in *. set (flag := fs + 20480 + pos) in *.
      zstep. rewrite ?land8191_mod64. fold pos.            (* [comment removed for export] *)
      zstep. fold flag.                                    (* [comment removed for export] *)
      zstep; rewrite ?zxb_lit by lia.                      (* [comment removed for export] *)
      zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].      (* [comment removed for export] *)
      eapply K; first [reflexivity | word_eq_tac].
    - (* [comment removed for export] *)
      assert (Hin : (i < n)%nat) by lia.
      pose proof (land8191_bound (h + Z.of_nat i)) as PB. pose proof (BUSY i Hin) as FB.
      set (pos := Z.land (h + Z.of_nat i) 8191) in *. set (flag := fs + 20480 + pos) in *.
      zstep. rewrite ?land8191_mod64. fold pos.            (* [comment removed for export] *)
      zstep. fold flag.                                    (* [comment removed for export] *)
      zstep; rewrite ?zxb_lit by lia.                      (* [comment removed for export] *)
      zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd; lia|].      (* [comment removed for export] *)
      zstep; lits.                                         (* [comment removed for export] *)
      rewrite ?(Z.mod_small (8192 - Z.of_nat i) 18446744073709551616) by lia. rewrite ?swrap32_small1K by lia.
      zstep.                                               (* [comment removed for export] *)
      zstep. if_cases Ke; zify_cond Ke; [| exfalso; clear - Ke Hin NB; lia].      (* [comment removed for export] *)
      eapply (IH (S i)); [lia| lia| word_eq_tac| word_eq_tac]. }
  intros i a0 a2 a5 a7 t0 Hi A0 A2. exact (IND (n - i)%nat i a0 a2 a5 a7 t0 eq_refl Hi A0 A2).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stack_malloc1_cspecK : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h : Z) (n : nat) (pos flag F : Z) (j24 j120 sh0 sh1 h0 h2 : word) (hs : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells asegs m fs [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells asegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  Z.of_nat n < 8192 ->
  (forall j, (j < n)%nat -> rw_cells asegs m (fs + 20480 + Z.land (h + Z.of_nat j) 8191) [C1 (Z_to_bv 8 1)]) ->
  (* [comment removed for export] *)
  pos = Z.land (h + Z.of_nat n) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  rw_cells asegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (F + 24) [C8 j24] -> rw_cells asegs m (F + 120) [C8 j120] ->
  rw_cells asegs m (shad F) [C8 sh0; C8 sh1] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (sm1_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat n) flag F h0 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CX0 CX1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC NB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm1_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm1_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192) by (subst pos; apply land8191_bound).
  Local Ltac2 Set LiaHints.tbl := fun () => "06M0?10028172029.14510090985683.15810694425001.15310863296243.15411154510418.13011154510418.15211154510418.15411154510418.15811247962948.15611263313.148   11534695739.1531162840619.141 1178057561.132 1178057561.158 11801586693.14511912261651.13712105240732.14212113445179.15312429510126.13212429510126.15812461674227.15312675873390.1311309658265.158 13205419683.13013547000029.13113742375437.13013742375437.15213742375437.15814335039570.13014335039570.15214335039570.15414335039570.15814671563435.15414761575534.13114869235822.13114981703928.15315064435441.15315418451002.15415526685939.15415600526930.13015600526930.15215600526930.15415600526930.15815685060272.13015970999098.9  16576250094.12916622434386.13016622434386.15216622434386.15416622434386.15816781328285.15216781328285.15416781328285.1581711046475.158 17221588796.12917763167515.15317776320428.12917776320431.1561803730589.141 18376799102.15118567534427.8  19006120615.13219139940946.13019139940946.15219139940946.15419139940946.15819625868450.14219842769139.1532004949074.130 2004949074.152 2004949074.154 2004949074.158 20066445936.1562027029998.132 2027029998.158 20580501374.13220580501374.15820712148848.13120855138317.13020855138317.15420855138317.15821261279374.13121788694114.13021788694114.15221788694114.15421788694114.15821828257790.13122185501522.13022185501522.15222185501522.15422185501522.15822322463106.13022322463106.15222322463106.15422322463106.15822541649553.15322690740306.13022690740306.15222690740306.15422690740306.15822700267513.14623023406835.15423039802350.13223039802350.15823118752381.14523182766875.15123230285244.13123436275955.15324434285121.15224493975745.13824498846877.1412482576659.153 25435258127.13025435258127.15725566553219.13225566553219.15825842667155.1292597719022.132 2597719022.158 25989429701.15626157784174.13126245389312.1522658730222.129 2679425267.156 26886528126.12927177037104.1442748580438.141 27995595862.14128192194670.13129071941542.15129071941542.15629168695305.13029440446802.12329458023242.13029458023242.15229458023242.15429514832494.13129782367974.11829786301405.14830195227828.14230401015406.12930603927662.13130883684441.12931091456718.13132377744366.13232377744366.15832480256782.13232480256782.15832505323477.1383273487251.132 32964912601.13133030292723.1563319336936.153 3319336936.154 3319336936.155 3319336936.156 3321256686.129 33399639534.13233399639534.15833527078768.13233527078768.15833680001082.12934145311854.13134292212932.12234925869678.1313497885311.151 35182850309.15635799908155.15335895327997.14535911566651.15335914383086.12936347741165.14236786877341.14236964796433.15336986663037.14537317216127.13237520469375.15137534656338.13037534656338.15237534656338.15437534656338.15837845668334.13237845668334.15837881405678.12938057555965.14538289982801.15238407447611.15338415960657.15838746804974.12938777913515.15238806986883.12938806986883.15639093924078.12939318646927.13039941337888.14939950916472.15239975443728.14239982430437.15740077673433.13140273267480.1234032775483.153 40653749742.13240653749742.15840919223559.14541387167214.13241387167214.15841562522423.14841590755381.14241716788283.15341834437230.13142666396205.15342831019478.13042831019478.15242831019478.15442831019478.15843018870045.12343061428541.12043344963635.15443350116725.14243477371917.15343484866395.15343493603410.13043493603410.15243493603410.15443493603410.1584359095406.131 43783722936.9  43987951406.13143987951406.15744474107393.9  44484923210.14544575565867.1414484320.141    4484320.149    44932779437.14245221239098.13245221239098.15845231500942.13245231500942.15846024206162.13046024206162.15246024206162.15446024206162.15846162087634.13046162087634.15246162087634.15446162087634.15846356275438.129463799374.132  46410543275.15446792172603.15346895219182.13246895219182.15846991319781.15047219577582.12947541194043.15347904107902.14048057003647.1294858766673.154 48615158610.13048615158610.15248615158610.15448615158610.15848779672091.15348986915965.14549147106492.13049147106492.15249147106492.15449147106492.15849225892809.15649537285875.15449610168957.14549725679086.13249725679086.15849746975485.14549759691888.12950077211645.14550341488883.15450343456312.1535090388529.148 51385255155.15451588457901.15851626400985.1425180980284.132 51893588449.14252198366190.13252198366190.15852331411998.14052485218579.13152564852745.19 52567164907.12952567164907.13052567164907.13152567164907.13252567164907.15252567164907.15352567164907.15452567164907.15852994560594.13052994560594.15252994560594.15452994560594.15853057627286.15653128540249.15653293700848.13153586536978.15353767577775.13053767577775.15654532700782.13154618151079.1315468461966.129 55104759171.13155104759171.15755149944142.12955242234517.1505597840985.129 56170218651.123563227834.131  56426686290.13056426686290.15256426686290.15456426686290.15856451330108.13056451330108.15256451330108.15456451330108.15856538540882.13056538540882.15256538540882.15456538540882.15856757832430.12957063784944.12957160565742.15757179964532.14257236893747.15357236893747.15457236893747.15557236893747.15657378835438.13257378835438.15857663453676.15557733900014.12957968800571.15358057019758.13258057019758.15858423725816.15359178106163.13059308634368.3  59308634497.1  59308634630.1  59490810099.15459611247859.15359714112337.15459828944221.12959944303675.15360030795750.15560030795751.15560092795981.1456040694587.153 60797519086.13160976774461.1456166287527.129 6232036083.154 62782676313.13262782676313.15862853848379.15363045513727.13163212485103.14463235321900.12863235321900.15563306163197.14563367749646.13163516854384.15663748486815.14464024731519.15664055302894.12964537798034.13064537798034.15264537798034.15464537798034.15864584828014.13164862446845.14565529023470.13265529023470.15866106517232.13266106517232.15866278783357.14566456881245.13266464870522.1566658245522.145 67020194875.15367551820761.15667609733595.15467842335232.15468008320110.13168501319406.12968685696243.15468705475182.13168714883566.13268714883566.1587191075638.127 7442894862.129 768600123.153  7874748219.153 7992270198.153 8272751126.145 8370967830.140 8471890429.145 8610795133.145 8989708403.153 9405451517.145 9945845998.129 9956545262.129 00000B00C00D00J00X00d01001@01A01V01d01e02802N03G03H03I03W03e04504;04I05305@05M05`05a06706E06Q06]06m06n07<07J07Z08>08?08E08S08_08k09;09@09L09Z09h0:40:@0:P0:c0;60;`0;a0;f0<40<80<<0<=0<>0<E0<F0<T0<`0<l0=<0==0=C0=Q0=]0=i0>90>D0>R0>b0>o0?40?A0?T0?U0?k0@90@N0@^0@n0AR0A_0Am0B90BE0BU0Bb0Bm0C80C=0CF0CT0C`0Cl0D<0E00E60ED0ET0Ef0F10F60F<0FE0FF0FG0FR0FS0FT0FU0FV0Fb0G00G@0GA0GO0GT0Gb0Gh0H50H90H:0H;0HI0HJ0HK0HX0H[0IE0I[0J10J?0J@0JA0JB0JP0J^0K10K[0Ki0L90LG0LW0Lf0M20ME0MK0MQ0MW0M]0Mc0N10N?0NO0N\0Na0Nf0O40O50OC0OD0OM0O[0Om0P;0PI0PJ0PK0PT0Pf0Q30Q40QB0QN0QZ0Qj0R80RH0RV0Rh0Ri0S70S<0SJ0SK0SL0SM0S[0Sg0Sk0Sl0Sm0Sn0TA0TB0TP0T^0Tn0To0U=0UM0UN0UT0Ub0V00V90V>0VC0VH0VM0VQ0VU0V[0V\0V`0Va0Vo0W;0WG0WW0We0X30X70X;0XG0XH0XI0X^0Y30Y40Y90Y>0YS0Z70ZE0ZQ0Z]0Zm0[;0[G0[S0[c0\10\[0\\0\j0]80]H0]I0]W0]e0]i0^60^70^E0^Q0^]0^m0_20_D0_Q0_\0_g0`@0`E0`K0`]0`k0a;0aM0aZ0al0b20b70b80b>0bC0bD0bI0bS0ba0c10c20c>0cb0cc0cd0ce0cf0cg0ch0ci0cj0d80dD0dP0d`0da0db0do0eD0eH0eL0eZ0e[0f00f10f20f\0f]0g00g10g60gD0gP0g\0gl0h90hD0hO0hT0hb0hn0i:0iJ0iX0ie0if0ig0il0j10j60j;0jI0jY0jZ0jh0k60kD0kT0kd0ke0kn0l20l60l<0lB0lC0lP0l^0l_0l`0m20m@0mN0m`0ma0mg0n:0nP0n^0nk0o20o60o:0oL0oa0ol10310410B10P10\10h11811F11X11f12612C12\12n13;13H13a13o14014114614D14R14X14f15415D15T15b16016>16?16P16Q16c17517;17M17[17iS2LO4CEIL4ATR03HspSSS4FLOLS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFS3FHI2FF4FLOL2PB4ATR0S4FLAG4FLOL2PBFS2LO4CEIL3FHI2FF2PBS3FAL4FLAG2FF4FLOL3SHFS3Hsp2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR02T13BHI3CX1FFS4FLAG4FLOL2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS4FLOLS2LO4CEIL4ATR0S2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S2LO4CEIL3CX1S2LO4CEIL3BHIS2LO4CEIL3FHI2FF2PBSS3FAL4FLAG2FF4FLOL3SHFS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFS2LO4CEIL4ATR0S2LO4CEIL4ATR0S3POS4FLAG2FF2PBS3FAL3POS4FLAG2FF4FLOL2PB3SHF3SHD2KaFS4FLOLS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS3HB0S2FF2PB4FLOBS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL3FHI2FF2PBS2LO4CEIL3FHI2FF2PBS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0SS3HB0S4FLAG4FLOL2PBS2LOS2LOFFS2FF2PBSS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFS4FLOLS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS3POS2FF2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL3FHIS3SHDS2LO4CEIL3FHIS2LO4CEIL3FHI2FF2PBSS3FAL4FLAG2FF4FLOL3SHFS2LO4CEIL4ATR0S2LO4CEIL3FHI4FLAG2PBS3POS4FLAG2FF2PBS3POS4FLAG2FF2PBS3FAL3POS4FLAG2FF4FLOL2PB3SHF3SHD2KaS2LO4CEIL3FHIS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL3FHIS3POS2FF2PBS3POS2FF2PBS3SHDS4FLAG2PBS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR03SHD3Hsp1HS4FLOLS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR03HspS3POS2FF2PBS3HB0S4FLOLS4FLAG2PBSFS3POS2FF2PBSSSSS2LO4CEIL2T1S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFFS2LO4CEIL4ATR0S3HB0S2LO4CEIL4ATR0S4FLOLS2LO4CEIL3FHIS2HjFFS2LO4CEIL4ATR0FFS2LO4CEIL3BHIS1VS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S3FAL4FLAG2FF4FLOL3SHFS3FAL4FLAG2FF4FLOL3SHFS2LO4CEIL4ATR0SSFS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2LO4CEIL3FHI2FF2PBS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS3FHI4FLOL4ATR0S2LO4CEIL2T1S2LO4CEIL3FHI2FF2PBS4FLOLS4FLOLS4FLOLS4FLOLS4FLOLS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL3FHIS3SHDS3HB0S2LO4CEIL4ATR0SS2LO4CEIL4ATR0SS4FLAG2PBS4FLAG4FLOL2PBS2LO4CEIL4ATR03HspS4FLAG4FLOL2PBS2LO4CEIL4ATR0FFS4FLAG2PBS2LO4CEIL4ATR03HspS2LO4CEIL3CX1SS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2LO4CEIL4ATR03HspSS4FLAG4FLOL2PBS3HB0S2LO4CEIL4ATR0SSSS2LO4CEIL4ATR0S2LO4CEIL2T1S2LOFFSS2LO4CEIL3FHI2FF2PBFS4FLAG4FLOL2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFSS4FLOLS4FLAG4FLOL2PBS2LO4CEIL4ATR0S4FLAG2PBS3HB0S3HB0S3HB0S3HB0S2LOS2LOS4FLOLFS2PBSS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF2PB4FLOB1HS2LOS2LOS2FF2PB4FLOBFFS3FHI2FF4FLOL2PB4ATR0S3FHI2FF4FLOL2PB4ATR0SS3HB0S3HB0S2LO4CEIL3FHI4FLAG2PBS3FAL3POS4FLAG2FF4FLOL2PB3SHF3SHD2KaS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0SS4FLAG4FLOL2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFSS2LO4CEIL4ATR0S4FLAG4FLOL2PBS2FFS2LO4CEIL3CX1SS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS3HB0S2LO4CEIL4ATR03HspS2LO4CEIL3FHIS3POS2FF2PBS3POS2FF2PBS3FAL4FLAG2FF4FLOL2PB3SHFS3SHDS4FLOLS2LO4CEIL4ATR03HspS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR03HspS2LO4CEIL3FHIS2LO4CEIL4ATR03HspS4FLOLS3HB0SS4FLOLS3HB0SS3HB0S3FHI4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFSS2LO4CEIL2T1S2LO4CEIL3FHI4FLAG2FF2PB3SHD3PBj3NEjSSSSSSSSS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFSS2LO4CEIL3FHIS2LO4CEIL3FHI4FLAG2PBS2LOS2LOS2LO4CEIL4ATR0SS2LO4CEIL3FHI4FLAG2PBSSS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0SS2LO4CEIL3FHI2FF2PBSS3HB0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL3FHIS3POS2FF2PBS3POS2FF2PBS3SHDS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2LO4CEIL3FHISFS3HB0S3HB0S3HB0S3HB0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFFS2LO4CEIL4ATR0S4FLAG4FLOL2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS3POS4FLAG2FF2PBSS4FLOL2KaS2KbS2KcS4FLOLS4FLOLFS2LO4CEIL3BHIS4FLAG4FLOL2PBSSS2LO4CEIL4ATR03HspS4FLAG4FLOL2PBS2LO4CEIL4ATR0S2LO4CEIL4ATR03HspSS4FLOLS2LO4CEIL3FHI2FF2PBS3FAL4FLAG2FF4FLOL3SHFS4FLAG4FLOL2PBS2LO4CEIL3CX1S2NB2HjS2LOS2LOS2LO4CEIL4ATR03HspS2LO4CEIL3FHI4FLAG2PBS3POS2FF2PBS2NB2HjFS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2LO4CEIL4ATR03HspS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL3FHIS3FAL4FLAG2FF4FLOL2PB3SHFS2LO4CEIL4ATR03HspS2LO4CEIL3BHIS2LO4CEIL3FHIS2LO4CEIL3FHI4FLAG2PB3HspS4FLAG4FLOL2PBSFS3HB0S2LO4CEIL4ATR0S2LO4CEIL4ATR0S4FLOLS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR01HS2LO4CEIL4ATR0S4FLAG4FLOL2PBS4FLAG4FLOL2PBFS2LO4CEIL3FHI3HspSS2LO4CEIL4ATR03HspS2LO4CEIL4ATR03HspS4FLOLS2LO4CEIL4ATR03HspS2LO4CEIL4ATR0S2LO4CEIL4ATR0".
assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof atop_range as ATR0.
  assert (SHD : shad F + 16 <= fs \/ fs + 11571200 <= shad F).
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  do 9 zstep.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with HM : munch _ m mm, HW : wmono asegs m mm |- _ =>
      assert (BUSY2 : forall j, (j < n)%nat -> rw_cells asegs mm (fs + 20480 + Z.land (h + Z.of_nat j) 8191) [C1 (Z_to_bv 8 1)]);
      [ intros j Hj; pose proof (land8191_bound (h + Z.of_nat j)) as PBj;
        pose proof (land8191_inj h (Z.of_nat j) (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(lia)) as NEj;
        rewrite <- POS in NEj;
        eapply rw_cells_transport; [exact (BUSY j Hj)| exact HM| exact HW|];
        cbn [disjoint_from cells_size csize Nat.add length];
        clear - PBj NEj PB FLAG FF SHD FHI CEIL LO ATR0; lia
      | ] end end.
  eapply (sm1_probe_loop RNG) with (fs := fs) (h := h) (n := n) (i := 0%nat);
    first [ exact NB | lia | reflexivity | word_eq_tac | exact BUSY2 | exact RFS
          | (rewrite <- POS, <- FLAG; exact FL0) | idtac ].
  (* [comment removed for export] *)
  unfold SM1_FOUND. intros a0' a2' a5' a7' t0' -> -> -> -> ->. rewrite <- POS, <- FLAG.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + (1048576 + Z.shiftl pos 7))] =>
    replace (fs + 36864 + (1048576 + Z.shiftl pos 7)) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 16).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  zstep. zstep.                             (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
