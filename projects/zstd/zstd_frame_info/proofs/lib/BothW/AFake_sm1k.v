(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells AProto ABase F_tryinit F_aunwind F_tlsga F_m2s_b.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit FsKit AFake_sm0.
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
Definition ASTKMALLOC1 : Z := 0x3c728.
Definition SM1_LOOP : Z := 0x3c7bc.
Definition SM1_FOUND : Z := 0x3c834.

(* [comment removed for export] *)
Definition sm1_W (sp fs flag F : Z) : list (Z * Z) :=
  [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (shad F, shad F + 16)].

Definition sm1_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo fs h flag F : Z) (h0 h2 : word) (hs : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 (shad F)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm1_W (bv_unsigned sp) fs flag F) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' fs [C8 h0; C8 (Z_to_bv 64 (h + 1)); C8 h2; CB 64 hs]
    /\ rw_cells bsegs m' flag [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (F + 24) [C8 sp]
    /\ rw_cells bsegs m' (F + 120) [C8 (Z_to_bv 64 flag)]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma sm1_probe_loop : forall RNG (POST : machine_state -> Prop)
    ra sp gp tp t1 t2 s0 s1 a1 a3 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (fs h : Z) (n : nat),
  Z.of_nat n < 8192 -> 0 <= fs -> fs + 11571200 < 2^64 ->
  a3 = Z_to_bv 64 (fs + 20480) -> a4 = Z_to_bv 64 8191 ->
  rng RNG fs 11571200 ->
  (forall j, (j < n)%nat -> rw_cells bsegs m (fs + 20480 + Z.land (h + Z.of_nat j) 8191) [C1 (Z_to_bv 8 1)]) ->
  rw_cells bsegs m (fs + 20480 + Z.land (h + Z.of_nat n) 8191) [C1 (Z_to_bv 8 0)] ->
  (forall a0 a2 a5 a7 t0 : word,
     a0 = Z_to_bv 64 (8192 - Z.of_nat n) -> a2 = Z_to_bv 64 (h + Z.of_nat n) ->
     a5 = Z_to_bv 64 (fs + 20480 + Z.land (h + Z.of_nat n) 8191) -> a7 = Z_to_bv 64 (Z.land (h + Z.of_nat n) 8191) ->
     t0 = Z_to_bv 64 0 ->
     evtF bsegs RNG POST
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 SM1_FOUND) fc None m (seg_rom bsegs))) ->
  forall (i : nat) (a0 a2 a5 a7 t0 : word), (i <= n)%nat ->
  a0 = Z_to_bv 64 (8192 - Z.of_nat i) -> a2 = Z_to_bv 64 (h + Z.of_nat i) ->
  evtF bsegs RNG POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 SM1_LOOP) fc None m (seg_rom bsegs)).
Proof.
  intros until n. intros NB FS0 FSH A3 A4 RFS BUSY FREE K. subst a3 a4. unfold SM1_LOOP, SM1_FOUND in *.
  assert (IND : forall (d i : nat) (a0 a2 a5 a7 t0 : word), (n - i = d)%nat -> (i <= n)%nat ->
            a0 = Z_to_bv 64 (8192 - Z.of_nat i) -> a2 = Z_to_bv 64 (h + Z.of_nat i) ->
            evtF bsegs RNG POST
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (fs + 20480)) (Z_to_bv 64 8191) a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  FR (Z_to_bv 64 0x3c7bc) fc None m (seg_rom bsegs))).
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
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  (* [comment removed for export] *)
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  Z.of_nat n < 8192 ->
  (forall j, (j < n)%nat -> rw_cells bsegs m (fs + 20480 + Z.land (h + Z.of_nat j) 8191) [C1 (Z_to_bv 8 1)]) ->
  (* [comment removed for export] *)
  pos = Z.land (h + Z.of_nat n) 8191 -> flag = fs + 20480 + pos -> F = fs + 1085440 + pos * 128 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 120) [C8 j120] ->
  rw_cells bsegs m (shad F) [C8 sh0; C8 sh1] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm1_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + Z.of_nat n) flag F h0 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY CX0 CX1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC NB BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm1_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm1_W in MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC1 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 8192) by (subst pos; apply land8191_bound).
  Local Ltac2 Set LiaHints.tbl := fun () => "06C0?10090985683.15810320659453.14510558322770.13010558322770.15210558322770.15410558322770.15810694425001.15311247962948.15611263313.148   11423301435.1531178057561.132 1178057561.158 11801586693.14511903774446.12912105240732.14212334040174.1311309658265.158 13205419683.13013547000029.13113742375437.13013742375437.15213742375437.15813855543027.1531414717243.153 14159447534.13214159447534.15814413815539.15414671563435.15414782759150.12914981703928.15315064435441.15315418451002.15415685060272.13015970999098.9  16354687726.12916781328285.15216781328285.15416781328285.158170773230.129  1711046475.158 17221588796.12917776320428.12917776320431.15618276986478.12918376799102.15118567534427.8  19006120615.13219007305966.1291931560046.131 19583701006.12919625868450.14219743703890.13019743703890.15219743703890.15419743703890.15820066445936.15620580501374.13220580501374.15820712148848.13120855138317.13020855138317.15420855138317.15821077578749.14521250035837.14521400702267.15321705295537.14821788694114.13021788694114.15221788694114.15421788694114.15821828257790.13122020459763.15422322463106.13022322463106.15222322463106.15422322463106.15822496007293.14522541649553.15322700267513.14623182766875.15123230285244.13123446526574.13123742962798.13123814431342.13123912386675.15324205896189.14524346898045.14524434285121.15224493975745.13824559830510.13224559830510.15824578764059.1532482576659.153 25435258127.13025435258127.15725566553219.13225566553219.15825777242222.13125842667155.12925886974446.13225886974446.15825989429701.15626245389312.15226886528126.12926961506542.12927177037104.1442728429678.131 27335527918.13227335527918.15827730847314.13027730847314.15227730847314.15427730847314.15829071941542.15129071941542.15629168695305.13029440446802.12329458023242.13029458023242.15229458023242.15429782367974.11829786301405.14830061110030.13230061110030.15830195227828.14230883684441.12931091456718.13131361185874.13031361185874.15231361185874.15431361185874.15832162886226.13032162886226.15232162886226.15432162886226.1583221751099.153 32505323477.1383273487251.132 32964912601.1313319336936.153 3319336936.154 3319336936.155 3319336936.156 33393696910.13133527078768.13233527078768.15833680001082.1293381640251.153 34292212932.12234501708331.1413497885311.151 35182850309.15635629539571.15336347741165.14236786877341.14236964796433.15337317216127.13237520469375.15137763497787.15338238797294.13238238797294.15838289982801.15238415960657.15838777913515.15238806986883.12938806986883.15639007438674.13039007438674.15239007438674.15439007438674.15839318646927.13039941337888.14939950916472.15239975443728.14239982430437.15740059657198.13240059657198.15840077673433.13140273267480.12340292163822.12940311178299.15340584289006.12940919223559.14541015738683.15341422737467.15341562522423.14841590755381.14241991077614.12942037359347.15442087620846.12942666396205.15342744733806.13142831019478.13042831019478.15242831019478.15442831019478.15843018870045.12343061428541.12043350116725.14243477371917.15343484866395.15343609253714.13043609253714.15243609253714.15443609253714.15843783722936.9  43987951406.13143987951406.15744253452910.13144395637586.13044395637586.15244395637586.15444395637586.15844474107393.9  44484923210.14544545694830.13144804625134.1294484320.141    4484320.149    44932779437.14245221239098.13245221239098.15845231500942.13245231500942.15845238050109.14545270092019.15645607773934.129463799374.132  46410543275.15446785618030.13146991319781.15047178742894.13147450240243.15347791873779.15447904107902.14048055189230.12948057003647.12948577040082.13048577040082.15248577040082.15448577040082.1584858766673.154 48654615790.13148779672091.15349123722493.14549147106492.13049147106492.15249147106492.15449147106492.15849225892809.15649759691888.12949978085870.13249978085870.1585012112366.132 5012112366.158 50343456312.15350575413842.13050575413842.15250575413842.15450575413842.15850682020438.14150698002838.14051588457901.15851626400985.14251787079037.1455180980284.132 51893588449.14252258020667.15352331411998.14052485218579.13152564852745.19 52567164907.12952567164907.13052567164907.13152567164907.13252567164907.15252567164907.15352567164907.15452567164907.15853057627286.15653128540249.1565318067259.153 53293700848.13153386120174.13253386120174.15853586536978.15353767577775.13053767577775.15654011733842.13054011733842.15254011733842.15454011733842.15854618151079.1315468461966.129 54878877755.15354959238227.13755104759171.13155104759171.15755149944142.12955183674350.13255183674350.15855207105262.12955242234517.1505597840985.129 56170218651.123563227834.131  56451330108.13056451330108.15256451330108.15456451330108.15856582466030.13256582466030.15856628831291.15357063784944.12957160565742.15757179964532.14257236893747.15357236893747.15457236893747.15557236893747.15657282212667.15357663453676.15557730705459.15458090187835.15358391494301.14158423725816.15358536729426.13058536729426.15258536729426.15458536729426.15859038122478.13259038122478.15859140765939.15459178106163.13059308634368.3  59308634497.1  59308634630.1  59714112337.15459828944221.12960030795750.15560030795751.15560272857843.15460435143278.13160471841134.13260471841134.1586166287527.129 61837801715.15462386236669.14562782676313.13262782676313.15863045513727.13163165162365.14563212485103.14463235321900.12863235321900.15563367749646.13163516854384.15663748486815.14464024731519.15664200421619.1536443449501.141 64723543165.14565006732531.15465006732531.15665346271869.14565485175549.14565811741693.14566054553331.15466106517232.13266106517232.15866456881245.13266464870522.1566658245522.145 66656729710.13167442352978.13067442352978.15267442352978.15467442352978.15867551820761.15667609733595.15467842335232.15468309604434.13068309604434.15268309604434.15468309604434.1587109422157.145 7191075638.127 7276799062.141 7950738834.130 7950738834.152 7950738834.154 7950738834.158 7992270198.153 802261998.132  802261998.158  8272751126.145 8726975058.130 8726975058.152 8726975058.154 8726975058.158 9253808171.141 9939242478.132 9939242478.158 00000100C00Q00]00i01901:01;01P01^02102G03@03N03O03]04G04T04a05405505K05Q05_05m06=06C06D06R06b07F07G07L07X07f08908L09609D09E09J09N09R09`09a09h09i0:70:E0:S0:T0:b0:n0;:0;J0;U0;b0;g0<40<G0<H0<^0=00=B0=P0=Q0=f0>60>F0>j0?70?=0?J0?U0?`0?e0@70@@0A40A?0AD0AR0A`0An0B40BF0BX0Ba0Bb0C00C@0CN0CY0CZ0C[0C\0C]0Ck0D70DE0DU0DV0D[0Dh0E60E:0EH0EV0Ef0F40F@0FL0F\0F]0F^0Fk0Fn0GX0Gn0HD0HE0HF0HT0Hd0He0I80Ib0J00J<0JH0JX0Jf0K20K>0KN0K\0Kk0L70LJ0LP0LV0L\0Lb0M00M=0MB0MG0MU0MV0MW0MX0Ma0Mg0Mh0Mi0N20N?0N@0NN0N\0Nl0Nm0O20O30O40O50OC0OO0O[0Ok0P70P;0P<0P=0P>0PL0P\0Po0Q00Q>0QL0QZ0Q[0Qi0R70R80R>0RL0RR0R`0Ri0S70S<0SA0SF0SK0SO0SS0ST0SX0SY0Sg0T30T?0TO0T]0Ta0Te0U30UA0UM0UY0Ui0V50V60VD0VR0Vg0W<0W=0WB0WG0W\0X@0XR0XX0Xf0YP0YQ0Y_0Y`0Yn0Z40Z:0Z>0ZL0ZY0Zg0[30[?0[O0[P0[^0[c0\50\B0\M0\X0]10]60]C0]Q0]a0]o0^?0^D0^R0^^0^j0_:0_;0_<0_A0_B0_T0_Y0_c0`10`20`>0`b0`c0`d0`e0`f0`g0`h0`i0`j0`k0`l0a:0aG0aU0ae0b:0b>0bB0bP0b\0bh0c80c90cN0c\0c]0c^0c_0dI0dW0dg0e50e60eI0eJ0eO0e\0eg0f20f70fE0fU0fc0g00g10g20g70g<0gA0gF0gT0gU0g[0gi0gj0h:0hH0hT0h`0i00i>0iN0iT0iU0i^0ib0if0ig0j40j50j60j<0jJ0jX0jh0ji0jo0kA0kT0kj0l70lI0lP0lT0lX0lm0m80m?0m@0mF0mG0mY0m_0me0n70nI0n[0na0nn0oG0oT0oa10:10H10V10b10n11>11?11@11E11S11_11k12;12M12]12^12l13813D13T13U13c14314D14R14^14j15:15;15I15YSS2LO4CEIL4ATR03HspS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFSFS3FHI2FF4FLOL2PB4ATR0S4FLAG4FLOL2PBS2LO4CEIL3FHI2FF2PBS3FAL4FLAG2FF4FLOL3SHFS3Hsp2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR02T13BHI3CX1S2LO4CEIL4ATR0FS2LO4CEIL4ATR0S2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S2LO4CEIL3CX1S2LO4CEIL3BHIS2LO4CEIL3FHI2FF2PBSS3FAL4FLAG2FF4FLOL3SHFS4FLOLS4FLAG4FLOL2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS4FLOLFS2LO4CEIL4ATR0S3POS4FLAG2FF2PBS3FAL3POS4FLAG2FF4FLOL2PB3SHF3SHD2KaFS3HB0S2FF2PB4FLOBS2LO4CEIL4ATR0S2LO4CEIL3FHI2FF2PBS2LO4CEIL3FHI2FF2PBS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S2LO4CEIL4ATR0SS3HB0S2LOS2LOS2LO4CEIL4ATR0FS2FF2PBSS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2LO4CEIL4ATR0FS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS3POS2FF2PBS2LO4CEIL3FHIS3SHDS2LO4CEIL3FHIS2LO4CEIL3FHI2FF2PBSS3FAL4FLAG2FF4FLOL3SHFS2LO4CEIL4ATR03HspS2LO4CEIL4ATR03HspS4FLAG4FLOL2PBSS2LO4CEIL3FHI4FLAG2PBS3POS4FLAG2FF2PBS3POS4FLAG2FF2PBS3FAL3POS4FLAG2FF4FLOL2PB3SHF3SHD2KaS2LO4CEIL3FHIS4FLOLS2LO4CEIL3FHIS3POS2FF2PBS3POS2FF2PBS3SHDS2LO4CEIL4ATR03HspS4FLAG2PBS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR03SHD3Hsp1HS3POS2FF2PBS3HB0S2LO4CEIL4ATR0S2LO4CEIL4ATR0S2LO4CEIL4ATR0S4FLOLS2LO4CEIL4ATR03HspS2LO4CEIL4ATR03HspS4FLAG2PBSS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS4FLAG4FLOL2PBS3POS2FF2PBSSSSS2LO4CEIL4ATR0S2LO4CEIL2T1S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFFS3HB0S2LO4CEIL3FHIS2LO4CEIL4ATR0S2HjS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFFS2LO4CEIL3BHIS1VS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S3FAL4FLAG2FF4FLOL3SHFS3FAL4FLAG2FF4FLOL3SHFSSS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFFS2LO4CEIL3FHI2FF2PBS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS4FLAG4FLOL2PBS3FHI4FLOL4ATR0S2LO4CEIL2T1S2LO4CEIL3FHI2FF2PBS4FLOLS4FLOLS4FLOLS4FLOLS2LO4CEIL4ATR0S2LO4CEIL3FHIS3SHDS3HB0S4FLAG4FLOL2PBSFSS4FLAG2PBS4FLOLFFS4FLAG2PBS2LO4CEIL3CX1SS4FLAG4FLOL2PBS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFSS3HB0SSSS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL2T1S2LOFFSS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL3FHI2FF2PBFS2LO4CEIL4ATR0S4FLAG4FLOL2PBS2LO4CEIL4ATR0FS4FLAG4FLOL2PBS4FLAG4FLOL2PBSS4FLOLS2LO4CEIL4ATR0S4FLOLS2LO4CEIL4ATR0S4FLAG2PBS2LO4CEIL4ATR0S3HB0S3HB0S3HB0S3HB0S2LOS2LOFS2PBSS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2FF2PB4FLOB1HS2LOS2LOS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2FF2PB4FLOBFS2LO4CEIL4ATR0S2LO4CEIL4ATR0S3FHI2FF4FLOL2PB4ATR0S3FHI2FF4FLOL2PB4ATR0SS3HB0S3HB0S2LO4CEIL3FHI4FLAG2PBS3FAL3POS4FLAG2FF4FLOL2PB3SHF3SHD2KaS2LO4CEIL4ATR03HspS4FLOLS2LO4CEIL4ATR0S2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0SS2LO4CEIL4ATR0SS2LO4CEIL4ATR0S4FLOLS4FLOLS2FFS2LO4CEIL4ATR0S2LO4CEIL3CX1S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFSS2LO4CEIL4ATR0S3HB0S2LO4CEIL4ATR03HspS2LO4CEIL3FHIS3POS2FF2PBS3POS2FF2PBS3FAL4FLAG2FF4FLOL2PB3SHFS3SHDS2LO4CEIL3FHIS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS3HB0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFSS3HB0SS2LO4CEIL4ATR03HspS3HB0S3FHI4ATR0S4FLAG4FLOL2PBSS2LO4CEIL2T1S2LO4CEIL3FHI4FLAG2FF2PB3SHD3PBj3NEjSSSSSSSSFSS4FLAG4FLOL2PBS2LO4CEIL3FHIS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL3FHI4FLAG2PBS2LOS2LOS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFSS2LO4CEIL3FHI4FLAG2PBS4FLAG4FLOL2PBFSSS2LO4CEIL3FHI3FAL4FLAG2FF4FLOL2PB3SHF4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL4ATR0SS2LO4CEIL3FHI2FF2PBSS3HB0S2LO4CEIL3FHIS3POS2FF2PBS3POS2FF2PBS3SHDS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS4FLAG4FLOL2PBS2LO4CEIL3FHISFS3HB0S3HB0S3HB0S3HB0S4FLAG4FLOL2PBFS4FLOLS4FLAG4FLOL2PBFS3POS4FLAG2FF2PBS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS4FLOLSS4FLOL2KaS2KbS2KcFS2LO4CEIL3BHISSS4FLOLS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PB3SHFSS4FLOLS2LO4CEIL4ATR03HspS2LO4CEIL3FHI2FF2PBS3FAL4FLAG2FF4FLOL3SHFS2LO4CEIL3CX1S2LO4CEIL4ATR03HspS2NB2HjS2LOS2LOS2LO4CEIL3FHI4FLAG2PBS3POS2FF2PBS2NB2HjFS4FLOLFS2LO4CEIL4ATR03HspS4FLOLS4FLOLS2LO4CEIL4ATR03HspS2LO4CEIL4ATR03HspS2LO4CEIL4ATR03HspS4FLOLS2LO4CEIL3FHIS3FAL4FLAG2FF4FLOL2PB3SHFS2LO4CEIL3BHIS2LO4CEIL3FHIS2LO4CEIL3FHI4FLAG2PB3HspS2LO4CEIL4ATR0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFSFS3HB0S2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFS2LO4CEIL4ATR03HspS2LO4CEIL4ATR01HFS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHFS2LO4CEIL3FHI3HspS2LO4CEIL4ATR0S2FF4FLOL2PBS2FF4FLOL2PBS2FF4FLOL2PB3SHFFS2LO4CEIL4ATR0S2FF4FLOL2PB3SHF".
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
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
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
    lazymatch goal with HM : munch _ m mm, HW : wmono bsegs m mm |- _ =>
      assert (BUSY2 : forall j, (j < n)%nat -> rw_cells bsegs mm (fs + 20480 + Z.land (h + Z.of_nat j) 8191) [C1 (Z_to_bv 8 1)]);
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
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
