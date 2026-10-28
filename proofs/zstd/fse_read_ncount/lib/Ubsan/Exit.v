(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun STRW_tac Startup_kit Amo_tac.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls Startup_A StdioFiles F_atexit.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Notation rsegs := UImg.usegs.
Notation PEXIT_ENTRY := 0x14fb0%Z (only parsing).
Notation PFUNCS_ON_EXIT := 0x14dcc%Z (only parsing).
Notation PLIBC_EXIT_FINI := 0x14f64%Z (only parsing).
Notation PSTDIO_EXIT := 0x17328%Z (only parsing).
Notation PEXIT_LOCK := 0x4f198%Z (only parsing).
Notation PFINALIZED := 0x1ee28%Z (only parsing).
Notation PDSO_HANDLE := 0x1ebc8%Z (only parsing).
Notation PGOT_CXA := 0x1db60%Z (only parsing).
Notation PGOT_FINI := 0x1dbb8%Z (only parsing).
Notation PFINI_ARRAY := 0x1db18%Z (only parsing).
Notation RTD := 0x2ee68%Z (only parsing).
Definition pfuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x4ef78, 0x4ef79); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp).
Lemma pfuncs_on_exit_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
atx_state reg m ->
rw_cells rsegs m 0x4f1c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (0x50000 <= lo)%Z ->
evt rsegs (pfuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFUNCS_ON_EXIT) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7) & CB) LCH MI LO LOLO.
unfold PATX, PATX_CALLFN, PEXIT_GUARD, PAEF_INCB in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x4ef78, 0x4ef79); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "02>0>10136806254.671130189294.65 12608870894.6612637488570.6912637488570.7312790310202.6612790310202.6813768071406.6814025007930.6814328636398.6714491644918.6715749456878.6716502971194.6616502971194.6816782942522.6616782942522.681723618286.65 17805621306.6617805621306.681800609155.66 1800609155.67 18589389294.6718744179310.6619916546158.6620306272826.6620306272826.6820351478586.6620351478586.6820979578165.6620979578165.6822389541692.6522398960058.6922398960058.732269937006.67 22793452142.6623437752430.6824638473347.6724638473347.6924657695214.6724820347194.6824885038966.6425449023214.6826030471949.6926030471949.7326407234618.6827289189946.6827297791862.6427487025262.6727906909603.5827922131438.6728232470254.6828417259964.6729108108270.6729292004410.682937793594.68 30180773870.6530675329978.6930675329978.7331068521070.6631378308326.5831798771054.6732359787248.6932359787248.7333680001082.6834430152252.6834613502574.6536901426061.6837111680570.6838467863406.6839132980026.6639132980026.6840057062766.6740457739452.6640531229166.6541161757422.6841201790582.6442732709998.6643059266230.5643086639342.6843988483203.6543988483203.674454318318.68 45221239098.674541777776.68 45505239918.6745745840622.6545848756903.6546284506554.6946284506554.7346468661564.6747794612789.6847962693050.6947962693050.7348918286448.6648918286448.6849245040366.6849649769127.6851711223320.5752024118390.6652105090727.6752136437230.6752567164907.6552567164907.6652567164907.6752567164907.6852567164907.6952567164907.7352644002798.6553813286638.6654053698550.6554082917742.6554149620538.6654149620538.6854243526019.6654243526019.6856023003502.67563227834.66  57745675194.6758240445498.6859176389614.6760020539322.6960020539322.7360858483367.6760870302650.6960870302650.7361127261166.6561501563758.6763305555623.6664101751662.6764997134979.6764997134979.6864997134979.6967003974766.6667615064174.667683670709.69 7683670709.73 8583720762.65 8745729466.69 8745729466.73 8773384430.67 952866957.66  952866957.68  00000900B00K00L00M00N00O00X00Y00b00c00l00m00n00o01001901:01;01<01=01F01O01X01Y01Z01[01\01e01n02202302402=02F02O02P02Q02Z02[02\02e02f02g02h02i02j03303703@03I03M03V03W03X03a03b03c03l03m04604704804=04A04J04K04L04U04V04W04`04d04m05605705@05D05M05N05O05X05]05^05g06006106206306706@06A06B06C06D06M06N06O06P06Q06Z06[06\06]06^06_06`06i07207307<07=07>07?07@07I07N07S07T07]07^07_07`07a07b07k08408508>08?08@08A08J08S08\08e08j08k08l095096097S2LO4LOLOS2LO4LOLOS2LO4LOLOSSSSS2LO4LOLOSS2LO4LOLOSS2LO4LOLOSSSSS2LO4LOLOSSSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSSSSS2LO4LOLOS2LO4LOLOS2HBSSS2LO4LOLOS2LO4LOLOS2LO4LOLOSSS2LO4LOLOSSS2LO4LOLOSSSSSS2LO4LOLOS2LOS2LO4LOLOS2LO4LOLOS2HBS2LO4LOLOSSS2LO4LOLOSSS2LO4LOLOSS2LO4LOLOSSS3RSPS2HBS2LO4LOLOSSS2LO4LOLOSSS2LO4LOLOS2HBS2LO4LOLOS2LO4LOLOSS2LO4LOLOS2LOS2LO4LOLOSSS2LO4LOLOS3RSPSS2LO4LOLOS2LO4LOLOSSSS2HBS2LO4LOLOSSSSS2LO4LOLOSSSSS2LO4LOLOSSSSSSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSSSSS2LO4LOLOS3RSPS3RSPSS2LO4LOLOSSSSSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSSSS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLOS3RSPSSS2LO4LOLOSS".
carve_frame 48%nat ST.
steps_to 0x1c73c%Z.
lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
lstep.
destruct reg; cbn [negb andb orb] in *.
-
lstep. if_false.
lstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
lstep. lstep. try change (bv_swrap 32 (1 + -1))%Z with 0%Z. lstep. lstep. if_false.
steps_to 0x1c9c4%Z.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
steps_to 0x134b0%Z.
lstep. lstep. lstep. if_false. lstep.
steps_to 0x1c73c%Z.
lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
lstep. try change (bv_swrap 32 (0 + -1))%Z with (-1)%Z. lstep. lstep. if_false.
steps_to 0x14e18%Z. lstep. if_true.
steps_to 0x14e8c%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
unfold pfuncs_on_exit_post, PATX. sys_finish.
-
lstep. if_true.
steps_to 0x14e8c%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
unfold pfuncs_on_exit_post, PATX. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition plibc_exit_fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (PFINALIZED, PFINALIZED + 1)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' PFINALIZED [C1 (Z_to_bv 8 1)].
Lemma plibc_exit_fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m PGOT_FINI [C8 (Z_to_bv 64 0x1db20); C8 (Z_to_bv 64 PFINI_ARRAY)] ->
rw_cells rsegs m PFINI_ARRAY [C8 (Z_to_bv 64 0x12ff8)] ->
rw_cells rsegs m PFINALIZED [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m PGOT_CXA [C8 (Z_to_bv 64 0x14e94); C8 z64] ->
rw_cells rsegs m PDSO_HANDLE [C8 (Z_to_bv 64 PDSO_HANDLE)] ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (0x50000 <= lo)%Z ->
evt rsegs (plibc_exit_fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PLIBC_EXIT_FINI) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros ST GF FA FIN GCX DSO MI LO LOLO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x1ee28, 0x1ee28 + 1)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "0170>10710707182.5912525277678.591309658265.59 1323122798.58 1329372557.65 14869079534.5914913876538.6516781328285.6017221588796.5619006120615.5919203945525.6520979536691.6023230285244.5824638473347.592469233210.65 24701821166.5625071629079.5625071629079.5825071629079.5925071629079.6025071629079.6525566553219.5925566553219.6026244411760.6526924678012.5126961506542.5627679091076.5027802499922.6027806399118.5227905104286.5228186829224.5030651617006.5631361185874.6033680001082.5634263294510.5134290115814.4935265982326.5738446806799.6038806986883.5638806986883.583888239342.56 39939243268.5140059657198.5940935381813.6541564619544.5042443086062.5642831019478.6042988233554.6043059266230.4744253452910.5845221239098.5946468661564.5947250211438.5849135984502.5850362574674.6050994398198.585180980284.59 53141810234.6554477882.65   54618151079.5855104759171.5855104759171.5955539254254.59563227834.58  56981146544.6057216550738.6060858483367.596166287527.56 64084433518.5867208578631.528684881006.58 00000900B00C00L00M00V00W00X00\00]00f00g00k00l00m01601701801901:01;01<01=01>01?01H01L01U01V01Z01[01d01m02202302402502602702802A02E02N02W02X02a02f02o03303<03A03E03N03O03X03Y03]03^03_03`03a03b03k04004404=04>04?04H04I04RS2LO4LOLOS2LO4LOLOSS2LO4LOLOSS2LO4LOLOSSS2HBSS2LO4LOLOSS2HBSSS2LO4LOLOSSSSSSSSSS2LO4LOLOS2LOS2LO4LOLOFS2LOFS2LO4LOLOS2LO4LOLOS3RSPFSSSSSS2LO4LOLOS2LOS2LO4LOLOS2LO4LOLOSS2LO4LOLOS3RSPS2LO4LOLOS2LOS2LO4LOLOS3RSPS2HBS2LO4LOLOSS2LO4LOLOSS2HBSSSSSS2LO4LOLOS3RSPS2HBS2LO4LOLOSSS2LO4LOLOSS2LO4LOLO".
carve_frame 32%nat ST. steps_to 0x12ff8%Z.
carve_frame 16%nat ST. steps_to 0x13080%Z. release_frame FR0 ST (bv_unsigned sp + -32)%Z. astep. astep.
steps_to 0x14fa8%Z. release_frame FR ST (bv_unsigned sp). astep. astep. astep.
unfold plibc_exit_fini_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition pexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x1501c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PSTDIO_EXIT) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (PEXIT_LOCK, PEXIT_LOCK + 4); (PFINALIZED, PFINALIZED + 1);
(0x4ef78, 0x4ef79); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -16)
/\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ rw_cells rsegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' PEXIT_LOCK [C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' PFINALIZED [C1 (Z_to_bv 8 1)].
Lemma pexit_prefix_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
(cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
rw_cells rsegs m PEXIT_LOCK [C4 z64] ->
rw_cells rsegs m PGOT_FINI [C8 (Z_to_bv 64 0x1db20); C8 (Z_to_bv 64 PFINI_ARRAY)] ->
rw_cells rsegs m PFINI_ARRAY [C8 (Z_to_bv 64 0x12ff8)] ->
rw_cells rsegs m PFINALIZED [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m PGOT_CXA [C8 (Z_to_bv 64 0x14e94); C8 z64] ->
rw_cells rsegs m PDSO_HANDLE [C8 (Z_to_bv 64 PDSO_HANDLE)] ->
rw_cells rsegs m 0x4f1c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_state reg m ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x50000 <= lo)%Z ->
evt rsegs (pexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PEXIT_ENTRY) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AX MI -> -> Ht LO LOLO.
destruct AX as [(X1 & X2 & X3 & X4 & X5 & X6 & X7) CB]. unfold PAEF_INCB in CB.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x4f198, 0x4f198 + 4); (0x1ee28, 0x1ee28 + 1);
(0x4ef78, 0x4ef79); (0x4ef80, 0x4ef84); (0x4ef88, 0x4ef90)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "02<0?10710707182.77 11436175540.87 11656353059.10211658450183.87 1203055275.103 12187559190.83 12193577164.10312195674344.87 12293593914.72 12430247196.10212525277678.77 12794519588.87 12843408052.87 1343986644.87  13604231482.72 14328636398.77 14869079534.77 15332305579.1021578976011.88  1590252853.102 1592349969.87  16227573284.87 16240027941.1031742864811.103 18027133498.72 18568930932.87 18589389294.77 20392859730.80 20422406836.87 20433961190.70 23237574068.87 235965754.72   2363895412.87  24395287152.72 24657695214.77 25079341492.87 26492228661.10326494325777.87 27487025262.77 27716857426.80 27802499922.80 27922131438.77 28644957732.87 28675273764.87 29108108270.77 29618419807.87 30721806830.77 3076118289.87  3078215477.103 31361185874.80 31365884986.72 32349584564.87 32443190325.10232445287441.87 32600174396.77 33056122578.80 33395433764.87 3362501458.80  3525607222.68  3525607222.84  35624951350.71 36051384754.98 36104482420.87 36634911984.71 36641385327.72 36972951755.88 38036350266.72 38124732271.87 38144430772.87 38263339322.72 3867822372.87  38787473210.72 39517401529.80 39521875765.64 39949608786.80 40059657198.77 40201484047.80 40250776495.87 40573281106.80 42148986991.64 42152937187.80 42831019478.80 42988233554.80 43059266230.68 43104399792.80 4339015994.72  45221239098.77 4578105780.87  46667034811.88 47301565754.72 47574158293.10348875108661.72 49323180613.88 49939022964.87 5005083474.80  50093581626.72 50362574674.80 51843638820.87 51898260084.87 52136437230.77 52567164907.72 52567164907.77 52567164907.80 52962496826.72 53898698513.87 53900795701.10354164510851.77 55360109666.10355539254254.77 55844476331.10357216550738.80 58656190123.10358882439482.72 59176389614.77 59314923118.72 59798990343.10361390257579.10261501563758.77 61581656914.80 62583080755.80 64182077138.80 64514610859.10365270743723.10265764202298.72 6604583028.87  66490360461.72 6661595409.87  6663692597.102 66747928658.80 67081926311.77 67323875956.87 67440430906.72 6788186404.87  67943285742.77 68303855698.80 8699632657.87  8701729845.103 9193493108.87  9665066293.103 9667163409.87  00000900:00;00<00=00>00C00H00I00J00S00T00U00V00W00`00i00j00m01:01G01H01K01L01M01N01W01`01a01b01c01d01e01f01o02002=02J02S02\02e02n02o03003903B03K03X03e03n03o04004=04J04N04W04X04a05005?05C05D05E05I05M05P05Q05Z05[05\05]05^05b05f05o06806906B06K06Q06W06\06e06i06m06n07307407707807G07P07_07`07i07j08308408508>08?08@08A08B08O08\08]08f08o09009909:09;09D09J09K09L09U09^09_09h09i09j09k09l09m0::0:G0:P0:Q0:R0:S0:T0:]0:f0;30;@0;A0;N0;[S2LO4LOLOSFFSSS3HspS3HspSFS2LO4LOLOSSFSS2LO4LOLOS2LO4LOLOSS1HS2LO4LOLO3HspS2LO4LOLO3HspSS1HSSSS2LO4LOLOS2LO4LOLOSSSSSSS2LO4LOLOSS2LO4LOLO3HspS2LO4LOLO3HspS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLOSSS2LO4LOLOS2LO4LOLOS2LO4LOLOS2LO4LOLO3HspS2LO4LOLO3HspS2LO4LOLOSSS2LO4LOLO3HspS2LO4LOLO3HspS2HBS2LO4LOLOSS2LO4LOLOS2LO4LOLO3RSP1HS2LO4LOLO3RSP1HS2HtSSS2HtS2HtS1HSS2LO4LOLOSSSSS2LOS2LOS2LO4LOLOS2LO4LOLOSS2LO4LOLOS2LO4LOLOS4LOLOS4LOLOS3RSPS2LO4LOLOS2LOS2HBSS3RSPSS1HSS2LO4LOLO3Hsp1HS2LO4LOLOS2LO4LOLO3Hsp1HSS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOSSSSS2LO4LOLO3HspS2LO4LOLO3HspSS2LO4LOLOS2LO4LOLOSS2LO4LOLOSSS2LO4LOLOS2Ht1KFSS2LO4LOLOS2LO4LOLOSS2LO4LOLOFSSSSS2LO4LOLO3HspS2LO4LOLO3HspS2LO4LOLOSSSSS2LO4LOLOS2LO4LOLOS2LO4LOLO3HspS2LO4LOLO3HspSS2LO4LOLO3HspS2LO4LOLO3Hsp".
carve_frame 16%nat ST.
do 6 lstep.
replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
lstep. lstep.
amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
lstep. if_false. amo_step. lstep. if_false.
lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
steps_to 0x14dcc%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AX : atx_state reg mx) by (exact (conj (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 X7)))))) CB)) end.
clear X1 X2 X3 X4 X5 X6 X7 CB.
call_sp (pfuncs_on_exit_spec reg);
[ exact ST | exact AX | exact LCH | exact MI | lia | lia | ].
astep.
call_sp plibc_exit_fini_spec;
[ hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | lia | lia | ].
astep.
unfold pexit_prefix_post, PATX. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section ExitProof.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.
#[using="stdio_exit_spec"] Lemma exit_spec : forall (reg : bool) (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
(cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
rw_cells rsegs m PEXIT_LOCK [C4 z64] ->
rw_cells rsegs m PGOT_FINI [C8 (Z_to_bv 64 0x1db20); C8 (Z_to_bv 64 PFINI_ARRAY)] ->
rw_cells rsegs m PFINI_ARRAY [C8 (Z_to_bv 64 0x12ff8)] ->
rw_cells rsegs m PFINALIZED [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m PGOT_CXA [C8 (Z_to_bv 64 0x14e94); C8 z64] ->
rw_cells rsegs m PDSO_HANDLE [C8 (Z_to_bv 64 PDSO_HANDLE)] ->
rw_cells rsegs m 0x4f1c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_state reg m ->
rw_cells rsegs m 0x4f5f0 [C8 z64] -> rw_cells rsegs m 0x4f5e0 [C8 z64] ->
rw_cells rsegs m 0x1edc8 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x1ecd8 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 guard] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x50000 <= lo)%Z ->
(bv_unsigned sp < 2^47)%Z ->
implM rsegs (Driver.exit_model (io_S get_so set_so) code) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PEXIT_ENTRY) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AX OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO SP47.
unfold got_ssp, ssp_guard in GG, GU.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
unfold file_cells in SOF1, SEF1.
unfold Driver.exit_model.
eapply (implM_bind rsegs _ _ s
(fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
ms' = MS (mkR (Z_to_bv 64 0x1501c) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x1501c) fc None m' (seg_rom rsegs))).
-
change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
unfold implM. iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "01[0?10429640106.10811494365812.10912496013604.10912843408052.1081343986644.107 14453598623.10914629696911.10915330208399.1081740767631.109 18120602740.10918316487071.10918369699793.10918568930932.10918661306695.10719510624548.10919904115748.10920422406836.10821549202591.1092168467805.108 22205432479.10822265834895.10922494168785.10922829363409.10823237574068.10923429741291.89 2363895412.107 24174289332.10925079341492.1092537045172.109 25697341876.10925897970079.10925967737268.10926344250387.13026686445521.10928104924788.10928644957732.10828675273764.10929886489716.10930616965329.10830635114383.1093154984228.109 32349584564.10933395433764.10734120870559.10834192586868.10934386371700.10934836214175.10934909279631.1093525607222.111 3609162420.109 36104482420.10936303827359.10937581467279.1093782168735.109 38043145682.89 38101937444.1093867822372.109 38772558031.10839107297935.10939116998353.10940110889631.10940364435343.1094124700881.109 42148696048.10842150807271.89 4578105780.107 46408991780.10947085762447.10947420327092.10947719393716.10948238586527.10850985523492.10951233566673.10751428495519.10951843638820.10851898260084.10851954741364.10952588068388.10952643152287.10953155210193.10953879884212.10953987397585.10953994943185.10954489906804.10955846573455.10955935229905.10957616802207.10758654092943.10961388160399.10762838276255.10963092633204.10963151259601.10963910239887.10964139408337.10964516707983.1096504875729.109 65123883423.10965268646543.10865742995665.1086604583028.109 6788186404.109 68246572324.10968396593567.1096855207889.109 8340255156.109 9120284623.109 9193493108.108 00000400500600700800900:00;00<00=00>00G00H00I00J00K00L00M00S00T00U00^00g00h00l00m00n00o01001101201301401=01>01?01@01A01J01K01L01M01N01O01P01Q01R01S01c01d01e01f01g01h01l01m01n01o02002902:02;02D02J02P02Q02R02S02T02U02V02W02`02a02b02c02d02e02f02o03003903B03C03D03M03N03O03P03Q03R03[03\03e03f03o04004104:04;04<04=04>04G04H04I04JS2LOSSSFSSSSSSS2LO4LOLOSFSSSSS4SP47SSS2LO4LOLOS2LO4LOLOSS2HtSSSSSSSSS2LO4LOLOSSSSS2LO4LOLOSSSSFSSSSS2LO4LOLO4SP471HSSSSSS2LOSSFSS2LO4LOLOSSS2LO4LOLOS4LOLOS4LOLOSSSSSSSS2LO4LOLOSSSSSSS2LO4LOLOSS2LO4LOLOS2LO4LOLOSSS2LO4LOLOSSSSSS2LO4LOLOSS2LO4LOLOFS2LO4LOLOSSS2LO4LOLOSSSSS2LO4LOLOSFS".
call (pexit_prefix_spec reg); [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact AX | exact MI
| reflexivity | reflexivity | lia | lia | lia | ].
name_sp sp (-16)%Z.
pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM, got_ssp, ssp_guard, GLOBALS_TOP in SE.
apply evt_done. eapply impl_epost_mono; [eapply SE|].
all: lazymatch goal with
| |- forall _, _ =>
intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
replace (ret_pc (Z_to_bv 64 0x1501c)) with (Z_to_bv 64 0x1501c) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
repeat eexists; cbv delta [mkR]; reflexivity
| |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
| |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
| |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
end.
-
clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
intros [] s' ms' PO. destruct_exs PO. subst ms'.
apply implM_sys. do 4 lstep. step_ecall.
split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ExitProof.
