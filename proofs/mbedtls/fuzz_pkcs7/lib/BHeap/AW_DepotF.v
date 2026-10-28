(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon AW_MmapDie AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DepotF () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.dblocks"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "ARUN_1.DepotF.fin_post"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_NODES"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dput_frame"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8ro"; "ARUN_1.dstatics"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_MAP1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_BI_CREATE"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "ARUN_1.DepotF.asc_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_N"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_TLM_CREATE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_MUR1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_MUR2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_MUR3"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dtab"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dmap1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnodes"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dwf"; "ARUN_1.DepotF.hit_post"; "ARUN_1.DepotF.headA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"].

Section ARUN_1. Context {hAR : arun}.
Definition dstatics (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "(0.(1.$2.O1.$3.(4.$5.(6.(7.&40.$8.))(9.$5.)))(1.$2.O1.(:.$8.+?0.)(4.$5.(;.(7.&40.=))(9.$5.))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38718667527.2L42465160097.2000001002SS". (* [comment removed for export] *)
#[using="Type"] Lemma mod64_mod32 : forall x, (x mod 2 ^ Z.of_N 64) mod 2 ^ 32 = x mod 2^32.
Proof.
  intros x. change (2 ^ Z.of_N 64) with (2^32 * 2^32).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma le4_low32 : forall a t, 0 <= a < 2^32 -> 0 <= t -> le4 (Z_to_bv 64 (a + t * 4294967296)) = le4 (Z_to_bv 64 a).
Proof.
  intros a t Ha Ht. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite <- (CellsX.Z_to_le_bytes_mod 4 ((a + t * 4294967296) mod 2 ^ Z.of_N 64)), <- (CellsX.Z_to_le_bytes_mod 4 (a mod 2 ^ Z.of_N 64)).
  f_equal. change (8 * Z.of_nat 4) with 32. rewrite !mod64_mod32. change (2^32) with 4294967296.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Section DepotF.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition fin_post (SP : Z) (gp tp s10 s11 t4 t5 t6 : word) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra : word)
      (F : bvmap 5 word) (fc : bv 32) (lo id h v bi NODE B tf' : Z) (bl : list Z) (alloc : word) (W : list (Z * Z)) (m0 : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Lms',$<.(=.(>.&40.)Lx5,(>.&40.)(=.(>.&40.)Lx6,(>.&40.)(=.(>.&40.)Lx7,(>.&40.)(=.(>.&40.)Lx11,(>.&40.)(=.(>.&40.)Lx12,(>.&40.)(=.(>.&40.)Lx13,(>.&40.)(=.(>.&40.)Lx14,(>.&40.)(=.(>.&40.)Lx15,(>.&40.)(=.(>.&40.)Lx16,(>.&40.)(=.(>.&40.)Lx17,(>.&40.)(=.(>.&40.)Lx28,(>.&40.)(=.(>.&40.)Lsidw,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(0.(10.$<.R>.(11.(12.O?.(7.&40.O21.)O20.O1?.R=.R<.R;.O19.O18.(7.&40.O;.)R:.R9.R8.R7.R6.R5.R4.O17.O16.O15.O14.O13.O12.O11.O10.O1>.O1=.R3.O1<.O1;.O1:.)O>.(13.O?.)O=.(14.(>.&40.))R1.(15.$2.)))(0.(16.O2.O1.R1.)(0.(17.$2.O1.R1.)(0.(18.$2.R1.)(0.(19.$2.R1.O7.(4.$5.(6.(7.&40.O:.))(4.$5.(;.(7.&40.O9.))(4.$5.(;.R2.)(9.$5.)))))(0.(19.$2.R1.(:.$1:.(1;.+4.O8.))(4.$5.(;.(7.&40.O;.))(9.$5.)))(0.(19.$2.R1.$1<.(4.$5.(6.(7.&40.O5.))(4.$5.(6.O3.)(9.$5.))))(0.(1=.VhAR,R1.O4.)(0.(1>.$2.R1.O6.(:.O6.(1?.+2.+17.)))(1>.$2.R1.O<.O21.)))))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma fin_post_pre : ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "PSP,$20.Pgp,(>.&40.)Ptp,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pq0,(>.&40.)Pq1,(>.&40.)Pq2,(>.&40.)Pq3,(>.&40.)Pq4,(>.&40.)Pq5,(>.&40.)Pq6,(>.&40.)Pq7,(>.&40.)Pq8,(>.&40.)Pq9,(>.&40.)Pqra,(>.&40.)PF,(21.&5.(>.&40.))Pfc,(>.&20.)Plo,$20.Pid,$20.Ph,$20.Pv,$20.Pbi,$20.PNODE,$20.PB,$20.Ptf',$20.Pbl,(22.$20.)Palloc,(>.&40.)PW,(22.$23.)Pm0,P,(>.&40.)(?.(>.&8.))Pm1,P,(>.&40.)(?.(>.&8.))Pms',$<.P,(16.R4.R3.R2.)P,(17.$2.R4.R3.)P,(24.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R4.R3.)(24.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R4.)")
(* [comment removed for export] *).
  Proof.
    intros until ms'. intros MU WM PT. unfold fin_post in *.
    ddestruct PT as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & sidw & m' & E & MU' & WM' & REST).
    dexists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, sidw, m'. split; [exact E|].
    split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']| exact REST].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0180@L12284855253.105L12570334085.105L1505402628.127 L15566607407.105L18991450597.105L1911314902.132 L19605101073.13 L19671342879.127L20269086718.105L211260964.7    L21957069652.127L2237532074.127 L22414635927.105L23016414597.105L23536198935.9  L23538013352.13 L24022352673.0  L25204004431.127L26125025108.127L27839757129.127L27848128723.105L28444717228.6  L28573892092.9  L30249441554.10 L30249441554.8  L31338182664.105L33246818934.127L35024725547.132L35159332395.102L35578841428.127L370777076.128  L38236103095.105L38244508205.127L396493423.127  L39759977813.6  L42151634452.6  L42738512639.105L44825135454.104L45083556926.6  L46934459684.105L47499685389.128L48280646757.105L50123849719.127L50645342408.127L50672502943.128L53525101975.105L55797156072.132L56764921988.105L57628700040.9  L58804882593.10 L58807237914.8  L58807237918.7  L58807237918.9  L59538028438.127L60200701487.105L60283885618.13 L60299090200.132L6313715448.105 L63200569965.105L65459068296.105L66224054574.127L66969711777.0  L6722037640.105 L67786092284.8  L67786594096.102L68573722777.9  L7385228992.105 L7503232206.105 L8806423751.9   L9227342469.105 L9541060277.128 L9563568548.105 00000100V01;01\02@02A02k03P03Q03j04K04L05405Y06806i06j06k07L08008T08c09@09g0:H0:m0;U0<=0<^0=?0=`0>D0>h0?I0?Q0?Y0@@0@d0A00A10AY0B=0Bb0Bc0CH0D00D10DY0E60E^0F;0FT0G30G[0H<0Hn0IS0J:0J_0KD0Ke0Kf0Kg0LH0Li0MH0Mi0NJ0Nk0OP0P10P2FS3hAR2SP4size5start4NODE2bl2ss2S03SPAS3hAR2SP4size5start4NODE2bl2ss2S03SPHS3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP4size5start2lo4NODE2bl2ss2S0FS3hAR2SP5start2lo2bl5LOIMG2B11A1n2H12H22H3S3hAR2SP4size5start4NODE2bl2ss2S03SPAFS3hAR2SP2lo4NODE2N05LOIMGS3hAR2SP4size5start4NODE2bl2ss2S0FS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLS3hAR2SP4size5start4NODE2bl2ss2S03SPAS3hAR2SP2lo2bi4NODE2BI2N05LOIMGS3hAR2SP5start2lo2bi4NODE2bl2BI5NBSEP5LOIMG2B02B1SFS3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP4size5start2lo4NODE2bl2ss2S0S3hAR2SP4size5start2lo4NODE2bl2ss2S0S3hAR2SP2lo3SPLS2SP5start2lo2bi4NODE2bl1x2HxS3hAR2SP5start2lo2bi2bl2BI5LOIMG3SPL2B0S3hAR2SP5start2lo2bl5LOIMG3SPL2B0S3hAR2SP4size5start4NODE2bl2ss2S03SPHS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLS3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP4size5start2lo4NODE2bl2ss2S0S3hAR2SP4size5start2lo4NODE2bl2ss2S0S3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SPS3hAR2SPS3hAR2SP2TR4size5start4NODE2bl2ss2S02T0S3hAR2SP4size5start4NODE2bl2ss2S02JLS3hAR2SP3SPHFS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLS3hAR2SP4size5start2lo4NODE2bl2ss2S0S3hAR2SP4size5start4NODE2bl2ss2S03SPHFS3hAR2SP4size5start4NODE2bl2ss2S03SPHS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLFS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLS2SP5start2lo2bi4NODE2bl1x2HxS3hAR2SP5start2lo4NODE2bl5NBSEP5LOIMG2B1S3hAR2SP2lo4NODE2N15LOIMG3SPLS3hAR2SP2lo4NODE2N05LOIMGS3hAR2SP2lo2bi4NODE2BI2N05LOIMGS3hAR2SP4size5start2lo4NODE2bl2ss2S03SPLS3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP5start2lo4NODE2bl2N02N15NBSEP5LOIMG3SPL2B1S3hAR2SP4size5start4NODE2bl2ss2S03SPHS3hAR2SP2TR4size5start4NODE2bl2ss2S02T0S3hAR2SP4size5start4NODE2bl2ss2S03SPHS3hAR2SP4size5start4NODE2bl2ss2S03SPHS3hAR2SP4size5start4NODE2bl2ss2S0SFS3hAR2SP5start2lo2bl5LOIMG3SPL2B0S3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP2lo2bi4NODE2BI2N05LOIMGS3hAR2SP4size5start4NODE2bl2ss2S0S3hAR2SP4size5start4NODE2bl2ss2S0S2SP5start2lo2bi4NODE2bl3SPL1x2HxS3hAR2SP4size5start4NODE2bl2ss2S03SPAS3hAR2SP4size5start4NODE2bl2ss2S0F". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma seg_tail : ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Pgp,(>.&40.)Ptp,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pa2,(>.&40.)Pa4,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Pa1,(>.&40.)Pa3,(>.&40.)Pa5,(>.&40.)Palloc,(>.&40.)Ppkw,(>.&40.)Psid,(>.&40.)Plockw,(>.&40.)Plnkw,(>.&40.)Pq0,(>.&40.)Pq1,(>.&40.)Pq2,(>.&40.)Pq3,(>.&40.)Pq4,(>.&40.)Pq5,(>.&40.)Pq6,(>.&40.)Pq7,(>.&40.)Pq8,(>.&40.)Pq9,(>.&40.)Pqra,(>.&40.)PSP,$20.PF,(21.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))PTR,$20.Psize,$20.Ptag,$20.Pstart,$20.Plo,$20.Ph,$20.Pv,$20.Pbi,$20.Pid,$20.PNODE,$20.Pbl,(22.$20.)Pss,(22.(>.&8.))Pfr0,(22.(>.&8.))Pfr1,(22.(>.&8.))Zcount,$20.(:.R=.+1.)Zj,$20.(25.R<.(1?.+2.+14.))ZB,$20.(26.R6.R1.)ZP,$20.(:.R1.(1;.+8.(27.R>.(1?.+2.+14.))))ZW,(22.(28.$20.$20.))(4.(28.$20.$20.)(29.$20.$20.R>.R16.)(4.(28.$20.$20.)(29.$20.$20.$1<.(:.(:.$1<.+10.)(1;.+10.+1000.)))(4.(28.$20.$20.)(29.$20.$20.R2.(:.R2.(1?.+2.+17.)))(4.(28.$20.$20.)(29.$20.$20.R9.(:.R9.+10.))(4.(28.$20.$20.)(29.$20.$20.(:.$1:.(1;.+4.R;.))(:.(:.$1:.(1;.+4.R;.))+4.))(9.(28.$20.$20.)))))))P,(0.(2:.+1.R12.)(2:.R12.+1>.))P,(0.(2:.=R12.)(2;.R12.+100.))P,(2:.=R12.)P,(2;.(:.R13.R8.)(1?.+2.+20.))P,(10.$20.R8.(25.(2<.(:.R14.R9.)+1.)(1?.+2.+14.)))P,(2;.R9.(2=.(2>.$20.R>.)))P,(0.(2:.=R11.)(2;.R11.(1?.+2.+1?.)))P,(0.(2:.=R14.)(2;.R14.(1?.+2.+1?.)))P,(0.(2:.=R14.)(2;.R14.(1?.+2.+14.)))P,(0.(2:.=R17.)(2;.R17.(1?.+2.+40.)))P,(2:.+65?000.R14.)P,(2:.(:.R15.+10.)(2?.VhAR,))P,(10.$20.(27.R16.+10.)=)P,(30.VCS,R17.+10.)P,(31.(2:.(:.R18.+10.)(26.R17.(25.R1>.(1?.+2.+14.))))(2:.(:.(26.R17.(25.R1>.(1?.+2.+14.)))(1?.+2.+17.))R18.))P,(19.$2.R23.(:.R26.-=0.)(4.$5.(6.(7.&40.R1?.))(4.$5.(6.(7.&40.R1<.))(4.$5.(6.(7.&40.$32.))(4.$5.(6.(7.&40.R1=.))(4.$5.(6.(7.&40.(:.$1:.(1;.+4.R1;.))))(4.$5.(6.(7.&40.R19.))(4.$5.(6.(7.&40.R19.))(4.$5.(6.(7.&40.+892>4.))(9.$5.))))))))))P,(19.$2.R24.(:.R27.-90.)(4.$5.(33.#8.R16.)(9.$5.)))P,(19.$2.R25.(:.R28.-88.)(4.$5.(6.R37.)(9.$5.)))P,(19.$2.R26.(:.R29.-80.)(4.$5.(6.(7.&40.=))(4.$5.(6.(7.&40.+897<8.))(9.$5.))))P,(34.R27.R2:.R1:.R26.(:.R25.(1;.R24.(1?.+2.+20.)))R2;.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.)P,(1.$2.R28.(:.R2;.-68.)(4.$5.(6.(7.&40.R27.))(4.$5.(;.(7.&40.R26.))(4.$5.(;.(7.&40.R25.))(9.$5.)))))P,(19.$2.R29.$1<.(4.$5.(6.(7.&40.(:.R25.R1:.)))(4.$5.(6.R3<.)(9.$5.))))P,(1=.VhAR,R2:.R1?.)P,(19.$2.R2;.R21.(4.$5.(6.(7.&40.R25.))(4.$5.(;.R3:.)(4.$5.(;.R3<.)(9.$5.)))))P,(19.$2.R2<.(:.$1:.(1;.+4.R24.))(4.$5.(;.R3<.)(9.$5.)))P,$35.P,(36.$2.R2>.R2=.R22.)P,(10.$20.(2=.(2>.(>.&8.)R23.))(1;.+8.R2=.))P,(1>.$2.R30.R1?.(:.R1?.(1?.+2.+17.)))P,(30.VCS,R20.(1?.+2.+17.))P,(37.R32.)P,(2:.R36.R32.)P,(2:.(:.R33.+?0.)(1?.+2.+3?.))P,(30.VCS,R34.+?0.)P,(1>.$2.R36.R31.(:.R39.-=0.))P,(2:.(2?.VhAR,)R32.)P,(2:.R33.(2<.R3;.+240.))P,(2:.R3<.(1?.+2.+3>.))P,(10.$20.(27.R3=.+10.)=)P,(30.VCS,R36.(2<.R3>.R36.))P,(18.$2.R3<.)(38.$2.VAL,VCS,(24.R40.R62.R61.R60.R5?.R5:.R59.R58.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R3?.R3>.R38.R34.R37.R36.R35.R33.R2<.(:.R39.R2>.)R32.R50.R2:.R3=.)(11.(12.(7.&40.+8701<.)(7.&40.(:.R40.-=0.))R62.R61.R5>.R5=.R5<.(7.&40.(:.R40.-88.))(7.&40.$1<.)(7.&40.R2;.)R53.R57.R52.R56.R51.R55.R54.(7.&40.R2>.)(7.&40.(:.R40.-68.))(7.&40.R3;.)(7.&40.R3:.)(7.&40.+????.)(7.&40.R34.)(7.&40.$39.)(7.&40.R36.)R60.R5?.R5;.R5:.R59.R58.)R3?.(7.&40.+8701<.)R3>.(14.(>.&40.))R3=.(15.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp s10 s11 t0 t1 t2 t3 t4 t5 t6 a2 a4 a6 a7 a1 a3 a5 alloc pkw sid lockw lnkw q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra SP F fc m
      TR size tag start lo h v bi id NODE bl ss fr0 fr1 count j B P W
      SZ TG S0 S1 SJ JL ID VB BI HR N0 N1 NAL NCS NBSEP
      FRS F1 F2 F3 FRP ARGS SSX DB NC TC _ HS LS STB BCS [GOTF CF240] T0 T1 TCS ST LOIMG SPL SPH SPA SCS MI.
    facts. subst j B P count W.
    assert (JB : 0 <= start / 2^20) by (apply Z.div_pos; lia).
    assert (BB : 0x65f000 <= sblk bl (start / 2^20) /\ sblk bl (start / 2^20) + 2^23 <= ACEIL).
    { unfold sblk. ddestruct DB as (_ & DBF & _).
      pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN.
      ddestruct (proj1 FN DBF (Z.to_nat (start / 2^20)) 0 ltac:(lia)) as (X0 & X1 & _). split; assumption. }
    destruct BB as [B0 B1].
    replace (SP + -208) with (SP + -144 + -64) in * by lia.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (ss_store_B AL IMG ALWF CS CSOK gp tp t0 t1 t2 _ _ _ _ s10 s11 t3 t4 t5 t6 a2 a4 a6 a7 a1 a3 a5 alloc pkw
                (Z_to_bv 64 0x0892e4) (Z_to_bv 64 NODE) (Z_to_bv 64 NODE) (Z_to_bv 64 (A_DEP + 4 * bi)) (Z_to_bv 64 h) (Z_to_bv 64 A_DEP_NODES) (Z_to_bv 64 v)
                (SP + -144) F fc m m (SP + -104) (SP + -136) TR size tag start lo bl ss);
        try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
      all: eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x16 & x17 & x28 & pkw' & m2 & -> & MU2 & WM2 & MI2 & SSX2 & DB2 & PK2 & STB2 & ST2)).
    replace (ret_pc (Z_to_bv 64 0x0892e4)) with (Z_to_bv 64 0x0892e4) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (DJ2 : forall A n, lo <= A -> SP + -136 + 8 <= A \/ A + n <= SP + -136 -> SP + -144 <= A ->
              A + n <= 2^63 -> disjoint_from [(lo, SP + -144); (SP + -136, SP + -136 + 8); (A_SS, A_SS + 16 + 16 * 4096); (sblk bl (start / 2^20), sblk bl (start / 2^20) + 2 ^ 23)] A n).
    { intros A n H1 H2 H3 H4. unfold A_SS. cbn [disjoint_from]. clear - H1 H2 H3 H4 B1 LOIMG. lia. }
    assert (F1' : rw_cells asegs m2 (SP + -144) [CB 8 fr1]) by (eapply rw_cells_transport; [exact F1| exact MU2| exact WM2| apply DJ2; cbn [cells_size csize Nat.add]; lia]).
    assert (F3' : rw_cells asegs m2 (SP + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x0897c8)]) by (eapply rw_cells_transport; [exact F3| exact MU2| exact WM2| apply DJ2; cbn [cells_size csize Nat.add]; lia]).
    assert (FRP' : dput_frame m2 SP fr0 TR (size + tag * 2^32) qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9).
    { eapply rw_cells_transport; [exact FRP| exact MU2| exact WM2| apply DJ2; cbn [cells_size csize Nat.add]; clear - SPL SPH LOIMG; lia]. }
    assert (NC' : rw_cells asegs m2 NODE [C8 (Z_to_bv 64 h); C4 lnkw; C4 sid]).
    { eapply rw_cells_transport; [exact NC| exact MU2| exact WM2|]. unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear - N0 N1 B0 B1 LOIMG SPL NBSEP.
      lia. }
    assert (TC' : rw_cells asegs m2 (A_DEP + 4 * bi) [C4 lockw]).
    { eapply rw_cells_transport; [exact TC| exact MU2| exact WM2|]. unfold A_SS, A_DEP; cbn [disjoint_from cells_size csize Nat.add]. clear - BI B0 LOIMG SPL. lia. }
    assert (GOTF' : ro_cells asegs m2 A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]) by (eapply ro_cells_transport; [exact GOTF| exact MU2| unfold A_SS, A_GOT_CFLAGS; cbn [disjoint_from cells_size csize Nat.add]; clear - B0 LOIMG SPL; lia]).
    assert (CF240' : ro_cells asegs m2 (A_CFLAGS + 240) [C4 (Z_to_bv 64 0)]) by (eapply ro_cells_transport; [exact CF240| exact MU2| unfold A_SS, A_CFLAGS; cbn [disjoint_from cells_size csize Nat.add Z.add]; clear - B0 LOIMG SPL; lia]).
    clear F1 F3 FRP NC TC GOTF CF240.
    (* [comment removed for export] *)
    replace (SP + -136) with (SP + -112 + -24) in PK2 by lia. replace (SP + -128) with (SP + -112 + -16) in F3' by lia.
    replace (SP + -144) with (SP + -112 + -32) by lia. replace (SP + -144) with (SP + -112 + -32) in F1', ST2 by lia.
    eapply evtA_cut.
    { eapply (dnode_store_B AL IMG ALWF CS CSOK (Z_to_bv 64 0x0897c8) gp tp x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 NODE)
                (Z_to_bv 64 (A_DEP + 4 * bi)) (Z_to_bv 64 h) (Z_to_bv 64 A_DEP_NODES) (Z_to_bv 64 v)
                (Z_to_bv 64 0xffff) (Z_to_bv 64 id) (Z_to_bv 64 A_DEP_MAP1) (Z_to_bv 64 v) s10 s11 x28 t4 t5 t6
                x11 x12 x13 x14 a5 x16 x17 x10 (Z_to_bv 64 h) sid pkw' lnkw (SP + -112) F fc m2 m2 NODE lo fr1 []);
        try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
      all: eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y0 & y1 & sidw & m3 & -> & MU3 & WM3 & MI3 & NC3 & ST3)).
    replace (ret_pc (Z_to_bv 64 0x0897c8)) with (Z_to_bv 64 0x0897c8) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (FRP3 : dput_frame m3 SP fr0 TR (size + tag * 2^32) qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9).
    { eapply rw_cells_transport; [exact FRP'| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL SPH LOIMG N1. lia. }
    assert (TC3 : rw_cells asegs m3 (A_DEP + 4 * bi) [C4 lockw]).
    { eapply rw_cells_transport; [exact TC'| exact MU3| exact WM3|]. unfold A_DEP; cbn [disjoint_from cells_size csize Nat.add]. clear - BI N0 LOIMG SPL. lia. }
    assert (SSX3 : rw_cells asegs m3 A_SS [C8 (Z_to_bv 64 (start + (size + 1))); C8 alloc]).
    { eapply rw_cells_transport; [exact SSX2| exact MU3| exact WM3|]. unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear - N0 LOIMG SPL. lia. }
    assert (STB3 : stk asegs m3 (sblk bl (start / 2^20)) (sblk bl (start / 2^20) + 2^23)).
    { eapply stk_transport_disjoint; [exact STB2| exact MU3| exact WM3|]. cbn [disjoint_from]. clear - NBSEP B1 LOIMG SPL. lia. }
    assert (DB3 : dblocks m3 bl).
    { eapply (dblocks_transport _ m2 m3 bl DB2 MU3 WM3). unfold A_SS; cbn [disjoint_from]. clear - N0 LOIMG SPL. lia. }
    clear FRP' TC' SSX2 STB2 DB2 NC' DJ2 F1' F3'.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dput_ins_C AL IMG ALWF CS CSOK gp tp s10 s11 x5 x6 x7 x28 t4 t5 t6 y0 y1 x12 x13 x14 a5 x16 x17
                (Z_to_bv 64 h) sidw lockw lnkw q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra SP F fc m3 m3 h bi v id NODE TR (size + tag * 2^32) lo fr0 []);
        try eassumption; try lia; try apply munch_refl; try apply wmono_refl. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m4 & -> & MU4 & WM4 & MI4 & NC4 & TC4 & ST4)).
    apply evtA_done. unfold fin_post. deexists 13.
    split; [reflexivity|].
    split. { (* [comment removed for export] *)
      eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
      eapply munch_trans. { eapply munch_weaken; [| exact MU3]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
      eapply munch_weaken; [| exact MU4]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
    split. { eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3| exact WM4]. }
    split; [exact MI4|]. split; [exact NC4|]. split; [exact TC4|].
    split. { eapply rw_cells_transport; [exact SSX3| exact MU4| exact WM4|]. unfold A_SS, A_DEP; cbn [disjoint_from cells_size csize Nat.add]. clear - N0 BI LOIMG SPL. lia. }
    split. { eapply (dblocks_transport _ m3 m4 bl DB3 MU4 WM4). unfold A_SS, A_DEP; cbn [disjoint_from]. clear - N0 BI LOIMG SPL. lia. }
    split. { eapply stk_transport_disjoint; [exact STB3| exact MU4| exact WM4|]. unfold A_DEP; cbn [disjoint_from]. clear - NBSEP B0 B1 BI LOIMG SPL. lia. }
    exact ST4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L1469252369.27 L18926591958.27L25933794721.27L39829202612.27L42560853854.27L42653672845.27L45332766828.2700000800900>00G00W00`00dS3tag2TGSS3tagS4size2SZS4size3tag2SZ2TGS4size2SZS2SP". (* [comment removed for export] *)
  #[using="Type"] Lemma args_view : ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Pm,P,(>.&40.)(?.(>.&8.))PSP,$20.Pfr,(22.(>.&8.))PTR,$20.Psize,$20.Ptag,$20.Pqra,(>.&40.)Pq0,(>.&40.)Pq1,(>.&40.)Pq2,(>.&40.)Pq3,(>.&40.)Pq4,(>.&40.)Pq5,(>.&40.)Pq6,(>.&40.)Pq7,(>.&40.)Pq8,(>.&40.)Pq9,(>.&40.)P,(0.(2:.+1.R=.)(2:.R=.+1>.))P,(0.(2:.=R=.)(2;.R=.+100.))P,(0.(2:.=R10.)(2;.R10.(1?.+2.+40.)))P,(34.R14.R13.R12.R11.(:.R10.(1;.R?.(1?.+2.+20.)))R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(1.$2.R15.(:.R14.-68.)(4.$5.(6.(7.&40.R12.))(4.$5.(;.(7.&40.R11.))(4.$5.(;.(7.&40.R10.))(9.$5.)))))")
(* [comment removed for export] *).
  Proof.
    intros m SP fr TR size tag qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 SZ TG TRR FR. unfold dput_frame in FR.
    apply (proj1 (rw_cells_app asegs m (SP + -112) [CB 8 fr] _)) in FR. destruct FR as [_ FR].
    apply (proj1 (rw_cells_app asegs m _ [C8 (Z_to_bv 64 TR); C8 (Z_to_bv 64 (size + tag * 2^32))] _)) in FR. destruct FR as [FR _].
    cbn [cells_size csize Nat.add] in FR. replace (SP + -112 + Z.of_nat 8) with (SP + -104) in FR by lia.
    apply (rw_cells_reshape asegs m (SP + -104) _ [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 tag)]) in FR;
      [| cbn; tauto | ].
    2:{ cbn [cells_bytes cbytes app]. rewrite (le8_split4 (Z_to_bv 64 (size + tag * 2^32))), unsigned_lit by lia.
        change (2^32) with 4294967296. replace ((size + tag * 4294967296) / 4294967296) with tag by (rewrite Z.div_add, Z.div_small by lia; lia).
        rewrite (le4_low32 size tag) by lia.
        rewrite <- !app_assoc. reflexivity. }
    destruct FR as [CA _]. exact CA.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition asc_post (SP : Z) (gp tp s10 s11 t4 t5 t6 : word) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra : word)
      (F : bvmap 5 word) (fc : bv 32) (lo id h v bi NODE TR size tag start : Z) (bl : list Z) (alloc : word)
      (fr0 : list byte) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Lms',$<.(=.(>.&40.)Lx5,(>.&40.)(=.(>.&40.)Lx6,(>.&40.)(=.(>.&40.)Lx7,(>.&40.)(=.(>.&40.)Lx12,(>.&40.)(=.(>.&40.)Lx14,(>.&40.)(=.(>.&40.)Lx16,(>.&40.)(=.(>.&40.)Lx17,(>.&40.)(=.(>.&40.)Lx28,(>.&40.)(=.(>.&40.)Lpk,(>.&40.)(=.(>.&40.)Lsid,(>.&40.)(=.(>.&40.)Llnkw,(>.&40.)(=.(>.&40.)Lbk,(>.&40.)(=.(22.(>.&8.))Lfr1,(22.(>.&8.))(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))Zcount,$20.(:.O8.+1.)(0.(10.$<.R10.(11.(12.(7.&40.+871=<.)(7.&40.(:.O24.->0.))O23.O22.R?.R>.R=.(7.&40.O6.)(7.&40.$1<.)(7.&40.(:.(:.$1<.+10.)(1;.+10.(25.O6.(1?.+2.+14.)))))(7.&40.$1<.)R<.(7.&40.(:.O24.-88.))R;.(7.&40.R1.)R:.R9.(7.&40.R1.)(7.&40.(:.O24.-68.))(7.&40.O8.)(7.&40.O7.)(7.&40.+????.)(7.&40.O>.)(7.&40.$39.)(7.&40.O<.)O21.O20.R8.O1?.O1>.O1=.)O11.(7.&40.$3:.)O10.(14.(>.&40.))R2.(15.$2.)))(0.(16.O2.O1.R2.)(0.(17.$2.O1.R2.)(0.(18.$2.R2.)(0.(19.$2.R2.(:.O24.->0.)(4.$5.(6.(7.&40.(:.O24.-88.)))(4.$5.(6.(7.&40.+8701<.))(9.$5.))))(0.(19.$2.R2.(:.O24.-=0.)(4.$5.(6.(7.&40.O6.))(9.$5.)))(0.(19.$2.R2.(:.O24.-<8.)(4.$5.(6.(7.&40.O<.))(4.$5.(6.(7.&40.$32.))(4.$5.(6.(7.&40.O=.))(4.$5.(6.(7.&40.(:.$1:.(1;.+4.O;.))))(4.$5.(6.(7.&40.O:.))(4.$5.(6.(7.&40.O:.))(4.$5.(6.(7.&40.+892>4.))(9.$5.)))))))))(0.(19.$2.R2.(:.O24.-90.)(4.$5.(33.#8.R3.)(9.$5.)))(0.(19.$2.R2.(:.O24.-88.)(4.$5.(6.R7.)(9.$5.)))(0.(19.$2.R2.(:.O24.-80.)(4.$5.(6.(7.&40.=))(4.$5.(6.(7.&40.+897<8.))(9.$5.))))(0.(34.R2.O24.O3.O9.(:.O8.(1;.O7.(1?.+2.+20.)))O12.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.)(0.(1.$2.R2.(:.O24.-68.)(4.$5.(6.(7.&40.O9.))(4.$5.(;.(7.&40.O8.))(4.$5.(;.(7.&40.O7.))(9.$5.)))))(0.(19.$2.R2.O:.(4.$5.(6.(7.&40.O=.))(4.$5.(;.R5.)(4.$5.(;.R6.)(9.$5.)))))(0.(19.$2.R2.(:.$1:.(1;.+4.O;.))(4.$5.(;.R4.)(9.$5.)))(0.(19.$2.R2.$1<.(4.$5.(6.(7.&40.(:.O6.R1.)))(4.$5.(6.O4.)(9.$5.))))(0.(1=.VhAR,R2.O5.)(0.(1>.$2.R2.O?.(:.O24.->0.))(0.(10.$20.(25.O6.(1?.+2.+14.))(25.(2<.(:.O6.R1.)+1.)(1?.+2.+14.)))(0.(10.$20.(25.O6.(1?.+2.+14.))(2=.(2>.$20.O5.)))(2:.=O6.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02?0@L10042309845.103L10234229450.1  L10281993173.4  L10319289635.142L10331739797.144L10523879957.1  L11377708045.122L12295109716.114L12576694431.122L12576910340.114L13143615528.5  L13143615528.7  L13246744724.4  L13388891551.122L13875334546.122L1441307378.122 L14752652106.142L1505710654.4   L15555881902.114L15703767798.122L15728120159.144L17863486591.122L18451125400.9  L18926735691.98 L18928860304.99 L18976848639.122L18977060452.114L18994852257.0  L19274458388.4  L19605100823.9  L19605101200.10 L19663821957.105L20208101127.11 L20211619719.144L20391638223.122L210820888.9    L2163309052.3   L21839504532.4  L21869790831.143L22412834409.114L22429060118.114L23002014212.114L23305446708.128L23305446708.139L23305446708.165L25212507605.105L25352339216.99 L25426245911.7  L25426246038.8  L2547266079.122 L25696969525.122L27078478760.144L27093352495.9  L27833502665.122L27833714514.114L27849013459.105L27866566932.4  L28188081845.122L29584333246.4  L30251788590.5  L30251788590.7  L31323244425.114L31323556626.122L31367688980.4  L33742536504.4  L34056211561.114L3456414210.7   L3458796162.105 L3471292805.144 L35157595318.143L35159414838.144L35159480328.141L35306571127.122L35539361338.103L370993749.4    L37536823913.114L37844031875.104L38127591898.122L38235414967.105L38250536502.114L38250844845.122L396873557.4    L39759977813.4  L4169174016.144 L42149148100.105L42154986053.114L42155329246.122L43586497528.4  L45083556926.4  L4510117937.144 L45287594732.105L45680522099.99 L45912337044.4  L46266910862.4  L46266910862.5  L46932309566.122L46932654757.114L47185826409.12 L48175908205.114L48270429156.114L50114853997.105L50672728382.4  L51162757380.105L51177107989.4  L51908117762.99 L53531446925.122L53531656726.114L57574016142.105L57628700040.6  L57628700040.9  L57699478293.122L57950336404.4  L58805046433.15 L58806793249.10 L58806793250.11 L58806793250.9  L58807237914.4  L58903439380.4  L59321330263.144L60104662136.4  L60210917806.114L60442842686.122L60957838539.105L60961095628.144L63214999020.114L63724396299.7  L63730750604.144L64861792658.122L65453056521.114L66567258439.104L67716476359.1  L67786676499.141L67787939520.5  L68027936357.5  L6822870346.1   L7471792062.122 L8068969941.4   L8806423751.6   L8806423751.9   L8981989310.4   L9212423428.114 L942498478.104  L9578481189.114 00000T00Y00]01N02?02D02k02l03P04404I04^04b05F05f06F07107907Y08@08A08d09E09`0:;0:^0;A0;B0;F0;e0<D0<h0<i0<j0<k0=L0=W0=[0>F0>f0?M0@10@X0A?0B10B20BP0B^0C:0C^0D>0D?0D@0Dc0EF0Ei0Em0FM0FU0Fj0GE0Gi0HM0HQ0HX0I80IM0J40Jf0K[0LL0N10NU0O90O=0O]0PC0Pc0QF0Qi0RL0RP0RT0T=0Tf0UO0V80VB0VJ0W80W_0X@0XD0XR0X`0Xa0Xb0YM0Z40ZW0[;0[C0\30\=0\[0]B0]i0]j0^?0^`0_@0_D0`80`]0aD0ae0al0b00b[0be0cE0cm0dT0eF0ej0fJ0fK0fo0gS0h60h;0hf0i;0iI0iN0iO0iS0ih0jI0jQ0k50k60k7S3hAR2SP2tf2id3blk2bl2ws4NODE2HL3NB1S3hARS2SPS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5start2KL2JBS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5start2KL2JBS3hARS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLFS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAS3hAR3blk4NODE2K13NB1S3hAR3blk4NODE2K13NB1S2SPS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5startS2SP3SPHS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLFS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2lo3blk4NODE2K05LOIMG3NB0S3hAR2SP2tf2id3blk2bl2ws2HLS3hAR2SP2tf2id3blk2bl2ws2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLSS2SPS3hAR2SP2lo5LOIMG3SPL1A1n2H12H2S3hAR2SP2lo5LOIMG3SPL1A1n2H12H2S3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAFFFS3hAR2SP2lo3blk4NODE2K05LOIMG3NB0S3hAR2bi2BIS2SPS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5startS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAS3hAR2SP2tf2id3blk2bl2ws4NODE2j'2HL3Hj'S3hAR2SP2tf2id3blk2bl2ws4NODE2HL2j'3Hj'S3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5start2j'3Hj'FS3hAR2SP2tf2id3blk2bl2ws2HL2IMS2SP2lo1A1n2H1S3hAR2SP2lo5LOIMG3SPL1A1n2H1S3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAS3hAR2SP2tf2id3blk2bl2ws4NODE2HLFFS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS2SPS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS2SP3SPHS3hAR2SP2lo5LOIMG3SPLS3hAR2SP2lo2bi2BI5LOIMG3SPLS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS2SPS2TR2T1S3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR3blk4NODE2K03NB0S3hAR2SP2tf2id3blk2bl2ws4NODE2K02HL3NB0S3hAR2SP4size2tf2id3blk2bl2ws4NODE2K02HL3NB05startS3hAR2SP4size2tf2id3blk2bl2ws4NODE3TF02BL2HL5start2KLS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5start2SB2JBS3hAR2AL2SP4size3tag2tf1h1v2bi2id3blk2bl2ws4NODE2SZ2TG3TF02ID2VB2BI2HR2HL4SB645ALWF'4IMG'2IM5start2SES3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3NB0S2SPS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2id3blk2bl2ws4NODE2K02K12HLS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS2SPS2SPS3hAR2AL2SP4size3tag2tf1h1v2bi2id3blk2bl2ws4NODE2SZ2TG3TF03TF12ID2VB2BI2HR2HL4SB645ALWF'4IMG'2IM5start2SES3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL5LOIMGS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL5LOIMGS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL5LOIMGS2SP2TR2T0S2SP3SPHS3hAR2SP4size2tf2id3blk2bl2ws4NODE2SZ2HL5startS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLS3hAR2SP2tf2id3blk2bl2ws3KAL2HL1HS2SPS3hAR2bl2j'2X1S3hAR2bl2j'2X1FFS3hAR2SP2TR2lo3blk4NODE2K12T05LOIMG3SPL3NB1S3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HLS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS2SP3SPHS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2K12HL5LOIMG3NB1S2SP2TR2T0S3hAR2SP2tf2id3blk2bl2ws2HL2IMS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLS3hAR2SP2tf2lo2id3blk2bl2ws4NODE2HL3SPLFS2SP2lo4NODE1x2Hx3SPLS2SP2lo2bi2bl4NODE5start1x2Hx3SPLS3hAR2SP2tf2id3blk2bl2ws4NODE2HLS2SPS3hAR2SP2lo3blk2bl4NODE2j'4KSEP5LOIMG3NB03NB13Hj'2X1S3hAR2SP2lo3blk4NODE2K15LOIMG3SPL3NB1S3hAR2SP2lo2bi3blk4NODE2BI2K05LOIMG3NB0S3hAR2SP2lo3blk4NODE2K05LOIMG3NB0S2SP2loS2SPS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5startS2SP2TR2T0S3hAR2SP2tf2id3blk2bl2ws4NODE2HLS3hAR2SP4size2tf2id3blk2bl2ws4NODE2SZ2HLS3hAR2SP2tf2id3blk2bl2ws4NODE2K12HL3NB1S3hAR2SP4size2tf2id3blk2bl2ws4NODE2K12HL3NB15startS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS3blk2bl4NODE5start4KSEP3NB03NB1FS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPHS3hAR2SP2tf2id3blk2bl2ws4NODE2ID2HLS3hARS3hAR2SP4size2tf2id3blk2bl2ws4NODE2HL5startS3hAR2SP2lo5LOIMG3SPLS3hAR2bl2j'2X0S3hARFS2SPS2SP2lo4NODE3SPL1x2HxS2SP2lo2bi2bl4NODE3SPL5start1x2HxS2SP3SPHS3hAR2SP2tf2id3blk2bl2ws4NODE2HL3SPAFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma seg_mid : ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Pra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Palloc,(>.&40.)Ppkw0,(>.&40.)Phsh,(>.&40.)Psid,(>.&40.)Plnkw,(>.&40.)Plnk,$20.Pq0,(>.&40.)Pq1,(>.&40.)Pq2,(>.&40.)Pq3,(>.&40.)Pq4,(>.&40.)Pq5,(>.&40.)Pq6,(>.&40.)Pq7,(>.&40.)Pq8,(>.&40.)Pq9,(>.&40.)Pqra,(>.&40.)PSP,$20.PF,(21.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))PTR,$20.Psize,$20.Ptag,$20.Ptf,$20.Plo,$20.Ph,$20.Pv,$20.Pbi,$20.Pid,$20.Pblk,$20.Pbl,(22.$20.)Pws,(22.(>.&40.))Pfr0,(22.(>.&8.))ZNODE,$20.(:.R4.(1;.+10.(27.R5.+10000.)))Zcount,$20.(:.R=.+1.)ZW,Pstart,$20.(22.(28.$20.$20.))Lstart,$20.(4.(28.$20.$20.)(29.$20.$20.R<.R14.)(4.(28.$20.$20.)(29.$20.$20.$1<.(:.(:.$1<.+10.)(1;.+10.+1000.)))(4.(28.$20.$20.)(29.$20.$20.(26.R6.(25.R1.(1?.+2.+14.)))(:.(26.R6.(25.R1.(1?.+2.+14.)))(1?.+2.+17.)))(4.(28.$20.$20.)(29.$20.$20.R3.(:.R3.+10.))(4.(28.$20.$20.)(29.$20.$20.(:.$1:.(1;.+4.R9.))(:.(:.$1:.(1;.+4.R9.))+4.))(9.(28.$20.$20.)))))))P,(0.(2:.+1.R?.)(2:.R?.+1>.))P,(0.(2:.=R?.)(2;.R?.+100.))P,(2:.=R?.)P,(2;.(:.R10.+40.)(1?.+2.+20.))P,(10.$20.(2=.(2>.$20.R:.))(25.(2<.(:.R11.(1?.+2.+14.))+1.)(1?.+2.+14.)))P,(0.(2:.=R=.)(2;.R=.(1?.+2.+1?.)))P,(0.(2:.=R10.)(2;.R10.(1?.+2.+1?.)))P,(0.(2:.=R10.)(2;.R10.(1?.+2.+14.)))P,(0.(2:.=R13.)(2;.R13.(1?.+2.+40.)))P,(2:.+65?000.R10.)P,(2:.(:.R11.(1?.+2.+14.))(2?.VhAR,))P,(10.$20.(27.R12.+1000.)=)P,(30.VCS,R13.(1?.+2.+14.))P,Pj',$20.P,(0.(2:.=R1.)(2;.R1.(2=.(2>.$20.R14.))))(31.(2:.(:.R16.(1?.+2.+14.))(26.R15.R2.))(2:.(:.(26.R15.R2.)(1?.+2.+17.))R16.))P,Pj',$20.P,(0.(2:.=R1.)(2;.R1.(2=.(2>.$20.R15.))))(0.(1>.$2.R21.(26.R16.R2.)(:.(26.R16.R2.)(1?.+2.+17.)))(30.VCS,(26.R16.R2.)(1?.+2.+17.)))P,(19.$2.R20.R12.(4.$5.(6.R32.)(4.$5.(;.R30.)(4.$5.(;.R31.)(9.$5.)))))P,(34.R21.R24.R14.R20.(:.R1?.(1;.R1>.(1?.+2.+20.)))R25.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)P,(1.$2.R22.(:.R25.-68.)(4.$5.(6.(7.&40.R21.))(4.$5.(;.(7.&40.R20.))(4.$5.(;.(7.&40.R1?.))(9.$5.)))))P,(19.$2.R23.$1<.(4.$5.(6.(7.&40.R1?.))(4.$5.(6.R37.)(9.$5.))))P,(1=.VhAR,R24.R19.)P,(19.$2.R25.(:.$1:.(1;.+4.R1=.))(4.$5.(;.R38.)(9.$5.)))P,(3;.$2.R26.R25.R1:.)P,(10.$3<.(2>.(>.&40.)R1;.)#1>.)P,(37.R28.)P,(2:.R2<.R28.)P,(2:.(:.R29.+?0.)(1?.+2.+3?.))P,(30.VCS,R2:.+?0.)P,(1>.$2.R2<.R27.(:.R2?.-70.))P,(2:.(2?.VhAR,)R28.)P,(2:.R29.(2<.R31.+240.))P,(2:.R32.(1?.+2.+3>.))P,(10.$20.(27.R33.+10.)=)P,(30.VCS,R2<.(2<.R34.R2<.))P,(18.$2.R32.)(38.$2.VAL,VCS,Lms',$<.(=.$20.Lstart,$20.(0.(31.(10.$20.R1.R31.)(0.(10.$20.R1.(:.R31.R26.))(2;.(25.R31.(1?.+2.+14.))(25.(2<.(:.R31.R26.)+1.)(1?.+2.+14.)))))(31.(0.(2;.(25.R1.(1?.+2.+14.))(2=.(2>.$20.R2:.)))(0.(10.$20.(25.R1.(1?.+2.+14.))(25.(2<.(:.R1.R26.)+1.)(1?.+2.+14.)))(24.R38.R5;.R5:.R59.R58.R53.R52.R51.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R37.R36.R30.R2<.R2?.R2>.R2=.R27.(26.R2:.(25.R1.(1?.+2.+14.)))(:.R1.R26.)R2:.R49.A1.R25.R1.R35.R2.)))(3=.R38.R5;.R5:.R59.R58.R53.R52.R51.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R37.R36.R30.R2<.R2?.R2>.R2=.R27.R34.R33.R32.R1.R2:.R49.R28.(4.(28.$20.$20.)(29.$20.$20.R30.R38.)(4.(28.$20.$20.)(29.$20.$20.$1<.(:.(:.$1<.+10.)(1;.+10.+1000.)))(4.(28.$20.$20.)(29.$20.$20.R27.(:.R27.+10.))(9.(28.$20.$20.)))))R35.R2.))))(11.(12.R5:.(7.&40.(:.R36.-70.))R59.R58.R55.R54.R53.(7.&40.=)(7.&40.R2:.)(7.&40.R29.)R4>.R4=.R4<.R4;.R4:.R49.R48.(7.&40.(:.$1:.(1;.+4.R2;.)))(7.&40.R2=.)(7.&40.$32.)(7.&40.R2<.)(7.&40.+????.)(7.&40.R2:.)(7.&40.$39.)(7.&40.R2<.)R57.R56.R52.R51.R50.R4?.)R35.(7.&40.+897:8.)R34.(14.(>.&40.))R33.(15.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s10 s11 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 alloc pkw0 hsh sid lnkw lnk q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra SP F fc m
      TR size tag tf lo h v bi id blk bl ws fr0 NODE count W
      SZ TG TF0 TF1 BL ID VB BI HR K0 K1 KAL KCS KSEP SBLK NC FRP ARGS SSX DB TC HTR HL [GOTF CF240] T0 T1 TCS ST LOIMG SPL SPH SPA SCS MI.
    facts. subst count W.
    assert (HN : NODE = blk + 16 * (id mod 65536)) by reflexivity. clearbody NODE.
    pose proof (Z.mod_pos_bound id 65536 ltac:(lia)) as IM.
    assert (NB : blk <= NODE /\ NODE + 16 <= blk + 2^20 /\ NODE mod 16 = 0).
    { subst NODE. pose proof (Z.div_mod blk 4096 ltac:(lia)). split; [lia| split; [lia|]].
      replace (blk + 16 * (id mod 65536)) with ((blk / 4096 * 256 + id mod 65536) * 16) by lia. apply Z_mod_mult. }
    ddestruct NB as (NB0 & NB1 & NAL).
    assert (NCS : crange CS NODE 16) by (eapply (crange_sub CS blk (2^20)); [exact KCS| lia| lia]).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dput_ins_B AL IMG ALWF CS CSOK ra gp tp s10 s11 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 SP F fc m h bi v id blk); try lia. exact MI. }
    cbn beta. intros ms1 (x1 & ->). rewrite <- HN.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dnode_store_A AL IMG ALWF CS CSOK (Z_to_bv 64 0x0897c8) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 NODE)
                (Z_to_bv 64 (A_DEP + 4 * bi)) (Z_to_bv 64 h) (Z_to_bv 64 A_DEP_NODES) (Z_to_bv 64 v)
                (Z_to_bv 64 0xffff) (Z_to_bv 64 id) (Z_to_bv 64 A_DEP_MAP1) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6
                x1 a4 a5 a6 a7 hsh sid (bv_unsigned lnkw) (SP + -112) F fc m NODE (SP + -104) h lo);
        try eassumption; try lia.
      - rewrite Z_to_bv_bv_unsigned. exact NC.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m2 & fr1 & -> & MU2 & WM2 & MI2 & F1 & F2 & F3 & NC2 & ST2)).
    (* [comment removed for export] *)
    assert (FRP2 : dput_frame m2 SP fr0 TR (size + tag * 2^32) qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9).
    { eapply rw_cells_transport; [exact FRP| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL SPH LOIMG K1 NB1. lia. }
    assert (ARGS2 : ro_cells asegs m2 (SP + -104) [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 tag)]).
    { eapply ro_cells_transport; [exact ARGS| exact MU2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL SPH LOIMG K1 NB1. lia. }
    assert (SSX2 : rw_cells asegs m2 A_SS [C8 (Z_to_bv 64 tf); C8 alloc]).
    { eapply rw_cells_transport; [exact SSX| exact MU2| exact WM2|]. unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear - SPL LOIMG K0 NB0. lia. }
    assert (DB2 : dblocks m2 bl).
    { eapply (dblocks_transport _ m m2 bl DB MU2 WM2). unfold A_SS; cbn [disjoint_from]. clear - SPL LOIMG K0 NB0. lia. }
    assert (TC2 : rw_cells asegs m2 (A_DEP + 4 * bi) [C4 pkw0]).
    { eapply rw_cells_transport; [exact TC| exact MU2| exact WM2|]. unfold A_DEP; cbn [disjoint_from cells_size csize Nat.add]. clear - BI SPL LOIMG K0 NB0. lia. }
    assert (HTR2 : u64arr asegs m2 TR ws).
    { eapply u64arr_transport; [exact HTR| exact MU2| exact WM2|]. rewrite HL. cbn [disjoint_from]. clear - T0 T1 SPL LOIMG K1 NB1. lia. }
    assert (GOTF2 : ro_cells asegs m2 A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]).
    { eapply ro_cells_transport; [exact GOTF| exact MU2|]. unfold A_GOT_CFLAGS; cbn [disjoint_from cells_size csize Nat.add]. clear - SPL LOIMG K0 NB0. lia. }
    assert (CF2 : ro_cells asegs m2 (A_CFLAGS + 240) [C4 (Z_to_bv 64 0)]).
    { eapply ro_cells_transport; [exact CF240| exact MU2|]. unfold A_CFLAGS; cbn [disjoint_from cells_size csize Nat.add Z.add]. clear - SPL LOIMG K0 NB0. lia. }
    assert (SBLK2 : forall j', 0 <= j' < Z.of_nat (length bl) -> stk asegs m2 (sblk bl j') (sblk bl j' + 2^23) /\ crange CS (sblk bl j') (2^23)).
    { intros j' Hj'. destruct (SBLK j' Hj') as [S1 S2]. split; [|exact S2].
      eapply stk_transport_disjoint; [exact S1| exact MU2| exact WM2|]. cbn [disjoint_from]. specialize (KSEP j' Hj').
      ddestruct DB as (_ & DBF & _). pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN.
      ddestruct (proj1 FN DBF (Z.to_nat j') 0 ltac:(lia)) as (X0 & X1 & _). unfold sblk in *. clear - KSEP X0 X1 SPL LOIMG NB0 NB1 Hj'. lia. }
    clear FRP ARGS SSX DB TC HTR GOTF CF240 SBLK NC.
    replace (SP + -112 + -32) with (SP + -144) in * by lia. replace (SP + -112 + -24) with (SP + -136) in * by lia.
    replace (SP + -112 + -16) with (SP + -128) in * by lia.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (ss_store_A AL IMG ALWF CS CSOK (Z_to_bv 64 0x0892e4) gp tp t0 t1 t2 (Z_to_bv 64 NODE) (Z_to_bv 64 NODE)
                (Z_to_bv 64 (A_DEP + 4 * bi)) (Z_to_bv 64 h) (Z_to_bv 64 A_DEP_NODES) (Z_to_bv 64 v)
                (Z_to_bv 64 0xffff) (Z_to_bv 64 id) (Z_to_bv 64 A_DEP_MAP1) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6
                (Z_to_bv 64 h) a4 a5 a6 a7 (Z_to_bv 64 0) (SP + -144) F fc m2 (SP + -104) (SP + -136) TR size tag lo);
        try eassumption; try lia.
      all: eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & FRS3 & PK3 & ST3)).
    (* [comment removed for export] *)
    assert (DJ3 : forall A n, SP + -128 <= A -> A + n <= 2^63 -> disjoint_from [(lo, SP + -144); (SP + -136, SP + -136 + 8)] A n).
    { intros A n H1 H2. cbn [disjoint_from]. clear - H1 H2 SPL. lia. }
    assert (DJ3' : forall A n, A + n <= ACEIL -> disjoint_from [(lo, SP + -144); (SP + -136, SP + -136 + 8)] A n).
    { intros A n H1. cbn [disjoint_from]. clear - H1 SPL LOIMG. lia. }
    assert (FRP3 : dput_frame m3 SP fr0 TR (size + tag * 2^32) qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9)
      by (eapply rw_cells_transport; [exact FRP2| exact MU3| exact WM3| apply DJ3; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (ARGS3 : ro_cells asegs m3 (SP + -104) [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 tag)])
      by (eapply ro_cells_transport; [exact ARGS2| exact MU3| apply DJ3; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (F13 : rw_cells asegs m3 (SP + -144) [CB 8 fr1])
      by (eapply rw_cells_transport; [exact F1| exact MU3| exact WM3| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (F33 : rw_cells asegs m3 (SP + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x0897c8)])
      by (eapply rw_cells_transport; [exact F3| exact MU3| exact WM3| apply DJ3; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (NC3 : rw_cells asegs m3 NODE [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 (bv_unsigned lnkw)); C4 sid])
      by (eapply rw_cells_transport; [exact NC2| exact MU3| exact WM3| apply DJ3'; cbn [cells_size csize Nat.add]; clear - K1 NB1; lia]).
    assert (SSX3 : rw_cells asegs m3 A_SS [C8 (Z_to_bv 64 tf); C8 alloc])
      by (eapply rw_cells_transport; [exact SSX2| exact MU3| exact WM3| apply DJ3'; unfold A_SS; cbn [cells_size csize Nat.add]; clear; lia]).
    assert (DB3 : dblocks m3 bl) by (eapply (dblocks_transport _ m2 m3 bl DB2 MU3 WM3); apply DJ3'; unfold A_SS; clear; lia).
    assert (TC3 : rw_cells asegs m3 (A_DEP + 4 * bi) [C4 pkw0])
      by (eapply rw_cells_transport; [exact TC2| exact MU3| exact WM3| apply DJ3'; unfold A_DEP; cbn [cells_size csize Nat.add]; clear - BI; lia]).
    assert (HTR3 : u64arr asegs m3 TR ws)
      by (eapply u64arr_transport; [exact HTR2| exact MU3| exact WM3| apply DJ3; rewrite ?HL; clear - T0 T1; lia]).
    assert (GOTF3 : ro_cells asegs m3 A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)])
      by (eapply ro_cells_transport; [exact GOTF2| exact MU3| apply DJ3'; unfold A_GOT_CFLAGS; cbn [cells_size csize Nat.add]; clear; lia]).
    assert (CF3 : ro_cells asegs m3 (A_CFLAGS + 240) [C4 (Z_to_bv 64 0)])
      by (eapply ro_cells_transport; [exact CF2| exact MU3| apply DJ3'; unfold A_CFLAGS; cbn [cells_size csize Nat.add Z.add]; clear; lia]).
    assert (SBLK3 : forall j', 0 <= j' < Z.of_nat (length bl) -> stk asegs m3 (sblk bl j') (sblk bl j' + 2^23) /\ crange CS (sblk bl j') (2^23)).
    { intros j' Hj'. destruct (SBLK2 j' Hj') as [S1 S2]. split; [|exact S2].
      eapply stk_transport_disjoint; [exact S1| exact MU3| exact WM3|]. apply DJ3'.
      ddestruct DB2 as (_ & DBF & _). pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN.
      ddestruct (proj1 FN DBF (Z.to_nat j') 0 ltac:(lia)) as (X0 & X1 & _). unfold sblk in *. clear - X1. lia. }
    clear FRP2 ARGS2 F1 F3 NC2 SSX2 DB2 TC2 HTR2 GOTF2 CF2 SBLK2 DJ3 DJ3'.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m3 (SP + -144 + -64) [C8 (Z_to_bv 64 0)] _) FRS3) as [IX3 FRS3']. clear FRS3.
    cbn [cells_size csize Nat.add] in FRS3'. replace (SP + -144 + -64 + Z.of_nat 8) with (SP + -200) in FRS3' by lia.
    replace (SP + -144 + -64) with (SP + -208) in * by lia.
    eapply evtA_cut.
    { eapply (ss_alloc_A AL IMG ALWF CS CSOK (Z_to_bv 64 0x08701c) gp tp t0 t1 t2 (Z_to_bv 64 (SP + -136)) (Z_to_bv 64 A_SS)
                (Z_to_bv 64 (size + 1)) (Z_to_bv 64 (SP + -104)) (Z_to_bv 64 size) (Z_to_bv 64 tag)
                (Z_to_bv 64 0xffff) (Z_to_bv 64 id) (Z_to_bv 64 A_DEP_MAP1) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6
                a4 a5 a6 a7 alloc (Z_to_bv 64 0) (SP + -208) F fc m3 (SP + -208) (SP + -136) tf (size + 1) 0 lo bl);
        try eassumption; try lia.
      all: eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (start & pc & x5 & x6 & x7 & x2 & x4 & x16 & x17 & x28 & pk & r0 & r8 & r1 & res & m4 & -> & MU4 & WM4 & MI4 & SSX4 & DB4 & IX4 & PK4 & SE & SB & CASES)).
    assert (DJ4 : forall A n, SP + -200 <= A -> (SP + -136 + 8 <= A \/ A + n <= SP + -136) -> A + n <= 2^63 ->
              disjoint_from [(lo, SP + -208); (A_SS, A_SS + 16 + 16 * 4096); (SP + -208, SP + -208 + 8); (SP + -136, SP + -136 + 8)] A n).
    { intros A n H1 H2 H3. unfold A_SS. cbn [disjoint_from]. clear - H1 H2 H3 SPL LOIMG. lia. }
    assert (DJ4' : forall A n, 0x65f000 <= A -> A + n <= ACEIL ->
              disjoint_from [(lo, SP + -208); (A_SS, A_SS + 16 + 16 * 4096); (SP + -208, SP + -208 + 8); (SP + -136, SP + -136 + 8)] A n).
    { intros A n H1 H2. unfold A_SS. cbn [disjoint_from]. clear - H1 H2 SPL LOIMG. lia. }
    assert (FRP4 : dput_frame m4 SP fr0 TR (size + tag * 2^32) qra q0 q1 q2 q3 q4 q5 q6 q7 q8 q9)
      by (eapply rw_cells_transport; [exact FRP3| exact MU4| exact WM4| apply DJ4; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (ARGS4 : ro_cells asegs m4 (SP + -104) [C8 (Z_to_bv 64 TR); C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 tag)])
      by (eapply ro_cells_transport; [exact ARGS3| exact MU4| apply DJ4; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (F14 : rw_cells asegs m4 (SP + -144) [CB 8 fr1])
      by (eapply rw_cells_transport; [exact F13| exact MU4| exact WM4| apply DJ4; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (F34 : rw_cells asegs m4 (SP + -128) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x0897c8)])
      by (eapply rw_cells_transport; [exact F33| exact MU4| exact WM4| apply DJ4; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (FRS4 : rw_cells asegs m4 (SP + -200) [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 A_DEP_NODES); C8 (Z_to_bv 64 h);
                                     C8 (Z_to_bv 64 (A_DEP + 4 * bi)); C8 (Z_to_bv 64 NODE); C8 (Z_to_bv 64 NODE); C8 (Z_to_bv 64 0x0892e4)])
      by (eapply rw_cells_transport; [exact FRS3'| exact MU4| exact WM4| apply DJ4; cbn [cells_size csize Nat.add]; clear - SPL SPH; lia]).
    assert (NC4 : rw_cells asegs m4 NODE [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 (bv_unsigned lnkw)); C4 sid])
      by (eapply rw_cells_transport; [exact NC3| exact MU4| exact WM4| apply DJ4'; cbn [cells_size csize Nat.add]; clear - K0 K1 NB0 NB1; lia]).
    assert (TC4 : rw_cells asegs m4 (A_DEP + 4 * bi) [C4 pkw0]).
    { eapply rw_cells_transport; [exact TC3| exact MU4| exact WM4|]. unfold A_DEP, A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear - BI SPL LOIMG. lia. }
    assert (HTR4 : u64arr asegs m4 TR ws)
      by (eapply u64arr_transport; [exact HTR3| exact MU4| exact WM4| apply DJ4; rewrite ?HL; clear - T0 T1; lia]).
    assert (GOTF4 : ro_cells asegs m4 A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]).
    { eapply ro_cells_transport; [exact GOTF3| exact MU4|]. unfold A_GOT_CFLAGS, A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear - SPL LOIMG. lia. }
    assert (CF4 : ro_cells asegs m4 (A_CFLAGS + 240) [C4 (Z_to_bv 64 0)]).
    { eapply ro_cells_transport; [exact CF3| exact MU4|]. unfold A_CFLAGS, A_SS; cbn [disjoint_from cells_size csize Nat.add Z.add]. clear - SPL LOIMG. lia. }
    assert (SBLK4 : forall j', 0 <= j' < Z.of_nat (length bl) -> stk asegs m4 (sblk bl j') (sblk bl j' + 2^23) /\ crange CS (sblk bl j') (2^23)).
    { intros j' Hj'. destruct (SBLK3 j' Hj') as [S1 S2]. split; [|exact S2].
      eapply stk_transport_disjoint; [exact S1| exact MU4| exact WM4|]. apply DJ4'.
      all: ddestruct DB3 as (_ & DBF & _); pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN;
           ddestruct (proj1 FN DBF (Z.to_nat j') 0 ltac:(lia)) as (X0 & X1 & _); unfold sblk in *; clear - X0 X1; lia. }
    clear FRP3 ARGS3 F13 F33 NC3 SSX3 DB3 TC3 HTR3 GOTF3 CF3 SBLK3 FRS3' DJ4 DJ4'.
    destruct CASES as [(-> & -> & -> & -> & KL & -> & ST4) | (-> & -> & -> & -> & KL & -> & FRA4 & ST4)].
    - (* [comment removed for export] *)
      rewrite Z_to_bv_bv_unsigned.
      replace (ret_pc (Z_to_bv 64 0x08701c)) with (Z_to_bv 64 0x08701c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      assert (FRSJ : rw_cells asegs m4 (SP + -208) ([C8 (Z_to_bv 64 start)] ++ [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 A_DEP_NODES); C8 (Z_to_bv 64 h);
                                     C8 (Z_to_bv 64 (A_DEP + 4 * bi)); C8 (Z_to_bv 64 NODE); C8 (Z_to_bv 64 NODE); C8 (Z_to_bv 64 0x0892e4)])).
      { apply (proj2 (rw_cells_app asegs m4 (SP + -208) _ _)). split; [exact IX4|]. cbn [cells_size csize Nat.add].
        replace (SP + -208 + Z.of_nat 8) with (SP + -200) by lia. exact FRS4. }
      cbn [app] in FRSJ. clear IX4 FRS4.
      assert (JB : 0 <= start / 2^20) by (apply Z.div_pos; lia).
      destruct (SBLK4 (start / 2^20) ltac:(lia)) as [STB4 BCS4].
      eapply evtA_mono.
      { eapply (seg_tail gp tp s10 s11 x5 x6 x7 x28 t4 t5 t6 x2 x4 x16 x17 _ _ _ alloc pk sid pkw0 (Z_to_bv 64 (bv_unsigned lnkw)) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra SP F fc m4
                  TR size tag start lo h v bi id NODE bl (firstn (Z.to_nat (8 * size)) (u64s ws)) fr0 fr1); try eassumption; try lia.
        all: first
          [ exact I
          | split; assumption
          | specialize (KSEP (start / 2^20) ltac:(lia)); clear - KSEP NB0 NB1; lia
          | destruct HTR4 as [HB _]; destruct (bytes_at_app asegs m4 TR (firstn (Z.to_nat (8 * size)) (u64s ws)) (skipn (Z.to_nat (8 * size)) (u64s ws))) as [X _];
            rewrite firstn_skipn in X; exact (proj1 (X HB))
          | rewrite length_firstn, u64s_length, HL; lia ]. }
      cbn beta. intros ms1 PT. exists start. split; [exact SE|]. left. split; [assumption|]. split; [exact SB|].
      eapply fin_post_pre; [| | exact PT].
      { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
        eapply munch_trans. { eapply munch_weaken; [| exact MU3]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
        eapply munch_weaken; [| exact MU4]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
      eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3| exact WM4].
    - (* [comment removed for export] *)
      apply evtA_done. exists start. split; [exact SE|]. right.
      replace (SP + -208 + -16) with (SP + -224) in * by lia.
      unfold asc_post, A_BI_CREATE. deexists 14.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
               eapply munch_trans. { eapply munch_weaken; [| exact MU3]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
               eapply munch_weaken; [| exact MU4]. unfold sub_fp, A_SS; cbn [outside]. clear - SPL. intros x Hx. lia. }
      split. { eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3| exact WM4]. }
      split; [exact MI4|].
      repeat (split; [first [eassumption| lia] |]). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hit_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo N : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Lms',$<.(=.$20.Ls,$20.(=.(>.&40.)Lx5,(>.&40.)(=.(>.&40.)Lx6,(>.&40.)(=.(>.&40.)Lx7,(>.&40.)(=.(>.&40.)Lx11,(>.&40.)(=.(>.&40.)Lx12,(>.&40.)(=.(>.&40.)Lx13,(>.&40.)(=.(>.&40.)Lx14,(>.&40.)(=.(>.&40.)Lx15,(>.&40.)(=.(>.&40.)Lx16,(>.&40.)(=.(>.&40.)Lx17,(>.&40.)(=.(>.&40.)Lx28,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(0.(10.$<.R>.(11.(12.O17.(7.&40.O18.)O16.O15.R<.R;.R:.O14.O13.(7.&40.R=.)R9.R8.R7.R6.R5.R4.R3.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R2.O8.O7.O6.)O5.(13.O17.)O4.(14.(>.&40.))R1.(15.$2.)))(0.(16.(4.(28.$20.$20.)(29.$20.$20.O3.O18.)(9.(28.$20.$20.)))O1.R1.)(0.(17.$2.O1.R1.)(0.(18.$2.R1.)(0.(1>.$2.R1.O3.O18.)(0.(2:.+1.R=.)(2:.R=.O2.))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition headA_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo N TR szt : Z) (nb : list Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Lms',$<.(=.$20.Lh,$20.(=.$20.Lbi,$20.(=.$20.Lv,$20.(=.$20.Lpc,$20.(=.(>.&40.)Lr1,(>.&40.)(=.(>.&40.)Lr10,(>.&40.)(=.(>.&40.)Lr11,(>.&40.)(=.(>.&40.)Lx5,(>.&40.)(=.(>.&40.)Lx6,(>.&40.)(=.(>.&40.)Lx7,(>.&40.)(=.(>.&40.)Lx12,(>.&40.)(=.(>.&40.)Lx13,(>.&40.)(=.(>.&40.)Lx14,(>.&40.)(=.(>.&40.)Lx15,(>.&40.)(=.(>.&40.)Lx16,(>.&40.)(=.(>.&40.)Lx17,(>.&40.)(=.(>.&40.)Llockw,(>.&40.)(=.(22.(>.&8.))Lfr,(22.(>.&8.))(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))Zk,$20.(25.(:.O5.+1.)+10000.)(0.(10.$<.R15.(11.(12.R10.(7.&40.(:.O1<.-70.))O1:.O19.R=.R<.R;.(7.&40.=)(7.&40.(:.O5.+1.))R?.R>.R:.R9.R8.R7.R6.R5.(7.&40.(:.$1:.(1;.+4.R13.)))(7.&40.R14.)(7.&40.$32.)(7.&40.R12.)(7.&40.+????.)(7.&40.(:.O5.+1.))(7.&40.$39.)(7.&40.R12.)O>.O=.O<.O;.O:.O9.)O8.(7.&40.R11.)O7.(14.(>.&40.))R2.(15.$2.)))(0.(16.(4.(28.$20.$20.)(29.$20.$20.O6.O1<.)(4.(28.$20.$20.)(29.$20.$20.(:.$1:.(1;.+4.R13.))(:.(:.$1:.(1;.+4.R13.))+4.))(4.(28.$20.$20.)(29.$20.$20.$3>.(:.$3>.+4.))(9.(28.$20.$20.)))))O1.R2.)(0.(17.$2.O1.R2.)(0.(18.$2.R2.)(0.(34.R2.O1<.R3.O4.O3.O1;.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.)(0.(19.$2.R2.(:.$1:.(1;.+4.R13.))(4.$5.(;.R4.)(9.$5.)))(0.(19.$2.R2.$3>.(4.$5.(;.(7.&40.(:.O5.+1.)))(9.$5.)))(0.(1>.$2.R2.O6.(:.O1<.-70.))(0.(0.(2:.=R14.)(2;.R14.(1?.+2.+40.)))(0.(0.(2:.=R13.)(2;.R13.(1?.+2.+14.)))(0.(0.(2:.=R12.)(2:.R12.O5.))(31.(0.(10.$20.R11.+897:8.)(0.(2;.R1.(2=.(2>.$20.O2.)))(10.(>.&40.)R?.(7.&40.(3?.O2.R1.)))))(0.(10.$20.R11.$40.)(0.(10.(>.&40.)R10.(7.&40.+89840.))(0.(10.$20.R1.(2=.(2>.$20.O2.)))(0.(10.$20.(:.O5.+1.)(1;.+10000.R1.))(0.(10.(>.&40.)R?.(7.&40.$32.))(10.(>.&40.)R>.(7.&40.R1.))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11149740284.132L13266555807.5  L13729783041.89 L17245688775.108L1763484206.89  L20379177870.89 L22706556809.5  L23072108830.3  L23305446708.122L27189815741.3  L27803943087.6  L28573892092.5  L35022906908.110L35024989724.89 L35078138783.5  L36690522898.10 L38301025552.106L40212493214.5  L42150905205.89 L44660010038.3  L4752731047.3   L50597713712.132L53601101470.4  L55356842776.3  L60299350319.89 L60300747039.108L60301433135.110L8794502284.3   L8886407227.132 L9827340300.1   00000R00_01A01d02C02o03>03L03o04=04T04c05F05i06;06\07:07H07m08;08I08j09809B09b0:B0:b0;00;Q0;US3hAR2SP2TR1N2tf2nb2bl2ws2HL2bi2BIS2SP2lo1A1n1HS3hAR2SP2TR1N2tf2lo2nb2bl2ws2T02HLS3hAR2SP2TR1N2tf2lo2nb2bl2ws2HL3SPLS3hAR2SP2TR1N2tf2nb2bl2ws2HL2WNS3hAR2SP2TR1N2tf2lo2nb2bl2ws2T02HL5LOIMG3SPLS2SP2lo2bi1x2HxS3hAR2lo5LOIMGS3hAR2SP2TR1N2tf2nb2bl2ws2HL2j'3Hj'S3hAR2lo5LOIMGS3hAR2lo2bl5LOIMG2j'2X1S2SP2lo2bi1x2HxS3hAR2SP2TR1N2tf2lo2nb2bl2ws2HL3SPLS3hAR2SP2TR1N2tf2lo2nb2bl2ws2HL3SPLS3hAR2lo5LOIMG1b1XS3hAR2SP2lo5LOIMG3SPL2bi2BI1A1n1HS3hAR2SP2TR1N2tf2nb2bl2ws2HL1vS3hAR2lo5LOIMGS3hAR2SP2TR1N2tf2lo2nb2bl2ws2HL5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR2SP2TR1N2tf2nb2bl2ws2HL1h2HRS3hAR2lo5LOIMGS2SP2TR2T0S3hAR2SP2TR1N2tf2nb2bl2ws2HL3SPHS3hAR2SP2TR1N2tf2nb2bl2ws2HL3SPHS3hAR2SP2TR1N2tf2nb2bl2ws2HL3SPHS3hAR2lo5LOIMGS3hAR2SP2TR1N2tf2nb2bl2ws2HL1v2VBS2SP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma seg_head : ltac2:(CDefT.buildp (gd_tbl_AW_DepotF ()) "Pra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Pc1,(>.&40.)Pc2,(>.&40.)Pc3,(>.&40.)Palloc,(>.&40.)PSP,$20.PF,(21.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))PTR,$20.Psize,$20.Ptag,$20.PN,$20.Ptf,$20.Plo,$20.Pnb,(22.$20.)Pbl,(22.$20.)Pws,(22.(>.&40.))Zszt,$20.(:.R8.(1;.R7.(1?.+2.+20.)))P,(0.(2:.+1.R9.)(2:.R9.+1>.))P,(0.(2:.=R9.)(2;.R9.+100.))P,(2:.R10.R<.)P,(2:.(:.R=.+100.)(1?.+2.+3?.))P,(10.$20.(27.R>.+8.)=)P,(3;.$2.R10.R?.R7.)P,(10.$3<.(2>.(>.&40.)R8.)#1>.)P,(30.VCS,R11.+?0.)P,(1.$2.R13.$41.(4.$5.(6.R1:.)(9.$5.)))P,(1.$2.R14.$42.(4.$5.(6.R1:.)(9.$5.)))P,(1.$2.R15.$43.(4.$5.(6.R1:.)(9.$5.)))P,(44.R16.R12.)P,(19.$2.R17.$3>.(4.$5.(;.(7.&40.R13.))(9.$5.)))P,(45.VhAR,R18.R11.)P,(46.R19.R12.R15.)P,(47.R13.R16.)P,Pk,$20.P,(0.(2:.=R1.)(2;.R1.(2=.(2>.$20.R15.))))(30.VCS,(3?.R16.R2.)(1?.+2.+14.))P,Pk,$20.Pj',$20.P,(0.(2:.=R2.)(2;.R2.(2=.(2>.$20.R17.))))P,(0.(2:.=R2.)(2;.R2.(2=.(2>.$20.R17.))))(31.(2:.(:.(3?.R19.R4.)(1?.+2.+14.))(26.R18.R3.))(2:.(:.(26.R18.R3.)(1?.+2.+17.))(3?.R19.R4.)))P,Pj',$20.P,(0.(2:.=R1.)(2;.R1.(2=.(2>.$20.R16.))))(0.(1>.$2.R1?.(26.R17.R2.)(:.(26.R17.R2.)(1?.+2.+17.)))(30.VCS,(26.R17.R2.)(1?.+2.+17.)))P,(19.$2.R1>.$1<.(4.$5.(6.(7.&40.R19.))(4.$5.(6.R22.)(9.$5.))))P,(1=.VhAR,R1?.R17.)P,(2:.=R1;.)P,(2;.(:.R1<.+40.)(1?.+2.+20.))P,(10.$20.(2=.(2>.$20.R1:.))(25.(2<.(:.R1=.(1?.+2.+14.))+1.)(1?.+2.+14.)))P,(37.R23.)P,(1>.$2.R24.R1>.R27.)P,(2:.(2?.VhAR,)R1?.)P,(2:.R20.(2<.R29.+240.))P,(2:.R2:.(1?.+2.+3>.))P,(10.$20.(27.R2;.+10.)=)P,(30.VCS,R23.(2<.R2<.R23.))P,(18.$2.R2:.)(38.$2.VAL,VCS,Lms',$<.(31.(48.R2?.R4?.R4>.R4=.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3<.R3;.R3:.R2>.R2=.R26.R28.R2<.R1.)(49.R2?.R4?.R4>.R4=.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R2>.R2=.R26.R28.R2;.R22.R25.R2<.R1.))(11.(12.R4>.(7.&40.R2>.)R4=.R4<.R4;.R4:.R49.R48.R47.(7.&40.R2:.)(7.&40.R21.)R38.R37.R36.R35.R34.R33.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.)R2=.(7.&40.$4:.)R2<.(14.(>.&40.))R2;.(15.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 c1 c2 c3 alloc SP F fc m TR size tag N tf lo nb bl ws
      szt SZ TG T0 T1 TAL HTR HL TCS M1 M2 M3 DT NC DM DN WF NBCS KSEP SBLK SSX DB TF0 TF1 BL DS ST LOIMG SPL SPH SPA SCS MI.
    facts. subst szt. pose proof WF as [WN WL]. pose proof (u64arr_bound _ _ _ _ HTR) as TRB.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dput_pro AL IMG ALWF CS CSOK); try eassumption; try lia. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (v & VB & h & bi & x2 & x4 & x5 & x6 & m1 & fr & -> & MU1 & WM1 & MI1 & FRP1 & ST1 & TC1 & HR & BI)).
    (* [comment removed for export] *)
    assert (LO : forall A n, A + n <= lo -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn [disjoint_from]; clear - H; lia).
    assert (HI : forall A n, SP <= A -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn [disjoint_from]; clear - H; lia).
    assert (DT1 : dtab m1 N) by (eapply (dtab_transport _ m m1 N DT MU1 WM1); apply LO; unfold A_DEP; clear - LOIMG; lia).
    assert (NC1 : rw_cells asegs m1 A_DEP_N [C4 (Z_to_bv 64 N)]) by (eapply rw_cells_transport; [exact NC| exact MU1| exact WM1| apply LO; unfold A_DEP_N; clear - LOIMG; cbn; lia]).
    assert (DM1 : dmap1 m1 nb) by (eapply (dmap1_transport _ m m1 nb DM MU1 WM1); apply LO; unfold A_DEP_MAP1; clear - LOIMG; lia).
    assert (DN1 : dnodes m1 nb N).
    { ddestruct DM as (_ & DMF & _). eapply (dnodes_transport _ m m1 nb N DN MU1 WM1 DMF). intros b Hb. apply LO.
      pose proof (proj1 (Forall_forall _ _) DMF b Hb) as (_ & X & _). clear - X LOIMG. lia. }
    assert (SSX1 : rw_cells asegs m1 A_SS [C8 (Z_to_bv 64 tf); C8 alloc]) by (eapply rw_cells_transport; [exact SSX| exact MU1| exact WM1| apply LO; unfold A_SS; clear - LOIMG; cbn; lia]).
    assert (DB1 : dblocks m1 bl) by (eapply (dblocks_transport _ m m1 bl DB MU1 WM1); apply LO; unfold A_SS; clear - LOIMG; lia).
    assert (HTR1 : u64arr asegs m1 TR ws) by (eapply u64arr_transport; [exact HTR| exact MU1| exact WM1| apply HI; clear - T0; lia]).
    assert (DS1 : dstatics m1).
    { destruct DS as [G1 G2]. split; (eapply ro_cells_transport; [eassumption| exact MU1| apply LO]); unfold A_GOT_CFLAGS, A_CFLAGS; cbn; clear - LOIMG; lia. }
    assert (SBLK1 : forall j', 0 <= j' < Z.of_nat (length bl) -> stk asegs m1 (sblk bl j') (sblk bl j' + 2^23) /\ crange CS (sblk bl j') (2^23)).
    { intros j' Hj'. destruct (SBLK j' Hj') as [S1 S2]. split; [|exact S2].
      eapply stk_transport_disjoint; [exact S1| exact MU1| exact WM1|]. apply LO.
      ddestruct DB as (_ & DBF & _). pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN.
      ddestruct (proj1 FN DBF (Z.to_nat j') 0 ltac:(lia)) as (X0 & X1 & _). unfold sblk in *. clear - X1 LOIMG. lia. }
    clear DT NC DM DN SSX DB HTR DS SBLK M1 M2 M3.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dfind_loop AL IMG ALWF CS CSOK (S (Z.to_nat v)) v nb N); try eassumption; try lia. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (pc & y0 & y1 & y2 & -> & CASES)).
    destruct CASES as [(-> & s & -> & SB) | (-> & ->)].
    - (* [comment removed for export] *)
      eapply evtA_mono.
      { eapply (dput_epi AL IMG ALWF CS CSOK); try eassumption; try lia; try apply munch_refl; try apply wmono_refl. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m2 & -> & MU2 & WM2 & MI2 & ST2)). left. unfold hit_post.
      exists s. deexists 12. split; [reflexivity|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2| exact SB].
    - (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (dput_ins_A AL IMG ALWF CS CSOK ra gp tp s5 s10 s11 t0 t1 t2 t3 t4 t5 t6 a7 y0 y2 (Z_to_bv 64 0x400008) x4 x5 x6 SP F fc m1 h bi v N lo nb);
          try eassumption; try lia. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (pc & r1 & r10 & r11 & x5' & x6' & x7' & x12 & x13 & x14 & x15 & x16 & x17 & lockw & m2 & -> & MU2 & WM2 & MI2 & TC2 & NC2 & ST2 & CASES)).
      assert (HI2 : forall A n, SP + -112 <= A -> disjoint_from [(lo, SP + -112); (A_DEP + 4 * bi, A_DEP + 4 * bi + 4); (A_DEP_N, A_DEP_N + 4)] A n).
      { intros A n H. unfold A_DEP, A_DEP_N in *. cbn [disjoint_from]. clear - H BI LOIMG SPL. lia. }
      assert (FRP2 : dput_frame m2 SP fr TR (size + tag * 2^32) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)
        by (eapply rw_cells_transport; [exact FRP1| exact MU2| exact WM2| apply HI2; clear; lia]).
      apply evtA_done. right. unfold headA_post. dexists h, bi, v, pc, r1, r10, r11. deexists 12.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
               eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
      split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
      split; [exact FRP2|]. split; [exact TC2|]. split; [exact NC2|]. split; [exact ST2|].
      split; [lia|]. split; [lia|]. split; [lia|].
      destruct CASES as [(-> & _ & KL & ->) | (-> & -> & KL & NK & -> & ->)]; [left | right]; repeat split; try assumption; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DepotF.

End ARUN_1.
