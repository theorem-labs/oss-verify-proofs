(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_F_memcpy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A HP_RF_am_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_am_E () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64s"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "Corelib.Init.Datatypes.app"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_E.am_init_st"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_init_done"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_secret"; "RP_1.ram_entry_post"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L61929833015.50L64303092338.49L8548902953.48 00000R00h01>S1D1S1n3src3LEN2D02D12S02S12N03SEPS1S1n3src3LEN2S02S12N0S1D1n3src3LEN2D02D12N0". (* [comment removed for export] *)
#[using="hRP"] Lemma rmemcpy_callZ3 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_E ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PD,$3.PS,$3.Pn,$3.Psrc,(4.(0.&8.))Pjunk,(4.(0.&8.))P,(5.$6.R6.R4.R2.)P,(7.$8.(9.(0.&8.)R3.)(:.R4.))P,(;.$6.R8.R7.(<.$=.(>.(:.R5.)R3.)(?.$=.)))P,(10.=R8.)P,(10.(11.R9.R7.)(12.+2.+40.))P,(10.=R9.)P,(10.(11.R:.R9.)(12.+2.+40.))P,(13.=R:.)P,(14.(10.(11.R<.R;.)R=.)(10.(11.R=.R;.)R<.))P,(15.$6.R?.)(16.$6.Lms',$17.(18.(0.&40.)Lt0',(0.&40.)(18.(0.&40.)Lt1',(0.&40.)(18.(0.&40.)Lt2',(0.&40.)(18.(0.&40.)La1',(0.&40.)(18.(0.&40.)La2',(0.&40.)(18.(0.&40.)La3',(0.&40.)(18.(0.&40.)La4',(0.&40.)(18.(0.&40.)La5',(0.&40.)(18.(0.&40.)La6',(0.&40.)(18.(0.&40.)La7',(0.&40.)(18.(0.&40.)Lt3',(0.&40.)(18.(0.&40.)Lt4',(0.&40.)(18.(0.&40.)Lt5',(0.&40.)(18.(0.&40.)Lt6',(0.&40.)(18.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(19.(7.$17.R10.(1:.(1;.R3>.R3=.R3<.R3;.R?.R>.R=.R37.R36.(1<.&40.R1?.)R<.R;.R:.R9.R8.R7.R6.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R5.R4.R3.R2.)R22.(1=.R3>.)R21.(1>.(0.&40.))R1.(1?.$6.)))(19.(20.(<.(21.$3.$3.)(22.$3.$3.R1?.(11.R1?.R1=.))(?.(21.$3.$3.)))R20.R1.)(19.(23.$6.R20.R1.)(19.(15.$6.R1.)(;.$6.R1.R1?.(<.$=.(>.(:.R1=.)R1<.)(?.$=.))))))))))))))))))))))(1:.(1;.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.(1<.&40.R?.)(1<.&40.R>.)(1<.&40.R=.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(1<.&40.+46:40.)R11.(1>.(0.&40.))R10.(1?.$6.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  ddestruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  deexists 15. split; [reflexivity|]. auto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L25273904528.16L46081068896.16L58870951973.16L61555382922.1600000@00U00h018S1i3pre4Hlen3HluS1i3pre4post4Hlen3HluS1i2Hi3pre4Hlen3HluS1i3pre4Hlen3Hlu". (* [comment removed for export] *)
#[using="hRP"] Lemma ru64s_read : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_E ()) "Pm,P,(0.&40.)(2.(0.&8.))PA,$3.Pws,(4.(0.&40.))Pi,$3.Pw,(0.&40.)Pa,(0.&40.)P,(5.$6.R6.R5.(24.R4.))P,(7.(2.(0.&40.))(25.(0.&40.)R5.(:.R4.))(26.(0.&40.)R3.))P,(10.=R5.)P,(7.(0.&40.)R4.(27.(11.R8.(28.+8.R6.))))(7.(2.(4.(0.&8.)))(29.$6.R:.R5.#8.)(26.(4.(0.&8.))(2:.R6.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L12627119992.10L17848223028.1000000;00BS1A3cs13cs2S1A3cs1". (* [comment removed for export] *)
#[using="hRP"] Lemma rrw_cells_app_split : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_E ()) "Pm,P,(0.&40.)(2.(0.&8.))PA,$3.Pcs1,(4.$=.)Pcs2,(4.$=.)P,(;.$6.R4.R3.(2;.$=.R2.R1.))(19.(;.$6.R5.R4.R3.)(;.$6.R5.(11.R4.(2<.(2=.R3.)))R2.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L1311789837.16 L19522555985.19L24931536571.16L53121998162.19L63892447207.1900000>00N00\00l01<S1A3cs13cs22H3S3cs13cs21i2Hi1HS1A3cs13cs22H0S1A3cs13cs21i2HiS3cs13cs21i2Hi1H". (* [comment removed for export] *)
#[using="hRP"] Lemma rrw_cells_app_join : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_E ()) "Pm,P,(0.&40.)(2.(0.&8.))PA,$3.Pcs1,(4.$=.)Pcs2,(4.$=.)P,(;.$6.R4.R3.R2.)P,(;.$6.R5.(11.R4.(2<.(2=.R3.)))R2.)(;.$6.R6.R5.(2;.$=.R4.R3.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. ddestruct W1 as (H0 & H1 & X1). ddestruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_E ()) "Lms',$17.(18.(0.&40.)Lx1,(0.&40.)(18.(0.&40.)Lt0,(0.&40.)(18.(0.&40.)Lt1,(0.&40.)(18.(0.&40.)Lt2,(0.&40.)(18.(0.&40.)Ls1x,(0.&40.)(18.(0.&40.)Ls4x,(0.&40.)(18.(0.&40.)La0,(0.&40.)(18.(0.&40.)La1,(0.&40.)(18.(0.&40.)La2,(0.&40.)(18.(0.&40.)La3,(0.&40.)(18.(0.&40.)La4,(0.&40.)(18.(0.&40.)La5,(0.&40.)(18.(0.&40.)La6,(0.&40.)(18.(0.&40.)La7,(0.&40.)(18.(0.&40.)Lt3,(0.&40.)(18.(0.&40.)Lt4,(0.&40.)(18.(0.&40.)Lt5,(0.&40.)(18.(0.&40.)Lt6,(0.&40.)(18.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(18.(4.(0.&8.))Ljunk,(4.(0.&8.))(19.(7.$17.R15.(1:.(1;.R14.(1<.&40.(11.(2>.&40.O14.)-40.))O13.O12.R13.R12.R11.(1<.&40.+1000.)R10.R>.R=.R<.R;.R:.R9.R8.R7.(1<.&40.$2?.)(1<.&40.$30.)R?.O<.O;.O:.O9.O8.O7.O6.R6.R5.R4.R3.)O5.(1<.&40.+40344.)O4.(1>.(0.&40.))R2.(1?.$6.)))(19.(20.(<.(21.$3.$3.)(22.$3.$3.(31.(2>.&40.O14.)+40.)(2>.&40.O14.))(<.(21.$3.$3.)(22.$3.$3.$32.(11.$32.+10.))(?.(21.$3.$3.))))O1.R2.)(19.(23.$6.O1.R2.)(19.(15.$6.R2.)(19.(;.$6.R2.(11.(2>.&40.O14.)-40.)(33.VhRP,R1.O=.O>.O?.O10.O11.O15.))(19.(34.$6.R2.O3.(11.(2>.&40.O14.)-40.))(35.VhRP,(36.O2.)R2.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0190@L11714716182.101L11801586693.106L12280974733.88 L12281056739.103L12753740126.88 L12937216788.87 L12937216788.88 L12937216788.89 L15045097248.86 L15226216740.87 L15226216740.88 L15226216740.89 L15648636875.106L17210337356.86 L17646078182.84 L17805285100.86 L19937319914.101L20314357271.106L20314357271.107L21473875220.87 L21473875220.88 L21473875220.89 L21542523261.105L22700267513.107L23811967384.85 L26405094859.106L29289735115.106L3049316236.102 L3049316236.87  L30985415188.86 L3122730443.106 L32467434613.106L32467434613.107L32539134702.106L3442237028.106 L3442237028.107 L34489533625.106L34712365207.106L34712365207.107L34774463764.87 L34774463764.88 L34774463764.89 L36192009725.105L36244065544.87 L36511751956.87 L36511751956.88 L36511751956.89 L36671707196.87 L40356513836.86 L40825509068.86 L41416020844.86 L43061792465.82 L44484923210.105L44945621387.106L46878830283.106L48831236093.105L49123722493.105L51587279636.87 L51587279636.88 L51587279636.89 L53427322480.86 L53990005404.86 L56537577096.87 L60542728832.87 L61238316461.87 L61238316461.88 L61238316461.89 L63368099340.86 L63370196603.87 L63967261868.86 L65502198668.86 L7381600893.105 L8374241300.87  00000100<00@00D00H00i01V02402502R03?03Y03Z03[03_03`03a04?04]05>05k06I06X06b06k06l06m07@07S07f07g08L09109209W0:<0:=0:[0;90;Z0<G0<e0=40=<0=]0>J0>h0?70?80?90?:0?F0?M0?X0?Y0?h0@70@X0AE0Ac0An0Ao0B70B?0B\0CI0Cc0Cd0Ce0Cf0Cg0D60DASS2sp3rnd2BRS2spS2spS2avS3hRP3RCB2ra2sp2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2s02AB2HB5Ha_st5Hl_st2s12s22s32s4S2sp3hRP3RCB2AB2HB5Ha_st5Hl_stSS2ra2sp2av3BAV2HB5Ha_st5Hl_stS2sp2s02av3BAV2HB5Ha_st5Hl_st2s12s22s32s43hRPS2sp2av3BAV2HB5Ha_st5Hl_stSSS2spSSS2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS3hRP3RCB2ra2sp2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2s02AB2HB5Ha_st5Hl_st2s12s22s32s4S2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2ABS2sp3x201HS2st4INITSSS2sp3hRP2lo2LO4LOLES2sp3hRP2lo2LO4LOLES2sp3hRP3RCB2AB3SPRSS2sp3hRP3RCB3rnd2AB2BR2HB5Ha_st5Hl_stS2sp3hRP3RCB3rnd2AB2BR2HB5Ha_st5Hl_stSS2sp3hRP3RCB2av2AB3BAV2HB5Ha_st5Hl_stS2sp3hRP3RCB2av2AB3BAV2HB5Ha_st5Hl_stFS2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS3hRP3RCB2ra2sp2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2s02AB2HB5Ha_st5Hl_st2s12s22s32s4S2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2ABS3rnd2XRS3hRP3RCB2ra2sp2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2s02AB2HB5Ha_st5Hl_st2s12s22s32s4S2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2ABSSSS2sp2lo4LOLES2sp2loS2sp2av3BAVSS2sp3hRP3RCB2ABS2sp3hRP3RCB2ABS3hRP3RCB2ra2sp2AB2HB5Ha_st5Hl_stS2sp3hRP3RCB2s02AB2HB5Ha_st5Hl_st2s12s22s32s4S2sp3hRP3RCB2AB2HB5Ha_st5Hl_stS3rnd2RH2XRSS2sp3SPRS3rnd2RHS2ra2sp3rnd2BR2HB5Ha_st5Hl_stS2sp2s03rnd2BR2HB5Ha_st5Hl_st2s12s22s32s43hRPS2sp3rnd2BR2HB5Ha_st5Hl_stSSSSS2sp3hRP3RCB2ABS2sp3rnd2BR". (* [comment removed for export] *)
#[using="Type"] Lemma ram_entry : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_E ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Plo,$3.Pst,$37.P,(35.VhRP,R1.R3.)P,(15.$6.R4.)P,(38.VhRP,R5.(2>.&40.R25.))P,(34.$6.R6.R5.(2>.&40.R26.))P,(10.(39.VhRP,)R6.)P,(10.R7.(31.(2>.&40.R28.)+40.))P,(14.(7.$3.(3:.(3;.R7.))=)(7.$3.(3:.(3;.R7.))+1.))P,(19.(10.=(3<.(3;.R8.)))(13.(3<.(3;.R8.))(12.+2.+40.)))(16.$6.(3=.R2<.R2;.R2:.R29.R25.R24.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R=.R<.R:.R9.R;.)(1:.(1;.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(1<.&40.+40290.)R<.(1>.(0.&40.))R;.(1?.$6.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR MI AUX ST LO LOLE INIT SECR. pose proof (rmrep_secret _ _ MR) as SEC0.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5) & _). unfold ctx_head_cells in C1.
  rceilb; unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. unfold wz in G4.
  (* [comment removed for export] *)
  move G4 at top.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  ddestruct AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & XHW & X6 & X11 & X12 & X23 & XR).
  unfold RAUXV_CELL in AVC.
  (* [comment removed for export] *)
  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{ (* [comment removed for export] *)
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. deexists 20. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; rceilb; lia. }
  (* [comment removed for export] *)
  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  Ltac skip_iter i key HB :=
    let RD := fresh "RD" in
    st1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ i (wz key) (wa (_ + 8 * i)) HB eq_refl ltac:(lia) eq_refl) as RD end;
    st1; try clear RD;
    st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
    st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
    st1.
  skip_iter 0 3 AVL.
  skip_iter 2 4 AVL. skip_iter 4 5 AVL. skip_iter 6 16 AVL (* [comment removed for export] *). skip_iter 8 6 AVL.
  skip_iter 10 11 AVL. skip_iter 12 12 AVL. skip_iter 14 23 AVL.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 16 (wz 25) (wa (_ + 8 * 16)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 17 (wz rnd) (wa (_ + 8 * 17)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD. st1. st1. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge rsegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  (* [comment removed for export] *)
  st1.
  call rmemcpy_callZ3.
  1:{ exact RND. } 1:{ rewrite length_le8; reflexivity. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end. }
  lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz rp_secret))] |- _ => rename H into DST end.
  (* [comment removed for export] *)
  st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 18 (wz 0) (wa (_ + 8 * 18)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
  st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells rsegs mX (bv_unsigned sp + -64) [C8 (wz rp_secret)])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; rceilb; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret rp_secret c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q). unfold wz at 2.
      lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.
  (* [comment removed for export] *)
  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells rsegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells rsegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge rsegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. deexists 20. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
