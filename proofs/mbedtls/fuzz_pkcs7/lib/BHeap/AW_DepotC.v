(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon AW_MmapDie AW_DepotA AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DepotC () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.eq"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.sptr"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "ARUN_1.dblocks"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8ro"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_IMEMCPY_LOOP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_IMEMCPY"; "stdpp.bitvector.definitions.bv_unsigned"; "ARUN_1.sblk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_BI_CREATE"; "ARUN_1.DepotC.alloc_post"; "ARUN_1.A_SS_ALLOC"].

Section ARUN_1. Context {hAR : arun}.
Definition A_IMEMCPY : Z := 0x7a9dc.
Definition A_IMEMCPY_LOOP : Z := 0x7a9e8.
Definition A_SS_ALLOC : Z := 0x0870c8.

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L26010794188.12L37405807067.13L4817866984.13 L54957159554.13L60252186448.1300000B00W00l01A01VS2ds1i2HL3pre4HlenS2ds1i2HL3pre4Hlen2L1S2ds1i2HL3pre4Hlen2L1S2ds1i2HL3pre4Hlen2L1S2ds1i2HL3pre4Hlen2L1". (* [comment removed for export] *)
#[using="Type"] Lemma firstn_upd_step : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Pds,(0.(1.&8.))Pss,(0.(1.&8.))Pi,$2.Pb,(1.&8.)P,(3.(0.(1.&8.))(4.(1.&8.)R2.R4.)(4.(1.&8.)R2.R3.))P,(3.(5.(1.&8.))(6.(1.&8.)R4.R3.)(7.(1.&8.)R2.))P,(8.R4.(9.(1.&8.)R6.))(3.(0.(1.&8.))(4.(1.&8.)(:.R5.)(;.(1.&8.)R7.R5.R4.))(4.(1.&8.)(:.R5.)R6.))")
(* [comment removed for export] *).
Proof.
  intros ds ss i b PRE HN HL.
  rewrite upd_firstn_skipn by exact HL.
  destruct (Arr.nth_error_split _ _ _ HN) as (pre & post & E & Hlen).
  assert (L1 : length (firstn i ds) = i) by (rewrite firstn_length; lia).
  rewrite firstn_app, L1. replace (S i - i)%nat with 1%nat by lia.
  rewrite firstn_all2 by lia. cbn [firstn].
  rewrite E, firstn_app, Hlen. replace (S i - i)%nat with 1%nat by lia. cbn [firstn].
  rewrite (firstn_all2 (n:=S i) pre) by lia. rewrite PRE. rewrite E at 1.
  rewrite firstn_app, Hlen, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sblk (bl : list Z) (j : Z) : Z := nth (Z.to_nat j) bl 0.
Definition sptr (bl : list Z) (j : Z) : Z := if j <? Z.of_nat (length bl) then sblk bl j else 0.
Definition dblocks (m : mem) (bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "(<.Pj,$=.P,(<.(>.=R1.)(?.R1.+1000.))(10.(1.&40.)Lstored,(1.&40.)(11.$12.O2.(13.(13.$14.+10.)(15.+10.R3.))(16.$17.(18.(19.&40.(1:.O1.R3.)))(16.$17.(1;.R1.)(16.$17.(1;.(19.&40.=))(1<.$17.))))))(<.(1=.$=.Lb,$=.(<.(>.+65?000.R1.)(<.(>.(13.R1.(1>.+2.+17.))(1?.VhAR,))(3.$=.(20.R1.+1000.)=)))O1.)(21.(9.$=.O1.)#1000.)))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L25105498149.800000?S2lo2hi2D11j2Hj". (* [comment removed for export] *)
#[using="Type"] Lemma dblocks_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "PW,(0.$22.)Pm,P,(1.&40.)(5.(1.&8.))Pm',P,(1.&40.)(5.(1.&8.))Pbl,(0.$=.)P,(23.R3.R1.)P,(24.R5.R4.R3.)P,(25.$12.R5.R4.)P,(26.R7.(13.$14.+10.)(15.+10.+1000.))(23.R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' bl dd_H; ddestruct dd_H as (DB & DF & DL); intros MU WM DJ). split; [|split; [exact DF| exact DL]].
  intros j Hj. destruct (DB j Hj) as (st & H). exists st. eapply rw_cells_transport; [exact H| exact MU| exact WM|].
  cbn [cells_size csize Nat.add]. clear -DJ Hj. unfold A_SS in *. induction W as [|[lo hi] W IH]; [exact I|].
  destruct DJ as [D1 D2]. split; [lia| apply IH; exact D2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma dblocks_reest : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "PE,P,$=.SpPW,(0.$22.)Pm,P,(1.&40.)(5.(1.&8.))Pm',P,(1.&40.)(5.(1.&8.))Pbl,(0.$=.)P,Pj,$=.P,(<.(>.=R1.)(?.R1.+1000.))P,(27.A1.R7.R2.)(10.(1.&40.)Lst,(1.&40.)(11.$12.R7.(13.(13.$14.+10.)(15.+10.R4.))(16.$17.(18.(19.&40.(1:.R5.R4.)))(16.$17.(1;.R1.)(16.$17.(1;.(19.&40.=))(1<.$17.))))))P,Pj,$=.P,(<.(>.=R1.)(?.R1.+1000.))P,A1.R8.R2.(10.(1.&40.)Lst,(1.&40.)(11.$12.R7.(13.(13.$14.+10.)(15.+10.R4.))(16.$17.(18.(19.&40.(1:.R6.R4.)))(16.$17.(1;.R1.)(16.$17.(1;.(19.&40.=))(1<.$17.))))))P,Pj,$=.(28.A1.R8.R1.(27.A1.R8.R1.))P,(1=.$=.Lb,$=.(<.(>.+65?000.R1.)(<.(>.(13.R1.(1>.+2.+17.))(1?.VhAR,))(3.$=.(20.R1.+1000.)=)))R4.)P,(21.(9.$=.R5.)#1000.)P,(24.R9.R8.R7.)P,(25.$12.R9.R8.)P,Pj,$=.P,(<.(>.=R1.)(?.R1.+1000.))P,(27.A1.R>.R2.)(26.R>.(13.(13.$14.+10.)(15.+10.R3.))+10.)(23.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros E W m m' bl OTH NEW DEC DF DL MU WM DJ. split; [|split; [exact DF| exact DL]].
  intros j Hj. destruct (DEC j) as [Ej|NEj]; [apply NEW; assumption|].
  destruct (OTH j Hj NEj) as (st & H). exists st. eapply rw_cells_transport; [exact H| exact MU| exact WM|].
  cbn [cells_size csize Nat.add]. apply DJ; assumption.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L18926399351.13L18926720323.6 L18930743321.7 L18932946886.10L24938537269.13L34282026578.13L41624202307.12L41624202307.13L4501977880.13 L56748220474.13L59314938599.12L59873440153.12L62811272829.13L64265955603.13L64272077992.13L64293818747.12L8026626546.10 00000A00B00I00T00m01>01T01j02C02\03803P03l04@04U04f059S2tf5count2H01q1rSS2tf2H0S2tf2H01q1rS2tf5count2H02HC1q1r1E2R1S2tf5count2H01q1rS2tf5count2H02HC1q1r1HS2tf5count2H02HC1q1r1HS2tf5count2H02HC1q1r1B2R1S2tf5count2H02HC1q1r1E2R1S2tf5count2H02HC1q2NE1r2C11DS2tf5count2H02HC1q1r1B1HS2tf5count2H01q1r2C11D2R12HCS2tf5count2H01q1r2R1S2tf5count2H01q1r1D1HS2tf5count2H01q1rS2tf5count2H01q1r1E". (* [comment removed for export] *)
#[using="Type"] Lemma straddle_arith : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Ptf,$=.Pcount,$=.P,(>.=R2.)P,(<.(>.+2.R2.)(>.R2.+20.))P,(27.(3.$=.(29.R4.+100000.)(29.(2:.(13.R4.R3.)+1.)+100000.)))(<.(3.$=.(29.(13.R5.R4.)+100000.)(13.(29.R5.+100000.)+1.))(<.(3.$=.(29.(2:.(13.R5.R4.)+1.)+100000.)(13.(29.R5.+100000.)+1.))(<.(3.$=.(29.(2:.(13.(13.R5.R4.)R4.)+1.)+100000.)(13.(29.R5.+100000.)+1.))(<.(>.+100000.(2:.(13.(20.R5.+100000.)R4.)+1.))(3.$=.(20.(13.R5.R4.)+100000.)(2:.(13.(20.R5.+100000.)R4.)+100000.))))))")
(* [comment removed for export] *).
Proof.
  intros tf count H0 HC NE.
  pose proof (Z.div_mod tf 1048576 ltac:(lia)) as E. pose proof (Z.mod_pos_bound tf 1048576 ltac:(lia)) as B.
  set (q := tf / 1048576) in *. set (r := tf mod 1048576) in *.
  assert (C1 : (tf + count - 1) / 1048576 = q + (r + count - 1) / 1048576).
  { replace (tf + count - 1) with (q * 1048576 + (r + count - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  assert (D01 : (r + count - 1) / 1048576 = 0 \/ (r + count - 1) / 1048576 = 1).
  { destruct (Z.lt_ge_cases (r + count - 1) 1048576).
    - left. apply Z.div_small. lia.
    - right. symmetry. apply Z.div_unique with (r := r + count - 1 - 1048576); lia. }
  assert (R1 : 1048576 <= r + count - 1) by (destruct D01 as [D|D]; [exfalso; lia|]; destruct (Z.lt_ge_cases (r + count - 1) 1048576); [rewrite Z.div_small in D by lia; lia| lia]).
  repeat split.
  - replace (tf + count) with ((q + 1) * 1048576 + (r + count - 1048576)) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - destruct D01 as [D|D]; lia.
  - replace (tf + count + count - 1) with ((q + 1) * 1048576 + (r + count + count - 1 - 1048576)) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - lia.
  - replace (tf + count) with ((r + count - 1048576) + (q + 1) * 1048576) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section DepotC.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0?L10351592143.68L11370340730.70L11370340730.71L12965493700.69L17295135606.69L19524653911.68L19526868180.69L19626380277.68L19706191991.69L20647521649.68L20843738630.69L21136494596.70L23502577467.68L25180034572.67L28562557131.69L29872649782.68L31403258585.69L3447078412.69 L36666933519.61L41253120083.72L41253120341.70L42216591364.70L43108442037.68L45386353571.69L51441930133.69L55295628407.73L55356808853.69L57485979241.72L5949147555.69 L60010326172.68L7892063709.70 00000D00_01:01;01W01n02E02c03C03a04404O04g06o07?07W07k08J0:J0:a0;80;S0;k0<?0<S0<T0=00=T0=U0=m0>ES1k1i1n2ds2ss2Hi3HinS1k1i1n3DST2ds2ss2Hi3Hin2D0S1k1i1n3DST2ds2ss2Hi3Hin2D0FS1k1i1n3DST2ds2ss2Hi3Hin3KneS1k1i1n2ds2ss2Hi3Hin2LDS1k1i1n2ds2ss2Hi3Hin2LDS1k1i1n3DST2ds2ss2Hi3Hin2D02DHS1k1i1n3DST3SRC2ds2ss2Hi3Hin3KneS1k1i1n3DST2ds2ss2Hi3Hin2D02DHS1k1i1n2ds2ss2Hi2LDS1k1i1n3DST2ds2ss2Hi2LS3KneS1k1i1n3SRC2ds2ss2Hi3HinS2AL2CS1k1i1n3DST3SRC2ds2ss2ra2sp2gp2tp2t02t12t22s02s12a02a42a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc2m01m2Hi3Hin2LS2HNS1k1i1n2ds2ss2HiS1k1i1n3SRC2ds2ss2Hi3HinS1k1i1n3SRC2ds2ss2HiS1k1i1n2ds2ss2Hi3Hin2LD3DST3KneS2AL2CS1i1n3DST3SRC2ds2ss2ra2sp2gp2tp2t02t12t22s02s12a02a42a52a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc2m01m2Hi3HinS1k1i1n3DST2ds2ss2Hi2DHS1k1i1n3DST2ds2ss2Hi2DHS1k1i1n3DST2ds2ss2Hi2LD3KneS1k1i1n3DST2ds2ss2Hi3HinS1k1i1n3DST2ds2ss2HiS1k1i1n2ds2ss2Hi3HinFS1k1i1n3DST2ds2ss2Hi3Hin3KneS1k1i1n3DST3SRC2ds2ss2Hi3Hin2LS2DJ1bFS1k1i1n3DST2ds2ss2Hi3HinS1k1i1n3DST2ds2ss2Hi3Hin". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imemcpy_loop : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Pk,$2.Pi,$=.Pn,$=.PDST,$=.PSRC,$=.Pcs,$=.Pcd,$=.Pds,(0.(1.&8.))Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2;.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(5.(1.&8.))Pm,P,(1.&40.)(5.(1.&8.))P,(3.$=.R28.(2:.R27.(2<.R29.)))P,(<.(>.=R29.)(?.R29.R28.))P,(3.$=.R26.(13.R27.R2:.))P,(3.$=.R26.(13.R29.R2;.))P,(2=.$12.R5.R2:.R26.)P,(2>.$12.R6.R2:.R26.)P,(3.$=.(2<.(9.(1.&8.)R28.))R2=.)P,(3.$=.(2<.(9.(1.&8.)R28.))R2>.)P,(3.(0.(1.&8.))(4.(1.&8.)(2?.R30.)R2:.)(4.(1.&8.)(2?.R30.)R29.))P,(?.=R2?.)P,(?.=R2?.)P,(28.(>.(13.R31.R32.)R30.)(>.(13.R30.R32.)R31.))P,(>.(13.R32.R33.)(1>.+2.+3?.))P,(>.(13.R32.R34.)(1>.+2.+3?.))P,(30.VCS,R34.R35.)P,(30.VCS,R34.R36.)P,(24.(16.(31.$=.$=.)(32.$=.$=.R36.(13.R36.R37.))(1<.(31.$=.$=.)))R12.R11.)P,(25.$12.R13.R12.)P,(33.$12.R13.)(34.$12.VAL,VCS,Lms',$35.(10.(1.&40.)Lx4,(1.&40.)(10.P,(1.&40.)(5.(1.&8.))Lm',P,(1.&40.)(5.(1.&8.))(<.(3.$35.R3.(36.(37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.(19.&40.(13.R3;.R3=.))(19.&40.(13.R3<.R3=.))(19.&40.(13.R3<.R3=.))R2.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(19.&40.+7:9?<.)R19.(38.(1.&40.))R1.(39.$12.)))(<.(24.(16.(31.$=.$=.)(32.$=.$=.R3<.(13.R3<.R3=.))(1<.(31.$=.$=.)))R18.R1.)(<.(25.$12.R18.R1.)(<.(33.$12.R1.)(2=.$12.R1.R3<.R37.)))))))(36.(37.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.(19.&40.R37.)(19.&40.(13.R39.R3:.))(19.&40.R36.)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(19.&40.$3:.)R16.(38.(1.&40.))R14.(39.$12.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i n DST SRC cs cd ds ss ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
      Hi Hin -> -> HD HS LD LS PRE D0 S0 DJ DH SH DCS SCS MU WM MI; [lia|].
    facts. unfold A_IMEMCPY_LOOP.
    (* [comment removed for export] *)
    destruct (nth_error ss (Z.to_nat i)) as [b|] eqn:HN; [| apply nth_error_None in HN; lia].
    pose proof (u8ro_read asegs m SRC ss i b (wa (SRC + i)) HS HN ltac:(lia) eq_refl) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok asegs m DST ds i _ HD ltac:(lia) eq_refl) as SOK.
    zstep.
    change (Z_to_bv 64 (bv_unsigned b)) with (zxb b). rewrite (le1_zxb b).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a _) _) =>
      pose proof (u8arr_write asegs mx DST ds i b HD ltac:(lia)) as HD'
    end.
    store_done. try clear HD. rename HD' into HD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kne; zify_cond Kne.
    - (* [comment removed for export] *)
      eapply (IH (i + 1) n DST SRC _ _ (upd ds (Z.to_nat i) b) ss); try eassumption; try lia.
      + rewrite upd_length. lia.
      + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply firstn_upd_step; [exact PRE| exact HN| lia].
    - apply evtA_done. replace (DST + i + 1) with (DST + n) by lia. replace (SRC + i + 1) with (SRC + n) by lia.
      deexists 2. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      replace ss with (upd ds (Z.to_nat i) b); [exact HD|].
      pose proof (firstn_upd_step ds ss (Z.to_nat i) b PRE HN ltac:(lia)) as E.
      rewrite !firstn_all2 in E by (rewrite ?upd_length; lia). exact E.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L21007957267.61L21689588103.61L33875860785.61L36347256419.61L392815877.61  L59308637593.61L61929805272.6000000<00G00S00T00_00n01DS1n2ds2ss2N0S3SRC2ds2ssS1n2ds2ss2N0FS3DST2ds2ssS1n2ds2ss2N02KzS1n3DST2ds2ss2N02D02DH". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imemcpy_spec : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Pn,$=.PDST,$=.PSRC,$=.Pds,(0.(1.&8.))Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2;.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(5.(1.&8.))P,(?.=R24.)P,(2=.$12.R2.R24.R22.)P,(2>.$12.R3.R24.R22.)P,(3.$=.(2<.(9.(1.&8.)R24.))R27.)P,(3.$=.(2<.(9.(1.&8.)R24.))R28.)P,(?.=R28.)P,(?.=R28.)P,(28.(>.(13.R2:.R2;.)R29.)(>.(13.R29.R2;.)R2:.))P,(>.(13.R2;.R2<.)(1>.+2.+3?.))P,(>.(13.R2;.R2=.)(1>.+2.+3?.))P,(30.VCS,R2=.R2>.)P,(30.VCS,R2=.R2?.)P,(33.$12.R=.)(34.$12.VAL,VCS,Lms',$35.(10.(1.&40.)Lx2,(1.&40.)(10.(1.&40.)Lx3,(1.&40.)(10.(1.&40.)Lx4,(1.&40.)(10.P,(1.&40.)(5.(1.&8.))Lm',P,(1.&40.)(5.(1.&8.))(<.(3.$35.R5.(36.(37.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.(19.&40.R35.)(19.&40.(13.R34.R36.))R4.R3.R2.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(3;.R31.)R14.(38.(1.&40.))R1.(39.$12.)))(<.(24.(16.(31.$=.$=.)(32.$=.$=.R35.(13.R35.R36.))(1<.(31.$=.$=.)))R13.R1.)(<.(25.$12.R13.R1.)(<.(33.$12.R1.)(2=.$12.R1.R35.R32.)))))))))(36.(37.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.(19.&40.R30.)(19.&40.R2?.)(19.&40.R31.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(19.&40.$3<.)R?.(38.(1.&40.))R>.(39.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros n DST SRC ds ss ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      N0 HD HS LD LS D0 S0 DJ DH SH DCS SCS MI.
    facts. unfold A_IMEMCPY. pose proof (munch_refl [(DST, DST + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz. { exfalso. lia. }
    zstep. zstep.
    eapply evtA_cut.
    { eapply (imemcpy_loop (Z.to_nat n) 0 n DST SRC _ _ ds ss); try eassumption; try lia. reflexivity. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x4 & m' & -> & MU' & WM' & MI' & HD')).
    (* [comment removed for export] *)
    zstep. apply evtA_done. deexists 4.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|eassumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition alloc_post (ra : word) (SP : Z) (gp tp t4 t5 t6 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 : word) (a3 : word)
      (F : bvmap 5 word) (fc : bv 32) (IDX PACK tf count lo : Z) (bl : list Z) (alloc : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Lms',$35.(10.$=.Lstart,$=.(10.$=.Lpc,$=.(10.(1.&40.)Lx5,(1.&40.)(10.(1.&40.)Lx6,(1.&40.)(10.(1.&40.)Lx7,(1.&40.)(10.(1.&40.)Lx2,(1.&40.)(10.(1.&40.)Lx4,(1.&40.)(10.(1.&40.)Lx16,(1.&40.)(10.(1.&40.)Lx17,(1.&40.)(10.(1.&40.)Lx28,(1.&40.)(10.(1.&40.)Lpk,(1.&40.)(10.(1.&40.)Lr0,(1.&40.)(10.(1.&40.)Lr8,(1.&40.)(10.(1.&40.)Lr1,(1.&40.)(10.(1.&40.)Lres,(1.&40.)(10.P,(1.&40.)(5.(1.&8.))Lm',P,(1.&40.)(5.(1.&8.))(<.(3.$35.R11.(36.(37.R3.R5.O1<.O1;.R>.R=.R<.R4.O17.R2.(19.&40.$14.)R;.O;.R:.(19.&40.O5.)R9.R8.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R7.O1:.O19.O18.)O:.(19.&40.R?.)O9.(38.(1.&40.))R1.(39.$12.)))(<.(24.(16.(31.$=.$=.)(32.$=.$=.O4.O1=.)(16.(31.$=.$=.)(32.$=.$=.$14.(13.(13.$14.+10.)(15.+10.+1000.)))(16.(31.$=.$=.)(32.$=.$=.O8.(13.O8.+8.))(16.(31.$=.$=.)(32.$=.$=.O7.(13.O7.+8.))(1<.(31.$=.$=.))))))O1.R1.)(<.(25.$12.O1.R1.)(<.(33.$12.R1.)(<.(11.$12.R1.$14.(16.$17.(18.(19.&40.(13.R10.O5.)))(16.$17.(18.O2.)(1<.$17.))))(<.(23.R1.O3.)(<.(11.$12.R1.O8.(16.$17.(18.(19.&40.R10.))(1<.$17.)))(<.(11.$12.R1.O7.(16.$17.(18.R6.)(1<.$17.)))(<.(28.(3.$=.R10.O6.)(<.(3.$=.R10.(13.O6.O5.))(?.(29.O6.(1>.+2.+14.))(29.(2:.(13.O6.O5.)+1.)(1>.+2.+14.)))))(<.(3.$=.(29.R10.(1>.+2.+14.))(29.(2:.(13.R10.O5.)+1.)(1>.+2.+14.)))(28.(<.(3.$=.R?.(3=.&40.(3;.O1>.)))(<.(3.(1.&40.)R3.O1>.)(<.(3.(1.&40.)R5.(19.&40.O1=.))(<.(3.(1.&40.)R4.O<.)(<.(?.(29.R10.(1>.+2.+14.))(2<.(9.$=.O3.)))(<.(3.(1.&40.)R2.(19.&40.(13.(3>.O3.(29.R10.(1>.+2.+14.)))(15.+8.(20.R10.(1>.+2.+14.))))))(3?.$12.R1.O4.O1=.)))))))(<.(3.$=.R?.$40.)(<.(3.(1.&40.)R3.(19.&40.+871=<.))(<.(3.(1.&40.)R5.(19.&40.(13.O1=.-10.)))(<.(3.(1.&40.)R4.(19.&40.R10.))(<.(3.$=.(29.R10.(1>.+2.+14.))(2<.(9.$=.O3.)))(<.(3.(1.&40.)R2.(19.&40.(13.(13.$14.+10.)(15.+10.(29.R10.(1>.+2.+14.))))))(<.(11.$12.R1.(13.O1=.-10.)(16.$17.(18.O<.)(16.$17.(18.O1>.)(1<.$17.))))(3?.$12.R1.O4.(13.O1=.-10.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L21033535062.8L21420736375.8L42950988582.8L8896303734.8 000003004005006S1xSSS". (* [comment removed for export] *)
  #[using="Type"] Lemma shl44_shr41 : forall x, 0 <= x < 2^64 -> Z.shiftr (Z.shiftl x 44 mod 18446744073709551616) 41 = 8 * (x mod 2^20).
  Proof.
    intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    change 18446744073709551616 with (2^20 * 2^44). rewrite Zmult_mod_distr_r.
    change (2^44) with (8 * 2^41). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00a0?L13495378807.88L16328246242.87L16786962785.87L16901216767.83L18941427511.80L19517082239.83L19860782912.80L21991601993.88L23585410382.88L2582463194.89 L25936734760.83L29540029262.12L30736976591.85L31947676840.83L31947676840.89L32410993720.86L32726146164.82L33069704969.88L35159332395.80L35683490024.82L3765119577.82 L38161912686.89L38164579086.89L38758412167.89L39594897244.88L40683086415.85L40825262534.87L44017511980.86L4838750501.88 L48792421578.86L49263641680.88L50656252574.85L53522082987.82L53578351378.89L56044590680.87L56440102736.84L56441741038.87L56441741038.89L58843485848.92L59308742992.92L62920645534.89L62920645534.90L62920739953.84L63554435408.86L64014136920.90L64105178562.82L65651403371.82L8379261393.3  L8682110429.82 00000i00j01T02502X03904604]05D06706\07C07j08O09=09>09Y0:f0;I0;J0;K0<50<^0=k0?40?[0@B0@i0AP0B70C40C\0D@0Dg0EZ0FD0Fn0G\0HM0I>0Ie0JL0K30L40M40MW0N>0NK0NLS2SP3IDX4PACK5start5count2bl2S03blk3DBL2I02HB5Ha_st5Hl_stFS2SP3IDX4PACK5start5count2bl2S03blk3DBL2HBS2SP5start5count2lo2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03DBLS2SP5start5count2lo2bl2S03blk3DBLS2SP3IDX4PACK5start5count2lo2bl3CNT2S02S13DBL2I02P05LOIMG3SPLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS3hAR2SP3IDX4PACK2tf5start5count2bl2S03blk2SL3DBL1nS2SP5start5count2lo2bl2S03blk3DBL3SPLS2SP3IDX5start2lo3blk2I05LOIMG3SPL1j2HjS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP5start5count2lo2bl2S03blk3DBL3SPLS2SP3IDX4PACK5start5count2lo2bl2S03blk3DBL3SPLFS5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2lo2bl2S03blk3DBL2I02P05LOIMG3SPL3BLK2HB5Ha_st5Hl_stS2SP3IDX4PACK5start5count2bl2S03DBLFFS2SP3IDX4PACK5start5count2bl2S03blk3DBL2KLS2SP3IDX4PACK5start5count2bl2S03blk3DBL1lS2SP3IDX4PACK5start5count2lo2bl3CNT2S03blk2SB3DBL2I02P03IAL3PAL5LOIMG3SPL3SPAS2SP3IDX4PACK5start5count2lo2bl2S03blk3DBL2I02P05LOIMG3SPL2HB5Ha_st5Hl_stS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS3hAR2SP3IDX4PACK5start5count2bl2S03blk3DBL2IP2HB5Ha_st5Hl_stS2SP3IDX4PACK5start5count2bl3blk3DBL3BLKS2AL5start5count2bl2S03blk3DBL5ALWF'S2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBL2I12HB5Ha_stS2SP3IDX4PACK5start5count2bl3CNT2S02S13DBLS2SP3IDX4PACK5start5count2bl3CNT2S02S13DBLS2SP3IDX4PACK5start5count2bl3CNT2S02S13blk3DBLS3hAR2SP3IDX4PACK5start5count2bl2S03blk3DBL2B02B1S3hAR2SP3IDX4PACK5start5count2bl2S03blk3DBL2Kb2B0S2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2bl2S03blk3DBLS2SP3IDX4PACK5start5count2lo2bl3CNT2S02S13blk3DBL2I02P05LOIMG3SPLS2SP3IDX4PACK5start5count2lo2bl3CNT2S03blk3DBL2I02P05LOIMG3SPL1lS2AL5start5count2bl2S03blk3DBL4IMG'S2AL5start5count2bl2S03blk3DBL4IMG'3BLKS5start3blk1jF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ss_alloc_tail : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pa0,(1.&40.)Pa4,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Palloc,(1.&40.)Pidx0,(1.&40.)Ppkw,(1.&40.)PSP,$=.PF,(2;.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(5.(1.&8.))Pm,P,(1.&40.)(5.(1.&8.))PIDX,$=.PPACK,$=.Ptf,$=.Pstart,$=.Pcount,$=.Plo,$=.Pbl,(0.$=.)P,(<.(>.+2.R3.)(>.R3.+20.))P,(>.=R5.)P,(?.(13.R6.R5.)(1>.+2.+20.))P,(28.(3.$=.R7.R8.)(<.(3.$=.R7.(13.R8.R6.))(?.(29.R8.(1>.+2.+14.))(29.(2:.(13.R8.R6.)+1.)(1>.+2.+14.)))))P,(3.$=.(29.R8.(1>.+2.+14.))(29.(2:.(13.R8.R7.)+1.)(1>.+2.+14.)))P,(>.(29.R9.(1>.+2.+14.))(2<.(9.$=.R6.)))P,(11.$12.R>.$14.(16.$17.(18.(19.&40.(13.R:.R9.)))(16.$17.(18.R15.)(1<.$17.))))P,(23.R?.R8.)P,(11.$12.R10.R?.(16.$17.(18.R16.)(1<.$17.)))P,(11.$12.R11.R?.(16.$17.(18.R16.)(1<.$17.)))P,(11.$12.R12.(13.R16.-10.)(16.$17.(18.R2=.)(16.$17.(18.R32.)(1<.$17.))))P,(>.R17.R12.)P,(>.(13.R13.+8.)(1>.+2.+3?.))P,(>.R19.R13.)P,(>.(13.R14.+8.)(1>.+2.+3?.))P,(28.(>.(13.R16.+8.)R15.)(>.(13.R15.+8.)R16.))P,(3.$=.(20.R17.+8.)=)P,(3.$=.(20.R17.+8.)=)P,(30.VCS,R19.+8.)P,(30.VCS,R19.+8.)P,(3?.$12.R1<.R16.(13.R20.-10.))P,(>.+65?000.R17.)P,(>.R18.(2:.R22.+10.))P,(>.R23.(1>.+2.+3?.))P,(3.$=.(20.R24.+10.)=)P,(30.VCS,R1;.(2:.R25.R1;.))P,(24.(16.(31.$=.$=.)(32.$=.$=.R1<.R26.)(16.(31.$=.$=.)(32.$=.$=.$14.(13.(13.$14.+10.)(15.+10.+1000.)))(16.(31.$=.$=.)(32.$=.$=.R21.(13.R21.+8.))(16.(31.$=.$=.)(32.$=.$=.R20.(13.R20.+8.))(1<.(31.$=.$=.))))))R23.R22.)P,(25.$12.R24.R23.)P,(33.$12.R24.)(34.$12.VAL,VCS,(41.R45.R29.R44.R43.R33.R32.R31.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R40.(19.&40.R23.)R28.R27.R24.R23.R22.R20.R1?.R1>.R2<.R26.)(36.(37.R45.(19.&40.(13.R29.-10.))R44.R43.(19.&40.(29.R21.(1>.+2.+14.)))R42.R41.(19.&40.R21.)R3?.R30.(19.&40.$14.)(19.&40.R24.)(19.&40.R23.)R2?.(19.&40.R20.)R2>.R2=.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R28.(19.&40.+870?4.)R27.(38.(1.&40.))R25.(39.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a4 a6 a7 alloc idx0 pkw SP F fc m0 m IDX PACK tf start count lo bl
      CNT S0 S1 SE SB SL SSX DB IX PX FR I0 I1 P0 P1 IP IAL PAL ICS PCS ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_SS in *. change (1947848 + 16) with 1947864 in *.
    ddestruct DB as (DB1 & DBF & DBL).
    change (2^20) with 1048576 in *. set (blk := start / 1048576) in *.
    assert (BLK : 0 <= blk < 4096) by (subst blk; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    destruct (DB1 blk BLK) as (stw & BC). unfold A_SS in BC.
    replace (1947848 + 16 + 16 * blk) with (1947848 + blk * 16 + 16) in BC by lia.
    assert (OTH : forall j', 0 <= j' < 4096 -> ~ (j' = blk) -> exists st, rw_cells asegs m (A_SS + 16 + 16 * j') [C8 (Z_to_bv 64 (sptr bl j')); C4 st; C4 (Z_to_bv 64 0)])
      by (intros j' H1 H2; apply DB1; exact H1).
    clear DB1.
    pose proof (munch_refl [(IDX, IDX + 8)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.
    (* [comment removed for export] *)
    zstep. rewrite Z.shiftr_div_pow2, (Z.div_small start (2^32)) by lia.
    zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 blk 4) by lia. change (2^4) with 16.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *)
      assert (KL : blk = Z.of_nat (length bl)).
      { unfold sptr in Kb. destruct (Z.ltb_spec0 blk (Z.of_nat (length bl))); [| lia].
        exfalso. pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN.
        ddestruct (proj1 FN DBF (Z.to_nat blk) 0 ltac:(lia)) as (B0 & B1 & _). unfold sblk in Kb.
        rewrite Z.mod_small in Kb by lia. lia. }
      zstep. zstep.
      apply evtA_done. unfold alloc_post, A_SS, A_BI_CREATE. dexists start, 0x087ab0. deexists 14.
      split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split. { eapply (dblocks_reest (fun j => j = blk) [(IDX, IDX + 8)] m); [exact OTH| | intros j; clear; lia| exact DBF| exact DBL| exact MU2| exact WM2|].
               - intros j Hj ->. eexists. unfold A_SS. replace (1947848 + 16 + 16 * blk) with (1947848 + blk * 16 + 16) by lia. eassumption.
               - intros j Hj NE. unfold A_SS. cbn. clear - Hj NE BLK I0 LOIMG SPL. lia. }
      split; [eassumption|]. split; [eassumption|]. split; [exact SE|]. split; [exact SB|].
      right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact KL|]. split; [f_equal; lia|]. split; assumption.
    - (* [comment removed for export] *)
      assert (KL : blk < Z.of_nat (length bl)).
      { unfold sptr in Kb. destruct (Z.ltb_spec0 blk (Z.of_nat (length bl))); [lia|]. exfalso. apply Kb. reflexivity. }
      unfold sptr. replace (blk <? Z.of_nat (length bl)) with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. zstep. rewrite (shl44_shr41 start) by lia. change (2^20) with 1048576.
      zstep. zstep. zstep. zstep.
      replace (SP + -16 + 16) with SP by lia. zstep.
      match goal with H : rw_cells _ _ (SP + -16) _ |- _ => release_frame H ST SP end.
      apply evtA_done. unfold alloc_post, A_SS, A_BI_CREATE. dexists start, (bv_unsigned (ret_pc ra)). deexists 14.
      split. { rewrite Z_to_bv_bv_unsigned. reflexivity. }
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split. { eapply (dblocks_reest (fun j => j = blk) [(IDX, IDX + 8)] m); [exact OTH| | intros j; clear; lia| exact DBF| exact DBL| exact MU2| exact WM2|].
               - intros j Hj ->. eexists. unfold A_SS. replace (1947848 + 16 + 16 * blk) with (1947848 + blk * 16 + 16) by lia. eassumption.
               - intros j Hj NE. unfold A_SS. cbn. clear - Hj NE BLK I0 LOIMG SPL. lia. }
      split; [eassumption|]. split; [eassumption|]. split; [exact SE|]. split; [exact SB|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact KL|]. split; [f_equal; lia|]. assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "02I0?L11370285727.76L11370581909.91L11482451736.97L13049257242.81L13350219423.96L14132756745.90L14133108724.91L14519609183.96L14687350362.3 L16127022420.82L16127022420.83L16127022420.98L16127022420.99L16144099947.97L1628955942.80 L1628955942.81 L1628955942.96 L1628955942.97 L16901428961.76L18396304292.97L18926385705.84L18926774381.96L18926775545.78L19340330555.95L19342040646.80L19342040646.96L19465279371.79L19465572993.95L19516900705.75L19626381153.96L19910437653.97L21913926156.76L21914091270.91L22524581708.91L22524744262.76L23256618216.99L23585410382.79L2366367711.79 L23977527371.96L23977527371.97L24125082750.95L2591794024.96 L2591794027.96 L25936553270.75L27924720421.79L27924840178.96L28041632991.97L28041632991.98L29122257813.90L29122411880.91L29243412126.97L30547143273.78L30547539862.79L306865516.92  L308867765.98  L3153725203.97 L3153725203.98 L31612845069.98L31947592630.76L32267020594.91L32267185208.76L33041267188.79L33282021991.99L33740621456.76L33740850074.91L35106341640.81L35106341640.97L35203061249.95L35203061250.95L35908294402.95L36488412050.82L36488412050.83L36488412050.98L36488412050.99L37329063974.99L37761343803.94L37761761222.95L39304300264.77L40823349102.96L40824912411.76L40825208593.91L40825294651.95L41720123547.96L43935884375.90L43936299690.91L46677605191.82L46677605191.98L46809601798.91L46809764364.76L47258619584.83L47258619584.99L47735081164.83L47735081164.99L47754107163.90L4838750501.80 L48829877873.96L49033520107.91L49033968918.90L49225653524.81L49225653524.82L49225653524.97L49225653524.98L49698585326.80L49698585326.81L49698585326.96L49698585326.97L50525371386.80L50656283747.94L51427585247.79L51427719695.84L52144837413.84L52566949988.14L53522065825.76L53522117206.90L53522230443.91L54127084603.98L54494111075.98L54496113338.92L55041910599.94L55044006597.78L55044407098.79L55262987142.79L57732951602.88L58272418673.81L58272418673.97L58459420406.79L58459420406.80L58621197378.91L58621600447.90L59308634630.95L59310732048.6 L59576990311.94L59579230769.95L59579230770.95L59879084381.91L59879231392.90L60061618800.79L60234967559.94L60237216338.95L61459283268.97L63468839727.80L63924496302.95L63924633285.96L6597240291.80 L66613222439.99L66795794069.79L7243903434.79 L8927213217.95 L8927213218.95 L8927461002.95 L9240251684.90 L9240433625.91 L9654815847.96 00000100201B01X02=02V02o03T03^04F04n06>07N08]09@09c0:f0;i0<60=60=S0>40>Q0?60?I0?n0@d0Al0B90C50C60CI0Cj0DK0DZ0E^0F10FN0G60G^0H?0Hd0II0IZ0J70J\0Kl0M<0M=0M>0Mf0N^0OV0P;0P`0QY0RR0SC0ST0SU0SV0TU0U]0Ud0V=0VY0WG0WH0WI0X20XZ0YB0ZR0[b0]:0^B0_J0_d0`I0`J0`K0a00a10aN0ak0bj0d10dJ0dQ0eP0fW0gV0h]0iF0iY0j>0jc0kH0lD0m@0nP0o`10@10`11N12<12X13A13X14514m15Y15i16K16m18818]19B19g1:H1:c1;61;_1<51<]1=:1=W1>81>Y1?E1?_1@@1@a1AB1AC1AD1Aa1BF1Bk1Cg1D:1E61F21FH1G\1HT1Hg1JD1KM1LI1LJ1LK1LLFFS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P03IAL3PAL5LOIMG3SPL3SPA3DBL3SA23SA3S2SP3IDX4PACK2tf2bl2HBS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2tf5count2bl3TF03DBL3blkS2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2tf3blk1jS2ra2SP3IDX4PACK2tf2bl2I02HB5Ha_st5Hl_stS2s02SP3IDX4PACK2tf2bl2I02HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk4stw02I02P05LOIMG3SPL3DBL3BLK2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk2I02P05LOIMG3SPL4stw13DBL3BLK2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF02BL3blk2I02P03IAL3PAL5LOIMG3SPL3SPA3DBL3SA3S2SP3IDX4PACK2tf2lo2bl2I02P03SPL2HBS2SP3IDX4PACK2tf2lo2bl2I02P03SPL2HBS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P05LOIMG3SPL3DBL3BLK2HBS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P05LOIMG3SPL3DBL3BLK2HBS2SP2tf2lo2blS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF13blk2I02P05LOIMG3SPL3DBLS2SP3IDX4PACK2tf5count2bl3TF0S2SP3IDX4PACK2tf5count2bl3TF03DBLS2SP3IDX4PACK2tf5count2bl3TF0S2SP3IDX4PACK2tf5count2bl3TF03DBL3blkS2SP3IDX4PACK2tf2blS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf2lo2bl3TF02I02P03IAL3PAL5LOIMG3SPL3SPAS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P03IAL3PAL5LOIMG3SPL3SPA3DBLS2SP2tf2lo2blS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPL3DBLFS2AL2tf2bl3TF04IMG'S2AL2tf5count2bl3TF03blk4IMG'3DBLS2AL2tf5count2bl3TF03blk4IMG'3DBLS2AL2tf2bl4IMG'S2SP3IDX4PACK2tf5count2pk2bl3TF03blk4stw02P03DBL2HB5Ha_st5Hl_st4stw1S2SP3IDX4PACK2tf2blS2SP3IDX4PACK2tf5count2bl3TF0S2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HBS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HBS2SP3IDX4PACK2tf5count2bl3TF03DBLS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2SP2tf2lo2bl3SPLS2SP3IDX4PACK2tf5count2bl3TF0S2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf5count2lo2bl3TF02I02P05LOIMG3SPL3blk4stw03DBL3BLK2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk2I02P05LOIMG3SPL4stw13DBL3BLK2HB5Ha_st5Hl_stFFS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HBS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPLS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPLS2SP3IDX4PACK2tf5count2bl3TF03DBL3blkS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf5count2bl3TF03blk4stw03DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2bl3TF03blk4stw13DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2bl3TF03blk2P13DBL2HB5Ha_stS2SP2tf2lo2bl3SPLFFS2SP3IDX4PACK2tf5count2lo2bl3TF02BL2I02P03IAL3PAL5LOIMG3SPL3SPAS3hAR2SP3IDX4PACK2tf5count2pk2bl3TF03blk4stw02IP3DBL2HB5Ha_st5Hl_st4stw1S2tf2blS2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf2bl2HB5Ha_stS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HB5Ha_stFFS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL3BLKS2ra2SP3IDX4PACK2tf2bl2P02HB5Ha_st5Hl_stS2s02SP3IDX4PACK2tf2bl2P02HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF02I02P05LOIMG3SPL3blk4stw03DBL3BLK2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk2I02P05LOIMG3SPL4stw13DBL3BLK2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2pk2lo2bl3TF03blk4stw02I02P05LOIMG3SPL3DBL3BLK2HB5Ha_st5Hl_st4stw1S2SP3IDX4PACK2tf5count2lo2bl3CNT3TF02I02P03IAL3PAL5LOIMG3SPL3SPA3DBL3blkS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P03IAL3PAL5LOIMG3SPL3SPA3DBLS2SP3IDX4PACK2tf2lo2bl3SPLS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLFFS2SP3IDX4PACK2tf5count2bl3TF03DBL3blkFS2tf5count2bl3TF03DBL3blk3BLKS2tf5count2bl3TF03blk3DBL3BLKS2SP3IDX4PACK2tf5count2lo2bl3TF02I02P05LOIMG3SPL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk2I02P05LOIMG3SPL3DBL2HB5Ha_st5Hl_stS2tf5count2bl3TF03blk3DBLS2tf2blS2SP3IDX4PACK2tf5count2lo2bl3TF02I02P05LOIMG3SPL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk2I02P05LOIMG3SPL3DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF02I02P05LOIMG3SPL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3TF03blk2I02P05LOIMG3SPL3DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2bl3TF03DBL3blk3BLKS2SP3IDX4PACK2tf2blS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2AL2tf5count2bl3TF03blk4IMG'3DBL3BLKS2AL2tf5count2bl3TF04IMG'3DBL3blk3BLKS2ra2SP3IDX4PACK2tf2lo2bl3TF02I02P05LOIMG3SPL2HB5Ha_st5Hl_stS2s02SP3IDX4PACK2tf2lo2bl3TF02I02P05LOIMG3SPL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF02I02P05LOIMG3SPL3blk4stw03DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P05LOIMG3SPL4stw13DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf2bl3SPH2HB5Ha_stS2SP3IDX4PACK2tf2bl3SPH2HB5Ha_stS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HB5Ha_stS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HB5Ha_stS2SP3IDX4PACK2tf2lo2bl5LOIMGS2SP3IDX4PACK2tf5count2bl3TF03DBL3blk3BLKS2SP3IDX4PACK2tf2bl3TF0S2SP3IDX4PACK2tf5count2bl3TF0S2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPLS2SP4PACK2tf2lo3blk2P05LOIMG3SPL3BLK1j2Hj2NES2AL2tf2bl5ALWF'S2AL2tf5count2bl3TF05ALWF'3DBL3blkS2AL2tf5count2bl3TF03blk5ALWF'3DBLS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P05LOIMG3SPL3DBL2HB5Ha_st5Hl_stS2SP3IDX4PACK2tf5count2bl3TF03blk3DBLS2SP3IDX4PACK2tf5count2bl3TF03DBL3blkS2SP3IDX4PACK2tf5count2bl3TF03TF13DBLS2SP3IDX4PACK2tf5count2bl3TF03TF1S2SP3IDX4PACK2tf2bl3TF03TF1S2SP3IDX4PACK2tf2blS2SP3IDX4PACK2tf5count2bl3TF03DBL3blk3BLKS2SP3IDX4PACK2tf2bl2HBS2SP3IDX4PACK2tf5count2bl3TF03blk3DBL2HBS2SP3IDX4PACK2tf2lo2bl3SPL2HBS2SP3IDX4PACK2tf2lo2bl3SPL2HBS2AL2tf5count2bl3TF03blk4IMG'3DBLS2AL2tf5count2bl3TF04IMG'3DBL3blkS2SP3IDX4PACK2tf5count2bl3CNT3TF03DBL3blk2KcS2tf5count3blk3SA13SA33KeqS2SP3IDX4PACK2tf5count2bl3TF03DBLS2SP3IDX4PACK2tf5count2bl3TF03DBLS2SP3IDX4PACK2tf5count2bl3TF03DBLFFS2SP3IDX4PACK2tf5count2bl3CNTS2SP3IDX4PACK2tf5count2bl3CNT3TF03DBLS2SP3IDX4PACK2tf5count2bl3CNT3TF03DBLS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03blk2I02P05LOIMG3SPL3DBLS2SP3IDX4PACK2tf2blS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPL3DBLS2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPL3DBLS2SP3IDX4PACK2tf2bl2HBS2SP3IDX4PACK2tf5count2pk2lo2bl3TF03blk4stw02I02P05LOIMG3SPL3DBL2HB5Ha_st5Hl_st4stw1S2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPLS2SP3IDX4PACK2tf2blS2SP3IDX4PACK2tf5count2lo2bl3TF03blk4stw12I02P03IAL3PAL5LOIMG3SPL3SPA3DBL3SA13SA23SA33SA43SA5S2SP3IDX4PACK2tf5count2lo2bl3TF04stw02I02P03IAL3PAL5LOIMG3SPL3SPA3DBL3SA4S2SP3IDX4PACK2tf5count2lo2bl3CNT3TF03TF12I02P05LOIMG3SPL3DBLFFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ss_alloc_A : ltac2:(CDefT.buildp (gd_tbl_AW_DepotC ()) "Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Palloc,(1.&40.)Pidx0,(1.&40.)PSP,$=.PF,(2;.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(5.(1.&8.))PIDX,$=.PPACK,$=.Ptf,$=.Pcount,$=.Ppk,$=.Plo,$=.Pbl,(0.$=.)P,(<.(>.+2.R4.)(>.R4.+20.))P,(>.=R6.)P,(?.(13.R7.+40.)(1>.+2.+20.))P,(<.(>.=R6.)(?.R6.+10.))P,(3.$=.(2<.(9.$=.R5.))(29.(2:.(13.R9.(1>.+2.+14.))+1.)(1>.+2.+14.)))P,(11.$12.R=.$14.(16.$17.(18.(19.&40.R:.))(16.$17.(18.R12.)(1<.$17.))))P,(23.R>.R7.)P,(11.$12.R?.R>.(16.$17.(18.R13.)(1<.$17.)))P,(11.$12.R10.R>.(16.$17.(18.(19.&40.R;.))(1<.$17.)))P,(>.R14.R10.)P,(>.(13.R11.+8.)(1>.+2.+3?.))P,(>.R16.R11.)P,(>.(13.R12.+8.)(1>.+2.+3?.))P,(28.(>.(13.R14.+8.)R13.)(>.(13.R13.+8.)R14.))P,(3.$=.(20.R15.+8.)=)P,(3.$=.(20.R15.+8.)=)P,(30.VCS,R17.+8.)P,(30.VCS,R17.+8.)P,(3?.$12.R1:.R14.R1=.)P,(>.+65?000.R15.)P,(>.R16.(2:.R1?.+10.))P,(>.R20.(1>.+2.+3?.))P,(3.$=.(20.R21.+10.)=)P,(30.VCS,R19.(2:.R22.R19.))P,(33.$12.R20.)(34.$12.VAL,VCS,(41.R40.R24.R3?.R3>.R2=.R2<.R2;.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R3:.(19.&40.R1?.)R23.R22.R20.R1?.R1>.R1=.R1;.R1:.R26.R21.)(36.(37.R40.(19.&40.R24.)R3?.R3>.R3=.R3<.R3;.R3:.R39.(19.&40.$14.)(19.&40.R1=.)(19.&40.R20.)(19.&40.R1?.)R2:.R29.R28.R27.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.)R23.(19.&40.$42.)R22.(38.(1.&40.))R21.(39.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a4 a5 a6 a7 alloc idx0 SP F fc m IDX PACK tf count pk lo bl
      CNT TF0 TF1 PK BL SSX DB IX PX I0 I1 P0 P1 IP IAL PAL ICS PCS ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_SS_ALLOC, A_SS in *. change (1947848 + 16) with 1947864 in *.
    pose proof (munch_refl [(lo, SP); (1947848, 1947864 + 16 * 4096); (IDX, IDX + 8); (PACK, PACK + 8)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, SP); (1947848, 1947856)] m) as MU3. pose proof (wmono_refl asegs m) as WM3.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^20) with 1048576.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (DB0 : dblocks mc bl) by (eapply (dblocks_transport _ m mc bl DB MU3 WM3); unfold A_SS; cbn; lia) end.
    clear MU3 WM3 DB.
    zstep. if_cases Kne; zify_cond Kne.
    - (* [comment removed for export] *)
      replace (count + -1 + tf) with (tf + count - 1) in Kne by lia.
      ddestruct (straddle_arith tf count ltac:(lia) ltac:(lia) Kne) as (SA1 & SA2 & SA3 & SA4 & SA5).
      set (blk := tf / 1048576) in *.
      assert (BLK : 0 <= blk /\ blk + 1 < 4096).
      { subst blk. split; [apply Z.div_pos; lia|]. rewrite <- SA1. apply Z.div_lt_upper_bound; lia. }
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
      ddestruct DB0 as (DB1 & DBF & DBL).
      destruct (DB1 blk ltac:(lia)) as (stw0 & BC0). destruct (DB1 (blk + 1) ltac:(lia)) as (stw1 & BC1). unfold A_SS in BC0, BC1.
      replace (1947848 + 16 + 16 * blk) with (1947864 + blk * 16) in BC0 by lia.
      replace (1947848 + 16 + 16 * (blk + 1)) with (1947864 + (blk + 1) * 16) in BC1 by lia.
      assert (OTH : forall j', 0 <= j' < 4096 -> ~ (j' = blk \/ j' = blk + 1) ->
                exists st, rw_cells asegs mA (A_SS + 16 + 16 * j') [C8 (Z_to_bv 64 (sptr bl j')); C4 st; C4 (Z_to_bv 64 0)])
        by (intros j' H1 H2; apply DB1; exact H1).
      clear DB1.
      pose proof (munch_refl [(1947864 + blk * 16, 1947864 + blk * 16 + 32); (PACK, PACK + 8); (1947848, 1947864); (lo, SP)] mA) as MU2.
      pose proof (wmono_refl asegs mA) as WM2.
      zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. lia. }
      zstep. zstep. zstep. change 1048575 with (Z.ones 20). rewrite Z.land_ones by lia. change (2^20) with 1048576.
      zstep. rewrite (Z.shiftl_mul_pow2 blk 4) by lia. change (2^4) with 16.
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      replace (count + -1 + tf) with (tf + count - 1) by lia. rewrite SA2.
      zstep. rewrite (Z.shiftl_mul_pow2 (blk + 1) 4) by lia. change (2^4) with 16.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. rewrite !Z.shiftr_div_pow2 by lia. change (2^20) with 1048576.
      replace (count + -1 + (tf + count)) with (tf + count + count - 1) by lia.
      zstep. if_cases Keq; zify_cond Keq. 2:{ exfalso. clear -Keq SA1 SA3. lia. }
      eapply (ss_alloc_tail ra gp tp _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ t4 t5 t6 _ _ _ _ alloc _ _ SP F fc m _ IDX PACK tf (tf + count) count lo bl);
        try eassumption; try lia.
      (* [comment removed for export] *)
      eapply (dblocks_reest (fun j => j = blk \/ j = blk + 1) _ mA); [exact OTH| | intros j; clear; lia| exact DBF| exact DBL| exact MU2| exact WM2|].
      + intros j Hj [->| ->]; eexists; unfold A_SS.
        * replace (1947848 + 16 + 16 * blk) with (1947864 + blk * 16) by lia. eassumption.
        * replace (1947848 + 16 + 16 * (blk + 1)) with (1947864 + (blk + 1) * 16) by lia. eassumption.
      + intros j Hj NE. unfold A_SS. cbn. clear - Hj NE BLK P0 LOIMG SPL I0. lia.
    - (* [comment removed for export] *)
      replace (count + -1 + tf) with (tf + count - 1) in Kne by lia.
      eapply (ss_alloc_tail ra gp tp _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ _ _ alloc idx0 (Z_to_bv 64 pk) SP F fc m _ IDX PACK tf tf count lo bl);
        try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DepotC.

End ARUN_1.
