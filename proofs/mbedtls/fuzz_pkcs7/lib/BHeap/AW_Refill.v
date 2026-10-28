(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
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
Ltac2 gd_tbl_AW_Refill () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_divuw"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.min"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.ltb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_signed"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Refill.ic_post"; "Corelib.Init.Datatypes.app"; "ARUN_1.Refill.pc_new"; "ARUN_1.Refill.pc_old"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "ARUN_1.Refill.ic_inv"; "ARUN_1.Refill.ic_exit_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.A_GETFROM"; "ARUN_1.Refill.refill_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "ARUN_1.Refill.refillA_post"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Combined.A_REFILL"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Definition A_GETFROM : Z := 0x4c858.       (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L13313128812.5L15489369424.5L19201695968.5L26983617675.5L56765667180.5L58931716944.5L61883801886.5L67593114226.500000600<00B00H00N00T00Z00`S1a2HaS1b2HbS1b2HbS1a2HaS1a2HaS1b2HbS1b2HbS1a2Ha". (* [comment removed for export] *)
#[using="Type"] Lemma v_divuw_small : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pa,$0.Pb,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+1?.)))P,(1.(3.=R2.)(3.R2.(4.+2.+1?.)))(5.(6.&40.)(7.(8.&40.R4.)(8.&40.R3.))(8.&40.(9.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb. unfold v_divuw. rewrite !unsigned_lit by lia. rewrite !wrap32_small by lia.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  f_equal. apply swrap32_small. split. { apply Z.div_pos; lia. }
  apply Z.le_lt_trans with a; [| lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L45181140153.5L54961752591.300000900?S1c2E12E2S1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma class_size_range : forall c, 1 <= c <= 31 -> 32 <= class_size c <= 65536.
Proof.
  intros c Hc.
  pose proof (zall_spec (fun y => (32 <=? class_size y) && (class_size y <=? 65536))%bool (Z.to_nat 31) 1
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as E.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L18928485036.7L19327006175.7L33548903247.9L38848079051.8L45538332699.9L55942305227.8L6758013062.8 00000300900G00R00`00k00nS1cS1c2R1S1c1q2Hq2R12H0S1c1q2Hq2R1S1c1q2Hq2R12H0S1c1q2Hq2R1S1c". (* [comment removed for export] *)
#[using="Type"] Lemma max_count_code : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pc,$0.Pq,$0.P,(1.(2.+1.R2.)(2.R2.+1?.))P,(5.$0.R2.(:.+8.(9.+400.(;.R3.))))(5.$0.(<.(=.(>.R3.(?.(10.R3.+1.)))+10000000000000000.)+1.)(11.R4.))")
(* [comment removed for export] *).
Proof.
  intros c q Hc Hq. pose proof (class_size_range c Hc) as [R1 R2].
  assert (0 <= 1024 / class_size c) by (apply Z.div_pos; lia).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (destruct (q <? 1); cbn; lia).
  unfold max_count, max_cached. rewrite <- Hq.
  destruct (Z.ltb_spec q 1); cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L27270539305.3000006S1i2Hi". (* [comment removed for export] *)
#[using="Type"] Lemma ic_size_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pi,$0.P,(1.(2.+11.R1.)(2.R1.+1>.))(5.$0.(>.(12.(=.(13.(14.&40.(8.&40.(<.R2.+3?.)))+3?.)+10000000000000000.)(13.(=.(<.+200.(=.(13.(15.R2.+10.)+1.)+40.))+10000000000000000.)+1.))(<.+200.(=.(13.(15.R2.+10.)+1.)+40.)))(;.R2.))")
(* [comment removed for export] *).
Proof.
  intros i Hi. apply Z.eqb_eq.
  apply (zall_spec (fun y => Z.land ((bv_signed (Z_to_bv 64 (y ≪ 63)) ≫ 63) mod 18446744073709551616)
                                    (((512 ≪ (((y - 16) ≫ 1) mod 64)) mod 18446744073709551616) ≫ 1)
                             + 512 ≪ (((y - 16) ≫ 1) mod 64) =? class_size y) (Z.to_nat 14) 17); [| lia].
  vm_compute. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L11865735282.3L25678403258.3L41415983243.3L4499441315.4 L50925151380.4L65327017703.3L6755911291.3 00000600<00=00B00E00K00LS1s2HsS1s2HsSS1s1HS1sS1s2HsS". (* [comment removed for export] *)
#[using="Type"] Lemma srliw1 : forall s, 0 <= s < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 s) 1) = s / 2.
Proof.
  intros s Hs. unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
  rewrite (Z.mod_small s) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  change (4294967296 / 2) with 2147483648. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  assert (0 <= s / 2 < 2147483648) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L19146306265.5L54961752591.300000900?S1c2E12E2S1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma max_count_range : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16.
Proof.
  intros c Hc.
  pose proof (zall_spec (fun y => (2 <=? max_count y) && (max_count y <=? 16))%bool (Z.to_nat 31) 1
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as E.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Refill.
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
  Definition ic_post (T i : Z) (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Lms',$16.(17.(6.&40.)Lx28,(6.&40.)(17.(6.&40.)Lx29,(6.&40.)(17.(6.&40.)Lx30,(6.&40.)(17.P,(6.&40.)(18.(6.&8.))Lm',P,(6.&40.)(18.(6.&8.))(1.(5.$16.R5.(19.(1:.O17.O16.O15.O14.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)O13.O12.O11.(8.&40.(>.(>.O19.+=8.)(1;.+50.(>.O18.+1.))))O10.(8.&40.(1;.+20.(>.O18.+1.)))O?.(8.&40.(15.(>.O18.+1.)+10.))(8.&40.+?.)(8.&40.+400.)O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R4.R3.R2.O4.)O3.(8.&40.+4<7?8.)O2.(1<.(6.&40.))R1.(1=.$1>.)))(1.(1?.(20.(21.$0.$0.)(22.$0.$0.(>.(>.O19.+=4.)(1;.+50.O18.))(>.(>.O19.+>0.)(1;.+50.O18.)))(23.(21.$0.$0.)))O1.R1.)(1.(24.$1>.O1.R1.)(1.(25.$1>.R1.)(1.(26.$1>.R1.(>.(>.(>.O19.+=8.)(1;.+50.O18.))-4.)(20.$27.(28.(8.&40.(11.O18.)))(23.$27.)))(26.$1>.R1.(>.(>.O19.+=8.)(1;.+50.O18.))(20.$27.(29.(8.&40.(;.O18.)))(23.$27.))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L15793019834.54L23032525345.51L23039609428.53L2759962930.53 L30174057280.53L33684292138.53L39406493016.54L40607598005.52L4077821263.56 L44267228151.53L49698585326.54L49698585326.55L50212270043.51L51680957915.52L53759178673.53L5610153650.54 L56775626401.52L57264168315.55L60350570763.53L63039384267.52L63717619176.5300000800@00E00J00O00W00\00d01801B01P01^01f01n02602;02F02\02a02b02gS1T1i2HBS1T1i2HiS1T1iS1T1iS1T1iS1T1i2HBS1T1iS1T1i2HiS1T1i2HB5Ha_st5Hl_stS1T1i1q2HqS1T1i2HB5Ha_stS1T1i2HB5Ha_stS1T1i2HiS1T1i2HiS1T1i2HiS1T1iS1T1i1q3Hq0S1T1i1q2HB5Ha_st5Hl_stS1T1iFS1T1i". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ic_tail : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pra,(6.&40.)Psp,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa0,(6.&40.)Pa2,(6.&40.)Pa4,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt6,(6.&40.)Pmx,(6.&40.)Pcs,(6.&40.)PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Pi,$0.Pq,$0.P,(1.(2.+1.R2.)(2.R2.+1?.))P,(1.(2.+1000.R4.)(2;.(2.(>.R4.+1000.)+10000.)(2.+65?000.R4.)))P,(2.(>.R5.+1000.)(4.+2.+2?.))P,(5.$0.(=.R6.+1000.)=)P,(2<.VCS,R7.+1000.)P,(5.$0.R6.(:.+8.(9.+400.(;.R7.))))P,(1.(2.=R7.)(2.R7.+8.))P,(26.$1>.R;.(>.(>.(>.R:.+=8.)(1;.+50.R9.))-4.)(20.$27.(28.R?.)(23.$27.)))P,(26.$1>.R<.(>.(>.R;.+=8.)(1;.+50.R:.))(20.$27.(29.R?.)(23.$27.)))P,(25.$1>.R=.)(2=.$1>.VAL,VCS,(2>.R=.R<.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R10.R?.R>.)(19.(1:.R29.R28.R27.R26.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)R25.R24.R23.(8.&40.(>.(>.R=.+=8.)(1;.+50.R<.)))R22.(8.&40.(1;.+20.R<.))R21.(8.&40.(15.R<.+10.))(8.&40.+?.)(8.&40.+400.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.(8.&40.(;.R<.))(8.&40.R;.)R1>.R13.)R10.(8.&40.+4<7=8.)R?.(1<.(6.&40.))R>.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 mx cs F fc m T i q
      Hi T0 T1 TAL TCS Hq Hq0 PC1 PC2 MI.
    facts.
    pose proof (munch_refl [(T + 212 + 80 * i, T + 224 + 80 * i)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (max_count_code i q) in * by (first [lia | assumption]).
    replace (i - 16 + 1) with (i + 1 - 16) by lia. replace (32 * i + 32) with (32 * (i + 1)) by lia.
    replace (T + 216 + 80 * i + 80) with (T + 216 + 80 * (i + 1)) by lia.
    apply evtA_done. unfold ic_post. deexists 4.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L18926645932.49L20189873461.51L20550879402.52L21460829398.52L33739334207.50L33741198141.49L33745525890.52L36188450049.51L53755065230.52L53765583274.47L57605407753.52L59583278607.52L61066147266.50L874001887.52  00000300@00J00O00X00a00j00o01701?01J01O01X01cS1TS1T1i3CR13CR2S1T1i2Q01KS1T1iS1T1i3CR1S1T1i3CR1S1T1i3CR1S1T1iS1T1i2HiS1T1i2HiS1T1i3CR11KS1T1iS1T1i3CR1S1T1i3CR11K". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ic_mid : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pra,(6.&40.)Psp,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa0,(6.&40.)Pa2,(6.&40.)Pa4,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt6,(6.&40.)Pmx,(6.&40.)Pcs,(6.&40.)PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Pi,$0.P,(1.(2.+1.R1.)(2.R1.+1>.))P,(1.(2.+1000.R3.)(2;.(2.(>.R3.+1000.)+10000.)(2.+65?000.R3.)))P,(2.(>.R4.+1000.)(4.+2.+2?.))P,(5.$0.(=.R5.+1000.)=)P,(2<.VCS,R6.+1000.)P,(26.$1>.R8.(>.(>.(>.R7.+=8.)(1;.+50.R6.))-4.)(20.$27.(28.R<.)(23.$27.)))P,(26.$1>.R9.(>.(>.R8.+=8.)(1;.+50.R7.))(20.$27.(29.R<.)(23.$27.)))P,(25.$1>.R:.)(2=.$1>.VAL,VCS,(2>.R:.R9.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R=.R<.R;.)(19.(1:.R26.R25.R24.R23.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)R22.R21.R20.(8.&40.(>.(>.R:.+=8.)(1;.+50.R9.)))R1?.(8.&40.(1;.+20.R9.))R1>.(8.&40.(15.R9.+10.))(8.&40.+?.)(8.&40.+400.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.(8.&40.(;.R9.))R1<.R1;.R10.)R=.(8.&40.+4<828.)R<.(1<.(6.&40.))R;.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 mx cs F fc m T i
      Hi T0 T1 TAL TCS PC1 PC2 MI.
    facts. pose proof (class_size_range i ltac:(lia)) as [CR1 CR2].
    assert (Q0 : 0 <= 1024 / class_size i) by (apply Z.div_pos; lia).
    assert (Q1 : 1024 / class_size i <= 32) by (apply Z.div_le_upper_bound; lia).
    (* [comment removed for export] *)
    zstep. rewrite (v_divuw_small 1024 (class_size i)) by lia.
    zstep. zstep. if_cases K; zify_cond K.
    - eapply ic_tail; try eassumption; try lia.
    - (* [comment removed for export] *)
      zstep. zstep. eapply ic_tail; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L11095013413.48L14948324624.49L15960101798.3 L19644660117.49L21465069800.49L24447725369.49L33449444961.4 L36185959937.49L36917849601.49L42663229436.49L43854269281.49L59153908329.48L59153908456.49L59576979888.49L66253711036.49L6755968444.49 L878217697.49  00000500600?00G00L00T00`00e00j00k01<01=01H01K01S01V01WS1T1iFS1i2Hi2K1S1T1i2K2S1T1iS1T1i2K2S1i2Hi2K12K2S1T1iS1T1iFS1T1i2Hi2K22T02K1FS1T1i2Hi2K2S1TS1T1i2HiS1TF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ic_body : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pra,(6.&40.)Psp,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa0,(6.&40.)Pa2,(6.&40.)Pa4,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt6,(6.&40.)Pmx,(6.&40.)Pcs,(6.&40.)PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Pi,$0.P,(1.(2.+1.R1.)(2.R1.+1?.))P,(1.(2.+1000.R3.)(2;.(2.(>.R3.+1000.)+10000.)(2.+65?000.R3.)))P,(2.(>.R4.+1000.)(4.+2.+2?.))P,(5.$0.(=.R5.+1000.)=)P,(2<.VCS,R6.+1000.)P,(26.$1>.R8.(>.(>.(>.R7.+=8.)(1;.+50.R6.))-4.)(20.$27.(28.R<.)(23.$27.)))P,(26.$1>.R9.(>.(>.R8.+=8.)(1;.+50.R7.))(20.$27.(29.R<.)(23.$27.)))P,(25.$1>.R:.)(2=.$1>.VAL,VCS,(2>.R:.R9.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R=.R<.R;.)(19.(1:.R26.R25.R24.R23.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)R22.R21.R20.(8.&40.(>.(>.R:.+=8.)(1;.+50.R9.)))R1?.(8.&40.(1;.+20.R9.))R1>.(8.&40.(15.R9.+10.))(8.&40.+?.)(8.&40.+400.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R1=.R1<.R1;.R10.)R=.(8.&40.+4<7?<.)R<.(1<.(6.&40.))R;.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 mx cs F fc m T i
      Hi T0 T1 TAL TCS PC1 PC2 MI.
    facts.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (I31 : i = 31) by (clear - K1 Hi; lia).
      zstep. zstep. rewrite (v_divuw_small 1024 64) by lia. change (1024 / 64) with 16.
      zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 64) with (Z_to_bv 64 (class_size i)) by (rewrite I31; reflexivity).
      eapply ic_tail; try eassumption; try lia. rewrite I31. reflexivity.
    - (* [comment removed for export] *)
      zstep. zstep. replace (i - 16 + 16) with i by lia.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (32 * i)) with (Z_to_bv 64 (class_size i)) at 2.
        2:{ unfold class_size. replace (i =? 31) with false by (symmetry; apply Z.eqb_neq; lia).
            replace (i <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
        eapply ic_mid; try eassumption; try lia.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        rewrite (ic_size_ok i) by (clear - K1 K2 Hi; lia).
        eapply ic_mid; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pc_old (m : mem) (T : Z) (cnt mx cs : Z -> word) (rest : Z -> list cell) (j : Z) : Prop :=
    rw_cells asegs m (T + 208 + 80 * j) ([C4 (cnt j); C4 (mx j); C8 (cs j)] ++ rest j).
  Definition pc_new (m : mem) (T : Z) (cnt : Z -> word) (rest : Z -> list cell) (j : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "(26.$1>.O5.(>.(>.O4.+=0.)(1;.+50.O1.))(2?.$27.(20.$27.(28.A1.O3.O1.)(20.$27.(28.(8.&40.(11.O1.)))(20.$27.(29.(8.&40.(;.O1.)))(23.$27.))))A1.O2.O1.))")
(* [comment removed for export] *).
  Definition ic_inv (m : mem) (T : Z) (cnt mx cs : Z -> word) (rest : Z -> list cell) (i : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "(1.Pj,$0.P,(1.(2.+1.R1.)(3.R1.O1.))(30.O7.O6.O5.O2.R2.)Pj,$0.P,(1.(2.O1.R1.)(2.R1.+1?.))(31.O7.O6.O5.O4.O3.O2.R2.))")
(* [comment removed for export] *).

  Definition ic_exit_post (T : Z) (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (cnt : Z -> word) (rest : Z -> list cell) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Lms',$16.(17.(6.&40.)Lx28,(6.&40.)(17.(6.&40.)Lx29,(6.&40.)(17.(6.&40.)Lx30,(6.&40.)(17.P,(6.&40.)(18.(6.&8.))Lm',P,(6.&40.)(18.(6.&8.))(1.(5.$16.R5.(19.(1:.O19.O18.O17.O16.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)O15.O14.O13.(8.&40.(>.(>.O1:.+=8.)(1;.+50.+20.)))O12.(8.&40.(1;.+20.+20.))O11.(8.&40.+10.)(8.&40.+?.)(8.&40.+400.)O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R4.R3.R2.O6.)O5.(8.&40.+4<850.)O4.(1<.(6.&40.))R1.(1=.$1>.)))(1.(1?.(20.(21.$0.$0.)(22.$0.$0.(>.O1:.+120.)(>.O1:.+:=0.))(23.(21.$0.$0.)))O1.R1.)(1.(24.$1>.O1.R1.)(1.(25.$1>.R1.)Pj,$0.P,(1.(2.+1.R1.)(2.R1.+1?.))(30.R3.O1:.O3.O2.R2.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L11691082914.62L11805651963.70L11805778843.72L11805778843.73L15522594879.62L15958011032.3 L16514794758.60L16517026440.70L1919508631.56 L21271118116.62L22706556555.72L26925670320.71L29589254017.72L36751043144.70L36753538502.60L51928152809.51L56496414937.65L62501256542.60L62503217872.7000000B00L00[01001101901C01M01Z01d02902H02Z02d02n04Y04l05605@S1n1i1T2Hn2Hi2T01KS1n1i1T2HnS1n1i1T2Hn1j2HjS1n1i1T2Hn2T01j2Hj2NEFS1i2Hi1KS1n1i1T2HnS1n1i1T2HnS1n1i1T2Hn2HiS1n1i1T2HnS1n1i1T2Hn2Hi2T01z2HzS1n1i1T2Hn1j2HjS1n1i1T2Hn1j2Hj2NES1n1i1T2HnS1n1i1T2HnS2AL2CS1i2ra2sp2gp2tp2s02s12a02a22a42t32t42t52s22s32s42s52s62s72s82s93s103s112t61F2fc2m01m1T3cnt4rest2Hn2HiS1n1i1T2Hn3I311j2HjS1n1i1T2HnS1n1i1T2Hn". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ic_loop : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pn,$32.Pi,$0.Pra,(6.&40.)Psp,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa0,(6.&40.)Pa2,(6.&40.)Pa4,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt6,(6.&40.)PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(18.(6.&8.))Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Pcnt,P,$0.(6.&40.)Pmx,P,$0.(6.&40.)Pcs,P,$0.(6.&40.)Prest,P,$0.(33.$27.)P,(5.$0.(>.R21.(34.R22.))+20.)P,(1.(2.+1.R22.)(2.R22.+1?.))P,(1.(2.+1000.R7.)(2;.(2.(>.R7.+1000.)+10000.)(2.+65?000.R7.)))P,(2.(>.R8.+1000.)(4.+2.+2?.))P,(5.$0.(=.R9.+1000.)=)P,(2<.VCS,R:.+1000.)P,Pj,$0.(5.$32.(35.A1.R8.R1.)#40.)P,(36.R=.R<.R;.R:.R9.R8.R28.)P,(1?.(20.(21.$0.$0.)(22.$0.$0.(>.R=.+120.)(>.R=.+:=0.))(23.(21.$0.$0.)))R?.R>.)P,(24.$1>.R10.R?.)P,(25.$1>.R10.)(2=.$1>.VAL,VCS,(37.R10.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R?.R<.R12.)(19.(1:.R2;.R2:.R29.R28.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)R27.R26.R25.(8.&40.(>.(>.R10.+=8.)(1;.+50.R2<.)))R24.(8.&40.(1;.+20.R2<.))R23.(8.&40.(15.R2<.+10.))(8.&40.+?.)(8.&40.+400.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R22.R21.R20.R15.)R14.(8.&40.+4<7?<.)R13.(1<.(6.&40.))R11.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros i ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m0 m T cnt mx cs rest
      Hn Hi T0 T1 TAL TCS REST [INV1 INV2] MU WM MI; [lia|].
    facts.
    (* [comment removed for export] *)
    pose proof (INV2 i ltac:(lia)) as PCI. unfold pc_old in PCI.
    change ([C4 (cnt i); C4 (mx i); C8 (cs i)] ++ rest i) with ([C4 (cnt i)] ++ [C4 (mx i)] ++ ([C8 (cs i)] ++ rest i)) in PCI.
    apply rw_cells_split3 in PCI as (PCa & PCb & PCcd). cbn [cells_size csize Nat.add] in PCb, PCcd.
    apply rw_cells_app in PCcd as [PCc PCd]. cbn [cells_size csize Nat.add] in PCd.
    change (Z.of_nat 4) with 4 in *. change (Z.of_nat 8) with 8 in *.
    replace (T + 208 + 80 * i + 4) with (T + 216 + 80 * i + -4) in PCb by lia.
    replace (T + 208 + 80 * i + 4 + 4) with (T + 216 + 80 * i) in PCc by lia.
    replace (T + 208 + 80 * i + 4 + 4 + 8) with (T + 224 + 80 * i) in PCd by lia.
    eapply evtA_cut. { eapply ic_body; try eassumption; lia. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (x28 & x29 & x30 & m' & -> & MUc & WMc & MI' & PCb' & PCc')).
    (* [comment removed for export] *)
    assert (INV' : ic_inv m' T cnt mx cs rest (i + 1)).
    { split.
      - intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
        + unfold pc_new.
          change ([C4 (cnt i); C4 (Z_to_bv 64 (max_count i)); C8 (Z_to_bv 64 (class_size i))] ++ rest i)
            with ([C4 (cnt i)] ++ [C4 (Z_to_bv 64 (max_count i))] ++ ([C8 (Z_to_bv 64 (class_size i))] ++ rest i)).
          apply rw_cells_join3; cbn [cells_size csize Nat.add]; change (Z.of_nat 4) with 4; change (Z.of_nat 8) with 8.
          * eapply (rw_cells_transport asegs _ m m'); [exact PCa| exact MUc| exact WMc|]. cbn. lia.
          * replace (T + 208 + 80 * i + 4) with (T + 216 + 80 * i + -4) by lia. exact PCb'.
          * apply rw_cells_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4; change (Z.of_nat 8) with 8. split.
            { replace (T + 208 + 80 * i + 4 + 4) with (T + 216 + 80 * i) by lia. exact PCc'. }
            replace (T + 208 + 80 * i + 4 + 4 + 8) with (T + 224 + 80 * i) by lia.
            eapply (rw_cells_transport asegs _ m m'); [exact PCd| exact MUc| exact WMc|]. rewrite REST. cbn. lia.
        + pose proof (INV1 j ltac:(lia)) as PJ. unfold pc_new in PJ |- *.
          eapply (rw_cells_transport asegs _ m m'); [exact PJ| exact MUc| exact WMc|].
          rewrite cells_size_app, REST. cbn. lia.
      - intros j Hj. pose proof (INV2 j ltac:(lia)) as PJ. unfold pc_old in PJ |- *.
        eapply (rw_cells_transport asegs _ m m'); [exact PJ| exact MUc| exact WMc|].
        rewrite cells_size_app, REST. cbn. lia. }
    assert (MU' : munch [(T + 288, T + 2768)] m0 m').
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros z Hz. cbn in Hz |- *. lia. }
    assert (WM' : wmono asegs m0 m') by (eapply wmono_trans; [exact WM| exact WMc]).
    clear PCa PCd PCb' PCc' MUc WMc MU WM MI INV1 INV2.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (I31 : i = 31) by (clear - K Hi; lia).
      apply evtA_done. unfold ic_exit_post. deexists 4.
      split. { rewrite I31. reflexivity. }
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. apply (proj1 INV'). lia.
    - eapply (IH (i + 1)); try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition refill_frame (m : mem) (SP : Z) (j0 : list byte) (q1 q0 qra : word) : Prop :=
    rw_cells asegs m (SP + -32) [CB 8 j0; C8 q1; C8 q0; C8 qra].

  (* [comment removed for export] *)
  Definition refillA_post (SP : Z) (gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (T c mxc lo : Z) (W : list (Z * Z)) (X : mem -> Prop) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Lms',$16.(17.P,(6.&40.)(18.(6.&8.))Lm',P,(6.&40.)(18.(6.&8.))(17.(33.(6.&8.))Lj0,(33.(6.&8.))(1.(5.$16.R3.(19.(1:.(8.&40.+4<798.)(8.&40.(>.O23.-20.))O22.O21.O20.O1?.O1>.(8.&40.(>.(>.O7.+=0.)(1;.+50.O6.)))(8.&40.(9.O5.+2.))(8.&40.$38.)(8.&40.(>.O7.+:=0.))(8.&40.O6.)(8.&40.(>.(>.(>.O7.+=0.)(1;.+50.O6.))+10.))(8.&40.(9.O5.+2.))O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.)O9.(8.&40.$39.)O8.(1<.(6.&40.))R2.(1=.$1>.)))(1.(1?.(20.(21.$0.$0.)(22.$0.$0.O4.O23.)O3.)O1.R2.)(1.(24.$1>.O1.R2.)(1.(25.$1>.R2.)(1.(3:.R2.O23.R1.O1<.O1=.O:.)(1.(3;.$1>.R2.O4.(>.O23.-20.))A1.O2.R2.))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L16433630438.62L16901428961.62L19516900705.61L25936553270.61L31947592630.62L32926925355.66L32933301684.65L33022511713.62L36169848443.65L37062217443.65L37062217443.66L37481963854.65L37741107402.64L37975166518.62L39302203090.62L43770836298.65L44235777020.62L49484637902.65L49698585326.66L49698585326.67L49782145994.65L57264168315.67L57264168315.68L58506288006.64L59314923118.3 L60388966608.65L60388966608.66L61839275086.6400000<00G00R00a01001B01T01_02102>02K02U02_02n03?03I03U03_04604M04W05U06V06`06k07?07S07]S3hAR1T1c2HCS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP1T3mxc3HMXS3hAR2SP1T3mxc3HMXS3hAR2SP2loS3hAR2SP1T3mxc3HMXS3hAR2SP1T2HBS3hAR2SP1T2HBS3hAR2SP1TS3hAR2SP1TS3hAR2SP2lo3SPLS3hAR2SP1T2lo3SPLS3hAR2SP1TS3hAR1T1c2HCS3hAR2SP1TS3hAR2SP1T3SPH2HB5Ha_stS3hAR2SP1T3SPH2HB5Ha_stS3hAR2SP1TS3hAR2ra2SP1T2lo1c2T03TAL2HC5LOIMG3SPL3SPA4TSEP2HB5Ha_st5Hl_stS3hAR2s02SP1T2lo1c2T03TAL2HC5LOIMG3SPL3SPA4TSEP2HB5Ha_st5Hl_st2s1S3hAR2SP1TS3mxc3HMX1KS3hAR2SP1T2lo3SPL2HBS3hAR2SP1T2lo3SPL2HBS3hAR2SP1T". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma refill_A : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pra,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pcntw,(6.&40.)Pcsw,(6.&40.)PSP,$0.PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Plo,$0.Pc,$0.Pmxc,$0.P,(1.(2.+1000.R4.)(2;.(2.(>.R4.+1000.)+10000.)(2.+65?000.R4.)))P,(2.(>.R5.+1000.)(4.+2.+2?.))P,(5.$0.(=.R6.+1000.)=)P,(2<.VCS,R7.+1000.)P,(1.(2.+1.R6.)(2.R6.+1?.))P,(1.(2.+1.R6.)(3.R6.(4.+2.+1?.)))P,(26.$1>.R;.(>.(>.R:.+=0.)(1;.+50.R8.))(20.$27.(28.R10.)(20.$27.(28.(8.&40.R7.))(20.$27.(29.R?.)(23.$27.)))))P,(3;.$1>.R<.R:.R?.)P,(2.(3<.VhAR,)R;.)P,(2.R<.(15.R11.+20.))P,(2.R12.(4.+2.+3?.))P,(5.$0.(=.R13.+10.)=)P,(2;.(2.(>.R10.+1000.)R?.)(2.R14.R10.))P,(2<.VCS,R10.(15.R15.R10.))P,(25.$1>.R13.)(2=.$1>.VAL,VCS,(3=.R17.R32.R31.R30.R2?.R2>.R2=.R2<.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R33.R16.R15.R13.R11.R10.R12.(23.(21.$0.$0.))L,P,(6.&40.)(18.(6.&8.))$3>.R14.)(19.(1:.R33.(8.&40.R17.)R32.R31.R30.R2?.R2>.R2=.R2<.(8.&40.(>.R13.+=0.))(8.&40.(>.(>.R13.+=0.)(1;.+50.R11.)))(8.&40.$38.)(8.&40.R11.)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R16.(8.&40.$3?.)R15.(1<.(6.&40.))R14.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cntw csw SP F fc m T lo c mxc
      T0 T1 TAL TCS HC HMX PC ST LOIMG SPL SPH SPA TSEP SCS MI.
    facts. unfold A_REFILL, A_INSTANCE, A_GETFROM in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite (sx32_small mxc) by lia.
    zstep. if_cases K; zify_cond K. { exfalso. clear - K HMX. lia. }
    (* [comment removed for export] *)
    zstep. rewrite (srliw1 mxc) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. unfold refillA_post, refill_frame. deexists 2.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0?L11332664038.8 L11803681823.75L1190691636.75 L15469027684.74L16433630438.66L16435873638.72L16901428961.66L19516900705.65L22700267513.77L25807760386.69L25936553270.65L31947592630.66L33022511713.66L37062217443.69L37062217443.70L37481963854.69L37741107402.68L37975166518.66L39302317016.66L43770836298.69L44233828476.72L44235777020.66L44482824016.75L48096643925.73L48097116777.65L48098741086.74L49484637902.69L49698585326.70L49698585326.71L49782145994.69L52894412766.69L57264168315.71L57264168315.72L58459420406.69L58459420406.70L58506288006.68L60388966608.69L60388966608.70L6093371841.69 L61839275086.68L6636662144.69 L67170517533.7100000C00j01:01J01V01b01m02802I02S02b03103<03I03V03`03j04904J04T04`04l05>05M05\05k06506L06c06m07708509609J09^09h0:<0:P0:Z0:d0:n0;=S2SP1T2lo4TSEP1j2HjS3hAR2SP1T2lo2T03TAL5LOIMG3SPL3SPA4TSEPS3hAR2SP1T1c3MCRS3hAR2SP1T1c3MCRS3hAR1T1c2HCS3hAR1T1c2HCS3hAR2SP2loS3hAR2SP2loS3hAR2SP1T2lo1x1HS3hAR2SP1TS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP1T2HBS3hAR2SP1T2HBS3hAR2SP1TS3hAR2SP1TS3hAR2SP2lo3SPLS3hAR2SP1T2lo3SPLS3hAR2SP1TS3hAR1T1c2HCS3hAR1T1c2HCS3hAR2SP1T2lo4TSEPS3hAR2SP1T1c2HCS3hAR2SP1T1c2HCS3hAR2SP1T1c2HCS3hAR2SP1TS3hAR2SP1T3SPH2HB5Ha_stS3hAR2SP1T3SPH2HB5Ha_stS3hAR2SP1TS3hAR2SP1TS3hAR2ra2SP1T2lo1c2T03TAL2HC5LOIMG3SPL3SPA4TSEP2HB5Ha_st5Hl_stS3hAR2s02SP1T2lo1c2T03TAL2HC5LOIMG3SPL3SPA4TSEP2HB5Ha_st5Hl_st2s1S3hAR2SP1T2lo3SPL2HBS3hAR2SP1T2lo3SPL2HBS3hAR2SP1TS3hAR2SP1T2lo3SPL2HBS3hAR2SP1T2lo3SPL2HBS3hAR2SP1TS3hAR2SP1TS3hAR2SP1TS3hAR2SP1T1j2Hj". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma refill_A_init : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pra,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PSP,$0.PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Plo,$0.Pc,$0.Pcnt,P,$0.(6.&40.)Pmx,P,$0.(6.&40.)Pcs,P,$0.(6.&40.)Prest,P,$0.(33.$27.)P,(1.(2.+1000.R7.)(2;.(2.(>.R7.+1000.)+10000.)(2.+65?000.R7.)))P,(2.(>.R8.+1000.)(4.+2.+2?.))P,(5.$0.(=.R9.+1000.)=)P,(2<.VCS,R:.+1000.)P,(1.(2.+1.R9.)(2.R9.+1?.))P,Pj,$0.(5.$32.(35.A1.R7.R1.)#40.)P,Pj,$0.P,(1.(2.+1.R1.)(2.R1.+1?.))(31.R10.R?.R<.R;.R:.R9.R2.)P,(5.(6.&40.)A1.R:.R<.(8.&40.=))P,(3;.$1>.R10.R>.R13.)P,(2.(3<.VhAR,)R?.)P,(2.R10.(15.R15.+20.))P,(2.R16.(4.+2.+3?.))P,(5.$0.(=.R17.+10.)=)P,(2;.(2.(>.R14.+1000.)R13.)(2.R18.R14.))P,(2<.VCS,R14.(15.R19.R14.))P,(25.$1>.R17.)(2=.$1>.VAL,VCS,Lms',$16.(17.(6.&40.)Lx28,(6.&40.)(17.(6.&40.)Lx29,(6.&40.)(17.(6.&40.)Lx30,(6.&40.)(3=.R1?.R38.R37.(8.&40.+10.)(8.&40.+11.)(8.&40.+200.)R33.R32.(8.&40.+10.)(8.&40.+?.)(8.&40.+400.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R3.R2.R1.R20.R39.R1>.R1=.R1;.R19.(11.R19.)R1:.(20.(21.$0.$0.)(22.$0.$0.(>.R1;.+120.)(>.R1;.+:=0.))(23.(21.$0.$0.)))Lm',P,(6.&40.)(18.(6.&8.))Pj,$0.P,(1.(2.+1.R1.)(2.R1.+1?.))(30.R3.R1>.R1;.R18.R2.)R1<.R4.))))(19.(1:.R35.(8.&40.R1;.)R34.R33.R32.R31.R30.R2?.R2>.(8.&40.(>.R17.+=0.))(8.&40.(>.(>.R17.+=0.)(1;.+50.R15.)))(8.&40.$38.)(8.&40.R15.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1:.(8.&40.$3?.)R19.(1<.(6.&40.))R18.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m T lo c cnt mx cs rest
      T0 T1 TAL TCS HC REST PCS MX0 ST LOIMG SPL SPH SPA TSEP SCS MI.
    facts. unfold A_REFILL, A_INSTANCE, A_GETFROM in *.
    pose proof (munch_refl [(lo, SP); (T + 288, T + 2768)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, SP)] m) as MU2.
    pose proof (PCS c ltac:(lia)) as PC. unfold pc_old in PC. rewrite MX0 in PC.
    apply rw_cells_app in PC as [PC _].
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite (sx32_small 0) by lia.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (T + 296) with (T + 216 + 80 * 1) by lia. change (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1)). change (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16)).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (PCS' : forall j, 1 <= j <= 31 -> pc_old mc T cnt mx cs rest j) end.
    { intros j Hj. unfold pc_old. eapply rw_cells_transport; [apply PCS; lia| exact MU2| exact WM|].
      rewrite cells_size_app, REST. cbn [cells_size csize Nat.add]. cbn. clear - Hj TSEP SPL T0; lia. }
    clear MU2.
    eapply evtA_cut.
    { eapply (ic_loop 31%nat 1). all: try apply munch_refl. all: try apply wmono_refl. all: try eassumption. all: try lia.
      split; [intros; lia|]. exact PCS'. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (x28 & x29 & x30 & m' & -> & MUc & WMc & MI' & PCN)).
    clear PC MI. lazymatch type of MUc with munch _ ?mp _ => transport_after_call asegs mp m' MUc WMc end. clear MUc WMc.
    pose proof (PCN c ltac:(lia)) as PC. unfold pc_new in PC. apply rw_cells_app in PC as [PC _].
    pose proof (max_count_range c ltac:(lia)) as MCR.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small (max_count c)) by lia. zstep.
    (* [comment removed for export] *)
    zstep. rewrite (srliw1 (max_count c)) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. deexists 3. unfold refillA_post, refill_frame. deexists 2.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|exact PCN].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L15793019834.71L16901135734.68L19516739318.68L25936916129.68L29012665503.69L31947757601.68L32140421705.69L33022673398.68L37481963854.70L37974869409.68L40602960267.68L44888221083.70L49484637902.70L49698585326.72L49765034975.73L57325747188.70L59314923118.3 L61839275086.70L64551750433.70L6508853087.68 L68095256546.7000000?00J00U00d01101@01H01S01[01j02602>02F02[03X03d03l04404C04O04[S3hAR2SP1T1c2HBS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP1r2HRS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR1T1c2HCS3hAR2SPS3hAR2SPS3hAR2SP1T1c2HB5Ha_stS3hAR2SP1T2lo1c1n1r2HC2HR5LOIMG3SPL3SPA4TSEP1K2HB5Ha_st5Hl_stS3hAR2SP1T1cS1r2HR1KS3hAR2SPS3hAR2SP2lo3SPLS3hAR1T1c2HCS3hAR2SP1T1c". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma refill_B_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq0,(6.&40.)Pq1,(6.&40.)Pqra,(6.&40.)Pcntw,(6.&40.)Pj0,(33.(6.&8.))PSP,$0.PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(18.(6.&8.))Pm,P,(6.&40.)(18.(6.&8.))PT,$0.Plo,$0.Pc,$0.Pn,$0.Pr,$0.PW,(33.(21.$0.$0.))P,(1.(2.+1000.R6.)(2;.(2.(>.R6.+1000.)+10000.)(2.+65?000.R6.)))P,(2.(>.R7.+1000.)(4.+2.+2?.))P,(2<.VCS,R8.+1000.)P,(1.(2.+1.R7.)(2.R7.+1?.))P,(1.(2.=R7.)(3.R7.(4.+2.+1?.)))P,(1.(3.=R7.)(3.R7.(4.+2.+40.)))P,(26.$1>.R=.(>.(>.R<.+=0.)(1;.+50.R:.))(20.$27.(28.R13.)(23.$27.)))P,(3:.R>.R12.R13.R16.R17.R15.)P,(3;.$1>.R?.R=.(>.R13.-20.))P,(2.(3<.VhAR,)R>.)P,(2.R?.(15.R15.+20.))P,(2.R16.(4.+2.+3?.))P,(5.$0.(=.R17.+10.)=)P,(2;.(2.(>.R13.+1000.)R12.)(2.R18.R13.))P,(2<.VCS,R13.(15.R19.R13.))P,(1?.(20.(21.$0.$0.)(22.$0.$0.R14.R1:.)(20.(21.$0.$0.)(22.$0.$0.(>.(>.R15.+=0.)(1;.+50.R13.))(>.(>.(>.R15.+=0.)(1;.+50.R13.))+4.))R10.))R17.R16.)P,(24.$1>.R18.R17.)P,(25.$1>.R18.)(2=.$1>.VAL,VCS,Lms',$16.(17.P,(6.&40.)(18.(6.&8.))Lm',P,(6.&40.)(18.(6.&8.))(1.(5.$16.R2.(19.(1:.R22.(8.&40.R1?.)R3>.R3=.R3<.R3;.R3:.R24.R23.(8.&40.R16.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R1>.(40.R22.)R1=.(1<.(6.&40.))R1.(1=.$1>.)))(1.(1?.(20.(21.$0.$0.)(22.$0.$0.R19.R1?.)(20.(21.$0.$0.)(22.$0.$0.(>.(>.R1:.+=0.)(1;.+50.R18.))(>.(>.(>.R1:.+=0.)(1;.+50.R18.))+4.))R15.))R1<.R1.)(1.(24.$1>.R1<.R1.)(1.(25.$1>.R1.)(1.(26.$1>.R1.(>.(>.R1:.+=0.)(1;.+50.R18.))(20.$27.(28.(8.&40.R17.))(23.$27.)))(3;.$1>.R1.R19.R1?.)))))))(19.(1:.(8.&40.+4<798.)(8.&40.(>.R1=.-20.))R3<.R3;.R3:.R39.R38.(8.&40.(>.(>.R18.+=0.)(1;.+50.R16.)))(8.&40.R15.)(8.&40.R14.)R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R1<.(8.&40.+4<798.)R1;.(1<.(6.&40.))R19.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 qra cntw j0 SP F fc m0 m T lo c n r W
      T0 T1 TCS HC HN HR PC FR ST LOIMG SPL SPH SPA TSEP SCS MU WM MI.
    facts. unfold refill_frame in FR.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { exfalso. clear - K HR. lia. }
    zstep. zstep. zstep. zstep. zstep.
    replace (SP + -32 + 32) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|eassumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L16905444186.57L19521308890.57L25924184205.57L31960227341.57L32140421705.57L33026492378.57L37481963854.59L37979210637.57L44884140983.58L49484637902.59L61839275086.59L64547441933.5800000;00F00U00d00l01701?01N01V01^01f025S3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma refill_B_no : ltac2:(CDefT.buildp (gd_tbl_AW_Refill ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq0,(6.&40.)Pq1,(6.&40.)Pqra,(6.&40.)Pj0,(33.(6.&8.))PSP,$0.PF,(2:.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(18.(6.&8.))Pm,P,(6.&40.)(18.(6.&8.))Plo,$0.PW,(33.(21.$0.$0.))P,(3:.R3.R7.R8.R:.R;.R9.)P,(3;.$1>.R4.R3.(>.R8.-20.))P,(2.(3<.VhAR,)R4.)P,(2.R5.(15.R:.+20.))P,(2.R;.(4.+2.+3?.))P,(5.$0.(=.R<.+10.)=)P,(2<.VCS,R8.(15.R=.R8.))P,(1?.(20.(21.$0.$0.)(22.$0.$0.R9.R>.)R8.)R;.R:.)P,(24.$1>.R<.R;.)P,(25.$1>.R<.)(2=.$1>.VAL,VCS,Lms',$16.(17.P,(6.&40.)(18.(6.&8.))Lm',P,(6.&40.)(18.(6.&8.))(1.(5.$16.R2.(19.(1:.R15.(8.&40.R13.)R33.R32.R31.R30.R2?.R17.R16.(8.&40.=)R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R12.(40.R15.)R11.(1<.(6.&40.))R1.(1=.$1>.)))(1.(1?.(20.(21.$0.$0.)(22.$0.$0.R>.R13.)R=.)R10.R1.)(1.(24.$1>.R10.R1.)(1.(25.$1>.R1.)(3;.$1>.R1.R>.R13.))))))(19.(1:.(8.&40.+4<798.)(8.&40.(>.R11.-20.))R31.R30.R2?.R2>.R2=.R2<.R2;.(8.&40.=)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R10.(8.&40.+4<798.)R?.(1<.(6.&40.))R=.(1=.$1>.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 qra j0 SP F fc m0 m lo W
      FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold refill_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    replace (SP + -32 + 32) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|eassumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Refill.

End ARUN_1.
