(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison AW_DepotB AW_MallocA AW_AllocA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AW_HdrBits.
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
Ltac2 gd_tbl_AW_CbRecycle () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_divuw"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_signed"; "Stdlib.ZArith.BinInt.Z.shiftl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SPACEBEG_CELL"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.CbRecycle.cbr_at_div"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "ARUN_1.CbRecycle.cbr_frame"; "ARUN_1.A_CB_RECYCLE"; "ARUN_1.A_CBR_MID"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_RI_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "ARUN_1.CbRecycle.cbrA2_post"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "ARUN_1.A_LC_DEALLOC"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.dealloc_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.CbRecycle.cbrB_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_CB_RECYCLE : Z := 0x49bc0.      (* [comment removed for export] *)
Definition A_CBR_MID : Z := 0x49d2c.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_LC_DEALLOC : Z := 0x49fc4.      (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_MAGIC_CELL : Z := 0x10340.      (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint zall (P : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S k => P lo && zall P (lo + 1) k end.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18874438963.6 L65848082566.1000000;00IS1P2lo1x2HxS1n2lo1x2Hx2n0". (* [comment removed for export] *)
#[using="Type"] Lemma zall_spec : forall P n lo, zall P lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> P x = true.
Proof.
  induction n as [|n IH]; intros lo H x Hx; [lia|].
  cbn [zall] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|]; [exact H1|].
  apply (IH (lo + 1) H2). lia.
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

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L16680827188.6L22555297538.6L31332195357.6L38447051293.6L42470665770.6L5744834161.6 00000800@00H00P00U00]S1x1y2HyS1x1y2HyS1x1y2HyS1x1y2HyS1x1yS1x1y2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma v_divuw_gen : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Px,$0.Py,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(1.(3.=R2.)(3.R2.(4.+2.+1?.)))P,(3.(5.(6.R4.(4.+2.+20.))R3.)(4.+2.+1?.))(7.(8.&40.)(9.(:.&40.R5.)(:.&40.R4.))(:.&40.(5.(6.R5.(4.+2.+20.))R4.)))")
(* [comment removed for export] *).
Proof.
  intros x y Hx Hy Hq. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  f_equal. apply swrap32_small. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia| exact Hq].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L18926751670.5L39240146823.5L44015169772.5L67182100153.500000100400500;SS1cSS1r2Hr". (* [comment removed for export] *)
#[using="Type"] Lemma off_hi32 : forall c r, 0 <= c -> 0 <= r < 2^32 -> Z.shiftr (c * 4294967296 + r) 32 = c.
Proof.
  intros c r Hc Hr. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. rewrite Z.add_comm, Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L29317573675.3L56918006115.3000001007SS1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma land31_small : forall c, 0 <= c < 32 -> Z.land c 31 = c.
Proof. intros c Hc. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34081429519.3000006S1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma csz_code_hi : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Pc,$0.P,(1.(2.+11.R1.)(2.R1.+1>.))(7.$0.(;.(<.(6.(=.(>.&40.(:.&40.(?.R2.+3?.)))+3?.)+10000000000000000.)(=.(6.(?.+200.(6.(=.(;.R2.-10.)+1.)+40.))+10000000000000000.)+1.))(?.+200.(6.(=.(;.R2.-10.)+1.)+40.)))(10.R2.))")
(* [comment removed for export] *).
Proof.
  intros c Hc. apply Z.eqb_eq.
  apply (zall_spec (fun y => Z.land ((bv_signed (Z_to_bv 64 (y ≪ 63)) ≫ 63) mod 18446744073709551616)
                                    (((512 ≪ (((y + -16) ≫ 1) mod 64)) mod 18446744073709551616) ≫ 1)
                             + 512 ≪ (((y + -16) ≫ 1) mod 64) =? class_size y) (Z.to_nat 14) 17); [| lia].
  vm_compute. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L1952414836.3 L29317573675.3L33305886548.3L56480171184.300000600700:00@S1c2HcSS1cS1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma csz_code_lo : forall c, 1 <= c <= 16 -> Z.shiftl c 5 = class_size c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2 by lia. unfold class_size.
  replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L29784460545.4L31548574444.4L36948952043.4L5773882842.5 00000300900<00DS1qS1q2HqS1qS1q2Hq1E". (* [comment removed for export] *)
#[using="Type"] Lemma shl3_mod32' : forall q, 0 <= q < 2^60 -> q mod 4 = 0 -> (Z.shiftl q 3 mod 18446744073709551616) mod 32 = 0.
Proof.
  intros q Hq Hm. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  rewrite (Z.mod_small (q * 8) 18446744073709551616) by lia.
  pose proof (Z.div_mod q 4 ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E.
  replace (q * 8) with ((q / 4) * 32) by lia. apply Z_mod_mult.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L10433141276.5L18217878030.5L18926751670.5L41491210997.5L4501543897.5 L53395065884.5L8076082093.5 00000100600700:00E00F00LSS1c1rSS1cS1c1r2Hc2HrSS1r2Hr". (* [comment removed for export] *)
#[using="Type"] Lemma shl27_shr59 : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Pc,$0.Pr,$0.P,(1.(2.=R2.)(3.R2.+20.))P,(1.(2.=R2.)(3.R2.+100000000.))(7.$0.(=.(6.(?.(;.(11.R4.+100000000.)R3.)+1;.)+10000000000000000.)+3;.)R4.)")
(* [comment removed for export] *).
Proof.
  intros c r Hc Hr. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^27) with 134217728. change (2^59) with 576460752303423488.
  rewrite Z.mod_small by lia.
  replace ((c * 4294967296 + r) * 134217728) with (c * 576460752303423488 + r * 134217728) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section CbRecycle.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Ltac bytes_eq := vm_compute; repeat (first [reflexivity | apply f_equal2; [apply bv_eq; vm_compute; reflexivity|] ]).

  Definition cbr_frame (m : mem) (SP : Z) (s4 s3 s2 s1 s0 ra : word) : Prop :=
    rw_cells asegs m (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition cbr_at_div (SP : Z) (ra gp tp t0 t1 t2 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (CBP SB c sz off : Z) (F : bvmap 5 word) (fc : bv 32) (m' : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Lms',$12.(13.(8.&40.)La6,(8.&40.)(13.(8.&40.)La7,(8.&40.)(7.$12.R3.(14.(15.O1:.(:.&40.(;.O1;.-30.))O19.O18.O17.O16.O15.(:.&40.O8.)(:.&40.(;.O7.O4.))(:.&40.O7.)(:.&40.(;.O7.+2000000000.))(:.&40.O6.)(:.&40.O6.)(:.&40.O4.)(:.&40.O5.)R2.R1.O14.(:.&40.$16.)(:.&40.+2000000000.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.)O3.(:.&40.+49<70.)O2.(17.(8.&40.))O1.(18.$19.)))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0?L10125035199.3 L12970285762.69L14948324886.69L15129414474.66L15615277569.66L15615277696.67L16591383828.67L16591383828.68L16901428961.65L1859764022.65 L19516900705.64L19824808731.65L21142837706.66L21907930384.2 L24441680159.3 L25233164513.65L25936553270.64L26905125859.65L26905125859.66L27170469450.66L27335347790.66L28774353236.67L29149214414.66L31947592630.65L32664343351.3 L3276969806.65 L33022511713.65L33180861642.66L33693828364.65L35138021157.66L35138021284.67L37975166518.65L38793549580.65L39302203090.62L39340114894.66L40202209158.64L41370106893.2 L42663228666.69L44015210668.67L45217263562.65L48193359348.67L49698585326.66L49698585326.67L53522065825.65L55345847873.70L55345848131.68L55345848258.69L58142605646.66L59308628566.3 L59308628820.3 L59576980150.69L60388966608.65L60388966608.66L6040143663.66 L60735508806.65L61013493601.65L61346586394.66L64551387318.65L65144493349.66L67176444897.65L6755968698.69 L68390338709.2 L7870557622.65 00000900F00G00O00_00o01V02I02T02c02n02o03703=03F03Q03`03k04604>04F04X04`04o05705?05J05R05W06106Q06`06m07<07D07L07R07S07X07`08008E08Z08h09209<09F09N09W09`09e0:70:I0:Q0:^0:i0;40;C0;K0;V0;[0;a0<0S1c2CB2K4S3hAR1c2CB2K4FS3hAR2SPS3hAR2SB3SB03SB1S3hAR2SB3SB03SB1S3hAR2ra2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2s02SP2lo5LOIMG3SPL2HB5Ha_st5Hl_st2s12s22s32s4S3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loFS3hAR2SPS1r2RBS1c2CB2K4S3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2HBS3hAR2SP2HBS3hAR2SPS3hAR2SPS3hAR2SB1c1r2K12K2S3hAR2SPS3hAR2SP2lo3SPLS2SB1c1rS3hAR2SPS3hAR2SP2loS3hAR2SPS3hARS3hAR2SB1c1r3SB03SB12CB2RBS3hAR2SB1c1r3SB03SB12CB2RB2K12K2S3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS1c2CBFS3hARS3hAR2SPS3hAR2SB3SB03SB1S3hAR2SP3SPH2HB5Ha_stS3hAR2SP3SPH2HB5Ha_stS3hAR2AL5ALWF'S3hAR1c2CBS3hAR1c2CBS3hAR1c2CBS3hAR2SPS1c2CB2K3S1c2CB2K5S3hARS3hAR2SP2lo3SPL2HBS3hAR2SP2lo3SPL2HBS3hAR2SPS3hAR2AL4IMG'S3hAR2SP2loS3hAR2SP2HBS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hARS1c2CBS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma cbr_A1 : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Pra,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps0,(8.&40.)Ps1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)PSP,$0.PCBP,$0.PSB,$0.Pc,$0.Psz,$0.Pr,$0.Plo,$0.PF,(1:.&5.(8.&40.))Pfc,(8.&20.)Pmm,P,(8.&40.)(1;.(8.&8.))P,(2.+10007???9000.R8.)P,(2.(;.R9.(4.+2.+25.))(4.+2.+2?.))P,(1.(2.+1.R9.)(2.R9.+1>.))P,(7.$0.R9.(10.R:.))P,(1.(2.=R9.)(3.R9.(4.+2.+20.)))P,(1<.$19.R6.$1=.(1>.$1?.(20.(:.&40.R=.))(21.$1?.)))P,(22.$19.R7.R:.R10.)P,(2.(23.VhAR,)R;.)P,(2.R<.(24.R12.+30.))P,(2.R13.(4.+2.+3>.))P,(25.VCS,R>.(24.R14.R>.))P,(26.$19.R<.)(27.$19.VAL,VCS,Lms',$12.(13.P,(8.&40.)(1;.(8.&8.))Lm',P,(8.&40.)(1;.(8.&8.))(1.(28.R18.R34.R33.R32.R31.R30.R2?.R26.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R17.R16.R15.R14.(;.(11.R15.(4.+2.+20.))R13.)R11.R10.R1.R2.)(1.(29.(1>.(2:.$0.$0.)(2;.$0.$0.R12.R18.)(21.(2:.$0.$0.)))R?.R1.)(1.(2<.$19.R?.R1.)(1.(26.$19.R1.)(1.(2=.R1.R18.R24.R25.R26.R2=.R2>.R34.)(22.$19.R1.R12.(;.R18.-30.))))))))(14.(15.R32.(:.&40.R16.)R31.R30.R2?.R2>.R2=.R2<.R2;.(:.&40.R15.)(:.&40.(;.R14.(;.(11.R13.(4.+2.+20.))R11.)))R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R?.(:.&40.$2>.)R>.(17.(8.&40.))R=.(18.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP CBP SB c sz r lo F fc mm
      SB0 SB1 CB HSZ RB SBC ST LOIMG SPL SPH SCS MI.
    facts. unfold A_CB_RECYCLE, A_SPACEBEG_CELL, A_INSTANCE in *.
    change (1074072 + 32) with 1074104 in SBC. change (2^32) with 4294967296 in *.
    pose proof (munch_refl [(lo, SP)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 SB0 CB RB. nia. }
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 SB0 SB1 CB RB. nia. }
    zstep. zstep. zstep. zstep.
    replace (SB + (c * 4294967296 + r) - SB) with (c * 4294967296 + r) by (clear; lia).
    rewrite (off_hi32 c r ltac:(clear -CB; lia) ltac:(clear -RB; lia)). rewrite (land31_small c) by (clear -CB; lia).
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 CB. lia. }
    zstep. zstep. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite (csz_code_hi c) by (clear -K4 CB; lia). rewrite <- HSZ.
      apply evtA_done. eexists. split. { unfold cbr_at_div, A_INSTANCE. deexists 2. reflexivity. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR| exact ST].
    - (* [comment removed for export] *)
      zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5 CB. lia. }
      zstep. zstep. rewrite (csz_code_lo c) by (clear -K4 CB; lia). rewrite <- HSZ.
      apply evtA_done. eexists. split. { unfold cbr_at_div, A_INSTANCE. deexists 2. reflexivity. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cbrA2_post (SP : Z) (gp tp s2 s5 s6 s7 s8 s9 s10 s11 : word)
      (CBP SB c k sz n ctx b1 AB m lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Lms',$12.(13.(8.&40.)Lt0,(8.&40.)(13.(8.&40.)Lt1,(8.&40.)(13.(8.&40.)Lt2,(8.&40.)(13.(8.&40.)La0,(8.&40.)(13.(8.&40.)La1,(8.&40.)(13.(8.&40.)La2,(8.&40.)(13.(8.&40.)La3,(8.&40.)(13.(8.&40.)La4,(8.&40.)(13.(8.&40.)La5,(8.&40.)(13.(8.&40.)La6,(8.&40.)(13.(8.&40.)La7,(8.&40.)(13.(8.&40.)Lt3,(8.&40.)(13.(8.&40.)Lt4,(8.&40.)(13.(8.&40.)Lt5,(8.&40.)(13.(8.&40.)Lt6,(8.&40.)(13.P,(8.&40.)(1;.(8.&8.))Lm',P,(8.&40.)(1;.(8.&8.))ZS,$0.(;.+7???8000.(5.(;.O5.+10.)+8.))Zkk,$0.(5.(;.O9.+7.)+8.)(1.(7.$12.R13.(14.(15.(:.&40.$2?.)(:.&40.(;.O19.-30.))O18.O17.R12.R11.R10.(:.&40.O>.)(:.&40.O5.)R?.R>.R=.R<.R;.R:.R9.R8.(:.&40.O6.)(:.&40.$16.)(:.&40.+2000000000.)O15.O14.O13.O12.O11.O10.O?.R7.R6.R5.R4.)O3.(:.&40.$2?.)O2.(17.(8.&40.))R3.(18.$19.)))(1.(29.(1>.(2:.$0.$0.)(2;.$0.$0.O4.O19.)(1>.(2:.$0.$0.)(2;.$0.$0.O6.(;.O6.+8.))(1>.(2:.$0.$0.)(2;.$0.$0.O5.(;.O5.+4.))(1>.(2:.$0.$0.)(2;.$0.$0.R2.(;.R2.R1.))(21.(2:.$0.$0.))))))O1.R3.)(1.(2<.$19.O1.R3.)(1.(26.$19.R3.)(1.P,(3.+10.(30.O9.))(31.$19.R4.O6.(1>.$1?.(20.(:.&40.=))(1>.$1?.(20.(:.&40.O5.))(21.$1?.))))(1.(31.$19.R3.O5.(32.O7.=))(1.(31.$19.R3.(;.O5.+4.)(33.O9.O8.))(1.(31.$19.R3.R2.(1>.$1?.(34.(35.R1.)(36.(8.&8.)(:.&8.+?:.)(35.R1.)))(21.$1?.)))(1.(37.R3.)(22.$19.R3.O4.(;.O19.-30.)))))))))))))))))))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "02d0@L10186871394.105L10255983865.108L10255983865.110L10726731663.13 L10733889501.7  L10840142427.107L10842197994.106L11818158146.96 L1203973476.8   L14209604789.116L1425785106.112 L14394589950.0  L15488928053.2  L15615277188.105L15636836527.107L15638064059.104L15640057354.105L1583001300.12  L1583027182.104 L1583027182.106 L1583027182.107 L1585098335.105 L1585098335.107 L16983613614.109L17120848823.0  L17156522240.6  L17463680011.126L17463680011.127L18470463381.116L18745342350.109L1901125876.6   L19160092211.108L19603220401.109L19603220401.110L2025117102.1   L20586251106.109L20586251106.110L20746232333.112L20818189959.6  L21061785939.3  L21708252405.104L21708252405.105L22033476167.112L22976972249.2  L25055546191.108L25055546191.109L2591776968.116 L26048465753.4  L26445675160.106L26447791913.107L276702331.6    L27846297964.3  L282996335.7    L2868327334.105 L29160255805.3  L30507153540.105L30507155211.106L30507155338.105L30507155338.107L31336323787.12 L32298664356.1  L32307333196.1  L32852247788.105L3331016729.104 L3331016729.105 L33713698779.107L34251895956.12 L34260051768.107L34262178441.106L3435562517.116 L34928778699.3  L35450344195.4  L35992908710.105L35993319342.108L3604087996.125 L3604087996.126 L36644267936.2  L36949528055.1  L37256312405.104L37256312405.105L38235734261.1  L38692635477.0  L39252637125.0  L40870879649.0  L41320489498.112L41422282358.96 L41758888586.3  L42473292482.126L42473292482.127L42965677224.104L42965677224.105L43511605754.3  L43882591751.107L43884645302.106L4420569916.2   L44314800993.116L44641083001.104L44641083001.105L44900578356.4  L45411141685.108L46444081826.109L46595273239.125L46595273239.126L46642563597.112L47895214433.1  L48098986201.2  L48193357951.106L48289182042.110L50198383746.125L50198383746.126L50483062200.107L50483062200.108L50651538139.2  L51188928554.5  L51792349212.116L51980271812.2  L51982470518.106L51982470518.107L52137102513.105L52231392292.7  L52241859120.2  L53519851936.112L53522111627.105L53775120562.110L54244139616.9  L54961838568.2  L55347782885.116L55606901317.2  L55936551073.117L55993556759.20 L56070161827.112L57018066361.2  L57539235556.104L57541309269.105L57622410744.126L57622410744.127L58550304769.110L58817773446.125L58817773446.126L58817773446.127L58943329556.112L59308628949.5  L59308629082.6  L59315137787.6  L60389186623.110L61025011698.95 L61712537026.104L61714671731.105L61744303959.0  L61931848722.106L61931848722.107L63374621462.96 L63411899393.116L64987951381.109L64987951381.110L6517142237.20  L65271643703.0  L65504523926.96 L6648657248.96  L66671450973.112L66732424200.105L67277887433.110L67782583095.0  L67782919415.107L67782919415.108L67827351854.107L67829431455.106L68252048817.5  L68467538222.110L7187989757.126 L7187989757.127 L7501968815.105 L759894238.127  L7804958024.104 L7804958024.105 L8848044271.4   L885845439.105  L8927229185.116 L9289892310.2   L959819899.107  00000<01F02Q02a03503603703H03]05O06F06G06O06f07807M07b08F0960:60;>0<60=>0=?0=@0=R0=S0=T0>20?B0?T0?i0@J0@k0@o0B90CJ0DT0Di0E40E`0FT0Fo0G00GH0G`0H60HC0I?0J<0JM0JT0JU0KF0KO0LX0Ma0NZ0Oc0PG0PK0PO0P`0Pa0Pb0Qg0RK0RZ0Ri0T[0Td0To0U80UG0VB0W;0WA0WB0Wn0Xb0Xf0Xg0Xh0Xi0Xj0Y90YA0ZD0[C0[X0[m0\70]70^60^>0^?0^@0^A0^L0^[0_60_70_80_K0_O0_U0_l0a20a30a40aF0aX0a`0ao0bJ0bP0bb0c40c50c60c>0cZ0cl0eC0e\0eb0f;0fC0f\0gT0gU0gV0hB0i60jR0ko0mE0nS0ob10]10^10o11D11T11U11d11e11f11g12912K12Z13414<15D16:16;16J16[17R17S18c18d19319B19Q19`1:11;H1<V1=e1>81?D1?Y1?n1@;1@<1Ae1Am1B?S3hAR1n2AB1mS3hAR2SP2SB2sz1n2b12AB1m2lo3SB02NB5LOIMG3SPL3ABB3abq3ABQ2K82HB5Ha_st5Hl_stS3hAR2SP2SB2sz1n2b12AB1m2lo2kk3SB02NB5LOIMG3SPL3ABB2MB2mq2MQ2HB5Ha_st5Hl_stS2SB1c1k2sz1H2H0S2sz1n2AB2kk3RZB3RZRFFS3hAR2SP2SB1n1m1HS2sz1n2AB1m2kk3RZB2HMS3hAR2SP2SB1c1k2sz1n2AB1m2mu2lo3SB02CB2K03KMU3MUB3HAB2NB2HM5LOIMG3SPL3SZR3RZR1R2HR4ROFF4KDIV3szq3SZQ3rzq3RZQ2mq2MQS3hAR2SB2RI1c2sz1n1m3SB02CB2NB3SZR1R4ROFF3sbq3SBQ2mq2MQSS2SP3SPAS3hAR2SP2SB1n1m3SB03SB1S3hAR2SP2SB1n2AB1mS3hAR2sz1n2AB1m2kk2MBS3hAR2sz1n2AB1m2kk2MBS2SB2sz1n2AB1m2kk3SB03SB13KKB3ABB2MBS3hAR2SB2sz1n2AB1m3SB03SB12NB3SZR3ABB3abq3ABQ2K8S3hAR2SP2SB2sz1n2AB1m2lo3SB03SB12NB5LOIMG3SPL3SZR3ABB3abq3ABQ2K8S3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3KKB3ABB2MB2mq2MQS3hAR2SB2sz1n2AB1m2kk3SB03SB12NB3RZB2HM3KKB3ABB2MB2mq2MQS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3KKB3ABB2MB2mq2MQFSS2SB1c1m2CB1R4ROFFFFS3hAR2SP2SB1c1k2sz1n1m2K01R2KBS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3ABB2MB2mq2MQ3abq3ABQ2HB5Ha_st5Hl_stS1n2AB1m2HM3RZR2K8S3hAR2SP2SB1n2AB1m2HBS3hAR2SP2SB1n2b11m2HB5Ha_st5Hl_stS3hAR2SP2SB1n2b11m2HB5Ha_st5Hl_stS2mqS3hAR2SP2SB2sz1n2b12AB1m2lo3SB03SB12NB5LOIMG3SPL3SZR3ABB2K82HB5Ha_st5Hl_stS3hAR2SP2SB2sz1n2b12AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3KKB3ABB2HB5Ha_st5Hl_stS3hAR2AL2SB1c1k2sz1n1m2NB4IMG'3SZR1R2HR4KDIV3sbq3SBQ3szq3SZQ3rzq3RZQ2mq2MQS2sz1n2kk3RZB3RZR3KKBS2SP2lo3SPLS3hAR2SB2sz1n2AB1m3SB02NB3SZR3ABB3abq3ABQ2K8S3hAR2SB2sz1n2AB1m2kk3SB02NB3RZB2HM3KKB3ABB2MB2mq2MQS3hAR2AL2SB1c2sz1n1m4IMG'1RSS3hAR2SP2SB1n1m2HB5Ha_stS3hAR2SP2SB1n1m2HB5Ha_stS3hAR2SP2SB1c2sz1n1m1RS1c1k3sbq3szqS3hAR2SP2SB2sz1n2AB1m2lo3SB02NB5LOIMG3SPL3SPA3ABB3abq3ABQ2K8S3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3SPA3ABB2MB2mq2MQS2SB1c2sz1m3SZR1RS2SP2loFS3hAR2AL2SB2sz1n2AB1m2kk3SB02NB4IMG'3ABB2MB2mq2MQS1k2K02KBS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB5LOIMG3SPL3SZR3ABB2MB2mq2MQ3abq3ABQS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB5LOIMG3SPL3SZR3ABB2MB2mq2MQ3abq3ABQS3hAR2SB2sz1n2AB1m2kk3SB03SB12NB3SZR3ABB2MB2mq2MQ3abq3ABQS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB5LOIMG3SPL3SZR3ABB2MB2mq2MQ3abq3ABQS2SB2sz1n2AB1m2kk3SB03SB13KKB3ABB2MBS2mqS2mqS3hAR2AL1n1m4IMG'FFS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3SPA3ABB2MB2mq2MQ3abq3ABQS2SB2sz1n2AB1m2kk3SB03SB13KKB3ABB2MBS3hAR2SP2SB1n1mS3hAR2SP2SB1n1mS3hAR2SP2SB1c1k2sz1n2AB1m2mu2lo3SB02CB2K03KMU3MUB3HAB2NB2HM5LOIMG3SPL3SZR3RZR1R2HR4ROFF4KDIV3szq3SZQ3rzq3RZQ2mq2MQS1n2kk2HKS1n2NB1H2H0S3hAR1n1mS3hAR2SP2SB1n1mS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3ABB3abq3ABQ2K8S3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3ABB2MB2mq2MQS1n2NBSS3hAR2SB2sz1n2AB1m3SB02NB3SZR3ABB3abq3ABQ2K8S3hAR2SB2sz1n2AB1m2kk3SB02NB3RZB2HM3KKB3ABB2MB2mq2MQS2loSSSFS3hAR2SP2SB1n1mS1k2sz1nS3hAR2SP2SB2sz1n2AB1m2lo1S2kk3SB03SB12NB3RZB2HM5LOIMG2HS3SZR3ABB2K8S3hAR2SP2SB2sz1n2AB1m2lo1S2kk3SB03SB12NB3RZB2HM5LOIMG2HS2HK3ABBS3hAR2sz1n2AB1m2kk2MBS3hAR2sz1n2AB1m2kk2MBS1n2kk3KKBS3hAR2SP2SB2sz1n2b12AB1m2lo2kk3SB03B1B2NB5LOIMG3SPL3ABB2MB2mq2MQS3hAR2SP2SB2sz1n2b12AB1m2lo3SB03B1B2NB5LOIMG3SPL3ABB3abq3ABQ2K8S2b13B1BFFFS2SB1c1k2szS3hAR2SP2SB1n1mS3hAR2SP2SB1n2AB1m2HB5Ha_stFFS3hAR2SB1c2sz1n1m1RS2mqS1c2CBS3hAR2SP2SB1n1m3SB03SB1S3hAR2SP2SB2sz1n2AB1m1S2kk3SB02NB3RZB2HM2HS3SZR3RZR3ABB2HB5Ha_st5Hl_stFFS3hAR2SP2SB1n1m2HBS3hAR2SP2SB1n1m2HBS2b13B1BS1n2AB1m2HM3RZRS3hAR2SP2SB1c1k2sz1n1m2K01RS1n2NBS3hAR2SP2SB1n1m2NBS3hAR2SP2SB1n1m2NBFFS2sz3SZRS3hAR2AL2SB1c2sz1n1m5ALWF'1RS3hAR2AL1n1m5ALWF'S3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3SPA3ABB2MB2mq2MQ3abq3ABQ2K82HB5Ha_st5Hl_stS2SB1c1k2sz1n2AB1m3HAB2HMS1c2CBS3hAR2SP2SB1c2sz1n1m2CB1RS2b13B1BS3hAR2SP2SB2RI1c2sz1n1m1RS3hAR2SP2SB2sz2AB1m2lo1S2kk3SB05LOIMG2HS3ABB2MB2A02n02HAFSS3hAR2SB2sz1n2AB1m3SB02NB3SZR3ABB3abq3ABQ2K8S3hAR2SB2sz1n2AB1m2kk3SB02NB3RZB2HM3KKB3ABB2MB2mq2MQS3hAR2SP2SB2sz1n2AB1m2lo1S2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3SPA2HS2HK3SZR3ABB3abq3ABQ2K83x151HS3hAR2SP2SB2sz1n2AB1m2lo1S2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3SPA2HS2HK3SZR3ABB2MB2mq2MQ2K83x151HS3hAR2SP2SB2sz1n2b12AB1m2lo2kk3SB02NB5LOIMG3SPL3SPA2MB2mq2MQ3abq3ABQ2K82HB5Ha_st5Hl_stS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3SPA3SZR3ABB3abq3ABQ2K8S3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3ABB3SPA2HK3SZR2MB2mq2MQS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3ABBFS2SB2sz2AB3ABB2K6S2SB2sz2AB3SZR3ABB2K7S1n2AB1m2HM2K81XFS3hAR2SP2SB1n1mFFSS3hAR2SP2SB1n1m2NBS3hAR2SP2SB1n1m2NBS3hAR2SP2SB1n1mS3hAR2SP2SB1c2sz1n1m3SZR1RS3hAR2SP2SB2sz1n2b12AB1m1S2kk3SB02NB3RZB2HM2HS3SZR3ABB2K82HB5Ha_st5Hl_stS3hAR2SP2SB2sz1n2b12AB1m1S2kk3SB02NB3RZB2HM2HS3SZR3ABB2MB2HB5Ha_st5Hl_stS3hAR2SP2SB2sz2AB1m2lo1S2kk3SB05LOIMG2HS3ABB2MB1A2n01HSS3hAR2SP2SB1n1mS3hAR2SP2SB1n1m1HS3hAR2SB2RI1c2sz1n1m3SB02CB2NB3SZR1R4ROFF3sbq3SBQ2mq2MQFS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB5LOIMG3SPL3SZR3ABB2MB2mq2MQ2HB5Ha_st5Hl_stSS3hAR2SP2SB1n1mS3hAR2SP2SB1n1mS3hAR2SP2SB1n1mS3hAR2SP2SB1n1mS1c1k3sbq3szq3rzqS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB02NB5LOIMG3SPL3SPA3ABB2MB2mq2MQ3abq3ABQ2K82HB5Ha_st5Hl_stS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3SPA3SZR3ABB3abq3ABQ2K8S3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3SPA2HK3SZR3ABB2MB2mq2MQS3hAR2sz1n2AB1m3SZRS3hAR2SP2SB2sz1n2AB1m2lo2kk3SB03SB12NB3RZB2HM5LOIMG3SPL3SPA3SZR3ABB2MB2mq2MQS3hAR2sz1n2AB1m2kk2MBS3hAR2sz1n2AB1m2kk2MBS1k2sz2mu3KMUFS3hAR2SP2SB1c1k2sz1n1m2mu2lo3SB03SB12CB2K03KMU3MUB2NB5LOIMG3SPL3SZR3RZR1R2HR4KDIV3sbq3SBQ3szq3SZQ3rzq3RZQS2SP3SPHS3hAR2SP2SB1n2AB1m". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma cbr_A2 : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Pra,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)Ps4x,(8.&40.)Ps3x,(8.&40.)Ps2x,(8.&40.)Ps1x,(8.&40.)Ps0x,(8.&40.)Prax,(8.&40.)PSP,$0.PCBP,$0.PSB,$0.PRI,$0.Pc,$0.Pk,$0.Psz,$0.Pn,$0.Pctx,$0.Pb1,$0.PAB,$0.Pm,$0.Pmu,$0.Plo,$0.PF,(1:.&5.(8.&40.))Pfc,(8.&20.)Pm0,P,(8.&40.)(1;.(8.&8.))Pmm,P,(8.&40.)(1;.(8.&8.))Pjunk,(38.(8.&8.))ZS,$0.(;.+7???8000.(5.(;.R8.+10.)+8.))Zkk,$0.(5.(;.R=.+7.)+8.)P,(2.+10007???9000.R13.)P,(2.(;.R14.(4.+2.+25.))(4.+2.+2?.))P,(7.$0.(6.R15.+1000.)=)P,(1.(2.+1.R14.)(2.R14.+1>.))P,(7.$0.R13.(10.R15.))P,(2.=R15.)P,(2.(11.(;.R16.+1.)R15.)R?.)P,(2.R10.+>0000000.)P,(1.(2.=R14.)(3.R14.+100.))P,(7.$0.R14.(;.(;.R1<.(11.R1:.+100000000.))(11.R19.R18.)))P,(1.(2.=R18.)(2.R18.(4.+2.+1<.)))P,(2.(;.(11.+8.R<.)(30.R19.))R1:.)P,(7.$0.R16.(24.(;.R17.(30.R1:.))+10.))P,(2.+65?000.R1?.)P,(2.(;.R20.+1000.)(23.VhAR,))P,(1<.$19.R13.$39.(1>.$1?.(20.(:.&40.R21.))(21.$1?.)))P,(31.$19.R14.(;.(;.R22.(11.R21.+80.))+30.)(1>.$1?.(20.(:.&40.R19.))(21.$1?.)))P,(25.VCS,R23.+1000.)P,P,(3.+10.(30.R20.))(31.$19.R17.R1>.(1>.$1?.(20.(:.&40.$3:.))(1>.$1?.(20.(:.&40.R1=.))(21.$1?.))))P,(31.$19.R17.R1=.(32.R1?.+3.))P,(31.$19.R18.(;.R1>.+4.)(33.R22.R21.))P,(25.VCS,R20.R24.)P,(31.$19.R1:.R18.(1>.$1?.(34.(35.R17.)R19.)(21.$1?.)))P,(37.R1;.)P,(2=.R1<.R2=.R33.R32.R31.R30.R2?.R2>.)P,(22.$19.R1=.R21.(;.R2>.-30.))P,(2.(23.VhAR,)R22.)P,(2.R23.(24.R30.+70.))P,(2.R31.(4.+2.+3>.))P,(7.$0.(6.R32.+10.)=)P,(29.(1>.(2:.$0.$0.)(2;.$0.$0.R26.R33.)(1>.(2:.$0.$0.)(2;.$0.$0.R29.(;.R29.+8.))(1>.(2:.$0.$0.)(2;.$0.$0.R28.(;.R28.+4.))(1>.(2:.$0.$0.)(2;.$0.$0.R20.(;.R20.R1?.))(21.(2:.$0.$0.))))))R23.R22.)P,(2<.$19.R24.R23.)P,(26.$19.R24.)P,(25.VCS,R29.(24.R36.R29.))(27.$19.VAL,VCS,Lms',$12.(1.(3;.R38.R51.R50.R4:.R49.R48.R47.R46.R45.R44.R43.R37.R36.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2;.R2:.R29.R28.R1.)(2=.(3<.R1.)R38.R3>.R3=.R3<.R3;.R3:.R39.))(14.(15.R51.(:.&40.(;.R37.-30.))R50.R4?.R4>.R4=.R4<.(:.&40.R36.)(:.&40.R2<.)(:.&40.R35.)(:.&40.(;.R35.+2000000000.))(:.&40.R33.)(:.&40.R33.)(:.&40.(;.(11.R33.+100000000.)(24.(24.R2<.R35.)(11.R33.+100000000.))))(:.&40.R31.)R4;.R4:.R49.(:.&40.$16.)(:.&40.+2000000000.)R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.)R29.(:.&40.+49<70.)R28.(17.(8.&40.))R26.(18.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s4x s3x s2x s1x s0x rax SP CBP SB RI c k sz n ctx b1 AB m mu lo F fc m0 mm junk S kk
      SB0 SB1 SBA CB HSZ K0 KMU MUB B1B HAB NB RZB HM RI0 RI1 RIC MUC RICS MAG HW0 HW1 ABCS SH PS FR ST LOIMG SPL SPH SPA MU WM MI SCS.
    facts. unfold hdr_w0, hdr_rest, cbr_frame in *. unfold A_RI_CELL, A_INSTANCE, A_CBR_MID, kAllocBegMagic in *.
    change (1074072 + 48) with 1074120 in RIC.
    assert (HS : S = 0x7fff8000 + (m + 16) / 8) by reflexivity. assert (HK : kk = (n + 7) / 8) by reflexivity. clearbody S kk.
    pose proof (munch_refl [(lo, SP); (AB, AB + 8); (m, m + 4); (S, S + kk)] mm) as MUS.
    pose proof (class_size_range c ltac:(clear -CB; lia)) as SZR. rewrite <- HSZ in SZR.
    assert (RZR : 16 <= rz_size n <= 2048).
    { unfold rz_size. pose proof (rz_log_bound n). split.
      - change 16 with (16 * 2^0) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia.
      - change 2048 with (16 * 2^7). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
    assert (RZ16 : rz_size n mod 16 = 0).
    { unfold rz_size. pose proof (rz_log_bound n). rewrite Z.mul_comm. apply Z_mod_mult. }
    assert (KKB : 0 <= kk /\ n <= 8 * kk < n + 8).
    { subst kk. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). clear -NB H H0. lia. }
    set (R := m - SB - c * 4294967296) in *.
    assert (HR : R = k * sz + (rz_size n - 16)) by (subst R; clear -HM HAB; lia).
    assert (ROFF : 0 <= R < 4294967296) by (rewrite HR; clear -K0 KMU MUB SZR RZR KKB RZB; nia).
    assert (KB : k < 134217728) by (clear -K0 KMU MUB SZR; nia).
    assert (KDIV : (c * 4294967296 + R) mod 2 ^ 32 / sz = k).
    { change (2^32) with 4294967296. rewrite Z.add_comm, Z_mod_plus_full, (Z.mod_small R) by exact ROFF.
      symmetry. apply Z.div_unique with (r := rz_size n - 16); [left; clear -RZR RZB KKB; lia| rewrite HR; clear; lia]. }
    (* [comment removed for export] *)
    pose proof (Z.div_mod SB 4096 ltac:(clear; lia)) as SBQ. rewrite SBA, Z.add_0_r in SBQ. set (sbq := SB / 4096) in SBQ. clearbody sbq.
    assert (SZ16 : sz mod 16 = 0).
    { rewrite HSZ. apply Z.eqb_eq. apply (zall_spec (fun y => class_size y mod 16 =? 0) (Z.to_nat 31) 1 ltac:(vm_compute; reflexivity) c). clear -CB; lia. }
    pose proof (Z.div_mod sz 16 ltac:(clear; lia)) as SZQ. rewrite SZ16, Z.add_0_r in SZQ. set (szq := sz / 16) in SZQ. clearbody szq.
    pose proof (Z.div_mod (rz_size n) 16 ltac:(clear; lia)) as RZQ. rewrite RZ16, Z.add_0_r in RZQ. set (rzq := rz_size n / 16) in RZQ. clearbody rzq.
    assert (ABB : SB + 4294967296 <= AB /\ AB + sz <= SB + 133143986176).
    { rewrite HAB. clear -SB0 CB K0 KMU MUB SZR. split; [nia|].
      assert (c * 4294967296 <= 30 * 4294967296) by nia. assert (k * sz + sz <= 3758096384) by nia. lia. }
    assert (MB : AB + 16 <= m + 16 /\ m + 16 + 8 * kk <= AB + sz) by (rewrite HM; clear -RZR RZB KKB; lia).
    assert (MQ : exists mq, m = 16 * mq).
    { exists (256 * sbq + c * 268435456 + k * szq + rzq - 1). rewrite HM, HAB, SBQ, SZQ, RZQ. clear; lia. }
    assert (ABQ : exists abq, AB = 16 * abq).
    { exists (256 * sbq + c * 268435456 + k * szq). rewrite HAB, SBQ, SZQ. clear; lia. }
    destruct MQ as [mq MQ]. destruct ABQ as [abq ABQ].
    (* [comment removed for export] *)
    zstep. rewrite (v_divuw_gen (c * 4294967296 + R) sz) by (first [clear -ROFF CB; lia | clear -SZR; lia | rewrite KDIV; clear -KB K0; lia]). rewrite KDIV.
    zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 c 7) by (clear; lia). change (2^7) with 128.
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 c 32) by (clear; lia). change (2^32) with 4294967296.
    zstep. zstep. zstep. rewrite (Z.mod_small k 4294967296) by (clear -K0 KB; lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (mu <? sz * k + sz) with false by (symmetry; apply Z.ltb_ge; clear -KMU; lia). cbn [Z.b2z].
    zstep. zstep. zstep.
    change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
    replace (c * 4294967296 + SB + sz * k) with AB by (rewrite HAB; clear; lia).
    rewrite (land_m1_64 AB) by (clear -HAB SB0 SB1 K0 KMU MUB CB SZR; nia).
    (* [comment removed for export] *)
    clear KDIV HR ROFF SZ16 RZ16 SBQ SZQ RZQ sbq szq rzq. subst R.
    (* [comment removed for export] *)
    zstep. if_cases K6; zify_cond K6. { exfalso. clear -K6 ABB. lia. }
    zstep. if_cases K7; zify_cond K7. { exfalso. clear -K7 ABB SZR. lia. }
    zstep. if_cases K8; zify_cond K8.
    - (* [comment removed for export] *)
      clear MAG.
      (* [comment removed for export] *)
      zstep. rewrite land_align2 by (clear -MB ABB SB0 SB1 KKB SZR; lia).
      replace (m / 4 * 4) with m by (rewrite MQ; clear; replace (16 * mq) with (mq * 4 * 4) by lia; rewrite Z.div_mul by lia; lia).
      zstep. zstep. zstep. zstep. zstep.
      rewrite !(shl3_mod32' m) by (first [rewrite MQ; clear; replace (16 * mq) with ((4 * mq) * 4) by lia; apply Z_mod_mult | clear -MB ABB SB0 SB1 KKB SZR; lia]).
      change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3.
      (* [comment removed for export] *)
      match goal with H : rw_cells _ ?mx m [C1 _; C1 _; C2 _] |- _ =>
        apply (rw_cells_reshape asegs mx m _ [C4 (Z_to_bv 64 (3 + 256 * b1))]) in H; [| cbn; tauto | apply w0_bytes; clear -B1B; lia] end.
      zstep. rewrite (sx32_small (3 + 256 * b1)) by (clear -B1B; lia).
      zstep. rewrite (w0_land255 3 b1) by (clear -B1B; lia).
      zstep. zstep. rewrite ?Z.lxor_0_r. zstep. rewrite ?(w0_land255 3 b1) by (clear -B1B; lia).
      zstep. rewrite (w0_lxor 3 b1 3) by (clear -B1B; lia). change (Z.lxor 3 3) with 0. rewrite ?Z.mod_small by (clear -B1B; lia).
      zstep. zstep.
      match goal with H : rw_cells _ ?mx m [C4 ?v] |- _ => idtac "HDRW0" v;
        apply (rw_cells_reshape asegs mx m _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | symmetry; apply w0_bytes; clear -B1B; lia] end.
      (* [comment removed for export] *)
      zstep. change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. rewrite (zx32_lit n) by (clear -NB; lia).
      zstep. zstep. zstep. rewrite (Z.lor_0_l n). zstep. zstep.
      rewrite land_align3 by (clear -NB; lia). replace ((n + 7) / 8 * 8) with (kk * 8) by (clear -HK; lia).
      zstep. zstep.
      callxA (eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (lo := lo) (junk := junk);
        [ rewrite MQ; clear; replace (16 * mq + 16) with ((2 * mq + 2) * 8) by lia; apply Z_mod_mult
        | clear; apply Z_mod_mult
        | clear -KKB; lia
        | clear; lia
        | right; clear -MB ABB SB0 SB1 KKB SZR; lia
        | left; clear; lia
        | eapply crange_sub; [exact ABCS| clear -HM RZR; lia| clear -HM RZB KKB; lia]
        | rewrite Z.div_mul by (clear; lia); rewrite <- HS; eassumption
        | eapply (poison_statics_transport _ _ _ PS MUS); intros; cbn [disjoint_from]; clear -H HS MB ABB SB0 LOIMG KKB SZR; lia
        | eassumption
        | exact LOIMG
        | clear -SPL; lia
        | clear -SPH; lia
        | clear -SPA; lia
        | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia]
        | apply munch_refl
        | apply wmono_refl
        | assumption ]).
      rewrite Z.div_mul in * by (clear; lia).
      apply evtA_done. split.
      + unfold cbrA2_post, A_INSTANCE, A_CBR_MID. cbv zeta. rewrite <- HS, <- HK. deexists 16.
        split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [intros X; exfalso; clear -X K8 HM; lia|].
        split; [assumption|]. split; [assumption|]. split; [rewrite HS; assumption|].
        split; [| assumption].
        eapply (poison_statics_transport _ _ _ PS MUS); intros A0 n0 HA; cbn [disjoint_from]; clear -HA HS MB ABB SB0 LOIMG KKB SZR; lia.
      + cbn [ms_mem]. assumption.
    - (* [comment removed for export] *)
      specialize (MAG ltac:(clear -K8 HM RZR; lia)).
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. rewrite land_align2 by (clear -MB ABB SB0 SB1 KKB SZR; lia).
      replace (m / 4 * 4) with m by (rewrite MQ; clear; replace (16 * mq) with (mq * 4 * 4) by lia; rewrite Z.div_mul by lia; lia).
      zstep. zstep. zstep. zstep. zstep.
      rewrite !(shl3_mod32' m) by (first [rewrite MQ; clear; replace (16 * mq) with ((4 * mq) * 4) by lia; apply Z_mod_mult | clear -MB ABB SB0 SB1 KKB SZR; lia]).
      change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3.
      (* [comment removed for export] *)
      match goal with H : rw_cells _ ?mx m [C1 _; C1 _; C2 _] |- _ =>
        apply (rw_cells_reshape asegs mx m _ [C4 (Z_to_bv 64 (3 + 256 * b1))]) in H; [| cbn; tauto | apply w0_bytes; clear -B1B; lia] end.
      zstep. rewrite (sx32_small (3 + 256 * b1)) by (clear -B1B; lia).
      zstep. rewrite (w0_land255 3 b1) by (clear -B1B; lia).
      zstep. zstep. rewrite ?Z.lxor_0_r. zstep. rewrite ?(w0_land255 3 b1) by (clear -B1B; lia).
      zstep. rewrite (w0_lxor 3 b1 3) by (clear -B1B; lia). change (Z.lxor 3 3) with 0. rewrite ?Z.mod_small by (clear -B1B; lia).
      zstep. zstep.
      match goal with H : rw_cells _ ?mx m [C4 ?v] |- _ => idtac "HDRW0" v;
        apply (rw_cells_reshape asegs mx m _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | symmetry; apply w0_bytes; clear -B1B; lia] end.
      (* [comment removed for export] *)
      zstep. change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. rewrite (zx32_lit n) by (clear -NB; lia).
      zstep. zstep. zstep. rewrite (Z.lor_0_l n). zstep. zstep.
      rewrite land_align3 by (clear -NB; lia). replace ((n + 7) / 8 * 8) with (kk * 8) by (clear -HK; lia).
      zstep. zstep.
      callxA (eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (lo := lo) (junk := junk);
        [ rewrite MQ; clear; replace (16 * mq + 16) with ((2 * mq + 2) * 8) by lia; apply Z_mod_mult
        | clear; apply Z_mod_mult
        | clear -KKB; lia
        | clear; lia
        | right; clear -MB ABB SB0 SB1 KKB SZR; lia
        | left; clear; lia
        | eapply crange_sub; [exact ABCS| clear -HM RZR; lia| clear -HM RZB KKB; lia]
        | rewrite Z.div_mul by (clear; lia); rewrite <- HS; eassumption
        | eapply (poison_statics_transport _ _ _ PS MUS); intros; cbn [disjoint_from]; clear -H HS MB ABB SB0 LOIMG KKB SZR; lia
        | eassumption
        | exact LOIMG
        | clear -SPL; lia
        | clear -SPH; lia
        | clear -SPA; lia
        | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia]
        | apply munch_refl
        | apply wmono_refl
        | assumption ]).
      rewrite Z.div_mul in * by (clear; lia).
      apply evtA_done. split.
      + unfold cbrA2_post, A_INSTANCE, A_CBR_MID. cbv zeta. rewrite <- HS, <- HK. deexists 16.
        split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [intros _; assumption|].
        split; [assumption|]. split; [assumption|]. split; [rewrite HS; assumption|].
        split; [| assumption].
        eapply (poison_statics_transport _ _ _ PS MUS); intros A0 n0 HA; cbn [disjoint_from]; clear -HA HS MB ABB SB0 LOIMG KKB SZR; lia.
      + cbn [ms_mem]. assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cbrB_post (SP : Z) (rax gp tp s0x s1x s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T c AB lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Lms',$12.(13.(8.&40.)Lt0,(8.&40.)(13.(8.&40.)Lt1,(8.&40.)(13.(8.&40.)Lt2,(8.&40.)(13.(8.&40.)La4,(8.&40.)(13.(8.&40.)La5,(8.&40.)(13.(8.&40.)La6,(8.&40.)(13.(8.&40.)La7,(8.&40.)(13.P,(8.&40.)(1;.(8.&8.))Lm',P,(8.&40.)(1;.(8.&8.))(13.(8.&40.)Lrf,(8.&40.)(13.(8.&40.)Lrfd,(8.&40.)(1.(7.$12.R;.(14.(15.O1:.(:.&40.O1;.)O19.O18.R:.R9.R8.O17.O16.(:.&40.(;.O7.+=0.))(:.&40.$16.)(:.&40.O6.)(:.&40.O5.)R7.R6.R5.R4.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.)O3.(:.&40.$3=.)O2.(17.(8.&40.))R3.(18.$19.)))(1.(29.(1>.(2:.$0.$0.)(2;.$0.$0.O4.O1;.)(1>.(2:.$0.$0.)(2;.$0.$0.(;.O7.+;18.)(;.O7.+;28.))(21.(2:.$0.$0.))))O1.R3.)(1.(2<.$19.O1.R3.)(1.(26.$19.R3.)(1.(31.$19.R3.(;.O7.+;18.)(1>.$1?.(20.R2.)(1>.$1?.(20.R1.)(21.$1?.))))(22.$19.R3.O4.O1;.))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02f0@L10726731663.11 L12695585661.105L13008179047.106L13010357315.103L13896129328.106L13898176532.103L13947102829.105L14672398125.105L15252174157.1  L15408760557.105L15514499197.106L15615277319.109L15615277696.108L16591383828.110L16591383828.112L16591383828.113L16901219654.108L17367838211.106L17537314435.105L17843262418.105L1859832977.108 L19097770877.106L19254688765.105L19517093574.108L19670172474.105L19824763834.106L1982837376.1   L21414497247.110L21706531409.105L22085110430.105L23537636879.107L23925044995.105L24483416543.112L24997006130.113L25232997190.108L25936729745.108L26227243962.105L26400619037.4  L26832349894.105L27076373828.111L27076373828.113L27076373828.114L27172440411.109L27197305308.110L27197305308.112L27197305308.113L27335347790.110L2777086687.110 L2777086687.112 L2777086687.115 L28249112353.105L28725181897.111L28725181897.113L28725181897.114L29149214414.110L3034226512.110 L30507153671.109L30507153921.107L30507154048.108L30681723193.108L30713647513.105L30754534054.105L31947677713.108L32679045046.112L3276969806.110 L33022343622.108L3333263037.105 L33524528429.105L33693660589.106L33840403608.113L34340530477.1  L35438268736.105L35444638219.106L35615823082.112L35915773416.105L36361325305.105L36594187357.113L36594187357.115L36644267936.2  L3682289274.105 L37253869809.105L37386999357.105L37974998417.108L38793504685.106L39340114894.110L40083418541.105L40482707888.113L41370106893.2  L42001773902.105L42001773902.108L4216595690.112 L42303277385.114L42963497484.105L44643522781.105L45352191666.113L45390947890.105L45422841347.105L45831443381.110L46364678881.106L46486759747.105L46491748631.105L46506220124.106L46536276577.105L47225596387.113L47468933037.105L47710106298.105L48014437652.110L48014437652.112L48014437652.113L48098986201.2  L48193359475.109L49225653524.110L49225653524.112L49225653524.113L49440411594.105L49698585326.109L49698585326.111L49698585326.112L49911977753.105L50066642841.106L52523578588.113L52923728609.105L53434917262.110L53434917262.112L53434917262.113L53436625319.105L53446206258.113L53519968640.105L53522110720.106L5399757306.108 L54001890285.113L54502676711.105L5485007946.107 L56958148372.110L56958148372.112L56958148372.113L5704162785.105 L57346470248.105L57348485608.105L57370105059.111L57471740362.107L58128025895.109L58142605646.110L58459420406.111L58459420406.113L58480858285.105L59238764521.107L59308628304.6  L59308628433.5  L59308628566.6  L59308632823.3  L59321219739.3  L59934034045.105L60735431143.106L60770881981.4  L60907135335.105L61013718214.108L61564445869.105L61929669302.106L62660600314.107L63257028542.105L63770278666.107L63787280654.1  L64551613201.108L65144493349.110L67176251462.108L67750724942.107L67750724942.108L67782919415.107L6847567636.106 L7281005543.105 L7802516460.105 L7870373393.108 L7870373393.115 L8166636633.105 L8171652662.107 L9232615065.105 L9407832852.110 L9407832852.112 L9407832852.113 L9778164857.105 L9780278521.105 00000@00A00L00W00f01501B01O01R01W01`02302F02j03N04404?04@04A04B04Q04R04S04^04_04`04c04o05?05@05J05K05b05j06506D06E06F06G07?08708a0990:30:m0<U0<]0=40=K0?30?40?k0@b0AK0AS0Ab0BP0C>0Cl0D80D90D:0DI0DQ0DY0Dd0De0Dj0Do0E<0E?0EJ0EU0E]0Ed0Ek0G60HA0HG0HH0HX0HY0Hh0I50I=0IB0IQ0IW0I_0Ig0Io0J70JD0JE0JM0JN0JO0JW0JX0JY0Jh0K70K80KC0KP0KQ0L50LY0M?0ME0MX0N<0N`0OF0ON0Oc0P80PO0PP0PQ0P`0Pa0Q[0RU0T=0TJ0TR0T`0Tn0U=0UJ0UW0Ua0VE0Vi0WO0WP0WW0W^0Wi0X10X20X:0XN0Xb0Xo0Y90YN0Y_0Z40Z>0ZL0ZM0ZZ0Ze0[20[=0[B0[O0[c0[d0[n0\20\A0\I0\T0\\0\d0\n0]70]D0]Q0]`0]o0^00^B0^C0^g0_K0`10`80`?S2SB1c1k2sz1H2H0FS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hAR2AL4IMG'S1TS3hARS3hAR3CTXS3hAR2SP2SB3SB03SB1S3hAR2SP2SB3SB03SB1S3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2rf2SP1T3TB12HB5Ha_st5Hl_st3rfd1nS3hAR2SP2loFFFS3hAR2SP2lo3SPLFFS3hAR2SP2loFFS1TS3hAR2SP3CBPS3hAR2sz2AB1m2M1FS3hAR2SP1TFS3hAR2SP2HB5Ha_st5Hl_stS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLFFFS3hAR2SP3CBP1T2lo3CBT5LOIMG3SPL4SEP14SEP32HB5Ha_st5Hl_stS3hAR2SP3CBP1T2lo3CBT5LOIMG3SPL4SEP14SEP32HB5Ha_st5Hl_stS3hAR2rf2SP3CBP1T3CBT2HB5Ha_st5Hl_st3rfd1nS3hAR2SP2SB2sz2AB3ABB2K3S3hAR2SP2SB2sz2AB1m2lo3SB12M15LOIMG3SPL3ABB2HB5Ha_st5Hl_stS3hAR2SP2SB2sz2AB1m2lo3SB12M15LOIMG3SPL3ABB2HB5Ha_st5Hl_stS3hAR2rf2SP2SB2sz2AB1m1T3CTX2lo3SB03SB12M02M13TB13XB13TSB5LOIMG3SPL3SPA3ABB4Kctx2KT2HB5Ha_st5Hl_st3rfd1nS3hAR2SPS3hAR2SP2HB5Ha_st5Hl_stS3hAR2SP2HB5Ha_st5Hl_stS3hAR2rf2SP3CBP2SB1T3CTX2lo3SB13CBT3TB13XB12TC5LOIMG3SPL3SPA4SEP14SEP24SEP34Kctx2KT2HB5Ha_st5Hl_st3rfd1nFS3hAR2SP1T3CTX2lo2TC5LOIMG3SPL4SEP14SEP22HB5Ha_st5Hl_stS3hAR2SP1T3CTX2lo2TC5LOIMG3SPL4SEP14SEP22HB5Ha_st5Hl_stS3hAR2rf2SP1T3CTX2TC2HB5Ha_st5Hl_st3rfd1nS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2SB2sz2AB2lo3SB03SB15LOIMG3SPL3SZR3ABBS3hAR2SP2SB2sz2AB2lo3SB03SB15LOIMG3SPL3SZR3ABBS3hAR2SP2SB2sz2AB2lo3SB03SB15LOIMG3SPL3SZR3ABBS3hAR2SP3CTXFFS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP2loFS3hARS3hARS3hAR2SP1T2HBS1TS3hAR2SP2loS3hAR2SP2loS3hAR2SPS3hAR1TS3hAR1TS3hAR2SP3CBP2SB1T3CTX2lo3SB13CBT2TC5LOIMG3SPL4SEP14SEP24SEP32HB5Ha_st5Hl_stS3hAR2SP3CBP2SB1T3CTX2lo3SB13CBT2TC5LOIMG3SPL4SEP14SEP24SEP32HB5Ha_st5Hl_stS1n2NBFS3hAR2sz2AB1m2M1FS3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hAR2SPS3hARS3hAR2SP2lo3SPLS1c2CBS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2AB1m2M0FS3hAR2SPFFS3hAR2SPFFS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLFS3hAR2SP2HBS3hAR2AL4IMG'FS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2rf2SP1T3TB12HB5Ha_st5Hl_st3rfd1nS1c2CBS3hAR2SP2SB3SB03SB1S3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2rf2SP1T3TB12HB5Ha_st5Hl_st3rfd1nS3hAR2SPS3hAR2SP3SPH2HB5Ha_stS3hAR2SP3SPH2HB5Ha_stS3hAR2SP1T3TB22HB5Ha_stFFS3hAR2SP2lo3SPLFS3hAR2SP2SB2sz2AB1m2lo3SB12M15LOIMG3SPL3ABB2HB5Ha_st5Hl_stS3hAR2SP2SB2sz2AB1m2lo3SB12M15LOIMG3SPL3ABB2HB5Ha_st5Hl_stS3hAR2rf2SP2SB2sz2AB1m1T3CTX2lo3SB03SB12M02M13TB13XB13TSB5LOIMG3SPL3SPA3ABB4Kctx2KT2HB5Ha_st5Hl_st3rfd1nS3hAR2AL4IMG'S3hAR2SPS3hAR2AL5ALWF'S3hAR2AL5ALWF'S3hAR2SP2lo3SPLS3hAR2SP1T2HBS3hAR2AL4IMG'S3hAR2SP1TS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2rf2SP1T3TB12HB5Ha_st5Hl_st3rfd1nFS3hAR1TS3hAR1TS3hAR2SP2HBS3hAR2SPFS3hAR2SPS3hAR2SP1T2lo3SPL2HBS3hAR2SP1T2lo3SPL2HBS3hAR2AL4IMG'S3hAR2SP1TS2SB2sz2AB3SB03ABB2K1S2SB2sz2AB3ABB2K2S2SB2sz2AB3SZR3ABB2K3S1T3TB12KTS3CTX3XB14KctxFS3hAR2AL4IMG'S2SB1c1k2szS3hAR2AL4IMG'S3hAR2SP2loS3hARS3hAR2SP1n2NBS3hAR2SP3CTX3XB13XB2FS3hAR2SP1TS2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SPS3hAR2SP1mS3hAR3CTXS3hAR2AL4IMG'S3hAR2AB1m2M0S3hAR2SP2lo3SPLS3hAR2SP2lo3SPLFS3hAR2SP1T3TB13TB2FS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2rf2SP1T3TB12HB5Ha_st5Hl_st3rfd1nS3hAR1TS3hAR1T". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma cbr_B : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycle ()) "Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Pa0,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)Ps4x,(8.&40.)Ps3x,(8.&40.)Ps2x,(8.&40.)Ps1x,(8.&40.)Ps0x,(8.&40.)Prax,(8.&40.)Prf,(8.&40.)Prfd,(8.&40.)PSP,$0.PCBP,$0.PSB,$0.Pc,$0.Pk,$0.Psz,$0.Pn,$0.Pctx,$0.Pb1,$0.PAB,$0.Pm,$0.PT,$0.PCTX,$0.Plo,$0.PF,(1:.&5.(8.&40.))Pfc,(8.&20.)Pm0,P,(8.&40.)(1;.(8.&8.))Pmm,P,(8.&40.)(1;.(8.&8.))P,(2.+10007???9000.R10.)P,(2.(;.(;.R11.(4.+2.+25.))+1000.)(4.+2.+2?.))P,(1.(2.+1.R11.)(2.R11.+1>.))P,(7.$0.R10.(10.R12.))P,(2.=R12.)P,(2.(11.(;.R13.+1.)R12.)+>0000000.)P,(7.$0.R?.(;.(;.R16.(11.R15.+100000000.))(11.R14.R13.)))P,(1.(2.=R13.)(2.R13.(4.+2.+1<.)))P,(2.R11.R10.)P,(2.(;.R11.+10.)(;.R12.R16.))P,(1<.$19.R;.$1=.(1>.$1?.(20.(:.&40.R1:.))(21.$1?.)))P,(31.$19.R<.R13.(32.R15.=))P,(31.$19.R=.(;.R14.+4.)(33.R18.R17.))P,(25.VCS,R16.R1:.)P,(1<.$19.R?.R1?.(1>.$1?.(20.(:.&40.(;.R15.+=0.)))(21.$1?.)))P,(25.VCS,R20.+8.)P,(2.=R21.)P,(2.(;.R22.+8.)(4.+2.+3?.))P,(3>.(2.(;.R19.+1000.)R23.)(2.(;.R23.+8.)R19.))P,(31.$19.R14.(;.R1:.+;18.)(1>.$1?.(20.R27.)(1>.$1?.(20.R26.)(21.$1?.))))P,(3?.R15.R1;.R1:.)P,(25.VCS,R1<.+1000.)P,(25.VCS,R1<.+10000.)P,(1.(2.+1000.R1>.)(3>.(2.(;.R1>.+1000.)+10000.)(2.+65?000.R1>.)))P,(2.(;.R1?.+1000.)(4.+2.+2?.))P,(2.+65?000.R1?.)P,(2.(;.R20.+10000.)(4.+2.+2?.))P,(3>.(2.(;.R22.+1000.)R21.)(2.(;.R21.+10000.)R22.))P,(3>.(2.(;.R23.+1000.)R2<.)(2.(;.R2<.(4.+2.+25.))R23.))P,(2=.R1>.R2?.R37.R36.R35.R34.R33.R32.)P,(22.$19.R1?.R23.(;.R30.-30.))P,(2.(23.VhAR,)R24.)P,(2.R25.(24.R32.+70.))P,(2.R33.(4.+2.+3>.))P,(7.$0.(6.R34.+10.)=)P,(3>.(2.R35.R2:.)(2.(;.R2:.+1000.)R28.))P,(3>.(2.R36.R2:.)(2.(;.R2:.+10000.)R29.))P,(3>.(2.R37.R36.)(2.(;.R36.+8.)R2:.))P,(29.(1>.(2:.$0.$0.)(2;.$0.$0.R2;.R38.)(1>.(2:.$0.$0.)(2;.$0.$0.(;.R2=.+;18.)(;.R2=.+;28.))(21.(2:.$0.$0.))))R28.R27.)P,(2<.$19.R29.R28.)P,(26.$19.R29.)P,(25.VCS,R2>.(24.R3;.R2>.))P,(7.(8.&40.)R5;.(:.&40.$40.))(27.$19.VAL,VCS,(41.R3=.R40.R5=.R5<.R41.R42.R43.R44.R45.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R32.R3:.R34.R30.R2?.R2>.R2=.)(14.(15.(:.&40.$2?.)(:.&40.(;.R3=.-30.))R5=.R5<.R5;.R5:.R59.(:.&40.R3<.)(:.&40.R33.)R58.R57.R56.R55.R54.R53.R52.R51.(:.&40.R34.)(:.&40.$16.)(:.&40.+2000000000.)R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.)R2?.(:.&40.$2?.)R2>.(17.(8.&40.))R2<.(18.$19.)))")
(* [comment removed for export] *).
  Proof.
    (intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s4x s3x s2x s1x s0x rax rf rfd SP CBP SB c k sz n ctx b1 AB m T CTX lo F fc m0 mm SB0 SB1 CB HSZ K0 KMU HAB NB M0 M1 SBC HW0 HW1 ABCS CBC CBCS CB0 CB1 CBT TST dd_H; ddestruct dd_H as (HK & TSD & TPC & TSA & CTH); intros TCS CTXCS TB1 TB2 XB1 XB2 TC TSB FR ST LOIMG SPL SPH SPA SEP1 SEP2 SEP3 MU WM MI SCS ->).
    facts. unfold hdr_w0, hdr_rest, cbr_frame in *.
    unfold A_CBR_MID, A_SPACEBEG_CELL, A_INSTANCE, A_LC_DEALLOC, A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP in *.
    change (1074072 + 32) with 1074104 in SBC. change (1684672 + 8) with 1684680 in HK.
    pose proof (class_size_range c ltac:(clear -CB; lia)) as SZR. rewrite <- HSZ in SZR.
    assert (ABB : SB + 4294967296 <= AB /\ AB + sz <= SB + 133143986176).
    { rewrite HAB. clear -SB0 CB K0 KMU SZR. split; [nia|].
      assert (c * 4294967296 <= 30 * 4294967296) by nia. assert (k * sz + sz <= 3758096384) by nia. lia. }
    assert (KSZ : 0 <= k * sz < 4294967296) by (clear -K0 KMU SZR; nia).
    (* [comment removed for export] *)
    zstep. carve_frame 16%nat ST. zstep. zstep.
    zstep. carve_frame 16%nat ST. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    zstep. zstep. zstep. zstep. zstep.
    try match goal with |- context [Z_to_bv 64 (Z.shiftr ?x 29)] =>
      replace (Z_to_bv 64 (Z.shiftr x 29)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity) end.
    zstep. zstep. zstep.
    zstep. if_cases Kctx; zify_cond Kctx. { exfalso. clear -Kctx XB1. lia. }
    zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (SP + -80) _ |- _ => release_frame H ST (SP + -64) end.
    zstep.
    zstep. if_cases KT; zify_cond KT. { exfalso. clear -KT TB1. lia. }
    zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (SP + -64) _ |- _ => release_frame H ST (SP + -48) end.
    zstep.
    (* [comment removed for export] *)
    replace (T + 2047 + 753) with (T + 2800) by (clear; lia).
    zstep. change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zstep. rewrite (zx32_lit n) by (clear -NB; lia).
    replace (T + 2800 + 48) with (T + 2840 + 8) by (clear; lia). replace (T + 2800 + 40) with (T + 2840) by (clear; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 ABB SB0. lia. }
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2 ABB. lia. }
    zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3 ABB SZR. lia. }
    zstep. zstep. zstep. zstep.
    replace (AB - SB) with (c * 4294967296 + k * sz) by (rewrite HAB; clear; lia).
    rewrite (shl27_shr59 c (k * sz)) by (first [clear -CB; lia | exact KSZ]).
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. replace (SP + -48 + 48) with SP by (clear; lia). zstep.
    release_frame FR ST SP.
    apply evtA_done. unfold cbrB_post, A_INSTANCE, A_LC_DEALLOC. deexists 10.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [eassumption| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CbRecycle.

End ARUN_1.
