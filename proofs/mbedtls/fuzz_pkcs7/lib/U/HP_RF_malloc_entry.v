(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_malloc_entry () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RDEBRUIJN"; "RP_1.rdbi"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_wrap"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "RP_1.rDB32"; "Stdlib.ZArith.BinInt.Z.lor"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_to_class"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.MMAP_THRESHOLD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RNEED_LOCKS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rentry_post"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmalloc_entry"; "RP_1.rentry_big_post"].

Section RP_1. Context {hRP : run_params}.
Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rDB32 : Z := 125613361.   (* [comment removed for export] *)
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L42464846132.2000001S". (* [comment removed for export] *)
#[using="Type"] Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition rdebruijn_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs RDEBRUIJN 32 with Some bs => bs | None => [] end).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020=L6389736766.3L9695465381.3000001002SS". (* [comment removed for export] *)
#[using="Type"] Lemma rdebruijn_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L12561274796.7L36800083462.8L43035830038.7L49165022855.7L66731657638.700000500>00D00I00OS1k1RS1n2Hk2HnS1k2HkS1k1RS1k2Hk". (* [comment removed for export] *)
#[using="Type"] Lemma rdebruijn_read : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "Pm,P,(0.&40.)(1.(0.&8.))Pk,$2.P,(3.$4.R2.)P,(5.(6.=R2.)(7.R2.+20.))(8.(1.(9.(0.&8.)))(:.$4.R4.(;.(<.$=.(>.R3.)))#1.)(?.(9.(0.&8.))(10.(0.&8.)(11.R3.)(12.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros m k MI Hk.
  destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (rdbi_range k) as R.
  rewrite (bytes_at_read rsegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
  assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
  ddestruct Hn as (n & -> & Hn).
  Ltac solve_db := vm_compute; reflexivity.
  do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L25673529136.3L41415986323.3L42464509897.4L51794599906.3L53401755006.400000600700:00@00CS1k2HkSS1kS1k2HkS1k". (* [comment removed for export] *)
#[using="Type"] Lemma mul_srliw27 k : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "P,(5.(6.=O1.)(7.O1.+20.))(8.$2.(13.&20.(14.(15.&20.(16.&40.(17.&40.(18.(19.+2.O1.)$1:.))))+1;.))(>.O1.))")
(* [comment removed for export] *).
Proof.
  intros Hk. unfold rdbi.
  assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
  rewrite unsigned_lit by (unfold rDB32; nia).
  change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition rclz_v4 (x : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "Zv1,$2.(1;.(14.O1.+2.)O1.)Zv2,$2.(1;.R1.(14.O1.+1.))Zw2,$2.(1;.(14.R1.+2.)(14.O1.+1.))Zw3,$2.(1;.(14.R1.+4.)R1.)(1;.(14.R1.+8.)R1.)")
(* [comment removed for export] *).
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
#[using="Type"] Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. vm_compute. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L56093946140.5L6160744982.3 L66743495062.300000600700=S1x2HxSS1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof.
  intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
  apply andb_prop in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
  unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39913182148.3000006S1k2Hk". (* [comment removed for export] *)
#[using="Type"] Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L6755913577.4000001S". (* [comment removed for export] *)
#[using="Type"] Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. intros Ha He.
  assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "Lms',$1<.(1=.(0.&40.)La0,(0.&40.)(1=.(0.&40.)La1,(0.&40.)(1=.(0.&40.)La2,(0.&40.)(1=.(0.&40.)La3,(0.&40.)(1=.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(5.(8.$1<.R6.(1>.(1?.O20.(17.&40.(<.(16.&40.O1?.)-30.))O1>.O1=.O10.O?.O>.(17.&40.O1.)(17.&40.$20.)R5.R4.R3.R2.O=.O<.O;.O:.O1:.(17.&40.$=.)(17.&40.(21.O1.))O17.O16.O15.O14.O13.O12.O11.O9.O8.O7.O6.)O5.(17.&40.+40774.)O4.(22.(0.&40.))R1.(23.$4.)))(5.(24.$4.R1.(<.(16.&40.O1?.)-30.)(10.$25.(26.O18.)(10.$25.(26.O19.)(10.$25.(26.O1:.)(10.$25.(26.O1;.)(10.$25.(26.O1<.)(10.$25.(26.O20.)(12.$25.))))))))(5.(27.$4.R1.O3.(<.(16.&40.O1?.)-30.))(5.(28.(10.(29.$2.$2.)(2:.$2.$2.(2;.(16.&40.O1?.)+30.)(16.&40.O1?.))(12.(29.$2.$2.)))O2.R1.)(5.(2<.$4.O2.R1.)(3.$4.R1.)))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "01a0?L10022931269.69L10023289312.70L11028254010.78L12076517061.75L12712880528.68L1482069293.85 L16075583823.72L16918837679.65L18179265889.62L18179724641.64L18181367782.61L18392021271.58L18468417428.66L20112476756.51L22796385821.66L23102976490.62L23235732884.84L24140570697.79L2425334338.53 L26454810024.67L27648159986.78L27688007078.72L27690091296.71L28155396397.67L30264064457.79L31323011143.85L31378308326.50L31464074128.84L31464074129.70L31799012504.85L32509216314.78L33547404564.53L33547404564.54L35516470224.72L35842097472.83L35842273781.84L36759189123.74L36761272705.75L37989264965.79L40346260359.84L40823607660.71L40825509068.51L41247213570.58L41415828429.62L41416053612.66L41417920842.61L41417920844.68L41418135242.79L41652169568.66L43061431595.48L43071640411.69L43073741533.66L43393816798.85L4351261724.84 L4353507130.85 L4353685161.85 L43901314518.78L4541396730.70 L45615793312.68L46778126076.63L48775325161.70L50998141849.66L51792414139.79L52488874831.68L52488886504.62L52489072197.64L52514079877.85L52514229526.85L53279723706.78L53517140246.78L53519091638.85L53519141806.66L53519207973.85L55347555524.84L56775177115.72L56777654300.84L5687611130.79 L5690084950.65 L5690538106.76 L5690538235.73 L5690538876.70 L5690555260.67 L57017997905.65L57394758142.84L5742896305.66 L5742896310.61 L5744989872.63 L59249165194.65L59251192621.66L59308628179.52L59308628304.52L59308631791.66L59603018663.70L61929812114.52L61929812241.52L61929812368.56L63370523563.74L65199789371.72L66468437330.72L67482146131.69L67507599744.71L6753458106.61 L6753458109.66 L6753473980.84 L6753473981.70 L67961326483.72L679672258.78  L7178147913.72 L7620900481.66 L7620900486.61 L8396965519.68 L9540656382.79 L9627047418.78 00000<00H00^01401E01S01`01j02402A02K02[02f02k03903H03V04504<04P04l05@05T05_05k06C06G06S06_07707M07m08Y08b09009>09U09l0:80:O0:_0:`0:n0;50;<0;C0;P0;h0<50<?0<O0<\0<j0=80=F0=T0=n0>70>H0>R0>^0>i0?H0?U0?d0?o0@60@=0@W0@m0A40A90A@0A^0Af0B00BH0BR0Bh0C;0CK0CX0C]0Cg0D40D>0DH0DS0D^0Df0Dn0E60E?0ED0EI0EN0Ea0F80FK0F[0Fh0Fo0G90G@0GG0GP0Gl0HC0HP0HZ0Hi0IA0I[S1n1q1k1i2IRS1n1q1k1i2IRS1n1q1x2v12v22w22w32w4S1n1q1x2v12v22w22w32R5S1n1q1x2v12v23RV2S1n1q1k2i13SR2S1n1q1k1i3SR1S1n1q1k2P2S1n1q1x2XRS1n1q1x2XR2v1S1n1q1x2XRS1n1N1q1x2QR3Q10S1n1q1k3K13S1n1NS1n1q1x2v13RV1S1n1q2K21r1H2H0S1n1q1k2i13SR2S1n1q1x1k2LG3Q102v12v22w22w32w4S1n1N1qS1n1N1q1x1k2EK3K131iS1n1N1q1x2v12v22w22w32w43RW4S1n1q1x2v12v22w23RW2S1n1q1x2v12v22w23RW2S1n1q1k3K13S1n1q1k1i2IRS1n1N1q1x1k2EX3K132i12LTS2spS1n1q1k1i2IRS1n1q1k1i2IRS1n1N1q1x1k2EX3K132i12GES1n1q1x2v12v22w22w32w4S2ra2sp2lo3ILO2LO2HB5Ha_st5Hl_stS2sp2s02lo3ILO2LO2HB5Ha_st5Hl_st2s12s22s32s4S1n1q1k1iS1n1q1k2i13I1RS1n1q1k2i13I1RS1n1q1x2v12v22w22w33RW3S1n1q1x2v12v22w22w33RW3S1n1q1k1i2IRS1n1N1q1k3K131i2i11c2HcS1n1q1x2v12v22w2SS1n1N1q1r1H2H0S1n1q1xS1n1q1kS1n1q1xS1n1q1x2v12v2S1n1q1x1k2v12v22w22w32w4S1n1N1q1k3K13S2sp2lo2LOS1n1q1x2R12v12v2S1n1q1x2R12v1S1n1q1k2i13I1RS1n1q1k2i13I1RS1n1q1k2i13I1RS1n1q1k2i13I1RS1n1q1x2v12v22w22w32w43RW4S1n1q1k1iS1n1q1x2v12v23RV2S1n1q1x2R2S1n1q1k1i2IRS1n1q1k3K13S1n1q1x1k2LG3Q102v12v22w22w32w4S1n1q1k3Q101iS1n1q2K21r1H2H0S1n1q1k3Q10S1n1q1kS1n1q1kS1n1q1x2v12v22w22w32w43RW4S1n1q1x2v12v22w22w32w4S1n1q1kS1n1qS1n1q1kS1n1N1q1k3K131i2IR2i11c2Hc3I1RS1q1k2QRS1n1q1k2QRS1n1q1x1k2v12v22w22w32w4S1n1q1x2v1S1n1q1x2v12v22w22w32w4S1n1q1x2v12v22w22w3S1n1q1x2v12v22w2S1n1q1x2v12v2S1n1qS1n1q1k2i1S1n1q1x2XR2v1S1n1q1x2XRS1n1q1x2XRS1n1q1k3K13S1n1q1k3K13S1n1N2K0S1n1N2K1S1n1q2KLS1n1q1k1iS1n1NS1n1NS1n1NS1n1q1x2v12v22w22w3S1n1N1q1x1k2EX3K131i2K3S1n1q1x2v12v22w22R4S1n1q1x2v12v22R3S1n1q1k1i3SR1S1n1q1xS1n1q1x2v1S1n1q1kS1n1q1kS1n1q1k1iS1n1N1q1x2v12v22w22w32w43RW4S1n1N1q1x1k2EX3K131i2K3S1n1q1x2XR2v1S1n1q1x2XRS1n1N1q1k3K131iS1n1q1x1k2v12v22w22w32w4S1n1q1x2v12v22w22w32w43RW4". (* [comment removed for export] *)
#[using="Type"] Lemma rmalloc_entry_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(2=.&5.(0.&40.))Pfc,(0.&20.)Pm,$2>.Plo,$2.Pn,$2.P,(8.(0.&40.)R1;.(17.&40.R1.))P,(5.(6.=R2.)(7.R2.$2?.))P,(27.$4.R5.R4.(16.&40.R25.))P,(6.+7>000.R5.)P,(6.R6.(2;.(16.&40.R27.)+30.))P,(3.$4.R8.)P,(24.$4.R9.$30.(10.$25.(31.(11.=))(12.$25.)))(32.$4.(33.R2;.R2:.R29.R28.R24.R23.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R27.R26.R25.R1>.R1=.R1<.R1;.R10.R?.R>.R=.R<.R;.R9.R:.R8.)(1>.(1?.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(17.&40.$34.)R;.(22.(0.&40.))R:.(23.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until n. intros HA N ST ILO LO MI NL. subst a0.
  dpose (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rmalloc_entry, RNEED_LOCKS in *.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  (* [comment removed for export] *)
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
    sc = size_to_class n ->
    mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 512851 [C1 (b8 0)] ->
    evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 512960) a0' a1' a2' a3' a4 a5 a6 a7
               s2 (Z_to_bv 64 68135) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x4075c) fc None mj (seg_rom rsegs))).
  { intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
    step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
    apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. deexists 5. split; [reflexivity|].
    split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply LOCKJ; try assumption.
    rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step.
    rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. step. replace (94460 + (i + 1) * 2) with (94460 + 2 * (i + 1)) by lia.
    lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z) (mj : mem),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
      munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 512851 [C1 (b8 0)] ->
      evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 512960)
                 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 94460) (Z_to_bv 64 c) (Z_to_bv 64 (94460 + 2 * (i + 1))) a4 a5 a6 a7
                 s2 (Z_to_bv 64 68135) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x40740) fc None mj (seg_rom rsegs))).
    { intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (94460 + i1 * 2) with (94460 + 2 * i1) by lia.
      pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "Lms',$1<.(1=.(0.&40.)La1,(0.&40.)(1=.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(5.(8.$1<.R3.(1>.(1?.O22.(17.&40.(<.(16.&40.O21.)-30.))O20.O1?.O12.O11.O10.(17.&40.O1.)(17.&40.$20.)(17.&40.+1??><.)R2.O?.O>.O=.O<.O;.O:.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O9.O8.O7.O6.)O5.(17.&40.+405=<.)O4.(22.(0.&40.))R1.(23.$4.)))(5.(24.$4.R1.(<.(16.&40.O21.)-30.)(10.$25.(26.O1:.)(10.$25.(26.O1;.)(10.$25.(26.O1<.)(10.$25.(26.O1=.)(10.$25.(26.O1>.)(10.$25.(26.O22.)(12.$25.))))))))(5.(27.$4.R1.O3.(<.(16.&40.O21.)-30.))(5.(28.(10.(29.$2.$2.)(2:.$2.$2.(2;.(16.&40.O21.)+30.)(16.&40.O21.))(12.(29.$2.$2.)))O2.R1.)(5.(2<.$4.O2.R1.)(3.$4.R1.))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L31378308326.46L43061431595.44L59308628179.48L59308628304.48L61929812114.48L61929812241.4800000400>00F00N00S00XS2spS2sp2lo2LOS1n1N2K0S1n1N2K1S1n1NS1n1N". (* [comment removed for export] *)
#[using="Type"] Lemma rentry_big_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_entry ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(2=.&5.(0.&40.))Pfc,(0.&20.)Pm,$2>.Plo,$2.Pn,$2.P,(8.(0.&40.)R1;.(17.&40.R1.))P,(5.(6.$2?.R2.)(7.R2.(19.+2.+20.)))P,(27.$4.R5.R4.(16.&40.R25.))P,(6.+7>000.R5.)P,(6.R6.(2;.(16.&40.R27.)+30.))P,(3.$4.R8.)(32.$4.(35.R2:.R29.R28.R27.R23.R22.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R26.R25.R24.R1?.R1>.R1=.R1<.R1;.R1:.R?.R>.R=.R<.R;.R:.R8.R9.R7.)(1>.(1?.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R;.(17.&40.$34.)R:.(22.(0.&40.))R9.(23.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold rmalloc_entry.
  step. carve_frame 48%nat ST. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  clear K0.
  step. step. step. step. step.
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  apply evt_done. unfold rentry_big_post, RMLOCK. deexists 2. split; [reflexivity|].
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
  repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
