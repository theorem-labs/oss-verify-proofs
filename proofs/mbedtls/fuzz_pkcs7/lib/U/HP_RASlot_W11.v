(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W11.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RASlot_W2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W11 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSMALL_CNT"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.small_cnt"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMED_CNT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.med_cnt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RP_1.HALVE.rcnt_regs"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.halve_big"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.even"; "Corelib.Init.Datatypes.true"; "RP_1.rcnt_regs"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.halve_even"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rsmall_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs RSMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs RMED_CNT 4 with Some bs => bs | None => [] end).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L47026461838.3L5977798933.3 000001002SS". (* [comment removed for export] *)
#[using="Type"] Lemma rsmall_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L13760596990.3L6995176421.3 000001002SS". (* [comment removed for export] *)
#[using="Type"] Lemma rmed_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11954610599.8 L12561014716.8 L13368604394.8 L17278245107.9 L36800083845.10L36800083845.9 L42192479848.10L51227166468.8 00000800E00R00]00l01<01G01MS2sc3HscS2sc1i3Hsc2HiS2sc1i3Hsc2HiS1i1n2Hi2HnS1n3Hsc1k2Hn2HkS3Hsc1k2Hi2Hn2HkS1n1k2Hn2HkS2sc1i". (* [comment removed for export] *)
#[using="Type"] Lemma rsmall_cnt_read : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "Pm,P,(0.&40.)(1.(0.&8.))Psc,$2.Pi,$2.P,(3.$4.R3.)P,(5.(6.=R3.)(7.R3.+9.))P,(5.(6.=R3.)(7.R3.+3.))(8.(1.(9.(0.&8.)))(:.$4.R6.(;.(<.(<.$=.(>.+3.R5.))R4.))#1.)(?.(9.(0.&8.))(10.(0.&8.)(11.(12.R5.R4.))(13.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros m sc i MI Hsc Hi.
  destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
  rewrite (bytes_at_read rsegs m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). ddestruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). ddestruct Hi' as (k & -> & Hk).
  replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
  unfold small_cnt. rewrite !Nat2Z.id.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L10357982403.6L15686399655.6L796775439.6  00000600<00BS1i2HiS1i2HiS1i2Hi". (* [comment removed for export] *)
#[using="Type"] Lemma rmed_cnt_read : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "Pm,P,(0.&40.)(1.(0.&8.))Pi,$2.P,(3.$4.R2.)P,(5.(6.=R2.)(7.R2.+4.))(8.(1.(9.(0.&8.)))(:.$4.R4.(;.(<.$14.R3.))#1.)(?.(9.(0.&8.))(10.(0.&8.)(11.(15.R3.))(13.(0.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros m i MI Hi.
  destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read rsegs m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "(16.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.(17.Vusage,)(17.+1000.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.(17.Vsize,)O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L19338236499.43L2043847691.41 L26771803911.57L41351692016.42L41352163945.39L42659555206.50L47816451760.42L47822661935.43L48274491860.50L52592503743.39L5331805151.43 L53511514102.57L59314923118.40L65106303156.42L65106351149.39L6758062595.43 L9600236033.40 00000300600J00X00`01=01L01[02202B02P03<03?03J03S03V03^S1FS1FS1F3cnt3C321q1r1H2H0S1F3cnt2CR3C32S3cnt2CRS4size2SZ1F3cnt2CR1q1K1r1H2H0S4size1F3cnt2PRS4size1F3cnt2PRS4size1F3cnt1q1K1r1H2H0S4size2SZ3cnt2CRS1F3cnt2CR3C32S4size2SZ1F3cnt2CR2PR2q01K1q1r1H2H02r02H42H5S1KS4size2SZ1FS4size2SZS1FS3cnt2CR". (* [comment removed for export] *)
#[using="SZ"] Lemma rhalve_big_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "PF,$18.Pcnt,$2.Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PFr,(19.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(5.(6.=R1?.)(7.R1?.(1:.+2.(1;.R20.))))P,(6.R20.+20.)P,(3.$4.R3.)(1<.$4.Lms',$1=.(1>.(0.&40.)La2',(0.&40.)(1>.(0.&40.)La3',(0.&40.)(8.$1=.R3.(1?.(20.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R2.R1.R1:.R19.R18.R17.R16.(17.(21.R26.R25.Vsize,))R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(22.&40.+40;7<.)R8.(23.(0.&40.))R7.(24.$4.)))))(1?.(20.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(17.R22.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(22.&40.+40;68.)R5.(23.(0.&40.))R4.(24.$4.)))")
(* [comment removed for export] *).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
  - cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
    step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
    apply evt_done. deexists 2. replace cnt with 0 by lia. reflexivity.
  - cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
    assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
    step. rewrite (unsigned_lit (size * cnt)) by lia.
    step. rewrite (wz_unsigned cnt) by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    + (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
      rewrite (F_malloc_entry.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
      apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
      rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
    + rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
      apply evt_done. deexists 2. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End HALVE.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L15042952629.4L1718820729.6 L6755884809.6 000001007008SS1n2NES". (* [comment removed for export] *)
#[using="Type"] Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
  intros H.
  assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|NE].
    - change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
    - replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
      rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
  rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L2043847691.42 L24946289669.44L25853701207.43L27811077419.44L31767182813.44L32173087313.49L41349968239.44L41354132621.43L41415987435.45L41418133777.43L45727963655.56L5045218403.44 L5331805151.44 L53817072791.45L53817093936.47L59308533096.40L66605058182.56L6758062595.44 L8471139760.47 00000300B00P00`00o01901G01U01\01c02=02K02Y02c02m03503O03V03]S1FS5usage1F3cnt1KS1F3cnt2CR3C32S5usage2UR1F3cntS5usage1F3cnt1KS1F3cnt2C2S1F3cnt2CR3C32S1F3cnt2CR3C32S1F3cntS1F3cntS1F3cnt2CR1r3EVm1q2HS2C21HS1F3cnt2CR3C32S1F3cnt2CR3C32S1F3cnt2CRS1F3cnt2CRS3cnt2CRS1F3cnt2CR3C321r3EVm1q1n1HS1F3cntS1F3cnt". (* [comment removed for export] *)
#[using="UR"] Lemma rhalve_even_loop : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "PF,$18.Pcnt,$2.Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PFr,(19.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(5.(6.+2.R1?.)(7.R1?.(1:.+2.(1;.R20.))))P,(6.R20.+20.)P,(8.$25.(26.R21.)$27.)P,(3.$4.R4.)(1<.$4.Lms',$1=.(1>.(0.&40.)La3',(0.&40.)(1>.(0.&40.)La4',(0.&40.)(8.$1=.R3.(1?.(28.Vusage,Vsize,R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(17.(29.R27.R26.Vusage,))R2.R1.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R:.(22.&40.+40;68.)R9.(23.(0.&40.))R8.(24.$4.)))))(1?.(28.Vusage,Vsize,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(17.R23.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R7.(22.&40.+40;40.)R6.(23.(0.&40.))R5.(24.$4.)))")
(* [comment removed for export] *).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
  - change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
  - cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
    assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
    + (* [comment removed for export] *)
      replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
      step. apply evt_done. deexists 2. reflexivity.
    + replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned cnt) by lia. rewrite (F_malloc_entry.srliw_small cnt 1) by lia.
      step. rewrite (wz_unsigned cnt) by lia. step.
      assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * (* [comment removed for export] *)
        assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
        assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
        { rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
        change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
        apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
      * (* [comment removed for export] *)
        step.
        assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
        replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
        apply evt_done. deexists 2. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L39049578461.43L41352163945.40L52520436111.41L58940969005.4300000;00I00L00ZS1F3cnt3C32S1F3cnt2CR3C32S1FS1F3cnt2CR3NE1". (* [comment removed for export] *)
#[using="UR"] Lemma rhalve_even_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "PF,$18.Pcnt,$2.Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PFr,(19.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(5.(6.+1.R1?.)(7.R1?.(1:.+2.(1;.R20.))))P,(6.R20.+20.)P,(3.$4.R3.)(1<.$4.Lms',$1=.(1>.(0.&40.)La3',(0.&40.)(1>.(0.&40.)La4',(0.&40.)(8.$1=.R3.(1?.(28.Vusage,Vsize,R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.(17.(29.R26.R25.Vusage,))R2.R1.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(22.&40.+40;68.)R8.(23.(0.&40.))R7.(24.$4.)))))(1?.(28.Vusage,Vsize,R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(17.R22.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(22.&40.+40;38.)R5.(23.(0.&40.))R4.(24.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until m; intros CR C32 MI; unfold rcnt_regs.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt) by lia.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
  - (* [comment removed for export] *)
    assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
    replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
    step. step. apply evt_done. deexists 2. reflexivity.
  - assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
    destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
    apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End HALVE2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L13227725593.13L30363033283.15L5208631479.13 L5208631604.12 L52352673314.14L52352673443.13L52930602171.12L52930602296.13L58139561083.12L5818568920.13 L5818569051.12 L59654440132.12L59654440263.13L61222816495.12L61222816620.13L61703251183.13L66053841170.14L66053841299.13L67212774306.14L8197809883.12 L8197810008.13 L8433447544.12 L8433447931.13 00000F00b01801901O01P01c02602L02_03203303I03a04904T04j04k05A05T05g05h06>S2st2sc1u4size4cnt02MCS2st2sc1u4size4cnt02MC2H12H2S2st2sc1u4size4cnt02H1FS2st2sc1u4size4cnt02H2FS2st2sc1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt02H0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0FS2st2sc1u4size4cnt02H1S2st2sc2SC1u4size4cnt01HS2st2sc2SC1u4size4cnt01HS2st2sc2SC1u4size4cnt01H2H1S2st2sc1u4size4cnt02H2FS2st2sc1u4size4cnt02H1S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0FS2st2sc1u4size4cnt02H1". (* [comment removed for export] *)
#[using="SC"] Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
      first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
  - pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L10312311201.43L11408186381.47L11883503445.47L13224913845.45L16203303697.46L18397739387.46L1847287747.46 L20050800344.47L21117097293.42L21121176574.42L22531929780.48L25519559788.46L2688827061.47 L2688827190.46 L32886413064.45L35759278399.41L35907686401.47L35907686786.46L36598523691.41L37609598733.43L40823334348.40L41046672482.46L41415828300.45L41415942734.46L47699263254.42L49182423289.47L5002755470.46 L52928847408.42L52930962873.45L53810874150.41L56096478626.46L58137392857.43L58139496190.42L5818585435.46 L5818995035.43 L58829209207.46L60015582180.40L61220909156.42L61222865647.46L61222865772.47L61222980335.43L61222980460.44L61222980589.45L61803412289.45L7443261284.43 L8197793624.47 L8198170456.44 L8243212024.43 00000G00]01001G01Z02002K02a03603K03^04504K04a05705J05Q05X05n06E06X06n07A07T07g08=08S08f09909N09d0::0:P0:c0;60;Q0;h0<@0<X0=00=H0=`0>80>N0>d0?70?J0?aS2st2sc1u4size4cnt03MCRS2st2sc1u4size4cnt02K1S2st2sc1u4size4cnt0S2st2sc1u4size4cnt03MCRS2st2sc1u4size4cnt0S2st2sc1u4size4cnt02R1S2st2sc1u4size4cnt03MCR3HERS2st2sc1u4size4cnt02R2S2st2sc1u4size4cnt01KS2st2sc1u4size4cnt01KS2st2sc1u4size4cnt0S2st2sc1u4size4cnt03SZRS2st2sc2UR1u4size4cnt0S2st2sc2UR1u4size4cnt0S2st2sc1u4size4cnt02R0S2st2sc1u4size4cnt0S2sc2R1S2sc2R0S2st2sc2SC1u4size4cnt0S2st2sc1u4size4cnt03MCRS2st2sc1u4size4cnt0S2st2sc1u4size4cnt02K0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt02K1S2st2sc1u4size4cnt02K0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt01KS2st2sc1u4size4cnt02R1S2st2sc1u4size4cnt02L3S2st2sc1u4size4cnt02L3S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt03MCR3HERS2st2sc1u4size4cnt03SZRS2st2sc2SC1u4size4cnt01KS2st2sc2SC1u4size4cnt01KS2st2sc2SC1u4size4cnt01KS2st2sc2SC1u4size4cnt01KS2st2sc2SC1u4size4cnt01KS2st2sc2SC1u4size4cnt01KS2st2sc1u4size4cnt02R0S2st2sc2SC1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt0S2st2sc1u4size4cnt03MCR". (* [comment removed for export] *)
#[using="hRP MR SC UR"] Lemma rcount_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W11 ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pgmw,(0.&40.)Prqw,(0.&40.)PFr,(19.&5.(0.&40.))Pfc,(0.&20.)P,(3.$4.Vm,)(1<.$4.Lms',$1=.(1>.(0.&40.)La2',(0.&40.)(1>.(0.&40.)La3',(0.&40.)(1>.(0.&40.)La4',(0.&40.)(8.$1=.R4.(1?.(28.Vu,Vsize,R:.R1?.R1>.R1=.R1<.R1;.R1:.(22.&40.Vsc,)R9.R3.R2.R1.R14.R13.R12.R8.(17.Vcnt0,)(22.&40.$2:.)R11.(22.&40.$2;.)(22.&40.(<.$2;.(>.+8.Vsc,)))(22.&40.$2<.)R10.R?.R>.R=.R<.R;.)R7.(22.&40.+40;7<.)R6.(23.(0.&40.))Vm,(24.$4.))))))(1?.(16.R6.R1;.R1:.R19.R18.R17.R16.(22.&40.Vsc,)R5.R15.R14.R13.R12.R11.R10.R?.R>.R4.(22.&40.(>.Vsc,+2.))(22.&40.$2:.)R=.(22.&40.$2;.)(22.&40.(<.$2;.(>.+8.Vsc,)))(17.(2=.Vsc,))(22.&40.$2<.)R<.R;.R:.R9.R8.R7.)R3.(22.&40.+40:=<.)R2.(23.(0.&40.))Vm,(24.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until fc. intros MI.
  pose proof (size_class_range sc SC) as SZR.
  dpose MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
  pose proof rcnt0_range as C0R.
  unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read st m sc (wa (512968 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
  step. clear RDU.
  (* [comment removed for export] *)
  step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
  - (* [comment removed for export] *)
    apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
    step. clear RDM. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a3' & a4' & ->)). unfold rcnt_regs.
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
    eapply evt_mono.
    { eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a2'' & a3'' & ->)). unfold rcnt_regs. deexists 3. reflexivity.
  - (* [comment removed for export] *)
    assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
    unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
    pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
    replace (wa (94556 + 3 * sc + 0)) with (Z_to_bv 64 (94556 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
    step. clear RD0. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
    { replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. deexists 3. reflexivity. }
    replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
    replace (wa (94556 + 3 * sc + 1)) with (Z_to_bv 64 (94556 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
    step. clear RD1. rewrite zxb_b8 by lia.
    step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
    { replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. deexists 3. reflexivity. }
    replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
    replace (wa (94556 + 3 * sc + 2)) with (Z_to_bv 64 (94556 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
    step. clear RD2. rewrite zxb_b8 by lia. step.
    apply evt_done. deexists 3. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End COUNT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L13721704148.44L15095956317.45L15524707335.45L15524707335.46L16637396593.44L16639408463.43L34019513447.44L42275237624.46L52520452874.45L53512866218.45L55813860202.46L58286658260.44L59301978119.45L59577143601.44L59579457969.42L62357396789.44L63463648957.45L65102387343.45L65104205973.42L65106487317.44L799247169.44  00000@00S00a01001C01V01h02;02K02[02n03>03R03b04204D04W04j05=05P05cS4size4cnt04cnt1S4size4cnt04cnt12K3S4size4cnt02PRS4size4cnt13PR1S4size4cnt02C04cnt1S4size4cnt02C04cnt1S4size4cnt04cnt11HS4size4cnt04cnt12K3S4size4cnt04cnt1S4size4cnt04cnt1S4size4cnt04cnt12K3S4size4cnt04cnt1S4size4cnt04cnt13C1RS4size4cnt04cnt1S4size4cnt04cnt1S4size4cnt04cnt11HS4size4cnt04cnt12K3S4size4cnt02SZ4cnt1S4size4cnt02SZ4cnt1S4size4cnt02SZ4cnt1S4size4cnt02SZ4cnt1". (* [comment removed for export] *)
#[using="SZ C0"] Lemma rcnt2_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 (if big then 0x40ba4 else 0x40be8)) fc None m (seg_rom rsegs))
    (MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x40b7c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI. unfold rcnt_regs.
  assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
  pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
  assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite ?unsigned_lit by lia. step. step.
    assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
    { unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
      destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
    assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
    { rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
      destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
    rewrite EV. clear EV.
    assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CNT2.

End RP_1.
