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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W11 ASlot_W15 ASlot_W16.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_W11.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W16 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.snd"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.fst"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.MMC.rmmc_post"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W16.mm_final"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.b2z"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W16.mm_cnt_red"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.usage"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W16.mm_usage1"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"].


Section RP_1. Context {hRP : run_params}.
Section MMC.
Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

(* [comment removed for export] *)
Definition rmmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (res : Z * Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W16 ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3',(2.&40.)(1.(2.&40.)La4',(2.&40.)(1.(2.&40.)La5',(2.&40.)(1.(2.&40.)La6',(2.&40.)(1.(2.&40.)La7',(2.&40.)(3.$0.R:.(4.(5.O18.O17.O16.O15.R9.O14.O13.O12.O11.R8.R7.R6.R5.R4.R3.R2.R1.O10.(6.(7.$8.$8.O1.))O?.O>.O=.O<.O;.(6.(9.$8.$8.O1.))O:.O9.O8.O7.O6.O5.)O4.(:.&40.+40?68.)O3.(;.(2.&40.))O2.(<.$=.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L11050471323.52L17968254384.40L19327076934.51L21201477243.42L22443028540.51L22530010272.48L23116422888.43L23425306160.49L24348510615.46L24348511260.51L24348572732.40L24928536178.45L27559289300.46L32276268065.49L33218088287.52L34115541399.46L34288582456.51L43592928594.40L4908146733.50 L4908146860.51 L59576979761.50L59848437869.46L60975110840.52L61874654742.46L64691766506.50L65106401460.40L6755968444.51 L6831360076.50 L7164927098.52 L799017793.50  00000K00X01401E01]02502E02^02n03F03M03]03m04B04R04f05>05G05X05i06>06O06j07:07R07[08008H08c09;S4size3req2c12u12UR3nd03rq'S4size2c13SCRS4size3req2SZ2c13SCR3nd03rq'S4size2c13SCR3nd0S4size3req2c13nd03rq'2K2S4size3req2RQ2c13nd03rq'S4size2c13nd02RUS4size3req2c13nd03rq'3RU2S4size2c12CR3nd0S4size3req2c12CR3nd03rq'S2c12CRS4size2c13nd02KNS4size2c13nd02K7S4size3req2c13nd03rq'S4size2SZ2c13SCRS4size3req2RQ2c13nd0S4size3req2c13nd03rq'2K2S4size2c1S3req2RQ3rq'4RUR2S3req2RQ3rq'4RUR2S4size3req2c13nd03rq'S4size3req2c13nd0S4size3req2c12u13nd03rq'2K3S4size2c13nd02K7S4size3req2c13nd03rq'2K1S4size2SZS4size3req2c13nd03rq'S4size3req2c13nd03rq'2K1S4size3req2c12u13nd03rq'2K3S4size3req2SZ2c13nd03rq'". (* [comment removed for export] *)
#[using="SZ RQ"] Lemma rj2c_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W16 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(>.&5.(2.&40.))Pfc,(2.&20.)Pm,$?.Pc1,$8.Pu1,$8.P,(10.(11.+1.R2.)(11.R2.+20.))P,(10.(11.=R2.)(12.R2.(13.+2.+3=.)))(14.$=.(15.R1>.R1=.R1<.R1;.R19.R18.(:.&40.Vsc,)R17.(:.&40.Vreq,)R11.R10.R?.R>.(6.Vsize,)R=.R<.R;.R:.R9.R8.R7.R6.R5.(16.Vsize,Vreq,R3.R4.Vnos,))(4.(5.R1>.R1=.R1<.R1;.R1:.R19.R18.(:.&40.Vsc,)R17.(6.R3.)(6.+1000.)(6.(17.Vsize,+10.))(:.&40.(18.Vnos,))R16.R15.R14.R13.(:.&40.Vreq,)R12.R11.R10.R?.R>.(6.Vsize,)(6.R4.)R=.R<.R;.R:.R9.R8.)R7.(:.&40.+40?0<.)R6.(;.(2.&40.))R5.(<.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * c1 < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR.
  unfold rmmc_post.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
  step. step. step. step. step. step.
  rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
  replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
  set (nd0 := round_up_pg (size * c1 + 16)).
  pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
  replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
  fold nd0 in RUR.
  assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
  { unfold mm_final, UNIT. reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
    deexists 9. reflexivity. }
  replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.
  (* [comment removed for export] *)
  step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    deexists 9. reflexivity. }
  replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
  replace (-20 + - req) with (- (req + 20)) by lia.
  set (rq' := round_up_pg (req + 20)).
  pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
  replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
  assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
  { unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
  rewrite ES in EF. clear ES. unfold PGSZ in EF. 
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
    step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
    step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
      deexists 9. reflexivity.
    + replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
      step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
      * (* [comment removed for export] *)
        step. step. step.
        apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
        deexists 9. reflexivity.
      * apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
        deexists 9. reflexivity.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
    step. step. step.
    apply evt_done. rewrite EF. cbn [fst snd]. deexists 9. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L10850062390.47L10850062644.53L11012146704.50L11050483385.42L22210772400.47L24928536178.43L32778357954.44L35168380004.47L35168380133.49L35914946408.41L36405705922.49L39715007009.46L41354137306.41L41418056518.41L42721829156.48L46044038027.42L47816254902.50L47816369713.51L47816371237.50L47816371237.53L47816371495.47L47816371495.48L48590145450.50L5047312761.42 L50812361234.51L55547690234.50L55715170566.49L55715170566.52L55715170695.48L55715170816.47L55715170945.46L58029163584.51L59308518135.50L59308630497.48L59308630759.49L59308630759.52L59308630884.50L59308630884.53L59576985984.47L59576986119.48L59576986373.50L59577147792.45L7441034468.45 L9871845494.48 00000=00J00Q00X00b00f01101>01Z01k02;02B02J02K02X02c03103?03M03[03i04704A04R04_04l04m04n04o05005105>05B05F05J05]06<06L06M06N06O06P06W06dS4size3cnt2KCS4size3cnt2LTS2sc2E0S2u12URS2sc2KA2KBS2KNS3cnt2u12KUS4size3cnt2KCS2sc4size3cnt2L32KA2KB2NC2KDS4size2SZ3cnt3SCRS2sc2L32KA2KB2KDS2sc2KAS3cnt2CRSS4size3cnt2KCS3cnt2u12KUS4size3cnt3SCRS4size3cnt3SCRS4size3cnt3SCRS4size3cnt3SCRS4size3cnt3SCRS4size3cnt3SCRS2sc2L32A1S4size2SZ3cnt3SCRS4size3cnt2KQS4size3cnt2LTSSSSSS4size3cnt2KQS2KCS2KBS2KDS2sc2L32KA2KB2A12KDS2sc4size3cnt2L32KA2KB2NC2KD2KES4size3cnt2LT2KESSSSS2sc2SCS4size3cnt2KC". (* [comment removed for export] *)
#[using="SC SZ"] Lemma rred_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W16 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(19.(2.&8.))Pcnt,$8.Pu1,$8.P,(10.(11.+1.R2.)(11.R2.+20.))P,(10.(11.=R2.)(12.R2.(13.+2.+3=.)))(14.$=.Lms',$0.(1.(2.&40.)La5',(2.&40.)(1.(2.&40.)La6',(2.&40.)(1.(2.&40.)La7',(2.&40.)(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Ls3',(2.&40.)(3.$0.R6.(4.(5.R23.R22.R21.R20.R2.R1>.R1=.(:.&40.Vsc,)R1<.(6.R9.)(6.+1000.)(6.(17.Vsize,+10.))(:.&40.(18.Vnos,))(6.(1:.Vsize,R:.))R5.R4.R3.(:.&40.Vreq,)R1.R18.R17.R16.R15.(6.Vsize,)(6.(1;.Vsc,Vsize,R:.R9.Vnos,))R13.R12.R11.R10.R?.R>.)R=.(:.&40.+40?0<.)R<.(;.(2.&40.))R;.(<.$=.))))))))(4.(5.R1=.R1<.R1;.R1:.R19.R18.R17.(:.&40.Vsc,)R16.(6.R3.)(6.+1000.)(6.(17.Vsize,+10.))(:.&40.(18.Vnos,))(6.(1:.Vsize,R4.))R15.R14.R13.(:.&40.Vreq,)(6.R4.)R12.R11.R10.R?.(6.Vsize,)R>.R=.R<.R;.R:.R9.R8.)R7.(:.&40.+40>98.)R6.(;.(2.&40.))R5.(<.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * cnt < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR. pose proof (ASlot_W16.land3_range sc) as L3.
  (* [comment removed for export] *)
  assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
    evt rsegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x40f0c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
             (Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40f08) fc None m (seg_rom rsegs))).
  { intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. deexists 5. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
  step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
  { eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
    rewrite Bool.andb_false_r. reflexivity. }
  assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
  assert (ER : mm_cnt_red sc size cnt u1 nos =
    (if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
     else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
     else cnt)).
  { unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold PGSZ in ER.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
  step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
  - (* [comment removed for export] *)
    replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
    step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
    + (* [comment removed for export] *)
      replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
      (* [comment removed for export] *)
      step. step. step.
      step. if_cases KC; zify_cond KC.
      * (* [comment removed for export] *)
        rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
        destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
        assert (E0 : Z.land sc 3 = 0) by lia.
        step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
        apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        deexists 5. reflexivity.
      * (* [comment removed for export] *)
        assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
        { intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
          replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
          replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
        clear KC. step. step.
        step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
        { (* [comment removed for export] *)
          apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
          deexists 5. reflexivity. }
        rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
        replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).
        (* [comment removed for export] *)
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
        step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
        step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
        -- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        -- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + (* [comment removed for export] *)
      rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
      step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
      step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
      * (* [comment removed for export] *)
        replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
        step. step. step.
        step. if_cases KG; zify_cond KG.
        { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
        clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
        apply evt_done. rewrite ER. deexists 5. reflexivity.
      * (* [comment removed for export] *)
        step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        deexists 5. reflexivity.
  - (* [comment removed for export] *)
    rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
    step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
    + (* [comment removed for export] *)
      replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
      step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
      step. step. step.
      step. if_cases KG; zify_cond KG.
      { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
      clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
      apply evt_done. rewrite ER. deexists 5. reflexivity.
    + (* [comment removed for export] *)
      step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      deexists 5. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L10248276741.43L13399868103.48L13950189401.45L1490232912.48 L16902063965.47L19344636060.48L20389440212.48L3280910006.45 L52514148243.46L60779133373.45L6753375772.43 L7447421819.45 00000700=00>00E00N00R00]00c00d00k00l013S2sc2SCS2sc1KSS2u02URS2sc2SC1KS2scS2sc2st3U1RS2sc1KSS2sc2SCSS2sc2SC". (* [comment removed for export] *)
#[using="SC"] Lemma rusage1_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W16 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(>.&5.(2.&40.))Pfc,(2.&20.)Pst,$1<.Pm,P,(2.&40.)(19.(2.&8.))Pu0,$8.P,(1=.VhRP,R3.R2.)P,(10.(11.=R2.)(12.R2.(13.+2.+3<.)))P,Pi,$8.(10.(11.=(1>.R6.R1.))(12.(1>.R6.R1.)(13.+2.+3<.)))(14.$=.Lms',$0.(1.(2.&40.)La5',(2.&40.)(3.$0.R2.(4.(5.R25.R24.R23.R22.R21.R20.R1?.(:.&40.Vsc,)R1>.(6.(1?.R8.Vsc,R6.))R1=.R1<.R1;.R1:.R1.R19.R18.R17.R16.R15.R14.R13.(:.&40.(17.$20.(1:.+8.Vsc,)))R12.R11.R10.R?.R>.R=.R<.R;.)R:.(:.&40.+40>98.)R9.(;.(2.&40.))R7.(<.$=.))))(4.(5.R23.R22.R21.R20.R1?.R1>.R1=.(:.&40.Vsc,)R1<.(6.R4.)R1;.R1:.R19.R18.(:.&40.+1?.)R17.R16.R15.R14.R13.R12.R11.(:.&40.(17.$20.(1:.+8.Vsc,)))R10.R?.R>.R=.R<.R;.R:.R9.)R8.(:.&40.+40>84.)R7.(;.(2.&40.))R5.(<.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until u0. intros MR UR USR. unfold RMLOCK, RCTX in *.
  pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
  { apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
    eexists. reflexivity. }
  apply Z.ltb_ge in K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia.
  step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
  { (* [comment removed for export] *)
    assert (ODD : Z.even sc = false).
    { rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
    apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
  assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read st m (sc + 1) (wa (512968 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
  replace (wa (512968 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (512960 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
  pose proof (USR (sc + 1)) as U1R.
  step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
  apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L22681454062.44L36418884054.38L45351629614.44L64673684378.38L67512800846.44L9839304622.44 00000100@00A00H00P00QSS2sc2st2u02UR1HSS2u02URS3cnt2CRS". (* [comment removed for export] *)
#[using="SC SZ RQ"] Lemma rmmc_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W16 ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(>.&5.(2.&40.))Pfc,(2.&20.)Pst,$1<.Pm,P,(2.&40.)(19.(2.&8.))Pcnt,$8.Pu0,$8.P,(1=.VhRP,R4.R3.)P,(10.(11.+1.R3.)(11.R3.+20.))P,(10.(11.=R3.)(12.R3.(13.+2.+3<.)))P,Pi,$8.(10.(11.=(1>.R8.R1.))(12.(1>.R8.R1.)(13.+2.+3<.)))(14.$=.(15.R1=.R1<.R1;.R1:.R18.R17.(:.&40.Vsc,)R16.(:.&40.Vreq,)R13.R12.(:.&40.$20.)(:.&40.(17.$20.(1:.+8.Vsc,)))(6.Vsize,)R10.R?.R>.R=.R<.R;.R:.R9.R7.(16.Vsize,Vreq,(1?.R8.Vsc,R5.)(1;.Vsc,Vsize,R6.(1?.R8.Vsc,R5.)Vnos,)Vnos,))(4.(5.R1=.R1<.R1;.R1:.R19.R18.R17.(:.&40.Vsc,)R16.(6.R5.)(6.+1000.)(6.(17.Vsize,+10.))(:.&40.(18.Vnos,))(6.(1:.Vsize,R6.))(:.&40.+1?.)R15.R14.(:.&40.Vreq,)(6.R6.)R13.R12.(:.&40.$20.)(:.&40.(17.$20.(1:.+8.Vsc,)))(6.Vsize,)R11.R10.R?.R>.R=.R<.R;.)R:.(:.&40.+40>84.)R9.(;.(2.&40.))R7.(<.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until u0. intros MR CR UR USR.
  assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
  { unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
  eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
  cbv beta. intros ms' (a5' & ->).
  eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
  cbv beta. (intros ms'' dd_H; ddestruct dd_H as (a5'' & a6'' & a7'' & t0'' & s3'' & ->)).
  assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
  { unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
  eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
  cbv beta. unfold rmmc_post. (intros ms3 dd_H; ddestruct dd_H as (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->)).
  deexists 9. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MMC.

End RP_1.
