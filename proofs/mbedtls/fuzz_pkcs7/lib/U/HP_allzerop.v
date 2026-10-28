(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RF_get_meta.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog MallocBlocks MallocHINV MallocFacts_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MI_Inv MI_Arith MI_Read MI_WFree MallocFacts_inv MallocFacts_inv2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMalloc_iface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_allzerop () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.iff"; "Corelib.Init.Logic.not"; "RP_1.allzero_val"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_maplen"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.undersized"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le2"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rallzerop_post"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.land"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.g_meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area_of"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_check"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_secret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freeable"; "RP_1.rallzerop_entry"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.bptr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.RHEAP"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_slots"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"].


Section RP_1. Context {hRP : run_params}.
Definition rallzerop_entry : Z := 0x412cc.

(* [comment removed for export] *)
Definition allzero_val (last_idx sc maplen : Z) : Z :=
  if 48 <=? sc then 1
  else if negb (maplen =? 0) && (last_idx =? 0) then (if maplen * 4096 - 16 <? 16 * size_class sc then 1 else 0)
  else 0.

Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L20386483684.6 L34333409566.10L37245632603.9 L44613148007.9 L44615246044.5 L67257976147.1000000900@00L00M00N00XS2mr1H2H'S2mr2H1S2mr1H2H12H0SSS2mr2H02H1". (* [comment removed for export] *)
#[using="hRP"] Lemma allzero_val_undersized mr : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "P,(0.(1.(2.=(3.O1.))(4.(3.O1.)+30.))(5.$6.(3.O1.)+3?.))(7.(8.(5.$6.(9.(:.O1.)(3.O1.)(;.O1.))=))(<.O1.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros SC. unfold allzero_val, undersized, get_stride, UNIT.
  destruct (Z.leb_spec 48 (m_sizeclass mr)).
  - split; [intros _ H'; lia| intros _; lia].
  - destruct (Z.eqb_spec (m_maplen mr) 0); destruct (Z.eqb_spec (m_last_idx mr) 0); cbn [negb andb];
      try (destruct (Z.ltb_spec (m_maplen mr * 4096 - 16) (16 * size_class (m_sizeclass mr)))); split; intros; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11757038953.5L46992856201.5000001002SS". (* [comment removed for export] *)
#[using="hRP"] Lemma allzero_val_range a b c : 0 <= allzero_val a b c <= 1.
Proof. rceilb. unfold allzero_val. destruct (48 <=? b); [lia|]. destruct (negb (c =? 0) && (a =? 0))%bool; [| lia]. destruct (c * 4096 - 16 <? 16 * size_class b); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition rallzerop_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 : word) (z : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Lms',$=.(>.(?.&40.)La1,(?.&40.)(>.(?.&40.)La2,(?.&40.)(>.(?.&40.)La3,(?.&40.)(>.(?.&40.)La4,(?.&40.)(>.(?.&40.)La5,(?.&40.)(>.(?.&40.)La6,(?.&40.)(5.$=.R7.(10.(11.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.(12.O4.)R6.R5.R4.R3.R2.R1.O5.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O3.(13.O1<.)O2.(14.(?.&40.))O1.(15.$16.)))))))))")
(* [comment removed for export] *).


Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L17803090418.6L17803238521.5L18926749479.4L26124096872.7L41422216306.600000300600700C00FS1aS1aSS1a2Ha1E1L1HS1a". (* [comment removed for export] *)
#[using="hRP"] Lemma land_3072 a : 0 <= a -> Z.land a 3072 = 1024 * ((a / 1024) mod 4).
Proof. rceilb.
  intros Ha. pose proof (Z.div_mod (Z.land a 3072) 1024 ltac:(lia)) as E.
  assert (L : (Z.land a 3072) mod 1024 = 0).
  { change 1024 with (2^10). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land 3072 (Z.ones 10)) with 0. apply Z.land_0_r. }
  assert (H : (Z.land a 3072) / 1024 = (a / 1024) mod 4).
  { change 1024 with (2^10) at 1. rewrite <- Z.shiftr_div_pow2, Z.shiftr_land by lia. rewrite Z.shiftr_div_pow2 by lia.
    change (Z.shiftr 3072 10) with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. }
  lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L32508646054.39L42790217749.40L44310621309.38L60013227756.40L6755554843.38 L7440756579.38 00000700>00B00I00J00QS2sc2SCS2sc2SZS2scS2sc2SZSS2sc2SC". (* [comment removed for export] *)
#[using="hRP"] Lemma rallzerop_ret0 : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(17.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(18.(?.&8.))Psc,$6.P,(1.(2.=R1.)(4.R1.+30.))P,(5.(18.(19.(?.&8.)))(1:.$16.R3.(1;.(1<.$1=.(1>.+2.R2.)))#2.)(1?.(19.(?.&8.))(20.(12.(21.R2.)))))(22.$16.(23.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R15.=R6.R5.R4.)(10.(11.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(24.&40.R3.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(24.&40.+41424.)R5.(14.(?.&40.))R4.(15.$16.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until sc. intros SC RS.
  st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
  assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (94460 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (94460 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
  pose proof (size_class_range sc ltac:(lia)) as SZ. st1. st1. st1.
  rewrite v_sltu_b2z, Z.ltb_irrefl. cbn [Z.b2z].
  st1. unfold rallzerop_post. finish.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L12415417473.51L16631481304.56L24120772675.46L24928565580.56L30175591391.54L30528612238.53L31956327793.66L32506700093.50L32506700474.51L32508646054.52L34881310438.48L34882993888.53L3523546895.54 L35937019556.56L40823231959.54L42790217749.53L44310207581.51L46242125712.50L5073687095.51 L53219017336.53L53219325399.45L60015684607.54L61264199136.56L6755968571.51 L7441129283.51 L754578955.44  L8927165467.54 L8929574535.42 00000_01G01N02102Z03N04U05@05k06V07>08208a09D09g0:M0;00;>0;N0<40<Z0=@0=h0>K0?10?W0@C0@lS8last_idx8freeable2sc6maplen5mword2LI2ML2K22K3S8last_idx8freeable2sc6maplen5mword1H2H0S2sc2SCS8last_idx8freeable2sc6maplen5mwordS8last_idx8freeable2sc6maplen5mword2ML2K2S8last_idx8freeable2sc6maplen5mword5Hsc631q1K1r1H2H0S8last_idx8freeable2sc6maplen2FB2SC2ML2q01K3AZ02K22K31q1r1H2H02r02H42H5S8last_idx8freeable2sc6maplen5mword2SC4SC48S8last_idx8freeable2sc6maplen5mword2SC4SC48S8last_idx8freeable2sc6maplen5mword2SC4SC48S8last_idx8freeable2sc6maplen5mword4SC48S8last_idx8freeable2sc6maplen5mword5Hsc631q1K1r1H2H0S8last_idx8freeable2sc6maplen5mword2SC2ML2MW2K2S8last_idx8freeable2sc6maplen5mwordS8last_idx8freeable2sc6maplen5mwordS8last_idx8freeable2sc6maplen5mword2SZS8last_idx8freeable2sc6maplen5mwordS2sc6maplen2MLS8last_idx2sc2LIS8last_idx8freeable2sc6maplen5mword2MWS8last_idx8freeable2sc6maplen5mword2MWS8last_idx8freeable2sc6maplen5mword2SZS8last_idx8freeable2sc6maplen5mword1H2H0S8last_idx8freeable2sc6maplen5mwordS8last_idx8freeable2sc6maplen5mword2SCS8last_idx8freeable2sc6maplen5mword2MWS8last_idx8freeable2sc6maplen5mword2SC2MW2SZS8last_idx8freeable2sc6maplen2LI2FB2SC2ML". (* [comment removed for export] *)
#[using="hRP"] Lemma rallzerop_fin : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa1,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(17.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(18.(?.&8.))Plast_idx,$6.Pfreeable,$6.Psc,$6.Pmaplen,$6.Zmword,$6.(1<.(1<.(1<.R4.(1>.+20.R3.))(1>.+40.R2.))(1>.+1000.R1.))P,(1.(2.=R5.)(4.R5.+20.))P,(1.(2.=R5.)(4.R5.+2.))P,(1.(2.=R5.)(4.R5.+40.))P,(1.(2.=R5.)(4.R5.(25.+2.+28.)))P,P,(2.+30.R7.)(5.$6.R8.+3?.)P,P,(4.R8.+30.)(5.(18.(19.(?.&8.)))(1:.$16.R<.(1;.(1<.$1=.(1>.+2.R9.)))#2.)(1?.(19.(?.&8.))(20.(12.(21.R9.)))))(22.$16.(23.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R1=.(9.R;.R9.R8.)R>.R=.R<.)(10.(11.R29.R28.R27.R26.R25.R24.R23.R22.R21.(12.R7.)R20.(24.&40.R;.)(24.&40.R8.)(24.&40.R9.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(24.&40.+413=8.)R=.(14.(?.&40.))R<.(15.$16.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until maplen. intros mword LI FB SC ML Hsc63 RS.
  assert (MW : 0 <= mword < 2^64) by (subst mword; lia).
  assert (M3 : Z.land mword 3072 = 1024 * (sc / 16)).
  { rewrite land_3072 by lia. f_equal. subst mword. Z.div_mod_to_equations. nia. }
  (* [comment removed for export] *)
  st1. st1. st1. rewrite M3. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (SC48 : sc < 48) by (Z.div_mod_to_equations; lia). pose proof (RS SC48) as RS1.
    assert (AZ0 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
    st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + replace (allzero_val last_idx sc maplen) with 0 by (unfold allzero_val; rewrite AZ0, K2; reflexivity).
      apply rallzerop_ret0; [lia| exact RS1].
    + st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
      * replace (allzero_val last_idx sc maplen) with 0
          by (unfold allzero_val; rewrite AZ0; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); rewrite andb_false_r; reflexivity).
        apply rallzerop_ret0; [lia| exact RS1].
      * (* [comment removed for export] *)
        st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
        assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (94460 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
        { replace (Z_to_bv 64 (94460 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS1. }
        pose proof (size_class_range sc ltac:(lia)) as SZ. st1. st1. st1. rewrite land_pgmask by lia.
        assert (MPG : mword - mword mod 4096 = maplen * 4096) by (subst mword; Z.div_mod_to_equations; lia). rewrite MPG.
        st1. st1. st1. rewrite v_sltu_b2z. rewrite Z.shiftl_mul_pow2, !unsigned_lit by lia. change (2^4) with 16.
        match goal with |- context [Z.b2z ?c] => replace (Z.b2z c) with (allzero_val last_idx sc maplen) end.
        2:{ unfold allzero_val. rewrite AZ0, K3. replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb Z.eqb].
            destruct (Z.ltb_spec (maplen * 4096 - 16) (16 * size_class sc)); destruct (Z.ltb_spec (maplen * 4096 + -16) (size_class sc * 16)); cbn; lia. }
        st1. unfold rallzerop_post. finish.
  - (* [comment removed for export] *)
    assert (SC63 : sc = 63) by (apply Hsc63; Z.div_mod_to_equations; lia).
    st1. st1. replace (allzero_val last_idx sc maplen) with 1 by (unfold allzero_val; rewrite SC63; reflexivity).
    unfold rallzerop_post. finish.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L12500184402.46L17210420679.46L18926672477.46L35497698988.51L36181730567.46L46244227119.50L52067444116.51L53219325399.49L59308628433.51L63368267308.51L67992058172.46L68243864272.51L752481830.48  L8929574535.45 00000O00P00Q01401Q02703:03`04U05805@05m06S07<S8last_idx8freeable2sc2LI2FB2SCSSS8last_idx8freeable2sc6maplen5mwordS8last_idx8freeable2sc6maplenS2sc6maplen2ML8last_idx8freeable5mwordS5off168last_idx8freeable2sc6maplen5mword3O162LI2FB2SC2ML2MW3MW42K2S8last_idx8freeable2sc6maplen5mword2MWS5off168last_idx8freeable2sc6maplen5mword2ML3Hml1K2K2S8last_idx8freeable2sc6maplen5mwordS6maplenS5off168last_idx8freeable2sc6maplen5mword3O16S8last_idx8freeable2sc6maplen5mword2MWS8last_idx8freeable2sc6maplen2LI2FB2SC2ML". (* [comment removed for export] *)
#[using="hRP"] Lemma rallzerop_tail : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa3,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(17.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(18.(?.&8.))Poff16,$6.Plast_idx,$6.Pfreeable,$6.Psc,$6.Pmaplen,$6.Zmword,$6.(1<.(1<.(1<.R4.(1>.+20.R3.))(1>.+40.R2.))(1>.+1000.R1.))P,(1.(2.=R6.)(4.R6.+10000.))P,(1.(2.=R6.)(4.R6.+20.))P,(1.(2.=R6.)(4.R6.+2.))P,(1.(2.=R6.)(4.R6.+40.))P,(1.(2.=R6.)(4.R6.(25.+2.+28.)))P,P,(2.+30.R8.)(5.$6.R9.+3?.)P,P,(8.(5.$6.R8.=))(2.R=.(26.(1>.R9.+100.)+1.))P,P,(4.R:.+30.)(5.(18.(19.(?.&8.)))(1:.$16.R?.(1;.(1<.$1=.(1>.+2.R;.)))#2.)(1?.(19.(?.&8.))(20.(12.(21.R;.)))))(22.$16.(23.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R20.(9.R=.R;.R:.)R11.R10.R?.)(10.(11.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.(12.R9.)(12.R>.)(24.&40.R=.)R23.(24.&40.R;.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(24.&40.+413<0.)R10.(14.(?.&40.))R?.(15.$16.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until maplen. intros mword O16 LI FB SC ML Hsc63 Hml RS.
  assert (MW : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (M3 : Z.land mword 3072 = 1024 * (sc / 16)).
  { rewrite land_3072 by lia. f_equal. subst mword. Z.div_mod_to_equations. nia. }
  (* [comment removed for export] *)
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
  - apply rallzerop_fin; assumption.
  - st1. st1. st1. if_cases K2; zify_cond K2.
    + apply rallzerop_fin; assumption.
    + exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
      first [ rewrite Z.mod_small in K2 by lia
            | change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia; rewrite Z.mod_small in K2 by lia
            | idtac ]. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "01J0@L11113887407.92 L11447729958.116L11447729958.132L11601594822.103L12286795281.99 L12413379419.104L13743595831.89 L16073345020.102L16075458812.100L1848929278.95  L18975794542.92 L19053596038.104L20979070012.88 L21920755834.100L22069180487.104L22557358668.103L23073665222.90 L25983155196.88 L27380898049.98 L27417980796.88 L29131992245.104L29259535719.107L29315560028.84 L29317547131.93 L30528594179.106L3096926302.109 L31278981366.87 L31426263356.103L31647478602.102L32508646054.107L34391417.104   L34881310438.107L34883041389.106L3525623219.93  L38136276674.87 L40599920879.95 L40819006291.87 L40825300204.88 L40928706962.92 L41239403044.88 L41415942218.95 L42167987094.95 L42630527239.93 L42790217749.108L42861977286.104L43605390242.109L44015211434.95 L44312718427.107L45081116263.104L46609845873.92 L49712580022.95 L49712984728.108L5073687222.95  L53221409744.105L53221409745.94 L53250693504.88 L54466369468.105L5650221412.102 L56721643023.104L56862904998.103L57022143158.87 L59308628433.88 L59308628566.93 L59308628695.95 L59308629082.104L59308629336.107L59314923118.87 L5973109196.88  L60013227756.108L60015712838.109L60140672325.103L60700203023.87 L63152162437.85 L63348584395.103L63483924577.104L6636562324.100 L6638938260.102 L66688225592.103L6753457725.107 L68243864272.88 L6970102948.88  L7441127501.107 L7441127886.106 L7442853701.107 L8532563493.98  L8534580141.99  L8927055265.110 L8927110142.83  L8929151147.103 L9538464382.95  00000e00f00g01702202n03d04Z05P06F06b06c07i08e09W09j0;00<60=10>70>80?B0?m0@_0AT0BJ0CF0Ck0Dg0E_0E`0FU0GJ0Gk0H`0IV0JH0K:0Kf0Lf0MX0NS0O\0PQ0PR0Q?0R10Rc0SU0Se0T[0UQ0Uf0V\0WR0WS0WT0XO0XP0X`0YR0ZG0[X0\R0]N0^a0_l0_m0`b0aW0bC0bL0c=0d70d80dj0e\0fj0g\0hX0i]0j00jC0k80kn0ld0mQ0nW0oW10IS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2B3FFS1P1G2b33idx3GLOS1P1G2b35freed8last_idx8freeable2sc6maplen3idx5mword3GLO2FRS1P1G2b38last_idx8freeable2sc6maplen6secret3idx5mword3GLO2SES1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3GHIS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3SXIS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3SXIS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3IDXS1P1G2b38last_idx3idx3GLO2LIFS2a01P1G2b35off168last_idx8freeable2sc6maplen3idx5mword2HP3PLO3GLO3O16S1P1G2b35avail8last_idx8freeable2sc6maplen3idx5mword3GLO3SXAS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b32sc3idx3GLOS2a01P1G2b35off168last_idx8freeable2sc6maplen3idx5mword2HP3PLO3GLO3O16S2a01P1G2b35off168last_idx8freeable2sc6maplen3idx5mword2HP3PLO3GLO3O16S1P1G2b35avail8last_idx8freeable2sc6maplen3idx5mword3GLO2AVS2a01P1G2b35off168last_idx8freeable2sc6maplen3idx5mword2HP3PLO3GLO3O16FS1P1G2b35off168last_idx8freeable2sc6maplen3idx5mword3PLO3GLO3O162SC3IDX2K9S1P1G8last_idx8freeable2sc6maplen5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2K8S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3IDXS1P1G2b35off168last_idx8freeable2sc6maplen3idx5mword3GLO3O16S1P1G2b38last_idx8freeable2sc3idx3GLOS1P1G2b35freed8last_idx8freeable2sc6maplen3idx5mword3GLO3SXFS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2SC2K8FS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2K8S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2K8S2a01P1G5off162HP3PLO3PHI3GLO3O16S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2B3S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3IDXS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx3GLOS1P1G2b35off168last_idx8freeable2sc6maplen3idx5mword3PLO3GLO3O16S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b35avail8last_idx8freeable2sc6maplen3idx5mword3GLO2AVS1P1G1B2b35off168last_idx8freeable2sc6maplen3idx5mword3PLO3PHI2HB3GLO3O16S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2SZFS1P1G5off162sc3idx3PLO3PHI3GLO3O163Hsc3IDX2SZS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b33idx3GLOS1P1G3idx3GLO3IDX2b38last_idx8freeable2sc6maplen5mwordS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3IDXS1P1G8last_idx3GLO2LIS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3MWRS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3MWRFFS1P1G2b35freed8last_idx8freeable2sc6maplen3idx5mword3GLO2FRFS1P1G2b33idx3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2K2S2a01P1G1B2b35off168last_idx8freeable2sc6maplen3idx5mword2HP2AL3PLO2HB3GLO3O162K3S1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO4Hidx2K4S1P1G2b38last_idx8freeable2sc6maplen6secret3idx5mword3GLO2K7S1P1G2b35off168last_idx8freeable2sc6maplen3idx5mword2AL3PLO3GLO3O162SC5Hsc633IDX2K9S2a01P1G2b35off168last_idx8freeable2sc6maplen3idx5mword2HP2AL3PLO3GLO3O161KFS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2SZS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2SZS1P1G2b38last_idx8freeable2sc6maplen3idx3GLOS1P1G3GLOS1P1G2b38last_idx8freeable2sc6maplen5mword3GLO2B3S1P1G2b35off168last_idx8freeable3idx3PLO3GLO3O162LI2FB3IDXFS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b35off168last_idx8freeable2sc6maplen3idx5mword3PLO3GLO3GHI2gw3O163IDX2HGS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLOS1P1G2b35off168last_idx8freeable2sc6maplen3idx5mword3GLO3O16S1P1G1B2b35off168last_idx8freeable2sc6maplen3idx5mword3PLO2HB3GLO3O16S1P1G2sc3idx3GLO2SCS1P1G2sc3idx3GLO2SCS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO2SCS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3IDXS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO3IDXS1P1G5off162sc3idx3PLO3PHI3GLO3O163Hsc3IDX2SZS1P1G2b35off168last_idx8freeable2sc6maplen3idx3PLO3GLO3O162LI2FB2SC2MLS1P1G2b35off168last_idx8freeable2sc3idx3PLO3GLO3O162LI2FB2SC3IDXS1P1G2b38last_idx8freeable2sc6maplen3idx5mword3GLO". (* [comment removed for export] *)
#[using="hRP"] Lemma rallzerop_walk : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(17.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(18.(?.&8.))PP,$6.PG,$6.PB,$6.PA,$6.Pb3,$6.Poff16,$6.Pavail,$6.Pfreed,$6.Plast_idx,$6.Pfreeable,$6.Psc,$6.Pmaplen,$6.Psecret,$6.Pprev,(?.&40.)Pnext,(?.&40.)Zidx,$6.(27.R;.+1?.)Zmword,$6.(1<.(1<.(1<.R8.(1>.+20.R7.))(1>.+40.R6.))(1>.+1000.R5.))P,(5.$6.(28.&40.R2:.)R11.)P,(5.$6.(29.R12.+10.)=)P,(2.(1<.(1>.+10.R>.)+10.)R13.)P,(2.(1<.R14.+10.)(25.+2.+40.))P,(5.$6.R13.(26.(26.R15.(1>.+10.R10.))+10.))P,(5.$6.R13.(26.R15.(29.R15.+1000.)))P,(2.=R16.)P,(2.(1<.R17.+28.)(25.+2.+40.))P,(5.(18.(19.(?.&8.)))(1:.$16.R1:.(1;.(26.R19.+4.))#1.)(1?.(19.(?.&8.))(2:.(?.&8.)(2;.=)(2<.(?.&8.)))))P,(5.(18.(19.(?.&8.)))(1:.$16.R1;.(1;.(26.R1:.+3.))#1.)(1?.(19.(?.&8.))(2:.(?.&8.)(2;.R16.)(2<.(?.&8.)))))P,(5.(18.(19.(?.&8.)))(1:.$16.R1<.(1;.(26.R1;.+2.))#2.)(1?.(19.(?.&8.))(20.(12.R16.))))P,(5.(18.(19.(?.&8.)))(1:.$16.R1=.(1;.R1:.)#8.)(1?.(19.(?.&8.))(2=.(12.R1;.))))P,(2>.$16.R1>.R1<.(2:.$2?.(30.R10.)(2:.$2?.(30.R?.)(2:.$2?.(30.(12.R1;.))(2:.$2?.(31.(12.R17.))(2:.$2?.(31.(12.R16.))(2:.$2?.(30.(12.R=.))(2<.$2?.))))))))P,(5.(18.(19.(?.&8.)))(1:.$16.R1?.(1;.R1;.)#8.)(1?.(19.(?.&8.))(2=.(12.R12.))))P,(5.(18.(19.(?.&8.)))(1:.$16.R20.(1;.$32.)#8.)(1?.(19.(?.&8.))(2=.(12.R13.))))P,P,(4.R16.+30.)(5.(18.(19.(?.&8.)))(1:.$16.R22.(1;.(1<.$1=.(1>.+2.R17.)))#2.)(1?.(19.(?.&8.))(20.(12.(21.R17.)))))P,(1.(2.=R1=.)(4.R1=.+100.))P,(1.(2.=R1=.)(4.R1=.+10000.))P,(1.(2.=R1=.)(4.R1=.(25.+2.+20.)))P,(1.(2.=R1=.)(4.R1=.(25.+2.+20.)))P,(1.(2.=R19.)(4.R19.(25.+2.+40.)))P,(1.(2.=R1>.)(4.R1>.+20.))P,(1.(2.=R1>.)(4.R1>.+2.))P,(1.(2.=R1>.)(4.R1>.+40.))P,(1.(2.=R1>.)(4.R1>.(25.+2.+28.)))P,(2.R1;.R22.)P,(5.$33.(34.R25.R1<.)$35.)P,(5.$33.(34.R25.R1=.)$35.)P,P,(4.R23.+30.)(1.(2.(1>.(21.R24.)R1?.)R29.)(4.R29.(1>.(21.R24.)(1<.R1?.+1.))))P,P,(2.+30.R24.)(5.$6.R25.+3?.)P,P,(8.(5.$6.R24.=))(2.R2;.(26.(1>.R25.+100.)+1.))(22.$16.(23.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R42.(9.R28.R26.R25.)R33.R32.R31.)(10.(11.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(24.&40.+412<<.)R32.(14.(?.&40.))R31.(15.$16.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  (* [comment removed for export] *)
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *) specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
    apply rallzerop_tail; first [assumption| lia].
  - pose proof (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)) as RS1. specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
    st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (94460 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (94460 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS1. }
    clear RS1. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
    try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. apply rallzerop_tail; first [assumption| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L10660016816.99 L11515307516.102L11888887009.131L16998880622.130L18844022393.130L18926747947.129L18928490433.128L19681463867.130L1988470344.129 L1990406306.128 L2442693916.105 L24805867756.105L28072791123.130L31276902392.130L35831776013.111L36044444300.130L37855574625.100L3869037841.102 L40017915602.102L40273374871.129L4154889992.130 L46234224835.130L52527029236.130L54785571905.130L58797286115.130L7243157411.130 00000S01201f01g02g03L03o04n05e06Y07707U08_09`0:;0:<0:_0;>0;Y0<>0=E0=o0>00?40?^0@HS1p1r2b32lo2hi2po5off163idx3P163PHIS1p1r2b32lo2hi2po5off163idx3PHIS2st1p1r1g2b32lo2hi2po5off163idx2mr1a1k2SC2rg2A03HltFS2st1p1r1g2b32lo2hi2po5off163idx3P161a1k2B02rg2A02HG3RB04RBAL2HmS1p1r2b32lo2hi2po5off163idx1a1k2rg2A0S1p1r2b32lo2hi2po5off163idx1a2rg2A0S2st1p1r1g2b32lo2hi2po5off163idx3P163PLO1a1k2B02rg2A02HG3RB02HmS1p1r2b32lo2hi2po5off163idx3P161a1k3Hkk2B02rg2A03RB02HmS1p1r2b32lo2hi2po5off163idx3P161a1k3Hkk2B02rg2A03RB0S1p1r2b32lo2hi2po5off163idx2LOS1p1r2b32lo2hi2po5off163idx2HIS3hRP3RCB2st1p1r1g2b32lo2hi2po5off163idx3P161a1k2B02rg2A02A12HG3RB03RBC2HmS2st1p1r1g2b32lo2hi2po5off163idx3P161a1k2B02LO2HI2rg2A02HG3RB02HmS1p1r2b32lo2hi2po5off163idxFS1p1r2b32lo2hi2po5off163idx3P163PHIS1p1r2b32lo2hi2po5off163idx3P16S1p1r2b32lo2hi2po5off163idxS1p1r2b32lo2hi2po5off163idx1a1k2rg2A0S2st1p1r1g2b32lo2hi2po5off163idx2AL3P161a1k2B03BAL2rg2A02HG3RB04RBAL2HmS2st1p1r1g2b32lo2hi2po5off163idx1a1k2rg2A0FS3hRP3RCB2st1p1r1g2b32lo2hi2po5off163idx3P163PHI1a1k2B02BC2rg2A03RB0S2st1p1r1g2b32lo2hi2po5off163idx1a1k2rg2A0S2st1p1r1g2b32lo2hi2po5off163idx1a1k2rg2A0". (* [comment removed for export] *)
#[using="Type"] Lemma rallzerop_spec : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(17.&5.(?.&40.))Pfc,(?.&20.)Pm,P,(?.&40.)(18.(?.&8.))Pst,$36.Pp,$37.Pr,$38.Pg,$37.Pgh,$39.Par,$3:.Pb3,$6.Plo,$6.Phi,$6.Zsh,$3;.(3<.R9.(3=.$3>.$6.R8.))Zpo,$6.(3?.$3>.$6.R9.)Zoff16,$6.(1<.R4.(1>.+100.R3.))Zidx,$6.(27.R6.+1?.)Zbase,$37.(40.R<.(26.(41.(1>.$42.R2.))$42.))Zmr,$43.(44.R>.R;.)P,(45.VhRP,R?.R10.)P,(46.$16.R11.)P,(5.(18.$38.)(47.$3>.$38.(48.$3>.$49.$4:.$38.)(4;.$3>.$49.$4:.$38.)(3=.$3>.$6.R10.)(4<.R11.))(1?.$38.R?.))P,(5.$4=.(4>.R10.)$4?.)P,(5.$6.(28.&40.R2<.)(1<.(50.R11.)R9.))P,(5.$6.(29.R:.+10.)=)P,(2.+10.R;.)P,(2.(1<.(1>.+10.R;.)+10.)R<.)P,(2.(1<.R=.+10.)(51.(52.R15.)))P,(5.$53.(54.R?.(26.R>.+4.))(55.=))P,(5.$53.(54.R10.(26.R?.+3.))(55.R13.))P,(5.$53.(54.R11.(26.R10.+2.))(55.R13.))P,(5.$53.(54.R12.(26.R11.+1.))(55.R13.))P,(5.(18.$39.)(47.$37.$39.(48.$37.(56.$3>.$49.$6.$57.)(58.$3>.$49.$4:.$6.$57.$59.)$39.)(4;.$37.(56.$3>.$49.$6.$57.)(58.$3>.$49.$4:.$6.$57.$59.)$39.)R?.(5:.R1<.))(1?.$39.R18.))P,(5.$5;.(5<.R19.)(1?.$37.R1:.))P,(5=.R1>.R1;.)P,(2.=(3?.$3>.$6.R1<.))P,(5.$5;.(5>.R12.)(1?.$37.R13.))P,(5.(18.$3:.)(47.$37.$3:.(48.$37.(56.$3>.$49.$6.$57.)(58.$3>.$49.$4:.$6.$57.$59.)$3:.)(4;.$37.(56.$3>.$49.$6.$57.)(58.$3>.$49.$4:.$6.$57.$59.)$3:.)(5?.R1>.)(60.R21.))(1?.$3:.R1<.))P,(5.$6.(61.R1=.)(62.(63.R22.)))P,(1.(2.=(64.R15.))(4.(64.R15.)(25.+2.+20.)))P,(1.(2.=(65.R16.))(4.(65.R16.)(25.+2.+20.)))P,(1.(2.=(62.(63.R25.)))(4.(62.(63.R25.))(25.+2.+40.)))P,(1.(2.=(:.R18.))(4.(:.R18.)+20.))P,(1.(2.=(66.R19.))(4.(66.R19.)+2.))P,(1.(2.=(3.R1:.))(4.(3.R1:.)+40.))P,(1.(2.=(;.R1;.))(4.(;.R1;.)(25.+2.+28.)))P,(2.R1>.(:.R1<.))P,(5.$33.(34.(64.R1=.)R1?.)$35.)P,(5.$33.(34.(65.R1>.)R20.)$35.)P,P,(4.(3.R1?.)+30.)(1.(2.(1>.(21.(3.R20.))R22.)R23.)(4.R23.(1>.(21.(3.R20.))(1<.R22.+1.))))P,P,(2.+30.(3.R20.))(5.$6.(3.R21.)+3?.)P,P,(8.(5.$6.(;.R21.)=))(2.R25.(26.(1>.(;.R22.)+100.)+1.))(22.$16.(23.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R42.(9.(:.R22.)(3.R22.)(;.R22.))R33.R32.R31.)(10.(11.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(24.&40.$67.)R32.(14.(?.&40.))R31.(15.$16.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk
         AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml.
  dpose MR as (WF & CX & GL & AR & GR & SH).
  ddestruct WF as ((Hres & RPHres) & WR & DISJ & WA & WG).
  ddestruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). rceilb.
  (* [comment removed for export] *)
  destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
  ddestruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia.
  (* [comment removed for export] *)
  destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
  (* [comment removed for export] *)
  pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  (* [comment removed for export] *)
  pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA. rewrite Hchk in RA.
  pose proof (rmrep_ctx_secret_read st m MR) as RC.
  (* [comment removed for export] *)
  ddestruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
  assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
  { unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
  ddestruct MS as (a & ara & k & Ha & Hkk & Eg).
  ddestruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
  ddestruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). rceilb.
  assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
    replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  unfold rallzerop_entry.
  eapply (rallzerop_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            (r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
            (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (c_secret (ctx st))
            (pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
  - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
  - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
  - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
  - intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L10024172344.5  L10364520275.117L12548808786.13 L2080052437.3   L20924176549.13 L24891065923.128L24950154027.13 L27906715242.128L28227473900.118L28229572302.117L28375886731.11 L32295271444.5  L33057745221.118L3370425191.4   L35018450965.3  L35584746471.10 L3610818572.4   L39612860665.5  L41328049273.12 L41575466635.4  L4509366462.2   L46069113267.10 L48388240430.4  L5028327039.4   L53628637541.11 L55993805461.6  L57672326176.5  L58836541205.3  L59321604827.5  L64435775665.12 L64963549102.4  L65096965063.4  L68571656807.4  L8927506457.19  L9013102293.3   00000900R00b00i01J01e02?02Z03203J03Y03e04>04F04M04a04h05405N05\05e05n06506=06J06X06d06k07807U07]07e07m08`08gS1i2mr2HiS3off1c2bm1i1a2mr2Hi2B01qS1n3off1c2mr3FITS3off1cS3off1c2bm1i2mr2Sc1r4SPAN3SIL3OFSS3off1c2bm1a2mr2B01q2Fc3A00S3off1c2bm1i2mr2B01q2Sc2Q1S3off1c2bm1a2mr2B01q2Fc3A00S3off1c2bm1a2mr3S162B01qS3off1c2bm1a2mr3S162B01qS2mr1r4SMOD1q1HS2mr3ML03MPLS3off1c2bm1i1a2mr2Hi2B01qS2mr3SCrS3off1cS3off1c2bm1i2mr1q2Q1S2mr2SBS2mr3Hsc3H28S3off1c2br2bo1i2mr1q2Sc2Q1S1a2ka3Hka3A00S3off3OFFS3off1c1rS2mr2GES2mr3BSCS1i2mr2Hi3LIrS1n3off2mr3FITS2mr3BSC3H48S3off1cS2mr3E634SC48S3off1c2bm1i2mr3OFF2B02Sc3SI0S2mr3S16S2mr3FBrS2mr3LIrS3hRP3RCB3off1c2bm1i2mr3OFF2B02Sc1r3SI03RB03RBC3PHIS3off1c". (* [comment removed for export] *)
#[using="Type"] Lemma rallzerop_heap : ltac2:(CDefT.buildp (gd_tbl_HP_allzerop ()) "Pra,(?.&40.)Psp,(?.&40.)Pgp,(?.&40.)Ptp,(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Ps0,(?.&40.)Ps1,(?.&40.)Pa0,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Ps2,(?.&40.)Ps3,(?.&40.)Ps4,(?.&40.)Ps5,(?.&40.)Ps6,(?.&40.)Ps7,(?.&40.)Ps8,(?.&40.)Ps9,(?.&40.)Ps10,(?.&40.)Ps11,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)PF,(17.&5.(?.&40.))Pfc,(?.&20.)Pm,$68.Ps,$69.PLB,(19.$6:.)Pp,$6;.PA,$6.Pn,$6.P,(6<.VhRP,R5.R4.R6.)P,(6=.(6>.(6>.$6;.$6.)$6.)(6?.(6>.$6;.$6.)$6.(6?.$6;.$6.R4.R3.)R2.)R5.)P,(46.$16.R8.)P,(5.(?.&40.)R21.(24.&40.R5.))(>.$37.Lg,$37.(>.$6.Li,$6.(>.$6.Lz,$6.(1.(5.(18.(6>.$37.$6.))(47.$70.(6>.$37.$6.)(48.$37.(56.$3>.$49.$6.$57.)(58.$3>.$49.$4:.$6.$57.$59.)(6>.$37.$6.))(4;.$37.(56.$3>.$49.$6.$57.)(58.$3>.$49.$4:.$6.$57.$59.)(6>.$37.$6.))(3=.$70.$6.R:.)(71.(72.R<.)))(1?.(6>.$37.$6.)(6?.$37.$6.R3.R2.)))(1.(7.(8.(5.$6.R1.=))(<.(44.(72.R<.)R3.)))(1.(1.(2.=R1.)(2.R1.+1.))(22.$16.(23.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R1>.R1.R?.R>.R=.)(10.(11.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(24.&40.$67.)R>.(14.(?.&40.))R=.(15.$16.)))))))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until n. intros HP Hin MI A0.
  ddestruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PERM| exact Hin]).
  pose proof (areach_facts_proof _ _ AR) as MF.
  destruct (areach_inv _ st LB0 AR) as (L & LS & BL0 & INV & LIVE & RESV & SEC & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hin0) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n']. unfold blk_slot, blk_size, blk_addr, bslot, bsize, boff in C1, C2, C3. cbn [fst snd] in C1, C2, C3. subst n' c.
  ddestruct (block_facts x0 st L BL0 LS INV (fst p) off n Hk) as (g & bm & i & ai & a & ar & ka & BF). set (c := fst p) in *.
  set (mr := MI_Inv.MR st g).
  dexists g, i, (allzero_val (m_last_idx mr) (m_sizeclass mr) (m_maplen mr)).
  split. { rewrite <- Hst. cbn [s_slots strip]. exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF). }
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC. fold mr in BSC.
  split. { rewrite <- Hst. rewrite get_meta_rec_strip. change (get_meta_rec st g) with mr. apply allzero_val_undersized. clear -BSC. lia. }
  split; [apply allzero_val_range|].
  (* [comment removed for export] *)
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem. fold mr in Hmem.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hgh.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. fold mr in Hi.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT. fold mr in FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SMOD]. fold mr in S16, SMOD.
  pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B0 B16].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. fold mr in NA.
  pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. fold mr in NF.
  pose proof (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Eg).
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP. fold mr in TOP.
  pose proof (c_snd _ _ _ _ _ _ _ _ _ _ _ BF) as Sc. fold mr in Sc.
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Q1 Q2]. fold mr in Q1. cbn [aadd snd] in Q1, Q2.
  pose proof (p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as P16. cbn [aadd snd] in P16.
  pose proof (gbase_bm _ _ _ _ _ _ _ _ _ _ _ BF) as GB. fold mr in GB.
  unfold MI_Pres2.blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH. rewrite GB in SH.
  ddestruct SH as (K4 & K3 & K2 & K1 & Q & _).
  set (q := (snd c + UNIT * off - snd bm - UNIT) / UNIT) in *.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g bm Hmem). cbv zeta in FG. change (get_meta_rec st g) with mr in FG.
  ddestruct FG as (MSL & AVr & FRr & LIr & FBr & SCr & ML0 & _ & (r & Hr & Hk0 & _ & _ & SPAN) & _).
  pose proof (mf_maplen _ _ MF g bm) as MPL. rewrite !get_meta_rec_strip in MPL. change (get_meta_rec st g) with mr in MPL. specialize (MPL Hmem).
  pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. ddestruct FC as (_ & SECR & _).
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default id snd] in SPAN.
  unfold sstart in Sc. rewrite GB in Sc.
  assert (SI0 : 0 <= get_stride mr * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride mr * (i + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia).
  assert (Fc : fst c = fst bm) by (rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF); reflexivity).
  (* [comment removed for export] *)
  pose proof MR as (WF & _). dpose WF as (_ & WR & _ & WA & _).
  destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & _). rceilb.
  ddestruct (WA a ar Ha) as (rg & Hrg & A00 & _).
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; rewrite Fc; exact Hr).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  assert (ST16 : exists k, get_stride mr = 16 * k) by (exists (get_stride mr / 16); clear -SMOD; unfold UNIT in SMOD; Z.div_mod_to_equations; lia).
  destruct ST16 as [k16 STK].
  assert (OFS : UNIT * off + 16 <= get_stride mr) by (clear -FIT N0 STK OFF; unfold UNIT, IB in *; nia).
  assert (PHI : snd c + UNIT * off + 16 <= round_up_pg (r_len r)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. clear -Sc SPAN SIL OFS. unfold UNIT in *. lia. }
  assert (EBM : aadd (aadd c (UNIT * off)) (- (UNIT * q) - UNIT) = bm).
  { unfold aadd. cbn [fst snd]. destruct bm as [br bo]. cbn [fst snd] in Fc, Sc, Q1 |- *. f_equal; [exact Fc| clear -Sc Q1; unfold UNIT in *; lia]. }
  clear WF WR WA CR LIVE INV Hk PERM Hin Hin0.
  (* [comment removed for export] *)
  eapply (rallzerop_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            st (aadd c (UNIT * off)) r g (mkGhdr (Some g) ai) ar (i + 32 * Z.min (snd c + get_stride mr - IB - (snd c + UNIT * off) - n) 5) (byte_of q 0) (byte_of q 1));
    rewrite ?(u16_bytes q Q), ?(land31_idx i) by (clear -Hi LIr FIT N0 OFF; unfold UNIT, IB in *; lia);
    rewrite ?EBM; cbn [aadd fst snd g_meta]; change (get_meta_rec st g) with mr.
  - exact MR.
  - exact MI.
  - rewrite Fc. exact Hr.
  - exact Hk0.
  - rewrite A0, C3, Cc, unsigned_lit by (clear -RB0 RBC RUP PHI OFF Sc B0 SI0 RCB; unfold UNIT in *; lia). clear -Sc. unfold UNIT. lia.
  - exact P16.
  - clear -Sc B0 SI0 OFF. unfold UNIT in *. lia.
  - clear -Q1 Sc B0 OFF. unfold UNIT in *. lia.
  - exact PHI.
  - eapply known_at; [exact K4| clear; unfold UNIT; lia| reflexivity].
  - eapply known_at; [exact K3| clear; unfold UNIT; lia| reflexivity].
  - eapply known_at; [exact K2| clear; unfold UNIT; lia| reflexivity].
  - eapply known_at; [exact K1| clear; unfold UNIT; lia| reflexivity].
  - exact Hgh.
  - reflexivity.
  - exact MSL.
  - rewrite Eg. unfold mslot, aadd, AREA_HDR, META_SIZE. cbn [snd]. clear -A00 Hka. lia.
  - exact Hmem.
  - rewrite Eg, (area_of_mslot a ka Hal Hka). exact Ha.
  - exact Hck.
  - exact AVr.
  - exact FRr.
  - exact SECR.
  - clear -LIr. lia.
  - clear -FBr. lia.
  - clear -SCr. lia.
  - clear -MPL ML0. lia.
  - clear -Hi. lia.
  - exact NA.
  - exact NF.
  - intros SC48. destruct BSC as [(Hsc & Hle & Hst2)| E63]; [| exfalso; clear -SC48 E63; lia].
    pose proof (size_class_bound _ Hsc) as SB.
    apply (guard16_arith (size_class (m_sizeclass mr)) (get_stride mr) i off n q (m_last_idx mr)).
    + clear -SB. lia.
    + clear -Q1. unfold UNIT in Q1. lia.
    + clear -FIT. unfold UNIT, IB in FIT. lia.
    + exact N0.
    + exact OFF.
    + exact Hi.
    + clear -Hst2. unfold UNIT in Hst2. tauto.
    + clear -Hle Hsc. unfold UNIT in Hle. destruct Hle as [Hle|H28]; [left; exact Hle| right; apply size_class_28; lia].
  - clear -BSC. intros H48. lia.
  - intros NM. destruct (TOP NM) as [BM0 GE]. unfold gend, cnt_of, sstart in GE. rewrite GB, BM0 in GE.
    replace (m_maplen mr * 256) with (m_maplen mr * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia).
    apply (guard17_arith (get_stride mr) i off n q (m_last_idx mr) (m_maplen mr)).
    + clear -S16. unfold UNIT in S16. lia.
    + clear -Q1. unfold UNIT in Q1. lia.
    + clear -FIT. unfold UNIT, IB in FIT. lia.
    + exact N0.
    + clear -OFF. lia.
    + exact Hi.
    + clear -GE. unfold UNIT in GE. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


End RP_1.
