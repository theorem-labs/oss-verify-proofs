(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_mm_syscalls F_ntf F_free_C F_free_K F_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_get_meta HP_RF_mm_syscalls.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RF_free_A HP_RF_free_B HP_RF_free_C HP_RF_ntf HP_RF_free_K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Heap.F_free.DROPPED"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.brkstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_brk"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.BrkLive"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.drop_region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_B.CINV"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_addr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.free"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "RP_1.rfree_end"; "RocqVerifyHarness.AgentSubmission.Heap.F_free.lbrm"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rfree_entry"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_free ()) "Lms',$0.(1.(2.$3.O1.O3.)(4.(5.&40.)Lt0,(5.&40.)(4.(5.&40.)Lt1,(5.&40.)(4.(5.&40.)Lt2,(5.&40.)(4.(5.&40.)La0,(5.&40.)(4.(5.&40.)La1,(5.&40.)(4.(5.&40.)La2,(5.&40.)(4.(5.&40.)La3,(5.&40.)(4.(5.&40.)La4,(5.&40.)(4.(5.&40.)La5,(5.&40.)(4.(5.&40.)La6,(5.&40.)(4.(5.&40.)La7,(5.&40.)(4.(5.&40.)Lt3,(5.&40.)(4.(5.&40.)Lt4,(5.&40.)(4.(5.&40.)Lt5,(5.&40.)(4.(5.&40.)Lt6,(5.&40.)(4.P,(5.&40.)(6.(5.&8.))Lm',P,(5.&40.)(6.(5.&8.))(1.(2.$0.R11.(7.(8.O1:.O19.O18.O17.R10.R?.R>.O16.O15.R=.R<.R;.R:.R9.R8.R7.R6.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R5.R4.R3.R2.)O:.(9.O1:.)O9.(:.(5.&40.))R1.(;.$<.)))(1.(=.$<.R1.)(1.(>.$<.R1.O8.(?.&40.O19.))(1.(10.$<.R1.(11.(?.&40.O17.)-:4.)(12.$13.(14.O4.)(15.$13.)))(1.(16.VhRP,O2.R1.)(1.(17.La,$18.(19.(1:.O7.O8.(?.&40.O19.)R1.)(19.(1;.O7.O2.R1.)(1.(1<.+5=024.R1.)(1=.R1.+5=028.))))O5.R1.)(1.Prid,$1>.Pr',$1?.P,(2.(6.$1?.)(20.$1>.$1?.(21.$1>.$22.$23.$1?.)(24.$1>.$22.$23.$1?.)R2.(25.O2.))(26.$1?.R1.))(2.(6.$1?.)(20.$1>.$1?.(21.$1>.$22.$23.$1?.)(24.$1>.$22.$23.$1?.)R3.(25.O7.))(26.$1?.R2.))(1.Pblk',$27.P,(28.$27.R1.O6.)(4.$1?.Lr',$1?.(2.(6.$1?.)(20.$1>.$1?.(21.$1>.$22.$23.$1?.)(24.$1>.$22.$23.$1?.)(29.$1>.$18.(2:.R3.))(25.O2.))(26.$1?.R1.)))(1.(2.$2;.(2<.(2=.O2.))(2<.(2=.O7.)))Pbrid,$1>.Pboff,$18.P,(2.$2;.(2<.(2=.O7.))(2>.R2.R1.))(2.(6.$1?.)(20.$1>.$1?.(21.$1>.$22.$23.$1?.)(24.$1>.$22.$23.$1?.)R3.(25.O2.))(20.$1>.$1?.(21.$1>.$22.$23.$1?.)(24.$1>.$22.$23.$1?.)R3.(25.O7.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L59308579281.27L59308579281.31L59308579414.27L59315020128.1800000?00_01101JS1a2Ha1r3Hin2H2S2st1a2Ha1b3Hin2rb2Cb3Sb03Sb12H2S1a2Ha1r3Hin2H22H3S3hRP2lo2sp1a3RCB2LO2Ha1A". (* [comment removed for export] *)
#[using="Type"] Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> rceil <= lo -> 380964 <= a < 380968 -> ~ rfree_fp st lo sp a.
Proof. rceilb.
  intros MR LO Ha. pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG). rceilb.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - ddestruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
  - ddestruct A as (b & gh & Hb & Hin). ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - ddestruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L44821141788.37L52101704234.48L56765662472.34L59308579027.47L59308579152.44L59308579152.47L59310683405.35L68478441328.39L68478441328.42L68478441328.43L68478610631.45L68480817008.34L7470072769.45 00000L00f00o01T02102X02n03F03o04Y05105E05bS3hRP2r23slo3shi2LO3RB01a2L1S2r23RB01a2rk3Ha'2H32H52H4S2r21a2HaS2r23RB01a2ak2ra3Ha'3Hin3Sa11H2H03ALRS2r23RB01a2rk3Ha'3Hin1H2H12H0S2r23RB01a1b2rb3Ha'3Hin3Sb11H2H13Sb02H0S2r23RB02D41a1C3Hin2D3S3hRP2r23RB01a2rk3Hin2RCS3hRP3st23rid2r23RB01a1b3Hin2rb2Cb3Sb12RCS3hRP3st23rid2r23RB01a2ak3Hin2ra2Ca3Sa12RCS3hRP2r23RB01a2rk3Ha'2RCS3hRP2r23RCB3RB01a1CS3rid2r23RB01a1k2rk2NE3Ha'2H2". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free ()) "P,(16.VhRP,(2?.O6.O7.)O4.)P,(16.VhRP,O7.O4.)P,(2.(6.$1?.)(20.$1>.$1?.(21.$1>.$22.$23.$1?.)(24.$1>.$22.$23.$1?.)O6.(25.O7.))(26.$1?.O5.))P,(2.$30.(31.O5.)$32.)P,(33.(12.(34.$18.$18.)(35.$18.$18.O2.O1.)(12.(34.$18.$18.)(35.$18.$18.+5=024.+5=028.)(12.(34.$18.$18.)(35.$18.$18.(36.O5.)(11.(36.O5.)(37.(38.O5.))))(15.(34.$18.$18.)))))O4.O3.)P,(1<.(39.VhRP,)O2.)(16.VhRP,(2?.O6.O7.)O3.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG). rceilb.
  pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). rceilb.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < rceil /\ ~ (380964 <= a < 380968) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold HP_RMallocRep.RPAGE_SIZE in C; lia.
        * ddestruct C as (ak & ar & Hak & Hin). ddestruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). rceilb. lia.
        * ddestruct C as (b & gh & Hb & Hin). ddestruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). rceilb. lia.
        * ddestruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). rceilb. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold HP_RMallocRep.RPAGE_SIZE in C; lia.
        * ddestruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          ddestruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * ddestruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          ddestruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
          assert (NE : fst b <> rid).
          { intros E. dpose (proj1 MRd) as (_ & _ & _ & _ & WG'). ddestruct (WG' b gh Hb) as (rb' & Hrb' & _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * ddestruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - ddestruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). rceilb.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  ddestruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="hRP"] Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. rceilb. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L16039846688.1000000HS2x02x12x22x31H2H02H12H2". (* [comment removed for export] *)
#[using="hRP"] Lemma bytes4_range (x0 x1 x2 x3 : byte) : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free ()) "(1.(1<.=(11.(11.(11.(?.&8.O4.)(3:.+100.(?.&8.O3.)))(3:.+10000.(?.&8.O2.)))(3:.+1000000.(?.&8.O1.))))(1=.(11.(11.(11.(?.&8.O4.)(3:.+100.(?.&8.O3.)))(3:.+10000.(?.&8.O2.)))(3:.+1000000.(?.&8.O1.)))(3;.+2.+20.)))")
(* [comment removed for export] *).
Proof. rceilb.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L16039846688.10L23974523120.24L53336679046.31L53749257917.31L54335070281.2400000H01601n02f03QS2x02x12x22x31H2H02H12H2S2x02x12x22x31H2H02H12H21q1r2H32H42q02r02H82H9S2x02x12x22x31H2H02H12H21q1r2H32H42q02r02r12H82H92q13H13S2x02x12x22x31H2H02H12H21q1r2H32H42q02r02r12H82H92q13H13S2x02x12x22x31H2H02H12H21q1r2r02H32H42q02H8". (* [comment removed for export] *)
#[using="hRP"] Lemma le4_of_bytes (x0 x1 x2 x3 : byte) : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free ()) "(2.(3<.(5.&8.))(3=.(3>.(11.(11.(11.(?.&8.O4.)(3:.+100.(?.&8.O3.)))(3:.+10000.(?.&8.O2.)))(3:.+1000000.(?.&8.O1.)))))(12.(5.&8.)O4.(12.(5.&8.)O3.(12.(5.&8.)O2.(12.(5.&8.)O1.(15.(5.&8.)))))))")
(* [comment removed for export] *).
Proof. rceilb.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  (* [comment removed for export] *)
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L28416475008.12L29311285958.5 00000?00@S1v1q1H1r2H02H1S". (* [comment removed for export] *)
#[using="hRP"] Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. rceilb. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L29311285958.5L4294722584.1200000100@SS1v1q1H1r2H02H1". (* [comment removed for export] *)
#[using="hRP"] Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. rceilb. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L16326081522.11L29317572024.4 00000?00@S1v2Hv1q1r1H2H0S". (* [comment removed for export] *)
#[using="hRP"] Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. rceilb. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : rceil <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Local Ltac2 Set LiaOrc.tbl := fun () => "01c0@L10354032718.128L10912578751.129L12126995025.155L12728961192.152L13070583853.158L1382374031.153 L14029807724.186L14788946355.197L14788946357.169L14789109775.258L14791075378.237L15526604756.237L17479887530.133L18420260431.117L19512066613.158L19526751053.158L19642438194.171L2019612259.207 L20927540382.186L20928290744.134L22602709862.153L22618742316.159L22618742316.180L2272979758.263 L23094780194.237L23648276763.153L23831897239.135L24892852038.127L24896721578.155L2630779867.151 L26644516120.294L2740165704.133 L27823692597.153L28206118222.161L2899996309.169 L29513969710.158L29524240247.199L29524291445.265L29524456754.201L29524616690.153L29524618736.216L29851195439.164L29851213098.133L29909465045.153L30500802930.154L31623957675.237L34303958027.258L34774637743.155L34774637743.176L35522313264.73 L35584126579.294L37310060433.227L37310060433.294L37410144924.237L37622523289.266L37670400727.135L38261021259.143L3882860516.143 L41575466635.159L42010583364.214L42536635552.150L43657705634.17 L43728151306.155L44420580483.153L45694801840.153L46062280881.118L46235043666.119L46491124354.135L47028770742.237L47028999824.124L47227130201.153L47776540700.213L47937923715.153L47938022951.158L47944318815.158L48462833845.141L48581247323.153L48879164436.152L5015452641.150 L50730677403.153L51695861210.146L5236105241.237 L52381212503.155L52383395849.155L52434604720.154L52434604720.181L52434604720.201L53001778891.155L53677837751.197L55299813705.266L56463164143.142L57034901365.197L5744833530.266 L57589471182.237L57619622870.186L57680746506.167L57685088653.128L57685088690.129L58829609757.151L59314873579.202L59314873579.3  L60495891164.186L62716980453.141L64012849077.9  L6410788334.237 L64569623259.153L64618030091.153L65123225494.237L65467925015.135L65478640403.153L66149329551.30 L66828378437.155L6755509565.140 L8927475618.153 L9049287895.129 00000Q01601Q01e02@03303Y04B04k05\06M07:08@08\09409L0:70:N0;:0<I0=:0=U0>@0>i0?W0@20@H0@e0A>0BC0BZ0CT0D:0DU0Dn0EG0E`0F<0FZ0G80GT0Go0HW0Hi0ID0JD0JV0LQ0MW0N00NW0O50O[0PO0QL0Qb0R@0RX0S70SU0T40TU0U40V@0W90WU0X40XJ0X\0Y90Y`0ZC0Z_0[60[M0[j0\E0\b0]?0]Z0^50^Q0`>0`b0a60aJ0a^0bJ0bY0cK0d00dB0e80eJ0f00f[0g>0ge0h80hQ0h\0iB0j20jI0jk0kF0kZ0l40lJ0le0mY0n20nF0n`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". (* [comment removed for export] *)
Theorem rlibc_free_implT : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free ()) "Pra,(5.&40.)Psp,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pm,$3?.Ps,$3.Pst,$40.Pblk,$27.Poff,$18.Perrv,(5.&40.)P,(41.R4.VLB,)P,(28.$27.R4.VLB,)P,(1<.=R4.)P,(2.$18.(42.R6.)(11.(43.R7.(2:.R6.))(3:.$44.R5.)))P,(16.VhRP,R8.R:.)P,(=.$<.R;.)P,(>.$<.R<.Vlo,(?.&40.R1<.))P,(1<.Vlo,(45.(?.&40.R1=.)+2000.))P,(10.$<.R>.(11.(?.&40.Vtp,)-:4.)(12.$13.(14.R9.)(15.$13.)))P,(2.(5.&40.)R1;.(46.&40.(42.R<.)))(47.$40.R10.(48.R>.(26.$49.(4:.(2:.R=.)(3:.$44.R<.))))R?.(4;.R21.R20.Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R>.(4<.VLB,R=.)R10.R;.R?.)(7.(8.R21.R20.Vgp,Vtp,R1?.R1>.R1=.Vs0,Vs1,R1<.R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(46.&40.$4=.)Vfc,(:.(5.&40.))R10.(;.$<.)))")
(* [comment removed for export] *).
Proof using LO TP.
  intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  ddestruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  ddestruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = 380964) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof LO as LOv. rceilb.
  (* [comment removed for export] *)
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (rceilb; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x7e000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  (* [comment removed for export] *)
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  (* [comment removed for export] *)
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  (* [comment removed for export] *)
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at rsegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at rsegs m (r_base r + snd q) 1).
    { ddestruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); rceilb; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  (* [comment removed for export] *)
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt rsegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). ddestruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. (* [comment removed for export] *) }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    (* [comment removed for export] *)
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    - (* [comment removed for export] *)
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32. 
      ddestruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0. 
      ddestruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1. 
      ddestruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
      ddestruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8. ddestruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. ddestruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. ddestruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    - (* [comment removed for export] *)
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. ddestruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. ddestruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  (intros r1 s' ms1 dd_H; ddestruct dd_H as (-> & -> & FH)). cbv beta iota.
  ddestruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  (* [comment removed for export] *)
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  - (* [comment removed for export] *)
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    ddestruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    split; [reflexivity|]. deexists 16. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  - (* [comment removed for export] *)
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    (intros ms2 dd_H; ddestruct dd_H as (y2 & y3 & y4 & y5 & y6 & y7 & ->)).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    (* [comment removed for export] *)
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    ddestruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x3fd50)) with (Z_to_bv 64 0x3fd50) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells rsegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    + (* [comment removed for export] *)
      cbv beta iota.
      ddestruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). rceilb.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x7e000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms4 FM. unfold rfmun_post in FM.
      ddestruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. lia.
        - rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      ddestruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
      rewrite (munmap_ok_range_val a ERNG).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x3fd80)) with (Z_to_bv 64 0x3fd80) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      (* [comment removed for export] *)
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      ddestruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. deexists 16. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { (* [comment removed for export] *)
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. dexists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 380964 <= a < 380968)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 380964 <= a < 380968)); [| exact NC].
          cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia | right; left; apply DR; lia]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 380964 <= a < 380968)); [| exact NC].
        cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    + (* [comment removed for export] *)
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      ddestruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. deexists 16. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 380964 <= a < 380968)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FREE.

End RP_1.
